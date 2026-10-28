/* ESP32 NAT Router - Main application
 *
 * Entry point, global variable definitions, WiFi/Ethernet initialization,
 * event handlers, LED status thread, and console REPL.
 *
 * Modular source files:
 *    portmap.c       - Port mapping (NAPT) table management
 *    dhcp_manager.c  - DHCP reservation management
 *    acl_nvs.c       - ACL firewall rule persistence
 *    vpn_manager.c   - WireGuard VPN connection management
 *    netif_hooks.c   - Network interface hooks (byte counting, ACL, PCAP, MSS/PMTU)
 *    dns_spoof.c     - DNS interception, captive portal & single-domain block
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <time.h>
#include <pthread.h>
#include "esp_system.h"
#include "esp_log.h"
#include "esp_timer.h"
#include "esp_console.h"
#include "esp_vfs_dev.h"
#include "driver/gpio.h"
#include "driver/uart.h"
#include "driver/uart_vfs.h"
#include "driver/usb_serial_jtag.h"
#include "driver/usb_serial_jtag_vfs.h"
#include "linenoise/linenoise.h"
#include "argtable3/argtable3.h"
#include "esp_vfs_fat.h"
#include "nvs.h"
#include "nvs_flash.h"
#include "esp_ota_ops.h"

#include "freertos/event_groups.h"
#include "esp_wifi.h"
#if !CONFIG_ETH_UPLINK
#include "esp_eap_client.h"
#endif
#if CONFIG_ETH_UPLINK
#include "esp_eth.h"
#endif

#include "lwip/opt.h"
#include "lwip/err.h"
#include "lwip/sys.h"

#include "dhcpserver/dhcpserver.h"
#include "dhcpserver/dhcpserver_options.h"

#include "cmd_system.h"
#include "cmd_router.h"
#include <esp_http_server.h>

#if !IP_NAPT
#error "IP_NAPT must be defined"
#endif
#include "lwip/lwip_napt.h"

#include "router_globals.h"
#include "lwip/ip_addr.h"
#include "esp_netif.h"
#include "client_stats.h"
#include "pcap_capture.h"
#include "remote_console.h"
#include "syslog_client.h"
#include "oled_display.h"
#include "led_strip_status.h"
#if !defined(CONFIG_IDF_TARGET_ESP32C5)
#include "mdns.h"
#endif
#if CONFIG_MQTT_HOMEASSISTANT
#include "mqtt_ha.h"
#endif

// External prototype for DNS Spoofing & Interception Task
extern void dns_server_task(void *pvParameters);

// Byte counting variables
uint64_t sta_bytes_sent = 0;
uint64_t sta_bytes_received = 0;

// TTL override for STA upstream (0 = disabled/no change)
uint8_t sta_ttl_override = 0;

// Reconnect watchdog timeout in seconds (0 = disabled)
uint16_t reconnect_watchdog_s = 0;

// MSS clamp for AP interface (0 = disabled, otherwise max MSS in bytes)
uint16_t ap_mss_clamp = 0;

// Path MTU for AP clients: send ICMP Fragmentation Needed when a DF-flagged packet
// from a client exceeds this size (0 = disabled).
uint16_t ap_pmtu = 0;

// AP SSID hidden (0 = visible, 1 = hidden)
uint8_t ap_ssid_hidden = 0;

// Allow only known clients (1 = MACs without a fixed-IP reservation are blocked)
uint8_t ap_known_only = 0;

// WiFi regulatory country code ("01" = world-safe default)
char wifi_country_code[3] = "01";

// AP auth mode (0 = WPA2/WPA3, 1 = WPA2 only, 2 = WPA3 only)
uint8_t ap_authmode = 0;

#if CONFIG_ETH_UPLINK
// AP WiFi channel (0 = auto, 1-13 = fixed channel; ETH_UPLINK only)
uint8_t ap_channel = 0;
#endif

#if !CONFIG_ETH_UPLINK
// WPA2-Enterprise settings
int32_t eap_method = 0;          // 0=Auto, 1=PEAP, 2=TTLS, 3=TLS
int32_t ttls_phase2 = 0;         // 0=MSCHAPv2, 1=MSCHAP, 2=PAP, 3=CHAP
int32_t use_cert_bundle = 0;     // 0=off, 1=on
int32_t disable_time_check = 0;  // 0=off, 1=on
#endif

#if WIFI_HAS_5GHZ
// STA band preference (0=auto, 1=2.4GHz, 2=5GHz)
uint8_t sta_band = STA_BAND_AUTO;
#endif

// WireGuard VPN settings
int32_t vpn_enabled = 0;
int32_t vpn_port = 51820;
int32_t vpn_keepalive = 0;
int32_t vpn_mtu = VPN_MTU_DEFAULT;
char* vpn_private_key = NULL;
char* vpn_public_key = NULL;
char* vpn_preshared_key = NULL;
char* vpn_endpoint = NULL;
char* vpn_address = NULL;
char* vpn_netmask = NULL;
char* vpn_dns = NULL;
bool vpn_connected = false;
uint32_t vpn_tunnel_ip = 0;         // Cached VPN tunnel IP (network byte order)
int32_t vpn_killswitch = 1;         // Kill switch default on
int32_t vpn_route_all = 1;          // Route all traffic through VPN (default on)

/* FreeRTOS event group to signal when we are connected*/
static EventGroupHandle_t wifi_event_group;

/* The event group allows multiple bits for each event, but we only care about one event
 * - are we connected to the AP with an IP? */
const int WIFI_CONNECTED_BIT = BIT0;

#define DEFAULT_DNS "8.8.8.8"

/* Effective DNS for AP clients: VPN DNS (while VPN enabled) overrides the
 * manual ap_dns override, which in turn overrides the upstream-supplied DNS.
 * Returns NULL when neither override is set so callers fall back to upstream. */
static const char* effective_ap_dns(void)
{
    if (vpn_enabled && vpn_dns && vpn_dns[0]) return vpn_dns;
    if (ap_dns && ap_dns[0]) return ap_dns;
    return NULL;
}

#if !CONFIG_ETH_UPLINK
/* STA reconnect backoff */
#define STA_RECONNECT_INITIAL_MS  250
#define STA_RECONNECT_MAX_MS     16000
static esp_timer_handle_t sta_reconnect_timer;
static uint32_t sta_reconnect_delay_ms = STA_RECONNECT_INITIAL_MS;
#endif

/* Global vars */
uint16_t connect_count = 0;
bool ap_connect = false;
bool wifi_scan_active = false;
bool has_static_ip = false;
int led_gpio = -1;  // -1 means LED disabled (none)
uint8_t led_lowactive = 0;  // 0 = active-high (default), 1 = active-low (inverted)
uint8_t led_toggle = 0;  // Shared toggle state for packet-driven LED flicker

int antenna_gpio = -1;      // -1 means antenna switching disabled (pins untouched)
int antenna_en_gpio = -1;   // Optional RF-switch enable pin, driven low
uint8_t antenna_state = 0;  // 0 = on-board antenna, 1 = external antenna

uint32_t my_ip;
uint32_t my_ap_ip;

struct portmap_table_entry portmap_tab[IP_PORTMAP_MAX];
struct dhcp_reservation_entry dhcp_reservations[MAX_DHCP_RESERVATIONS];

esp_netif_t* wifiAP;
bool ap_disabled = false;
uint8_t ap_nat_enabled = 1;
#if CONFIG_ETH_UPLINK
esp_netif_t* ethNetif = NULL;
esp_eth_handle_t eth_handle = NULL;
#else
esp_netif_t* wifiSTA;
#endif

#include "http_server.h"

static const char *TAG = "ESP32 NAT router";

/* Console command history can be stored to and loaded from a file.
 * The easiest way to do this is to use FATFS filesystem on top of
 * wear_levelling library.
 */
#if CONFIG_STORE_HISTORY

#define MOUNT_PATH "/data"
#define HISTORY_PATH MOUNT_PATH "/history.txt"

static void initialize_filesystem(void)
{
    static wl_handle_t wl_handle;
    const esp_vfs_fat_mount_config_t mount_config = {
            .max_files = 4,
            .format_if_mount_failed = true
    };
    esp_err_t err = esp_vfs_fat_spiflash_mount_rw_wl(MOUNT_PATH, "storage", &mount_config, &wl_handle);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to mount FATFS (%s)", esp_err_to_name(err));
        return;
    }
}
#endif // CONFIG_STORE_HISTORY

static void initialize_nvs(void)
{
    esp_err_t err = nvs_flash_init();
    if (err == ESP_ERR_NVS_NO_FREE_PAGES || err == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK( nvs_flash_erase() );
        err = nvs_flash_init();
    }
    ESP_ERROR_CHECK(err);
}

static void initialize_console(void)
{
    /* Disable buffering on stdin */
    setvbuf(stdin, NULL, _IONBF, 0);

#if CONFIG_ESP_CONSOLE_UART_DEFAULT || CONFIG_ESP_CONSOLE_UART_CUSTOM
    /* Drain stdout before reconfiguring it */
    fflush(stdout);
    fsync(fileno(stdout));

    /* Minicom, screen, idf_monitor send CR when ENTER key is pressed */
    uart_vfs_dev_port_set_rx_line_endings(0, ESP_LINE_ENDINGS_CR);
    /* Move the caret to the beginning of the next line on '\n' */
    uart_vfs_dev_port_set_tx_line_endings(0, ESP_LINE_ENDINGS_CRLF);

    /* Configure UART. Note that REF_TICK is used so that the baud rate remains
     * correct while APB frequency is changing in light sleep mode.
     */
    const uart_config_t uart_config = {
            .baud_rate = CONFIG_ESP_CONSOLE_UART_BAUDRATE,
            .data_bits = UART_DATA_8_BITS,
            .parity = UART_PARITY_DISABLE,
            .stop_bits = UART_STOP_BITS_1,
            .source_clk = UART_SCLK_DEFAULT,
    };
    /* Install UART driver for interrupt-driven reads and writes */
    ESP_ERROR_CHECK( uart_driver_install(CONFIG_ESP_CONSOLE_UART_NUM,
            256, 0, 0, NULL, 0) );
    ESP_ERROR_CHECK( uart_param_config(CONFIG_ESP_CONSOLE_UART_NUM, &uart_config) );

    /* Tell VFS to use UART driver */
    uart_vfs_dev_use_driver(CONFIG_ESP_CONSOLE_UART_NUM);
#endif

#if CONFIG_ESP_CONSOLE_USB_SERIAL_JTAG
    /* Enable non-blocking mode on stdin and stdout */
    fcntl(fileno(stdout), F_SETFL, O_NONBLOCK);
    fcntl(fileno(stdin), F_SETFL, O_NONBLOCK);

    /* Minicom, screen, idf_monitor send CR when ENTER key is pressed */
    usb_serial_jtag_vfs_set_rx_line_endings(ESP_LINE_ENDINGS_CR);

    /* Move the caret to the beginning of the next line on '\n' */
    usb_serial_jtag_vfs_set_tx_line_endings(ESP_LINE_ENDINGS_CRLF);
    usb_serial_jtag_driver_config_t usb_serial_jtag_config = {
        .tx_buffer_size = 256,
        .rx_buffer_size = 256,
    };

    /* Install USB-SERIAL-JTAG driver for interrupt-driven reads and writes */
    usb_serial_jtag_driver_install(&usb_serial_jtag_config);

    /* Tell vfs to use usb-serial-jtag driver */
    usb_serial_jtag_vfs_use_driver();
#endif

    /* Initialize the console */
    esp_console_config_t console_config = {
            .max_cmdline_args = 32,
            .max_cmdline_length = 256,
#if CONFIG_LOG_COLORS
            .hint_color = atoi(LOG_COLOR_CYAN)
#endif
    };
    ESP_ERROR_CHECK( esp_console_init(&console_config) );

    /* Configure linenoise line completion library */
    /* Enable multiline editing. If not set, long commands will scroll within
     * single line.
     */
    linenoiseSetMultiLine(1);

    /* Tell linenoise where to get command completions and hints */
    linenoiseSetCompletionCallback(&esp_console_get_completion);
    linenoiseSetHintsCallback((linenoiseHintsCallback*) &esp_console_get_hint);

    /* Set command history size */
    linenoiseHistorySetMaxLen(100);

#if CONFIG_STORE_HISTORY
    /* Load command history from filesystem */
    linenoiseHistoryLoad(HISTORY_PATH);
#endif
}

// BOOT button GPIO: GPIO28 on ESP32-C5 board, GPIO9 on C3/C2/C6, GPIO0 on ESP32/S2/S3
#if defined(CONFIG_IDF_TARGET_ESP32C5)
#define BOOT_BUTTON_GPIO      28
#elif defined(CONFIG_IDF_TARGET_ESP32C3) || defined(CONFIG_IDF_TARGET_ESP32C2) || defined(CONFIG_IDF_TARGET_ESP32C6)
#define BOOT_BUTTON_GPIO      9
#else
#define BOOT_BUTTON_GPIO      0
#endif
#define FACTORY_RESET_HOLD_MS 5000
#define POLL_INTERVAL_MS      50

void * led_status_thread(void * p)
{
#if !CONFIG_ETH_UPLINK
    // Init boot button for factory reset detection (GPIO0 used by ETH clock on WT32-ETH01)
    gpio_reset_pin(BOOT_BUTTON_GPIO);
    gpio_set_direction(BOOT_BUTTON_GPIO, GPIO_MODE_INPUT);
    gpio_set_pull_mode(BOOT_BUTTON_GPIO, GPIO_PULLUP_ONLY);
#endif

    bool led_enabled = (led_gpio >= 0);
    if (led_enabled) {
        ESP_LOGI(TAG, "LED status on GPIO %d%s", led_gpio, led_lowactive ? " (low-active)" : "");
        gpio_reset_pin(led_gpio);
        gpio_set_direction(led_gpio, GPIO_MODE_OUTPUT);
    } else {
        ESP_LOGI(TAG, "LED status disabled (no GPIO configured)");
    }

    int held_ms = 0;
    uint32_t wd_disconnected_s = 0;

    bool strip_active = led_strip_is_active();

    while (true)
    {
        // --- LED status: OFF=disconnected, ON=connected (packet hooks flicker it off) ---
        if (led_enabled && held_ms == 0) {
            gpio_set_level(led_gpio, ap_connect ^ led_lowactive);
        }

        // --- Poll interval with button polling ---
        for (int t = 0; t < 1000 / POLL_INTERVAL_MS; t++) {
            vTaskDelay(pdMS_TO_TICKS(POLL_INTERVAL_MS));

            // Update addressable LED strip colour each tick
            if (strip_active) {
                led_strip_status_update();
            }

#if !CONFIG_ETH_UPLINK
            if (gpio_get_level(BOOT_BUTTON_GPIO) == 0) {
                held_ms += POLL_INTERVAL_MS;
                // Rapid LED toggle for visual feedback during hold
                if (led_enabled) {
                    gpio_set_level(led_gpio, ((held_ms / POLL_INTERVAL_MS) % 2) ^ led_lowactive);
                }
                if (strip_active) {
                    led_strip_set_factory_reset(true);
                }
                if (held_ms >= FACTORY_RESET_HOLD_MS) {
                    ESP_LOGW(TAG, "BOOT button held %d ms - factory reset!", held_ms);
                    nvs_handle_t nvs;
                    if (nvs_open(PARAM_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
                        nvs_erase_all(nvs);
                        nvs_commit(nvs);
                        nvs_close(nvs);
                    }
                    esp_wifi_restore();
                    esp_restart();
                }
            } else {
                if (held_ms > 0 && strip_active) {
                    led_strip_set_factory_reset(false);
                }
                held_ms = 0;
            }
#endif
        }

        /* Reconnect watchdog: restart if uplink has been down too long */
        if (reconnect_watchdog_s > 0
#if !CONFIG_ETH_UPLINK
            && ssid != NULL && ssid[0] != '\0'
#endif
        ) {
            if (ap_connect) {
                wd_disconnected_s = 0;
            } else if (++wd_disconnected_s >= reconnect_watchdog_s) {
                ESP_LOGW(TAG, "Watchdog: no uplink for %"PRIu32" s, restarting", wd_disconnected_s);
                esp_restart();
            }
        }
    }
}

/* Event handlers */

#if CONFIG_ETH_UPLINK
static void eth_event_handler(void* arg, esp_event_base_t event_base,
                               int32_t event_id, void* event_data)
{
    if (event_base == ETH_EVENT) {
        if (event_id == ETHERNET_EVENT_CONNECTED) {
            ESP_LOGI(TAG, "Ethernet link up");
        } else if (event_id == ETHERNET_EVENT_DISCONNECTED) {
            ESP_LOGI(TAG, "Ethernet link down");
            if (vpn_connected) {
                vpn_disconnect();
            }
            ap_connect = false;
            xEventGroupClearBits(wifi_event_group, WIFI_CONNECTED_BIT);
        } else if (event_id == ETHERNET_EVENT_START) {
            ESP_LOGI(TAG, "Ethernet started");
        }
    } else if (event_base == IP_EVENT && event_id == IP_EVENT_ETH_GOT_IP) {
        ip_event_got_ip_t* event = (ip_event_got_ip_t*) event_data;
        ESP_LOGI(TAG, "ETH got ip:" IPSTR, IP2STR(&event->ip_info.ip));
        ap_connect = true;
        my_ip = event->ip_info.ip.addr;
        delete_portmap_tab();
        apply_portmap_tab();

        // Copy DNS from ETH to AP (or use the effective override: VPN DNS / ap_dns)
        esp_netif_dns_info_t dns;
        const char *eff_dns = effective_ap_dns();
        if (eff_dns) {
            dns.ip.u_addr.ip4.addr = esp_ip4addr_aton(eff_dns);
            dns.ip.type = ESP_IPADDR_TYPE_V4;
            esp_netif_set_dns_info(wifiAP, ESP_NETIF_DNS_MAIN, &dns);
            ESP_LOGI(TAG, "AP DNS set to %s", eff_dns);
        } else if (esp_netif_get_dns_info(ethNetif, ESP_NETIF_DNS_MAIN, &dns) == ESP_OK) {
            esp_netif_set_dns_info(wifiAP, ESP_NETIF_DNS_MAIN, &dns);
            ESP_LOGI(TAG, "set dns to:" IPSTR, IP2STR(&(dns.ip.u_addr.ip4)));
        }

        // esp_netif just (re)set netif_default to the uplink on this GOT_IP. If
        // the VPN is up in route-all mode, restore the tunnel as the default
        // route so forwarded traffic keeps going through WireGuard across DHCP
        // lease renewals and uplink reconnects.
        vpn_reassert_default_route();

        init_byte_counter();

        init_sntp_if_needed();
        syslog_notify_connected();
        if (vpn_enabled) {
            vpn_connect_task_start();
        }
        xEventGroupSetBits(wifi_event_group, WIFI_CONNECTED_BIT);
    }
}

static void wifi_ap_event_handler(void* arg, esp_event_base_t event_base,
                                   int32_t event_id, void* event_data)
{
    if (event_id == WIFI_EVENT_AP_START) {
        ESP_LOGI(TAG, "AP started");
        init_ap_netif_hooks();
    } else if (event_id == WIFI_EVENT_AP_STACONNECTED) {
        wifi_event_ap_staconnected_t* event = (wifi_event_ap_staconnected_t*) event_data;

        /* Check if this MAC is blacklisted (reservation with IP 0.0.0.0), or
         * unknown while "known clients only" is on */
        if (is_mac_blocked(event->mac)) {
            const char* name = lookup_device_name_by_mac(event->mac);
            ESP_LOGW(TAG, "Blocked client: %02X:%02X:%02X:%02X:%02X:%02X%s%s",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     name ? " (" : "", name ? name : "");
            esp_wifi_deauth_sta(event->aid);
            return;
        }

        connect_count++;
        client_stats_on_connect(event->mac);
        const char* name = lookup_device_name_by_mac(event->mac);
        if (name) {
            ESP_LOGI(TAG, "Client connected: %02X:%02X:%02X:%02X:%02X:%02X (%s) - %d total",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     name, connect_count);
        } else {
            ESP_LOGI(TAG, "Client connected: %02X:%02X:%02X:%02X:%02X:%02X - %d total",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     connect_count);
        }
    } else if (event_id == WIFI_EVENT_AP_STADISCONNECTED) {
        wifi_event_ap_stadisconnected_t* event = (wifi_event_ap_stadisconnected_t*) event_data;
        /* Blocked MACs are deauthed on connect without ever being counted, and
         * that deauth raises this event. Decrement only for clients that were
         * counted on connect — asking is_mac_blocked() here instead would miss
         * clients blocked (or made unknown) while connected. */
        if (client_stats_on_disconnect(event->mac) && connect_count > 0) {
            connect_count--;
        }
        const char* name = lookup_device_name_by_mac(event->mac);
        if (name) {
            ESP_LOGI(TAG, "Client disconnected: %02X:%02X:%02X:%02X:%02X:%02X (%s) - %d remain",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     name, connect_count);
        } else {
            ESP_LOGI(TAG, "Client disconnected: %02X:%02X:%02X:%02X:%02X:%02X - %d remain",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     connect_count);
        }
    }
}
#else

#if WIFI_HAS_5GHZ
/**
 * Band-aware STA connection helper.
 *
 * When a band preference is configured (sta_band == STA_BAND_2G or STA_BAND_5G),
 * this function scans for the configured SSID, selects the best BSSID on the
 * preferred band, and sets it in the STA config before connecting.
 * Falls back to the other band if the preferred one is unavailable.
 *
 * When sta_band == STA_BAND_AUTO (or on non-5GHz chips) this just calls
 * esp_wifi_connect() directly.
 */
static void wifi_connect_band_aware(void)
{
    if (sta_band == STA_BAND_AUTO || ssid == NULL || ssid[0] == '\0') {
        esp_wifi_connect();
        return;
    }

    /* Targeted scan for our SSID only */
    wifi_scan_config_t scan_cfg = {
        .ssid = (uint8_t *)ssid,
        .bssid = NULL,
        .channel = 0,
        .show_hidden = true,
        .scan_type = WIFI_SCAN_TYPE_ACTIVE,
    };

    esp_err_t err = esp_wifi_scan_start(&scan_cfg, true);  /* blocking */
    if (err != ESP_OK) {
        ESP_LOGW(TAG, "Band-aware scan failed (%s), falling back", esp_err_to_name(err));
        esp_wifi_connect();
        return;
    }

    uint16_t ap_count = 0;
    esp_wifi_scan_get_ap_num(&ap_count);
    if (ap_count == 0) {
        ESP_LOGI(TAG, "No APs found for SSID '%s', connecting normally", ssid);
        esp_wifi_connect();
        return;
    }

    wifi_ap_record_t *ap_list = malloc(sizeof(wifi_ap_record_t) * ap_count);
    if (ap_list == NULL) {
        esp_wifi_connect();
        return;
    }
    esp_wifi_scan_get_ap_records(&ap_count, ap_list);

    /* Find best BSSID on preferred band, and best on any band as fallback */
    int best_preferred = -1;
    int best_fallback = -1;
    for (int i = 0; i < ap_count; i++) {
        bool is_5g = (ap_list[i].primary > 14);
        bool matches_pref = (sta_band == STA_BAND_5G) ? is_5g : !is_5g;

        if (matches_pref) {
            if (best_preferred < 0 || ap_list[i].rssi > ap_list[best_preferred].rssi)
                best_preferred = i;
        } else {
            if (best_fallback < 0 || ap_list[i].rssi > ap_list[best_fallback].rssi)
                best_fallback = i;
        }
    }

    int chosen = (best_preferred >= 0) ? best_preferred : best_fallback;
    if (chosen < 0) {
        free(ap_list);
        esp_wifi_connect();
        return;
    }

    if (best_preferred < 0) {
        ESP_LOGW(TAG, "Preferred band (%s) unavailable, falling back to %s",
                 (sta_band == STA_BAND_5G) ? "5 GHz" : "2.4 GHz",
                 (sta_band == STA_BAND_5G) ? "2.4 GHz" : "5 GHz");
    }

    ESP_LOGI(TAG, "Connecting to BSSID %02X:%02X:%02X:%02X:%02X:%02X (ch %d, %s, %d dBm)",
             ap_list[chosen].bssid[0], ap_list[chosen].bssid[1],
             ap_list[chosen].bssid[2], ap_list[chosen].bssid[3],
             ap_list[chosen].bssid[4], ap_list[chosen].bssid[5],
             ap_list[chosen].primary,
             ap_list[chosen].primary > 14 ? "5 GHz" : "2.4 GHz",
             ap_list[chosen].rssi);

    /* Update STA config with the chosen BSSID */
    wifi_config_t sta_cfg;
    esp_wifi_get_config(WIFI_IF_STA, &sta_cfg);
    memcpy(sta_cfg.sta.bssid, ap_list[chosen].bssid, 6);
    sta_cfg.sta.bssid_set = true;
    sta_cfg.sta.channel = ap_list[chosen].primary;
    esp_wifi_set_config(WIFI_IF_STA, &sta_cfg);

    free(ap_list);
    esp_wifi_connect();
}
#endif /* WIFI_HAS_5GHZ */

static inline void sta_connect(void)
{
#if WIFI_HAS_5GHZ
    wifi_connect_band_aware();
#else
    esp_wifi_connect();
#endif
}

static void sta_reconnect_timer_cb(void* arg)
{
    ESP_LOGI(TAG, "reconnect backoff expired (%"PRIu32" ms), attempting STA connect", sta_reconnect_delay_ms);
    sta_connect();
    /* Double the delay for next time, capped at max */
    if (sta_reconnect_delay_ms < STA_RECONNECT_MAX_MS) {
        sta_reconnect_delay_ms *= 2;
        if (sta_reconnect_delay_ms > STA_RECONNECT_MAX_MS) {
            sta_reconnect_delay_ms = STA_RECONNECT_MAX_MS;
        }
    }
}

static void sta_schedule_reconnect(void)
{
    /* Stop any pending reconnect timer before starting a new one */
    esp_timer_stop(sta_reconnect_timer);
    ESP_LOGI(TAG, "scheduling STA reconnect in %"PRIu32" ms", sta_reconnect_delay_ms);
    esp_timer_start_once(sta_reconnect_timer, (uint64_t)sta_reconnect_delay_ms * 1000);
}

static void wifi_event_handler(void* arg, esp_event_base_t event_base,
                                int32_t event_id, void* event_data)
{
    esp_netif_dns_info_t dns;

    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START)
    {
        sta_connect();
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED)
    {
        ESP_LOGI(TAG,"disconnected - retry to connect to the AP");
        if (vpn_connected) {
            vpn_disconnect();
        }
        ap_connect = false;
        if (wifi_scan_active) {
            ESP_LOGI(TAG, "scan in progress - deferring reconnect");
        } else {
            sta_schedule_reconnect();
        }
        xEventGroupClearBits(wifi_event_group, WIFI_CONNECTED_BIT);
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_SCAN_DONE)
    {
        if (wifi_scan_active) {
            /* Just clear the flag — don't reconnect here.
             * Reconnection is handled by the caller (CLI after reading results,
             * or the disconnect handler once wifi_scan_active is cleared). */
            wifi_scan_active = false;
            ESP_LOGI(TAG, "scan complete");
        }
    }
    else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP)
    {
        ip_event_got_ip_t* event = (ip_event_got_ip_t*) event_data;
        ESP_LOGI(TAG, "got ip:" IPSTR, IP2STR(&event->ip_info.ip));
        /* Reset backoff on successful connection */
        sta_reconnect_delay_ms = STA_RECONNECT_INITIAL_MS;
        esp_timer_stop(sta_reconnect_timer);
        ap_connect = true;
        my_ip = event->ip_info.ip.addr;
        /* Re-enable NAPT here in case the AP cycled (channel change from
         * band-aware scan) after the initial ip_napt_enable in app_main.
         * Must precede the portmap restore: ip_portmap_add() is a silent
         * no-op until NAPT has allocated its tables. */
        if (ap_nat_enabled)
            ip_napt_enable(my_ap_ip, 1);
        delete_portmap_tab();
        apply_portmap_tab();
        const char *eff_dns = effective_ap_dns();
        if (eff_dns) {
            dns.ip.u_addr.ip4.addr = esp_ip4addr_aton(eff_dns);
            dns.ip.type = ESP_IPADDR_TYPE_V4;
            esp_netif_set_dns_info(wifiAP, ESP_NETIF_DNS_MAIN, &dns);
            ESP_LOGI(TAG, "AP DNS set to %s", eff_dns);
        } else if (esp_netif_get_dns_info(wifiSTA, ESP_NETIF_DNS_MAIN, &dns) == ESP_OK) {
            esp_netif_set_dns_info(wifiAP, ESP_NETIF_DNS_MAIN, &dns);
            ESP_LOGI(TAG, "set dns to:" IPSTR, IP2STR(&(dns.ip.u_addr.ip4)));
        }

        // esp_netif just (re)set netif_default to the uplink on this GOT_IP. If
        // the VPN is up in route-all mode, restore the tunnel as the default
        // route so forwarded traffic keeps going through WireGuard across DHCP
        // lease renewals and uplink reconnects.
        vpn_reassert_default_route();

        // Initialize byte counter after getting IP (interface is ready)
        init_byte_counter();

        // Start SNTP time synchronization
        init_sntp_if_needed();

        // Re-resolve syslog server now that network is up
        syslog_notify_connected();

        // Start VPN connection if enabled
        if (vpn_enabled) {
            vpn_connect_task_start();
        }

        xEventGroupSetBits(wifi_event_group, WIFI_CONNECTED_BIT);
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_AP_START)
    {
        ESP_LOGI(TAG, "AP started");
        // Initialize AP netif hooks now that interface is ready
        init_ap_netif_hooks();
        /* Re-enable NAPT on every AP start: covers the initial start and any
         * restart caused by the band-aware scan forcing a channel change. */
        if (ap_nat_enabled && my_ap_ip != 0)
            ip_napt_enable(my_ap_ip, 1);
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_AP_STACONNECTED)
    {
        wifi_event_ap_staconnected_t* event = (wifi_event_ap_staconnected_t*) event_data;

        /* Check if this MAC is blacklisted (reservation with IP 0.0.0.0), or
         * unknown while "known clients only" is on */
        if (is_mac_blocked(event->mac)) {
            const char* name = lookup_device_name_by_mac(event->mac);
            ESP_LOGW(TAG, "Blocked client: %02X:%02X:%02X:%02X:%02X:%02X%s%s",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     name ? " (" : "", name ? name : "");
            esp_wifi_deauth_sta(event->aid);
            return;
        }

        connect_count++;
        client_stats_on_connect(event->mac);

        /* Look up device name from DHCP reservations */
        const char* name = lookup_device_name_by_mac(event->mac);
        if (name) {
            ESP_LOGI(TAG, "Client connected: %02X:%02X:%02X:%02X:%02X:%02X (%s) - %d total",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     name, connect_count);
        } else {
            ESP_LOGI(TAG, "Client connected: %02X:%02X:%02X:%02X:%02X:%02X - %d total",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     connect_count);
        }
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_AP_STADISCONNECTED)
    {
        wifi_event_ap_stadisconnected_t* event = (wifi_event_ap_stadisconnected_t*) event_data;
        /* Blocked MACs are deauthed on connect without ever being counted, and
         * that deauth raises this event. Decrement only for clients that were
         * counted on connect — asking is_mac_blocked() here instead would miss
         * clients blocked (or made unknown) while connected. */
        if (client_stats_on_disconnect(event->mac) && connect_count > 0) {
            connect_count--;
        }

        /* Look up device name from DHCP reservations */
        const char* name = lookup_device_name_by_mac(event->mac);
        if (name) {
            ESP_LOGI(TAG, "Client disconnected: %02X:%02X:%02X:%02X:%02X:%02X (%s) - %d remain",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     name, connect_count);
        } else {
            ESP_LOGI(TAG, "Client disconnected: %02X:%02X:%02X:%02X:%02X:%02X - %d remain",
                     event->mac[0], event->mac[1], event->mac[2],
                     event->mac[3], event->mac[4], event->mac[5],
                     connect_count);
        }
    }
}
#endif

void ap_set_enabled(bool enabled)
{
#if CONFIG_ETH_UPLINK
    if (enabled) {
        esp_wifi_start();
        if (ap_nat_enabled) {
            ip_napt_enable(my_ap_ip, 1);
            /* Portmaps restored while NAPT was off were dropped; re-add them */
            delete_portmap_tab();
            apply_portmap_tab();
        }
    } else {
        connect_count = 0;
        esp_wifi_stop();
    }
#else
    if (enabled) {
        esp_wifi_set_mode(WIFI_MODE_APSTA);
        if (ap_nat_enabled) {
            ip_napt_enable(my_ap_ip, 1);
            /* Portmaps restored while NAPT was off were dropped; re-add them */
            delete_portmap_tab();
            apply_portmap_tab();
        }
    } else {
        connect_count = 0;
        esp_wifi_set_mode(WIFI_MODE_STA);
    }
#endif
    ap_disabled = !enabled;
    set_config_param_int("ap_disabled", ap_disabled ? 1 : 0);
    ESP_LOGI(TAG, "AP interface %s", enabled ? "enabled" : "disabled");
}

static wifi_auth_mode_t get_ap_authmode(void)
{
    switch (ap_authmode) {
        case 1: return WIFI_AUTH_WPA2_PSK;
        case 2: return WIFI_AUTH_WPA3_PSK;
        default: return WIFI_AUTH_WPA2_WPA3_PSK;
    }
}

void app_main(void)
{
    initialize_nvs();

#if CONFIG_STORE_HISTORY
    initialize_filesystem();
#endif

    initialize_console();

    /* Register console commands */
    esp_console_register_our_system_commands();
    esp_console_register_our_router_commands();

    /* Read persistent configuration parameters from NVS */
    get_config_param();

    /* Create background LED & button management thread */
    pthread_t thread;
    pthread_create(&thread, NULL, led_status_thread, NULL);

    /* Initialize HTTP Web Server */
    start_webserver();

    /* Spawn custom DNS server task for domain blocking and captive portal redirection */
    xTaskCreate(dns_server_task, "dns_server_task", 4096, NULL, 5, NULL);
}
