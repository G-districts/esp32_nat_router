#include <string.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "lwip/sockets.h"
#include "esp_log.h"

#define BLOCKED_DOMAIN "example.com"
static const char *TAG = "DNS_SPOOF";

void dns_server_task(void *pvParameters) {
    uint8_t rx_buffer[512];
    uint8_t tx_buffer[512];
    struct sockaddr_in listen_addr, client_addr;
    socklen_t addr_len = sizeof(client_addr);

    int sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP);
    if (sock < 0) {
        ESP_LOGE(TAG, "Failed to create UDP socket");
        vTaskDelete(NULL);
        return;
    }

    listen_addr.sin_family = AF_INET;
    listen_addr.sin_port = htons(53);
    listen_addr.sin_addr.s_addr = htonl(INADDR_ANY);

    if (bind(sock, (struct sockaddr *)&listen_addr, sizeof(listen_addr)) < 0) {
        ESP_LOGE(TAG, "Failed to bind UDP socket on port 53");
        close(sock);
        vTaskDelete(NULL);
        return;
    }

    ESP_LOGI(TAG, "DNS Interceptor server running on UDP port 53");

    while (1) {
        int len = recvfrom(sock, rx_buffer, sizeof(rx_buffer), 0, (struct sockaddr *)&client_addr, &addr_len);
        if (len < 12) continue; // Skip malformed packets

        char *domain_ptr = (char *)&rx_buffer[12];

        // Redirect blocked domain requests to ESP32 Gateway (192.168.4.1)
        if (strstr(domain_ptr, BLOCKED_DOMAIN) != NULL) {
            memcpy(tx_buffer, rx_buffer, len);
            tx_buffer[2] = 0x81; // Flags: Standard response, No error
            tx_buffer[3] = 0x80;
            tx_buffer[6] = 0x00; // Answer count = 1
            tx_buffer[7] = 0x01;

            int resp_len = len;
            const uint8_t answer_meta[] = { 
                0xc0, 0x0c,             // Pointer to domain name in query
                0x00, 0x01,             // Type: A record
                0x00, 0x01,             // Class: IN
                0x00, 0x00, 0x00, 0x3c, // TTL: 60 seconds
                0x00, 0x04              // Data length: 4 bytes (IPv4)
            };
            memcpy(&tx_buffer[resp_len], answer_meta, sizeof(answer_meta));
            resp_len += sizeof(answer_meta);

            // Append 192.168.4.1
            tx_buffer[resp_len++] = 192;
            tx_buffer[resp_len++] = 168;
            tx_buffer[resp_len++] = 4;
            tx_buffer[resp_len++] = 1;

            sendto(sock, tx_buffer, resp_len, 0, (struct sockaddr *)&client_addr, addr_len);
        }
    }
}
