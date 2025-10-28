/*_____________________________________________________

main.c
Oct 25 2025
cojedadesilva@g.hmc.edu
Carlos Ojeda de Silva
gotten from code made by Josh Brake
_______________________________________________________
*/


#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include "main.h"
#include "DS1722.h"


/////////////////////////////////////////////////////////////////
// Provided Constants and Functions
/////////////////////////////////////////////////////////////////

//Defining the web page in two chunks: everything before the current time, and everything after the current time
char* webpageStart = "<!DOCTYPE html><html><head><title>E155 lab6 Webpage</title>\
	<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\
	</head>\
	<body><h1>E155 lab6 Webpage</h1>";
char* ledStr = "<p>LED Control:</p><form action=\"ledon\"><input type=\"submit\" value=\"Turn the LED on!\"></form>\
	<form action=\"ledoff\"><input type=\"submit\" value=\"Turn the LED off!\"></form>";
char* bitStr = "<p>Bit Resolution Control:</p><form action=\"8bit\"><input type=\"submit\" value=\"8 bits\"></form>\
	<form action=\"9bit\"><input type=\"submit\" value=\"9 bits\"></form>\
	<form action=\"10bit\"><input type=\"submit\" value=\"10 bits\"></form>\
	<form action=\"11bit\"><input type=\"submit\" value=\"11 bits\"></form>\
	<form action=\"12bit\"><input type=\"submit\" value=\"12 bits\"></form>";
char* webpageEnd   = "</body></html>";

//determines whether a given character sequence is in a char array request, returning 1 if present, -1 if not present
int inString(char request[], char des[]) {
	if (strstr(request, des) != NULL) {return 1;}
	return -1;
}

int updateLEDStatus(char request[])
{
	int led_status = 0;
	// The request has been received. now process to determine whether to turn the LED on or off
	if (inString(request, "ledoff")==1) {
		digitalWrite(LED_PIN, PIO_LOW);
		led_status = 0;
	}
	else if (inString(request, "ledon")==1) {
		digitalWrite(LED_PIN, PIO_HIGH);
		led_status = 1;
	}

	return led_status;
}
/////////////////////////////////////////////////////////////////
// Solution Functions
/////////////////////////////////////////////////////////////////

/*_____________________________________________________

Function to set resolution based on data received from website
_______________________________________________________
*/

int updatebitresStatus(char request[])
{
	int bitresstatus = 0;
	if (inString(request, "8bit")==1) {
		bitresstatus = 8;
                setupDS(0XE0); //sets resolution to 8 bits
	}
	else if (inString(request, "9bit")==1) {
		bitresstatus = 9;
                setupDS(0XE2); //sets resolution to 9 bits
	}
        else if (inString(request, "10bit")==1) {
		bitresstatus = 10;
                setupDS(0XE4); //sets resolution to 10 bits
	}
	else if (inString(request, "11bit")==1) {
		bitresstatus = 11;
                setupDS(0XE6); //sets resolution to 11 bits
	}
        else if (inString(request, "12bit")==1) {
		bitresstatus = 12;
                setupDS(0XE8); //sets resolution to 12 bits
	}
	return bitresstatus;
}

int main(void) {
  configureFlash();
  configureClock();
  gpioEnable(GPIO_PORT_A);
  gpioEnable(GPIO_PORT_B);
  gpioEnable(GPIO_PORT_C);
  pinMode(PB6, GPIO_OUTPUT);
  RCC->APB2ENR |= (RCC_APB2ENR_TIM15EN); //Tim15
  initTIM(TIM15);
  USART_TypeDef * USART = initUSART(USART1_ID, 125000);
  initSPI(0b100, 0, 1); //set clock divider to 2^4, which would be around 500kHz
  setupDS(0XE4); // Sets up as 10 bit resolution
  volatile uint8_t config;
  volatile uint8_t msb;
  volatile uint8_t lsb;
  volatile uint8_t resolution;
  resolution = 10; //using default of 10 bits
  while(1) {
    /* Wait for ESP8266 to send a request.
    Requests take the form of '/REQ:<tag>\n', with TAG begin <= 10 characters.
    Therefore the request[] array must be able to contain 18 characters.
    */
    // Receive web request from the ESP
    char request[BUFF_LEN] = "                  "; // initialize to known value
    int charIndex = 0;
    // Keep going until you get end of line character
    while(inString(request, "\n") == -1) {
    // Wait for a complete request to be transmitted before processing
      while(!(USART->ISR & USART_ISR_RXNE));
      request[charIndex++] = readChar(USART);
  }
    config = configread();
    msb = MSBread();
    lsb = LSBread();
    int led_status = updateLEDStatus(request); //get LED data
    resolution = updatebitresStatus(request); //get resolution data
    float temp = numtotemp(msb,  lsb);
    char tempStr[50];
    sprintf(tempStr,"TEMPERATURE IS %.4f C",temp);
    char resStr[50];
    sprintf(resStr,"Current resolution is %d bits",resolution);
    char ledStatusStr[20];
    if (led_status == 1)
      sprintf(ledStatusStr,"LED is on!");
    else if (led_status == 0)
      sprintf(ledStatusStr,"LED is off!");
    //// finally, transmit the webpage over UART
    sendString(USART, webpageStart); // webpage header code
    sendString(USART, ledStr); // LED buttons
    sendString(USART, bitStr); // resolution buttons
    sendString(USART, "<p>");
    sendString(USART, ledStatusStr); //LED is on or off?
    sendString(USART, "</p>");
    sendString(USART, "<h2>TEMPERATURE</h2>");
    sendString(USART, "<p>");
    sendString(USART, tempStr); //what is the current temperature?
    sendString(USART, "</p>");
    sendString(USART, "<h2>RESOLUTION</h2>");
    sendString(USART, "<p>");
    sendString(USART, resStr); //what is the current resolution?
    sendString(USART, "</p>");
    sendString(USART, webpageEnd);//end
  }
}