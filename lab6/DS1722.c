/*_____________________________________________________

Functions for the DS1722 temperature sensor
_______________________________________________________
*/

#include "DS1722.h"
#include "STM32L432KC_GPIO.h"

/*_____________________________________________________

Function to calculate temperature from value given back.
_______________________________________________________
*/
float numtotemp(uint8_t MSB, uint8_t LSB) {
    int16_t rawTemp = ((MSB << 8) | LSB) >> 4;  // make it in the format a 12 bit value would be.
    if (rawTemp & 0x0800) rawTemp |= 0xF000;    // Fill upper bits for negative values
    float temp = rawTemp * 0.0625f; // since it is in a 12 bit format, we use the 12 bit temperature formula
    return temp;
}

/*_____________________________________________________

Sets up the DS1722 temperature sensor
_______________________________________________________
*/
void setupDS(char byteS){
  digitalWrite(SPI_CE, 1);
  spiSendReceive(0x80); 
  spiSendReceive(byteS);
  digitalWrite(SPI_CE, 0);
  }

/*_____________________________________________________

Function to read configuration register
_______________________________________________________
*/
uint8_t configread(void){
    uint8_t config;
    digitalWrite(SPI_CE, 1);
    spiSendReceive(0x00);          // read config command
    config = spiSendReceive(0x00); // dummy to clock out config
    digitalWrite(SPI_CE, 0);
    return config;
}
/*_____________________________________________________

Function to read from the the MSB
_______________________________________________________
*/
uint8_t MSBread(void){
    uint8_t msb;
    digitalWrite(SPI_CE, 1);
    spiSendReceive(0x02);        // read MSB addr
    msb = spiSendReceive(0x00);  // dummy to clock out
    digitalWrite(SPI_CE, 0);
    return msb;

  }

/*_____________________________________________________

Function to read the lsb
_______________________________________________________
*/
uint8_t LSBread(void){
    uint8_t lsb;
    digitalWrite(SPI_CE, 1);
    spiSendReceive(0x01);        // read MSB addr
    lsb = spiSendReceive(0x00);  // dummy to clock out
    digitalWrite(SPI_CE, 0);
    return lsb;
}





