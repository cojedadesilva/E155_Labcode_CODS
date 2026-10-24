/*_____________________________________________________

DS1722.h
Oct 25 2025
cojedadesilva@g.hmc.edu
Carlos Ojeda de Silva
_______________________________________________________
*/

#ifndef DS1722_H
#define DS1722_H

#include <stdint.h>
#include <stm32l432xx.h>
#include "STM32L432KC.h"

///////////////////////////////////////////////////////////////////////////////
// Function prototypes
///////////////////////////////////////////////////////////////////////////////

void setupDS(char byteS);
uint8_t MSBread(void);
float numtotemp(uint8_t MSB, uint8_t LSB);
uint8_t LSBread(void);
uint8_t configread(void);

#endif