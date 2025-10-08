//PA1 and PA2 can use different interrupts, which makes code a bit easier
#ifndef LAB5_H
#define LAB5_H


#include "STM32L432KC_GPIO.h"
#include "STM32L432KC_RCC.h"
#include "STM32L432KC_TIM.h"
#include "STM32L432KC_FLASH.h"
#include "STM32L432KC_USART.h"
#include "STM32L432KC_SPI.h"]

#define ENCODER1 PA1
#define ENCODER2 PA2 
#define TIM TIM2 //using timer 2
#define ARRtim2 499 //counts to 499+1 ms.
#define MOTORCPR 1632 //408 * 4


void setuptimer(void);
void setupGPIO(void);
void setupintr(void);
int _write(int file, char *ptr, int len);

#endif