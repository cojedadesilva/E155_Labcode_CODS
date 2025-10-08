
#include <stdio.h>
#include <stm32l432xx.h>
#include "lab5.h"
#include "STM32L432KC.h"


void setuptimer(void){
    RCC->APB1ENR1 |= RCC_APB1ENR1_TIM2EN;// Enables timer2
    initTIM(TIM); // Initialize timer2 to 1ms ticks
    TIM->ARR = ARRtim2; //1000ms for 1 second overflows
    TIM->DIER |= TIM_DIER_UIE; //Enables overflow timer
    RCC->APB2ENR |= RCC_APB2ENR_SYSCFGEN; // Enable SYSCFG clock domain in RCC
}

void setupGPIO(void){
  // Setting up GPIO as PORT A (1 and 2 are 5 Volt tolerable and use different interrupt channels)
  gpioEnable(GPIO_PORT_A); //enable A pins for reading
  pinMode(ENCODER1, GPIO_INPUT);
  pinMode(ENCODER2, GPIO_INPUT);
}


void setupintr(void){
  SYSCFG->EXTICR[0] &= ~SYSCFG_EXTICR1_EXTI1; // Clear old value (precaution)
  SYSCFG->EXTICR[0] &= ~SYSCFG_EXTICR1_EXTI2;

  SYSCFG->EXTICR[0] |= _VAL2FLD(SYSCFG_EXTICR1_EXTI1, 0b000); // Select PA1
  SYSCFG->EXTICR[0] |= _VAL2FLD(SYSCFG_EXTICR1_EXTI2, 0b000); // Select PA2

  // Enable interrupts globally
   __enable_irq();

  //Configuring to be triggered during High/Low edges
  //Set up mask bit for PA1 and PA2
  EXTI->IMR1 |= (1 << gpioPinOffset(ENCODER1));
  EXTI->IMR1 |= (1 << gpioPinOffset(ENCODER2));
  //Detects Rising edge
  EXTI->RTSR1 |= (1 << gpioPinOffset(ENCODER1));
  EXTI->RTSR1 |= (1 << gpioPinOffset(ENCODER2));
  //Detects Falling Edge
  EXTI->FTSR1 |= (1 << gpioPinOffset(ENCODER1));
  EXTI->FTSR1 |= (1 << gpioPinOffset(ENCODER2));
   // We have 3 interrupts, PA1, PA2, and TIM2
  NVIC->ISER[0] |= (1 << EXTI1_IRQn);
  NVIC->ISER[0] |= (1 << EXTI2_IRQn);
  NVIC->ISER[0] |= (1 << TIM2_IRQn);
}

// Print
int _write(int file, char *ptr, int len) {
  int i = 0;
  for (i = 0; i < len; i++) {
    ITM_SendChar((*ptr++));
  }
  return len;
}
