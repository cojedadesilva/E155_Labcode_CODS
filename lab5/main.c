/*
Carlos Ojeda de Silva
cojedadesilva@g.hmc.edu
Oct 8 2025
This code will run a Timer for 1 second to update on the calculated RPS value, basd on the amount of pulses read on a time interval.
*/

#include <stdio.h>
#include <stm32l432xx.h>
#include "STM32L432KC.h"

//PA1 and PA2 can use different interrupts, which makes code a bit easier
#define ENCODER1 PA1
#define ENCODER2 PA2 
#define TIM TIM2 //using timer 2
#define ARRtim2 499 //counts to 1000 ms.

//Variables to be used
volatile int print = 0; //0 for no, 1 for yes
volatile int last = 0; //for test
volatile float Count = 0; //start edge counter at 0
volatile float PPR = 408; //defined as float since we will use them for a floating point calculation Pulses per revolution
volatile float CPR = 1632;  //defined as 4*PPR to ensure we read all 4 edges of each count
volatile int lastPin; //tracks who generated the last edge, 0 for PA1, 1 for PA2
volatile int dir = 0; //0 or 1 depending if going clockwise or counterclockwise
volatile float RPS; //revolutions per second


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


void EXTI1_IRQHandler(void) {  // Interrupt on PA1
      if(EXTI->PR1 & (1<<1)){
        EXTI->PR1 |= (1 << 1);  // Clear interrupt flag
        dir = !(dir ^ lastPin); //really lastpin is xor(lastpin,currentpin), where current pin depends if the edge was in PA1 or PA2, so no ! ahead to adjust for this
        Count += (2*(dir)-1); //adds 1 if dir = 0 and -1 if dir = 1
        lastPin = 0; //0 means that the last interrupt came from PA1, 1 means PA2
  }
}

void EXTI2_IRQHandler(void) {  // Interrupt on PA2 
      if(EXTI->PR1 & (1<<2)){
        EXTI->PR1 |= (1 << 2);  // Clear interrupt flag
        dir = (dir ^ lastPin);//really lastpin is xor(lastpin,currentpin), where current pin depends if the edge was in PA1 or PA2, so ! ahead to adjust for this
        Count += (2*(dir)-1); //adds 1 if dir = 0 and -1 if dir = 1
        lastPin = 1; //0 means that the last interrupt came from PA1, 1 means PA2
  }
}


void TIM2_IRQHandler(void){
  if(TIM->SR & 1){
    TIM->SR &= ~(0x1); // Clear interrupt flag
    TIM->CNT = 0;      // Reset counter
    print = 1;
  }
} 

// Print
int _write(int file, char *ptr, int len) {
  int i = 0;
  for (i = 0; i < len; i++) {
    ITM_SendChar((*ptr++));
  }
  return len;
}

//in this code, we will only test PA1 (interrupts) and PA7 (pulling)
int main(void) {
  setupGPIO();
  setuptimer();
  dir = (digitalRead(ENCODER1) ^ digitalRead(ENCODER2));
  volatile int lastPin = (digitalRead(ENCODER1) ^ digitalRead(ENCODER2)); //Gets initial readings
  setupintr();
  while(1){
    RPS = Count / (CPR*(ARRtim2+1) / 1000); //calculate RPS by the formula (Pulses/(seconds TIM2 counted))
    if(print){
      printf("Interrupt:  %f RPS\n", RPS); //print last calculated RPS value
      Count = 0; //reset count so it only check pulses in the measured period
      print = 0; //print only once
    }  
  }
}

