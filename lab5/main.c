/*
Carlos Ojeda de Silva
cojedadesilva@g.hmc.edu
Oct 8 2025
This code will run a Timer for 1 second to update on the calculated RPS value, basd on the amount of pulses read on a time interval.
*/

#include <stdio.h>
#include <stm32l432xx.h>
#include "lab5.h"
#include "STM32L432KC.h"



//Variables to be used
volatile int print = 0; //0 for no, 1 for yes
volatile int last = 0; //for test
volatile int32_t Count = 0; //start edge counter at 0
volatile int lastPin; //tracks who generated the last edge, 0 for PA1, 1 for PA2
volatile int dir, switchdir; //0 or 1 depending if going clockwise or counterclockwise
volatile float RPS = 0; //revolutions per second


void EXTI1_IRQHandler(void) {  // Interrupt on PA1
      if(EXTI->PR1 & (1<<1)){
        EXTI->PR1 |= (1 << 1);  // Clear interrupt flag
        if (!switchdir) dir = !(dir ^ lastPin); //really lastpin is xor(lastpin,currentpin), where current pin depends if the edge was in PA1 or PA2, so no ! ahead to adjust for this
        lastPin = 0; //0 means that the last interrupt came from PA1, 1 means PA2
        Count += (2*(dir)-1); //adds 1 if dir = 0 and -1 if dir = 1
  }
}

void EXTI2_IRQHandler(void) {  // Interrupt on PA2 
      if(EXTI->PR1 & (1<<2)){
        EXTI->PR1 |= (1 << 2);  // Clear interrupt flag
        if (!switchdir) dir = (dir ^ lastPin);//really lastpin is xor(lastpin,currentpin), where current pin depends if the edge was in PA1 or PA2, so ! ahead to adjust for this
        lastPin = 1; //0 means that the last interrupt came from PA1, 1 means PA2
        Count += (2*(dir)-1); //adds 1 if dir = 0 and -1 if dir = 1
  }
}


void TIM2_IRQHandler(void){
  if(TIM->SR & 1){
    TIM->SR &= ~(0x1); // Clear interrupt flag
    TIM->CNT = 0;      // Reset counter
    print = 1;

  }
} 

//in this code, we will only test PA1 (interrupts) and PA7 (pulling)
int main(void) {
  setupGPIO();
  setuptimer();
  dir = 0;
  volatile int lastPin = (digitalRead(ENCODER1) ^ digitalRead(ENCODER2)); //Gets initial readings
  setupintr();
  while(1){
    RPS = (float)Count / ((float)MOTORCPR*(ARRtim2+1) / 1000);; //calculate RPS by the formula (Pulses/(seconds TIM2 counted))
    if(print){
      switchdir = (abs(RPS) > 2);
      printf("%f RPS\n", RPS); //print last calculated RPS value
      Count = 0; //reset count so it only check pulses in the measured period
      print = 0; //print only once
    }  
  }
}

