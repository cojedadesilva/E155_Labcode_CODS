/*
by Carlos Ojeda de Silva, September 17 2025
cojedadesilva@g.hmc.edu
This file combines SEVEN SEGMENT LOGIC WITH THE SWITCHING AND KEYPAD
*/
module top(
	input 	reset,
	input logic [3:0] col,
	output logic [3:0] row,
	output 	logic [1:0] disps,
	output  logic [6:0] number 
);
	logic [31:0] counter;
	logic [3:0] sout;
	clock clock(reset, counter); //comment for tb
	leds_co leds_co(reset, counter, col, row, sout, disps);
	sevseg sevseg(sout[3:0], number[6:0]);
endmodule