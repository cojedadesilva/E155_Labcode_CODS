/*
by Carlos Ojeda de Silva, September 10 2025
cojedadesilva@g.hmc.edu
This file combines both tasks for lab2
*/
module top(
	input 	logic [3:0] s1, s2,
	output 	logic [1:0] fpga_blink_out,
	output  logic [6:0] number,
	output  logic [4:0] leds
);
logic [3:0] sout;
leds_co leds_co(s1[3:0], s2[3:0], fpga_blink_out, sout[3:0], leds[4:0]);
lab1_co lab1_co(sout[3:0], number[6:0]);
endmodule