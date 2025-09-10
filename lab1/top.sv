/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file combines both tasks for lab1
*/
module top(
	input 	logic [3:0] s,
	output 	logic fpga_blink_out, led0, led1,
	output  logic [6:0] number
);
leds_co leds_co(s[3:0], fpga_blink_out, led0, led1);
lab1_co lab1_co(s[3:0], number[6:0]); 
endmodule