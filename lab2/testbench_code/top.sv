/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file combines both tasks for lab1
*/
module top(
	input 	logic [3:0] s1, s2,
	input   logic [31:0] counter, //uncomment for testbench
	output 	logic [1:0] disps,
	output  logic [6:0] number,
	output  logic [4:0] leds
);
logic [3:0] sout;
leds_co leds_co(s1[3:0], s2[3:0],/**/ counter[31:0],/*uncomment for testbench*/ disps, sout[3:0], leds[4:0]);
lab1_co lab1_co(sout[3:0], number[6:0]);
endmodule