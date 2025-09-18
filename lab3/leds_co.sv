/*
by Carlos Ojeda de Silva, September 16 2025
cojedadesilva@g.hmc.edu
This file controls the LED 7 segment display switching, helps with button stability (asynchronous), and calls the keydecoder
*/
module leds_co(
	input reset,
	input logic [31:0] counter,
	input logic [3:0] col,
	output logic [3:0] row,
	output logic [3:0] sout,
	output logic [1:0] disps
);
	logic [3:0] savecol;
	logic [3:0] N1;
	logic [3:0] N2;
	keydec keydec(reset, savecol, counter[25:23], N1, N2);
	assign sout = counter[22] ? N1 : N2;
	assign disps[0] = counter[22];
	assign disps[1] = ~counter[22]; 
	always_ff @(posedge counter[21])
		begin
			savecol = col;
		end
	assign row = 1'b1 << counter[25:24];
endmodule