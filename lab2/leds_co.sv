/*
by Carlos Ojeda de Silva, September 10 2025
cojedadesilva@g.hmc.edu
This file controls which 7 segment display is used with the corresponding s values. It also outputs the sum of 2 numbers in binary with 5 leds
*/
module leds_co(
	input logic [3:0] s1, s2,
	output 	logic [1:0] fpga_blink_out,
	output logic [3:0] sout,
	output logic [4:0] leds
);

	logic int_osc;
	logic pulse; 
	logic led_state = 0;
	logic [31:0] counter = 0;
	
	// Internal high-speed oscillator 
	HSOSC hf_osc (.CLKHFPU(1'b1), .CLKHFEN(1'b1), .CLKHF(int_osc));
	
	// Simple clock divider
	
	always_ff @(posedge int_osc)
		begin
			counter <= counter + 215; //this value works
			if (counter[21]) sout = s1;
			if (~counter[21]) sout = s2; //using index 21 makes it around 2.6kHz, which is higher than human eye and slow enough for the transistor.
			leds = s1 + s2;
		end
  assign fpga_blink_out[0] = counter[21];
  assign fpga_blink_out[1] = ~counter[21];
endmodule