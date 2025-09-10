/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file does and and and xor operatioon on 4 switches and also makes a 2.4Hz blinking LED.
*/
module leds_co(
	input 	logic [3:0] s,
	output 	logic fpga_blink_out, led00, led10
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
			counter <= counter + 215; //107 * 48,000,000 ~= 2.4 * 2^30, so a 2.4Hz square wave
		end
  assign fpga_blink_out = counter[31];
  
  assign led00 = s[0] ^ s[1]; //xor
  assign led10 = s[2] & s[3]; //and

endmodule