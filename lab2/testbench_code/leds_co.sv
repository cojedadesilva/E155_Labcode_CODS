/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file does and and and xor operatioon on 4 switches and also makes a 2.4Hz blinking LED.
*/
module leds_co(
	input logic [3:0] s1, s2,
	input logic [31:0] counter, //uncomment for testbench
	output 	logic [1:0] disps,
	output logic [3:0] sout,
	output logic [4:0] leds
);

	logic int_osc;
	logic pulse; 
	logic led_state = 0;
	//logic [31:0] counter = 0; //comment for testbench
	
	// Internal high-speed oscillator 
	HSOSC hf_osc (.CLKHFPU(1'b1), .CLKHFEN(1'b1), .CLKHF(int_osc));
	
	// Simple clock divider
	/*
	always_ff @(posedge int_osc) //comment for testbench
		begin
			counter <= counter + 215; 
			if (counter[21]) sout = s1;
			if (~counter[21]) sout = s2;
			leds = s1 + s2;
		end //*/
  assign disps[0] = counter[21];
  assign disps[1] = ~counter[21];
  //*
  always @(*) begin
  if (counter[21]) sout = s2; //uncomment for testbench
  if (~counter[21]) sout = s1;
  leds = s1 + s2;
  end
  //*/
  
  
endmodule