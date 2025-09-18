/*
by Carlos Ojeda de Silva, September 16 2025
cojedadesilva@g.hmc.edu
This file controls the timing in the top module by changing the counter value, we can consistently use index 0 for clock.
*/
module clock(
input logic reset,
output logic [31:0] counter
);
logic int_osc;
HSOSC hf_osc (.CLKHFPU(1'b1), .CLKHFEN(1'b1), .CLKHF(int_osc));//comment for tb
	always_ff @(posedge int_osc)
		begin
			counter = counter + 215; 
			//if (~reset) counter = 0;
		end
endmodule