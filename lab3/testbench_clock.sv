/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file tests the possible values and the expected outputs
*/

module testbench_clock();
logic clk, reset;
logic [31:0] counter;

// These variables or signals represent 3 inputs, 2 outputs, 2 expected 
`timescale 1 ps / 1 ps
// outputs, respectively.
clock dut(reset, counter);

//// Generate clock.
always

begin
dut.int_osc=1;
#5; 
dut.int_osc=0;
#5;
end
//// Start of test. 
initial
begin
reset=0; #22; 
reset=1;
end
//// Check results on falling edge of clk.
endmodule