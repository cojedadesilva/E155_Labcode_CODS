/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file tests the possible values and the expected outputs
*/

module testbench_ledlogic();
logic reset;
logic [31:0] counter;
logic [3:0] col, row, colsh, sout;
logic [1:0] disps;

logic [4:0] rowcheck = 0;
// These variables or signals represent 3 inputs, 2 outputs, 2 expected 
`timescale 1 ns / 1 ns
// outputs, respectively.
leds_co dut(reset, counter, col, row, sout, disps);

always
begin
#10; 
counter <= counter + 1048577; //2^20 + 1 bc it has to be odd
end
always @(negedge counter[25]) begin
if (~colsh[3]) colsh = colsh << 1;
else colsh = 1;
end


property col_async; //N1 maping is correct
    @(posedge counter[23]) disable iff (~reset) ((dut.savecol == col) || (col == 0) || (dut.savecol == 0));
endproperty

assert property (col_async)
    $display("PASSED! Got savecol = %b when col was %b during counter[23] rising edge", dut.savecol, col);  
else 
    $error("FAILED!...");



//posedge counter[21] check if number matchess expected
property N_right_side;
    @(posedge dut.counter[21]) disable iff (~reset) (sout == dut.N1*disps[0] + dut.N2*disps[1]);
endproperty

assert property (N_right_side)
    $display("PASSED! Got sout = %b when N1 was %h , N2 was %h and disps was %b", sout, dut.N1, dut.N2, disps);  
else 
    $error("FAILED!...");

initial
begin
counter = 0;
col = 8;
reset=0; #85; 
reset=1;
end
always @(posedge dut.counter[0])
begin
if (rowcheck[4:1] == counter[24:21]) begin
	col = 0;
	rowcheck = rowcheck - 1;
	end
	else col = colsh;


#1;
end
always @(negedge counter[0])
if (reset) begin
end
endmodule