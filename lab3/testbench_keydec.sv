/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file tests the possible values and the expected outputs
*/

module testbench_keydec();
logic reset;
logic [3:0] col;
logic [4:0] counter;
logic [3:0] N1, N2;
logic [4:0] colsh;
logic [4:0] colcont;

// These variables or signals represent 3 inputs, 2 outputs, 2 expected 
`timescale 1 ns / 1 ns
// outputs, respectively.
keydec dut(reset, col, counter[2:0], N1, N2);

always
begin
#5; 
counter <= counter + 1;
end
always @(negedge counter[0]) begin
	
//if (colcont[4]) colcont = 0;
if (counter[2:1] == colcont[1:0]) begin //row = desired row to check
colcont[4] = 1;

if (~colsh[4]) colsh = colsh << 1; //1-2-3-4
else begin colsh = 1;
colcont[1:0] = colcont[1:0] + 1;
	end
end else colcont[4] = 0;
end


always @(negedge counter[0]) begin //if row is 1 for 4 times, then 2, etc...
if (colcont[4] == 0) col = colsh[4:1]; else col = 0;
end

property N1_matchescoord;
    @(posedge dut.pressed) disable iff (~reset) $past(N1) inside {N2};
endproperty

assert property (N1_matchescoord)
    $display("PASSED! Got N2 = %h when N1 was %h last cycle", N2, N2);  
else 
    $error("FAILED!...");


property N1_mapping; //N1 maping is correct
    @(posedge dut.pressed) disable iff (~reset) N1 == $past({counter[2:1],dut.coln});
endproperty

assert property (N1_mapping)
    $display("PASSED! Got N1 = %b when counter was %b and coln was %b", N1, counter[2:0], dut.coln);  
else 
    $error("FAILED!...");


initial
begin
counter = 0;
colsh = 1;
colcont = 5'b10000;
col = 8;
reset=0; #22; 
reset=1;
end
always @(posedge counter[0])
begin
#1;
end
always @(negedge counter[0])
if (reset) begin
end
endmodule