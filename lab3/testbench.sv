/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file tests the possible values and the expected outputs
*/

module testbench();
logic reset;
logic [3:0] col, row, colsh;
logic [1:0] disps;
logic [6:0] number;

logic [4:0] rowcheck = 0;
// These variables or signals represent 3 inputs, 2 outputs, 2 expected 
`timescale 1 ns / 1 ns
// outputs, respectively.
top dut(reset, col, row, disps, number);

logic [6:0] expected [0:15] = '{
    7'b1001111, // 0
    7'b0010010, // 1
    7'b0000110, // 2
    7'b0001000, // 3
    7'b1001100, // 4
    7'b0100100, // 5
    7'b0100000, // 6
    7'b1100000, // 7
    7'b0001111, // 8
    7'b0000000, // 9
    7'b0000100, // A
    7'b0110001, // B
    7'b1000010, // C
    7'b0000001, // D
    7'b0110000, // E
    7'b0111000  // F
    };



always
begin
#10; 
dut.counter<=dut.counter + 1048577; //2^20 + 1 bc it has to be odd
end
always @(negedge dut.counter[25]) begin
if (~colsh[3]) colsh = colsh << 1;else colsh = 1;
end

property N1_matchescoord;
    @(posedge dut.leds_co.keydec.pressed) disable iff (~reset) $past(dut.leds_co.N1) inside {dut.leds_co.N2};
endproperty

assert property (N1_matchescoord)
    $display("PASSED! Got N2 = %h when N1 was %h last cycle", dut.leds_co.N2, dut.leds_co.N2);  
else 
    $error("FAILED!...");

property N1_mapping; //N1 maping is correct
    @(posedge dut.leds_co.keydec.pressed) disable iff (~reset) dut.leds_co.N1 == $past({dut.counter[25:24],dut.leds_co.keydec.coln});
endproperty

assert property (N1_mapping)
    $display("PASSED! Got N1 = %b when counter was %b and coln was %b", dut.leds_co.N1, dut.counter[25:23], dut.leds_co.keydec.coln);  
else 
    $error("FAILED!...");

//posedge counter[21] check if number matchess expected
property N_right_side;
    @(posedge dut.counter[21]) disable iff (~reset) (number == expected[dut.leds_co.N1]*disps[0] + expected[dut.leds_co.N2]*disps[1]);
endproperty

assert property (N_right_side)
    $display("PASSED! Got number = %b when N1 was %h , N2 was %h and disps was %b", number, dut.leds_co.N1, dut.leds_co.N2, disps);  
else 
    $error("FAILED!...");

initial
begin
dut.counter = 0;
col = 8;
reset=0; #85; 
reset=1;
end
always @(posedge dut.counter[0])
begin
if (rowcheck[4:1] == dut.counter[24:21]) begin
	col = 0;
	rowcheck = rowcheck - 1;
	end
	else col = colsh;


#1;
end
always @(negedge dut.counter[0])
if (reset) begin
end
endmodule