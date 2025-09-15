/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file tests the possible values and the expected outputs
*/

module testbench_sevseg();
logic clk, reset;
logic [3:0] s;
logic [6:0] number;
logic [6:0] expected;

logic [10:0] testvectors[15:0] = '{ //s[4] led0 led1 number[7]
11'b00000000001,
11'b00011001111,
11'b00100010010,
11'b00110000110,
11'b01001001100,
11'b01010100100,
11'b01100100000,
11'b01110001111,
11'b10000000000,
11'b10010000100,
11'b10100001000,
11'b10111100000,
11'b11000110001,
11'b11011000010,
11'b11100110000,
11'b11110111000};

// These variables or signals represent 3 inputs, 2 outputs, 2 expected 
`timescale 1 ps / 1 ps
// outputs, respectively.
logic [31:0] vectornum, errors;
// '[31:0]' indicates that the following signals, vectornum and errors 
// in this case, are 32-bit long (start from bit 0 to bit 31) in little 
// endian order (the least significant bit at the lowest address or 
// [msb:lsb]).
// vectornum shows the number of test vectors that has been applied.
// errors represents the number of errors found.
// The size of 'int' data type is 4 bytes, thus 32 bits. 
//logic [12:0] testvectors[17:0];
// Above is a 5-bit binary array named testvectors with index 0 to 10000 
//(testvectors[0],testvectors[1],testvectors[2],...,testvectors[10000]).
// In other words, testvectors contains 10001 elements, each of which is 
// a 5-bit binary number. The number of bits represent the sum of the 
// number of input and output bits (eg. three 1-bit inputs + two 1-bit 
// outputs = one 5-bit testvector). 
// In this tutorial, we will only 
// use 8 test vectors (found in .tv file below), however it doesnÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬ÃƒÂ¢Ã¢â‚¬Å¾Ã‚Â¢t hurt 
// to set up array to support more so we could easily add test vectors
// later. 
//// Instantiate device under test (DUT).
// Inputs: a, b, cin. Outputs: s, cout.
sevseg dut(s, number);
//// Generate clock.
always
// 'always' statement causes the statements in the block to be 
// continuously re-evaluated.
begin
 //// Create clock with period of 10 time units. 
// Set the clk signal HIGH(1) for 5 units, LOW(0) for 5 units 
clk=1; #5; 
clk=0; #5;
end
//// Start of test. 
initial
// 'initial' is used only in testbench simulation.
begin
//// Load vectors stored as 0s and 1s (binary) in .tv file.
//$readmemb("lab1tv.tv", testvectors);


// $readmemb reads binarys, $readmemh reads hexadecimals.
// Initialize the number of vectors applied & the amount of 
// errors detected.
vectornum=0; 
errors=0;
// Both signals hold 0 at the beginning of the test.
//// Pulse reset for 22 time units(2.2 cycles) so the reset 
// signal falls after a clk edge.
reset=1; #22; 
 reset=0;
// The signal starts HIGH(1) for 22 time units then remains 
// for the rest of the test.
end
//// Apply test vectors on rising edge of clk.
always @(posedge clk)
// Notice that this 'always' has the sensitivity list that controls when all
// statements in the block will start to be evaluated. '@(posedge clk)' means 
// at positive or rising edge of clock. 
begin
//// Apply testvectors 1 time unit after rising edge of clock to 
// avoid data changes concurrently with the clock.
#1;
//// Break the current 5-bit test vector into 3 inputs and 2 
// expected outputs.
//4 1 1 7 = 13
//{s, expected} = testvectors[vectornum][12:0];
s = testvectors[vectornum][10:7];
expected = testvectors[vectornum][6:0];
#1
vectornum = vectornum + 1;
end
//// Check results on falling edge of clk.
always @(negedge clk)
// This line of code lets the program execute the following indented 
// statements in the block at the negative edge of clock.
//// DonÃƒÆ’Ã‚Â¢ÃƒÂ¢Ã¢â‚¬Å¡Ã‚Â¬ÃƒÂ¢Ã¢â‚¬Å¾Ã‚Â¢t do anything during reset. Otherwise, check result.
if (~reset) begin
//// Detect error by checking if outputs from DUT match 
// expectation.
if (number !== expected[6:0]) begin
// If error is detected, print all 3 inputs, 2 outputs, 
// 2 expected outputs.
$display("Error: inputs = %b", {s});
// '$display' prints any statement inside the quotation to 
// the simulator window.
// %b, %d, and %h indicate values in binary, decimal, and 
// hexadecimal, respectively.
// {a, b, cin} create a vector containing three signals.
$display(" outputs = %b ( %b expected)", number, 
expected);
//// Increment the count of errors.
errors = errors + 1;
end
//// In any event, increment the count of vectors.

//// When the test vector becomes all 'x', that means all the 
// vectors that were initially loaded have been processed, thus 
// the test is complete.
if (testvectors[vectornum] === 11'bx) begin
// '==='&'!==' can compare unknown & floating values (X&Z),unlike 
// '=='&'!=', which can only compare 0s and 1s.
// 5'bx is 5-bit binary of x's or xxxxx.
// If the current testvector is xxxxx, report the number of 
// vectors applied & errors detected.
$display("%d tests completed with %d errors", vectornum, 
errors);
// Then stop the simulation.
$stop;
end
end
// In summary, new inputs are applied on the positive clock edge and the 
// outputs are checked against the expected outputs on the negative clock 
// edge. Errors are reported simultaneously. The process repeats until there 
// are no more valid test vectors in the testvectors arrays. At the end of 
// simulation, the module prints the total number of test vectors applied and 
// the total number of errors detected. 
endmodule