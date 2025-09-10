/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file tests the possible values and the expected outputs
*/

module testbench();
logic clk, reset;
logic [3:0] s1, s2;
logic [1:0] disps;
logic [6:0] number;
logic [4:0] leds;
logic [15:0] expected;
logic [31:0] counter;

logic [24:0] testvectors[31:0] = '{ //s1[4] s2[4] number[7] sout[4] leds[5]
25'b0000000000000010000000000,
25'b0001000010011110001000010,
25'b0010000000100100010000100,
25'b0011000000001100011000110,
25'b0100000010011000100001000,
25'b0101000001001000101001010,
25'b0110000001000000110001100,
25'b0111000000011110111001110,
25'b1000000000000001000010000,
25'b1001000000001001001010010,
25'b1010000000010001010010100,
25'b1011000011000001011010110,
25'b1100000001100011100011000,
25'b1101000010000101101011010,
25'b1110000001100001110011100,
25'b1111000001110001111011110, //second disp v
25'b1111000000000010000011111,
25'b1111000110011110001100001,
25'b1111001000100100010100011,
25'b1111001100001100011100101,
25'b1111010010011000100100111,
25'b1111010101001000101101001,
25'b1111011001000000110101011,
25'b1111011100011110111101101,
25'b1111100000000001000101111,
25'b1111100100001001001110001,
25'b1111101000010001010110011,
25'b1111101111000001011110101,
25'b1111110001100011100110111,
25'b1111110110000101101111001,
25'b1111111001100001110111011,
25'b1111111101110001111111101};

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
// use 8 test vectors (found in .tv file below), however it doesn 
// to set up array to support more so we could easily add test vectors
// later. 
//// Instantiate device under test (DUT).
// Inputs: a, b, cin. Outputs: s, cout.
top dut(s1, s2, counter, disps, number, leds);

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

//s1[4] s2[4] number[7] disps[2] sout[4] leds[5]

s1 = testvectors[vectornum][24:21];
s2 = testvectors[vectornum][20:17];
counter[21] = testvectors[vectornum][0];
expected = testvectors[vectornum][16:1];
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

//expected = number[7] sout[4] leds[5]

if (((s1 !== expected[8:5]) && disps[1]) || ((s2 !== expected[8:5]) && disps[0]) || number !== expected[15:9] || leds !== expected[4:0]) begin
// If error is detected, print all 3 inputs, 2 outputs, 
// 2 expected outputs.
$display("Error: inputs = %b", {s1, s2, disps});
// '$display' prints any statement inside the quotation to 
// the simulator window.
// %b, %d, and %h indicate values in binary, decimal, and 
// hexadecimal, respectively.
// {a, b, cin} create a vector containing three signals.
$display(" outputs = %b %b (%b %b expected)", leds, number, expected[4:0], expected[15:9]);
//// Increment the count of errors.
errors = errors + 1;
end
//// In any event, increment the count of vectors.

//// When the test vector becomes all 'x', that means all the 
// vectors that were initially loaded have been processed, thus 
// the test is complete.
if (testvectors[vectornum] === 24'bx) begin
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