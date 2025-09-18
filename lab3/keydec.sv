/*
by Carlos Ojeda de Silva, September 16 2025
cojedadesilva@g.hmc.edu
Controls the logic for the 4x4 keyboard and does the decoding. it also stablishes the FSM that prevents input bouncing
*/
module keydec(
	input logic reset,
	input logic [3:0] col,
	input logic [2:0] counter, //row
	output logic [3:0] N1 = 0,
	output logic [3:0] N2 = 0
);
logic [1:0] coln = 0;
logic pressed = 0;
//Logic to break down into the col number
always_comb begin
	if (col[3]) coln = 2'b11;
	else if (col[2]) coln = 2'b10;
	else if (col[1]) coln = 2'b01;
	else coln = 2'b00;
end
always_ff @(posedge (counter[0]))
	begin
		if (~reset) begin
		N1 = 13;
		N2 = 13;// set 0 because the coordinate in keypad for 0 is 13
		end else if ((~pressed) && (col != 0)) //first time pressing a button
		begin
		N2 = N1; //save last number to the second hex spot
		N1 = {counter[2:1],coln}; //make the new number match coordinatres 
		pressed = 1; //set state to pressed
		end else if ((~col[N1[1:0]]) && (N1[3:2] == counter[2:1])) begin //if the signal in the expected column and row
			pressed = 0;
			end
	end
endmodule