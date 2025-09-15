/*
by Carlos Ojeda de Silva, September 3 2025
cojedadesilva@g.hmc.edu
This file transforms a 4 bit signal in the s pins to a hex display (number)
*/


module sevseg(
	input 	logic	[3:0] s,
	output 	logic   [6:0] number
);


always_comb
case(s) //ABCDEFG      
4'd0: number = 7'b0000001;
4'd1: number = 7'b1001111;
4'd2: number = 7'b0010010;
4'd3: number = 7'b0000110;
4'd4: number = 7'b1001100;
4'd5: number = 7'b0100100;
4'd6: number = 7'b0100000;
4'd7: number = 7'b0001111;
4'd8: number = 7'b0000000;
4'd9: number = 7'b0000100;
4'd10: number = 7'b0001000;
4'd11: number = 7'b1100000;
4'd12: number = 7'b0110001;
4'd13: number = 7'b1000010;
4'd14: number = 7'b0110000;
4'd15: number = 7'b0111000;
default: number = 7'b1111111; //off if not sure
endcase
endmodule
