timeunit 10ns; 
`include "alu_packet.sv"
//`include "alu_assertions.sv"

module alu_tb();
	reg clk = 0;
	bit [0:7] a = 8'h0;
	bit [0:7] b = 8'h0;
	bit [0:2] op = 3'h0;
	wire [0:7] r;

parameter NUMBERS = 10000;

//make your vector here
alu_data test_data[NUMBERS];

//Make your loop here
initial begin: data_gen
	int i;
	#20;
	//test_data = new[NUMBERS];
	for (i = 0; i < NUMBERS; i = i+1) begin
		test_data[i] = new();
		test_data[i].randomize();
		test_data[i].get(a, b, op);
		#20;
	end;
end;

//Displaying signals on the screen
always @(posedge clk) 
  $display($stime,,,"clk=%b a=%b b=%b op=%b r=%b",clk,a,b,op,r);

//Clock generation
always #10 clk=~clk;

//Declaration of the VHDL alu
alu dut (clk,a,b,op,r);

//Make your opcode enumeration here
enum { ADD, SUB, NOT, NAND, NOR, AND, OR, XOR } opcode;

//Make your covergroup here
covergroup alu_cg @(posedge clk);
	op_cp : coverpoint op;// {
//		bins valid = {[0:6]};
//		bins invalid = {7};
//	}
	a_cp : coverpoint a {
		bins zero = {0};
		bins smalll = {[1:50]};
		bins hunds[3] = {[100:200]};
		bins llarge = {[200:$]};
	}
	a_b_cp : cross a, b;
endgroup

//Initialize your covergroup here
alu_cg alu_inst = new();

//Sample covergroup here


endmodule:alu_tb
