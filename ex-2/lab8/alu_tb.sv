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

//Make your loop here

//Displaying signals on the screen
always @(posedge clk) 
  $display($stime,,,"clk=%b a=%b b=%b op=%b r=%b",clk,a,b,op,r);

//Clock generation
always #10 clk=~clk;

//Declaration of the VHDL alu
alu dut (clk,a,b,op,r);

//Make your opcode enumeration here


//Make your covergroup here


//Initialize your covergroup here


//Sample covergroup here


endmodule:alu_tb
