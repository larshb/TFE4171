/*
 * ex2_1
 * 
 * Purpose:
 * - Reset on rst=1
 * - When validi=1 three clk's in a row, compute data_out=a*b+c
 *   where a is data_in on the first clk, b on the second and c
 *   on the third. Also set valido=1. Else valido=0 which means
 *   data_out is not valid.
 */

module ex2_1 (
	      input 		  clk, rst, validi,
	      input [31:0] 	  data_in,
	      output logic 	  valido, 
	      output logic [31:0] data_out
	      );
   
   enum 			  {S0, S1, S2} state = S0, next = S0;
   
   logic [31:0] 		  a, b, multi_r, adder_r, data_in_buf;
   logic clk_;

   always @(edge clk) begin
   	clk_ <= !clk;
   end

	alu fake_multiplier
		(
		clk_,
		a, b,
		3'b111, // Op - mult
		multi_r
		);
	
	alu adder
		(
		clk_,
		multi_r, data_in_buf,
		3'b000, // Op - add
		adder_r
		);
 
   always_comb data_out <= adder_r & {32{valido}};

   always_ff @(posedge clk or posedge rst) begin
      data_in_buf <= data_in;
      if (rst) begin
//	 data_out <= 32'b0;
	 valido <= 1'b0;
	 state = S0;
      end
   
      else begin   
//	 $display($time,,,"\ta=%d, b=%d, a*b=%d, adder_r=%d\n", a, b, multi_r, adder_r);
	 case (state)
	   
	   // S0
	   S0: begin
	      valido <= 1'b0;
	      if (validi) begin
		 a = data_in;
		 next = S1;
	      end
	   end

	   // S1
	   S1: begin
	      if (validi) begin
		 b = data_in;
		 next = S2;
	      end
	      else
		next = S0;
	   end

	   // S2
	   S2: begin
	      if (validi) begin
//		 data_out <= a*b+data_in;
//		 data_out <= adder_r;
		 a = b;
		 b = data_in;
		 valido <= 1'b1;
		 next = S2;
	      end
	      else begin
	        next = S0;
		valido = 1'b0;
	      end
	   end

	 endcase
	 state = next;
	 
      end
   end
endmodule
