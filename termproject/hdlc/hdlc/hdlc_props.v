program hdlc_props(input txclk,rxclk,tx,rx,txen,rxen);
	// Reuse below with a sequence with formal parameters
	cover property (@(posedge txclk) !tx ##1 tx [*6] ##1 !tx)
	  $display($stime,,,"\tTX flag, frame start\n"); // Looking for 01111110
	cover property (@(posedge rxclk) !rx ##1 rx [*6] ##1 !rx)
	  $display($stime,,,"\tRX flag, frame start\n"); // Looking for 01111110
endprogram
