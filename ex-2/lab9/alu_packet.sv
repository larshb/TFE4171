//Make your struct here
typedef struct {
	rand bit[0:7] a, b;
	rand bit[0:2] op;
} data_t;

class alu_data;
        //Initialize your struct here
	rand data_t data;

        // Class methods(tasks) go here
	function void get(ref bit[0:7] a, b, ref bit[0:2] op);
		a = data.a;
		b = data.b;
		op = data.op;
	endfunction

        // Constraints
	constraint c1 {
		//data.a >= 0;
		//data.a <= 127;

		data.a inside {[0:127]};
	}
	constraint c2 {
		//data.b >= 0;
		//data.b <= 255;
		data.b inside {[0:255]};
	}
	constraint c3 {
		//data.op >= 0;
		//data.op <= 6;
		data.op inside {[0:6]};
	}


endclass: alu_data

