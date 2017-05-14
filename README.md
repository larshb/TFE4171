TFE4171: Design of Digital Systems 2
==============================

Introduction
-----------------
### The verification gap
Traditional verification methodology (directed tests, etc.) cannot keep up with today's designs. Directed test does not scale to complex designs like system on chips (SoC). About 50% of a projects resources go to functional design verification. More than 50% of designs require re-spin due to functional bugs.

The aim is to close the gap and increase design verification productivity. That means raising abstraction level of tests and simulation to reduce both development time and time to simulate.

### SystemVerilog
#### Procedures
In addition to Verilog's `always`-procedure SystemVerilog enables use of three more;

|Procedure	  	  |Logic			       |Sensitivity list|
|---------------|---------------|----------------
|`always_ff`	   |Sequential		   |Explicit
|`always_comb`	 |Combinational	 |Inferred from code
|`always_latch`	|Latched		      |Inferred from code

#### Connecting ports
Ports are connected using `DUT(.*)`, which means connect all ports to variables or nets with the same name as the ports.

#### Data types
|Type		     |Description
|-----------|-----------
|`reg`		    |4-state (Verilog-2001)
|`logic`	   |4-valued logic
|`bit`		    |2-state bit 0 or 1
|`integer`	 |4-state, 32-bit, signed (Verilog-2001)
|`byte`		   |8-bit signed integer
|`int`		    |2-state 32-bit signed integer
|`shortint`	|2-state 16-bit signed integer
|`longint`	 |2-state 64-bit signed integer

#### Testbench constructs

 - Queue
 - Mailbox
 - Fork/join
 - Class
 - Constraint
 - Covergroup
 - Program
 - Virtual interface
 - Clocking block
 - Modports

Acronyms
-------------
|Acronym|Description              			
|-------|----------------------------
|ABV	|Assertion-Based Verification
|ASIC|Application-Specific Integrated Circuit
|ASSP|Application-Specific Standard Product
|BCA	|Bus Cycle-Accurate
|CA 	|Cycle-Accurate
|CRV	|Constrained Random Verification
|CTL	|Computational Tree Logic
|DFG	|Data Flow Graph
|DPI	|Directed Programming Interface
|DSM	|Design Sign-off Model
|DUT	|Design Under Test
|EDA	|Electronic Design Automation
|ESL	|Electronic System Level
|FLIT|FLow control unITs
|FPGA|Field-Programmable Gate Array
|FV 	|Formal Verification
|HDL	|Hardware Description Language
|HDVL|Hardware Description and Verification Language
|IPC	|Interval Property Checking
|ISA	|Instruction Set Architechture
|ISS	|Instruction Set Simulator
|LoC	|Lines of Code
|NBA	|Non-Blocking Assignments
|NoC	|Network On a Chip
|NRE	|Non-Recurring Engineering
|PLI	|Programming Language Interface
|PSL	|Property Specification Language
|PSM	|Program State Machine
|PVT	|Programmer’s View plus Timing
|RNG	|Random Number Generator
|RPC	|Remote Procedure Call
|RTB	|Reconfigurable Testbench
|RTL	|Register-Transfer Level
|SAM	|System Architecture Model
|SAT	|Boolean Satisfiability
|SFSMD|Super-state Finite State Machine with Data
|SoC	|System on Chip
|SVA	|System Verilog Assertions
|TAC	|Transaction Accurate Communication
|TLM	|Transaction Level Modelling
|UVM	|Universal Verification Methodology
|VC		|Virtual Component
|VCT	|Virtual Component Transfer
|VSI	|Virtual Socket Interface
