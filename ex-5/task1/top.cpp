/* -*- mode: c++ -*-
**
** top.cpp
**
** top level instatiations and simulation control
** 
** Made by Kjetil Svarstad
** 
*/

#include "fifo.h"
#include "producer.h"
#include "consumer.h"

// Top level module
class top : public sc_module {
public:
  // need instances of fifo, producer and consumer
  fifo fifo_inst;
  producer prod_inst;
  consumer cons_inst;
  
  // constructor for top, sends name to sc_module constructor
  top (sc_module_name name, int size) : sc_module (name) ,
					// and executes the actual
					// instantiation of the  fifo,
					// the producer and consumer
					// with their respective
					// parameter values
				       fifo_inst ("fifo", size), 
				       prod_inst ("producer"), 
				       cons_inst ("consumer") {

    // Connects the producers writep port to the fifo instance
    prod_inst.writep (fifo_inst);
    
    // and then the consumers readp port to the fifo instance
    cons_inst.readp (fifo_inst);
  }
};

// Main program, running the simulation

int sc_main (int argc , char *argv[])  {
  // FIFO size can be set as command line argument
  // default is 10
  int size = 10;

  if (argc > 1)
    size = atoi(argv[1]);
  
  if (size < 1)
    size = 1;

  if (size > 100000)
    size = 100000;
  
  // instantiating top module
  top top1("Top1", size);
  
  // initializing random number generator
  srand ( time(NULL) );

  // run simualtion indefinitely until some module calls sc_stop
  sc_start();
  return 0;
}
