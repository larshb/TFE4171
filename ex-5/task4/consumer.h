/* -*- mode: c++ -*-
** 
** consumer.h
** 
** Made by Kjetil Svarstad
** 
*/

#ifndef   	__CONSUMER_H_
# define   	__CONSUMER_H_

#include "if.h"

// Data consumer class, inherits standard SystemC module (supporting
// threads)
class consumer : public sc_module, public fifo_callback_if {
 // Task 4:
 private:
   bool acked;

 public:
  // need a port to the fifo's read interface
  sc_port < fifo_read_cb_if<char> > readp;
  
  // constructor
  consumer (sc_module_name name) : sc_module(name) {
    // connect module to the systemC simulator since we don't use the
    // pre-made SC_MODULE declaration macro
    SC_HAS_PROCESS(consumer);
  
    // setter bare prosess-tråd til main-funksjon. Ikke sensitiv for
    // noen eksterne "events", dvs. må startes manuelt etter
    // suspendering (som med wait (tid))
    //
    // one process thread for the main function. Not sensitive for any
    // external events, starts at time 0 and runs until simulation stops
    SC_THREAD(main); 
  } 
 
  // Task 4:
  void ack(bool do_ack) {
    acked = do_ack;
  }

  // definition of the process main thread
  void main() {
    // local char variable for storing read byte
    char c;

    // thread needs to run indefinitely until simulator itself stops
    while (true) {
      // Task 4:
      readp->req_r(true);
      if (acked) {
      
        // read byte from the readp port which we assume is connected to
        // the fifo's fifo_read_if interface
        c = readp->read ();
	
	readp->req_r(false);
	acked = false;
      }

      // Wait for some time assuming there's some processing of the
      // byte going on in the background (it's a performance model,
      // and we have to model the timing of processing assumptions)
      // before next read operation
      wait (long_time);
    }
  }
};


#endif 	    /* !__CONSUMER_H_ */
