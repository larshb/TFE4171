/* -*- mode:c++ -*-
** 
** fifo.cpp
**
** Fifo internals
** 
** Made by Kjetil Svarstad
**
*/

#include "fifo.h"

// fifo konstruktor
// setter size til verdi fra size_ parameter
//
// fifo constructor sets the size variable according to the size_
// parameter and sends the name parameter to the SystemC backbone
// through the inherited class sc_channels specific constructor
fifo::fifo(sc_module_name name, int size_) : sc_channel(name), size(size_) {
  // byte-array som buffer for fifo
  //
  // allocating the buffer
  data = new char[size];

  // initialisering av alle tellere
  //
  // initializing all the counters
  num_elements = first = 0;
  num_read = max_used = average = 0;
  num_overwrite = num_emptyread = 0;

  // initialisering av tids-stempel for "siste" hendelse
  //
  // and initializing the time counter
  last_time = SC_ZERO_TIME;
}

// destruktor, her vil vi bruke den til å skrive ut
// ytelses-statistikken for fifo'en siden vi vet at den først kalles
// når simulering termineres
//
// destructor, we know that when this is called the simulation has
// stopped, and we can then summarize and write out the performance
// statistics for the fifo
fifo::~fifo() {

  // fjerner buffer-arrayet
  //
  // deletes the allocated buffer memory
  delete[] data;

  // trekker fra "tomme" skrive og lese-sykler fra total-antallet
  //
  // subtracts the empty read operations and destructive write
  // operations from the number of real (efficient, useful) reads from
  // the fifo since they represent an error in the performance model
  num_read -= num_emptyread + num_overwrite;
  
  // Skriver ut all statistikken:
  //
  // Print the performance statistics
  cout << endl << "Fifo size is: " << size << endl;
  cout << "Average fifo fill depth: " << 
    double(average) / num_read << endl;
  cout << "Maximum fifo fill depth: " << max_used << endl;
  cout << "Average transfer time per character: " 
       << last_time / num_read << endl;
  cout << "Number of overwrites: " << num_overwrite << endl;
  cout << "Number of empty reads: " << num_emptyread << endl;
  cout << "Total characters transferred: " << num_read << endl;
  cout << "Total time: " << last_time << endl;
}

// write-method implementation
void fifo::write (char c) {
  // Write byte into the fifo buffer
  data[(first + num_elements) % size] = c;

#ifdef TRACE
  cout << "+" << c;
#endif
  
  // if the buffer is already full we increment the overwrite counter
  if (num_elements == size) ++ num_overwrite;

  else   // otherwise we increment the num of elements counter
    ++ num_elements;
}

// read method implementation
char fifo::read () {
  // local buffer for storing the read byte until return
  char c;

  // record time
  last_time = sc_time_stamp();

  // fetch the "oldest" byte in the buffer
  c = data[first];

  // compute the new stats based on new counters
  compute_stats();

  // if the buffer is already empty, we update the empty read counter
  if (num_elements == 0) {
    c = '0';
    ++ num_emptyread;
  }

  // otherwise we decrement the number of elements counter, and
  // increment the first pointer to point to the next oldest element
  else {
    -- num_elements;
    first = (first + 1) % size;
  }
  
#ifdef TRACE
  cout << "-" << c;
#endif

  // return the correct byte
  return c;
}

// reset buffer counters
void fifo::reset() { 
  num_elements = first = 0; 
}

// buffer fill
int fifo::num_available() { 
  return num_elements;
}

// update stats
void fifo::compute_stats() {
  average += num_elements;
  
  if (num_elements > max_used)
    max_used = num_elements;
  
  ++num_read;
}
