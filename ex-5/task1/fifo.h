/* -*- mode:c++ -*-
** 
** fifo.h
** 
** Made by Kjetil Svarstad
**
*/

#ifndef   	__FIFO_H_
# define   	__FIFO_H_

#include <systemc.h>
#include "if.h"

// definerer noen hendige tids-konstanter
//
// declaring some useful time constants
const sc_time very_short_time (10, SC_PS),
  short_time (1, SC_NS),
  long_time (100, SC_NS),
  very_long_time (1000, SC_NS);


// fifo er en egen klasse som arver egenskaper fra systemc sin
// sc_channel som er en systemc-modul uten tråder (men som kan ha
// metoder for å respondere på input)
//
// fifo is a class inheriting all features of the SystemC specific
// sc_channel which is a systemc module without support for threads
// (but supporting methods)
class fifo : public fifo_read_if<char>,
	     public fifo_write_if<char>,
	     public sc_channel {
 public:
  // konstruktor (kalles før simulering starter, tar et argument for
  // systemc-type navn og ett for å sette størrelse på fifo'en
  //
  // constructor -- called prior to simulation start, takes one
  // argument for module name and one for fifo size
  fifo (sc_module_name name, int size_);

  // destruktor, kalles når fifo termineres, vanligvis når simulering
  // avsluttes (ved maks-tid eller når "noen" kaller sc_stop
  //
  // destructor, called when objects of this class is deleted (fifo
  // terminated), usually when simulation stops due to reaching set
  // simulation max or some module calls sc_top.
  ~fifo ();
  
  // fifo'ens "tjenster" til omverden, en skrive-funksjon for å skrive
  // inn ny byte i fifo i henhold til fifo_write_if
  //
  // The fifo services to other modules, i.e. the methods in the
  // inherited interfaces that the class will implement. First the
  // write method (from fifo_write_if)
  virtual void write (char);

  // og en lese funksjon for å hente ut en byte
  //
  // and then the read method (from fifo_read_if)
  virtual char read ();

  // en reset-funksjon for intern bruk
  //
  // reset function for internal use (not in interface)
  void reset ();

  // og en intern funksjon for å holde rede på fyllings-grad
  //
  // internal size method (not in interface)
  int num_available ();

 private:
  // trenger et array for å holde på byte ihht. størrelse på fifo
  // (instansieres i konstruktor-kode)
  //
  // data array which is the actual fifo buffer (will be instantiated
  // and allocated in the constructor proper
  char *data;

  // og trenger en del teller-variable for å holde styr på
  // fyllings-grad, hvor første element er i arrayet (brukes som
  // ring-buffer) og størrelse på fifo. Trenger i tillegg en del
  // tellere for å generere bruks-statistikk for fifo'en som antall
  // utlesinger, gjennomsnittlig fyllings-grad, antall overskrivinger
  // og null-lesinger (ved lesing av tom fifo)
  //
  // and a bunch of counters for num of elements in the fifo, the
  // current start (first element) in the fifo, and additional
  // counters for counting events for the performance statistics such
  // as destructive overwrites and unsafe empty reads
  int num_elements, first;
  int size, num_read, max_used, average;
  int num_overwrite, num_emptyread;

  // holder rede på tidspunktene for å regne ut gjennomsnittlig
  // forsinkelse gjennom fifo
  //
  // also, we need a time variable to keep track of averagw
  // performance
  sc_time last_time;

  // en funksjon for å gjøre statistikk-beregning som kan presenteres
  // ved avslutning av simulering
  //
  // and an internal method for collecting and computing the
  // statistics during operation
  void compute_stats ();
};


#endif 	    /* !__FIFO_H_ */
