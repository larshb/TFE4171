/* -*- c++ -*-
** if.h
** 
** Made by Kjetil Svarstad
** Login   <kjetil@svarstad-laptop.fysel.ime.ntnu.no>
** 
** Started on  Thu Jan 17 20:21:10 2008 Kjetil Svarstad
** Last update Thu Jan 17 20:21:10 2008 Kjetil Svarstad
*/

#ifndef   	__IF_H_
# define   	__IF_H_

// Declarations of all the interfaces used for the fifo channel
// performance model

// FIFO non-blocking, non-controlled write interface
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
// 
// - Uses a write method that should be non-blocking and
//   non-controlled.
//
// - the write service method is destructive and will overwrite data
//   in the fifo if the fifo buffer is full
template < class T >
class fifo_write_if : public sc_interface {
public:
  virtual void write (T) = 0;
};

// FIFO non-blocking, non-controlled read interface
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
// 
// - Uses a read method that should be non-blocking and
//   non-controlled.
//
// - the read service method is unsafe and will read data even
//   when the fifo is empty
template < class T >
class fifo_read_if : public sc_interface {
public:
  virtual T read () = 0;
};

// FIFO blocking write interface
//
// Exactly the same signature (methods and type) as the non-controlled
// non-blocking interface fifo_write_if
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
//
// - write method is blocking. This means that the fifo will block a
//   write call from a master if the fifo is full until the fifo is no
//   longer full. The blocking will normally be implemented with a
//   wait-condition.
//
// - the interface is non-controlled, it does not support a full flag
//   (which is not needed due to the blocking behaviour)
template < class T >
class fifo_write_bl_if : public fifo_write_if <T> {
};

// FIFO blocking read interface
//
// Exactly the same signature (methods and type) as the non-controlled
// non-blocking interface fifo_read_if
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
//
// - read method is blocking. This means that the fifo will block a
//   read call from a master if the fifo is empty until the fifo is no
//   longer empty. The blocking will normally be implemented with a
//   wait-condition.
//
// - the interface is non-controlled, it does not support an empty flag
//   (which is not needed due to the blocking behaviour)
template < class T >
class fifo_read_bl_if : public fifo_read_if <T> {
};

// FIFO non-blocking, controlled write interface
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
// 
// - Uses a write method that should be non-blocking and
//   controlled.
//
// - the write service method is destructive and will overwrite data
//   in the fifo if the fifo buffer is full
//
// - the full method will return true if called when the fifo buffer
//   is full, and thus enables the checking of the fifo state prior to
//   calling the destructive write method
template < class T >
class fifo_write_ctrl_if : public fifo_write_if <T> {
public:
  virtual bool full () = 0;
};

// FIFO non-blocking, controlled read interface
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
// 
// - Uses a read method that should be non-blocking and
//   controlled.
//
// - the read service method is unsafe and will read data
//   even when the fifo buffer is empty
//
// - the empty method will return true if called when the fifo buffer
//   is empty, and thus enables the checking of the fifo state prior to
//   calling the unsafe read method
template < class T >
class fifo_read_ctrl_if : public fifo_read_if <T> {
public:
  virtual bool empty () = 0;
};

// FIFO non-blocking callback write interface
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
//
// - Uses a write method that is non-blocking and possibly destructive
//   in overwriting data in a full fifo buffer. This service is
//   supported to be used with a non-blocking, controlled req/ack
//   handshake protocol
//
// - Uses a req method to request writing to the fifo by calling
//   req(true), and then calling req(false) to turn off a pending or
//   executed request
//
// - Is assumed to be used in conjunction with the callback interface
//   fifo_callback_if implemented by the master for acknowledge
//   handshake.
template < class T >
class fifo_write_cb_if : public fifo_write_if <T> {
public:
  virtual void req_w (bool) = 0;
};

// FIFO non-blocking callback read interface
//
// This interface is supposed to support a fifo functionality that
// conforms to the following:
//
// - Uses a read method that is non-blocking and possibly unsafe
//   in reading data from an empty fifo buffer. This service is
//   supported to be used with a non-blocking, controlled req/ack
//   handshake protocol
//
// - Uses a req method to request reading from the fifo by calling
//   req(true), and then calling req(false) to turn off a pending or
//   executed request
//
// - Is assumed to be used in conjunction with the callback interface
//   fifo_callback_if implemented by the master for acknowledge
//   handshake.
template < class T >
class fifo_read_cb_if : public fifo_read_if <T> {
public:
  virtual void req_r (bool) = 0;
};

// FIFO callback interface
//
// This interface is supposed to be implemented by a master
// communicating with a fifo slave using the non-blocked callback read
// and write interfaces. The functionality implemented in the master
// should conform to the following:
//
// - An ack(true) call will confirm a req(true) request from the
//   master, allowing the master to safely and non-destructively call
//   read or write.
//
// - An ack(false) call will confirm the closure of a write or read
//   transaction previously signalled by a req(false) call from the
//   master.
class fifo_callback_if : public sc_interface {
public:
  virtual void ack (bool) = 0;
};


#endif 	    /* !__IF_H_ */
