CC     = g++
OPT    = -O3
DEBUG  = -g
#OTHER  = -Wno-deprecated -permissive
CFLAGS = $(OPT) $(OTHER)
# CFLAGS = $(DEBUG) $(OTHER)

MODULE = run
SRCS = fifo.cpp top.cpp
OBJS = $(SRCS:.cpp=.o)

all: run.x

fifo.o: if.h fifo.h fifo.cpp

top.o: if.h fifo.h producer.h consumer.h top.cpp

ifneq (, $(realpath ~/systemc/Makefile.defs))
include ~/systemc/Makefile.defs
else ifneq (, $(realpath ../Makefile.defs))
include ../Makefile.defs
else
$(error "Cannot find Makefile.defs")
endif