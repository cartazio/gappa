CXX=g++-3.4
CXXFLAGS=-Wall -ansi -I.. -g -O2
OBJS=float.o

all: $(OBJS)

include .depend

.depend: *.cpp
	g++ -MM -I.. *.cpp > .depend
