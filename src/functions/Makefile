CXX=g++-3.4
CXXFLAGS=-Wall -ansi -g -O2 -I..
OBJS=float.o

all: $(OBJS)

include .depend

.depend: *.cpp
	g++ -MM -I.. *.cpp > .depend
