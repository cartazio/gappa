CXX=g++-3.5
CXXFLAGS=-Wall -Wextra -ansi -g -O2
OBJS=ast.o basic_proof.o dichotomy.o lexer.yy.o main.o parser.o parser.tab.o program.o proof_graph.o property.o
OBJS_functions=functions/float.o
OBJS_numbers=numbers/float.o numbers/io.o numbers/interval.o numbers/real.o numbers/softfloat.o

export CXX
export CXXFLAGS

main: build build_functions build_numbers
	$(CXX) -o $@ $(OBJS_functions) $(OBJS_numbers) $(OBJS) -lfl -lmpfr -lgmp

gappa: build build_functions build_numbers
	$(CXX) -static -o $@ $(OBJS_functions) $(OBJS_numbers) $(OBJS) -lfl -lmpfr -lgmp
	strip -s $@

build:	$(OBJS)

build_functions:
	$(MAKE) -C functions

build_numbers:
	$(MAKE) -C numbers

include .depend

.depend: *.hpp *.cpp
	g++ -MM *.cpp > .depend

parser.tab.cpp parser.tab.hpp: parser.ypp
	bison -d parser.ypp

lexer.yy.cpp: lexer.l parser.tab.hpp
	flex -o lexer.yy.cpp lexer.l
