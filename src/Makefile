CXX=g++-3.4
CXXFLAGS=-Wall -Wextra -ansi -g -O2
OBJS=ast.o basic_proof.o dichotomy.o lexer.yy.o main.o parser.o parser.tab.o program.o proof_graph.o property.o
OBJS_functions=functions/float.o
OBJS_numbers=numbers/float.o numbers/io.o numbers/interval.o numbers/real.o numbers/softfloat.o

export CXX
export CXXFLAGS

main: build build_functions build_numbers
	$(CXX) -o $@ $(OBJS_functions) $(OBJS_numbers) $(OBJS) -lfl -lmpfr -lgmp

build:	$(OBJS)

build_functions:
	$(MAKE) -C functions

build_numbers:
	$(MAKE) -C numbers

#plouf2.exe: $(OBJS)
#	$(CXX) -static -o $@ $^ -lfl -lmpfr -lgmp
#	strip $@

include .depend

.depend: *.hpp *.cpp
	g++ -MM *.cpp > .depend

parser.tab.cpp parser.tab.hpp: parser.ypp
	bison -d parser.ypp

lexer.yy.cpp: lexer.l parser.tab.hpp
	flex -o lexer.yy.cpp lexer.l
