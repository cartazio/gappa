CXX=g++-3.4
CXXFLAGS=-Wall -ansi -g -O2
OBJS=ast.o basic_proof.o dichotomy.o lexer.yy.o main.o parser.o parser.tab.o program.o proof_graph.o property.o
OBJS_functions=functions/float.o
OBJS_numbers=numbers/float.o numbers/interval.o numbers/real.o

main: $(OBJS) $(OBJS_functions) $(OBJS_numbers)
	$(CXX) -o $@ $^ -lfl -lmpfr -lgmp

$(OBJS_functions)::
	make -C functions

$(OBJS_numbers)::
	make -C numbers

plouf2.exe: $(OBJS)
	$(CXX) -static -o $@ $^ -lfl -lmpfr -lgmp
	strip $@

include .depend

.depend: *.hpp *.cpp
	g++ -MM *.cpp > .depend

parser.tab.cpp parser.tab.hpp: parser.ypp
	bison -d parser.ypp

lexer.yy.cpp: lexer.l parser.tab.hpp
	flex -o lexer.yy.cpp lexer.l
