CXX=g++-3.4
CXXFLAGS=-Wall -ansi -g -O2
OBJS=ast.o basic_proof.o interval.o lexer.yy.o main.o number.o parser.o parser.tab.o program.o proof_graph.o property.o softfloat.o functions/float.o

main: $(OBJS)
	$(CXX) -o $@ $^ -lfl -lmpfr -lgmp

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

softfloat.o:
	ln -s ../../lib/SoftFloat-2b/softfloat/bits64/386-Win32-GCC/softfloat.o

softfloat.h:
	ln -s ../../lib/SoftFloat-2b/softfloat/bits64/386-Win32-GCC/softfloat.h
