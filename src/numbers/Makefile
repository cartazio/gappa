CXX=g++-3.4
CXXFLAGS=-Wall -ansi -g -O2
OBJS=float.o interval.o real.o softfloat.o

all: $(OBJS)

include .depend

.depend: *.hpp *.cpp
	g++ -MM *.cpp > .depend

SOFTFLOAT_ARCH=386-Win32-GCC
SOFTFLOAT_PATH=../../../lib/SoftFloat-2b/softfloat/bits64/$(SOFTFLOAT_ARCH)

softfloat.o:
	make -C $(SOFTFLOAT_PATH) softfloat.o
	ln -s $(SOFTFLOAT_PATH)/softfloat.o

softfloat.h:
	ln -s $(SOFTFLOAT_PATH)/softfloat.h
