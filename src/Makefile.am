BUILT_SOURCES = parser.h
AM_YFLAGS = -d

bin_PROGRAMS = gappa
gappa_LDADD = softfloat.o

gappa_SOURCES = \
numbers/float.cpp \
numbers/float.hpp \
numbers/float_fun.cpp \
numbers/interval.cpp \
numbers/interval.hpp \
numbers/interval_ext.hpp \
numbers/io.cpp \
numbers/real.cpp \
numbers/real.hpp \
ast.cpp \
ast.hpp \
ast_real.hpp \
basic_proof.cpp \
basic_proof.hpp \
dichotomy.cpp \
function.hpp \
lexer.lpp \
main.cpp \
parser_aux.cpp \
parser.ypp \
program.cpp \
program.hpp \
proof_graph.cpp \
proof_graph.hpp \
property.cpp \
property.hpp \
softfloat.h \
types.hpp

SOFTFLOAT_ARCH=386-Win32-GCC
SOFTFLOAT_PATH=../../lib/SoftFloat-2b/softfloat/bits64/$(SOFTFLOAT_ARCH)

softfloat.o:
	make -C $(SOFTFLOAT_PATH) softfloat.o
	ln -s $(SOFTFLOAT_PATH)/softfloat.o

softfloat.h:
	ln -s $(SOFTFLOAT_PATH)/softfloat.h
