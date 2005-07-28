AUTOMAKE_OPTIONS = subdir-objects
BUILT_SOURCES = parser/parser.h
AM_YFLAGS = -d

bin_PROGRAMS = gappa

# Dependencies:
# parser/ast.cpp initialization requires proofs/field.cpp initialization

gappa_SOURCES = \
	arithmetic/float.cpp \
	arithmetic/homogen.cpp \
	backends/coq.cpp \
	numbers/interval.cpp \
	numbers/interval.hpp \
	numbers/interval_arith.hpp \
	numbers/interval_utility.hpp \
	numbers/io.cpp \
	numbers/real.cpp \
	numbers/real.hpp \
	numbers/round.cpp \
	numbers/round.hpp \
	parser/ast_real.hpp \
	parser/ast.hpp \
	parser/lexer.lpp \
	parser/parser_aux.cpp \
	parser/parser.ypp \
	parser/pattern.cpp \
	parser/pattern.hpp \
	parser/ring.cpp \
	proofs/basic_proof.cpp \
	proofs/basic_proof.hpp \
	proofs/dichotomy.cpp \
	proofs/dichotomy.hpp \
	proofs/field.cpp \
	proofs/proof_graph.cpp \
	proofs/proof_graph.hpp \
	proofs/property.cpp \
	proofs/property.hpp \
	proofs/schemes.cpp \
	proofs/schemes.hpp \
	parser/ast.cpp \
	main.cpp
