AUTOMAKE_OPTIONS = subdir-objects
BUILT_SOURCES = parser/parser.h
AM_YFLAGS = -d

bin_PROGRAMS = gappa

# Dependencies:
# proofs/rewriting.cpp initialization requires parser/ast.cpp initialization
# backends/*.cpp initialization requires backends/backends.cpp initialization

gappa_SOURCES = \
	arithmetic/fixed.cpp \
	arithmetic/float.cpp \
	arithmetic/homogen.cpp \
	arithmetic/relative.cpp \
	backends/coq.cpp \
	backends/coq_lambda.cpp \
	backends/holl.cpp \
	backends/backend.cpp \
	backends/backend.hpp \
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
	proofs/dichotomy.cpp \
	proofs/dichotomy.hpp \
	proofs/proof_graph.cpp \
	proofs/proof_graph.hpp \
	proofs/property.cpp \
	proofs/property.hpp \
	proofs/rewriting.cpp \
	proofs/rewriting.hpp \
	proofs/schemes.cpp \
	proofs/schemes.hpp \
	proofs/updater.cpp \
	proofs/updater.hpp \
	parser/ast.cpp \
	main.cpp \
	parameters.cpp \
	parameters.hpp \
	utils.hpp
