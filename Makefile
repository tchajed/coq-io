all: Prog.vo Interpreter.o


Prog.vo Prog.hs: Prog.v
	coqc $< -o $@

Interpreter.o: Interpreter.hs Prog.hs
	ghc $<
