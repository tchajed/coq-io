all: Prog.vo


Prog.vo word-count/src/Prog.hs: Prog.v
	coqc $< -o $@

clean:
	rm -f *.glob *.vo
	rm -f word-count/src/Prog.hs
