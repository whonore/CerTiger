CC=coqc

all: Semant.vo

Symbol.vo: Symbol.v
	coqc Symbol.v

Absyn.vo: Absyn.v Symbol.vo
	coqc Absyn.v

Types.vo: Types.v Symbol.vo
	coqc Types.v

Env.vo: Env.v Symbol.vo Types.vo
	coqc Env.v

Semant.vo: Semant.v Absyn.vo Env.vo Symbol.vo Types.vo
	coqc Semant.v

clean:
	rm -f *.vo *.glob
