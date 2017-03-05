CC=coqc -I ..

all: SemantChecks.vo

Examples.vo: Examples.v ../Absyn.vo ../Env.vo ../Symbol.vo
	$(CC) Examples.v

SemantChecks.vo: SemantChecks.v Examples.vo ../Absyn.vo ../Semant.vo ../Types.vo
	$(CC) SemantChecks.v

clean:
	rm -f *.vo *.glob
