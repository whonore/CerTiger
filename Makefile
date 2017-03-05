CC=coqc

all: Semant.vo

.PHONY: checks
checks: all
	$(MAKE) -C checks

Symbol.vo: Symbol.v
	$(CC) Symbol.v

Absyn.vo: Absyn.v Symbol.vo
	$(CC) Absyn.v

Types.vo: Types.v Symbol.vo
	$(CC) Types.v

Env.vo: Env.v Symbol.vo Types.vo
	$(CC) Env.v

Errors.vo: Errors.v
	$(CC) Errors.v

Semant.vo: Semant.v Absyn.vo Errors.vo Env.vo Symbol.vo Types.vo
	$(CC) Semant.v

Examples.vo: Examples.v Absyn.vo Env.vo Symbol.vo
	$(CC) Examples.v

SemantSanity.vo: SemantSanity.v Absyn.vo Examples.vo Semant.vo Types.vo
	$(CC) SemantSanity.v

clean:
	rm -f *.vo *.glob
	$(MAKE) -C checks clean
