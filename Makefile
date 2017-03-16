DIRS=frontend util checks

COQOPTS=-q -noglob
COQINCLUDES=$(foreach d, $(DIRS), -R $(d) certiger.$(d))

COQC=coqc $(COQINCLUDES) $(COQOPTS)
COQDEP=coqdep $(COQINCLUDES)

UTIL=util/Errors.v \
	 util/DecEqFacts.v

FRONTEND=frontend/Absyn.v \
		 frontend/Env.v \
		 frontend/Semant.v \
		 frontend/Symbol.v \
		 frontend/Types.v

CHECKS=checks/Examples.v \
	   checks/SemantChecks.v

PROOF=$(FRONTEND) $(UTIL)
FILES=$(FRONTEND) $(UTIL) $(CHECKS)

all:
	@test -f .depend || $(MAKE) depend
	@$(MAKE) proof

proof: $(PROOF:.v=.vo)

checks: $(CHECKS:.v=.vo)

%.vo: %.v
	@echo "COQC $*.v"
	@$(COQC) $*.v

depend: $(FILES)
	@echo "Checking dependencies"
	@$(COQDEP) $^ > .depend

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f .depend

check-admits: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ | echo "No admits."

print-includes:
	@echo $(COQINCLUDES)

-include .depend
