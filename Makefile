CURRENT_DIR = .
SETS_DIR = sets
FIXPOINT_DIR = fixedpoints
MONAD_DIR = monadlib

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

SETS_FLAG = -R $(SETS_DIR) SetsClass 
FIXPOINT_FLAG = $(SETS_FLAG) -R $(FIXPOINT_DIR) FP
MONAD_FLAG = $(FIXPOINT_FLAG) -R $(MONAD_DIR)/monadnrm StateMonad.monadnrm -R $(MONAD_DIR)/monaderror StateMonad.monaderror

DEP_FLAG = $(MONAD_FLAG) -R lib Regex2NFA.lib -R theories Regex2NFA.theories

SETS_Files = \
  SetsClass.v \
  SetsClass_AxiomFree.v \
  SetsDomain.v \
  SetElement.v \
  SetElementProperties.v \
  RelsDomain.v \
  SetProd.v \
  SetsDomain_Classic.v

SETS_FILES = \
	$(SETS_Files:%.v=$(SETS_DIR)/%.v)

FIXPOINT_Files = \
  AllFramework.v \
  Coqlib.v \
  LiftConstructors.v \
  PartialOrder_Setoid.v \
  KnasterTarski.v \
  BourbakiWitt.v \
  SetsFixedpoints.v

FIXPOINT_FILES = \
	$(FIXPOINT_Files:%.v=$(FIXPOINT_DIR)/%.v)

MonadNrm_Files = \
	monadbasic.v safeexec_lib.v mergeExample.v

MonadError_Files = \
	monadEbasic.v monadEwhile.v monadesafe_lib.v monadEhoare.v
  
MONAD_FILES = \
	$(MonadNrm_Files:%.v=$(MONAD_DIR)/monadnrm/%.v) \
	$(MonadError_Files:%.v=$(MONAD_DIR)/monaderror/%.v) \

Regex2NFAlib_Files = \
	PreGraph.v

Regex2NFAtheories_Files = \
	hoare.v regex.v st_graph_nfa.v st_nograph_nfa.v

Regex2NFA_FILES = \
	$(Regex2NFAlib_Files:%.v=lib/%.v) \
	$(Regex2NFAtheories_Files:%.v=theories/%.v)

REQUIREMENT_FILES = \
	$(SETS_FILES) \
	$(FIXPOINT_FILES) \
	$(MONAD_FILES)

FILES = \
	$(REQUIREMENT_FILES) \
	$(Regex2NFA_FILES)

$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(SETS_FLAG) $<

$(FIXPOINT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(FIXPOINT_FLAG) $<

$(MONAD_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(MONAD_FLAG) $<

$(Regex2NFA_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(DEP_FLAG) $<

requirements: $(REQUIREMENT_FILES:%.v=%.vo)

world: $(FILES:%.v=%.vo)

all: world

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f .lia.cache .nia.cache .depend _CoqProject
	@rm -f sets/*.{vo,vos,vok,glob}
	@rm -f fixedpoints/*.{vo,vos,vok,glob}
	@rm -f monadlib/monadnrm/*.{vo,vos,vok,glob}
	@rm -f monadlib/monaderror/*.{vo,vos,vok,glob}
	@rm -f lib/*.{vo,vos,vok,glob}
	@rm -f theories/*.{vo,vos,vok,glob}

.DEFAULT_GOAL := all

-include .depend

