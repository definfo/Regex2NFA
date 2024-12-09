CURRENT_DIR=.
SETS_DIR = ./sets
FIXPOINT_DIR = ./fixedpoints
MONAD_DIR = ./monadlib
CERTIGRAPH_DIR = ./CertiGraph

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

SETS_FLAG = -R $(SETS_DIR) SetsClass 
FIXPOINT_FLAG = -R $(FIXPOINT_DIR) FP
MONAD_FLAG = $(SETS_FLAG) $(FIXPOINT_FLAG) -R $(MONAD_DIR)/monadnrm StateMonad.monadnrm -R $(MONAD_DIR)/monaderror StateMonad.monaderror
CERTIGRAPH_FLAG = -R $(CERTIGRAPH_DIR) CertiGraph.lib

DEP_FLAG = $(MONAD_FLAG) $(CERTIGRAPH_FLAG) -R lib Regex2NFA.lib -R theories Regex2NFA.theories

CertiGraphlib_Files = \
	Coqlib.v EquivDec_ext.v Ensembles_ext.v

CERTIGRAPH_FILES = \
	$(CertiGraphlib_Files:%.v=CertiGraph/%.v)

Regex2NFAlib_Files = \
	PreGraph.v

Regex2NFAtheories_Files = \
	hoare.v regex.v st_graph_nfa.v st_nograph_nfa.v

Regex2NFA_FILES = \
	$(Regex2NFAlib_Files:%.v=lib/%.v) \
	$(Regex2NFAtheories_Files:%.v=theories/%.v)

FILES = $(CERTIGRAPH_FILES) $(Regex2NFA_FILES)

$(Regex2NFA_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(DEP_FLAG) $<

$(CERTIGRAPH_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(CERTIGRAPH_FLAG) $<

world:
	$(MAKE) -C $(SETS_DIR)
	$(MAKE) -C $(FIXPOINT_DIR)
	$(MAKE) -C $(MONAD_DIR)

all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	$(MAKE) -C $(SETS_DIR) clean
	$(MAKE) -C $(FIXPOINT_DIR) clean
	$(MAKE) -C $(MONAD_DIR) clean
	@rm -f .lia.cache .nia.cache .depend _CoqProject
	@rm -f lib/*.{vo,vos,vok,glob}
	@rm -f theories/*.{vo,vos,vok,glob}
	@rm -f sets/*.{vo,vos,vok,glob}
	@rm -f fixedpoints/*.{vo,vos,vok,glob}
	@rm -f monadlib/monadnrm/*.{vo,vos,vok,glob}
	@rm -f monadlib/monaderror/*.{vo,vos,vok,glob}
	@rm -f CertiGraph/*.{vo,vos,vok,glob}

.DEFAULT_GOAL := all

-include .depend

