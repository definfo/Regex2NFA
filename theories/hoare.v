Require Import Regex2NFA.lib.PreGraph.
Require Import Regex2NFA.theories.st_graph_nfa.
Require Import Regex2NFA.theories.st_nograph_nfa.
Require Import Regex2NFA.theories.regex.
Require Import Coq.ZArith.ZArith.
From StateMonad.monaderror Require Import monadEbasic monadEwhile monadesafe_lib monadEhoare.

Import MonadwitherrDeno.
Import MonadNotation.
Local Open Scope stmonad_scope.
Local Open Scope Z_scope.

(** high_level prop *)
Lemma st_nograph_inc {T: Type} :
  forall (r: reg_exp T), exists (v e : Z),
  Hoare (fun s1 => s1.(max_v) = v /\ s1.(max_e) = e)
        (regexToNFA r)
        (fun el s2 => let G := el.(graph) in
                      let g := G.(pg) in
                      s2.(max_v) > v /\
                      s2.(max_e) > e /\
                      (forall n, g.(vvalid) n -> v < n <= s2.(max_v)) /\
                      (forall n, g.(evalid) n -> e < n <= s2.(max_e)) /\
                      forall str, exp_match r str <->
                                  G_match_str G el.(startVertex) el.(endVertex) str
        ).
Proof.
Admitted.

(** low_level prop *)
Lemma st_graph_inc {T: Type} :
  forall (r : reg_exp T), exists (v e : Z) (G: @pg_nfa T),
  Hoare (fun s1 => s1.(max_v') = v /\
                   s1.(max_e') = e /\
                   s1.(st_graph) = G)
        (regexToNFA' r)
        (fun el s2 => let g := G.(pg) in
                      s2.(max_v') > v /\
                      s2.(max_e') > e /\
                      (forall n, g.(vvalid) n -> n <= s2.(max_v')) /\
                      (forall n, g.(evalid) n -> n <= s2.(max_e'))
        ).
Proof.
Admitted.

Lemma st_graph_refine {T: Type} :
  (** ∀ X, *)
  forall (r : reg_exp T) (G: @pg_nfa T) X,
  Hoare ( fun s1 =>
            (** safeExec_X P_abs c_abs X *)
            (safeExec (fun s => s.(max_v) = s1.(max_v') /\ s.(max_e) = s1.(max_e'))
                      (regexToNFA r)
                      X) /\
            (*** P_con *)
            s1.(st_graph) = G
            (** G \forall v e, <= max_v max_e *)
        )
        (regexToNFA' r) (** c_con *)
        ( 
          fun el' s2 =>
            (** ∃ a, safeExec_X Q_abs(a) skip *)
            exists el, (safeExec (
                                   fun s => s.(max_v) = s2.(max_v') /\
                                            s.(max_e) = s2.(max_e')
                                 )
                                 (return el) (*? skip *)
                                 X
                       ) /\
            (** Q_con(a) *)
            let g := G.(pg) in
              el'.(startVertex') = el.(startVertex) /\
              el'.(endVertex') = el.(endVertex) /\
              G_union_rel G el.(graph) s2.(st_graph) (** refinement *)
        ).
Proof.
Admitted.

Check safeExec.


