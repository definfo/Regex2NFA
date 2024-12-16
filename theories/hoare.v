Require Import Regex2NFA.lib.PreGraph.
Require Import Regex2NFA.theories.st_graph_nfa.
Require Import Regex2NFA.theories.st_nograph_nfa.
Require Import Regex2NFA.theories.regex.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
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

Lemma get_new_vertex'_fact {T: Type} :
  forall P,
  Hoare P (@get_new_vertex' T) (
                                fun n s =>
                                  exists s',
                                  n = s.(max_v') /\
                                  s.(max_v') = s'.(max_v') + 1 /\
                                  s.(max_e') = s'.(max_e') /\
                                  s.(st_graph) = s'.(st_graph) /\
                                  P s'
                               ).
Proof.
unfold get_new_vertex', Hoare.
split; intros.
- eexists σ1.
  destruct H0 as [?[?[?]]].
  repeat split; auto.
- eauto.
Qed.

Lemma pregraph_add_whole_vertex'_fact {T: Type} :
  forall P,
  Hoare P
        (v <- @get_new_vertex' T ;; pregraph_add_vertex' v)
        (
          fun G s =>
            exists s',
            G = s.(st_graph) /\
            s.(max_v') = s'.(max_v') + 1 /\
            s.(max_e') = s'.(max_e') /\
            G_add_vertex s'.(st_graph) s.(max_v') s.(st_graph) /\
            P s'
        ).
Proof.
intros. eapply Hoare_bind. 1 : { apply get_new_vertex'_fact. }
intros. unfold pregraph_add_vertex', Hoare.
split; intros.
- destruct H as [?[?[?[?[]]]]].
  destruct H0 as [?[?[?]]].
  eexists x.
  split. eauto.
  split. lia.
  split. lia.
  split. rewrite <- H3. rewrite H0. rewrite <- H. eauto.
  eauto.
- destruct H as [?[?[?[?[]]]]].
  destruct H0.
  eauto.
Qed.

Lemma st_graph_refine {T: Type} :
  (** ∀ X, *)
  forall (r : reg_exp T) (G: @pg_nfa T) X,
  Hoare (
          fun s1 =>
            (** safeExec_X P_abs c_abs X *)
            (safeExec (fun s => s.(max_v) = s1.(max_v') /\ s.(max_e) = s1.(max_e'))
                      (regexToNFA r)
                      X) /\
            (*** P_con *)
            s1.(st_graph) = G /\
            (forall v, G.(pg).(vvalid) v -> v <= s1.(max_v')) /\
            (forall e, G.(pg).(evalid) e -> e <= s1.(max_e'))
        )
        (regexToNFA' r) (** c_con *)
        ( 
          fun '(sv, ev) s2 =>
            (** ∃ a, safeExec_X Q_abs(a) skip *)
            exists el, (safeExec (
                                   fun s => s.(max_v) = s2.(max_v') /\
                                            s.(max_e) = s2.(max_e')
                                 )
                                 (return el) (*? skip *)
                                 X
                       ) /\
            (*? *)
            (forall n, el.(graph).(pg).(vvalid) n -> n <= s2.(max_v')) /\
            (forall n, el.(graph).(pg).(evalid) n -> n <= s2.(max_e')) /\
            (** Q_con(a) *)
            sv = el.(startVertex) /\
            ev = el.(endVertex) /\
            G_union_rel G el.(graph) s2.(st_graph) (** refinement *)
        ).
Proof.
induction r.
- intros. simpl regexToNFA'.
  intros. eapply Hoare_bind. 1 : { apply get_new_vertex'_fact. }
  intros. eapply Hoare_bind.
Admitted.

Check safeExec.


