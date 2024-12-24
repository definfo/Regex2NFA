Require Import Regex2NFA.lib.PreGraph.
Require Import Regex2NFA.theories.st_graph_nfa.
Require Import Regex2NFA.theories.st_nograph_nfa.
Require Import Regex2NFA.theories.regex.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
From SetsClass Require Import SetsClass.
From StateMonad.monaderror Require Import monadEbasic monadEwhile monadesafe_lib monadEhoare.

Import MonadwitherrDeno.
Import MonadNotation.
Import PreGraphNotations.
Import SetsNotation.
Local Open Scope stmonad_scope.
Local Open Scope Z_scope.
Local Open Scope pg_scope.



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
  forall (r : reg_exp T), exists (v e : Z) (G: pg_nfa T),
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

(*********************************************************)
(**                                                      *)
(** Low_level facts                                      *)
(**                                                      *)
(*********************************************************)

Lemma G_add_vertex'_fact {T: Type} : forall P,
  Hoare P
        (@G_add_vertex' T)
        (fun n s =>
          n = s.(max_v') /\
          exists s',
          s.(max_v') = s'.(max_v') + 1 /\
          s.(max_e') = s'.(max_e') /\
          add_vertex s'.(st_graph) s.(max_v') s.(st_graph) /\
          P s'
        ).
Proof.
unfold G_add_vertex', Hoare. split; intros.
- destruct H0 as [?[?[?]]].
  repeat split; eauto.
- destruct H0.
Qed.

(*********************************************************)
(**                                                      *)
(** High_level facts                                     *)
(**                                                      *)
(*********************************************************)

Lemma get_new_vertex_fact {T: Type} : forall v e,
  (fun s =>
    s.(max_v) = v /\
    s.(max_e) = e) -@
  get_new_vertex -⥅
  (fun s =>
    s.(max_v) = v + 1 /\
    s.(max_e) = e) ♯ (v + 1).
Proof.
unfold hs_eval. intros.
destruct H.
eexists {|
  max_v := v + 1;
  max_e := e
|}.
simpl; repeat split; subst; eauto.
Qed.

Lemma G_add_vertex_fact {T: Type} : forall (g1 g2: pg_nfa T) v P,
  add_vertex g1 v g2 ->
  P -@ (G_add_vertex g1 v) -⥅ P ♯ (g2).
Proof.
unfold hs_eval. intros. simpl.
eexists σₕ.
split; eauto.
Qed.

Definition pregraph_add_vertex {T: Type} (g: pg_nfa T) (v: Z) : pg_nfa T := {|
  pg := (@Graph.Build_PreGraph Z Z
    (fun n => n = v \/ g.(pg).(vvalid) n)
    (g.(pg).(evalid))
    (g.(pg).(src))
    (g.(pg).(dst))
  );
  symbol := g.(symbol)
|}.

Definition pregraph_add_edge {T: Type} (g: pg_nfa T) (e x y : Z) c : pg_nfa T := {|
  pg := (@Graph.Build_PreGraph Z Z
    (fun n => n = x \/ n = y \/ g.(pg).(vvalid) n)
    (fun n => n = e \/ g.(pg).(evalid) n)
    (fun n => if n =? e then x else g.(pg).(src) n)
    (fun n => if n =? e then y else g.(pg).(src) n)
  );
  symbol := fun n => if n =? e then c else g.(symbol) n
|}.

(* Lemma G_add_vertex_fact1 {T: Type} : forall (g1: pg_nfa T) v P,
  ~ g1.(pg).(vvalid) v -> P -@ (G_add_vertex g1 v) -⥅ P ♯ (pregraph_add_vertex g1 v).
Proof.
unfold hs_eval, pregraph_add_vertex. intros. simpl.
eexists σₕ.
repeat split; eauto.
- intros. unfold not in H. admit.
- 
Qed.
 *)

Lemma add_vertex_det_pg {T: Type} : forall v g,
(forall v0, g.(pg).(vvalid) v0 -> v0 < v) ->
@add_vertex T g v
  {|
    pg := @Graph.Build_PreGraph Z Z
        (fun n => n = v \/ g.(pg T).(vvalid) n)
        (g.(pg T).(evalid))
        (g.(pg T).(src))
        (g.(pg T).(dst))
    ;
    symbol := g.(symbol)
  |}
.
Proof.
intros.
repeat split; SetsDomain.unfold_SETS_in_goal_tac; simpl; intros.
- destruct H0.
  unfold SetsDomain.Sets.singleton in *. subst; eauto.
  pose proof (H a H0).
  apply Z.lt_irrefl in H1. eauto.
- unfold SetsDomain.Sets.empty in H0. simpl in *.
  contradiction.
- unfold SetsDomain.Sets.empty in H0. simpl in *.
  contradiction.
- unfold SetsDomain.Sets.singleton in *. destruct H0; eauto.
- unfold SetsDomain.Sets.singleton in *. destruct H0; eauto.
- eauto.
- eauto.
Qed.

(** Refinement proof between high_level and low_level *)

Lemma st_graph_refine {T: Type} :
  (** ∀ X, *)
  forall (r : reg_exp T) (G: pg_nfa T) X,
  Hoare (
          fun s1 =>
            (** safeExec_X P_abs c_abs X *)
            (safeExec (fun s =>
                        s.(max_v) = s1.(max_v') /\
                        s.(max_e) = s1.(max_e'))
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
            exists el,
            (safeExec (fun s =>
                        s.(max_v) = s2.(max_v') /\
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
            union_rel G el.(graph) s2.(st_graph) (** refinement *)
        ).
Proof.
induction r.
- (** EmptySet_r *)
  simpl regexToNFA'.
  intros. eapply Hoare_bind. 1 : { eapply G_add_vertex'_fact. }
  intros. eapply Hoare_bind. 1 : { eapply G_add_vertex'_fact. }
  intros. eapply Hoare_return. 1 : {
    intros.
    destruct H as [?[?[?[?]]]].
    destruct H2 as [?[?[?[?[?[? [?[?[?] ]]]]]]]].
    (* TODO *)
    (** eexists (Build_elem a a1 ... ) *)
    eexists (@Build_elem T a a0 (emptyset_nfa a a0)).
    repeat split; eauto.
    - unfold emptyset_nfa. unfold regexToNFA, act_empty in H7.
      eapply highstepbind_derive in H7. 2 : { eapply get_new_vertex_fact. }
      eapply highstepbind_derive in H7. 2 : { eapply get_new_vertex_fact. }
      unfold graph_constr, graph_constr_rec in H7.
      rewrite bind_bind_equiv in H7.
      eapply highstepbind_derive in H7. 2 : {
        eapply G_add_vertex_fact.
        eapply add_vertex_det_pg.
        intros. simpl in H11. contradiction.
      }
      rewrite bind_bind_equiv in H7.
      eapply highstepbind_derive in H7. 2 : {
        eapply G_add_vertex_fact.
        eapply add_vertex_det_pg.
        intros. simpl in H11. destruct H11; nia.
      }
      eapply highstepbind_derive in H7. 2 : {
        simpl in *. eapply highret_eval2.
      }
      unfold ret_nfa in H7. subst.
      rewrite H0, H1, H4, H5.
      
      eapply H7.
    - simpl. intros. destruct H11; nia.
    - simpl. intros. destruct H11; nia.
    - SetsDomain.unfold_SETS_in_goal_tac.
      simpl; intros. destruct H11.
      repeat destruct H12; subst; simpl in *.
      + pose proof H9 σ.(max_v') H11. nia.
      + pose proof H9 x.(max_v') H11. nia.
    - unfold SetsDomain.Sets.empty in *; simpl in *; contradiction.
    - unfold SetsDomain.Sets.empty in *; simpl in *; contradiction.
    - SetsDomain.unfold_SETS_in_goal_tac. simpl; intros.
      (** x0 --> x --> σ **)
      destruct H11 as [?|[?|[?|?]]];
      destruct H2, H6; destruct add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_vertex_vertex, add_vertex_vertex0;
      rewrite <- H13 in H6; apply H6;
      unfold SetsDomain.Sets.singleton. subst.
      + left. left. eauto.
      + right. lia.
      + left. right. lia.
      + contradiction.
    - SetsDomain.unfold_SETS_in_goal_tac. simpl; intros.
      destruct H2, H6; destruct add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_vertex_vertex, add_vertex_vertex0;
      rewrite <- H13 in H6; apply H6 in H11.
      destruct H11 as [[?|?]|?]; unfold SetsDomain.Sets.singleton;
      subst.
      + left. eauto.
      + right. right. left. eauto. 
      + right. left. eauto.
    - SetsDomain.unfold_SETS_in_goal_tac. simpl; intros.
      destruct H11; eauto.
    - destruct H11.
    - SetsDomain.unfold_SETS_in_goal_tac. simpl; intros.
      destruct H11.
      + destruct H2, H6; destruct add_vertex_pg, add_vertex_pg0;
        unfold Sets_disjoint_union in *.
        apply add_vertex_edge, add_vertex_edge0. subst; eauto.
      + contradiction.
    - SetsDomain.unfold_SETS_in_goal_tac. simpl; intros.
      destruct H2, H6; destruct add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *.
      apply add_vertex_edge, add_vertex_edge0 in H11. subst; eauto.
    - SetsDomain.unfold_SETS_in_goal_tac. simpl; intros.
      destruct H2, H6; destruct add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *.
      subst.
      pose proof (add_vertex_src0 e H11). rewrite <- H.
      apply add_vertex_src. apply add_vertex_edge0.
      eauto.
    - simpl.


Admitted.
