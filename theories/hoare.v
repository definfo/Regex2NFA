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

Local Ltac my_destruct Σ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σ => let σ := fresh "σₕ" in destruct H as [σ H];my_destruct Σ H
              | program Σ ?A => let c := fresh "c" in destruct H as [c H];my_destruct Σ H
              | _ => destruct H as [? H];my_destruct Σ H
              end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct Σ H;
              my_destruct Σ H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct Σ H
  | _ => (discriminate || contradiction  || idtac)
  end.

Context {T: Type}.
Ltac destructs H := my_destruct T H.

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

Lemma G_add_edge'_fact {T: Type} : forall x y t P,
  Hoare P
        (@G_add_edge' T x y t)
        (fun n s =>
          n = s.(max_e') /\
          exists s',
          s.(max_v') = s'.(max_v') /\
          s.(max_e') = s'.(max_e') + 1 /\
          add_edge s'.(st_graph) s.(max_e') x y t s.(st_graph) /\
          P s'
        ).
Proof.
unfold G_add_edge', Hoare. split; intros.
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

Lemma get_new_edge_fact {T: Type} : forall v e,
  (fun s =>
    s.(max_v) = v /\
    s.(max_e) = e) -@
  get_new_edge -⥅
  (fun s =>
    s.(max_v) = v /\
    s.(max_e) = e + 1) ♯ (e + 1).
Proof.
unfold hs_eval. intros.
destruct H.
eexists {|
  max_v := v;
  max_e := e + 1
|}.
simpl. repeat split; subst; eauto.
Qed.

Lemma G_add_vertex_fact {T: Type} : forall (g1 g2: pg_nfa T) v P,
  add_vertex g1 v g2 ->
  P -@ (G_add_vertex g1 v) -⥅ P ♯ (g2).
Proof.
unfold hs_eval. simpl; intros.
eexists σₕ.
split; eauto.
Qed.

Lemma add_vertex_det_pg {T: Type} : forall v g,
(forall v0, g.(pg).(vvalid) v0 -> v0 < v) ->
@add_vertex T g v (pregraph_add_vertex g v).
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

Lemma G_add_edge_fact {T: Type} : forall (g1 g2: pg_nfa T) e x y t P,
  add_edge g1 e x y t g2 ->
  P -@ (G_add_edge g1 e x y t) -⥅ P ♯ g2.
Proof.
unfold hs_eval. simpl; intros.
eexists σₕ.
split. eauto. eauto.
Qed.

Lemma add_edge_det_pg {T: Type} : forall e x y t g,
g.(pg).(vvalid) x -> g.(pg).(vvalid) y ->
(forall e0, g.(pg).(evalid) e0 -> e0 < e) ->
@add_edge T g e x y t (pregraph_add_edge g e x y t).
Proof.
intros.
repeat split; SetsDomain.unfold_SETS_in_goal_tac; simpl; intros; eauto.
- destructs H2; subst; eauto.
- unfold SetsDomain.Sets.singleton in *.
  destruct H2; subst; eauto.
  pose proof (H1 a H2). apply Z.lt_irrefl in H3. eauto.
- unfold SetsDomain.Sets.empty in H0. simpl in *.
  contradiction.
- unfold SetsDomain.Sets.empty in H0. simpl in *.
  contradiction.
- destruct H2; eauto.
- unfold SetsDomain.Sets.singleton in *.
  destruct H2; eauto.
- destruct (Z.eqb_spec e0 e); subst.
  + pose proof (H1 e H2). apply Z.lt_irrefl in H3. contradiction.
  + eauto.
- destruct (Z.eqb_spec e0 e); subst.
  + pose proof (H1 e H2). apply Z.lt_irrefl in H3. contradiction.
  + eauto.
- rewrite Z.eqb_refl. eauto.
- rewrite Z.eqb_refl. eauto.
- destruct (Z.eqb_spec e0 e); subst.
  + pose proof (H1 e H2). apply Z.lt_irrefl in H3. contradiction.
  + eauto.
- rewrite Z.eqb_refl. eauto.
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
      pose proof add_vertex_src0 e H11. rewrite <- H.
      apply add_vertex_src. apply add_vertex_edge0.
      eauto.
    - simpl; intros.
      destruct H11.
    - simpl; intros.
      destruct H2, H6; destruct add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *.
      subst.
      pose proof add_vertex_dst0 e H11. rewrite <- H.
      apply add_vertex_dst. apply add_vertex_edge0.
      eauto.
    - simpl; intros.
      destruct H11.
    - simpl; intros.
      destruct H2, H6; destruct add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *.
      subst.
      pose proof add_vertex_symbol0 e H11. rewrite <- H.
      apply add_vertex_symbol. apply add_vertex_edge0.
      eauto.
    - simpl; intros.
      destruct H11.
  }
- (** EmptyStr_r *)
  simpl regexToNFA'.
  intros. eapply Hoare_bind. 1 : { eapply G_add_vertex'_fact. }
  intros. eapply Hoare_bind. 1 : { eapply G_add_vertex'_fact. }
  intros. eapply Hoare_bind. 1 : { eapply G_add_edge'_fact. }
  intros. eapply Hoare_return. 1 : {
    intros.
    destructs H.
    eexists (@Build_elem T a a0 (emptystr_nfa a1 a a0)).
    repeat split; eauto.
    - unfold regexToNFA, act_singleton in *.
      rename H11 into Hprog.
      eapply highstepbind_derive in Hprog. 2 : { eapply get_new_vertex_fact. }
      eapply highstepbind_derive in Hprog. 2 : { eapply get_new_vertex_fact. }
      unfold graph_constr, graph_constr_rec in Hprog.
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply G_add_vertex_fact.
        eapply add_vertex_det_pg.
        intros. simpl in Hprog. contradiction.
      }
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply G_add_vertex_fact.
        eapply add_vertex_det_pg.
        intros. simpl in *. destruct H11; nia.
      }
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply get_new_edge_fact.
      }
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply G_add_edge_fact.
        eapply add_edge_det_pg;
        simpl; intros; eauto. contradiction.
      }
      unfold ret_nfa in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply highret_eval2.
      }
      eapply highret_eval2 in Hprog.
      destructs Hprog.
      rewrite H, H3, H7.
      rewrite H0, H1, H4, H5, H8, H9.
      unfold emptystr_nfa, emptyset_nfa.
      destruct Hprog. subst.
      apply H11.
    - simpl; intros; subst. destructs H15; nia.
    - simpl; intros; subst. destructs H15; nia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destructs H15; subst;
      try pose proof H13 x0.(max_v') H15;
      try pose proof H13 x.(max_v') H15;
      nia.
    - destructs H15; eauto.
    - destructs H15; eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destructs H15; subst;
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_vertex_vertex, add_vertex_vertex0;
      apply add_edge_vertex; apply H2;
      try (right; reflexivity);
      try (left; apply H6; right; reflexivity).
      + left. apply H6. left. eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_vertex_vertex, add_vertex_vertex0;
      apply add_edge_vertex in H15; apply H2 in H15.
      destruct H15.
      + apply H6 in H7.
        destruct H7.
        left. eauto.
        right; left. eauto.
      + right; right; left. eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destructs H15. subst.
      pose proof H14 σ.(max_e') H15. nia.
    - destruct H15; eauto.
    - destruct H15; eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *.
      destruct add_edge_edge.
      destructs H15; apply H2.
      + left. apply add_vertex_edge. apply add_vertex_edge0. eauto.
      + right. subst. reflexivity.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      apply H2 in H15. destruct H15.
      + apply add_vertex_edge, add_vertex_edge0 in H3. eauto.
      + right; left. rewrite H3; reflexivity.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      assert ((e ∈ ((x0.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge0. eauto. }
      assert ((e ∈ ((x.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge. eauto. }
      pose proof add_vertex_src0 e H15.
      pose proof add_vertex_src e H3.
      pose proof add_edge_src_old e H6.
      lia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      destruct (Z.eqb_spec e a1).
      + subst; lia.
      + destruct H15; nia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      assert ((e ∈ ((x0.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge0. eauto. }
      assert ((e ∈ ((x.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge. eauto. }
      pose proof add_vertex_dst0 e H15.
      pose proof add_vertex_dst e H3.
      pose proof add_edge_dst_old e H6.
      lia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      destruct (Z.eqb_spec e a1).
      + subst; lia.
      + destruct H15; nia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      assert ((e ∈ ((x0.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge0. eauto. }
      assert ((e ∈ ((x.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge. eauto. }
      pose proof add_vertex_symbol0 e H15.
      pose proof add_vertex_symbol e H.
      pose proof add_edge_symbol_old e H2.
(*       lia. *)
(*? Why does lia fail here? *)
      rewrite H7, H6, H3. reflexivity.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct (Z.eqb_spec e a1).
      + subst. apply add_edge_symbol_new.
      + destruct H15; nia.
  }
- (** Char_r *)
  simpl regexToNFA'.
  intros. eapply Hoare_bind. 1 : { eapply G_add_vertex'_fact. }
  intros. eapply Hoare_bind. 1 : { eapply G_add_vertex'_fact. }
  intros. eapply Hoare_bind. 1 : { eapply G_add_edge'_fact. }
  intros. eapply Hoare_return. 1 : {
    intros.
    destructs H.
    eexists (@Build_elem T a a0 (char_nfa a1 a a0 (Some t))).
    repeat split; eauto.
    - unfold regexToNFA, act_singleton in *.
      rename H11 into Hprog.
      eapply highstepbind_derive in Hprog. 2 : { eapply get_new_vertex_fact. }
      eapply highstepbind_derive in Hprog. 2 : { eapply get_new_vertex_fact. }
      unfold graph_constr, graph_constr_rec in Hprog.
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply G_add_vertex_fact.
        eapply add_vertex_det_pg.
        intros. simpl in Hprog. contradiction.
      }
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply G_add_vertex_fact.
        eapply add_vertex_det_pg.
        intros. simpl in *. destruct H11; nia.
      }
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply get_new_edge_fact.
      }
      rewrite bind_bind_equiv in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply G_add_edge_fact.
        eapply add_edge_det_pg;
        simpl; intros; eauto. contradiction.
      }
      unfold ret_nfa in Hprog.
      eapply highstepbind_derive in Hprog. 2 : {
        eapply highret_eval2.
      }
      eapply highret_eval2 in Hprog.
      destructs Hprog.
      rewrite H, H3, H7.
      rewrite H0, H1, H4, H5, H8, H9.
      unfold emptystr_nfa, emptyset_nfa.
      destruct Hprog. subst.
      apply H11.
    - simpl; intros; subst. destructs H15; nia.
    - simpl; intros; subst. destructs H15; nia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destructs H15; subst;
      try pose proof H13 x0.(max_v') H15;
      try pose proof H13 x.(max_v') H15;
      nia.
    - destructs H15; eauto.
    - destructs H15; eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destructs H15; subst;
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_vertex_vertex, add_vertex_vertex0;
      apply add_edge_vertex; apply H2;
      try (right; reflexivity);
      try (left; apply H6; right; reflexivity).
      + left. apply H6. left. eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_vertex_vertex, add_vertex_vertex0;
      apply add_edge_vertex in H15; apply H2 in H15.
      destruct H15.
      + apply H6 in H7.
        destruct H7.
        left. eauto.
        right; left. eauto.
      + right; right; left. eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destructs H15. subst.
      pose proof H14 σ.(max_e') H15. nia.
    - destruct H15; eauto.
    - destruct H15; eauto.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *.
      destruct add_edge_edge.
      destructs H15; apply H2.
      + left. apply add_vertex_edge. apply add_vertex_edge0. eauto.
      + right. subst. reflexivity.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      apply H2 in H15. destruct H15.
      + apply add_vertex_edge, add_vertex_edge0 in H3. eauto.
      + right; left. rewrite H3; reflexivity.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      assert ((e ∈ ((x0.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge0. eauto. }
      assert ((e ∈ ((x.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge. eauto. }
      pose proof add_vertex_src0 e H15.
      pose proof add_vertex_src e H3.
      pose proof add_edge_src_old e H6.
      lia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      destruct (Z.eqb_spec e a1).
      + subst; lia.
      + destruct H15; nia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      assert ((e ∈ ((x0.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge0. eauto. }
      assert ((e ∈ ((x.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge. eauto. }
      pose proof add_vertex_dst0 e H15.
      pose proof add_vertex_dst e H3.
      pose proof add_edge_dst_old e H6.
      lia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct add_edge_edge.
      destruct (Z.eqb_spec e a1).
      + subst; lia.
      + destruct H15; nia.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros; subst.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      assert ((e ∈ ((x0.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge0. eauto. }
      assert ((e ∈ ((x.(st_graph)).(pg)).(evalid))%sets). { apply add_vertex_edge. eauto. }
      pose proof add_vertex_symbol0 e H15.
      pose proof add_vertex_symbol e H.
      pose proof add_edge_symbol_old e H2.
(*       lia. *)
(*? Why does lia fail here? *)
      rewrite H7, H6, H3. reflexivity.
    - simpl; SetsDomain.unfold_SETS_in_goal_tac; intros.
      destruct H2, H6, H10;
      destruct add_edge_pg, add_vertex_pg, add_vertex_pg0;
      unfold Sets_disjoint_union in *;
      destruct (Z.eqb_spec e a1).
      + subst. apply add_edge_symbol_new.
      + destruct H15; nia.
  }
  - 
 
Admitted.
