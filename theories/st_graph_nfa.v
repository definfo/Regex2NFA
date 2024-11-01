Require Import Regex2NFA.lib.PreGraph.
Require Import Regex2NFA.theories.regex.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import List.
From StateMonad.monaderror Require Import monadEbasic.

Import MonadwitherrDeno.
Import MonadNotation.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope stmonad_scope.
Local Open Scope char_scope.

Section Graph_NFA_DEF.

(* state with graph *)
Record state' := {
  max_v' : Z;
  max_e' : Z;
  st_graph : pg_nfa
}.

Record elem' := {
  startVertex' : Z;
  endVertex' : Z
}.

(** program state' (sv, ev) *)

Definition get_new_vertex' : program state' Z := {|
  nrm :=
    fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') + 1 /\
    s2.(max_e') = s1.(max_e') /\
    n = s2.(max_v');
  err := fun s1 => False (* no error case *)
|}.

Definition get_new_edge' : program state' Z := {|
  nrm :=
    fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') /\
    s2.(max_e') = s1.(max_e') + 1 /\
    n = s2.(max_v');
  err := fun s1 => False (* no error case *)
|}.

Definition pregraph_add_vertex' (v: Z) : program state' pg_nfa := {|
  nrm :=
    fun s1 G s2 =>
    let G1 := s1.(st_graph) in
    let G2 := s2.(st_graph) in
    s2.(max_v') = s1.(max_v') /\
    s2.(max_e') = s1.(max_e') /\
    G_add_vertex G1 v G2 /\
    G = G2;
  err := fun s1 => v <> s1.(max_v')
  (* error if new vertex label mismatches current state *)
|}.

Definition pregraph_add_edge' (e: Z) (s t: Z) (c : option ascii) : program state' pg_nfa := {|
  nrm :=
    fun s1 G s2 =>
    let G1 := s1.(st_graph) in
    let G2 := s2.(st_graph) in
    s2.(max_v') = s1.(max_v') /\
    s2.(max_e') = s1.(max_e') /\
    G_add_edge G1 e s t c G2 /\
    G = G2;
  err :=
    fun s1 =>
    let g1 := s1.(st_graph).(pg) in
    exists e',
    g1.(vvalid) s /\ g1.(vvalid) t /\
    g1.(evalid) e' /\
    g1.(src) e' = s /\
    g1.(dst) e' = t
  (* error if edge exists *)
|}.

Definition pregraph_add_whole_edge' (s t: Z) (c: option ascii) : program state' pg_nfa :=
  e <- get_new_edge' ;;
  pregraph_add_edge' e s t c.

Definition nfa_to_elem' (sv ev: Z) : program state' elem' := {|
  nrm :=
    fun s1 E s2 =>
    s1 = s2 /\
    E = {|
      startVertex' := sv;
      endVertex' := ev;
    |};
  err :=
    fun s1 =>
    let g := s1.(st_graph) in
    ~ vvalid g.(pg) sv \/ ~ vvalid g.(pg) ev
|}.

Definition init_singleton (c: option ascii) : program state' elem' := {|
  nrm :=
    fun s1 el s2 =>
    s2.(max_v') = s1.(max_v') + 2 /\
    s2.(max_e') = s1.(max_e') + 1 /\
    el = {|
      startVertex' := s1.(max_v') + 1;
      endVertex' := s1.(max_v') + 2;
    |};
  err :=
    fun s1 => False
|}.

Fixpoint regexToNFA' (r : reg_exp (option ascii) ) : program state' elem' :=
  match r with
  | EmptySet | EmptyStr =>
    return {|
      startVertex' :=0;
      endVertex' := 0
    |}
  | Char t =>
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 v2 t ;;
    nfa_to_elem' v1 v2
  | Concat r1 r2 =>
    E1 <- regexToNFA' r1 ;;
    E2 <- regexToNFA' r2 ;;
    pregraph_add_whole_edge' E1.(endVertex') E2.(startVertex') epsilon ;;
    nfa_to_elem' E1.(startVertex') E2.(endVertex')
  | Union r1 r2 =>
    E1 <- regexToNFA' r1 ;;
    E2 <- regexToNFA' r2 ;;
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 E1.(startVertex') epsilon ;;
    pregraph_add_whole_edge' v1 E2.(startVertex') epsilon ;;
    pregraph_add_whole_edge' E1.(endVertex') v2 epsilon ;;
    pregraph_add_whole_edge' E2.(endVertex') v2 epsilon ;;
    nfa_to_elem' E1.(startVertex') E2.(startVertex')
  | Star r =>
    E <- regexToNFA' r ;;
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 E.(endVertex') epsilon ;;
    pregraph_add_whole_edge' E.(endVertex') v2 epsilon ;;
    pregraph_add_whole_edge' E.(endVertex') E.(startVertex') epsilon ;;
    nfa_to_elem' v1 v2
  | Plus r =>
    E <- regexToNFA' r ;;
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 E.(startVertex') epsilon ;;
    pregraph_add_whole_edge' E.(endVertex') v2 epsilon ;;
    pregraph_add_whole_edge' E.(endVertex') E.(startVertex') epsilon ;;
    nfa_to_elem' v1 v2
  | Question r =>
    E <- regexToNFA' r ;;
    pregraph_add_whole_edge' E.(startVertex') E.(endVertex') epsilon ;;
    nfa_to_elem' E.(startVertex') E.(endVertex')
  end.

(** recursion *)

End Graph_NFA_DEF.
