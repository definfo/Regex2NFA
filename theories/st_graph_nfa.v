Require Import Regex2NFA.lib.PreGraph.
Require Import Regex2NFA.theories.regex.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
From StateMonad.monaderror Require Import monadEbasic.

Import MonadwitherrDeno.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope stmonad_scope.

Section Graph_NFA_DEF.

(* state with graph *)
Record state' {T} := {
  max_v' : Z;
  max_e' : Z;
  st_graph : @pg_nfa T
}.

Record elem' := {
  startVertex' : Z;
  endVertex' : Z
}.

(** program state' (sv, ev) *)

Definition get_new_vertex' {T} : program (@state' T) Z := {|
  nrm :=
    fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') + 1 /\
    s2.(max_e') = s1.(max_e') /\
    n = s2.(max_v');
  err := fun s1 => False (* no error case *)
|}.

Definition get_new_edge' {T} : program (@state' T) Z := {|
  nrm :=
    fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') /\
    s2.(max_e') = s1.(max_e') + 1 /\
    n = s2.(max_v');
  err := fun s1 => False (* no error case *)
|}.

Definition pregraph_add_vertex' {T} (v: Z) : program (@state' T) pg_nfa := {|
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

Definition pregraph_add_edge' {T} (e: Z) (s t: Z) (c : option T)
: program (@state' T) pg_nfa := {|
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

Definition pregraph_add_whole_edge' {T} (s t: Z) (c: option T)
: program state' pg_nfa :=
  e <- get_new_edge' ;;
  pregraph_add_edge' e s t c.

Definition nfa_to_elem' {T} (sv ev: Z) : program (@state' T) elem' := {|
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

Fixpoint regexToNFA' {T} (r : reg_exp T)
: program state' elem' :=
  match r with
  | EmptySet_r =>
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    nfa_to_elem' v1 v2

  | EmptyStr_r =>
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 v2 None ;;
    nfa_to_elem' v1 v2

  | Char_r t =>
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 v2 (Some t) ;;
    nfa_to_elem' v1 v2

  | Concat_r r1 r2 =>
    E1 <- regexToNFA' r1 ;;
    E2 <- regexToNFA' r2 ;;
    pregraph_add_whole_edge' E1.(endVertex') E2.(startVertex') epsilon ;;
    nfa_to_elem' E1.(startVertex') E2.(endVertex')

  | Union_r r1 r2 =>
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

  | Star_r r =>
    E <- regexToNFA' r ;;
    v1 <- get_new_vertex' ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 E.(endVertex') epsilon ;;
    pregraph_add_whole_edge' E.(endVertex') v2 epsilon ;;
    pregraph_add_whole_edge' E.(endVertex') E.(startVertex') epsilon ;;
    nfa_to_elem' v1 v2
  end.

(** recursion *)

End Graph_NFA_DEF.
