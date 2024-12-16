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

(** program state' (sv, ev) *)

Definition get_new_vertex' {T} : program (@state' T) Z := {|
  nrm :=
    fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') + 1 /\
    s2.(max_e') = s1.(max_e') /\
    n = s2.(max_v') /\
    s2.(st_graph) = s1.(st_graph);
  err := fun s1 => False (* no error case *)
|}.

Definition get_new_edge' {T} : program (@state' T) Z := {|
  nrm :=
    fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') /\
    s2.(max_e') = s1.(max_e') + 1 /\
    n = s2.(max_v') /\
    s2.(st_graph) = s1.(st_graph);
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

(* Definition pregraph_add_whole_vertex' {T}
: program (@state' T) pg_nfa :=
  v <- get_new_vertex' ;;
  pregraph_add_vertex' v. *)

Definition pregraph_add_whole_edge' {T} (s t: Z) (c: option T)
: program state' pg_nfa :=
  e <- get_new_edge' ;;
  pregraph_add_edge' e s t c.

(* Definition nfa_to_elem' {T} (sv ev: Z) : program (@state' T) elem' := {|
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
|}. *)

Fixpoint regexToNFA' {T} (r : reg_exp T)
: program state' elem' :=
  match r with
  | EmptySet_r =>
    v1 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v2 ;;
    return (v1, v2)

  | EmptyStr_r =>
    v1 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 v2 None ;;
    return (v1, v2)

  | Char_r t =>
    v1 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 v2 (Some t) ;;
    return (v1, v2)

  | Concat_r r1 r2 =>
    '(sv1, ev1) <- regexToNFA' r1 ;;
    '(sv2, ev2) <- regexToNFA' r2 ;;
    pregraph_add_whole_edge' ev1 ev2 epsilon ;;
    return (sv1, ev2)

  | Union_r r1 r2 =>
    '(sv1, ev1) <- regexToNFA' r1 ;;
    '(sv2, ev2) <- regexToNFA' r2 ;;
    v1 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 sv1 epsilon ;;
    pregraph_add_whole_edge' v1 sv2 epsilon ;;
    pregraph_add_whole_edge' ev1 v2 epsilon ;;
    pregraph_add_whole_edge' ev2 v2 epsilon ;;
    return (v1, v2)

  | Star_r r =>
    '(sv, ev) <- regexToNFA' r ;;
    v1 <- get_new_vertex' ;;
    pregraph_add_vertex' v1 ;;
    v2 <- get_new_vertex' ;;
    pregraph_add_vertex' v2 ;;
    pregraph_add_whole_edge' v1 ev epsilon ;;
    pregraph_add_whole_edge' ev v2 epsilon ;;
    pregraph_add_whole_edge' ev sv epsilon ;;
    return (v1, v2)
  end.

(** recursion *)

End Graph_NFA_DEF.
