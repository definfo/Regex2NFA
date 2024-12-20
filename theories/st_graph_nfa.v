Require Import Regex2NFA.lib.PreGraph.
Require Import Regex2NFA.theories.regex.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
From SetsClass Require Import SetsClass.
From StateMonad.monaderror Require Import monadEbasic.

Import MonadwitherrDeno.
Import MonadNotation.
Import PreGraphNotations.
Local Open Scope Z_scope.
Local Open Scope stmonad_scope.
Local Open Scope pg_scope.

(** program state' (sv, ev) *)

Definition get_new_vertex' {T} : program (state' T) Z := {|
  nrm := fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') + 1 /\
    s2.(max_e') = s1.(max_e') /\
    n = s2.(max_v') /\
    s2.(st_graph) = s1.(st_graph);
  err := fun s1 => False (* no error case *)
|}.

Definition get_new_edge' {T} : program (state' T) Z := {|
  nrm :=
    fun s1 n s2 =>
    s2.(max_v') = s1.(max_v') /\
    s2.(max_e') = s1.(max_e') + 1 /\
    n = s2.(max_e') /\
    s2.(st_graph) = s1.(st_graph);
  err := fun s1 => False (* no error case *)
|}.

Definition G_add_vertex' {T} : program (state' T) Z := {|
  nrm := fun s1 n s2 =>
    let G1 := s1.(st_graph) in
    let G2 := s2.(st_graph) in
    s2.(max_v') = s1.(max_v') + 1 /\
    s2.(max_e') = s1.(max_e') /\
    add_vertex G1 s2.(max_v') G2 /\
    n = s2.(max_v');
  err := fun s1 => False (* no error case *)
|}.

Definition G_add_edge' {T} (x y: Z) t : program (state' T) Z := {|
  nrm := fun s1 n s2 =>
    let G1 := s1.(st_graph) in
    let G2 := s2.(st_graph) in
    s2.(max_v') = s1.(max_v') /\
    s2.(max_e') = s1.(max_e') + 1 /\
    add_edge G1 s2.(max_e') x y t G2 /\
    n = s2.(max_e');
  err := fun s1 => False (* error if edge exists *)
  (*? or  *)
|}.

Fixpoint regexToNFA' {T} (r : reg_exp T)
: program (state' T) elem' :=
  match r with
  | EmptySet_r =>
    v1 <- G_add_vertex' ;;
    v2 <- G_add_vertex' ;;
    return (v1, v2)

  | EmptyStr_r =>
    v1 <- G_add_vertex' ;;
    v2 <- G_add_vertex' ;;
    G_add_edge' v1 v2 epsilon ;;
    return (v1, v2)

  | Char_r t =>
    v1 <- G_add_vertex' ;;
    v2 <- G_add_vertex' ;;
    G_add_edge' v1 v2 (Some t) ;;
    return (v1, v2)

  | Concat_r r1 r2 =>
    '(sv1, ev1) <- regexToNFA' r1 ;;
    '(sv2, ev2) <- regexToNFA' r2 ;;
    G_add_edge' ev1 ev2 epsilon ;;
    return (sv1, ev2)

  | Union_r r1 r2 =>
    '(sv1, ev1) <- regexToNFA' r1 ;;
    '(sv2, ev2) <- regexToNFA' r2 ;;
    v1 <- G_add_vertex' ;;
    v2 <- G_add_vertex' ;;
    G_add_edge' ev1 ev2 epsilon ;;
    G_add_edge' v1 sv2 epsilon ;;
    G_add_edge' ev1 v2 epsilon ;;
    G_add_edge' ev2 v2 epsilon ;;
    return (v1, v2)

  | Star_r r =>
    '(sv, ev) <- regexToNFA' r ;;
    v1 <- G_add_vertex' ;;
    v2 <- G_add_vertex' ;;
    G_add_edge' v1 ev epsilon ;;
    G_add_edge' ev v2 epsilon ;;
    G_add_edge' ev sv epsilon ;;
    return (v1, v2)
  end.

(** recursion *)
