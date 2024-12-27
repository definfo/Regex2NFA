Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
From StateMonad.monaderror Require Import monadEbasic.

Import MonadwitherrDeno.
Import MonadNotation.
Import SetsNotation.
Local Open Scope Z_scope.
Local Open Scope sets_scope.

(** Set relations *)

Definition Sets_disjoint_union {X: Type} (A B C: X -> Prop): Prop :=
  A ∩ B == ∅ /\
  A ∪ B == C.

Definition Sets_overlap {X: Type} (A B: X -> Prop): Prop :=
  exists x, x ∈ A /\ x ∈ B.

Module Graph.

Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y.

Record add_vertex {V E} (g1: PreGraph V E) (v: V) (g2: PreGraph V E): Prop :=
{
  add_vertex_vertex:
    Sets_disjoint_union g1.(vvalid) (Sets.singleton v) g2.(vvalid);
  add_vertex_edge:
    g1.(evalid) == g2.(evalid);
  add_vertex_src:
    forall e, e ∈ g1.(evalid) -> g2.(src) e = g1.(src) e;
  add_vertex_dst:
    forall e, e ∈ g1.(evalid) -> g2.(dst) e = g1.(dst) e;
}.

Record add_edge {V E} (g1: PreGraph V E) (e0: E) (x y: V) (g2: PreGraph V E): Prop :=
{
  add_edge_vertex:
    g1.(vvalid) == g2.(vvalid);
  add_edge_edge:
    Sets_disjoint_union g1.(evalid) (Sets.singleton e0) g2.(evalid);
  add_edge_src_old:
    forall e, e ∈ g1.(evalid) -> g2.(src) e = g1.(src) e;
  add_edge_dst_old:
    forall e, e ∈ g1.(evalid) -> g2.(dst) e = g1.(dst) e;
  add_edge_src_new: g2.(src) e0 = x;
  add_edge_dst_new: g2.(dst) e0 = y;
}.

(* disjoint union *)
Record union_rel {V E} (g1 g2 g: PreGraph V E): Prop :=
{
  union_vertex: Sets_disjoint_union g1.(vvalid) g2.(vvalid) g.(vvalid);
  union_edge: Sets_disjoint_union g1.(evalid) g2.(evalid) g.(evalid);
  union_src1: forall e, e ∈ g1.(evalid) -> g.(src) e = g1.(src) e;
  union_src2: forall e, e ∈ g2.(evalid) -> g.(src) e = g2.(src) e;
  union_dst1: forall e, e ∈ g1.(evalid) -> g.(dst) e = g1.(dst) e;
  union_dst2: forall e, e ∈ g2.(evalid) -> g.(dst) e = g2.(dst) e;
}.

End Graph.

Notation "'PreGraph'" := (Graph.PreGraph) (at level 0).
Notation "pg '.(vvalid)'" := (Graph.vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (Graph.evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (Graph.src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (Graph.dst _ _ pg) (at level 1).


(** NFA definition *)

Section PG_NFA.

Definition epsilon {T: Type} : option T := None.

(* We use Z as unique label for each vertex and edge. *)
(* And use `symbol` to record character on each edge based on label. *)
(** represent multi-edge symbol(s) as symbol set *)
Record pg_nfa (T: Type) := {
  pg : PreGraph Z Z;
  symbol : Z -> option (T -> Prop)
}.

Notation "g '.(pg)'" := (pg _ g) (at level 1).
Notation "g '.(symbol)'" := (symbol _ g) (at level 1).

Record add_vertex {T} (g1: pg_nfa T) (v: Z) (g2: pg_nfa T): Prop :=
{
  add_vertex_pg:
    Graph.add_vertex g1.(pg) v g2.(pg);
  add_vertex_symbol:
    forall e, e ∈ g1.(pg).(evalid) -> g2.(symbol) e = g1.(symbol) e;
}.

Record add_edge {T} (g1: pg_nfa T) (e0 x y: Z) t (g2: pg_nfa T): Prop :=
{
  add_edge_pg:
    Graph.add_edge g1.(pg) e0 x y g2.(pg);
  add_edge_symbol_old:
    forall e, e ∈ g1.(pg).(evalid) -> g2.(symbol) e = g1.(symbol) e;
  add_edge_symbol_new:
    g2.(symbol) e0 = t;
}.

Record union_rel {T} (g1 g2 g: pg_nfa T): Prop :=
{
  union_pg: Graph.union_rel g1.(pg) g2.(pg) g.(pg);
  union_symbol1: forall e, e ∈ g1.(pg).(evalid) -> g.(symbol) e = g1.(symbol) e;
  union_symbol2: forall e, e ∈ g2.(pg).(evalid) -> g.(symbol) e = g2.(symbol) e;
}.

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
    (fun n => if n =? e then y else g.(pg).(dst) n)
  );
  symbol := fun n => if n =? e then c else g.(symbol) n
|}.

Definition empty_nfa {T: Type} : pg_nfa T := {|
  (* ? Pose src/dst as `fun n => -1` to indicate emptyness *)
  pg := @Graph.Build_PreGraph Z Z (fun v => False) (fun e => False) (fun n => (-1)%Z) (fun n => (-1)%Z);
  symbol := fun _ => None
|}.

Definition emptyset_nfa {T: Type} (v1 v2 : Z) : pg_nfa T :=
  pregraph_add_vertex (pregraph_add_vertex empty_nfa v1) v2.

Definition emptystr_nfa {T: Type} (e1: Z) (v1 v2 : Z) : pg_nfa T :=
  pregraph_add_edge (emptyset_nfa v1 v2) e1 v1 v2 None.

Definition e_step {T} (G: pg_nfa T) : Z -> Z -> Prop :=
  fun x y => exists e, Graph.step_aux G.(pg) e x y /\ G.(symbol) e = None.

Definition e_steps {T} (G: pg_nfa T) : Z -> Z -> Prop :=
  clos_refl_trans (e_step G).

Definition c_step {T} (G: pg_nfa T) (c: T) : Z -> Z -> Prop :=
  fun x y =>
    (* t: T -> Prop *)
    exists e t, Graph.step_aux G.(pg) e x y /\ G.(symbol) e = Some t /\ c ∈ t.

(** FIX *)
Definition char_step {T} (G: pg_nfa T) (c: T) : Z -> Z -> Prop :=
  (c_step G c) ∘ (e_steps G).

(** FIX *)
Fixpoint string_step {T} (G: pg_nfa T) (l: list T) : Z -> Z -> Prop :=
  match l with
  | nil => e_steps G
  | cons s l' => (string_step G l') ∘ (char_step G s)
  end.

Definition G_match_str {T} (G: pg_nfa T) (sv ev: Z) (l: list T)
  : Prop := string_step G l sv ev.

End PG_NFA.

(** Reserved relations for DFA representation *)

(* Calculate the new e_closure when consuming a char *)
Definition closure_step {T} (G: pg_nfa T) (ec: Z -> Prop) (c: T) : Z -> Prop :=
  fun y => exists x, ec x /\ c_step G c x y.

Fixpoint nfa_closure {T} (G: pg_nfa T) (ec: Z -> Prop) (l: list T) : Z -> Prop :=
  match l with
  | nil => ec
  | cons s l' => nfa_closure G (closure_step G ec s) l'
  end.

Definition G_match_string {T} (G: pg_nfa T) (sv ev: Z) (l: list T) : Prop :=
  (nfa_closure G (e_steps G sv) l) ev.


Section NFA_REL.

(* state without graph *)
Record state := {
  max_v : Z;
  max_e : Z
}.

Record elem (T: Type) := {
  startVertex : Z;
  endVertex : Z;
  graph : pg_nfa T;
}.

(* state with graph *)
Record state' (T: Type) := {
  max_v' : Z;
  max_e' : Z;
  st_graph : pg_nfa T
}.

Definition elem' : Type := (Z * Z)%type.

End NFA_REL.

Module PreGraphNotations.

Declare Scope pg_scope.
Delimit Scope pg_scope with pg.

Notation "'PreGraph'" := (Graph.PreGraph) (at level 0).
Notation "pg '.(vvalid)'" := (Graph.vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (Graph.evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (Graph.src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (Graph.dst _ _ pg) (at level 1).

Notation "g '.(pg)'" := (pg _ g) (at level 1).
Notation "g '.(symbol)'" := (symbol _ g) (at level 1).

Notation "s '.(max_v)'" := (max_v s) (at level 1).
Notation "s '.(max_e)'" := (max_e s) (at level 1).

Notation "el '.(startVertex)'" := (startVertex _ el) (at level 1).
Notation "el '.(endVertex)'" := (endVertex _ el) (at level 1).
Notation "el '.(graph)'" := (graph _ el) (at level 1).

Notation "s '.(max_v')'" := (max_v' _ s) (at level 1).
Notation "s '.(max_e')'" := (max_e' _ s) (at level 1).
Notation "s '.(st_graph)'" := (st_graph _ s) (at level 1).

End PreGraphNotations.
