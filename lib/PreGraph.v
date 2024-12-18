Require Import CertiGraph.lib.Ensembles_ext.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
From StateMonad.monaderror Require Import monadEbasic.

Import MonadwitherrDeno.
Import MonadNotation.
Import SetsNotation.
Local Open Scope Z_scope.
Local Open Scope sets_scope.

Definition epsilon {T: Type} : option T := None.

Section GRAPH_DEF.

Record PreGraph {Vertex Edge: Type} := {
  vvalid : Ensemble Vertex;
  evalid : Ensemble Edge;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

(* We use Z as unique label for each vertex and edge. *)
(* And use `symbol` to record character on each edge based on label. *)
Record pg_nfa {T: Type} := {
  pg : @PreGraph Z Z;
  symbol : Z -> option T
}.

(* state without graph *)
Record state := {
  max_v : Z;
  max_e : Z
}.

Record elem {T: Type} := {
  startVertex : Z;
  endVertex : Z;
  graph : @pg_nfa T;
}.

(* state with graph *)
Record state' {T} := {
  max_v' : Z;
  max_e' : Z;
  st_graph : @pg_nfa T
}.

(* Record elem' := {
  startVertex' : Z;
  endVertex' : Z
}. *)

Definition elem' : Type := (Z * Z)%type.

Definition addValidFunc {T: Type} (v: T) (validFunc: Ensemble T) : Ensemble T :=
  fun n => validFunc n \/ n = v.

Definition updateEdgeFunc (edgeFunc: Z -> Z) (e: Z) (v: Z) :
  Z -> Z := fun n => if Z.eqb e n then v else edgeFunc n.

Definition removeValidFunc {T: Type} (v: T) (validFunc: Ensemble T) : Ensemble T :=
  fun n => validFunc n /\ n <> v.

Inductive step (pg: @PreGraph Z Z): Z -> Z -> Prop :=
  | step_intro: forall e x y, evalid pg e -> src pg e = x -> dst pg e = y -> step pg x y.

Definition edge (pg : @PreGraph Z Z) (n n' : Z) : Prop :=
  vvalid pg n /\ vvalid pg n' /\ step pg n n'.

Definition vertex_overlap {T: Type} : @pg_nfa T -> @pg_nfa T -> Prop :=
  fun g1 g2 =>
    exists v, vvalid g1.(pg) v /\ vvalid g2.(pg) v.

Definition edge_overlap {T} : @pg_nfa T -> @pg_nfa T -> Prop :=
  fun g1 g2 => exists v v', edge g1.(pg) v v' /\ edge g2.(pg) v v'.

Definition symbol_overlap {T} : @pg_nfa T -> @pg_nfa T -> Prop :=
  fun g1 g2 => exists e c1 c2, g1.(symbol) e = Some c1 /\ g2.(symbol) e = Some c2.

Definition G_add_vertex {T} : @pg_nfa T -> Z -> @pg_nfa T -> Prop :=
  fun G1 n G2 =>
    let g1 := G1.(pg) in
    let g2 := G2.(pg) in
    (~ vvalid g1 n) /\
    (forall v, g2.(vvalid) v <-> g1.(vvalid) v \/ v = n) /\
    (forall e, evalid g2 e <-> evalid g1 e) /\
    (forall e, g2.(src) e = g1.(src) e) /\
    (forall e, g2.(dst) e = g1.(dst) e) /\
    (forall e, G2.(symbol) e = G1.(symbol) e).

Definition G_add_edge {T} : pg_nfa -> Z -> Z -> Z -> option T -> pg_nfa -> Prop :=
  fun G1 n s t c G2 =>
    let g1 := G1.(pg) in
    let g2 := G2.(pg) in
    (g1.(vvalid) s /\ g1.(vvalid) t) /\
    (forall v, g2.(vvalid) v <-> g1.(vvalid) v) /\
    (~ g1.(evalid) n) /\
    (forall e, g2.(evalid) e <-> g1.(evalid) e \/ e = n) /\
    (forall e, g2.(src) e = g1.(src) e) /\
    (forall e, g2.(dst) e = g1.(dst) e) /\
    (forall e, G2.(symbol) e = if Z.eqb e n then c else G1.(symbol) e).

(* disjoint *)
Definition G_union_rel {T} : @pg_nfa T -> @pg_nfa T -> @pg_nfa T -> Prop :=
  fun g1 g2 g =>
    (forall v, vvalid g1.(pg) v \/ vvalid g2.(pg) v <-> vvalid g.(pg) v) /\
    (forall e, evalid g1.(pg) e \/ evalid g2.(pg) e <-> evalid g.(pg) e) /\
    (forall e, src g.(pg) e = if src g1.(pg) e >? 0
                              then src g1.(pg) e
                              else src g2.(pg) e) /\
    (forall e, dst g.(pg) e = if dst g1.(pg) e >? 0
                              then dst g1.(pg) e
                              else dst g2.(pg) e) /\
    (forall e, symbol g e = match symbol g1 e with
                            | Some c1 => Some c1
                            | None => symbol g2 e
                            end).

Definition G_disjoint {T} : @pg_nfa T -> @pg_nfa T -> Prop :=
  fun G1 G2 =>
    let g1 := G1.(pg) in
    let g2 := G2.(pg) in
    (forall v, g1.(vvalid) v /\ g2.(vvalid) v -> False) /\
    (forall e, g1.(evalid) e /\ g2.(evalid) e -> False).

End GRAPH_DEF.

Section GRAPH_EXAMPLE.

Definition empty_nfa {T: Type} : @pg_nfa T := {|
  (* ? Pose src/dst as `fun n => -1` to indicate emptyness *)
  pg := @Build_PreGraph Z Z (fun v => False) (fun e => False) (fun n => (-1)%Z) (fun n => (-1)%Z);
  symbol := fun _ => None
|}.

Definition emptyset_nfa {T: Type} (v1 v2 : Z) : @pg_nfa T := {|
  (* ? Pose src/dst as `fun n => -1` to indicate emptyness *)
  pg := @Build_PreGraph Z Z (fun v => v = v1 \/ v = v2) (fun e => False) (fun n => (-1)%Z) (fun n => (-1)%Z);
  symbol := fun _ => None
|}.

End GRAPH_EXAMPLE.

Section NFA_REL.

Definition e_step {T} (G: @pg_nfa T) : Z -> Z -> Prop :=
  fun x y => exists e, step G.(pg) x y /\ G.(symbol) e = None.

Definition e_steps {T} (G: @pg_nfa T) : Z -> Z -> Prop :=
  (** See SetsClass *)
  clos_refl_trans (e_step G).
(** TODO: SetsClass induction_1n transitivity_1n one_step vs n_step *)
(** rel *)

(** T -> rel *)
(** string_step : rel concat  *)
(** G_match_str := string_step + e_closure *)

(* ? *)
Definition c_step {T} (G: @pg_nfa T) (c: T) : Z -> Z -> Prop :=
  fun x y => exists e, step G.(pg) x y /\ G.(symbol) e = Some c.

Definition char_step {T} (G: @pg_nfa T) (c: T) : Z -> Z -> Prop :=
  (e_steps G) ∘ (c_step G c) ∘ (e_steps G).

Fixpoint string_step {T} (G: @pg_nfa T) (l: list T) : Z -> Z -> Prop :=
  match l with
  | nil => Rels.id
  | cons s l' => (char_step G s) ∘ (string_step G l')
  end.

Definition G_match_str {T} (G: @pg_nfa T) (sv ev: Z) (l: list T)
  : Prop := string_step G l sv ev.



(** Calculate the new e_closure when consuming a char *)
Definition closure_step {T} (G: @pg_nfa T) (ec: Z -> Prop) (c: T) : Z -> Prop :=
  fun y => exists x, ec x /\ c_step G c x y.

Fixpoint nfa_closure {T} (G: @pg_nfa T) (ec: Z -> Prop) (l: list T) : Z -> Prop :=
  match l with
  | nil => ec
  | cons s l' => nfa_closure G (closure_step G ec s) l'
  end.

Definition G_match_string {T} (G: @pg_nfa T) (sv ev: Z) (l: list T) : Prop :=
  (nfa_closure G (e_steps G sv) l) ev.

End NFA_REL.

(* step (epsilon / char) ; reflexive transitive closure *)
(* monad repeatBreak whileBreak *)
