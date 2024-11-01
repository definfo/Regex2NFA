Require Import CertiGraph.lib.Ensembles_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.lib.relation_list.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
From StateMonad.monaderror Require Import monadEbasic.

Import MonadwitherrDeno.
Import MonadNotation.
Local Open Scope Z_scope.

Definition epsilon : option ascii := None.

Section GRAPH_DEF.

Record PreGraph {Vertex Edge: Type} := {
  vvalid : Ensemble Vertex;
  evalid : Ensemble Edge;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

(* We use Z as unique label for each vertex and edge. *)
(* And use `symbol` to record character on each edge based on label. *)
Record pg_nfa := {
  pg : @PreGraph Z Z;
  symbol : Z -> option ascii
}.

Record elem := {
  startVertex : Z;
  endVertex : Z;
  graph : pg_nfa;
}.

Definition empty_nfa : pg_nfa := {|
  (* ? Pose src/dst as `fun n => -1` to indicate emptyness *)
  pg := @Build_PreGraph Z Z (fun v => False) (fun e => False) (fun n => (-1)%Z) (fun n => (-1)%Z);
  symbol := fun n => None
|}.

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

Definition vertex_overlap : pg_nfa -> pg_nfa -> Prop :=
  fun g1 g2 =>
    exists v, vvalid g1.(pg) v /\ vvalid g2.(pg) v.

Definition edge_overlap : pg_nfa -> pg_nfa -> Prop :=
  fun g1 g2 => exists v v', edge g1.(pg) v v' /\ edge g2.(pg) v v'.

Definition symbol_overlap : pg_nfa -> pg_nfa -> Prop :=
  fun g1 g2 => exists e c1 c2, g1.(symbol) e = Some c1 /\ g2.(symbol) e = Some c2.

Definition G_add_vertex : pg_nfa -> Z -> pg_nfa -> Prop :=
  fun G1 n G2 =>
    let g1 := G1.(pg) in
    let g2 := G2.(pg) in
    (~ vvalid g1 n) /\
    (forall e, g2.(vvalid) e <-> g1.(vvalid) e \/ e = n) /\
    (forall v, evalid g2 v <-> evalid g1 v) /\
    (forall e, g2.(src) e = g1.(src) e) /\
    (forall e, g2.(dst) e = g1.(dst) e) /\
    (forall e, G2.(symbol) e = G1.(symbol) e).

Definition G_add_edge : pg_nfa -> Z -> Z -> Z -> option ascii -> pg_nfa -> Prop :=
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
Definition G_union : pg_nfa -> pg_nfa -> pg_nfa -> Prop :=
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

End GRAPH_DEF.
