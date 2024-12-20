Require Import Coq.ZArith.ZArith.
From SetsClass Require Import SetsClass.
Local Open Scope sets_scope.
Local Open Scope list_scope.
(* Definition of regular expressiontheories/st_graph_nfa.v theories/st_nograph_nfa.v on alphabet T 
   in Software Foundations *)
(*? remove Question/Plus *)

(* TODO: Denotational defined regex *)
(* String -> Prop *)
(* Star r := Union (r^0, r^1, ..., r^n)  *)

Inductive reg_exp (T: Type) : Type :=
  (* Ø *)
  | EmptySet_r
  (* '' *)
  | EmptyStr_r
  (* 't' *)
  | Char_r (t : T -> Prop)
  (* '<r1><r2>' *)
  | Concat_r (r1 r2 : reg_exp T)
  (* '<r1>|<r2>' *)
  | Union_r (r1 r2 : reg_exp T)
  (* '<r>*' *)
  | Star_r (r : reg_exp T).

Arguments EmptySet_r {T}.
Arguments EmptyStr_r {T}.
Arguments Char_r {T} _.
Arguments Concat_r {T} _ _.
Arguments Union_r {T} _ _.
Arguments Star_r {T} _.

Definition set_prod {T} (A B : list T -> Prop) : list T -> Prop :=
  fun s => exists s1 s2, s1 ∈ A /\ s2 ∈ B /\ s = s1 ++ s2.

Fixpoint star_r_indexed {T} (n : nat) (s : list T -> Prop) : list T -> Prop :=
  match n with
  | 0 => [ nil ]
  | S n' => set_prod s (star_r_indexed n' s)
  end.

Fixpoint exp_match {T} (r : reg_exp T) : list T -> Prop :=
  match r with
  | EmptySet_r => ∅
  | EmptyStr_r => [ nil ]
(*   | Char_r t => [ (cons t nil) ] *)
  | Char_r t => fun s => exists c, c ∈ t /\ s = (cons c nil)
  | Concat_r r1 r2 => set_prod (exp_match r1) (exp_match r2)
  | Union_r r1 r2 => (exp_match r1) ∪ (exp_match r2)
  | Star_r r => ⋃ star_r_indexed (exp_match r)
  end.

(** Proof: exp_match *)
(** (v_n,v_m) <= (v_n', v_m') *)
(** interval (v_n,v_m) return_graph (v_n', v_m') *)
(** correctness *)
(** 1. st_graph: Hoare triple definition + Admitted. *)
(** 2. Refinement proof between st_nograph and st_graph *)
(** forall G: graph, (low_level state = G & alloc same val), execute, (ret val start,end same , Hi ret graph ⋃ G = G') *)
