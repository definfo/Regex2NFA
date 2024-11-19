Require Import Regex2NFA.lib.PreGraph.
Require Import Regex2NFA.theories.st_graph_nfa.
Require Import Regex2NFA.theories.st_nograph_nfa.
Require Import Regex2NFA.theories.regex.
Require Import Coq.ZArith.ZArith.
From StateMonad.monaderror Require Import monadEbasic.
From StateMonad.monaderror Require Import monadEhoare.

Import MonadNotation.
Local Open Scope stmonad_scope.
Local Open Scope Z_scope.

(** high_level prop *)
Lemma st_nograph_inc {T: Type} :
  forall (G: @pg_nfa T) (r: reg_exp T), exists (v e : Z),
  Hoare (fun s1 => s1.(max_v) = v /\
                   s1.(max_e) = e)
        (regexToNFA r)
        (fun el s2 => el.(startVertex) >= v /\
                      el.(endVertex) >= v /\
                      G_disjoint G el.(graph) ).
Proof.
Admitted.

(** high_level (st_nograph)
(v, e)
(sv, ev, G_ret) <- execute
(v', e')
*)
(** low_level (st_graph)
(v, e, G)
(sv, ev) <- execute'
(v', e', G')
*)
(* Lemma graph_corr_prop {T: Type} :
  forall (G: @pg_nfa T) (r: reg_exp T) (v e: Z),
  exists (G_ret: @pg_nfa T) (v' e' sv ev : Z),
  (** low_level : @Hoare state' elem' *)
  Hoare (fun s1 => s1.(st_graph) = G /\
                   s1.(max_v') = v /\
                   s1.(max_e') = e )
        (regexToNFA' r)
        (fun el s2 => s2.(max_v') = v' /\
                      s2.(max_e') = e' /\
                      G1_union G G_ret s2.(st_graph) ) /\
  (** high_level : @Hoare state elem *)
  Hoare (fun s1 => s1.(max_v) = v /\
                   s1.(max_e) = e)
        (regexToNFA r)
        (fun el s2 => s2.(max_v) = v' /\
                      s2.(max_e) = e' /\
                      el.(startVertex) = sv /\
                      el.(endVertex) = ev /\
                      el.(graph) = G_ret).
  (* v' >= v /\ e' >= e *)
  (* sv > v /\ sv <= v' /\ ev > v /\ ev <= v' *)
  (** el.(graph) rel *)
  (*? edge rel *)
Proof.
Admitted. *)