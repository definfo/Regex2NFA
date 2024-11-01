(* Definition of regular expression on alphabet T 
   in Software Foundations *)
(* TODO: add '()' '[]' '{n}' *)

Inductive reg_exp (T : Type) : Type :=
  (* Ø *)
  | EmptySet
  (* '' *)
  | EmptyStr
  (* 't' *)
  | Char (t : T)
  (* '<r1><r2>' *)
  | Concat (r1 r2 : reg_exp T)
  (* '<r1>|<r2>' *)
  | Union (r1 r2 : reg_exp T)
  (* '<r>*' *)
  | Star (r : reg_exp T)
  (* '<r>?' *)
  | Question (r : reg_exp T)
  (* '<r>+' *)
  | Plus (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments Concat {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.
Arguments Question {T} _.
Arguments Plus {T} _.

Reserved Notation "s =~ re" (at level 80).

(* If the string can be matched by the reg_exp *)
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : nil =~ EmptyStr
  | MChar x : cons x nil =~ (Char x)
  | MConcat s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (Concat re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : nil =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  | MQuestion0 re : nil =~ (Question re)
  | MQuestion1 s re
               (H : s =~ re)
               : s =~ (Question re)
  | MPlus1 s re
            (H : s =~ re)
            : s =~ (Plus re)
  | MPlusApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Plus re))
               : (s1 ++ s2) =~ (Plus re)

  where "s =~ re" := (exp_match s re).
