(* This file is not an exercise from the book. It is a small
   experiment with some properties of inductive types; the type
   defined here would correspond to a C++ class with only a copy
   constructor and all other constructors deleted.
 *)

Require Import Equality Tactics.

Inductive weird : Set :=
| W : weird -> weird.

Section inhabitation.

  (* Some elementary properties of the constructor W, all direct
     consequences of the inductive nature of the type.
   *)

  Definition invariant (w : weird) : Prop := W w = w.

  (* The constructor conserves indempotent values *)
  Lemma L1 : forall w : weird, invariant w -> invariant (W w).
    intros w H.
    rewrite -> H.
    assumption.
  Qed.

  (* The constructor is idempotent *)
  Lemma L2 : forall w : weird, invariant w.
    induction w.
    rewrite -> IHw.
    assumption.
  Qed.    

  (* Every value has an antecedent *)
  Lemma L3 : forall w : weird, exists v : weird, W v = w.
    induction w.
    exists w.
    reflexivity.
  Qed.    

  (* All values are equal, e.g. there is at most 1 value in the type *)
  Lemma L4 : forall x y : weird, x = y.
    intro x.
    induction (W x).
    assumption.
  Qed.    

  (* Independently of the above, the main result is that the type is uninhabitated *)
  Theorem uninhabitable : weird -> False.
    intro x.
    induction x.
    assumption.    
  Qed.

End inhabitation.
