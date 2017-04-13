(*
   Define an inductive type slist that implements lists with support
   for constant-time concatenation. This type should be polymorphic in
   a choice of type for data values in lists. The type slist should
   have three constructors, for empty lists, singleton lists, and
   concatenation. Define a function flatten that converts slist s to
   list s. (You will want to run Require Import List. to bring list
   definitions into scope.) Finally, prove that flatten distributes
   over concatenation, where the two sides of your quantified equality
   will use the slist and list versions of concatenation, as
   appropriate. Recall from Chapter 2 that the infix operator ++ is
   syntactic sugar for the list concatenation function app.
*)

Require Import List.
Set Implicit Arguments.

Inductive slist (T : Set) : Set :=
| Snil : slist T
| Ssing : list T -> slist T
| Sconc : list T -> list T -> slist T.

Fixpoint flatten (T : Set) (l : slist T) : list T :=
  match l with
    | Snil => nil
    | Ssing s =>  s
    | Sconc s t => s ++ t
  end.

Theorem flatten_distributive :
  forall T : Set, forall s t : list T, flatten (Sconc s t) = s ++ t.

  intros.
  simpl.
  reflexivity.
Qed.
