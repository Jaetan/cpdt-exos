(* Define mutually inductive types of even and odd natural numbers,
   such that any natural nymber is isomorphic to one of the values of
   the two types. (This problem does not ask you to prove that
   correspondence, though some interpretations of the task may be
   interesting exercises.) Write a function that computes the sum of
   two even numbers, such that the function type guarantees that the
   output is even as well. Prove that this function is commutative.
*)

Inductive even_nat : Set :=
| Zero : even_nat
| ENext : odd_nat -> even_nat

with odd_nat : Set :=
| ONext : even_nat -> odd_nat.

Fixpoint even_add (x y : even_nat) : even_nat :=
  match x with
    | Zero => y
    | ENext (ONext z) => ENext (ONext (even_add z y))
  end.

Scheme even_nat_mut := Induction for even_nat Sort Prop
with odd_nat_mut := Induction for odd_nat Sort Prop.

(* Looking at how even_nat_add is written, even_add Zero e directly
   matches the Zero case, returning e; so even_add Zero e = e would be
   proved in one go. With the arguments to even_add in the reverse
   order, though, we need to use induction to get the result.
*)

Lemma even_add_zero_right :
  forall e : even_nat, even_add e Zero = e.
  intros.
  apply (even_nat_mut
           (fun e : even_nat => even_add e Zero = e)
           (fun o : odd_nat => even_add (ENext o) Zero = ENext o)) ;
    [ reflexivity               (* Zero case *)
    | intros ; assumption       (* odd_nat case *)
    | intros ; simpl even_add ; rewrite -> H ; reflexivity (* even_nat case *)
    ].
Qed.

(* This is the next step to prepare for the commutativity theorem.
   Addition stacks type constructors to its left; we need to prove
   that the stack can be unwound into the second argument to even_add.
 *)

Lemma even_add_constructors_commute :
  forall x y : even_nat,
    even_add (ENext (ONext x)) y = even_add x (ENext (ONext y)).

  intros.
  apply (even_nat_mut
           (fun e : even_nat => even_add (ENext (ONext e)) y = even_add e (ENext (ONext y)))
           (fun o : odd_nat => even_add (ENext (ONext (ENext o))) y = even_add (ENext o) (ENext (ONext y)))) ;
    [ reflexivity               (* Zero case *)
    | intros ; rewrite -> H ; reflexivity (* odd_nat case *)
    | intros ; simpl ; rewrite <- H ; reflexivity (* even_nat_case *)
    ].
Qed.

Theorem even_add_commutative:
  forall x y : even_nat, even_add x y = even_add y x.

  intros x y.
  apply (even_nat_mut
           (fun e : even_nat => even_add e y = even_add y e)
           (fun o : odd_nat => even_add (ENext o) y = even_add y (ENext o))) ;
    [ symmetry ; apply even_add_zero_right (* Zero case *)
    | intros ; apply H                     (* odd_nat case *)
    | intros ;
      rewrite <- even_add_constructors_commute ;
      simpl ; rewrite -> H ; reflexivity
    ].
Qed.
