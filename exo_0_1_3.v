(*
   Modify the first example language of Chapter 2 to include
   variables, where variables are represented with nat. Extend the
   syntax and semantics of expressions to accommodate the change. Your
   new expDenote function should take as a new extra first argument a
   value of type var -> nat , where var is a synonym for
   naturals-as-variables, and the function assigns a value to each
   variable. Define a constant folding function which does a bottom-up
   pass over an expression, at each stage replacing every binary
   operation on constants with an equivalent constant. Prove that
   constant folding preserves the meanings of expressions.
 *)

(*
   The representation of the expressions we will compute with, as well
   as the representation of the operations available on them:

    * Plus represents the abstract addition of natural numbers

    * Times represents the abstract multiplication of natural numbers

   The meaning of these operations (e.g. the mapping from their
   representation to the computation it stands for) is in binopDenote.
 *)
Inductive binop : Set := Plus | Times.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

(*
   Each variable is uniquely identified by a natural number. A
   valuation, which needs to be provided to each function manipulating
   variables, associates a variable with its value.
*)
Definition var := nat.
Definition valuation := var -> nat.

(*
   The representation of expressions wwe will compute with:

    * Const represents a constant natural number

    * Var represents a variable, whose identity is encoded as a
      natural number (such as its address in memory).

    * Binop represents one of the binary operations defined above.

   The function expDenote computes the meaning of an expression. The
   value of variables is resolved according to a valuation function,
   mapping the identity of a variable to its value. Thus, the
   variables in this example are global; changing the value of a
   variable amounts to passing a modified valuation function to
   expDenote and associated functions.
*)
Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Binop : binop -> exp -> exp -> exp.

Fixpoint expDenote (val : valuation) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => val v
    | Binop b e1 e2 => (binopDenote b) (expDenote val e1) (expDenote val e2)
  end.

(*
   This function folds constants inside expressions: constants and
   variables are left alone, and operations whose operands are both
   constants (or can be folded into constants) are replaced by the
   equivalent constant.

   We rely on expDenote, defined above, to compute the value of
   expressions, The interface of this function forces us to pass a
   valuation around, even if we are not in fact touching
   variables. One way to cope with this situation is to define a dymmy
   valuation, which just returns a default value for any variable.
*)
Definition dummyValuation : valuation := fun v => O.

Fixpoint foldConstants (e : exp) : exp :=
  match e with
    | Const n => Const n
    | Var v => Var v
    | Binop b e1 e2 =>
      match foldConstants e1, foldConstants e2 with
        | Const c1, Const c2 => Const ((binopDenote b)
                                         (expDenote dummyValuation (Const c1))
                                         (expDenote dummyValuation (Const c2)))
        | e'1, e'2 => Binop b e'1 e'2
      end
  end.

(*
   To use our induction hypotheses for binary operators while proving
   the conservation of the meaning of expressions, we will need to
   distribute constant folding over binary operators. So let us first
   show that this distribution is valid.
*)
Lemma constant_folding_distributes_over_binop :
  forall v e1 e2 b,
    expDenote v (foldConstants (Binop b e1 e2)) = expDenote v (Binop b (foldConstants e1) (foldConstants e2)).

  intros.
  simpl.
  destruct (foldConstants e1) ; destruct (foldConstants e2) ; reflexivity.
Qed.

Theorem constant_folding_preserves_meaning :
  forall v e, expDenote v (foldConstants e) = expDenote v e.

  intros.
  induction e ;
    [ reflexivity
    | reflexivity
    | rewrite -> constant_folding_distributes_over_binop ;
      destruct (foldConstants e1) ; destruct (foldConstants e2) ; simpl ;
      rewrite <- IHe1 ; rewrite <- IHe2 ;
      reflexivity
    ].
Qed.
