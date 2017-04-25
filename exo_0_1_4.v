(* Reimplement the second example language of Chapter 2 to use
   mutually inductive types instead of dependent types. That is,
   define two separate (non-dependent) inductive types nat_exp and
   bool_exp for expressions of the two different types, rather than a
   single indexed type. To keep things simple, you may consider only
   the binary opera- tors that take naturals as operands. Add natural
   number variables to the language, as in the last exercise, and add
   an ¡Èif¡É expression form taking as arguments one boolean
   expression and two natural number expressions. Define semantics and
   constant-folding functions for this new language. Your constant
   folding should simplify not just binary operations (returning
   naturals or booleans) with known arguments, but also ¡Èif¡É
   expressions with known values for their test expressions but
   possibly undetermined ¡Èthen¡É and ¡Èelse¡É cases. Prove that
   constant-folding a natural number expression preserves its meaning.
*)

Require Import Arith Bool.

(* As in the previous exercise, we represent variables with natural
   numbers that stand for the variable's identity. The variables are
   again global, and a valuation function is used to map each variable
   to its current value.
*)
Definition var := nat.
Definition valuation := var -> nat.

(* We define two kinds of expressions; expressions on natural numbers,
   and expressions on booleans.

   For expressions on natural numbers:

    * NConst represents a natural number constant

    * NVar represents a variable identified by a natural number

    * NPlus represents the addition of two expressions on natural
      numbers

    * NTimes represents the product of two expressions on natural
      numbers

    * NIf represents branching; its first argument, a boolean
      expression, represents the condition to check. Its second
      argument, the natural number expression to evaluate if the
      condition is true (the "then" branch), and its third argument
      the natural number expression to ecaluate if the condition is
      false (the "else" branch).

   For expressions on booleans:

    * BConst represents a boolean constant

    * BNot represents the negation of a boolean expression

    * BAnd represents the conjonction of two boolean expressions

    * BOr represents the disjunction of two boolean expressions

    * BEqB represents the equality of two boolean expressions.

    * BEqN represents the equality of two expressions on natural
      numbers. This allows NIf to support expressions like "if n1 = n2
      then expr1 else expr2", with n1 and n2 any natural number
      expressions.
*)
Inductive nat_exp : Set :=
| NConst : nat -> nat_exp
| NVar : var -> nat_exp
| NPlus : nat_exp -> nat_exp -> nat_exp
| NTimes : nat_exp -> nat_exp -> nat_exp
| NIf : bool_exp -> nat_exp -> nat_exp -> nat_exp

with bool_exp : Set :=
| BConst : bool -> bool_exp
| BNot : bool_exp -> bool_exp
| BAnd : bool_exp -> bool_exp -> bool_exp
| BOr : bool_exp -> bool_exp -> bool_exp
| BEqB : bool_exp -> bool_exp -> bool_exp
| BEqN : nat_exp -> nat_exp -> bool_exp.

Fixpoint nat_exp_denote (v : valuation) ( e : nat_exp) : nat :=
  match e with
    | NConst n => n
    | NVar x => v x
    | NPlus x y => (nat_exp_denote v x) + (nat_exp_denote v y)
    | NTimes x y => (nat_exp_denote v x) * (nat_exp_denote v y)
    | NIf b e1 e2 => if (bool_exp_denote v b) then (nat_exp_denote v e1) else (nat_exp_denote v e2)
  end

with bool_exp_denote (v : valuation) (e : bool_exp) : bool :=
       match e with
         | BConst b => b
         | BNot b => negb (bool_exp_denote v b)
         | BAnd x y => andb (bool_exp_denote v x) (bool_exp_denote v y)
         | BOr x y => orb (bool_exp_denote v x) (bool_exp_denote v y)
         | BEqB x y => eqb (bool_exp_denote v x) (bool_exp_denote v y)
         | BEqN x y=> beq_nat (nat_exp_denote v x) (nat_exp_denote v y)
       end.

(* These are the constant folding functions. Each case runs constant
   folding on its operands, checks if the results are constants, and
   in this case builds an appropriate constant expression.
*)
Fixpoint nat_exp_cfold (v : valuation) (e : nat_exp) : nat_exp :=
  match e with
    | NConst n => NConst n
    | NVar x => NVar x
    | NPlus x y => let (cfx, cfy) := (nat_exp_cfold v x, nat_exp_cfold v y) in
                   match cfx, cfy with
                     | NConst x1, NConst x2 => NConst (nat_exp_denote v (NPlus (NConst x1) (NConst x2)))
                     | _, _ => NPlus cfx cfy
                   end
    | NTimes x y => let (cfx, cfy) := (nat_exp_cfold v x, nat_exp_cfold v y) in
                    match cfx, cfy with
                      | NConst x1, NConst x2 => NConst (nat_exp_denote v (NTimes (NConst x1) (NConst x2)))
                      | _, _ => NTimes cfx cfy
                    end
    | NIf b x y => let cfb := bool_exp_cfold v b in
                   let (cfx, cfy) := (nat_exp_cfold v x, nat_exp_cfold v y) in
                   match cfb with
                     | BConst b1 => if b1 then cfx else cfy
                     | _ => NIf cfb cfx cfy
                   end
  end

with bool_exp_cfold (v : valuation) (e : bool_exp) : bool_exp :=
       match e with
         | BConst b => BConst b
         | BNot b => let cfx := bool_exp_cfold v b in
                     match cfx with
                       | BConst b1 => BConst (negb b1)
                       | _ => BNot cfx
                     end
         | BAnd x y => let (cfx, cfy) := (bool_exp_cfold v x, bool_exp_cfold v y) in
                       match cfx, cfy with
                         | BConst x1, BConst x2 => BConst (bool_exp_denote v (BAnd (BConst x1) (BConst x2)))
                         | _, _ => BAnd cfx cfy
                       end
         | BOr x y => let (cfx, cfy) := (bool_exp_cfold v x, bool_exp_cfold v y) in
                      match cfx, cfy with
                        | BConst x1, BConst x2 => BConst (bool_exp_denote v (BOr (BConst x1) (BConst x2)))
                        | _, _ => BOr cfx cfy
                      end
         | BEqB x y => let (cfx, cfy) := (bool_exp_cfold v x, bool_exp_cfold v y) in
                       match cfx, cfy with
                         | BConst x1, BConst x2 => BConst (bool_exp_denote v (BEqB (BConst x1) (BConst x2)))
                         | _, _ => BEqB cfx cfy
                       end
         | BEqN x y => let (cfx, cfy) := (nat_exp_cfold v x, nat_exp_cfold v y) in
                       match cfx, cfy with
                         | NConst x1, NConst x2 => BConst (bool_exp_denote v (BEqN (NConst x1) (NConst x2)))
                         | _, _ => BEqN cfx cfy
                       end
       end.

Scheme nat_exp_mut := Induction for nat_exp Sort Prop
with bool_exp_mut := Induction for bool_exp Sort Prop.

(* To prove by induction that constant folding preserves the meaning
   of expressions, we will need to prove that constant folding
   distributes over each of the constructors for expressions. For
   clarity of the proof, we write one lemma for each constructor with
   two operands, since distribution is proved in the same way for each
   of them. Single operand constructors lead to proofs that are almost
   trivial, and are thus kept in the body of the main proof.

   Then, we factor the proofs in the user-defined tactic below, and
   call this tactic to dispatch each of the lemmas.

   The tactic binop_case below expects to be called in the context of
   our lemmas on binary operations, with a goal made of several
   implications, from which the following variables can be introduced
   as hypotheses:

    * a valuation function v

    * the 2 operands x1 and x2

    * one induction hypothesis for each of these variables

   In almost all cases, the name of the constant folding function in
   the conclusion is the same as that of the constant folding function
   in the hypothesis. But for BEqN, the conclusion is for boolean
   expressions, while the hypotheses are for natural expressions. So
   the tactic needs to retrieve the correct constant folding function
   for the current operation.

   The tactic works by matching the goal against a desired context of
   the form [ <variable> : <type>, ... |- <conclusion> ], where
   underscores stand for "don't care" arguments, and variables with
   question marks in their names are unified with the part of the
   hypothesis or variable they hold place for. Once the goal is
   matched, all variables become available to give as parameters to
   the tactics that will be executed.
*)

Ltac binop_case :=
  intros v x1 x2 Hx1 Hx2 ;
  match goal with
    | [ v : _, x1 : _, x2 : _,
        Hx1 : ?d1 v (?cfold v x1) = ?d1 v x1,
        Hx2 : ?d2 v (?cfold v x2) = ?d2 v x2
        |- ?denote v (_ v ?e) = ?denote v ?e ] =>
      simpl denote at 2 ; rewrite <- Hx1 ; rewrite <- Hx2 ; simpl denote at 1 ;
      destruct (cfold v x1) ; destruct (cfold v x2) ;
      reflexivity
  end.

Lemma NPlus_case:
  forall v e1 e2,
    nat_exp_denote v (nat_exp_cfold v e1) = nat_exp_denote v e1 ->
    nat_exp_denote v (nat_exp_cfold v e2) = nat_exp_denote v e2 ->
    nat_exp_denote v (nat_exp_cfold v (NPlus e1 e2)) = nat_exp_denote v (NPlus e1 e2).

  binop_case.
Qed.

Lemma NTimes_case:
  forall v e1 e2,
    nat_exp_denote v (nat_exp_cfold v e1) = nat_exp_denote v e1 ->
    nat_exp_denote v (nat_exp_cfold v e2) = nat_exp_denote v e2 ->
    nat_exp_denote v (nat_exp_cfold v (NTimes e1 e2)) = nat_exp_denote v (NTimes e1 e2).

  binop_case.
Qed.

Lemma NIf_case:
  forall v b e1 e2,
    bool_exp_denote v (bool_exp_cfold v b) = bool_exp_denote v b ->
    nat_exp_denote v (nat_exp_cfold v e1) = nat_exp_denote v e1 ->
    nat_exp_denote v (nat_exp_cfold v e2) = nat_exp_denote v e2 ->
    nat_exp_denote v (nat_exp_cfold v (NIf b e1 e2)) = nat_exp_denote v (NIf b e1 e2).

  intros v b e1 e2 Hb He1 He2.
  simpl nat_exp_denote at 2.
  rewrite <- Hb.
  rewrite <- He1.
  rewrite <- He2.
  simpl nat_exp_cfold.
  destruct (bool_exp_cfold v b) ;
    first [ destruct b0 ; reflexivity | reflexivity ].
Qed.

Lemma BAnd_case:
  forall v b1 b2,
    bool_exp_denote v (bool_exp_cfold v b1) = bool_exp_denote v b1 ->
    bool_exp_denote v (bool_exp_cfold v b2) = bool_exp_denote v b2 ->
    bool_exp_denote v (bool_exp_cfold v (BAnd b1 b2)) = bool_exp_denote v (BAnd b1 b2).

  binop_case.
Qed.

Lemma BOr_case:
  forall v b1 b2,
    bool_exp_denote v (bool_exp_cfold v b1) = bool_exp_denote v b1 ->
    bool_exp_denote v (bool_exp_cfold v b2) = bool_exp_denote v b2 ->
    bool_exp_denote v (bool_exp_cfold v (BOr b1 b2)) = bool_exp_denote v (BOr b1 b2).

  binop_case.
Qed.

Lemma BEqB_case:
  forall v b1 b2,
    bool_exp_denote v (bool_exp_cfold v b1) = bool_exp_denote v b1 ->
    bool_exp_denote v (bool_exp_cfold v b2) = bool_exp_denote v b2 ->
    bool_exp_denote v (bool_exp_cfold v (BEqB b1 b2)) = bool_exp_denote v (BEqB b1 b2).

  binop_case.
Qed.

Lemma BEqN_case:
  forall v e1 e2,
    nat_exp_denote v (nat_exp_cfold v e1) = nat_exp_denote v e1 ->
    nat_exp_denote v (nat_exp_cfold v e2) = nat_exp_denote v e2 ->
    bool_exp_denote v (bool_exp_cfold v (BEqN e1 e2)) = bool_exp_denote v (BEqN e1 e2).

  binop_case.
Qed.

Lemma BNot_case:
  forall v b,
    bool_exp_denote v (bool_exp_cfold v b) = bool_exp_denote v b ->
    bool_exp_denote v (bool_exp_cfold v (BNot b)) = bool_exp_denote v (BNot b).

  intros.
  simpl bool_exp_denote at 2.
  rewrite <- H.
  simpl bool_exp_denote at 1.
  destruct (bool_exp_cfold v b) ; reflexivity.
Qed.  

Theorem cfold_preserves_nat_exp_denote :
  forall v e,
    nat_exp_denote v (nat_exp_cfold v e) = nat_exp_denote v e.

  intros.
  apply (nat_exp_mut
           (fun e => nat_exp_denote v (nat_exp_cfold v e) = nat_exp_denote v e)
           (fun b => bool_exp_denote v (bool_exp_cfold v b) = bool_exp_denote v b)) ;
    [ reflexivity               (* NConst case *)
    | reflexivity               (* NVar case *)
    | intros ; rewrite -> NPlus_case ; first [ reflexivity | assumption ]
    | intros ; rewrite -> NTimes_case ; first [ reflexivity | assumption ]
    | intros ; rewrite -> NIf_case ; first [ reflexivity | assumption ]
    | destruct b ; reflexivity  (* BConst case *)
    | intros ; rewrite -> BNot_case ; first [ reflexivity | assumption ]
    | intros ; rewrite -> BAnd_case ; first [ reflexivity | assumption ]
    | intros ; rewrite -> BOr_case ; first [ reflexivity | assumption ]
    | intros ; rewrite -> BEqB_case ; first [ reflexivity | assumption ]
    | intros ; rewrite -> BEqN_case ; first [ reflexivity | assumption ]
    ].
Qed.
