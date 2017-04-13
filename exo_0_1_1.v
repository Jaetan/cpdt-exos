(* Define an inductive type truth with three constructors, Yes, No,
   and Maybe. Yes stands for certain truth, No for certain falsehood,
   and Maybe for an unknown situation. Define ¡Ènot,¡É ¡Èand,¡É and
   ¡Èor¡É for this replacement boolean algebra. Prove that your
   implementation of ¡Èand¡É is commutative and distributes over your
   implementation of ¡Èor.¡É
 *)

Inductive truth : Set :=
| Yes : truth
| No : truth
| Maybe : truth.

Definition not (t : truth) : truth :=
  match t with
    | Yes => No
    | No => Yes
    | _ => Maybe
  end.

Definition and (t u : truth) : truth :=
  match t with
    | Yes => u
    | No => No
    | Maybe => match u with No => No | _ => Maybe end
  end.

Definition or (t u : truth) : truth :=
  match t with
    | Yes => Yes
    | No => u
    | Maybe => match u with Yes => Yes | _ => Maybe end
  end.

Theorem and_commutative : forall t u, and t u = and u t.
  destruct t ; destruct u ; reflexivity.
Qed.  

Theorem or_commutative : forall t u, or t u = or u t.
  destruct t ; destruct u ; reflexivity.
Qed.

Theorem and_or_distributive : forall t u v, and t (or u v) = or (and t u) (and t v).
  destruct t ; destruct u ; destruct v ; reflexivity.
Qed.
