Inductive nat : Type :=
 | O : nat
 | S : nat -> nat.

Fixpoint add (x y : nat) : nat :=
 match x with
 | O => y
 | S z => S (add z y)
end.

Infix "+" := add (at level 50, left associativity).

Fixpoint mult (x y : nat) : nat :=
 match x with
 | O => O
 | S z => add y (mult z y)
end.

Infix "*" := mult (at level 40, left associativity).

Inductive le : nat -> nat -> Prop :=
 | le_refl_rule : forall x : nat, le x x
 | le_step_rule : forall x y : nat, le x y -> le x (S y).

Definition lt (x y : nat) : Prop := le (S x) y.
Definition ge (x y : nat) : Prop := le y x.
Definition gt (x y : nat) : Prop := lt y x.

Infix "<=" := le (at level 70, no associativity).
Infix "<" := lt (at level 70, no associativity).
Infix ">=" := ge (at level 70, no associativity).
Infix ">" := gt (at level 70, no associativity).