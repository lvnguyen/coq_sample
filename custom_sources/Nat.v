Module CustomInteger.

(** Peano arithmetic of natural numbers *)
Inductive nat : Type :=
  | O: nat  (** Zero value *)
  | S: nat -> nat. (** Successor *)

(** Predecessor *)
Definition pred (n: nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

(** Check whether n is even. Introduce concept of recursive definition. *)
Fixpoint evenb (n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

End CustomInteger.

(** Arithmetic. *)
Fixpoint plus (n m: nat): nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m: nat): nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Fixpoint exp(base power: nat): nat :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.

Fixpoint factorial(n: nat): nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

(** TODO: div, gcd, comparison *)