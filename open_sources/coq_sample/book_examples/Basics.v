Definition admit {T: Type} : T.  Admitted.

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity.  Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

Example test_orb1:  (orb true  false) = true. 
Proof. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. reflexivity.  Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
 match b1 with
 | false => true
 | true => negb b2
 end.

Example test_nandb1:               (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
 | false => false
 | true => andb b2 b3
 end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. reflexivity. Qed.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. reflexivity.  Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity.  Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat := 
 match n with
 | O => S O
 | S p => mult n (factorial p)
 end.

Example test_factorial1:          (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y)  
                       (at level 40, left associativity) 
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. reflexivity.  Qed.

Definition blt_nat (n m : nat) : bool :=
 andb (ble_nat n m) (negb (beq_nat n m))
 .

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.  Qed.

Theorem plus_n_O : forall n, n + 0 = n.

Proof.
  simpl. (* Doesn't do anything! *)
Abort.

Theorem plus_1_l : forall n:nat, 1 + n = S n. 
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.

Proof.
  intros n m.   (* move both quantifiers into the context *)
  intros H.     (* move the hypothesis into the context *)
  rewrite -> H. (* Rewrite the goal using the hypothesis *)
  reflexivity.  Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros J.
  rewrite -> H.
  rewrite -> J.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  intros n m.
  rewrite <- plus_1_l.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. 
  simpl.  (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H1.
  intros b.
  rewrite -> H1.
  rewrite -> H1.
  reflexivity.
  Qed.

Theorem negation_fn_applied_twice :
  forall (f: bool -> bool),
  (forall (x: bool), f x = negb x) ->
  forall (b: bool), f (f b) = b.
Proof.
  intros f.
  intro H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  destruct b.
    reflexivity.
    reflexivity. Qed.

(** Thanks Sorawit for this idea. *)
Lemma andb_left_true:
  forall b: bool, (andb b true) = b.
Proof.
  destruct b.
    reflexivity.
    reflexivity.
  Qed.

Lemma andb_left_false:
  forall b: bool, (andb b false) = false.
Proof.
  destruct b.
    reflexivity.
    reflexivity.
  Qed.

Lemma orb_left_true:
  forall b: bool, (orb b true) = true.
Proof.
  destruct b.
    reflexivity.
    reflexivity.
  Qed.

Lemma orb_left_false:
  forall b: bool, (orb b false) = b.
Proof.
  destruct b.
    reflexivity.
    reflexivity.
  Qed.

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct c.
    rewrite -> andb_left_true.
    rewrite -> orb_left_true.
      intro HT.
      rewrite HT.
      reflexivity.
    rewrite -> andb_left_false.
    rewrite -> orb_left_false.
      intro HF.
      rewrite HF.
      reflexivity.
  Qed.

Inductive binary : Type :=
  | O: binary
  | D: binary -> binary
  | DA: binary -> binary.

Fixpoint incr (b: binary) : binary :=
  match b with
  | O => DA O
  | D p => DA p
  | DA p => D (incr p)
  end.

Fixpoint bin_to_nat (b: binary) : nat :=
  match b with
  | O => 0
  | D p => bin_to_nat(p) * 2
  | DA p => bin_to_nat(p) * 2 + 1
  end.

Eval compute in (bin_to_nat(DA (DA O))).
Eval compute in (bin_to_nat (D (incr(O)) ) ).

Example test_bin_incr1:
  (bin_to_nat(O) = 0).
Example test_bin_incr2:
  (bin_to_nat(D (DA O)) = 2).
Example test_bin_incr3:
  (bin_to_nat(incr (incr (incr (incr O)))) = 4).
Example test_bin_incr4:
  (bin_to_nat(incr(DA (DA (DA O)))) = 8).
Example test_bin_incr5:
  (bin_to_nat (incr (DA (D (DA (D (incr O)))))) = 22).