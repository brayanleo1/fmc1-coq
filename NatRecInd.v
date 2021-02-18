Module coq_fmc1.

Inductive nat : Type :=
  | O
  | S (n : nat)
.

Fixpoint plus_nat (m n : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus_nat m n')
 end.

Notation "a + b" := (plus_nat a b).

(*x4.3*)
Example x4_3: (O + S(S(S(S O)))) = S(S(S(S O))).
Proof. simpl. reflexivity.  Qed.

(*x4.4*)
Example x4_4_1: S(S(S O)) + (S(S O) + S O) = S(S(S(S(S(S O))))).
Proof. simpl. reflexivity.  Qed.

Example x4_4_2: (S(S(S O)) + S(S O)) + S O = S(S(S(S(S(S O))))).
Proof. simpl. reflexivity.  Qed.

Fixpoint double_nat (n : nat) : nat :=
  n + n. (* Ele diz que não foi definido
de forma recursiva mas, como eu faço isso?
Talvez quando tiver multiplicação?*)

(*x4.5*)
Example x4_5: double_nat (S(S(S O))) = S(S(S(S(S(S O))))).
Proof. simpl. reflexivity.  Qed.

Fixpoint times_nat (m n : nat) : nat :=
  match n with
  | O => O
  | S n' => m + (times_nat m n')
end.

Notation "a * b" := (times_nat a b).

(*x4.7*)
Example x4_6: S(S O) * (O + S O)  = S(S O).
Proof. simpl. reflexivity.  Qed.

Fixpoint exp_nat (m n : nat) : nat :=
  match n with
  | O => S O
  | S n' => n * (exp_nat m n')
end.

Notation "a ^ b" := (exp_nat a b).

Fixpoint fib_nat (n : nat) : nat :=
  match n with
  | O => O
  | S O => S O
  | S (S n'' as n') => (fib_nat n'') + (fib_nat n')
end.

End coq_fmc1.