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

(*x4.6*)
Fixpoint times_nat (m n : nat) : nat :=
  match n with
  | O => O
  | S n' => (times_nat m n') + m
end.

Notation "a * b" := (times_nat a b).

(*x4.7*)
Example x4_7: S(S O) * (O + S O)  = S(S O).
Proof. simpl. reflexivity.  Qed.

(*x4.8*)
Example x4_8_1: S(S O) * S(S(S O)) = S(S(S(S(S(S O))))).
Proof. simpl. reflexivity.  Qed.

Example x4_8_2: S(S(S O)) * S(S O) = S(S(S(S(S(S O))))).
Proof. simpl. reflexivity.  Qed.

(*x4.9*)
Fixpoint exp_nat (m n : nat) : nat :=
  match n with
  | O => S O
  | S n' => (exp_nat m n') * m
end.

Notation "a ^ b" := (exp_nat a b).

(*x4.10*)
Example x4_10: S(S O) ^ S(S(S O))  = S(S(S(S(S(S(S(S O))))))).
Proof. simpl. reflexivity.  Qed.

(*x4.11*)
Fixpoint fib_nat (n : nat) : nat :=
  match n with
  | O => O
  | S O => S O
  | S (S n'' as n') => (fib_nat n'') + (fib_nat n')
end.

(*x4.12*)
Example x4_12: forall a m : nat, (a + m) + O = a + (m + O).
Proof. simpl. reflexivity. Qed.

Theorem plus_ass : forall m n t : nat, (m + n) + t = m + (n + t).
Proof.
  intro m.
  intro n.
  intro t.
  induction t as [| t' HIt'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> HIt'. 
    reflexivity.
Qed.

Theorem plus_com_suc : forall m n : nat, m + S n = S m + n.
Proof.
  intro m.
  intro n.
  induction n as [| n' HIn'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite <- HIn'. 
    simpl. 
    reflexivity.
Qed.

Theorem plus_com : forall m n : nat, m + n = n + m.
Proof.
  intro m.
  intro n.
  induction n as [| n' HIn'].
  - induction m as [| m' HIm'].
    * reflexivity.
    * simpl. 
      rewrite <- HIm'. 
      simpl. 
      reflexivity.
  - simpl. 
    rewrite <- plus_com_suc. 
    simpl. 
    rewrite <- HIn'. 
    reflexivity.
Qed.

(*x4.16*)
Theorem dist : forall x y z : nat, x * (y + z) = (x * y) + (x * z).
Proof.
  intro x.
  intro y.
  intro z.
  induction z as [| z' HIz'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> HIz'. 
    rewrite -> plus_ass.
    reflexivity.
Qed.

(*x4.15*)
Theorem times_com : forall m n : nat, m * n = n * m.
Proof.
  intro m.
  intro n.
  induction n as [| n' HIn'].
  - induction m as [| m' HIm'].
    * reflexivity.
    * simpl. 
    rewrite <- HIm'. 
    simpl. 
    reflexivity.
  - induction m as [| m' HIm'].
    * simpl. 
    rewrite -> HIn'. 
    simpl. 
    reflexivity.
    * simpl. (*Continua...*)
    rewrite -> HIn'.
    simpl.
    rewrite -> plus_com.
    simpl in HIn'.
    rewrite <- HIn'.
    simpl.
Qed.
(*x4.14*)


End coq_fmc1.