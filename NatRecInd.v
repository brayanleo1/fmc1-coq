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

Theorem times_suc : forall m n : nat, S m * n = (m * n) + n.
Proof.
  intro m.
  intro n.
  induction n as [| n' HIn'].
  - simpl. 
    reflexivity.
  - simpl.
    rewrite -> HIn'.
    rewrite -> plus_ass.
    rewrite -> (plus_com n' m).
    rewrite <- plus_ass.
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
  - simpl. 
    rewrite -> HIn'. 
    rewrite -> times_suc. 
    reflexivity.
Qed.

(*x4.14*)
Theorem times_ass : forall m n k : nat, (m * n) * k = m * (n * k).
Proof.
  intro m.
  intro n.
  intro k.
  induction k as [| k' HIk'].
  - simpl. 
    reflexivity.
  - simpl. 
    rewrite -> dist. 
    rewrite -> HIk'. 
    reflexivity.
Qed.

Theorem times_id1 : forall m : nat, m * S O = m.
Proof.
  intro m.
  simpl.
  rewrite -> plus_com.
  simpl.
  reflexivity.
Qed.

Theorem times_id2 : forall m : nat, S O * m = m.
Proof.
  intro m.
  rewrite -> times_com.
  rewrite -> times_id1.
  reflexivity.
Qed.

(*x4.17*)
Theorem exp_law1 : forall x a b : nat, x^(a+b) = (x^a) * (x^b).
Proof.
  intro x.
  intro a.
  intro b.
  induction b as [| b' HIb'].
  - simpl.
    rewrite -> plus_com.
    simpl.
    reflexivity.
  - simpl.
    rewrite -> HIb'.
    rewrite <- times_ass.
    reflexivity.
Qed.

(*x4.18*)
Theorem exp_law2 : forall a b c : nat, a^(b * c) = (a^b)^c.
Proof.
  intro a.
  intro b.
  intro c.
  induction c as [| c' HIc'].
  - simpl. 
    reflexivity.
  - simpl.
    rewrite -> exp_law1.
    rewrite -> HIc'.
    reflexivity.
Qed.

(*x4.19*)
Theorem exp_law3 : forall n : nat, S O ^ n = S O.
Proof.
  intro n.
  induction n as [| n' HIn'].
  - simpl. 
    reflexivity.
  - simpl.
    rewrite -> plus_com.
    simpl.
    rewrite -> HIn'.
    reflexivity.
Qed.

Definition leq_nat (m n : nat) := exists (k : nat), m + k = n.

Notation "a <= b" := (leq_nat a b).


(*x4.20*)
Theorem leq_suc : forall m n : nat, (n <= S m) <-> (n <= m \/ n = S m).
Proof.
  intro m.
  intro n.
  split.
  - intro n_leq_Sm.
    destruct n_leq_Sm as [k kpn_eq_Sm].
    destruct k as [ | k'].
    * right.
      simpl in kpn_eq_Sm.
      rewrite <- kpn_eq_Sm.
      reflexivity.
    * left.
      exists k'.
      simpl in kpn_eq_Sm.
      inversion kpn_eq_Sm.
      reflexivity.
  - intro n_leq_m_or_n_eq_Sm.
    destruct n_leq_m_or_n_eq_Sm as [n_leq_m | n_eq_Sm].
    * destruct n_leq_m as [k npk_eq_m].
      exists (S k).
      inversion npk_eq_m.
      simpl.
      reflexivity.
    * exists O.
      simpl.
      rewrite -> n_eq_Sm.
      reflexivity.
Qed.

(*x4.21*)
Theorem leq_refl : forall x : nat, x <= x.
Proof.
  intro x.
  exists O.
  simpl.
  reflexivity.
Qed.

(*x4.22*)
Theorem leq_ant_sym : forall x y : nat, (x <= y /\ y <= x) -> x = y.
Proof.
  intro x.
  intro y.
  intro x_leq_y_and_y_leq_x.
  destruct x_leq_y_and_y_leq_x as [x_leq_y y_leq_x].
  destruct x_leq_y as [k xpk_eq_y].
  destruct y_leq_x as [i ypi_eq_x].
  rewrite <- xpk_eq_y.
  destruct k as [| k'].
  - simpl.
    reflexivity.
  - rewrite -> xpk_eq_y.
    admit.
Admitted.

(*x4.23*)
Theorem leq_trans : forall x y z : nat, (x <= y /\ y <= z) -> x <= z.
Proof.
  intro x.
  intro y.
  intro z.
  intro x_leq_y_and_y_leq_z.
  destruct x_leq_y_and_y_leq_z as [x_leq_y y_leq_z].
  destruct x_leq_y as [k xpk_eq_y].
  destruct y_leq_z as [i ypi_eq_z].
  inversion ypi_eq_z.
  inversion xpk_eq_y.
  exists (k + i).
  rewrite -> plus_ass.
  reflexivity.
Qed.

Theorem leq_suc_suc : forall x y : nat, S x <= S y -> x <= y.
Proof.
  intro x.
  intro y.
  intro Sx_leq_Sy.
  destruct Sx_leq_Sy as [k Sxpk_eq_Sy].
  destruct k as [| k'].
  - simpl in Sxpk_eq_Sy.
    inversion Sxpk_eq_Sy.
    exists O.
    simpl.
    reflexivity.
  - inversion Sxpk_eq_Sy.
  exists ((S O) + k').
  rewrite <- plus_ass.
  simpl.
  reflexivity.
Qed.

(*x4.24*)
Theorem leq_tot : forall x y : nat, (x <= y) \/ (y <= x).
Proof.
  intro x.
  intro y.
  induction y as [| y' HIy'].
  - right.
  exists x.
  rewrite -> plus_com.
  simpl.
  reflexivity.
  - destruct HIy' as [x_leq_y' | y'_leq_x].
    *
left.
destruct x_leq_y' as [k xpk_eq_y].
exists (k + (S O)).
rewrite <- plus_ass.
rewrite <- plus_com.
rewrite -> xpk_eq_y.
rewrite -> plus_com.
simpl.
reflexivity.
    * induction x as [| x' HIx'].
      + destruct y'_leq_x as [k x'pk_eq_y'].
left. 
exists (S y').
rewrite -> plus_com.
simpl.
reflexivity.
      + destruct y'_leq_x as [k x'pk_eq_y'].
right.
rewrite leq_suc_suc.
destruct HIx' as [a | c].
        -- exists k.
inversion x'pk_eq_y'.
rewrite -> x'pk_eq_y'.
left.
exists (S O).
rewrite -> plus_com.
simpl.







End coq_fmc1.