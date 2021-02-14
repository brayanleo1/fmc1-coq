Theorem t1_1 : forall P : Prop, P -> ~~P.
Proof.
  intro P.
  intro h.
  unfold not.
  intro i.
  apply i.
  apply h.
Qed.

Theorem t1_2 : forall P : Prop, ~~P -> P.
Proof.
  intro P.
  unfold not.
  intro h.
Abort.


Definition lem : Prop :=
forall P : Prop, P \/ ~P.

Theorem t1_2_fei : lem -> forall P : Prop, ~~P -> P.
Proof.
  intro L.
  intro P.
  unfold not.
  intro h.
  destruct (L P) as [p1 | p2].
  apply p1.
  unfold not in p2.
  contradiction.
Qed.

Theorem t2_1 : forall P : Prop, ~~ (P \/ ~P).
Proof.
  intro P.
  unfold not.
  intro h.
  apply h.
  right.
  intro i.
  apply h.
  left.
  apply i.
Qed.

Theorem t3_1 : forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
  intro P.
  intro Q.
  intro h.
  apply h.
  intro i.
Abort.


Theorem t3_1_fei : lem -> forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
  intro L.
  intro P.
  intro Q.
  intro h.
  destruct (L P) as [p1 | p2].
  apply p1.
  apply h.
  intro i.
  contradiction.
Qed.

Theorem t3_2 : forall P Q : Prop, ((P -> Q) -> P) -> ~~P.
Proof.
  intro P.
  intro Q.
  intro h.
  unfold not.
  intro i.
  apply i.
  apply h.
  intro j.
  contradiction.
Qed.

Theorem t4_1_fei : forall P Q : Prop, (P -> Q) -> (~P \/ Q).
Proof.
  intro P.
  intro Q.
  intro h.
  unfold not.
  left.
  intro i.
Abort.

Theorem t4_1_fei : lem -> forall P Q : Prop, (P -> Q) -> (~P \/ Q).
Proof.
  intro L.
  intro P.
  intro Q.
  intro h.
  unfold not.
  destruct (L P) as [p1 | p2].
  right.
  apply h.
  apply p1.
  left.
  intro i.
  unfold not in p2.
  contradiction.
Qed.

Theorem t4_2 : forall P Q : Prop, (~P \/ Q) -> (P -> Q).
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  intro i.
  destruct h as [h1 | h2].
  contradiction.
  apply h2.
Qed.

Theorem t4_3 : forall P Q : Prop, (P \/ Q) -> (~P -> Q).
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  intro i.
  destruct h as [h1 | h2].
  contradiction.
  apply h2.
Qed.

Theorem t4_4 : forall P Q : Prop, (~P -> Q) -> (P \/ Q).
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  right.
  apply h.
  intro i.
Abort.

Theorem t4_4_fei : lem -> forall P Q : Prop, (~P -> Q) -> (P \/ Q).
Proof.
  intro L.
  intro P.
  intro Q.
  unfold not.
  intro h.
  destruct (L P) as [p1 | p2].
  left.
  apply p1.
  right.
  apply h.
  intro i.
  unfold not in p2.
  contradiction.
Qed.

Theorem t5_1 : forall P Q : Prop, P \/ Q -> ~(~P /\ ~Q).
Proof.
  intro P.
  intro Q.
  intro h.
  unfold not.
  intro i.
  destruct i as [i1 i2].
  destruct h as [h1 | h2].
  apply i1.
  apply h1.
  apply i2.
  apply h2. (*** GG \in \nat ... tendeu? :p ***)
Qed.


Theorem t5_2 : forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  left.
  destruct h.
  split.
  intro i.
Abort.

Theorem t5_2_fei : lem -> forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.
Proof.
  intro L.
  intro P.
  intro Q.
  unfold not.
  intro h.
  destruct (L P) as [p1 | p2].
  left.
  apply p1.
  unfold not in p2.
  destruct h.
  split.
  apply p2.
  intro i.
  apply p2.
  contradiction.
  intro i.
  apply p2.
