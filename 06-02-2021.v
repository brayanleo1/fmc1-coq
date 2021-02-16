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
  right.
  destruct (L Q) as [q1 | q2].
  apply q1.
  unfold not in q2.
  destruct h.
  split.
  intro i.
  destruct q2.
  admit.
  apply q2.
Admitted.

Theorem t5_3 : forall P Q : Prop, P /\ Q -> ~(~P\/~Q).
Proof.
  intro P.
  intro Q.
  intro h.
  unfold not.
  intro i.
  destruct i as [i1 | i2].
  apply i1.
  apply h.
  apply i2.
  apply h.
Qed.

Theorem t5_4 : forall P Q : Prop,~(~P\/~Q) -> P /\ Q.
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  split.
Abort.

Theorem t5_4 : lem -> forall P Q : Prop, ~(~P\/~Q) -> P /\ Q.
Proof.
  intro L.
  intro P.
  intro Q.
  unfold not.
  intro h.
  split.
  destruct (L P) as [p1 | p2].
  apply p1.
  unfold not in p2.
  destruct h.
  left.
  apply p2.
  destruct (L Q) as [q1 | q2].
  apply q1.
  unfold not in q2.
  destruct h.
  right.
  apply q2.
Qed.

Theorem t6_1 : forall P Q : Prop, ~(P \/ Q) -> (~P /\ ~Q).
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  split.
  intro i.
  apply h.
  left.
  apply i.
  intro j.
  apply h.
  right.
  apply j.
Qed.

Theorem t6_2 : forall P Q : Prop, (~P /\ ~Q) -> ~(P \/ Q).
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  intro i.
  destruct h as [h1 h2].
  destruct i as [i1 | i2].
  apply h1.
  apply i1.
  apply h2.
  apply i2.
Qed.

Theorem t6_3 : forall P Q : Prop, ~(P /\ Q) -> (~Q \/ ~P).
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  right.
  intro i.
  apply h.
  split.
  apply i.
Abort.

Theorem t6_3_fei : lem -> forall P Q : Prop, ~(P /\ Q) -> (~Q \/ ~P).
Proof.
  intro L.
  intro P.
  intro Q.
  unfold not.
  intro h.
  destruct (L Q) as [q1 | q2].
  right.
  intro i.
  apply h.
  split.
  apply i.
  apply q1.
  unfold not in q2.
  left.
  apply q2.
Qed.

Theorem t6_4 : forall P Q : Prop, (~Q \/ ~P) -> ~(P /\ Q).
Proof.
  intro P.
  intro Q.
  unfold not.
  intro h.
  intro i.
  destruct i as [i1 i2].
  destruct h as [h1 | h2].
  apply h1.
  apply i2.
  apply h2.
  apply i1.
Qed.

Theorem t7_1 : forall P Q R : Prop, P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intro P.
  intro Q.
  intro R.
  intro h.
  destruct h as [h1 h2].
  destruct h2 as [h3 | h4].
  left.
  split.
  apply h1.
  apply h3.
  right.
  split.
  apply h1.
  apply h4.
Qed.

Theorem t7_2 : forall P Q R : Prop, (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R).
Proof.
  intro P.
  intro Q.
  intro R.
  intro h.
  destruct h as [h1 | h2].
  destruct h1 as [p q].
  split.
  apply p.
  left.
  apply q.
  destruct h2 as [p r].
  split.
  apply p.
  right.
  apply r.
Qed.

Theorem t7_3 : forall P Q R : Prop, P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intro P.
  intro Q.
  intro R.
  intro h.
  destruct h as [p | qr].
  split.
  left.
  apply p.
  left. 
  apply p.
  destruct qr as [q r].
  split.
  right.
  apply q.
  right.
  apply r.
Qed.

Theorem t7_4 : forall P Q R : Prop, (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intro P.
  intro Q.
  intro R.
  intro h.
  destruct h as [pq pr].
  destruct pq as [p | q].
  left.
  apply p.
  destruct pr as [p | r].
  left.
  apply p.
  right.
  split.
  apply q.
  apply r.
Qed.