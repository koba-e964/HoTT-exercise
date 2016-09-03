Require Import HoTT.

Goal forall A B, ~(A * B) -> IsHProp A -> IsHProp B -> IsHProp (A + B).
intros A B H H0 H1.
apply ishprop_sum; auto.
Qed.

Lemma merely_functorial: forall P Q, (P -> Q) -> merely P -> merely Q.
  intros P Q H.
  apply Trunc_rec.
  intro H0.
  apply tr.
  auto.
Defined.

Theorem thm7_2_2:
  forall X: Type, forall R: X -> X -> hProp,
  (forall x y, R x y -> x = y) -> IsHSet X.
Admitted.

Section ex_7_1.
  Proposition ex_7_1_q1: (forall A, merely A -> A) -> forall X, IsHSet X.
  Proof.
    intros H X.
    apply (thm7_2_2 X (fun x y => merely (x = y))).
    intros x y.
    apply H.
  Qed.
  Goal (forall A B (f: A -> B), (forall b, merely (hfiber f b)) -> (forall b, hfiber f b))
        -> forall X, IsHSet X.
  Proof.
    intros H X.
    apply ex_7_1_q1.
    intros A H0.
    generalize (H A Unit (fun _ => tt)); intro H1.
    unfold hfiber in H1.
    apply H1.
    induction b.
    apply merely_functorial with (P := A); auto.
    intro a.
    exists a.
    auto.
    exact tt.
  Qed.
End ex_7_1.

