Require Import HoTT.

Definition isProp(A: Type) := forall x y: A, x = y.
Definition isSet(A: Type) := forall x y: A, isProp (x = y).
Section ex_3_1.
  Context `{fe:Funext}.
  Goal forall A B, A <~> B -> isSet A -> isSet B.
    intros A B H sa x y p q.
    destruct H as [f [g]].
    generalize (sa (g x) (g y) (ap g p) (ap g q)); intro H.
    assert (ap f (ap g p) = ap f (ap g q)).
    rewrite H.
    reflexivity.
    generalize (fun x => eisretr x); intro H0.
    repeat rewrite <- ap_compose in X.
    apply path_arrow in H0.
    assert (forall A B (ff: A -> B) gg x y (pp: x = y), forall e:ff = gg,
      transport (fun P => P x = P y) e (ap ff pp) = ap gg pp). 
      induction e.
      simpl.
      reflexivity.
    do 2 rewrite <- (X0 _ _ _ (f o g)  _ _ _ (H0 ^)) in X.
    do 2 rewrite ap_idmap in X.
    assert (forall A P (x: A) y (p: x = y) u v,
      transport P p u = transport P p v -> u = v).
    induction p0.
    simpl.
    auto.
    apply X1 with (A := B -> B) (P := (fun P : B -> B => P x = P y))
     (p := H0 ^).
    apply X.
  Defined.
End ex_3_1.

Section ex_3_2.
  Goal forall A B, isSet A -> isSet B -> isSet (A + B).
  Proof.
    intros A B H H0 x y p q.
    induction p.
    destruct x.
  Admitted.
End ex_3_2.
