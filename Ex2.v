Require Import HoTT.

Definition myinv : forall (A:Type) (x y:A) (p:x=y), y=x.
intros A x y p.
induction p.
exact 1.
Defined.

Section ex_2_1.
  Definition comp_stmt:=
    forall (A:Type) (x y z:A), x=y -> y=z -> x=z.
  Definition comp_pr1: comp_stmt.
    intros A x y z p.
    assert (forall (z:A) (q:y=z), x=z).
    induction p.
    assert (forall (a b:A) (q:a=b), a=b).
    intros a b q.
    induction q.
    exact 1.
    exact (X x).
    exact (X z).
    Defined.
  Definition comp_pr2: comp_stmt.
    intros A x y z p q.
    induction p.
    induction q.
    exact 1.
    Defined.
  Goal comp_pr1 = comp_pr2.
    compute.
    reflexivity.