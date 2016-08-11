Require Import HoTT.

Definition myinv : forall (A:Type) (x y:A) (p:x=y), y=x.
intros A x y p.
induction p.
exact idpath.
Defined.

Section ex_2_1.
  Context `{Funext}.
  Definition comp_stmt:=
    forall (A:Type) (x y z:A), x=y -> y=z -> x=z.
  Definition comp_pr1: comp_stmt. (* induction on p *)
    intros A x y z p q.
    induction p.
    exact q.
  Defined.
  Definition comp_pr2: comp_stmt. (* induction on q *)
    intros A x y z p q.
    induction q.
    exact p.
  Defined.
  Definition comp_pr3: comp_stmt. (* induction on p,q *)
    intros A x y z p q.
    induction p.
    induction q.
    exact idpath.
  Defined.
  Definition comp_pr12: comp_pr1 = comp_pr2.
    unfold comp_pr1, comp_pr2.
    apply path_forall; intro A.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply path_forall; intro z.
    apply path_forall; intro p.
    induction p.
    apply path_forall; intro q.
    induction q.
    reflexivity.
  Defined.
  Definition comp_pr23: comp_pr2 = comp_pr3.
    unfold comp_pr2, comp_pr3.
    apply path_forall; intro A.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply path_forall; intro z.
    apply path_forall; intro p.
    induction p.
    apply path_forall; intro q.
    induction q.
    reflexivity.
  Defined.
  Definition comp_pr13: comp_pr1 = comp_pr3.
    unfold comp_pr3, comp_pr1.
    apply path_forall; intro A.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply path_forall; intro z.
    apply path_forall; intro p.
    induction p.
    apply path_forall; intro q.
    induction q.
    reflexivity.
  Defined.
End ex_2_1.

Section ex_2_2.
  Context `{Funext}.
  Goal (comp_pr12 @ comp_pr23) = comp_pr13.
    unfold comp_pr12, comp_pr13, comp_pr23.
    Admitted.
End ex_2_2.
Section ex_2_5.
  Definition map236: forall (A B:Type)(x y:A) (p:x=y)(f:A->B),
    f x = f y -> transport (const B) p (f x) = f y.
    intros A B x y p f fp.
    exact (transport_const p (f x) @ fp).
  Defined.
  Definition map237 (A B:Type)(x y:A) (p:x=y)(f:A->B)
    (tp : transport (const B) p (f x) = f y) : f x = f y :=
      (transport_const p (f x))^ @ tp.
  Lemma ididq:(forall A (x y:A) (q:x=y), paths (idpath @ q) q).
    induction q.
    auto.
  Defined.
  Lemma isequiv_map236: forall A B x y p f, IsEquiv (map236 A B x y p f).
    intros A B x y p f.
Print IsEquiv.
  Check eisretr.
    refine ({| equiv_inv:=map237 A B x y p f;eisretr:=_; eissect:=_; eisadj:=_ |}).

    intro x0.
  Admitted.
End ex_2_5.

Section ex_2_6.
  Goal forall A (x y z:A) (p:x = y), IsEquiv (concat p : y = z -> x = z).
  intros A x y z p.
  refine ({| equiv_inv:=concat (p^);eisretr:=_; eissect:=_; eisadj:=_ |}).
  unfold Sect.
  induction x0.
  induction p.
  simpl.
  Admitted.
End ex_2_6.
