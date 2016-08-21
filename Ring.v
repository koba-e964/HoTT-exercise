Require Import HoTT.

Definition isAbelianGroup(M: Type)
 (e: M) (d: M -> M -> M) :=
  (forall x, d x x = e) *
  (forall x, d x e = x) *
  (forall x y z, d x (d y z) = d z (d y x)) *
  (forall x y z, d (d x z) (d y z) = d x y).

Section s1_properties.

  Definition s1_inv: S1 -> S1.
  apply S1_rec with (b := base).
  apply loop^.
  Defined.


  Goal (ap s1_inv loop = loop^).
  apply S1_rec_beta_loop.
  Qed.

  Goal forall b, s1_inv (s1_inv b) = b.
  refine (S1_ind (fun u => s1_inv (s1_inv u) = u) idpath _).
  rewrite transport_paths_FlFr.
  rewrite ap_idmap.
  unfold s1_inv.
  rewrite ap_compose.
  rewrite S1_rec_beta_loop.
  rewrite ap_V.
  rewrite S1_rec_beta_loop.
  rewrite concat_p1.
  rewrite inv_V.
  apply concat_Vp.
  Qed.

  Context `{Univalence}.
  Definition s1_sub (a b: base = base): base = base
    := a @ b^.
  Theorem loopS1_comm: forall a b: base = base,
    a @ b = b @ a.
  intros a b.
  Admitted.

  Definition s1_abelian: isAbelianGroup (base = base) idpath s1_sub.
  do 3 (try split).
  apply concat_pV.
  apply concat_p1.
  intros x y z.
  unfold s1_sub.
  do 2 rewrite inv_pV.
  rewrite (loopS1_comm z).
  rewrite concat_p_pp.
  apply loopS1_comm.

  intros x y z.
  unfold s1_sub.
  rewrite inv_pV.
  rewrite concat_p_pp.
  rewrite (concat_pp_p _ z^).
  rewrite concat_Vp.
  rewrite concat_p1.
  reflexivity.
  Defined.
End s1_properties.

