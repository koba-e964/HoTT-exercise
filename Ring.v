Require Import HoTT.

Definition isAbelianGroup(M: Type)
 (e: M) (d: M -> M -> M) :=
  (forall x, d x x = e) *
  (forall x, d x e = x) *
  (forall x y z, d x (d y z) = d z (d y x)) *
  (forall x y z, d (d x z) (d y z) = d x y).

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

Definition s1_roll: S1 -> S1 
  := S1_rec S1 base loop.

Definition s1_m: (S1 * S1) -> S1.
intro x.

SearchAbout (_ * _).
apply prod_rec.

