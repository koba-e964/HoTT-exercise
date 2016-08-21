Require Import HoTT.

Record isAbelianGroup(M: Type)
 (e: M) (d: M -> M -> M) :=
  BuildIsAbelianGroup
  {
    isabelian_sub_xx: forall x, d x x = e;
    isabelian_sub_r: forall x, d x e = x;
    isabelian_13: forall x y z, d x (d y z) = d z (d y x);
    isabelian_cancel: forall x y z, d (d x z) (d y z) = d x y
  }.

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

Record isRing (R: Type) (one: R) (sub: R -> R -> R)
  (mul: R -> R -> R) :=
  BuildIsRing
  {
    isring_isabelian: isAbelianGroup R (sub one one) sub;
    isring_mul_assoc: forall a b c, mul (mul a b) c = mul a (mul b c);
    isring_distr_l: forall a b c, mul a (sub b c) = sub (mul a b) (mul a c);
    isring_distr_r: forall a b c, mul (sub a b) c = sub (mul a c) (mul b c);
    isring_mul_unit_l: forall a, mul one a = a;
    isring_mul_unit_r: forall a, mul a one = a
  }.

Definition xorb (a b: Bool) := if a then negb b else b.

Proposition isring_bool: isRing Bool true xorb andb.
do 5 (try split).
intro x; case x; auto.
intro x; case x; auto.
intros x y z; case x, y, z; auto.
intros x y z; case x, y, z; auto.
intros x y z; case x, y, z; auto.
intros x y z; case x, y, z; auto.
intros x y z; case x, y, z; auto.
intro x; case x; auto.
Defined.

Record isModule {R one sub mul} {ring: isRing R one sub mul}
  (M: Type) (mzero: M) (msub: M -> M -> M) (act: R -> M -> M) :=
  BuildIsModule
  {
    ismodule_abelian: isAbelianGroup M mzero msub;
    ismodule_distr_l: forall r m n, act r (msub m n) = msub (act r m) (act r n);
    ismodule_distr_r: forall r s m, act (sub r s) m = msub (act r m) (act s m);
    ismodule_act_one: forall m, act one m = m;
    ismodule_act_assoc: forall r s m, act r (act s m) = act (mul r s) m
  }.

Proposition self_module {R one sub mul} {isring: isRing R one sub mul}
  : isModule R (ring := isring)
    (sub one one) sub mul.
split.
split; apply (isring_isabelian _ _ _ _ isring).

apply (isring_distr_l _ _ _ _ isring).
apply (isring_distr_r _ _ _ _ isring).
apply (isring_mul_unit_l _ _ _ _ isring).
intros r s m; symmetry; apply (isring_mul_assoc _ _ _ _ isring).
Defined.

Record isHom {R one sub mul} {isring: isRing R one sub mul}
  {M mzero msub mact} {ismod_m: isModule (ring := isring) M mzero msub mact}
  {N nzero nsub nact} {ismod_n: isModule (ring := isring) N nzero nsub nact}
  (f: M -> N) := 
  BuildIsHom
  {
    ishom_zero: f mzero = nzero;
    ishom_sub: forall x y, f (msub x y) = nsub (f x) (f y);
    ishom_act: forall r x, f (mact r x) = nact r (f x)
  }.

Definition isHom_idmap {R one sub mul} {isring: isRing R one sub mul}
 {M mzero msub mact} {ismod_m: isModule (ring := isring) M mzero msub mact}
  :isHom (isring := isring) (ismod_m := ismod_m) (ismod_n := ismod_m)
    (idmap: M -> M).
split; auto.
Defined.

Definition isHom_zeromap {R one sub mul} {isring: isRing R one sub mul}
  {M mzero msub mact} {ismod_m: isModule (ring := isring) M mzero msub mact}
  {N nzero nsub nact} {ismod_n: isModule (ring := isring) N nzero nsub nact}
  :isHom (isring := isring) (ismod_m := ismod_m) (ismod_n := ismod_n)
    (fun _ => nzero).
split; auto.
intros _ _.
destruct ismod_n as [is_abelian _ _ _ _].
destruct is_abelian.
symmetry; auto.
intros r _.
destruct ismod_n as [[H H0 H1 H2] H3 _ _ _].
assert (nzero = nact r (nsub nzero nzero)).
rewrite H3.
symmetry; apply H.
rewrite (H nzero) in X.
auto.
Defined.




