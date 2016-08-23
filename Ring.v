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

Proposition ismodule_act_zero {R one sub mul} {isring: isRing R one sub mul}
  {M mzero msub mact} {ismod_m: isModule (ring := isring) M mzero msub mact}
  : forall r, mact r mzero = mzero.
destruct ismod_m as [[H H0 H1 H2] H3 _ _ _].
intro r.
assert (mact r (msub mzero mzero) = mzero).
rewrite H3.
apply H.
rewrite (H mzero) in X.
auto.
Defined.

Record isHom {R one sub mul} {isring: isRing R one sub mul}
  {M mzero msub mact} {ismod_m: isModule (ring := isring) M mzero msub mact}
  {N nzero nsub nact} {ismod_n: isModule (ring := isring) N nzero nsub nact}
  (f: M -> N) := 
  BuildIsHom
  {
    ishom_sub: forall x y, f (msub x y) = nsub (f x) (f y);
    ishom_act: forall r x, f (mact r x) = nact r (f x)
  }.

Proposition isHom_zero {R one sub mul} {isring: isRing R one sub mul}
  {M mzero msub mact} {ismod_m: isModule (ring := isring) M mzero msub mact}
  {N nzero nsub nact} {ismod_n: isModule (ring := isring) N nzero nsub nact}
  : forall f: M -> N, isHom (isring := isring) (ismod_m := ismod_m) (ismod_n := ismod_n) f -> f mzero = nzero.
intros f H.
destruct H.
assert (f (msub mzero mzero) = nzero).
rewrite ishom_sub0.
destruct ismod_n as [[H H0 H1 _] _ _ _ _].
apply H.
destruct ismod_m as [[H _ _ _] _ _ _ _].
rewrite H in X.
auto.
Defined.


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
symmetry; apply (ismodule_act_zero (ismod_m := ismod_n)).
Defined.

Section kernel_def.
Variables (R: Type)
  (one: R)
  (sub: R -> R -> R)
  (mul: R -> R -> R)
  (isring: isRing R one sub mul).
Variables (M: Type)
  (mzero: M)
  (msub: M -> M -> M)
  (mact: R -> M -> M)
  (ismod_m: isModule (ring := isring) M mzero msub mact).
Variables (N: Type)
  (nzero: N)
  (nsub: N -> N -> N)
  (nact: R -> N -> N)
  (ismod_n: isModule (ring := isring) N nzero nsub nact).
Variables (f: M -> N)
  (isHom_f: isHom f (isring := isring) (ismod_m := ismod_m) (ismod_n := ismod_n)).
Definition kernel
  := {x: M | f x = nzero }.


Definition kernel_zero: kernel.
exists mzero.
apply (isHom_zero (ismod_m := ismod_m) (ismod_n := ismod_n)).
auto.
Defined.
Print kernel_zero.
Definition kernel_sub: kernel -> kernel -> kernel.
intros x y.
destruct x as [x H], y as [y H0].
exists (msub x y).
destruct isHom_f.
rewrite ishom_sub0.
rewrite H, H0.
destruct ismod_n as [[]];
auto.
Defined.

Definition kernel_act: R -> kernel -> kernel.
intros r x.
destruct x as [x H].
exists (mact r x).
destruct isHom_f.
rewrite ishom_act0.
rewrite H.
apply (ismodule_act_zero (ismod_m := ismod_n)).
Defined.

Definition isModule_kernel:
  isModule (ring := isring) kernel kernel_zero kernel_sub kernel_act.
Admitted.

End kernel_def.

Section im_def.
Variables (R: Type)
  (one: R)
  (sub: R -> R -> R)
  (mul: R -> R -> R)
  (isring: isRing R one sub mul).
Variables (M: Type)
  (mzero: M)
  (msub: M -> M -> M)
  (mact: R -> M -> M)
  (ismod_m: isModule (ring := isring) M mzero msub mact).
Variables (N: Type)
  (nzero: N)
  (nsub: N -> N -> N)
  (nact: R -> N -> N)
  (ismod_n: isModule (ring := isring) N nzero nsub nact).
Variables (f: M -> N)
  (isHom_f: isHom f (isring := isring) (ismod_m := ismod_m) (ismod_n := ismod_n)).
Context `{funext:Funext}.
(* It might be better to use "merely",
   but "Trunc (-1)" is easier to deal with... *)
  Definition image := {x: N | Trunc (-1) (hfiber f x)}. 
  Definition image_zero: image.
    exists nzero.
    apply tr.
    exists mzero.
    apply (isHom_zero (ismod_m := ismod_m) (ismod_n := ismod_n)); auto.
  Defined.
  Definition image_sub: image -> image -> image.
  intros x y.
  destruct x as [x H], y as [y H0].
  exists (nsub x y).
  refine (Trunc_rec _ H).
  refine (Trunc_rec _ H0).
  intros m n.
  destruct m as [m H1], n as [n H2].
  apply tr.
  exists (msub n m).
  rewrite <- H1.
  rewrite <- H2.
  apply (ishom_sub (ismod_n := ismod_n) (ismod_m := ismod_m)).
  auto.
  Defined.
  Definition image_act: R -> image -> image.
    intros r x.
    destruct x as [x H].
    exists (nact r x).
    refine (Trunc_rec _ H).
    intro H0.
    destruct H0 as [m H0].
    apply tr.
    exists (mact r m).
    rewrite <- H0.
    apply (ishom_act _ isHom_f (ismod_m := ismod_m) (ismod_n := ismod_n)).
  Defined.

  (* Turn an equality (X) in N to an equality in image (:= {x: N | exists y, f y = x}). *)
  Ltac eq_in_image X := apply path_sigma' with (p := X); apply path_ishprop.
  Definition isModule_image:
  isModule (ring := isring) image image_zero image_sub image_act.
    case ismod_n; intros
      ismodule_abelian0
      ismodule_distr_l0
      ismodule_distr_r0
      ismodule_act_one0
      ismodule_act_assoc0.
    destruct ismodule_abelian0 as [isabelian_sub_xx0 isabelian_sub_r0 isabelian_130 isabelian_cancel0].
    split.
    split.

    intro x.
    destruct x as [x H].
    assert (nsub x x = nzero).
    auto.
    eq_in_image X.

    intro x.
    destruct x as [x H].
    assert (nsub x nzero = x).
    auto.
    eq_in_image X.

    intros x y z.
    destruct x as [x H0], y as [y H1], z as [z H2].
    assert (nsub x (nsub y z) = nsub z (nsub y x)).
    auto.
    eq_in_image X.

    intros x y z.
    destruct x as [x H0], y as [y H1], z as [z H2].
    assert (nsub (nsub x z) (nsub y z) = nsub x y).
    auto.
    eq_in_image X.

    intros r m n.
    destruct m as [m H0], n as [n H1].
    assert (nact r (nsub m n) = nsub (nact r m) (nact r n)).
    auto.
    eq_in_image X.

    intros r s m.
    destruct m as [m H0].
    assert (nact (sub r s) m = nsub (nact r m) (nact s m)).
    auto.
    eq_in_image X.

    intro m.
    destruct m as [m H0].
    assert (nact one m = m).
    auto.
    eq_in_image X.

    intros r s m.
    destruct m as [m H0].
    assert (nact r (nact s m) = nact (mul r s) m).
    auto.
    eq_in_image X.
  Defined.

End im_def.

Section subquo.
  Variables (R: Type)
    (one: R)
    (sub: R -> R -> R)
    (mul: R -> R -> R)
    (isring: isRing R one sub mul).
  Variables (M: Type)
    (mzero: M)
    (msub: M -> M -> M)
    (mact: R -> M -> M)
    (ismod_m: isModule (ring := isring) M mzero msub mact).
  Variable (P: M -> hProp)
    (p_mzero: P mzero)
    (p_msub: forall m n, P m -> P n -> P (msub m n))
    (p_mact: forall r m, P m -> P (mact r m)).
  Definition submodule := {x: M | P x}.
  Definition submodule_zero: submodule := (mzero; p_mzero).
  Definition submodule_sub: submodule -> submodule -> submodule.
  intros [m H] [n H0].
  exists (msub m n).
  auto.
  Defined.
  Definition submodule_act: R -> submodule -> submodule.
  intros r [m H].
  exists (mact r m).
  auto.
  Defined.
  Definition isModule_submodule: isModule (ring := isring) submodule submodule_zero submodule_sub submodule_act.
  Admitted.
  Hypothesis (ishset_m: IsHSet M).
  Definition quotient_module :=
    (quotient (A := M) (fun x y => P (msub x y))).
  Definition quotient_module_zero: quotient_module := class_of _ mzero.
  Context `{univalence_tag: Univalence}.
  Definition quotient_module_sub: quotient_module -> quotient_module -> quotient_module.
  refine (quotient_rec2 (fun x y => P (msub x y)) _ (dclass := fun a1 a2 => class_of _ (msub a1 a2))).
  intro x.
  destruct ismod_m as [[H _ _ _] _ _ _ _].
  rewrite H.
  auto.
  intros x x' H y y' H0.
  apply related_classes_eq.
  assert (msub (msub x y) (msub x' y') = msub (msub x x') (msub y y')) as X.
  admit.
  rewrite X.
  apply p_msub; auto.
  Admitted.
  Definition quotient_module_act (r: R): quotient_module -> quotient_module.
  refine (quotient_rec (fun x y => P (msub x y)) (fun a => class_of _ (mact r a)) _).
  intros x y H.
  apply related_classes_eq.
  destruct ismod_m as [_ H0 _ _ _].
  rewrite <- H0.
  auto.
  Defined.  
  Definition isModule_quotient: isModule (ring := isring)
    quotient_module quotient_module_zero quotient_module_sub quotient_module_act.
  Admitted.
End subquo.

