(* Exercises in HoTT.
  Template from http://blog.ezyang.com/2013/07/hott-exercises-in-coq-in-progress/. *)

Require Import HoTT.

Definition admit {T: Type} : T. Admitted.

(* Exercise 1.1 *)
Definition mycompose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C 
  := fun x => g (f x).

Goal forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
       mycompose h (mycompose g f) = mycompose (mycompose h g) f.
unfold mycompose.
reflexivity.
Qed.

(* Exercise 1.2 *)
Section ex_1_2_prod.
  Variable A B : Type.
  Check @fst.
  Check @snd.
  Definition my_prod_rec (C : Type) (g : A -> B -> C) (p : A * B) : C 
    := g (fst p) (snd p).
  Goal fst = my_prod_rec A (fun a => fun b => a).
    unfold my_prod_rec.
    reflexivity.
  Qed.
  Goal snd = my_prod_rec B (fun a => fun b => b).
    unfold my_prod_rec.
    reflexivity.
  Qed.

End ex_1_2_prod.

Section ex_1_2_sig.
  Variable A : Type.
  Variable B : A -> Type.
  Check @projT1.
  Check @projT2.
  Definition my_sig_rec (C : Type) (g : forall (x : A), B x -> C) (p : exists (x : A), B x) : C
    := g (projT1 p) (projT2 p).
  Goal @projT1 A B = my_sig_rec A (fun a => fun b => a).
    reflexivity.
  Qed.
  (* What goes wrong when you try to prove this for projT2? *)
  
End ex_1_2_sig.

(* Exercise 1.3 *)

Definition refl {A : Type} (x : A) : x = x := 1%path.

Section ex_1_3_prod.
  Variable A B : Type.
  (* Given by the book *)
  Definition uppt : forall (x : A * B), ((fst x, snd x) = x) :=
    fun p => match p with (a,b) => refl (a,b) end.
  Definition my_prod_ind (C : A * B -> Type)
    (g : forall (x : A) (y : B), C (x, y)) (x : A * B) : C x
    := (paths_rew (A*B) (fst x, snd x) x C
      (g (fst x) (snd x)) (uppt x)).
  Goal forall C g a b, my_prod_ind C g (a, b) = g a b.
    intros C g a b.
    unfold my_prod_ind.
    simpl.
    reflexivity.
  Qed.
End ex_1_3_prod.

Section ex_1_3_sig.
  Variable A : Type.
  Variable B : A -> Type.
  Definition sig_uppt : forall (x : exists (a : A), B a), ((projT1 x; projT2 x) = x).
    intro x.
    destruct x.
    exact (refl (x;b)).
  Defined.
  Definition mysig_ind (C : (exists (a : A), B a) -> Type) 
    (g : forall (a : A) (b : B a), C (a; b)) (x : exists (a : A), B a) : C x
    := paths_rew (exists (a:A), B a) (projT1 x; projT2 x) x C
      (g (projT1 x) (projT2 x)) (sig_uppt x).
  Goal forall C g a b, mysig_ind C g (a; b) = g a b.
    intros C g a b.
    unfold mysig_ind.
    simpl.
    reflexivity.
  Qed.
End ex_1_3_sig.

(* Exercise 1.4 *)
Fixpoint iter (C : Type) (c0 : C) (cs : C -> C) (n : nat) : C :=
  match n with
    | 0 => c0
    | S n' => cs (iter C c0 cs n')
  end.
Definition mynat_rec (C : Type) : C -> (nat -> C -> C) -> nat -> C.
  intros e s n.
  apply (snd : nat * C -> C).
  apply iter.
  exact (0, e).
  intro p.
  destruct p.
  exact (S n0, s n0 c).
  exact n.
Defined.
Eval compute in mynat_rec (list nat) nil (@cons nat) 2.
Eval compute in nat_rect (fun _ => list nat) nil (@cons nat) 2.

(* Exercise 1.5 *)
Definition mycoprod (A B : Type) := exists (x : Bool), Bool_rect (fun _ => Type) A B x.

Section ex_1_5.
  Variable A B : Type.
  Definition inl := existT (Bool_rect (fun _ => Type) A B) true.
  Definition inr := existT (Bool_rect (fun _ => Type) A B) false.
  Definition mycoprod_ind (C : mycoprod A B -> Type)
                          (l : forall (a : A), C (inl a))
                          (r : forall (b : B), C (inr b))
                          (x : mycoprod A B) : C x.
    destruct x.
    unfold inl in l.
    unfold inr in r.
    destruct x.
    exact (l b).
    exact (r b).
   Defined.
  Goal forall C l r x, mycoprod_ind C l r (inl x) = l x.
    unfold mycoprod_ind; simpl.
    intros C l b x.
    auto.
  Qed.
  Goal forall C l r x, mycoprod_ind C l r (inr x) = r x. auto. Qed.
End ex_1_5.

(* Exercise 1.6 *)

Definition myprod (A B : Type) := forall (x : Bool), Bool_rect (fun _ => Type) A B x.
Section ex_1_6.
  Context `{Funext}.
  Variable A B : Type.
  Definition mypr1 (p : myprod A B) := p true.
  Definition mypr2 (p : myprod A B) := p false.
  Definition mymkprod (a : A) (b : B) : myprod A B := Bool_rect (Bool_rect (fun _ => Type) A B) a b.
  Definition myprod_ind (C : myprod A B -> Type)
    (g : forall (x : A) (y : B), C (mymkprod x y)) (x : myprod A B) : C x.
    generalize (g (mypr1 x) (mypr2 x)); intro H1.
    unfold mymkprod in H1.
    unfold Bool_rect in H1.
    unfold mypr1 in H1.
    unfold mypr2 in H1.
    assert ((fun (b:Bool) => if b  return (if b then A else B)
           then x true else x false) = x).
    apply path_forall.
    compute.
    intro x0.
    case x0; auto.
    rewrite X in H1.
    exact H1.
  Defined.
  Goal forall C g a b, myprod_ind C g (mymkprod a b) = g a b.
    intros C g a b.
    unfold myprod_ind.
    simpl.
    compute.
    simpl.
    Check (let (equiv_inv, eisretr, eissect, _) :=
       isequiv_apD10 Bool
         (fun x : Bool => if x then A else B)
         (fun b0 : Bool =>
          if b0 as b1 return (if b1 then A else B)
          then a
          else b)
         (fun b0 : Bool =>
          if b0 as b1 return (if b1 then A else B)
          then a
          else b) in
   equiv_inv).
   Admitted.
   (*
    Check (fun x0 : Bool =>
     if x0 as b0
      return
        ((if b0 as b1 return (if b1 then A else B)
          then a
          else b) =
         (if b0 as b1 return (if b1 then A else B)
          then a
          else b))
     then 1
     else (1 : b = b)).
    Check a.
    assert (forall (x y: myprod A B) (z:C x) (a: x = y), match a in (_ = y) return (C y) with | 1 => z end = z).
    intros A0 B0 x y z a0.
    elim a0.
    reflexivity.
    simpl.
    compute.
    replace ((let (equiv_inv, eisretr, eissect, _) :=
       isequiv_apD10 Bool
         (fun x : Bool => if x then A else B)
         (fun b0 : Bool =>
          if b0 as b1 return (if b1 then A else B)
          then a
          else b)
         (fun b0 : Bool =>
          if b0 as b1 return (if b1 then A else B)
          then a
          else b) in
   equiv_inv)) with tt.
    apply X with (z := g a b).
    simpl.
  *)
End ex_1_6.

Section ex_1_7.

(* based path induction. given in 1.12 *)
  Definition path_ind: forall (A:Type)
    (C:(forall (x y:A), x=y -> Type)),
       (forall x, C x x 1)
     -> forall (x y:A) (p:x=y), C x y p.
    intros A C t x y p.
    case p.
    exact (t x).
  Defined.
(* equation which hold in based path induction. *)
  Lemma bpi_equality:
    forall (A:Type) 
      (C:forall (x y:A), x = y -> Type)
      (x:A)
      (c:forall x, C x x 1),
         path_ind A C c x x 1 = c x.
    simpl.
    reflexivity.
  Qed.
  (* question: derive based_path_ind by path_ind. *)
  Definition based_path_ind: forall (A:Type) (a:A)
    (C:forall (x:A), a = x -> Type), C a 1 -> 
      forall (x:A) (p: a = x), C x p.
  intros A a C c x p.
  (*
  change (C x p) with ((fun t u (p:t = u) => C u p) a x p).
  apply path_ind with (C:= (fun _ x0 => C x0)) (p:=p).
  exact c.
  Defined.
  *)
  Admitted.
End ex_1_7.

Section ex_1_7_inv.

(* based path induction. given in 1.12 *)
  Definition based_path_ind_i: forall (A:Type) (a:A)
    (C:forall (x:A), a = x -> Type), C a 1 -> 
      forall (x:A) (p: a = x), C x p.
  intros A a C c x p.
  case p.
  exact c.
  Defined.
(* equation which hold in based path induction. *)
  Lemma bpi_equality_i:
    forall (A:Type) (a:A)
      (C:forall (x:A), a = x -> Type)
      (c:C a 1),
         based_path_ind_i A a C c a 1 = c.
    simpl.
    reflexivity.
  Qed.
  (* question: derive path_ind by based_path_ind. *)
  Definition path_ind_i: forall (A:Type)
    (C:(forall (x y:A), x=y -> Type)),
       (forall x, C x x 1)
     -> forall (x y:A) (p:x=y), C x y p.
    intros A C t x y p.
    apply based_path_ind_i.
    exact (t x).
  Defined.
End ex_1_7_inv.

Section ex_1_8.
  Fixpoint rec_N (C:Type) (init:C)
   (cs: nat -> C -> C) (n:nat) :C := match n with
    | 0 => init
    | S m => cs m (rec_N C init cs m)
   end.
End ex_1_8.

Section ex_1_9.
  Definition fin(n: nat) : Type.
  induction n.
  exact Empty.
  Print Empty.
  exact (option IHn).
  Defined.
  Definition fmax: forall n, fin (S n).
  induction n.
  simpl.
  exact None.
  simpl.
  exact (Some IHn).
  Defined.
End ex_1_9.

Section ex_1_10.
  Fixpoint ack(n m:nat):nat :=
    rec_N (nat->nat) S (fun _ q m' => rec_N nat (1%nat) (fun _ => q) (S m')) n m.
  Goal forall n, ack 0 n = S n.
  simpl.
  auto.
  Qed.
  Goal forall n, ack (S n) 0 = ack n 1.
  induction n.
  simpl.
  auto.
  auto.
  Qed.
End ex_1_10.

Section ex_1_11.
  Goal forall P:Type, ~~~P -> ~P.
  intros P H H1.
  apply H.
  intro H2.
  exact (H2 H1).
  Qed.
End ex_1_11.

Section ex_1_14.
  Goal forall (A:Type) (x:A)(p: x=x), p = 1.
  intros A x p.
  Admitted.
End ex_1_14.




