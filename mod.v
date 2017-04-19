Require Import HitTactics.
Require Import HoTT.

Module Export Mod2.
  Private Inductive Nmod2 :=
  | O : Nmod2
  | S : Nmod2 -> Nmod2.
  Axiom mod : O = S (S O).
  Fixpoint Nmod2_recd
           (Y : Nmod2 -> Type)
           (z : Y O)
           (s : forall x, Y x -> Y (S x))
           (q : mod # z = s (S O) (s O z))
           (x : Nmod2) : Y x :=
    match x return _ -> Y x with
    | O => fun _ => z
    | S x => fun _ => s x (Nmod2_recd Y z s q x)
    end q.
  Axiom Nmod2_recd_beta_path : forall
      (Y : Nmod2 -> Type)
      (z : Y O)
      (s : forall x, Y x -> Y (S x))
      (q : mod # z = s (S O) (s O z)),
      apD (Nmod2_recd Y z s q) mod = q.
  Definition Nmod2_ind (Y : Nmod2 -> Prop) := Nmod2_recd Y.
  Definition Nmod2_rec
           (Y : Type)
           (z : Y)
           (s : Y -> Y)
           (q : z = s (s z))
           (x : Nmod2) : Y.
  Proof.
    refine (Nmod2_recd (fun _ => Y) z (fun _ => s) _ x).
    etransitivity.
    + apply transport_const.
    + apply q.
  Defined.
  Definition Nmod2_rec_beta_path : forall
      (Y : Type)
      (z : Y)
      (s : Y -> Y)
      (q : z = s (s z)),
      ap (Nmod2_rec Y z s q) mod = q.
  Proof. intros.
    unfold Nmod2_rec.
    Check cancelL.
    Check transport_const.
    eapply (cancelL (transport_const mod _)).
    Check apD_const.
    rewrite <- apD_const.
    rewrite Nmod2_recd_beta_path. cbn. reflexivity.
  Defined.
End Mod2. 


Definition gmod (n : Nmod2) : n = S (S n).
Proof.
  hrecursion n Nmod2_recd.
  - apply mod.
  - intros n p. apply ap. exact p.
  - simpl. rewrite <- ap_compose. 
    rewrite transport_paths_FlFr. hott_simpl.
Defined.

Definition plus (n m : Nmod2) : Nmod2.
Proof.
hrecursion m Nmod2_rec.
- exact n. 
- intros r. exact (S r).
- simpl. apply gmod.
Defined.
Print plus.
Definition plus' : Nmod2 -> Nmod2 -> Nmod2.
Proof.
intro n.
refine (Nmod2_recd _ _ _ _).
  Unshelve.

  Focus 2.
  apply n.

  Focus 2.
  intros m k.
  apply (S k).

  simpl. etransitivity. apply transport_const. apply gmod.
Defined.
Goal forall n m,  plus n m = plus' n m.
intros n m. hrecursion m Nmod2_recd; try reflexivity.
- cbn. rewrite transport_paths_FlFr. hott_simpl.
  rewrite ap_V.
  rewrite Nmod2_rec_beta_path.
  eapply (cancelL (gmod _)). hott_simpl.
  eapply (cancelL (transport_const mod (plus' n O))).
  rewrite <- (apD_const (plus' n) mod).
  rewrite Nmod2_recd_beta_path. reflexivity. Qed.

Definition f (b : Bool) : Nmod2 :=
if b then (S O) else O.
Definition g (x : Nmod2) : Bool.
Proof.
hrecursion x Nmod2_rec.
- exact false.
- intros b. exact (negb b).
- simpl. auto.
Defined.

Lemma gf_iso x : g (f x) = x.
Proof.
  destruct x; auto. 
Qed.

Lemma f_neg b : f (negb b) = S (f b).
Proof. destruct b; simpl; auto. apply mod. Defined.

Lemma fg_iso x : f (g x) = x.
Proof.
hrecursion x Nmod2_recd.
- reflexivity.
- intros x Hfg.
  transitivity (S (f (g x))).
  + apply f_neg. 
  + exact (ap S Hfg).
- simpl. 
  rewrite transport_paths_FlFr.
  hott_simpl. rewrite ap_compose.
  assert (ap g mod = idpath) by apply hset_bool. rewrite X.
  hott_simpl.
Qed.

Instance: IsEquiv g.
Proof.
  refine (BuildIsEquiv _ _ g f gf_iso fg_iso _).
  intros. apply hset_bool.
Defined. 
Global Instance hset_Nmod : IsHSet Nmod2.
Proof. 
  apply trunc_equiv with Bool (g^-1);
  typeclasses eauto.
Defined.

