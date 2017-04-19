Require Import HitTactics.
Require Import HoTT.

Lemma transport_pathspace {X Y : Type} (f g : X -> Y) (x y : X)
      (p : x = y) (q : f x = g x) :
   (transport (fun x => f x = g x) p q) = (ap f p)^ @ q @ (ap g p).
Proof. destruct p. simpl. destruct q. auto. Qed.

Module Export Z2.
  Private Inductive Z2 :=
  | plus' : nat -> Z2
  | minus' : nat -> Z2.
  Axiom zero' : plus' 0 = minus' 0.
  Fixpoint Z2_recd
           (Y : Z2 -> Type)
           (pl : forall n, Y (plus' n))
           (mn : forall n, Y (minus' n))
           (q : zero' # (pl 0) = mn 0)
           (x : Z2) {struct x} : Y x :=
    match x return _ -> Y x with
    | plus' n => fun _ => pl n
    | minus' n => fun _ => mn n
    end q.

  Axiom Z2_recd_beta_path : forall
         (Y : Z2 -> Type)
         (pl : forall n, Y (plus' n))
         (mn : forall n, Y (minus' n))
         (q : zero' # (pl 0) = mn 0),
         apD (Z2_recd Y pl mn q) zero' = q.
  Definition Z2_rec 
           (Y : Type)
           (pl : nat -> Y)
           (mn : nat -> Y)
           (q : pl 0 = mn 0)
           (x : Z2) : Y.
  Proof.  refine (Z2_recd (fun _ => Y) pl mn _ x).
    etransitivity.
    + apply transport_const.
    + apply q.
  Defined.

  Axiom Z2_rec_beta_path : forall
         (Y : Type)
         (pl : forall n, Y)
         (mn : forall n, Y)
         (q : pl 0 = mn 0),
         ap (Z2_rec Y pl mn q) zero' = q.
  Hint Unfold Z2_rec. (* TODO: ??? *)
End Z2.

Fixpoint j (x : nat) : Pos := 
  match x as x' return Pos with
  | 0 => Int.one
  | S y => match y with
           | 0 => Int.one
           | S y' => succ_pos (j y)
           end
  end.

Fixpoint j' (x : Pos) : nat := 
  match x with
  | Int.one => S 0
  | succ_pos y => S (j' y)
  end.

Lemma j'_j n : j' (j (S n)) = S n.
Proof.
  induction n; auto.
  simpl. f_ap. 
Qed.

Lemma j'_pos p : exists n, j' p = S n.
Proof. induction p; eexists; simpl; eauto. Qed.
Lemma j_j' p : j (j' p) = p.
Proof.
  induction p; auto.
  simpl. rewrite IHp. 
  destruct (j'_pos p) as [n Hp]. by rewrite Hp.
Qed.

Definition g : Z2 -> Int.
Proof. intro x.
hrecursion x Z2_rec.
- exact (fun x => match x with 0 => Int.zero | S x => pos (j (S x)) end).
- exact (fun x => match x with 0 => Int.zero | S x => neg (j (S x)) end).
- simpl. reflexivity.
Defined.

Definition f (x : Int) : Z2 :=
  match x with
  | neg n => minus' (j' n)
  | Int.zero => plus' 0
  | pos n => plus' (j' n)
  end.

Lemma gf_iso1 x : g (f x) = x.
Proof.
  induction x; simpl; auto; induction p; try reflexivity.
  - cbn. f_ap. 
    rewrite j_j'.
    destruct (j'_pos p) as [n Hp]. by rewrite Hp.
  - cbn. f_ap.
    rewrite j_j'. 
    destruct (j'_pos p) as [n Hp]. by rewrite Hp.
Qed.

Lemma fg_iso1 x : f (g x) = x.
Proof.
  hrecursion x Z2_recd.
  - induction n; [simpl; reflexivity |].
    simpl. by rewrite j'_j.
  - induction n; [simpl; apply zero'|].
    simpl. by rewrite j'_j.
  - simpl. rewrite transport_pathspace.
    hott_simpl.
    rewrite ap_apply_Fr. 
    rewrite Z2_rec_beta_path. hott_simpl.
Qed.


Instance: IsEquiv g.
Proof.
  refine (BuildIsEquiv _ _ g f gf_iso1 fg_iso1 _).
  intros. apply hset_int.
Defined. 
Global Instance hset_Z : IsHSet Z2.
Proof. 
  apply trunc_equiv with Int (g^-1);
  apply _.
Defined.
