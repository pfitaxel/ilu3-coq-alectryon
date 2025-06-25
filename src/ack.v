(* iteree n fois de f *)
Fixpoint pow (f:nat->nat) n a :=
  match n with
    0 => a
  | S p => pow f p (f a)
  end.

Lemma pow_swap: forall f n a, pow f n (f a) = f (pow f n a).
Proof.
  induction n; simpl; intros; auto.
Qed.

(* ack défini avec pow *)
Fixpoint ack a b : nat :=
match a with
| 0 => S b
| S a => pow (ack a) (S b) 1
end.
Require Import Lia.

(* on montre que ack satisfait les axiomes de la définition classique *)
Lemma ack1: forall y, ack 0 y = y+1.
Proof.
  simpl; intros; lia.
Qed.

Lemma ack2: forall x, x > 0 -> ack x 0 = ack (x-1) 1.
Proof.
  simpl; intros.
  destruct x; try lia.
  simpl.
  f_equal; lia.
Qed.

Lemma ack3: forall x y, x>0 -> y>0->ack x y = ack (x-1) (ack x (y-1)).
Proof.
  intros; destruct x; try lia; destruct y; try lia.
  simpl.
  assert (forall x, x-0=x) as h0 by (intro; lia); do 2 rewrite h0; clear h0.
  rewrite pow_swap.
  reflexivity.
Qed.

