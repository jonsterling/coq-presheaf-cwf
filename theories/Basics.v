From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.
Set Primitive Projections.
Generalizable All Variables.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.ProofIrrelevance.
Require Import Unicode.Utf8.


Import EqNotations.

Local Definition eq_exist_uncurried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
           (pq : { p : u1 = v1 | rew p in u2 = v2 })
  : exist _ u1 u2 = exist _ v1 v2.
Proof.
  destruct pq as [p q].
  destruct q; simpl in *.
  destruct p; reflexivity.
Qed.


Local Definition eq_sig_uncurried {A : Type} {P : A -> Prop} (u v : { a : A | P a })
           (pq : { p : proj1_sig u = proj1_sig v | rew p in proj2_sig u = proj2_sig v })
  : u = v.
Proof.
  destruct u as [u1 u2], v as [v1 v2]; simpl in *.
  apply eq_exist_uncurried; exact pq.
Qed.

Theorem eq_sig {A : Type} {P : A -> Prop} (u v : { a : A | P a }) :
  proj1_sig u = proj1_sig v
  → u = v.
Proof.
  move=> p.
  apply: eq_sig_uncurried.
  exists p.
  apply: proof_irrelevance.
Qed.


Hint Extern 4 => apply: eq_sig.