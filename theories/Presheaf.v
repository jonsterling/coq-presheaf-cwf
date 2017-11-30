From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.
Set Primitive Projections.
Generalizable All Variables.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.ProofIrrelevance.
Require Import Unicode.Utf8.

From cwf Require Import Basics Category Functor Sets.


Local Hint Extern 4 => apply: id_l.
Local Hint Extern 4 => apply: id_r.
Local Hint Extern 4 => apply: cmp_assoc.

Definition Psh (ℂ : Category) :=
  ℂ ⟶ SET.

Record Elt `(ℱ : Psh ℂ) :=
  { fib : obj;
    elt : ℱ fib }.

Arguments fib [ℂ ℱ].
Arguments elt [ℂ ℱ].

Program Definition ELT `(ℱ : Psh ℂ) : Category :=
  {| obj := Elt ℱ;
     hom := fun a b => { f : fib a ~> fib b | f <$[ ℱ ]> (elt a) = elt b };
     idn := fun _ => idn;
     cmp := fun _ _ _ => cmp
  |}.

Next Obligation.
  by rewrite fmap_idn.
Qed.

Next Obligation.
  by rewrite fmap_cmp.
Qed.

Notation "∮ ℱ" := (ELT ℱ) (at level 10).