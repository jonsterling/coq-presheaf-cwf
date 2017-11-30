From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.
Set Primitive Projections.
Generalizable All Variables.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.ProofIrrelevance.
Require Import Unicode.Utf8.

From cwf Require Import Basics Category Functor Sets Presheaf.

Section CWF.
  Context `{ℂ : Category}.

  Definition Cx := Psh ℂ.
  Definition Ty `(Γ : Cx) := Psh (∮ Γ).

  Notation "Γ ⊢ 'type'" := (Ty Γ) (at level 10).

  Program Definition Emp : Cx :=
    {| fobj := fun x => True |}.

  Notation "⋄" := Emp.


End CWF.