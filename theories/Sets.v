From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.
Set Primitive Projections.

Require Import Coq.Program.Tactics.
Require Import Unicode.Utf8.

From cwf Require Import Category.

Program Definition SET : Category :=
  {| obj := Type;
     hom := λ A B, A → B;
     idn := λ _ x, x;
     cmp := λ _ _ _ f g x, f (g x)
  |}.
