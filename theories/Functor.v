From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.
Set Primitive Projections.

Require Import Unicode.Utf8.

From cwf Require Import Category.

(* From John Wiegley's category theory formalization *)

Class Functor {C D : Category} := {
  fobj : C -> D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_idn {x : C} : fmap (@idn C x) = idn;
  fmap_cmp {x y z : C} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) = fmap f ∘ fmap g
}.

Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.


Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

Arguments fmap
  {C%category D%category Functor%functor x%object y%object} f%morphism.

Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.


Hint Rewrite @fmap_idn @fmap_cmp.