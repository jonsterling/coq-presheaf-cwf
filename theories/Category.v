From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.
Set Primitive Projections.

Require Import Unicode.Utf8.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).

(* Drawn from John Wiegley's formalization *)
Class Category :=
  { obj : Type;
    hom : obj → obj → Type
    where "a ~> b" := (hom a b);
    idn {x} : x ~> x;
    cmp {x y z} (f : y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (cmp f g);


    id_l {x y} (f : x ~> y) : idn ∘ f = f;
    id_r {x y} (f : x ~> y) : f ∘ idn = f;

    cmp_assoc
      {x y z w}
      (f : z ~> w) (g : y ~> z) (h : x ~> y) :
      f ∘ (g ∘ h) = (f ∘ g) ∘ h
  }.

Bind Scope category_scope with Category.
Bind Scope object_scope with obj.
Bind Scope homset_scope with hom.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope homset_scope with homset.
Delimit Scope morphism_scope with morphism.


Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.
Notation "x ~{ C }~> y" := (@hom C%category x%object y%object)
  (at level 90) : homset_scope.

Notation "x <~ y" := (@hom _%category y%object x%object)
  (at level 90, right associativity, only parsing) : homset_scope.
Notation "x <~{ C }~ y" := (@hom C%category y%object x%object)
  (at level 90, only parsing) : homset_scope.

Notation "id[ x ]" := (@id _%category x%object)
  (at level 9, format "id[ x ]") : morphism_scope.

Notation "f ∘ g" :=
  (@cmp _%category _%object _%object _%object f%morphism g%morphism)
  : morphism_scope.
Notation "f ∘[ C ] g" :=
  (@cmp C%category _%object _%object _%object f%morphism g%morphism)
  (at level 40, only parsing) : morphism_scope.


Notation "f ≈[ C ] g" :=
  (@eq (@hom C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.
Notation "f ≈[ C ] g" :=
  (@eq (@hom C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.



Coercion obj : Category >-> Sortclass.

Hint Rewrite @id_l : categories.
Hint Rewrite @id_r : categories.

Open Scope category_scope.
Open Scope object_scope.
Open Scope homset_scope.
Open Scope morphism_scope.


Arguments id_l {_%category _%object _%object} _%morphism.
Arguments id_r {_%category _%object _%object} _%morphism.
Arguments cmp_assoc {_%category _%object _%object _%object _%object}
  _%morphism _%morphism _%morphism.
