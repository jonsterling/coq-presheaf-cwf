From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".
Set Primitive Projections.
Set Universe Polymorphism.
Generalizable All Variables.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.ProofIrrelevance.
Require Import Unicode.Utf8.
Require Import Coq.Logic.EqdepFacts.

From cwf Require Import Basics Category Functor Sets Presheaf.

Close Scope nat_scope.

Local Hint Extern 4 => apply: id_l.
Local Hint Extern 4 => apply: id_r.
Local Hint Extern 4 => apply: cmp_assoc.


Section CWF.
  Context `{ℂ : Category}.

  Definition Cx := Psh ℂ.
  Definition Ty `(Γ : Cx) := Psh (∮ Γ).

  Notation "Γ ⊢ 'type'" := (Ty Γ) (at level 10).

  Program Definition Emp : Cx :=
    {| fobj := fun x => True |}.

  Notation "⋄" := Emp.

  Program Definition Snoc (Γ : Cx) (A : Γ ⊢ type) : Cx :=
    {| fobj := fun x => { γ : Γ x & A {| fib := x; elt := γ |} };
       fmap := fun x y f X => existT _ (f <$[Γ]> (projT1 X)) (f <$[A]> (projT2 X))
    |}.
  Next Obligation.
    apply: functional_extensionality.
    move=> [γ a].
    simplify_eqs.
 (* THIS IS HARD *)
  Admitted.

  Theorem fold_cmp {A B C : SET} {m : B ~> C} {n : A ~> B} :
    (fun x : A => m (n x)) = m ∘ n.
  Proof.
    auto.
  Qed.

  Ltac t_fold_cmps :=
    repeat rewrite fold_cmp.

  (* non-dependent products *)
  Program Definition Prod Γ (A B : Γ ⊢ type) : Γ ⊢ type :=
    {| fobj := fun X => A X * B X;
       fmap := fun X Y f a => (f <$[A]> fst a, f <$[B]> snd a)
    |}.

  Next Obligation.
    apply: functional_extensionality; move=> [? ?].
    by repeat erewrite @fmap_idn.
  Qed.

  Next Obligation.
    apply: functional_extensionality; move=> [a b] //=.
    apply: f_equal2; [move: a | move: b];
    apply: equal_f; t_fold_cmps;
    by rewrite <- fmap_cmp.
  Qed.

End CWF.