Require Import Category.
Require Import Coq.

Set Universe Polymorphism.

Class Isomorphism `{Category} (a b:object):= {
  f : a → b;
  g : b → a;
  fgCompose : f ∘ g = id;
  gfCompose : g ∘ f = id
}.

Notation "a ≈ b" := (Isomorphism a b) (at level 45).

Definition bijection := @Isomorphism Coq.
