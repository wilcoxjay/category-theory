Require Import Program.

Set Universe Polymorphism.

Class Category := {
  object : Type;
  morphism : object -> object -> Type;
  id {A} : morphism A A;
  (* note that composition is defined "the right way" where f ∘ g = \a. g (f a) *)
  composition {A B C} : morphism A B -> morphism B C -> morphism A C;
  leftId {A B} {f:morphism A B} : composition id f = f;
  rightId {A B} {f:morphism A B} : composition f id = f;
  assoc {A B C D} {f:morphism A B} {g:morphism B C} {h:morphism C D} : composition (composition f g) h = composition f (composition g h)
}.

Notation "A → B" := (morphism A B) (at level 45).
Notation "f ∘ g" := (composition f g).
