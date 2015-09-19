Require Import Category.

Set Universe Polymorphism.

Instance Coq : Category := {|
  object := Type;
  morphism A B := A -> B;
  id A a := a;
  composition A B C f g a := g (f a)
|}.
Proof.
  all: intros; reflexivity.
Defined.