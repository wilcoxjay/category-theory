Require Import Category.
Require Import FunctionalExtensionality.

Set Universe Polymorphism.

Instance co `(Category) : Category := {|
  object := object;
  morphism a b := morphism b a;
  id a := id;
  composition a b c f g := g ∘ f
|}.
Proof.
  - intros.
    apply Category.rightId.
  - intros.
    apply Category.leftId.
  - intros.
    symmetry.
    apply Category.assoc.
Defined.

Definition coCoEqId C : co (co C) = C.
  unfold co.  
  cbn.
  destruct C.
  f_equal.
  repeat (let x:=fresh in extensionality x).
  cbn.
  rewrite eq_sym_involutive.
  reflexivity.
Defined.
