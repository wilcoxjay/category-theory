Require Import FunctionalExtensionality.
Require Import Category.
Require Import Functor.
Require Import Coq.

Instance CatProduct (C D:Category) : Category := {
  object := @object C * @object D;
  morphism A B := ((fst A → fst B) * (snd A → snd B)) % type;
  id A := (id, id);
  composition A B C f g := (fst f ∘ fst g, snd f ∘ snd g)
}.
Proof.
  - intros ? ? []; intros.
    cbn.
    f_equal; apply Category.leftId.
  - intros ? ? []; intros.
    cbn.
    f_equal; apply Category.rightId.
  - intros ? ? ? ? [] []; intros.
    cbn.
    f_equal; apply Category.assoc.
Defined.

Definition BiFunctor A B C := Functor (CatProduct A B) C.

Definition productBiFunctor : BiFunctor Coq Coq Coq.
  refine {|
    fobj a := _;
    fmap := _ 
  |}.
  - cbn in *. 
    exact (fst a * snd a).
  - cbn. 
    intros ? ? []; intros f g []; intros x y.
    exact (f x, g y).
  - cbn. 
    intros.
    extensionality x.
    destruct x.
    reflexivity.
  - cbn. 
    intros [] [] [] [] []; intros.
    extensionality x.
    destruct x.
    reflexivity.
Defined. 

Definition sumBiFunctor : BiFunctor Coq Coq Coq.
  refine {|
    fobj a := _;
    fmap := _ 
  |}.
  - cbn in *.
    exact (fst a + snd a).
  - cbn.
    intros ? ? []; intros f g x.
    refine (match x with
    | inl x => inl (f x)
    | inr x => inr (g x)
    end).
  - cbn.
    intros.
    extensionality x.
    destruct x; reflexivity.
  - cbn.
    intros [] [] [] [] []; intros.
    extensionality x.
    destruct x; reflexivity.
Defined.
