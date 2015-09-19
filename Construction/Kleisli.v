Require Import Program.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Monad.
Require Import Category.
Require Import Functor.
Require Import Isomorphism.

Set Universe Polymorphism.

Instance KleisliCategory T `{Monad T} : Category := {|
  object := Type;
  morphism A B := A -> T B;
  id A := ret;
  composition A B C f g a := bind (f a) g
|}.
Proof.
  - intros.
    extensionality a.
    apply left_identity.
  - intros.
    extensionality a.
    apply right_identity.
  - intros.
    extensionality a.
    apply associativity.
Defined.      

Instance maybeCat : Category := {| 
  object := Type;
  morphism A B := A -> option B;
  id A := Some;
  composition A B C f g a := match f a with None => None | Some b => g b end
|}.
Proof.
  - intros. 
    reflexivity.
  - intros. 
    extensionality a.
    case (f a); reflexivity.
  - intros. 
    extensionality a.
    case (f a); reflexivity.
Defined.

Example composeMaybe0 {A} : Some ∘ Some ∘ Some = Some   :> (A -> option A).
  compute; reflexivity.
Defined.

Example composeMaybe1 {A} : Some ∘ const None ∘ Some = const None   :> (A -> option A).
  compute; reflexivity.
Defined.

Example composeMaybe2 {A} : Some ∘ id ∘ id = Some   :> (A -> option A).
  compute; reflexivity.
Defined. 

Example composeMaybe3 : Some ∘ const (id 5) ∘ id = const (id 5)   :> (nat -> option nat).
  compute; reflexivity.
Defined. 

Example composeMaybe4 : const (id 5) ∘ const (id 4) = const (id 4)   :> (nat -> option nat).
  compute; reflexivity.
Defined. 

Instance maybeCatKleisliIso : @Isomorphism Cat maybeCat (KleisliCategory option) := {|
  f := _;
  g := _
|}.
Proof.
  - refine {| fobj o := _; fmap a b f := _ |}.
    + exact o.
    + exact f.
    + reflexivity.
    + reflexivity.
  - refine {| fobj o := _; fmap a b f := _ |}.
    + exact o.
    + exact f.
    + reflexivity.
    + reflexivity.
  - compute.
    reflexivity.
  - compute.
    reflexivity.
Defined.
