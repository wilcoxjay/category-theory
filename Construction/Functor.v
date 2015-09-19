Require Import Category.
Require Import Coq.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import List.

Set Universe Polymorphism.

Class Functor (C D:Category) := {
  fobj : @object C -> @object D;
  fmap {a b} : (a → b) -> (fobj a → fobj b);
  mapId {a} : fmap (@id C a) = id;
  mapCompose {a b c} {f:a → b} {g:b → c} : fmap (f ∘ g) = fmap f ∘ fmap g
}.

Instance IdentityFunctor C : Functor C C :=
  {| fobj a := a; fmap a b f := f |}.
Proof.
  all: intros;reflexivity. 
Defined.

Instance Cat : Category := {|
  object := Category;
  morphism := Functor;
  id := IdentityFunctor;
  composition a b c f g := {| fobj a := fobj (fobj a); 
                              fmap a b f := fmap (fmap f) |}
|}.
Proof.
  - intros.
    rewrite mapId.
    rewrite mapId.
    reflexivity.
  - intros.
    rewrite mapCompose.
    rewrite mapCompose.
    reflexivity.
  - cbn. 
    intros.
    case f.
    intros.
    f_equal; apply proof_irrelevance.
  - cbn. 
    intros.
    case f.
    intros.
    f_equal; apply proof_irrelevance.
  - cbn. 
    intros.
    f_equal; apply proof_irrelevance.
Defined.

Definition endoFunctor `{C:Category} := Functor C C.

Definition listEndoFunctor : @endoFunctor Coq.
  refine {|
    fobj := list : @object Coq -> @object Coq;
    fmap := map
  |}.
  - intro A.
    extensionality l.
    apply map_id.
  - intros A B C f g.
    extensionality l.
    induction l.
    + reflexivity.
    + cbn in *.
      congruence.
Defined.

Instance Const (C D:Category) (o:@object D) : Functor C D := {|
  fobj a := o;
  fmap a b f:= id
|}.
Proof.
  - intros. 
    reflexivity.
  - intros. 
    rewrite Category.rightId.
    reflexivity.
Defined.