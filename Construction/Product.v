Require Import FunctionalExtensionality.
Require Import Program.
Require Import List.
Import ListNotations.
Require Import ListEx.
Require Import String.
Require Import Ascii.
Require Import Misc.
Require Import Category.
Require Import Coq.
Require Import Co.
Require Import Functor.
Require Import Diagram.
Require Import Diagram.Parser.

Set Universe Polymorphism.

Module SimpleProduct.
Class Product `{Category} := {
  bundle : object -> object -> object;
  factor {a b c:object} (p:c → a) (q:c → b) : c → bundle a b;
  projL {a b:object} : bundle a b → a;
  projR {a b:object} : bundle a b → b;
  productOk {a b c} {p:c → a} {q:c → b} : factor p q ∘ projL = p /\ factor p q ∘ projR = q;
  pairUnique {a b c} {p:c → a} {q:c → b} f : 
    f p q ∘ projL = p -> f p q ∘ projR = q -> f p q = factor p q
}.
End SimpleProduct.

Module ImmediateDiagramProduct.
Section ImmediateDiagram.

Context `{Category}.

Variable c a prod b:object.
Variable p:c → a.
Variable pair : c → prod.
Variable q:c → b.
Variable fst : prod → a.
Variable snd : prod → b.

Definition objects := [a; b; c; prod].
Definition Vertex := ListEx.index objects.

Definition ai : Vertex := found.
Definition bi : Vertex := next found.
Definition ci : Vertex := next (next found).
Definition prodi : Vertex := next (next (next found)).

Definition arrows : list {s:Vertex & {d:Vertex & lookup s → lookup d}} := [
  [ci & [ai & p]];
  [ci & [bi & q]];
  [ci & [prodi & pair]];
  [prodi & [ai & fst]];
  [prodi & [bi & snd]]
].

Definition immediateDiagram : Diagram := {|
  Diagram.Vertex := Vertex;
  vertexObject := lookup;
  Arrow s d := ListEx.index (section arrows s d);
  arrowMorphism x y := lookup
|}.

End ImmediateDiagram.

Class Product `{Category} := {
  bundle : object -> object -> object;
  factor {a b c:object} (p:c → a) (q:c → b) : c → bundle a b;
  projL {a b:object} : bundle a b → a;
  projR {a b:object} : bundle a b → b;
  productOk {a b c} {p:c → a} {q:c → b} : denote (immediateDiagram c a (bundle a b) b p (factor p q) q projL projR);
  pairUnique {a b c} {p:c → a} {q:c → b} f : 
    f p q ∘ projL = p -> f p q ∘ projR = q -> f p q = factor p q
}.

End ImmediateDiagramProduct.

Class Product `{Category} := {
  bundle : object -> object -> object;
  factor {a b c:object} (p:c → a) (q:c → b) : c → bundle a b;
  projL {a b:object} : bundle a b → a;
  projR {a b:object} : bundle a b → b;
  pairUnique {a b c} {p:c → a} {q:c → b} f : 
    f p q ∘ projL = p -> f p q ∘ projR = q -> f p q = factor p q;
  productOk {a b c} {p:c → a} {q:c → b} : denote (parseDiagram ([
    "                       ";
    "     p     c     q     ";
    "  +--------o--------+  ";
    "  |        |        |  ";
    "  |        |factr   |  ";
    "  |        |        |  ";
    "  v  prjL  v  prjR  v  ";
    "  o<-------o------->o  ";
    "  a      bundle     b  ";
    "                       "
    ] % string) c a (bundle a b) b p (factor p q) q projL projR)
}.

Record prod A B := pair {fst:A; snd:B}.
Arguments pair [_ _] _ _.
Arguments fst [_ _] _.
Arguments snd [_ _] _.

Instance prodIsProduct : @Product Coq := {|
  bundle := prod : @object Coq -> @object Coq -> @object Coq;
  factor a b c p q x := pair (p x) (q x);
  projL := fst;
  projR := snd
|}.
Proof.
  - compute.
    intros ? ? ? ? ? f h h'.
    extensionality x.
    specialize (equal_f h x); clear h; intro h.
    specialize (equal_f h' x); clear h'; intro h'.
    rewrite <- h.
    rewrite <- h'.
    destruct (f p q x).
    reflexivity.
  - Opaque morphism object composition id fst snd.
    intros. 
    compute. 
    Transparent morphism object composition id fst snd.
    compute.
    constructor; reflexivity.
Defined.

Inductive sum A B := 
| inl : A -> sum A B
| inr : B -> sum A B.
Arguments inl [_ _] _.
Arguments inr [_ _] _.

Instance sumIsCoProduct : @Product (co Coq) := {|
  bundle := sum : @object (co Coq) -> @object (co Coq) -> @object (co Coq);
  factor a b c p q x := match x with inl a => p a | inr b => q b end;
  projL := @inl;
  projR := @inr
|}.
Proof.
  - compute.
    intros ? ? ? ? ? f h h'.
    extensionality x.
    destruct x as [l | r].
    + specialize (equal_f h l); clear h; intro h.
      rewrite <- h.
      reflexivity.
    + specialize (equal_f h' r); clear h; intro h.
      rewrite <- h.
      reflexivity.
  - compute. 
    intros.
    constructor; reflexivity.
Defined.

Definition Sum {C:Category} := @Product (co C).

Instance CatProduct (C D:Category) : Category := {
  object := prod (@object C) (@object D);
  morphism A B := prod (fst A → fst B) (snd A → snd B);
  id A := pair id id;
  composition A B C f g := pair (fst f ∘ fst g) (snd f ∘ snd g)
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

Instance catProductIsProduct : @Product Cat := {|
  bundle := CatProduct : @object Cat -> @object Cat -> @object Cat;
  factor a b c p q := {|
      fobj x := _;
      fmap x y f := _ 
    |};
  projL x := _;
  projR x := _
|}.
Proof.
  - cbn in *. 
    exact (pair (@fobj _ _ p x) (@fobj _ _ q x)).
  - cbn in *.
    exact (pair (@fmap _ _ p _ _ f) (@fmap _ _ q _ _ f)).
  - shelve.
  - shelve.
  - cbn in *.
Admitted.

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
    exact (sum (fst a) (snd a)).
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
