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
Require Import Diagram.
Require Import Diagram.Parser.

Set Universe Polimorphism.

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

Definition imageDiagram := parseDiagram [
  "        c        ";
  "    +---o---+    ";
  "  p |   |   | q  ";
  " +--+   |   +--+ ";
  " |      |      | ";
  " |      |pair  | ";
  " v      v      v ";
  " o<-----o----->o ";
  " a     prd     b "
] % string.

Class Product `{Category} := {
  prod : object -> object -> object;
  pair {a b c:object} (p:c → a) (q:c → b) : c → prod a b;
  fst {a b:object} : prod a b → a;
  snd {a b:object} : prod a b → b;
  productOk {a b c} {p:c → a} {q:c → b} : pair p q ∘ fst = p -> pair p q ∘ snd = q;
(*  productOk {a b c} {p:c → a} {q:c → b} : denote (ImmediateDiagram.diagram c a (prod a b) b p (pair p q) q fst snd); *)
(* productOk {a b c} {p:c → a} {q:c → b} : denoteDiagram (parseDiagram img (* denoteProdDiagram *) c a (prod a b) b p (pair p q) q fst snd); *)
  pairUnique {a b c} {p:c → a} {q:c → b} f : 
    f p q ∘ fst = p -> f p q ∘ snd = q -> f p q = pair p q
}.

Instance prodIsProduct : @Product Coq := {|
  prod := Datatypes.prod : @object Coq -> @object Coq -> @object Coq;
  pair a b c p q x := (p x, q x);
  fst := @Datatypes.fst;
  snd := @Datatypes.snd
|}.
Proof.
  - intros.
    Opaque morphism object composition id Datatypes.fst Datatypes.snd.
    (* pair p q ∘ fst = p /\ pair p q ∘ snd = q *)
    compute.
    Transparent morphism object composition id Datatypes.fst Datatypes.snd.
    compute.
    constructor; reflexivity.
  - compute.
    intros ? ? ? ? ? f h h'.
    extensionality x.
    specialize (equal_f h x); clear h; intro h.
    specialize (equal_f h' x); clear h'; intro h'.
    rewrite <- h.
    rewrite <- h'.
    destruct (f p q x).
    reflexivity.
Defined.

Definition Sum {C:Category} := @Product (co C).

Definition sumIsSum : @Sum Coq.
  unfold Sum.
  refine {|
    prod := _;
    pair := _;
    fst := _;
    snd := _
  |}.
  - exact sum.
  - exact (fun a b c p q x => match x with inl a => p a | inr b => q b end).
  - exact @inl.
  - exact @inr.
Proof.
  - compute. 
    intros.
    constructor; reflexivity.
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
Defined.
