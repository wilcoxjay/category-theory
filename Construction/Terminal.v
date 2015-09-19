Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Program.
Require Import Category.
Require Import Isomorphism.
Require Import Coq.
Require Import Co.

Set Universe Polymorphism.

Class Terminal `{Category} := {
  terminal : object;
  receivesAll o : o → terminal;
  receivesAllUnique {o f} : receivesAll o = f
}.

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

Definition Initial {C} := @Terminal (co C).

Definition coqInitialEmptySet : @Initial Coq. 
refine {|
  terminal := Empty_set:@object (co Coq);
  receivesAll o := Empty_set_rect (const o)
|}.
Proof.
  compute.
  intros.
  extensionality a.
  destruct a.
Defined.

Instance coqTerminalUnit : @Terminal Coq. 
refine {|
  terminal := unit:@object Coq;
  receivesAll o := fun _ => tt
|}.
Proof.
  compute.
  intros.
  extensionality a.
  destruct (f a).
  reflexivity.
Defined.

Instance coqTerminalTrue : @Terminal Coq. 
refine {|
  terminal := True:@object Coq;
  receivesAll o := fun _ => I
|}.
Proof.
  compute.
  intros.
  apply proof_irrelevance.
Defined.

Instance BoolCat : Category := {|
  object := bool:Type;
  morphism a b := match a,b with true,false => Empty_set | _,_ => unit end:Type;
  id := $( intros []; exact tt )$;
  composition := $( intros [] [] [] [] []; exact tt)$
|}.
Proof.
  all: repeat intros []; reflexivity.
Defined.

Instance boolTerminal : @Terminal BoolCat := {|
  terminal := true:@object BoolCat;
  receivesAll := $( intros []; exact tt )$
|}.
Proof.
  repeat intros []; reflexivity.
Defined.

Definition boolInitial : @Initial BoolCat.
refine {|
  terminal := false:@object (co BoolCat);
  receivesAll := $( intros []; exact tt )$
|}.
Proof.
  repeat intros []; reflexivity.
Defined.

Instance allTerminalsIso `{C:Category} (t t':Terminal) : @terminal _ t ≈ @terminal _ t'.
  refine {|
    f := receivesAll terminal;
    g := receivesAll terminal
  |}.
  - match goal with |- ?H = _ => generalize H; intros h end.
    specialize (@receivesAllUnique _ t _ id).
    specialize (@receivesAllUnique _ t _ h).
    congruence.
  - match goal with |- ?H = _ => generalize H; intros h end.
    specialize (@receivesAllUnique _ t' _ id).
    specialize (@receivesAllUnique _ t' _ h).
    congruence.
Defined.

(* dualityPrinciple, should be formalized *)
Instance allInitialsIso `{C:Category} (t t':Initial) : @terminal _ t ≈ @terminal _ t'.
  apply allTerminalsIso.
Defined.

Lemma allTerminalsIsoUnique `{C:Category} (t t':@Terminal C) 
                             (i:@terminal _ t ≈ @terminal _ t')
                             (j:@terminal _ t ≈ @terminal _ t') : i = j.
  destruct i as [fi gi]. 
  destruct j as [fj gj].
  f_equal.
  - intros; subst.
    f_equal; apply proof_irrelevance.
  - specialize (@receivesAllUnique _ _ _ fj).
    specialize (@receivesAllUnique _ _ _ fi).
    congruence.
  - specialize (@receivesAllUnique _ _ _ gj).
    specialize (@receivesAllUnique _ _ _ gi).
    congruence.
Qed. 

