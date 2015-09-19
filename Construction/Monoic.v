Require Import FunctionalExtensionality.
Require Import Program.
Require Import Category.
Require Import Coq.
Require Import Co.

Set Universe Polymorphism.

Definition monoic (C:Category) {a b} (m:b → a) := forall {c} {f g:c → b}, f ∘ m = g ∘ m -> f = g.

Definition epi (C:Category) {a b} (m:a → b) := forall {c} {f g:b → c}, m ∘ f = m ∘ g -> f = g.

Definition epiIsCoMonoic : forall C, @epi C = @monoic (co C).
  unfold epi, monoic.
  cbn.
  reflexivity.
Defined.  

Definition idMonoic {A} : monoic Coq (fun a:A=>a).
  compute in *.
  intros ? f g ?.
  rewrite (eta_expansion f).
  rewrite (eta_expansion g).
  trivial.
Defined.

Definition constNotMonoic : exists A B (b:B), ~monoic Coq (fun _:A => b).
  exists nat.
  exists nat.
  exists 0.
  compute.
  intro h.
  specialize (h nat S (const 0) eq_refl).
  compute in *.
  specialize (equal_f h 0).
  congruence.
Defined.

Definition injectiveIsMonoic {A B} {i:A->B} : (forall a a', i a = i a' -> a = a') <-> monoic Coq i.
  compute.
  constructor.
  - intros h ? f g h'.
    extensionality x.
    specialize (equal_f h' x); intro h''.
    specialize (h (f x) (g x)).
    intuition.
  - intros h a a' h'.
    specialize (h A (const a) (const a')).
    compute in *.
    refine ((fun h'' => equal_f h'' a) (h _)). 
    extensionality x.
    apply h'.
Defined.

Require Import Classical_Pred_Type.
Require ClassicalFacts.
Axiom prop_ext : ClassicalFacts.prop_extensionality.

Definition surjectiveIsEpi {A B} {s:A->B} : (forall b, exists a, s a = b) <-> epi Coq s.
  compute.
  constructor.
  - intros h ? f g h'.
    extensionality x.
    specialize (equal_f h'); intro h''.
    destruct (h x) as [x' h'''].
    clear h h'.
    specialize (h'' x').
    rewrite h''' in *.
    apply h''.
  - intros h.
    apply not_ex_not_all.
    intros [b h'].
    specialize (not_ex_all_not _ _ h'); clear h'; intro h'.
    specialize (h Prop (fun b' => b' = b) (fun _ => False)).
    compute in *.
    refine ((fun h'' => _) (h _)). {
      specialize (equal_f h'' b); clear h''; intro h''.
      rewrite <- h''.
      reflexivity.
    }
    clear h. 
    extensionality x.
    specialize (h' x).
    apply prop_ext.
    intuition.
Defined.
