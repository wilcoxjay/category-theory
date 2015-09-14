Require FunctionalExtensionality.
Require ProofIrrelevance.
Require Import Program.
Require Import List.
Require Import Equality.
Import EqNotations.
Require Import Arith.

Module Category.
Polymorphic Class Category := {
  object : Type;
  morphism : object -> object -> Type;
  id {A} : morphism A A;
  (* note that composition is defined "the right way" where f ∘ g = \a. g (f a) *)
  composition {A B C} : morphism A B -> morphism B C -> morphism A C;
  leftId {A B} {f:morphism A B} : composition id f = f;
  rightId {A B} {f:morphism A B} : composition f id = f;
  assoc {A B C D} {f:morphism A B} {g:morphism B C} {h:morphism C D} : composition (composition f g) h = composition f (composition g h)
}.
End Category.
Import Category.

Notation "A → B" := (morphism A B) (at level 45).
Notation "f ∘ g" := (composition f g).

Instance Coq : Category := {|
  object := Type;
  morphism A B := A -> B;
  id A a := a;
  composition A B C f g a := g (f a)
|}.
Proof.
  all: intros; reflexivity.
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

Module Monad.
Class Monad (T:Type->Type) := {
  bind {A} {B} : T A -> (A -> T B) -> T B;
  pure {A} : A -> T A;
  leftId {A B a} {f:A->T B} : bind (pure a) f = f a;
  rightId {A} {v:T A} : bind v pure = v;
  assoc {A B C} {v} {f:A->T B} {g:B->T C} : bind (bind v f) g = bind v (fun a => bind (f a) g)
}.
End Monad.
Import Monad.

Instance KleisliCategory T `{Monad T} : Category := {|
  object := Type;
  morphism A B := A -> T B;
  id A := pure;
  composition A B C f g a := bind (f a) g
|}.
Proof.
  - intros.
    extensionality a.
    apply leftId.
  - intros.
    extensionality a.
    apply rightId.
  - intros.
    extensionality a.
    apply assoc.
Defined.      

Module Functor.
Class Functor (C D:Category) := {
  fobj : @object C -> @object D;
  fmap {a b} : (a → b) -> (fobj a → fobj b);
  mapId {a} : fmap (@id C a) = id;
  mapCompose {a b c} {f:a → b} {g:b → c} : fmap (f ∘ g) = fmap f ∘ fmap g
}.
End Functor.
Import Functor.

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

Module InfinityGroupoidExperiment.

Variable A : Type.

Section InfinityGroupoidExperiment.

Variable x y : A.
Variable p q : x = y.
Variable r s : p = q.

Definition eq0 := A.
Definition eq1 x y := @eq eq0 x y.
Definition eq2 x y p q := @eq (eq1 x y) p q.
Definition eq3 x y p q r s := @eq (eq2 x y p q) r s.

End InfinityGroupoidExperiment.

Compute eq0.
Compute eq1.
Compute eq2.
Compute eq3.
(*
eq0  = A
     : Type

eq1  = fun x y : eq0 => x = y
     : eq0 -> eq0 -> Prop

eq2  = fun (x y : eq0) (p q : eq1 x y) => p = q
     : forall x y : eq0, eq1 x y -> eq1 x y -> Prop

eq3  = fun (x y : eq0) (p q : eq1 x y) (r s : eq2 x y p q) => r = s
     : forall (x y : eq0) (p q : eq1 x y), eq2 x y p q -> eq2 x y p q -> Prop
*)

End InfinityGroupoidExperiment.

Module Terminal.
Class Terminal `{Category} := {
  terminal : object;
  receivesAll o : o → terminal;
  receivesAllUnique {o f} : receivesAll o = f
}.
End Terminal.
Import Terminal.

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

Module Isomorphism.
Class Isomorphism `{Category} (a b:object):= {
  f : a → b;
  g : b → a;
  fgCompose : f ∘ g = id;
  gfCompose : g ∘ f = id
}.
End Isomorphism.
Import Isomorphism.

Notation "a ≈ b" := (Isomorphism a b) (at level 45).

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

Definition bijection := @Isomorphism Coq.

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

Instance One : Category := {|
  object := unit;
  morphism a b := unit;
  id a := tt;
  composition a b c f g := tt
|}.
Proof.
  all: repeat intros []; reflexivity.
Defined.

Instance Two : Category := {|
  object := bool;
  morphism a b := match a,b with 
                  | true,true => unit
                  | false,false => unit
                  | _,_ => Empty_set
                  end;
  id := $(intros []; exact tt)$;
  composition := $(intros [] [] [] [] []; exact tt)$
|}.
Proof.  
  all: repeat intros []; reflexivity.
Defined.

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

Instance ConstFunctor (C D:Category) (o:@object D) : Functor C D := {|
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
  exists nat nat 0.
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

Module Product.
Class Product `{Category} := {
  prod : object -> object -> object;
  factorizer {a b c:object} (p:c → a) (q:c → b) : c → prod a b;
  fst {a b:object} : prod a b → a;
  snd {a b:object} : prod a b → b;
  fstOk {a b c} {p:c → a} {q:c → b} : factorizer p q ∘ fst = p;
  sndOk {a b c} {p:c → a} {q:c → b} : factorizer p q ∘ snd = q;
  pairUnique {a b c} {p:c → a} {q:c → b} f : 
    f p q ∘ fst = p -> f p q ∘ snd = q -> f p q = factorizer p q
}.
End Product.
Import Product.

Instance prodIsProduct : @Product Coq := {|
  prod := Datatypes.prod : @object Coq -> @object Coq -> @object Coq;
  factorizer a b c p q x := (p x, q x);
  fst := @Datatypes.fst;
  snd := @Datatypes.snd
|}.
Proof.  
  - compute.
    intros.
    extensionality x.
    reflexivity.
  - compute.
    intros.
    extensionality x.
    reflexivity.
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
    prod := sum : @object (co Coq) -> @object (co Coq) -> @object (co Coq);
    factorizer a b c p q x := match x with inl a => p a | inr b => q b end;
    fst := @inl;
    snd := @inr
  |}.
  - compute. 
    intros.
    extensionality x.
    reflexivity.
  - compute. 
    intros.
    extensionality x.
    reflexivity.
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
