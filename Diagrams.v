Require FunctionalExtensionality.
Require ProofIrrelevance.
Require Import Program.
Require Import List.
Require Import Equality.
Import EqNotations.
Require Import Arith.
Require Import Misc.
Require Import JamesTactics.
Require Import Enumerable.
Require Import Monad.
Require Import ListEx.
Require Import EqDec.
Require Import CpdtTactics.
Import ListNotations.
Require Import ZArith.

Fixpoint findIndecies {A} `{eqDec A} (a:A) (l:list A) : list (ListEx.index l) :=
  match l with
  | [] => []
  | a'::l' => (if a =? a' then cons found else id) (@next _ _ _ <$> (findIndecies a l'))
  end.

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

Instance co `(Category) : Category := {|
  object := object;
  morphism a b := morphism b a;
  id a := id;
  composition a b c f g := g ∘ f
|}.
Proof.
  - intros.
    apply rightId.
  - intros.
    apply leftId.
  - intros.
    symmetry.
    apply assoc.
Defined.

End Category.
Import Category.

Module Graph.
Section Graph.

Class Graph := {
  Vertex : Type;
  Edge : Vertex -> Vertex -> Type
}.

Context `{Graph}.

Inductive Path : Vertex -> Vertex -> Type :=
| refl {a} : Path a a
| step  {a b c} : Edge a b -> Path b c -> Path a c.

End Graph.
End Graph.
Import Graph.

Module Diagram.
Section Diagram.

Context `{Category}.

Class Diagram := {
  Vertex : Type;
  vertexObject : Vertex -> object;
  Arrow : Vertex -> Vertex -> Type;
  arrowMorphism {a b} : Arrow a b -> (vertexObject a) → (vertexObject b)
}.

Variable D:Diagram.
Context `{eqDec Vertex}.
Context `{enumerable Vertex}.
Context `{forall v v', enumerable (Arrow v v')}.

Instance diagramGraph : Graph := {| 
  Graph.Vertex := Vertex;
  Graph.Edge := Arrow
|}.

Definition vertices := @enumerate Vertex _.
Definition edges v v' := @enumerate (Edge v v') _.

Fixpoint composePath {s d} (p:Path s d) : vertexObject s → vertexObject d :=
  match p in Path s d return vertexObject s → vertexObject d with
  | refl => id
  | step a p' => arrowMorphism a ∘ composePath p'
  end.

Definition listPaths s : list {d : Vertex & Path s d}.
  refine ((fix rec fuel := match fuel
  return forall v, list {d : Vertex & Path v d} with
  | 0 => fun _ => []
  | S fuel => fun v => _
  end) (List.length vertices) s).
  clear s.
  refine ([v & refl]::_).
  refine (d <- vertices;; _).
  refine (e <- edges v d;; _).
  refine (P <- rec fuel d;; _).
  refine (ret [projT1 P & step e (projT2 P)]).
Defined.

Definition groupBy {A C} `{eqDec A} `{enumerable A} {B:A->Type} (l:list (sigT B)) (f:forall a:A, list (B a) -> C) : list C.
  refine (a <- enumerate;; _).
  refine (ret (f a _)).
  refine (e <- l;; _).
  destruct e as [a' b].
  refine (if a =? a' then ret _ else []).
  subst.
  exact b.
Defined.

Definition nonsymmetricNonreflexiveCrossproduct {A} (l:list A) : list (A * A).
  refine ((fix rec l :=
    match l with
    | [] => []
    | a::l' => _ ++ rec l'
    end) l).
  refine ((fix rec' l :=
    match l with
    | [] => []
    | a'::l' => (a,a') :: rec' l'
    end) l').
Defined.

Definition denoteDiagram : Prop.
  refine ((fix rec (l:list Prop) := match l with
    | [] => True
    | [h] => h
    | h::l' => h /\ rec l'
    end) _).
  refine (v <- @enumerate Vertex _;; _).
  refine (concat (groupBy (listPaths v) (fun v' ps => _))).
  refine (_ <$> nonsymmetricNonreflexiveCrossproduct ps).
  intros [P Q].
  refine (composePath P = composePath Q).
Defined.

Lemma denoteDiagramCommutative : denoteDiagram <-> forall s d (P Q:Path s d), composePath P = composePath Q.
Admitted.

End Diagram.
End Diagram.
Import Diagram.

Module Direction.
Inductive Direction := north | east | south | west.
End Direction.
Import Direction.

Module Product.
Section Product.

Context `{Category}.

Section ProductDiagram.

Variable c a prod b:object.
Variable p:c → a.
Variable pair : c → prod.
Variable q:c → b.
Variable fst : prod → a.
Variable snd : prod → b.

Definition objects := [a; b; c; prod].
Definition Vertex := index objects.

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

Definition section {A} `{eqDec A} {B:A->A->Type} (l:list {s:A & {d:A & B s d}}) (s d:A) : list (B s d).
  refine (v <- l;; _).
  destruct v as [s' [d' v]].
  refine (match (s, d) =? (s', d') with
  | left e => ret _
  | right _ => []
  end).
  inversion e.
  subst.
  exact v.
Defined.

Instance prodDiagram : Diagram := {|
  Diagram.Vertex := Vertex;
  vertexObject := lookup;
  Arrow s d := index (section arrows s d);
  arrowMorphism x y := lookup
|}.

Definition denoteProdDiagram := denoteDiagram prodDiagram.

End ProductDiagram.

Section ProductImage.

Require Import String.
Require Import Ascii.

Definition Z_to_nat (z:Z) : option nat :=
  match z with
  | 0%Z => Some 0
  | Z.pos p => Some (Pos.to_nat p)
  | Z.neg _ => None
  end.

Definition imgMap (img:list string) (x:Z*Z) : ascii. 
  destruct x as [x y].
  destruct (Z_to_nat x) as [x'|]; [|exact " "%char].
  destruct (Z_to_nat y) as [y'|]; [|exact " "%char].
  refine (let s := nth y' img " "%string in _). 
  destruct (get x' s) as [cc|]; [|exact " "%char].
  exact cc.
Defined.

Instance eqDecAscii : eqDec ascii.
  constructor.
  apply ascii_dec.
Defined.

Definition points (w h:nat) (m:(Z*Z)->ascii) : list (Z*Z).
  refine (y <- seq 0 h;; _).
  refine (x <- seq 0 w;; _).
  refine (let x' := Z.of_nat x in let y' := Z.of_nat y in _). 
  refine (if m (x',y') =? "o" % char then ret (x',y') else []).
Defined.

Instance enumerableDirection : enumerable Direction :=
  {| enumerate := [west; south; east; north] |}.
Proof.
  intros []; intuition.
Defined.

Definition directionEdgeChar d :=
  match d with
  | north => "|"
  | east => "-"
  | south => "|"
  | west => "-"
  end % char.

Definition directionEdgeEndChar d :=
  match d with
  | north => "^"
  | east => ">"
  | south => "v"
  | west => "<"
  end % char.

Definition directionMove (d:Direction) (x:Z*Z) : Z*Z.
  destruct x as [x y].
  exact match d with
  | north => (x, Z.pred y)
  | east => (Z.succ x, y)
  | south => (x, Z.succ y)
  | west => (Z.pred x, y)
  end.
Defined.

Definition directionFlip (d:Direction) : Direction :=
  match d with
  | north => south
  | east => west
  | south => north
  | west => east
  end.

Instance eqDecDirection : eqDec Direction.
  constructor.
  decide equality.
Defined.

Fixpoint traceEdges (fuel:nat) (m:(Z*Z)->ascii) (ps:list (Z*Z)) {struct fuel} : list ((Z*Z)*(Z*Z)).
  refine (s <- ps;; _).
  refine (d <- @enumerate Direction _;; _).
  refine (_ fuel (directionMove d s) d).
  clear d fuel.
  refine (fix rec fuel x d :=
    match fuel with
    | 0 => []
    | S fuel' => _
    end).
  specialize (rec fuel').
  refine (if m x =? "+"%char then _ else _).
  - refine (d' <- @enumerate Direction _;; _).
    refine (if directionFlip d =? d' then [] else _).
    exact (rec (directionMove d' x) d').
  - refine (if m x =? directionEdgeChar d then _ else
            if m x =? directionEdgeEndChar d then _ else []).
    + exact (rec (directionMove d x) d).
    + exact (ret (s,directionMove d x)).
Defined.

Definition img : list string := [
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

Instance eqDecZ : eqDec Z.
  constructor.
  decide equality;
  decide equality.
Defined.

Existing Instance eqDecProd.

Definition parseImage (img:list string) : list (Z*Z) * list ((Z*Z)*(Z*Z)).
  refine (let m := imgMap img in _).
  refine (let h := List.length img in _).
  refine (let w := String.length (nth 0 img " "%string) in _).
  refine (let ps := points w h m in _).
  refine (let es := traceEdges (w*h) m ps in _).
  refine (ps, es).
Defined.

Definition parseDiagramType (img:list string) : Type.
  destruct (parseImage img) as [ps es].
  revert ps.
  refine ((fix rec os (om:(Z*Z) -> option (ListEx.index os)) ps := 
    match ps with
    | [] => _
    | x::ps' => forall o:object, rec (o::os) _ ps'
    end) [] (fun _ => None)); revgoals. 
  {
    refine (fun x' => if x =? x' then Some found else (om x') >>= _).
    exact (fun oi => Some (next oi)).
  }
  clear rec ps.
  revert es.
  refine (fix rec es := 
    match es with
    | [] => Diagram
    | (s,d)::es' => (fun T => _) (rec es')
    end).
  destruct (om s) as [si|]; [|exact T].
  destruct (om d) as [di|]; [|exact T].
  refine (forall m : lookup si → lookup di, T).
Defined.

Definition parseDiagram (img:list string) : parseDiagramType img.
  unfold parseDiagramType.
  destruct (parseImage img) as [ps es].
  match goal with |- _ ?os ?om ?ps => revert ps; generalize om; generalize os end.
  refine (fix rec os om ps {struct ps} := 
    match ps with
    | [] => _
    | x::ps' => _
    end); revgoals. {
    refine (fun o:object => rec _ _ _).
  }
  clear rec ps.
  revert es.
  refine ((fix rec (ms:list {s:ListEx.index os & {d:ListEx.index os & lookup s → lookup d}}) es {struct es} := 
    match es with
    | [] => _
    | (s,d)::es' => _
    end) []); revgoals. {
    destruct (om s) as [si|]; [|exact (rec ms es')].
    destruct (om d) as [di|]; [|exact (rec ms es')].
    refine (fun m => rec ([si & [di & m]]::ms) es').
  }
  clear rec es om.
  refine {|
    Diagram.Vertex := ListEx.index os;
    vertexObject := lookup;
    Arrow s d := ListEx.index (section ms s d);
    arrowMorphism x y := lookup
  |}.
Defined.

Goal True.
  refine (let ps := points 20 20 (imgMap img) in _).  
  compute in ps.
  refine (let r := parseImage img in _).  
  compute in r.
Abort.

End ProductImage.

Class Product := {
  prod : object -> object -> object;
  pair {a b c:object} (p:c → a) (q:c → b) : c → prod a b;
  fst {a b:object} : prod a b → a;
  snd {a b:object} : prod a b → b;
  productOk {a b c} {p:c → a} {q:c → b} : denoteDiagram (parseDiagram img (* denoteProdDiagram *) c a (prod a b) b p (pair p q) q fst snd);
  pairUnique {a b c} {p:c → a} {q:c → b} f :
    f p q ∘ fst = p -> f p q ∘ snd = q -> f p q = pair p q
}.

End Product.

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
    prod := sum : @object (co Coq) -> @object (co Coq) -> @object (co Coq);
    pair a b c p q x := match x with inl a => p a | inr b => q b end;
    fst := @inl;
    snd := @inr
  |}.
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

End Product.
