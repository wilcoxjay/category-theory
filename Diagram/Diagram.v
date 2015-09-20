Require Import Enumerable.
Require Import List.
Import ListNotations.
Require Import Monad.
Require Import ListEx.
Require Import EqDec.
Require Import Misc.
Require Import Graph.
Require Import Category.
Require Import Coq.
Require Import Co.

Set Universe Polymorphism.

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

Definition denote : Prop.
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

Lemma denoteDiagramCommutative : denote <-> forall s d (P Q:Path s d), composePath P = composePath Q.
Admitted.

End Diagram.

