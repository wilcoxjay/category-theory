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

Require Import JamesTactics.
Require Import Omega.

Set Universe Polymorphism.

Definition acyclic (G : Graph) : Prop := forall v (p : Path v v), p = refl.

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

Fixpoint all_list (l : list Prop) : Prop :=
  match l with
  | [] => True
  | [h] => h
  | h::l' => h /\ all_list l'
  end.

Fixpoint pathLength {s d} (p : Path s d) {struct p} : nat :=
   match p with
   | refl => O
   | step e p' => S (pathLength p')
   end.

Fixpoint pathEnumEq (n : nat) s {struct n} : list {d : Vertex & Path s d} :=
  match n with
  | O => ret [s & refl]
  | S n' => (m <- @enumerate Vertex _ ;;
             e <- @enumerate (Arrow s m) _ ;;
             p' <- pathEnumEq n' m ;;
             ret [projT1 p' & step e (projT2 p')])
  end.

Lemma pathEnumEq_complete :
  forall s d (p : Path s d),
    In [d & p] (pathEnumEq (pathLength p) s).
Proof.
  intros.
  remember (pathLength p) as n. generalize dependent s. generalize dependent d.
  induction n; intros; destruct p; simpl in *.
  - auto.
  - discriminate.
  - discriminate.
  - eapply concatIn; [|apply in_map with (x := b); apply enumerateContainsEverything].
    eapply concatIn; [|apply in_map with (x := e); apply enumerateContainsEverything].
    eapply concatIn; [|apply in_map with (x := [c & p])].
    + simpl. auto.
    + auto.
Qed.

Fixpoint pathEnumLe (n : nat) s {struct n} : list {d : Vertex & Path s d} :=
  pathEnumEq n s ++
  match n with
  | O => []
  | S n' => pathEnumLe n' s
  end.

Lemma pathEnumLe_cumulative :
  forall m n,
    n <= m ->
    forall s p,
    In p (pathEnumLe n s) ->
    In p (pathEnumLe m s).
Proof.
  induction 1.
  - auto.
  - intros. simpl. apply in_or_app. right. auto.
Qed.

Lemma pathEnumLe_includes_pathEnumEq :
  forall n s p,
    In p (pathEnumEq n s) ->
    In p (pathEnumLe n s).
Proof.
  unfold pathEnumLe; intros; destruct n; simpl in *; auto.
  apply in_or_app. left. auto.
Qed.

Lemma pathEnumLe_complete :
  forall n s d (p : Path s d),
    pathLength p <= n ->
    In [d & p] (pathEnumLe n s).
Proof.
  intros.
  apply pathEnumLe_cumulative with (n := pathLength p); auto.
  apply pathEnumLe_includes_pathEnumEq.
  apply pathEnumEq_complete.
Qed.

Definition denote : Prop.
  refine (all_list _).
  refine (v <- @enumerate Vertex _;; _).
  refine (concat (groupBy (listPaths v) (fun v' ps => _))).
  refine (_ <$> nonsymmetricNonreflexiveCrossproduct ps).
  intros [P Q].
  refine (composePath P = composePath Q).
Defined.

Lemma denoteDiagramCommutative : denote <-> forall s d (P Q:Path s d), composePath P = composePath Q.
Admitted.

End Diagram.

