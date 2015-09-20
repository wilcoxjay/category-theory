Require FunctionalExtensionality.
Require ProofIrrelevance.
Require Import Program.
Require Import List.
Require Import Equality.
Import EqNotations.
Require Import Arith.
Import ListNotations.
Require Import ZArith.
Require Import Misc.
Require Import JamesTactics.
Require Import Enumerable.
Require Import Monad.
Require Import ListEx.
Require Import EqDec.
Require Import CpdtTactics.
Require Import Graph.
Require Import Category.
Require Import Coq.
Require Import Co.
Require Import Diagram.
Require Import String.
Require Import Ascii.

Set Universe Polymorphism.

Section Parse.

Context `{Category}.

Inductive Direction := north | east | south | west.

Instance enumerableDirection : enumerable Direction :=
  {| enumerate := [west; south; east; north] |}.
Proof.
  intros []; intuition.
Defined.

Instance eqDecDirection : eqDec Direction.
  constructor.
  decide equality.
Defined.

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

Definition points (w h:nat) (m:(Z*Z)->ascii) : list (Z*Z).
  refine (y <- seq 0 h;; _).
  refine (x <- seq 0 w;; _).
  refine (let x' := Z.of_nat x in let y' := Z.of_nat y in _). 
  refine (if m (x',y') =? "o" % char then ret (x',y') else []).
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

End Parse.
