Set Universe Polymorphism.

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
