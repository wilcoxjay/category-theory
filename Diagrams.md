---
content_type: md
layout: main
header_style: max-height:50px;
click: download('/')
title: Konstantin Weitz
comments: true
info:
---

Fully Formal Pictorial Definitions for Category Theory
------------------------------------------------------

Pictorial definitions and proofs are essential in conveying mathematics ([empirical evidence][STUDY]). Unfortunately, the definitions and proofs written in proof assistants are all-too formulaic and thus harder to understand. This blog post changes this situation, by formalizing commutative diagrams for category theory in Coq.

<!-- more -->

The standard introduction to category theory, Mac Lane's "Categories for the Working Mathematician", motivates category theory with:

> Category theory starts with the observation that many properties ... can be unified and simplified by a presentation with diagrams of arrows [commutative diagrams].

However, despite this emphasis on diagrams and the [sheer endless list][LIST] of formalizations of category theory in proof assistants, formalizations of category theory in proof assistants do not support commutative diagrams.

This blog post shows how to formalize commutative diagrams in Coq. Let's jump right in. Following is a pictorial definition of a category theoretical `Product` in Coq (not that the arguments of `∘` are reversed from it's usual mathematical definition). You can downloaded the entire code from GitHub.

    Class Product `{Category} := {
      bundle : object -> object -> object;
      factor {a b c:object} (p:c → a) (q:c → b) : c → bundle a b;
      projL {a b:object} : bundle a b → a;
      projR {a b:object} : bundle a b → b;
      productOk {a b c} {p:c → a} {q:c → b} : denote (parse ([
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
        ] % string) c a (bundle a b) b p (factor p q) q projL projR);
      pairUnique {a b c} {p:c → a} {q:c → b} f : 
        f p q ∘ projL = p -> f p q ∘ projR = q -> f p q = factor p q
    }.

Unfortunately, I won't be able to satisfactorily explain the category theory used in this post. But there are many sources out there that explain it well, e.g. Milewski's [Category Theory for Programmers blog][MILEWSKI].

Trust me, that everything seems standard, except the `productOk` field. It takes the ascii-art representation of a commutative diagram and passes it to the `parse` function along with a ton of objects and morphism. The result is then passed to the `denote` function.

I'll explain how this works in more detail later, but for now I'll given an example of how to use it. Let's prove that the inductively defined product in the Coq standard library, is indeed a product in the `Coq` category.

    Instance prodIsProduct : @Product Coq := {|
      bundle := prod : @object Coq -> @object Coq -> @object Coq;
      factor a b c p q x := pair (p x) (q x);
      projL := fst;
      projR := snd
    |}.

Next, we have to prove `productOk`. Our initial goals is (to nobodies surprise):

    forall (a b c : object) {p:c → a} {q:c → b} : denote (parse ([
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
        ] % string) c a (bundle a b) b p (factor p q) q projL projR);

Now how do we prove this? First we introduce the variables, and then we actually run the diagram parser and denote the result, meanwhile taking care not to expand any definitions particular to `prod` or the `Coq` category.

      Opaque morphism object composition id fst snd.
      intros.
      compute.

The resulting goal is:

    q ∘ id = (fun x : c => pair (p x) (q x)) ∘ snd ∘ id) /\
    (fun x : c => pair (p x) (q x)) ∘ fst ∘ id = p ∘ id

Pretty close (and certainly identical in meaning) to what you would expect the definition to be like if written as a formula, namely:

    (fun x : c => pair (p x) (q x)) ∘ snd = q /\
    (fun x : c => pair (p x) (q x)) ∘ fst = p

And this should be no problem to prove.

The rest of this post first explains the `parse` function that turns the pictorial representation of the diagram into the internal representation, and asks for the right number and type of objects and morphism. And then the `denote` function that turns an internal representation of the diagram into a Coq formula.

### Parsing

The ultimate goal of the parsing is to turn the ascii-art image into a Diagram, as defined below:

    Class Diagram `{Category} := {
      Vertex : Type;
      vertexObject : Vertex -> object;
      Arrow : Vertex -> Vertex -> Type;
      arrowMorphism {a b} : Arrow a b -> (vertexObject a) → (vertexObject b)
    }.

A `Diagram` consists of a set of vertexes, a set of arrows between any two vertexes, and two functions that map vertexes and arrows to objects and morphisms in a given category.

The first step toward this goal is to find all vertexes of the image, along with the start and end point of each edge. The function that does this has the following type `parseImage (img:list string) : list (Z*Z) * list ((Z*Z)*(Z*Z))`. There parser is pretty boring, as it is completely unverified. Note that all the text on the image (e.g. `a`, `b`, `bundle`) is just commentary. Can you guess why the comments don't contains `o`s?

The next step is to map the vertexes and arrows to objects and morphisms. We do that by asking the caller of the `parse` function to pass an object for each object, and a morphism for each arrow --- i.e. the number of arguments to the function depends on the image! Consequently, the `parse` function is a dependently typed hell! Let's start with its type `parseType`:

    Definition parseDiagramType (img:list string) : Type.

We first parse the image, resulting in a list of vertexes `ps` and a list of arrows `es`. 

      destruct (parseImage img) as [ps es].

Next, we iterate over the vertexes `ps`. For every vertex in `ps`, we add an additional function argument `forall o:object, _`.

      
      revert ps.
      refine ((fix rec os (om:(Z*Z) -> option (ListEx.index os)) ps := 
        match ps with
        | [] => _
        | x::ps' => forall o:object, _ 
        end) [] (fun _ => None)); revgoals. 

We also construct two data structures on the way. `os` is the list of objects collected as parameters, and `om` is a function that maps a vertex to the `index` of its corresponding object in `os`. The following code keeps these data structures up to date:

      {
        refine (rec (o::os) _ ps').
        refine (fun x' => if x =? x' then Some found else (om x') >>= _).
        exact (fun oi => Some (next oi)).
      }

One we ran out of vertexes, we ask the user to provide morphisms for each arrow. We do this by iterating over the list of all vertexes `es`.

      clear rec ps.
      revert es.
      refine (fix rec es := 
        match es with
        | [] => Diagram
        | (s,d)::es' => (fun T => _) (rec es')
        end).

For every vertex, we lookup the source `s` and destination `d` in the map from vertexes to objects. If that lookup fails, we fail silently by simply ignoring that arrow. If we succeed, we add another parameter with `forall m : ...`.

      destruct (om s) as [si|]; [|exact T].
      destruct (om d) as [di|]; [|exact T].
      refine (forall m : lookup si → lookup di, T).
    Defined.

Great, we defined the type! Just a quick remark on the order of the arguments passed to the parser. The vertexes in `ps` are ordered from top to bottom, breaking ties from left-to-right. Morphisms are ordered in the order of their source vertex, breaking ties in a circle from left to top. This is depicted for the product example in the following diagram:

![parsing.jpg]

Now to the real parser. 

    Definition parseDiagram (img:list string) : parseDiagramType img.
      unfold parseDiagramType.

The good thing is that the type is already pretty restrictive, so much of the vertex iteration code writes itself (remember that code enclosed in `{` and `}`. That's just an `_` now!):

      destruct (parseImage img) as [ps es].
      match goal with |- _ ?os ?om ?ps => revert ps; generalize om; generalize os end.
      refine (fix rec os om ps {struct ps} := 
        match ps with
        | [] => _
        | x::ps' => _
        end); revgoals. {
        refine (fun o:object => rec _ _ _).
      }

The code for arrows is a bit more complex, because now we actually need to keep track of the morphisms that the users provided us with. We do that in the `ms` data-structure that collects all morphisms, along with the `index` of the morphisms source `s` and destination `d`.

      clear rec ps.
      revert es.
      refine ((fix rec (ms:list {s:ListEx.index os & {d:ListEx.index os & lookup s → lookup d}}) es {struct es} := 
        match es with
        | [] => _
        | (s,d)::es' => _
        end) []); revgoals. 

And this is the code to keep the data-structure up to date. As in the type, we silently ignore arrows whose source or destination isn't a vertex.

      {
        destruct (om s) as [si|]; [|exact (rec ms es')].
        destruct (om d) as [di|]; [|exact (rec ms es')].
        refine (fun m => rec ([si & [di & m]]::ms) es').
      }

Lastly, we use the `os` and `ms` list to build a Diagram. The set of vertexes is simply the set of `index`es into the `os` list. The set of arrows is the set of `index`es into the list of morphisms `ms`, filtered with `section` to only contain morphisms starting at `s` and ending in `d`. Mapping vertexes and arrows is straight forward, we just have to `lookup` the value associated with the index.

      clear rec es om.
      refine {|
        Vertex := ListEx.index os;
        vertexObject := lookup;
        Arrow s d := ListEx.index (section ms s d);
        arrowMorphism x y := lookup
      |}.
    Defined.

### Denotation

Now that we have a `Diagram` we want to denote what it means for it to commute. [Wolfram][WOLF] has the answer (and I'm paraphrasing now):

> A [diagram commutes] if all compositions starting from the same [object] A and ending with the same [object] B give the same result. 

Rigorously, this means that a diagram commutes iff:

    forall s d (P Q:Path s d), composePath P = composePath Q.

Where `Path` is the reflexive transitive closure of the arrows:

    Inductive Path : Vertex -> Vertex -> Type :=
    | refl {a} : Path a a
    | step  {a b c} : Arrow a b -> Path b c -> Path a c.

And `composePath` composes the morphisms along a path:

    Fixpoint composePath {s d} (p:Path s d) : vertexObject s → vertexObject d :=
      match p in Path s d return vertexObject s → vertexObject d with
      | refl => id
      | step a p' => arrowMorphism a ∘ composePath p'
      end.

We have just denoted a diagram into Coq's logic. Unfortunately, this is a pain to work with. But we can do better. For finite, non-cyclic diagrams, we can enumerate all sources, all destinations, and all paths between them `P` and `Q`, and ask the user to prove that every one of these commutes, i.e. the result of this transformation is a possibly long list of conjuncts of the form 
`composePath P = composePath Q`. This is precisely what the `denote` function does.

### Exercises

By which I mean stuff that I haven't had time to do yet, but that I think would be valuable to do. If you solve any of these, please send me a pull request.

- Support diagonal lines, e.g. how slick would the following be:
    
    ["             ";
     "      c      ";
     "      o      ";
     "     /|\     ";
     "    / | \    ";
     "   /  |  \   ";
     "  v   v   v  ";
     "  o<--o---o  ";
     "  a       b  ";
     "             "]

- Proof the that the `denote` function actually does what I claimed it does in this blog post.
- The parser is completely unverified. It would actually be cool to find some declarative way to define the vertexes and edges in the image, and then prove that the parser does the right thing.
- Improve performance.
- Support uniqueness arrows. E.g. the `factor` morphism has to be unique in a product. This is currently done with the field `pairUnique` but it would be cool to combine that into the image. Unique morphisms are usually represented with a dotted line, i.e. something like the following:
 
    ["                       ";
     "     p     c     q     ";
     "  +--------o--------+  ";
     "  |        :        |  ";
     "  |        :factr   |  ";
     "  |        :        |  ";
     "  v        v        v  ";
     "  o<-------o------->o  ";
     "  a      bundle     b  ";
     "                       "]

- Instead of asking the users to pass objects and morphisms as arguments, can we read them directly from the labels in the image? Some Ltac magic might be in order here.
- Somehow pictorial definitions make it easier for humans to do reasoning. Can we use pictorial definitions to make it easier for tactics to do reasoning, i.e. can we use pictorial definitions to improve automation? 

[LIST]: http://mathoverflow.net/questions/152497/formalizations-of-category-theory-in-proof-assistants
[STUDY]: http://www.jstor.org/stable/40248377?seq=1#page_scan_tab_contents
[MILEWSKI]: http://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/
[WOLF]: http://mathworld.wolfram.com/CommutativeDiagram.html

