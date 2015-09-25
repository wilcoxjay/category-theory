I defined my product diagram as:

diagram : Diagram := {|
  Node := index [a, b, c, ...]
  Edge := fun v v' => ...
|}

In the `Edge` in enumerated over a list of edges and checked whether the start and end in the list were equal to `v` and `v'` respectively. Unfortunately, calling `compute` on anything that somehow dealt with `diagram`, even if it was just in the type, started unfolding the entire `Edge` function! You can imagine how large the function is unfolded given that it refers to two lists with a considerable amount of elements, and then compares them using `=?` (a function that does tons of dependent pattern matches). Turns out that almost all of Coq's computation tactics reduce terms under binders, except `hnf`!

    Goal (fun (_:nat) => 5 + 2) = (fun (_:nat) => 7).
      cbn.
    Restart.
      lazy.
    Restart.
      hnf.
    Restart.
      compute.
    Restart.
      vm_compute.
    Restart.
      reflexivity.
    Qed.

