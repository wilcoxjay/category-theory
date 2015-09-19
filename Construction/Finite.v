Require Import Category.

Set Universe Polymorphism.

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
