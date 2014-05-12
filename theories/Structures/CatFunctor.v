Require Import ExtLib.Structures.Cat.

Set Implicit Arguments.
Set Strict Implicit.

Section catfunctor.
  Variable Cat_T : Category Type.

  Variable F : Type -> Type.

  Class CatFunctor : Type := mkCatFunctor
  { cmap : forall A B, (mor A B) -> mor (F A) (F B) }.

(*
  Class CatFunctorLaws (GF : CatFunctor) : Type :=
  { cmap_compose : forall A B C,
    forall (f : @mor _ Cat_T A B) (g : @mor _ Cat_T B C),
    @mor_equal _ Cat_T _ _
               (@cmap GF A C (@compose _ Cat_T _ _ _ g f))
               (@compose _ Cat_T _ _ _ (cmap _ _ g) (cmap _ _ f))
  ; cmap_id : forall T,
    mor_equal (cmap (id T)) (@id (F T))
    (** NOTE:
     ** - The [properness] of [cmap] is really encapsulated by what
     **   it means to be an [mor]
     ** - Naively an [mor] is an arrow that respects all the
     **   desired properties
     ** - This gets to the intrinsic vs. extrinsic representation.
     **)
  }.
*)

End catfunctor.
