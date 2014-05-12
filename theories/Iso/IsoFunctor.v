Require Import ExtLib.Structures.Cat.
Require Import ExtLib.Structures.CatFunctor.
Require Import ExtLib.Iso.Iso.

Set Implicit Arguments.
Set Strict Implicit.

Section IsoFunctor.

  Definition IsoFunctor := @CatFunctor Category_Iso.
  Existing Class IsoFunctor.
  Definition isomap {F : Type -> Type} {IsF : IsoFunctor F}
  : forall A B, Iso A B -> Iso (F A) (F B)
    := @cmap _ _ IsF.
  Definition mkIsoFunctor (F : Type -> Type)
             (isomap : forall A B, Iso A B -> Iso (F A) (F B))
  : IsoFunctor F :=
  {| cmap := isomap |}.

(*
  Definition IsoFunctorOk F (iso : IsoFunctor F) : Type :=
    @GFunctorLaws Iso Iso_compose Iso_ident Iso_equiv _ iso.
*)

End IsoFunctor.
