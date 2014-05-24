Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.CoFunctor.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Global Instance proper_id (T : Type) {tT : type T} : proper (fun x => x).
Proof.
  repeat red; intros. apply H.
Qed.


Section functors.
  Variable A : Type.

  Local Instance Functor_Fun : Functor (Fun A) :=
    mkFunctor (Fun A) (fun _A _B g f x => g (f x)).

  Local Instance CoFunctor_Fun T : CoFunctor (fun x => x -> T) :=
    mkCoFunctor (fun x => x -> T)
                (fun _ _ g f => fun x => f (g x)).

  Local Instance Functor_functor F G (fF : Functor F) (fG : Functor G)
  : Functor (fun x => F (G x)) :=
    mkFunctor (fun x => F (G x))
              (fun _ _ g => @fmap F _ _ _ (@fmap G _ _ _ g)).

  Local Instance CoFunctor_functor F G (fF : Functor F) (fG : CoFunctor G)
  : CoFunctor (fun x => F (G x)) :=
    mkCoFunctor (fun x => F (G x))
                (fun _ _ g => @fmap F _ _ _ (@cofmap G _ _ _ g)).

  Local Instance Functor_cofunctor F G (fF : CoFunctor F) (fG : Functor G)
  : CoFunctor (fun x => F (G x)) :=
    mkCoFunctor _
                (fun _ _ g => @cofmap F _ _ _ (@fmap G _ _ _ g)).

  Local Instance CoFunctor_cofunctor F G (fF : CoFunctor F) (fG : CoFunctor G)
  : Functor (fun x => F (G x)) :=
    mkFunctor _
              (fun _ _ g => @cofmap F _ _ _ (@cofmap G _ _ _ g)).

End functors.

Definition Monoid_compose T : Monoid (T -> T) :=
{| monoid_plus g f x := g (f x)
 ; monoid_unit x := x
|}.

Export PreFun.
