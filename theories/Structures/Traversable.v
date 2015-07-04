Require Import ExtLib.Structures.Applicative.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class Traversable (T : Type -> Type) : Type :=
{ mapT : forall {F : Type -> Type } {Ap:Applicative F} {A B : Type}, (A -> F B) -> T A -> F (T B) }.

Section traversable.

  Definition sequence {T : Type -> Type} {Tr:Traversable T} {F : Type -> Type} {Ap:Applicative F} {A : Type}
  : T (F A) -> F (T A) := mapT (@id _).
  Definition forT  {T : Type -> Type} {Tr:Traversable T} {F : Type -> Type} {Ap:Applicative F} {A B : Type} (aT:T A) (f:A -> F B) : F (T B) := mapT f aT.
End traversable.
