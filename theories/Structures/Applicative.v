Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class PApplicative (T : Type -> Type) :=
{ AppP : Type -> Type
; ppure : forall {A : Type} {P : AppP A}, A -> T A
; pap : forall {A B : Type} {P : AppP B}, T (A -> B) -> T A -> T B
}.

Class Applicative (T : Type -> Type) :=
{ pure : forall {A : Type}, A -> T A
; ap : forall {A B : Type}, T (A -> B) -> T A -> T B
}.

Module ApplicativeNotation.
  Notation "f <*> x" := (ap f x) (at level 51, right associativity).
End ApplicativeNotation.
Import ApplicativeNotation.

Section applicative.
  Definition liftA {T : Type -> Type} {AT:Applicative T} {A B : Type} (f:A -> B) (aT:T A) : T B := pure f <*> aT.
  Definition liftA2 {T : Type -> Type} {AT:Applicative T} {A B C : Type} (f:A -> B -> C) (aT:T A) (bT:T B) : T C := liftA f aT <*> bT.
End applicative.
