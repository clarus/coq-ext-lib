Set Implicit Arguments.
Set Strict Implicit.

Section category.
  Variable T : Type.

  Class Category : Type :=
  { mor : T -> T -> Type
  ; compose : forall T U V, mor U V -> mor T U -> mor T V
  ; id : forall A, mor A A
  }.

  Variable C : Category.

  Class CategoryLaws : Type :=
  { mor_equal : forall A B, mor A B -> mor A B -> Prop
  }.
End category.

(** [Type] forms a category with arrows **)
Instance Category_Type : Category Type :=
{ mor := fun x y => x -> y
; compose := fun _ _ _ f g x => f (g x)
; id := fun _ => fun x => x
}.

(** [Type] forms a category with relations **)
Definition Category_Iso : Category Type :=
{| mor := fun x y => x -> y -> Prop
 ; compose := fun _ _ _ f g a b =>
                exists y, g a y /\ f y b
 ; id := fun T => @eq T
 |}.

Definition Category_op T (C : Category T) : Category T :=
{| mor := fun x y => mor y x
 ; compose := fun _ _ _ f g => @compose _ C _ _ _ g f
 ; id := fun _a => id _a
 |}.