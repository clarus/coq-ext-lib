Require Import ExtLib.Structures.Cat.
Require Import ExtLib.Data.Fun.

Set Implicit Arguments.
Set Strict Implicit.

(** The idea for this file is to describe computational isomorphisms
 ** - A basic isomorphism is just [Iso A B = A <-> B]
 ** - An equivalence is: [Equiv A B = forall F, F A <-> F B]
 **   - This is great but we need to be able to reason about this
 **     when given different [F]s. The key is to require that it
 **     respects all isomorphisms
 **)

Section Iso.
  Variables A B : Type.

  Class Iso : Type := mkIso
  { into : A -> B
  ; outof : B -> A
  }.

  Class IsoOk (iso : Iso) : Type :=
  { into_outof : forall x, into (outof x) = x
  ; outof_into : forall x, outof (into x) = x
  }.
End Iso.

Arguments into {_ _} {iso} _ : rename.
Arguments outof {_ _} {iso} _ : rename.

Definition Iso_ident T : Iso T T :=
{| into := fun x => x
 ; outof := fun x => x
 |}.

Definition IsoOk_ident T : IsoOk (Iso_ident T).
Proof.
  constructor; reflexivity.
Qed.

Definition Iso_flip A B (i : Iso A B) : Iso B A :=
{| into := outof
 ; outof := into
 |}.

Definition IsoOk_flip A B iso (isoOk : @IsoOk A B iso) : IsoOk (Iso_flip iso).
Proof.
  destruct isoOk; constructor; assumption.
Qed.

Section compose.
  Variables A B C : Type.
  Variable iBC : Iso B C.
  Variable iAB : Iso A B.

  Definition Iso_compose : Iso A C :=
  {| into := compose into into
   ; outof := compose outof outof
   |}.

  Variable iokBC : IsoOk iBC.
  Variable iokAB : IsoOk iAB.

  Definition IsoOk_compose : IsoOk Iso_compose.
  Proof.
    constructor; simpl; unfold compose; simpl; intros; repeat (rewrite outof_into || rewrite into_outof); auto.
  Qed.
End compose.

Definition Iso_equiv (A B : Type) (i1 i2 : Iso A B) : Prop :=
  Iso_compose i1 (Iso_flip i2) = Iso_ident _.

Instance Category_Iso : Category Type :=
{ mor := Iso
; compose := Iso_compose
; id := Iso_ident
}.



(* Section Equiv. *)
(*   Variables A B : Type. *)

(*   Class Equiv : Type := *)
(*     siso : forall (F : Type -> Type), Iso (F A) (F B). *)

(*   Definition sinto (iso : Equiv) (F : Type -> Type) : F A -> F B := *)
(*     @into (F A) (F B) (siso F). *)

(*   Definition soutof (iso : Equiv) (F : Type -> Type) : F B -> F A := *)
(*     @outof (F A) (F B) (siso F). *)

(*   Class EquivOk (SI : Equiv) : Type := *)
(*   { siso_dist :> DistIsoFunc (@siso SI) *)
(*   ; sinto_soutof_Iso : forall F func, @IsoFunctorOk F func -> IsoOk (@siso SI F) *)
(*   }. *)


(* (* *)
(*   Definition IsIdent {T} (f : T -> T) : Prop := *)
(*     forall x, f x = x. *)

(*   Class Respects_IsIdent {T} (F : Type -> Type) (f : (T -> T) -> (F T -> F T)) : Prop := *)
(*   { respects_ident : forall x, IsIdent x -> IsIdent (f x) }. *)
(* *) *)

(* End Equiv. *)

(* Arguments sinto {_ _} {iso} F _ : rename. *)
(* Arguments soutof {_ _} {iso} F _ : rename. *)

(* Section flip. *)
(*   Variables A B : Type. *)
(*   Variable E : Equiv A B. *)

(*   Definition Equiv_flip : Equiv B A := *)
(*     fun F => Iso_flip (siso F). *)

(*   Variable Eok : EquivOk E. *)

(*   Definition EquivOk_flip : EquivOk Equiv_flip. *)
(*   Proof. *)
(*     destruct Eok. *)
(*     constructor. *)
(*     { red; intros. *)
(*       specialize (siso_dist0 F _ _). *)
(*       unfold siso, Equiv_flip. *)
(*       rewrite <- isomap_flip. *)
(*       f_equal. *)
(*       rewrite <- siso_dist0. reflexivity. } *)
(*     { unfold Equiv_flip; simpl. intros. *)
(*       eapply IsoOk_flip. eauto. } *)
(*   Qed. *)
(* End flip. *)

(* Section ident. *)
(*   Variable A : Type. *)

(*   Definition Equiv_ident : Equiv A A := *)
(*     fun F => {| into := fun x : F A => x ; outof := fun x : F A => x |}. *)

(*   Global Instance EquivOk_ident : EquivOk Equiv_ident. *)
(*   Proof. *)
(*     constructor. *)
(*     { red. simpl. destruct 1. eauto. } *)
(*     { constructor; reflexivity. } *)
(*   Qed. *)
(* End ident. *)

(* Section Equiv_compose. *)
(*   Variables A B C : Type. *)
(*   Variable Equiv_AB : Equiv A B. *)
(*   Variable Equiv_BC : Equiv B C. *)

(*   Definition Equiv_compose : Equiv A C := *)
(*     fun F => Iso_compose (siso F) (siso F). *)

(*   Hypothesis EquivOk_AB : EquivOk Equiv_AB. *)
(*   Hypothesis EquivOk_BC : EquivOk Equiv_BC. *)

(*   Global Instance EquivOk_compose : EquivOk Equiv_compose. *)
(*   Proof. *)
(*     constructor. *)
(*     { red. intros. *)
(*       unfold siso, Equiv_compose. *)
(*       rewrite <- (@siso_dist _ _ _ EquivOk_AB _ _ fOk). *)
(*       rewrite <- (@siso_dist _ _ _ EquivOk_BC _ _ fOk). *)
(*       generalize (@isomap_compose _ _ fOk _ _ _ (@siso A B Equiv_AB (fun x : Type => x)) (@siso _ _ Equiv_BC (fun x : Type => x))). *)
(*       eauto. } *)
(*     { simpl; intros. eapply IsoOk_compose; simpl; *)
(*       eapply sinto_soutof_Iso; eauto. } *)
(*   Qed. *)
(* End Equiv_compose. *)
