Require Import ExtLib.Structures.Cat.
Require Import ExtLib.Structures.CatFunctor.
Require Import ExtLib.Iso.Iso.
Require Import ExtLib.Iso.IsoFunctor.

Set Implicit Arguments.
Set Strict Implicit.

Definition Pi (T : Type) (F : T -> Type) : Type :=
  forall x : T, F x.

Section dependent_functors.
  Variable Cat : Category Type.
  Variable App : forall A B, (mor A B) -> A -> B.
  Variables (Q : Type -> Type) (F : Pi Q).

  Class DFunctor
        (Hiso : CatFunctor Cat Q)
        (equiv : forall x, Q x -> Q x -> Type) (** This the morphism in the target category **)
  : Type :=
  { fdmap : forall A B : Type,
            forall i : mor A B, equiv _ (@App _ _ (@cmap Cat Q Hiso _ _ i) (F A)) (F B)
  }.

  Definition IsoIso A : IsoFunctor (fun x : Type => Iso A x -> Type).
    constructor; intros.
    constructor. intros.
    apply X0. eapply Iso_compose. apply Iso_flip. eassumption. assumption.
    intros. apply X0. eapply Iso_compose. eapply X. eassumption.
  Defined.

End dependent_functors.

Definition Iso_app {A B : Type} (i : Iso A B) (x : A) : B :=
  @into _ _ i x.

Definition Iso_rect
           (A : Type)
           (P : forall B, Iso A B -> Type)
           (IsoDFunctor : @DFunctor Category_Iso (@Iso_app)
                                    (fun x => Iso A x -> Type) P (IsoIso _) (fun x a b => forall i, Iso (a i) (b i)))
           (br : P A (Iso_ident A))
           (B : Type) (pf : Iso A B) : P B pf.
  refine (
      match pf as i return P B i with
        | {| into := into'; outof := outof' |} =>
          @outof
            (P B {| into := fun x : A => into' x; outof := fun x : B => outof' x |})
            (P A (Iso_ident A))
            (@fdmap _ _ _ _ _ _ IsoDFunctor B A
                    {| into := outof'; outof := into' |}
                    (Iso_ident A)) br
      end
    ).
Defined.

(** NOTE: If Iso wasn't a record then this would simplify completely *)
(* Eval compute in @Iso_rect. *)

(**
(** What is the generalization of [Functor] to a dependent function? **)
Class DFunctor (Q : Type -> Type) (F : Pi Q)
      (Hiso : IsoFunctor Q)
      (equiv : forall x, Q x -> Q x -> Type) (** TODO: this is odd... **)
: Type :=
{ fdmap : forall A B : Type,
          forall i : Iso A B, equiv _ (F A) (@outof _ _ (@gmap Iso Q Hiso _ _ i) (F B))
}.

Definition IsoIso A : IsoFunctor (fun x : Type => Iso A x -> Type).
constructor; intros.
constructor. intros.
apply X0. eapply Iso_compose. apply Iso_flip. eassumption. assumption.
intros. apply X0. eapply Iso_compose. eapply X. eassumption.
Defined.

Lemma iso_compose_id : forall A B (i : Iso A B), i = Iso_compose i (Iso_ident _).
unfold Iso_compose. simpl. unfold compose.
(** eta for records would give you this equation without a match! **)
destruct i. reflexivity.
Defined.

Definition Iso_rect
           (A : Type)
           (P : forall B, Iso A B -> Type)
           (IsoDFunctor : @DFunctor (fun x => Iso A x -> Type) P (IsoIso _) (fun x a b => forall i, Iso (a i) (b i)))
           (br : P A (Iso_ident A))
           (B : Type) (pf : Iso A B) : P B pf.
rewrite (iso_compose_id pf).
revert br.
exact (@into _ _ (@fdmap _ _ _ _ IsoDFunctor A B pf (Iso_ident _))).
Show Proof.
Defined.
**)