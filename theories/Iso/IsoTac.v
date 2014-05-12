Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.FunctorLaws.
Require Import ExtLib.Structures.CoFunctor.
Require Import ExtLib.Iso.Iso.
Require Import ExtLib.Iso.IsoFunctor.

Set Implicit Arguments.
Set Strict Implicit.

(** AXIOMS **)
Require Import FunctionalExtensionality.

Section instances.

  Variable A B : Type.

  Definition Functor_const T : Functor (fun x => T) :=
    mkFunctor (fun _ => T)
              (fun T' U' (f : T' -> U') (x : T) => x).

  Instance type1_const T (t : type T) : type1 (fun x : _ => T) :=
    fun _ _ => t.

  Instance FunctorLaws_const T t : @FunctorLaws _ (Functor_const T) (@type1_const T t).
  Proof.
    constructor; intros; repeat red; simpl; auto.
  Qed.

  Definition Functor_option : Functor option :=
    mkFunctor option
              (fun _ _ f x => match x with
                                | None => None
                                | Some x => Some (f x)
                              end).

(*
  Instance FunctorLaws_option : FunctorLaws Functor_option.
  Proof.
    constructor; compute;
    intros; apply functional_extensionality; destruct x; reflexivity.
  Qed.
*)

  Local Instance Functor_Fun T : Functor (fun x => T -> x) :=
    mkFunctor (fun x => T -> x)
              (fun _ _ g f => fun x => g (f x)).

  Local Instance CoFunctor_Fun T : CoFunctor (fun x => x -> T) :=
  {| cofmap := fun _ _ g f => fun x => f (g x) |}.

  Local Instance Functor_functor F G (fF : Functor F) (fG : Functor G)
  : Functor (fun x => F (G x)) :=
    mkFunctor (fun x => F (G x))
              (fun _ _ g => @fmap F _ _ _ (@fmap G _ _ _ g)).

  Local Instance CoFunctor_functor F G (fF : Functor F) (fG : CoFunctor G)
  : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @fmap F _ _ _ (@cofmap G _ _ _ g) |}.

  Local Instance Functor_cofunctor F G (fF : CoFunctor F) (fG : Functor G)
  : CoFunctor (fun x => F (G x)) :=
  {| cofmap := fun _ _ g => @cofmap F _ _ _ (@fmap G _ _ _ g) |}.

  Local Instance CoFunctor_cofunctor F G (fF : CoFunctor F) (fG : CoFunctor G)
  : Functor (fun x => F (G x)) :=
    mkFunctor (fun x => F (G x))
              (fun _ _ g => @cofmap F _ _ _ (@cofmap G _ _ _ g)).

  Instance IsoFunctor_compose F G (fF : IsoFunctor F) (fG : IsoFunctor G)
  : IsoFunctor (fun x => F (G x)) :=
    mkIsoFunctor (fun x => F (G x))
                 (fun A B (i : Iso A B) => @isomap _ fF _ _ (@isomap _ fG _ _ i)).

(*
  Global Instance IsoFunctorLaws_compose
         F fF (fokF : @IsoFunctorLaws F fF)
         G fG (fokG : @IsoFunctorLaws G fG)
  : IsoFunctorLaws (IsoFunctor_compose fF fG).
  Proof.
    constructor.
    { intros. simpl. repeat rewrite isomap_id. reflexivity. }
    { simpl; intros. repeat rewrite isomap_compose. reflexivity. }
    { simpl. intros; repeat rewrite isomap_flip. reflexivity. }
  Qed.
*)

  Definition IsoFunctor_eta F (f : IsoFunctor F) : IsoFunctor (fun x => F x) :=
    mkIsoFunctor (fun x => F x)
                 (fun _ _ f => isomap f).

(*
  Definition IsoFunctorLaws_eta F (f : IsoFunctor F) (fok : IsoFunctorLaws f) : IsoFunctorLaws (IsoFunctor_eta f).
  Proof.
    constructor.
    { intros; simpl. eapply isomap_id. }
    { intros. simpl. eapply isomap_compose. }
    { intros; simpl. eapply isomap_flip. }
  Qed.
*)

  Instance IsoFunctor_option F (iF : IsoFunctor F)
  : IsoFunctor (fun x => option (F x)) :=
    mkIsoFunctor (fun x => option (F x))
                 (fun _ _ i =>
                    {| into := fun x =>
                                 match x with
                                   | None => None
                                   | Some x => Some (into (iso := isomap i) x)
                                 end
                     ; outof := fun x =>
                                  match x with
                                    | None => None
                                    | Some x => Some (outof (iso := isomap i) x)
                                  end |}).

  Theorem into_into_Iso_compose : forall A B C iAB iBC x,
                                    @into B A iAB (@into C B iBC x) =
                                    @into C A (Iso_compose iAB iBC) x.
  Proof. reflexivity. Qed.
  Theorem outof_outof_Iso_compose : forall A B C iAB iBC x,
                                      @outof A B iAB (@outof B C iBC x) =
                                      @outof A C (Iso_compose iBC iAB) x.
  Proof. reflexivity. Qed.


(*
  Instance IsoFunctorLaws_option F iF (iokF : @IsoFunctorLaws F iF) : IsoFunctorLaws (IsoFunctor_option iF).
  Proof.
    clear - iokF; constructor.
    { simpl; intros. f_equal; apply functional_extensionality; destruct x; auto;
                     rewrite isomap_id; auto. }
    { unfold Iso_compose; simpl; intros. f_equal; apply functional_extensionality; destruct x; unfold compose; simpl; auto.
      rewrite into_into_Iso_compose. rewrite isomap_compose. reflexivity.
      rewrite outof_outof_Iso_compose. rewrite isomap_compose. reflexivity. }
    { intros. Opaque Iso_flip. simpl. repeat rewrite <- isomap_flip.
      Transparent Iso_flip. simpl. unfold Iso_flip. simpl. reflexivity. }
  Qed.
*)

End instances.

(*
Ltac solve_isoFunctor X :=
  match X with
    | _ => assumption
    | (fun _ => ?T) => solve [ eapply IsoFunctor_Functor; eapply Functor_const ]
    | (fun x => x) => solve [ eapply IsoFunctor_Functor; eapply Functor_id ]
    | (fun x => option (@?F x)) => eapply IsoFunctor_option; solve_isoFunctor F
    | (fun x => (@?F x) -> (@?G x)) => eapply IsoFunctor_Fun; [ solve_isoFunctor F | solve_isoFunctor G ]
    | (fun x => ?F (@?G x)) => eapply (@IsoFunctor_compose F G); [ solve_isoFunctor F | solve_isoFunctor G ]
  end.
Ltac solve_isoFunctorLaws :=
  repeat (   simple eapply IsoFunctorLaws_Fun
          || simple eapply IsoFunctorLaws_option
          || simple eapply IsoFunctorLaws_compose
          || simple eapply IsoFunctorLaws_Functor
          || simple eapply FunctorLaws_const
          || simple eapply FunctorLaws_id
          || assumption).

Hint Extern 1 (@IsoFunctor ?X) => solve [ solve_isoFunctor X ] : typeclass_instances.
Hint Extern 1 (@IsoFunctorLaws _ _) => solve [ solve_isoFunctorLaws ] : typeclass_instances.
*)

(*
Section iso_tac.
  Variable A B : Type.
  Variable iso : forall F, Iso (F A) (F B).
  Context {isoOk : forall F, IsoOk (iso F)}.
  Context {DistFunc_f : DistIsoFunc iso}.


  Lemma f_const : forall T x, into (iso := iso (fun _ => T)) x = x.
  Proof.
    intro.
    specialize (@dist_over _ _ _ DistFunc_f (fun _ => T) _ _); simpl; intros.
    match goal with
      | [ H : _ = ?X |- context [ ?Y ] ] =>
        replace Y with X; [ rewrite <- H | ]; try reflexivity
    end.
  Qed.

  Lemma f_option : forall F (fF : IsoFunctor F) (fFok : IsoFunctorLaws fF) x,
                     into (iso := iso (fun T => option (F T))) x =
                     match x with
                       | None => None
                       | Some x => Some (into (iso := iso (fun T => (F T))) x)
                     end.
  Proof.
    intros.
    specialize (@dist_over _ _ _ DistFunc_f (fun T : Type => option (F T)) _ _); simpl; intros.
    match goal with
      | [ H : _ = ?X |- context [ ?Y ] ] =>
        replace Y with X; [ rewrite <- H | ]; try reflexivity
    end.
    simpl. destruct x; auto.
    f_equal. rewrite dist_over; auto.
  Qed.

  Lemma f_arrow : forall F G (fF : IsoFunctor F) (fG : IsoFunctor G),
                  IsoFunctorLaws fG -> IsoFunctorLaws fF ->
                  forall (x : F A -> G A),
                  into (iso := iso (fun T => F T -> G T)) x =
                  compose (into (iso := iso G)) (compose x (outof (iso := iso F))).
  Proof.
    intros.
    unfold compose.
    assert (IsoFunctorLaws (IsoFunctor_Fun fF fG)).
    { apply IsoFunctorLaws_Fun; auto. }
    specialize (@dist_over _ _ _ _ _ _ H1); simpl; intros.
    match goal with
      | [ H : _ = ?X |- context [ ?Y ] ] =>
        replace Y with X; [ rewrite <- H | ]; try reflexivity
    end.
    simpl.
    repeat rewrite dist_over by assumption. reflexivity.
  Qed.

End iso_tac.

Create HintDb iso discriminated.

Section with_iso.
  Variable A B : Type.
  Variable SI : Equiv A B.
  Variable SIOk : EquivOk SI.

  Let iso : forall F, Iso (F A) (F B) := @siso _ _ SI.
  Lemma isoOk : forall F func, @IsoFunctorLaws F func -> IsoOk (iso F).
  Proof.
    intros; eapply sinto_soutof_Iso; auto.
  Qed.
  Lemma DistFunc_f : DistIsoFunc iso.
  Proof.
    intros; apply siso_dist; auto.
  Qed.

  Let fiso : forall F, Iso (F B) (F A) := @siso _ _ (Equiv_flip SI).
  Lemma fisoOk : forall F func, @IsoFunctorLaws F func -> IsoOk (fiso F).
  Proof.
    intros; eapply IsoOk_flip. eapply isoOk; eauto.
  Qed.
  Lemma fDistFunc_f : DistIsoFunc fiso.
  Proof.
    intros. unfold fiso.
    eapply EquivOk_flip. eauto.
  Qed.

  Lemma sinto_soutof : forall F func, @IsoFunctorLaws F func -> forall x,
                         sinto F (soutof F x) = x.
  Proof.
    unfold sinto, soutof; simpl; intros.
    rewrite into_outof; auto. eapply isoOk; eauto.
  Qed.

  Lemma soutof_sinto : forall F func, @IsoFunctorLaws F func -> forall x,
                         soutof F (sinto F x) = x.
  Proof.
    unfold sinto, soutof; simpl; intros.
    rewrite outof_into; auto. eapply isoOk; eauto.
  Qed.



  Lemma sinto_option : forall (T : Type -> Type) fT x, @IsoFunctorLaws T fT ->
                         sinto (iso := SI) (fun Ty => option (T Ty)) x =
                         match x with
                           | None => None
                           | Some x => Some (sinto (iso := SI) (fun Ty => T Ty) x)
                         end.
  Proof.
    intros.
    generalize (@f_option A B iso DistFunc_f _ _ H x).
    simpl. auto.
  Qed.

  Lemma soutof_option : forall (T : Type -> Type) fT x, @IsoFunctorLaws T fT ->
                         soutof (iso := SI) (fun Ty => option (T Ty)) x =
                         match x with
                           | None => None
                           | Some x => Some (soutof (iso := SI) (fun Ty => T Ty) x)
                         end.
  Proof.
    intros.
    generalize (@f_option _ _ fiso fDistFunc_f _ _ H x).
    simpl. auto.
  Qed.
  Hint Rewrite sinto_option soutof_option using eauto with typeclass_instances : iso.
  Lemma sinto_const : forall (T : Type) x,
                        sinto (iso := SI) (fun _ => T) x = x.
  Proof.
    intros.
    generalize (@f_const _ _ iso DistFunc_f _ x).
    simpl. auto.
  Qed.
  Lemma soutof_const : forall (T : Type) x,
                        soutof (iso := SI) (fun _ => T) x = x.
  Proof.
    intros.
    generalize (@f_const _ _ fiso fDistFunc_f _ x).
    simpl. auto.
  Qed.
  Hint Rewrite sinto_const soutof_const using eauto with typeclass_instances : iso.

  Lemma sinto_app : forall T U fT fU,
                      @IsoFunctorLaws T fT ->
                      @IsoFunctorLaws U fU ->
                      forall (f : T A -> U A),
                      sinto (iso := SI) (fun Ty => T Ty -> U Ty) f =
                      (fun x => (sinto (iso := SI) (fun Ty => U Ty) (f (soutof _ x)))).
  Proof.
    intros.
    generalize (@f_arrow _ _ iso DistFunc_f _ _ _ _ H0 H f).
    simpl. auto.
  Qed.
  Lemma soutof_app : forall T U fT fU,
                      @IsoFunctorLaws T fT ->
                      @IsoFunctorLaws U fU ->
                      forall (f : T B -> U B),
                      soutof (iso := SI) (fun Ty => T Ty -> U Ty) f =
                      (fun x => (soutof (iso := SI) (fun Ty => U Ty) (f (sinto _ x)))).
  Proof.
    intros.
    generalize (@f_arrow _ _ fiso fDistFunc_f _ _ _ _ H0 H f).
    simpl. auto.
  Qed.
  Hint Rewrite sinto_app soutof_app : iso.

  Theorem soutof_app' : forall T U fU,
                          @IsoFunctorLaws U fU ->
                          forall f,
                         soutof (fun Ty => T -> U Ty) f =
                         (fun x => (soutof U (f x))).
  Proof.
    intros.
    rewrite (@soutof_app _ _ _ _ (IsoFunctorLaws_Functor (FunctorLaws_const T)) H f).
    apply functional_extensionality; intros. rewrite sinto_const. reflexivity.
  Qed.
  Theorem sinto_app' : forall T U fU,
                          @IsoFunctorLaws U fU ->
                          forall f,
                         sinto (fun Ty => T -> U Ty) f =
                         (fun x => (sinto U (f x))).
  Proof.
    intros.
    rewrite (@sinto_app _ _ _ _ (IsoFunctorLaws_Functor (FunctorLaws_const T)) H f).
    apply functional_extensionality; intros. rewrite soutof_const. reflexivity.
  Qed.

  Theorem soutof_app'' : forall T U fU,
                          @IsoFunctorLaws U fU ->
                           forall f,
                         soutof (fun Ty => U Ty -> T) f =
                         (fun x => f (sinto U x)).
  Proof.
    intros.
    rewrite (@soutof_app _ _ _ _ H (IsoFunctorLaws_Functor (FunctorLaws_const T)) f).
    apply functional_extensionality; intros. rewrite soutof_const. reflexivity.
  Qed.

  Theorem sinto_app'' : forall T U fU,
                          @IsoFunctorLaws U fU ->
                           forall f,
                         sinto (fun Ty => U Ty -> T) f =
                         (fun x => f (soutof U x)).
  Proof.
    intros.
    rewrite (@sinto_app _ _ _ _ H (IsoFunctorLaws_Functor (FunctorLaws_const T)) f).
    apply functional_extensionality; intros. rewrite sinto_const. reflexivity.
  Qed.

  Hint Rewrite sinto_app sinto_app' sinto_app'' using eauto with typeclass_instances : iso.
  Hint Rewrite soutof_app soutof_app' soutof_app'' using eauto with typeclass_instances : iso.
End with_iso.

Hint Rewrite sinto_option soutof_option using eauto with typeclass_instances : iso.
Hint Rewrite sinto_const soutof_const using eauto with typeclass_instances : iso.
Hint Rewrite sinto_app soutof_app using eauto with typeclass_instances : iso.
Hint Rewrite sinto_app sinto_app' sinto_app'' using eauto with typeclass_instances : iso.
Hint Rewrite soutof_app soutof_app' soutof_app'' using eauto with typeclass_instances : iso.

Ltac iso_norm :=
  autorewrite with iso in *.
*)