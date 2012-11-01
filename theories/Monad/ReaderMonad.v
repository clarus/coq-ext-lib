Require Import Monad.
Require Import ExtLib.Data.Monoid.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section ReaderType.
  Variable S : Type.

  Record reader (t : Type) : Type := mkReader
  { runReader : S -> t }.

  Global Instance Monad_reader : Monad reader :=
  { ret  := fun _ v => mkReader (fun _ => v)
  ; bind := fun _ c1 _ c2 =>
    mkReader (fun s =>
      let v := runReader c1 s in
      runReader (c2 v) s)
  }.

  Global Instance Reader_reader : Reader S reader :=
  { ask := mkReader (fun x => x)
  ; local := fun f _ cmd => mkReader (fun x => runReader cmd (f x))
  }.

  Variable m : Type -> Type.

  Record readerT (t : Type) : Type := mkReaderT
  { runReaderT : S -> m t }.

  Variable M : Monad m.

  Global Instance Monad_readerT : Monad readerT :=
  { ret := fun _ x => mkReaderT (fun s => @ret _ M _ x)
  ; bind := fun _ c1 _ c2 =>
    mkReaderT (fun s =>
      @bind _ M _ (runReaderT c1 s) _ (fun v =>
        runReaderT (c2 v) s))
  }.

  Global Instance Reader_readerT : Reader S readerT :=
  { ask := mkReaderT (fun x => ret x)
  ; local := fun f _ cmd => mkReaderT (fun x => runReaderT cmd (f x))
  }.

  Global Instance MonadT_readerT : MonadT readerT m :=
  { lift := fun _ c => mkReaderT (fun _ => c)
  }.

  Global Instance Zero_readerT (MZ : Zero m) : Zero readerT :=
  { zero := fun _ => lift zero }.

  Global Instance State_readerT T (MZ : State T m) : State T readerT :=
  { get := lift get
  ; put := fun x => lift (put x)
  }.

  Global Instance Writer_readerT T (Mon : Monoid T) (MZ : Writer Mon m) : Writer Mon readerT :=
  { tell := fun v => lift (tell v)
  ; listen := fun _ c => mkReaderT (fun s => listen (runReaderT c s))
  ; pass := fun _ c => mkReaderT (fun s => pass (runReaderT c s))
  }.

  Global Instance Exception_readerT {E} (ME : MonadExc E m) : MonadExc E readerT :=
  { raise := fun _ v => lift (raise v)
  ; catch := fun _ c h => mkReaderT (fun s => catch (runReaderT c s) (fun x => runReaderT (h x) s))
  }.

  Global Instance MonadPlus_readerT {mMonadPlus:MonadPlus m} : MonadPlus readerT :=
  { mplus _A _B mA mB := mkReaderT (fun r => mplus (runReaderT mA r)
                                                   (runReaderT mB r))
  }.

End ReaderType.

Arguments mkReaderT {S} {m} {t} _.

Global Instance Reader_lift_readerT T S m (R : Reader T m) : Reader T (readerT S m) :=
{ ask := mkReaderT (fun _ => ask)
; local := fun f _ c =>
  mkReaderT (fun s => local f (runReaderT c s))
}.