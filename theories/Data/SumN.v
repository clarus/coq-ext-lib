Require Import ExtLib.Data.Map.FMapPositive.

Fixpoint pmap_lookup' (ts : pmap Type) (p : positive) : option Type :=
  match p with
    | xH => pmap_here ts
    | xI p => pmap_lookup' (pmap_right ts) p
    | xO p => pmap_lookup' (pmap_left ts) p
  end.

Record OneOf (ts : pmap Type) : Type :=
{ index : positive
; value : match pmap_lookup' ts index with
            | None => Empty_set
            | Some T => T
          end
}.

Definition Into {ts} {T : Type} (v : T) (n : positive) (pf : Some T = pmap_lookup' ts n) : OneOf ts :=
{| index := n
; value := match pf in _ = z return match z with
                                      | None => Empty_set
                                      | Some T => T
                                    end
           with
             | eq_refl => v
           end
|}.

Fixpoint asNth' {ts : pmap Type} (p p' : positive)
: match pmap_lookup' ts p' with
    | None => Empty_set
    | Some T => T
  end -> option (match pmap_lookup' ts p with
                   | None => Empty_set
                   | Some T => T
                 end) :=
  match p as p , p' as p'
        return match pmap_lookup' ts p' with
                 | None => Empty_set
                 | Some T => T
               end -> option (match pmap_lookup' ts p with
                                | None => Empty_set
                                | Some T => T
                              end)
  with
    | xH , xH => Some
    | xI p , xI p' => asNth' p p'
    | xO p , xO p' => asNth' p p'
    | _ , _ => fun _ => None
  end.

Definition asNth {ts : pmap Type} (p : positive) (oe : OneOf ts)
: option (match pmap_lookup' ts p with
            | None => Empty_set
            | Some T => T
          end) :=
  @asNth' ts p oe.(index ts) oe.(value ts).

Theorem asNth_eq
: forall ts p oe v,
    @asNth ts p oe = Some v ->
    oe = {| index := p ; value := v |}.
Proof.
  unfold asNth.
  destruct oe; simpl.
  revert value0. revert index0. revert ts.
  induction p; destruct index0; simpl; intros;
  solve [ congruence | eapply IHp in H; inversion H; clear H IHp; subst; auto ].
Qed.

Section elim.
  Context {T : Type}.
  Variable F : T -> Type.

  Fixpoint pmap_elim (R : Type) (ts : pmap T) : Type :=
    match ts with
      | Empty => R
      | Branch None l r => pmap_elim (pmap_elim R r) l
      | Branch (Some x) l r => F x -> pmap_elim (pmap_elim R r) l
    end.
End elim.

(*
Fixpoint matchOn' T {ts : pmap Type} (p : positive) {struct ts}
: match pmap_lookup p ts with
    | None => Empty_set
    | Some T => T
  end -> pmap_elim (fun x => x -> T) T ts.
  refine
    match ts as ts
        , p as p
          return match pmap_lookup p ts with
                   | None => Empty_set
                   | Some T => T
                 end -> pmap_elim (fun x => x -> T) T ts with
      | Empty , xH => fun x : Empty_set => match x with end
      | Empty , xO _ => fun x : Empty_set => match x with end
      | Empty , xI _ => fun x : Empty_set => match x with end
      | Branch None l r , xH => _
      | Branch (Some T) l r , xH => _
      | Branch b l r , xO p => _
      | Branch b l r , xI p => _
    end; simpl.
  Focus 3.
*)