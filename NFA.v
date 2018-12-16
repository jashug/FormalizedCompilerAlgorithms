Set Primitive Projections.

From Coq Require Import String Ascii ZArith.
From Coq Require Import FSets FMaps FMapAVL OrderedTypeEx.

Definition state := Z.

Module Char_as_UOT <: UsualOrderedType.
Definition t := ascii.
Definition eq := @eq t.
Definition lt (x y : t) := (N_of_ascii x < N_of_ascii y)%N.
Definition eq_refl := @eq_refl t.
Definition eq_sym : forall {x y : t}, eq x y -> eq y x := @eq_sym t.
Definition eq_trans : forall {x y z : t}, eq x y -> eq y z -> eq x z :=
  @eq_trans t.
Definition lt_trans (x y z : t) : lt x y -> lt y z -> lt x z :=
  N.lt_trans _ _ _.
Definition lt_not_eq (x y : t) (p : lt x y) (e : eq x y) : False :=
  N_as_OT.lt_not_eq _ _ p (f_equal N_of_ascii e).
Definition compare (x y : t) : Compare lt eq x y :=
  match N_as_OT.compare (N_of_ascii x) (N_of_ascii y) with
  | LT p => @LT t lt eq x y p
  | EQ p => @EQ t lt eq x y (eq_trans (eq_trans
    (eq_sym (ascii_N_embedding x))
    (f_equal ascii_of_N p))
    (ascii_N_embedding y))
  | GT p => @GT t lt eq x y p
  end.
Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y } := ascii_dec.
End Char_as_UOT.

Module StateSet := FSetAVL.Make(Z_as_OT).
Module CharMap := FMapAVL.Make(Char_as_UOT).

Record NFA : Type := {
  start : StateSet.t;
  finals : StateSet.t;
  next : state -> CharMap.t StateSet.t;
}.
(*
The set of reachable states should be finite to capture true finite automata.
Consider next : StateMap.t (CharMap.t StateSet.t), with not-found -> empty map.
*)

Definition find_states sym nfa m :=
  match CharMap.find sym (nfa.(next) m) with
  | Some ss => ss
  | None => StateSet.empty
  end.

Definition flat_map f ss : StateSet.t :=
  StateSet.fold (fun s => StateSet.union (f s)) ss StateSet.empty.

Definition accept (nfa : NFA) : string -> bool :=
  let fix step cur s := match s with
    | EmptyString => negb (StateSet.is_empty (StateSet.inter cur nfa.(finals)))
    | String c cs => step (flat_map (find_states c nfa) cur) cs
    end
  in step nfa.(start).
