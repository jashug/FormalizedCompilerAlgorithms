Set Primitive Projections.

From Coq Require Import String Ascii ZArith.
From Coq Require Import FSets FMaps FMapAVL OrderedTypeEx.

Definition state := Z.

Module Char_as_UOT <: UsualOrderedType.
Definition t := ascii.
Definition eq := @eq t.
Axiom lt : t -> t -> Prop.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.
Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Axiom compare : forall x y : t, Compare lt eq x y.
Axiom eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
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
