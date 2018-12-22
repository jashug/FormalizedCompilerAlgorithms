Set Primitive Projections.
Set Uniform Inductive Parameters.
Unset Universe Minimization ToSet.

From Coq Require Import String Ascii ZArith.
From Coq Require Import FSets FMaps FMapAVL FMapFacts OrderedTypeEx.

Open Scope Z_scope.

From CompilerOrg Require Import NFA.

Module State2_as_OT := PairOrderedType Z_as_OT Z_as_OT.

Module CharSet := FSetAVL.Make(Char_as_UOT) .
Module StateMap := FMapAVL.Make(Z_as_OT).
Module StateMapP := FMapFacts.Properties(StateMap).
Module State2Map := FMapAVL.Make(State2_as_OT).
Module State2MapP := FMapFacts.Properties(State2Map).
Module CharSetMap := FMapAVL.Make(CharSet).

Polymorphic Cumulative Inductive regex@{i} {Γ : Type@{i}} : Type@{i} :=
  | Empty (* L = { } *)
  | Eps   (* L = {ε} *)
  | Char : Γ -> regex
  | Alt : regex -> regex -> regex
  | Seq : regex -> regex -> regex
  | Star : regex -> regex
.
Arguments regex Γ : clear implicits.

Fixpoint l {Γ} (x : regex Γ) : bool :=
  match x with
  | Empty => false
  | Eps => true
  | Char _ => false
  | Alt e f => l e || l f
  | Seq e f => l e && l f
  | Star _ => true
  end.

Module Import Notation.
Declare Scope state_set_scope.
Bind Scope state_set_scope with StateSet.t.
Infix "<+>" := (StateSet.union)
  (at level 50, left associativity) : state_set_scope.
Declare Scope state_map_scope.
Bind Scope state_map_scope with StateMap.t.
Infix "<+>" := (StateMapP.update)
  (at level 50, left associativity) : state_map_scope.
Declare Scope state2_map_scope.
Bind Scope state2_map_scope with State2Map.t.
Local Open Scope state2_map_scope.
Infix "<+>" := (State2MapP.update)
  (at level 50, left associativity) : state2_map_scope.
Infix ">>=" :=
  (fun m k =>
   StateMap.fold (fun a b s => k a b <+> s) m (State2Map.empty _))
  (at level 50, no associativity) : state2_map_scope.
Infix "<*>" :=
  (fun (l r : StateMap.t _) =>
     l >>= fun a cs1 =>
     r >>= fun b cs2 =>
     State2Map.add (a , b) cs2 (State2Map.empty _))
  (at level 50, no associativity) : state2_map_scope.
End Notation.

(* initial letters *)
(* note that performance of p (aaa...a) will be quadratic, due to repeated
   calculation of l. Easy to fix by making one recursive function that computes
   all four values simultaneously. *)
Fixpoint p (x : regex (CharSet.t * state)) : StateMap.t CharSet.t :=
  match x with
  | Empty | Eps => StateMap.empty _
  | Char c => StateMap.add c.(snd) c.(fst) (StateMap.empty _)
  | Alt e f => p e <+> p f
  | Seq e f => p e <+> (if l e then p f else StateMap.empty _)
  | Star e => p e
  end.

(* final letters *)
Fixpoint d (x : regex (CharSet.t * state)) : StateMap.t CharSet.t :=
  match x with
  | Empty | Eps => StateMap.empty _
  | Char c => StateMap.add c.(snd) c.(fst) (StateMap.empty _)
  | Alt e f => d e <+> d f
  | Seq e f => (if l f then d e else StateMap.empty _) <+> d f
  | Star e => d e
  end.

(* letter pairs *)
Fixpoint f_ (x : regex (CharSet.t * state)) : State2Map.t CharSet.t :=
  match x with
  | Empty | Eps | Char _ => State2Map.empty _
  | Alt e f => f_ e <+> f_ f
  | Seq e f => f_ e <+> f_ f <+> (d e <*> p f)
  | Star e => f_ e <+> (d e <*> p e)
  end.

Definition add_transition2 c i tm :=
  let ss := match CharSetMap.find c tm with
    | None => StateSet.empty
    | Some ss => ss
    end
  in CharSetMap.add c (StateSet.add i ss) tm.

Definition add_transition i1 c2 i2 sm :=
  let tm := match StateMap.find i1 sm with
    | None => CharSetMap.empty StateSet.t
    | Some ss => ss
    end
  in StateMap.add i1 (add_transition2 c2 i2 tm) sm.

Definition transition_map_of_factor_set fs :=
  State2Map.fold
    (fun st12 cs sm => add_transition
       st12.(fst) cs st12.(snd) sm)
    fs
    (StateMap.empty _).

Definition positions (s : StateMap.t CharSet.t) : StateSet.t :=
  StateMap.fold (fun st cs ss => StateSet.add st ss) s StateSet.empty.

Definition transition_map_of_letter_set (s : StateMap.t CharSet.t)
  : CharSetMap.t StateSet.t :=
  StateMap.fold
    (fun i c tm => add_transition2 c i tm)
    s
    (CharSetMap.empty _).

Definition t := regex CharSet.t.

Fixpoint annotate_helper {Γ} (i : Z) (x : regex Γ) : regex (Γ * Z) * Z :=
  match x with
  | Empty => (Empty, i)
  | Eps => (Eps, i)
  | Char c => (Char (c, i), Z.succ i)
  | Alt e f =>
    let ae := annotate_helper i e in
    let af := annotate_helper ae.(snd) f in
    (Alt ae.(fst) af.(fst), af.(snd))
  | Seq e f =>
    let ae := annotate_helper i e in
    let af := annotate_helper ae.(snd) f in
    (Seq ae.(fst) af.(fst), af.(snd))
  | Star e =>
    let ae := annotate_helper i e in
    (Star ae.(fst), ae.(snd))
  end.

Definition start_state : state := 0.

Definition annotate {Γ} (x : regex Γ) : regex (Γ * state) :=
  (annotate_helper 1 x).(fst).

Definition flatten_transitions (cm : CharSetMap.t StateSet.t)
  : CharMap.t StateSet.t :=
  CharSetMap.fold
    (fun cs ss cm =>
       CharSet.fold
         (fun c cm =>
            let entry := match CharMap.find c cm with
              | None => StateSet.empty
              | Some ss => ss
              end
            in CharMap.add c (StateSet.union ss entry) cm)
         cs
         cm)
    cm
    (CharMap.empty _).

Definition compile (r : regex CharSet.t) : NFA :=
  let r := annotate r in
  let finals :=
    if l r then StateSet.add start_state (positions (d r))
    else positions (d r)
  in
  let transitions := transition_map_of_factor_set (f_ r) in
  let initial_transitions := transition_map_of_letter_set (p r) in
  let joint_transitions :=
    StateMap.add start_state initial_transitions transitions in
  (* Consider using StateMap.map flatten_transitions joint_transitions *)
  let next s := match StateMap.find s joint_transitions with
    | Some cm => flatten_transitions cm
    | None => CharMap.empty _
    end
  in
  {| start := StateSet.singleton start_state; finals := finals; next := next |}.
