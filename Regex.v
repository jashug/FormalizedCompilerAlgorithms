Set Primitive Projections.
Set Uniform Inductive Parameters.
Unset Universe Minimization ToSet.

From Coq Require Import String Ascii ZArith.
From Coq Require Import FSets FMaps FMapAVL OrderedTypeEx.

Open Scope Z_scope.

From CompilerOrg Require Import NFA.

Module CharSet := FSetAVL.Make(Char_as_UOT) .

Module Letter <: OrderedType.
Definition t : Type := CharSet.t * state.
Definition eq (x y : t) := x.(snd) = y.(snd).
Definition lt (x y : t) := x.(snd) < y.(snd).
Definition eq_refl (x : t) : eq x x := eq_refl.
Definition eq_sym (x y : t) : eq x y -> eq y x :=
  fun p => eq_sym p.
Definition eq_trans (x y z : t) : eq x y -> eq y z -> eq x z :=
  fun p q => eq_trans p q.
Definition lt_trans (x y z : t) : lt x y -> lt y z -> lt x z :=
  Z.lt_trans _ _ _.
Definition lt_not_eq (x y : t) : lt x y -> ~ eq x y :=
  @Z_as_OT.lt_not_eq _ _.
Definition compare (x y : t) : Compare lt eq x y :=
  match Z_as_OT.compare x.(snd) y.(snd) return Compare lt eq x y with
  | LT p => @LT t lt eq x y p
  | EQ p => @EQ t lt eq x y p
  | GT p => @GT t lt eq x y p
  end.
Definition eq_dec (x y : t) : { eq x y } + { ~ eq x y } :=
  Z.eq_dec _ _.
End Letter.

Module LetterSet.
Module S := FSetAVL.Make(Letter).
Module Notation.
Declare Scope letter_set_scope.
Bind Scope letter_set_scope with S.t.
Infix "<+>" := (S.union) (at level 50, left associativity) : letter_set_scope.
End Notation.
End LetterSet.
Import LetterSet.Notation.

Module Letter2Set.
Module OT := PairOrderedType Letter Letter.
Module S := FSetAVL.Make(OT).
Module Notation.
Declare Scope letter2_set_scope.
Bind Scope letter2_set_scope with S.t.
Local Open Scope letter2_set_scope.
Infix "<+>" := (S.union) (at level 50, left associativity) : letter2_set_scope.
Infix ">>=" :=
  (fun m k =>
   LetterSet.S.fold (fun x s => k x <+> s) m S.empty)
  (at level 50, no associativity) : letter2_set_scope.
Infix "<*>" :=
  (fun (l r : LetterSet.S.t) =>
     l >>= fun a =>
     r >>= fun b =>
     S.singleton (a , b))
  (at level 50, no associativity) : letter2_set_scope.
End Notation.
End Letter2Set.
Import Letter2Set.Notation.

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

(* initial letters *)
(* note that performance of p (aaa...a) will be quadratic, due to repeated
   calculation of l. Easy to fix by making one recursive function that computes
   all four values simultaneously. *)
Fixpoint p (x : regex Letter.t) : LetterSet.S.t :=
  match x with
  | Empty | Eps => LetterSet.S.empty
  | Char c => LetterSet.S.singleton c
  | Alt e f => p e <+> p f
  | Seq e f => p e <+> (if l e then p f else LetterSet.S.empty)
  | Star e => p e
  end.

(* final letters *)
Fixpoint d (x : regex Letter.t) : LetterSet.S.t :=
  match x with
  | Empty | Eps => LetterSet.S.empty
  | Char c => LetterSet.S.singleton c
  | Alt e f => d e <+> d f
  | Seq e f => (if l f then d e else LetterSet.S.empty) <+> d f
  | Star e => d e
  end.

(* letter pairs *)
Fixpoint f_ (x : regex Letter.t) : Letter2Set.S.t :=
  match x return Letter2Set.S.t with
  | Empty | Eps | Char _ => Letter2Set.S.empty
  | Alt e f => f_ e <+> f_ f
  | Seq e f => f_ e <+> f_ f <+> (d e <*> p f)
  | Star e => f_ e <+> (d e <*> p e)
  end.

Module StateMap := FMapAVL.Make(Z_as_OT).
Module CharSetMap := FMapAVL.Make(CharSet).

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
  Letter2Set.S.fold
    (fun elt sm => add_transition
       elt.(fst).(snd) elt.(snd).(fst) elt.(snd).(snd) sm)
    fs
    (StateMap.empty _).

Definition positions (s : LetterSet.S.t) : StateSet.t :=
  LetterSet.S.fold (fun lt ss => StateSet.add lt.(snd) ss) s StateSet.empty.

Definition transition_map_of_letter_set (s : LetterSet.S.t)
  : CharSetMap.t StateSet.t :=
  LetterSet.S.fold
    (fun elt tm => let c := elt.(fst) in let i := elt.(snd) in
     let entry := match CharSetMap.find c tm with
       | None => StateSet.singleton i
       | Some s => StateSet.add i s
       end
     in CharSetMap.add c entry tm)
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
  let next s := match StateMap.find s joint_transitions with
    | Some cm => flatten_transitions cm
    | None => CharMap.empty _
    end
  in
  {| start := StateSet.singleton start_state; finals := finals; next := next |}.
