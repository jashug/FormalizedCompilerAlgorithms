Set Primitive Projections.
Set Uniform Inductive Parameters.
Unset Universe Minimization ToSet.

From Coq Require Import String Ascii ZArith.
From Coq Require Import FSets FMaps FMapAVL OrderedTypeEx.

Open Scope Z_scope.

From CompilerOrg Require Import NFA Regex.
Import LetterSet.Notation Letter2Set.Notation.

(*
Here we prove that compile : regex CharSet.t -> NFA produces
an automaton that recognizes the same language as the input regex.
*)

(* First, we define what that means *)

Inductive regex_match : regex CharSet.t -> string -> Prop :=
  | mEps : regex_match Eps EmptyString
  | mChar : forall cs c, CharSet.mem c cs = true ->
            regex_match (Char cs) (String c EmptyString)
  | mAltl : forall e f s, regex_match e s -> regex_match (Alt e f) s
  | mAltr : forall e f s, regex_match f s -> regex_match (Alt e f) s
  | mSeq : forall e f s1 s2, regex_match e s1 -> regex_match f s2 ->
           regex_match (Seq e f) (s1 ++ s2)
  | mStar_emp : forall e, regex_match (Star e) EmptyString
  | mStar_more : forall e s1 s2, regex_match e s1 -> regex_match (Star e) s2 ->
                 regex_match (Star e) (s1 ++ s2)
.

(* This is our goal: *)
Definition Glushkov_is_correct : Prop :=
  forall r s, regex_match r s <-> accept (compile r) s = true.

Definition find_default (cm : CharMap.t StateSet.t) (key : ascii) : StateSet.t
  := match CharMap.find key cm with
     | None => StateSet.empty
     | Some ss => ss
     end.

(* Go through NFA_path_accept *)
Fixpoint NFA_path (next : state -> CharMap.t StateSet.t) (s : string)
    (first last : state) : Prop :=
  match s with
  | EmptyString => first = last
  | String c s => exists mid : state,
      StateSet.mem mid (find_default (next first) c) = true /\
      NFA_path next s mid last
  end.
Fixpoint NFA_path_compose next s1 s2 first mid last
  : NFA_path next s1 first mid -> NFA_path next s2 mid last ->
    NFA_path next (s1 ++ s2) first last :=
  match s1 with
  | EmptyString => fun 'eq_refl p2 => p2
  | String c s => fun '(ex_intro _ mid (conj P p1)) p2 =>
    ex_intro _ mid (conj P (NFA_path_compose _ _ _ _ _ _ p1 p2))
  end.
Definition NFA_path_accept (n : NFA) (s : string) : Prop :=
  exists (first last : state),
  StateSet.mem first n.(start) = true /\
  StateSet.mem last n.(finals) = true /\
  NFA_path n.(next) s first last.

Axiom Admit : forall {T}, T.

Definition finals_d r first : StateSet.t :=
  if l r then StateSet.add first (positions (d r))
  else positions (d r).
Definition finals_ad r i first : StateSet.t :=
  finals_d (annotate_helper i r).(fst) first.
Definition if_l_first_final r i first (ar := (annotate_helper i r).(fst))
  : l ar = true -> StateSet.mem first (finals_ad r i first) = true
  := fun H => match eq_sym H in _ = b
     return StateSet.mem first (if b then _ else _) = true
     with eq_refl => StateSet.mem_1 (StateSet.add_1 _ eq_refl) end.
Definition d_in_finals r i first (ar := (annotate_helper i r).(fst))
  : forall lt, LetterSet.S.In lt (d ar) ->
    StateSet.In lt.(snd) (finals_ad r i first)
  := fun lt H =>
     let H' : StateSet.In lt.(snd) (positions (d ar))
      := Admit in
     match l ar as b
     return StateSet.In lt.(snd) (if b then _ else _)
     with true => StateSet.add_2 _ H' | false => H' end.
Axiom finals_ad_alt_inc1 : forall e f i first s,
  StateSet.mem s (finals_ad e i first) = true ->
  StateSet.mem s (finals_ad (Alt e f) i first) = true.
Axiom finals_ad_alt_inc2 : forall e f i first s,
  StateSet.mem s (finals_ad f (annotate_helper i e).(snd) first) = true ->
  StateSet.mem s (finals_ad (Alt e f) i first) = true.

Fixpoint regex_match_to_path (r : regex CharSet.t) (i : Z) (s : string)
    (next : state -> CharMap.t StateSet.t) (first : state)
    (m : regex_match r s)
    :
    let ar := (annotate_helper i r).(fst) in
    (forall lt, LetterSet.S.In lt (p ar) -> forall c, CharSet.In c lt.(fst) ->
     StateSet.In lt.(snd) (find_default (next first) c)) ->
    (forall lt1 lt2, Letter2Set.S.In (lt1 , lt2) (f_ ar) ->
     forall c, CharSet.In c lt2.(fst) ->
     StateSet.In lt2.(snd) (find_default (next lt1.(snd)) c)) ->
    exists last : state,
    StateSet.mem last (finals_d ar first) = true /\
    NFA_path next s first last :=
  match m in regex_match r s
  return
    let ar := (annotate_helper i r).(fst) in
    (forall l, LetterSet.S.In l (p ar) -> forall c, CharSet.In c l.(fst) ->
     StateSet.In l.(snd) (find_default (next first) c)) ->
    (forall lt1 lt2, Letter2Set.S.In (lt1 , lt2) (f_ ar) ->
     forall c, CharSet.In c lt2.(fst) ->
     StateSet.In lt2.(snd) (find_default (next lt1.(snd)) c)) ->
    exists last : state,
    StateSet.mem last (finals_d ar first) = true /\
    NFA_path next s first last
  with
  | mEps => fun H1 H2 =>
    ex_intro _ first (conj (if_l_first_final Eps i first eq_refl) eq_refl)
  | mChar cs c c_in_cs => fun H1 H2 =>
    let A1 : StateSet.mem i (finals_ad (Char cs) i first) = true
     := StateSet.mem_1 (d_in_finals (Char cs) _ _ (cs , i)
                        (LetterSet.S.singleton_2 eq_refl)) in
    let A2 : StateSet.mem i (find_default (next first) c) = true
     := StateSet.mem_1 (H1 (cs , i) (LetterSet.S.singleton_2 eq_refl)
          c (CharSet.mem_2 c_in_cs)) in
    ex_intro _ i (conj A1 (ex_intro _ i (conj A2 eq_refl)))
  | mAltl e f s mes => fun H1 H2 =>
    let '(ex_intro _ last (conj last_final first_last_path))
     := regex_match_to_path e i s next first mes
        (fun lt A => H1 lt (LetterSet.S.union_2 _ A))
        (fun lt1 lt2 A => H2 lt1 lt2 (Letter2Set.S.union_2 _ A))
    in ex_intro _ last (conj
       (finals_ad_alt_inc1 e f i first last last_final)
       first_last_path)
  | mAltr e f s mfs => fun H1 H2 =>
    let '(ex_intro _ last (conj last_final first_last_path))
     := regex_match_to_path f (annotate_helper i e).(snd) s next first mfs
        (fun lt A => H1 lt (LetterSet.S.union_3 _ A))
        (fun lt1 lt2 A => H2 lt1 lt2 (Letter2Set.S.union_3 _ A))
    in ex_intro _ last (conj
       (finals_ad_alt_inc2 e f i first last last_final)
       first_last_path)
  | mSeq e f s1 s2 mes1 mfs2 => fun H1 H2 =>
    let '(ex_intro _ elast (conj elast_final efirst_last_path))
     := regex_match_to_path e i s1 next first mes1
        (fun lt A => H1 lt (LetterSet.S.union_2 _ A))
        (fun lt1 lt2 A => H2 lt1 lt2
         (Letter2Set.S.union_2 _ (Letter2Set.S.union_2 _ A))) in
    let '(ex_intro _ flast (conj flast_final ffirst_last_path))
     := regex_match_to_path f (annotate_helper i e).(snd) s2 next elast mfs2
        (fun lt lt_in_pf => Admit(* either (s1 is empty, l e = true, and elast = first) or elast is in d e *))
        (fun lt1 lt2 A => H2 lt1 lt2
         (Letter2Set.S.union_2 _ (Letter2Set.S.union_3 _ A))) in
    ex_intro _ flast (conj
      Admit(* finals_ad of Seq *)
      (NFA_path_compose _ s1 s2 _ _ _ efirst_last_path ffirst_last_path))
  | mStar_emp e => fun H1 H2 =>
    ex_intro _ first (conj (if_l_first_final (Star e) _ _ eq_refl) eq_refl)
  | mStar_more e s1 s2 mes1 mses2 => fun H1 H2 =>
    let '(ex_intro _ elast (conj elast_final efirst_last_path))
     := regex_match_to_path e i s1 next first mes1 H1
        (fun lt1 lt2 A => H2 lt1 lt2 (Letter2Set.S.union_2 _ A)) in
    let '(ex_intro _ selast (conj selast_final sefirst_last_path))
     := regex_match_to_path (Star e) i s2 next elast mses2
        Admit(* use f transitions *)
        H2 in
    ex_intro _ selast (conj
      Admit(* finals_ad of Star *)
      (NFA_path_compose _ s1 s2 _ _ _ efirst_last_path sefirst_last_path))
  end.

(* This is the hard one *)
Definition regex_match_path_from_zero_iff
  : forall r s, regex_match r s <->
    exists last : state,
    StateSet.mem last (finals_d (annotate r) 0) = true /\
    NFA_path (compile r).(next) s 0 last :=
  fun r s => conj
    (fun m => regex_match_to_path r 1 s
      (compile r).(next) 0 m
      Admit(* transitions to all first letters *)
      Admit(* transitions on all of f *))
    Admit(* reverse direction: induction on regex? *).

(* easy *)
Axiom compiled_NFA_path_zero_iff
  : forall r s,
    (exists last : state,
     StateSet.mem last (compile r).(finals) = true /\
     NFA_path (compile r).(next) s 0 last)
    <->
    NFA_path_accept (compile r) s.

(* easy *)
Axiom NFA_accept_path_iff
  : forall n s, NFA_path_accept n s <-> accept n s = true.

(* prove this without any axioms, then we have succeeded. *)
Definition Glushkov_correct : Glushkov_is_correct :=
  fun r s =>
  iff_trans (iff_trans
  (regex_match_path_from_zero_iff r s)
  (compiled_NFA_path_zero_iff r s))
  (NFA_accept_path_iff (compile r) s)
.
