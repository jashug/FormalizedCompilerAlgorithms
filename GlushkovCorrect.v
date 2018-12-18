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
  | mChar : forall cs c, CharSet.In c cs ->
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
      StateSet.In mid (find_default (next first) c) /\
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
  StateSet.In first n.(start) /\
  StateSet.In last n.(finals) /\
  NFA_path n.(next) s first last.

Fixpoint fold_left_inc {A B} {P : A -> Prop}
  (f : A -> B -> A) (l : list B) (i : A)
  (IH : forall a b, P a -> P (f a b)) (IH2 : P i)
  : P (fold_left f l i)
  := match l with
     | nil => IH2
     | cons b l' => fold_left_inc f l' (f i b) IH (IH i b IH2)
     end.
Fixpoint fold_left_inc_in {A B} {P : A -> Prop} {e : B -> B -> Prop}
  (f : A -> B -> A) (l : list B) (i : A)
  (IH : forall a b, P a -> P (f a b)) (b : B)
  (IH2 : forall a y, e b y -> P (f a y))
  (H : InA e b l) : P (fold_left f l i)
  := match H in InA _ _ l return P (fold_left f l i) with
     | InA_cons_hd l H => fold_left_inc _ _ _ IH (IH2 _ _ H)
     | InA_cons_tl y H' => fold_left_inc_in f _ _ IH b IH2 H'
     end.

(* Definition string_app_eq_emp_split (s1 s2 : string)
  : (s1 ++ s2)%string = EmptyString -> s1 = EmptyString /\ s2 = EmptyString
  := match s1 with
     | EmptyString => fun H => conj eq_refl H
     | String _ _ => fun (H : String _ _ = EmptyString) => ltac:(congruence)
     end. *)

(* Fixpoint match_emp_l r i s (m : regex_match r s)
  : s = EmptyString -> l (annotate_helper i r).(fst) = true
  := match m in regex_match r s
     return s = EmptyString -> l (annotate_helper i r).(fst) = true
     with
     | mEps | mStar_more _ _ _ _ _ | mStar_emp _ => fun _ => eq_refl
     | mChar cs c _ => fun X => ltac:(congruence)
     | mAltl e _ s me => fun H => orb_true_intro _ _
       (or_introl (match_emp_l e i s me H))
     | mAltr _ f s mf => fun H => orb_true_intro _ _
       (or_intror (match_emp_l f _ s mf H))
     | mSeq e f s1 s2 mes1 mfs2 => fun H =>
       let '(conj H1 H2) := string_app_eq_emp_split s1 s2 H in
       andb_true_intro (conj
         (match_emp_l e i s1 mes1 H1)
         (match_emp_l f _ s2 mfs2 H2))
     end. *)

Definition finals_d r first : StateSet.t :=
  if l r then StateSet.add first (positions (d r))
  else positions (d r).

Definition if_l_first_final r i first (ar := (annotate_helper i r).(fst))
  : l ar = true ->
    StateSet.In first (finals_d (annotate_helper i r).(fst) first)
  := fun H => match eq_sym H in _ = b
     return StateSet.In first (if b then _ else _)
     with eq_refl => StateSet.add_1 _ eq_refl end.
Definition d_in_finals r i first (ar := (annotate_helper i r).(fst))
  : forall lt, LetterSet.S.In lt (d ar) ->
    StateSet.In lt.(snd) (finals_d (annotate_helper i r).(fst) first)
  := fun lt H =>
     let H' : StateSet.In lt.(snd) (positions (d ar)) :=
       match eq_sym (LetterSet.S.fold_1 (d ar) _ _) in _ = ss
       return StateSet.In lt.(snd) ss with eq_refl =>
         fold_left_inc_in (P := StateSet.In lt.(snd)) _ _ _
           (fun ss lt H => StateSet.add_2 _ H)
           _ (fun ss lt e => StateSet.add_1 ss (eq_sym e))
           (LetterSet.S.elements_1 H)
       end in
     match l ar as b
     return StateSet.In lt.(snd) (if b then _ else _)
     with true => StateSet.add_2 _ H' | false => H' end.

Axiom Admit : forall {T}, T.

Axiom LetterSet_prod_inc : forall lt1 lt2 ls1 ls2,
  LetterSet.S.In lt1 ls1 -> LetterSet.S.In lt2 ls2 ->
  Letter2Set.S.In (lt1 , lt2) (ls1 <*> ls2).

Definition regex_match_to_path_result r i s next first : Prop :=
  let ar := (annotate_helper i r).(fst) in
  (l ar = true /\ EmptyString = s) \/
  (exists lt : Letter.t,
   LetterSet.S.In lt (d ar) /\
   NFA_path next s first lt.(snd)).

Definition regex_match_to_path_result_weaken r1 r2 i1 i2 s next first
  : let ar1 := (annotate_helper i1 r1).(fst) in
    let ar2 := (annotate_helper i2 r2).(fst) in
    (l ar1 = true -> l ar2 = true) ->
    (forall lt, LetterSet.S.In lt (d ar1) -> LetterSet.S.In lt (d ar2)) ->
    regex_match_to_path_result r1 i1 s next first ->
    regex_match_to_path_result r2 i2 s next first
  := fun H1 H2 B => match B with
     | or_introl (conj r1_emp s_emp) => or_introl (conj (H1 r1_emp) s_emp)
     | or_intror (ex_intro _ lt (conj lt_d path)) => or_intror
       (ex_intro _ lt (conj (H2 lt lt_d) path))
     end.

Axiom string_app_emp : forall s : string, s = (s ++ "")%string.

Definition regex_match_to_path_result_compose :
  forall r1 r2 r3 i1 i2 i3 s1 s2 next first,
  let ar1 := (annotate_helper i1 r1).(fst) in
  let ar2 := (annotate_helper i2 r2).(fst) in
  let ar3 := (annotate_helper i3 r3).(fst) in
  (l ar1 = true -> l ar2 = true -> l ar3 = true) ->
  (forall lt, l ar2 = true -> LetterSet.S.In lt (d ar1) ->
   LetterSet.S.In lt (d ar3)) ->
  (forall lt, LetterSet.S.In lt (d ar2) -> LetterSet.S.In lt (d ar3)) ->
  (l ar1 = true -> regex_match_to_path_result r2 i2 s2 next first) ->
  (forall lt, LetterSet.S.In lt (d ar1) ->
   regex_match_to_path_result r2 i2 s2 next lt.(snd)) ->
  regex_match_to_path_result r1 i1 s1 next first ->
  regex_match_to_path_result r3 i3 (s1 ++ s2) next first :=
  fun r1 r2 r3 i1 i2 i3 s1 s2 next first H1 H2 H3 A1 A2 B =>
  match B with
  | or_introl (conj r1_emp s1_emp) => match s1_emp with eq_refl =>
    let B2 : regex_match_to_path_result r2 i2 s2 next first := A1 r1_emp in
    regex_match_to_path_result_weaken r2 r3 i2 i3 s2 next first
      (H1 r1_emp) H3 B2
    end
  | or_intror (ex_intro _ lt (conj lt_d path1)) =>
    let B2 : regex_match_to_path_result r2 i2 s2 next lt.(snd) := A2 lt lt_d in
    match B2 with
    | or_introl (conj r2_emp s2_emp) => match s2_emp with eq_refl =>
      match string_app_emp s1 in _ = s1'
      return regex_match_to_path_result r3 i3 s1' next first
      with eq_refl => or_intror (ex_intro _ lt (conj
        (H2 lt r2_emp lt_d)
        path1)) : regex_match_to_path_result r3 i3 s1 next first
      end end
    | or_intror (ex_intro _ lt2 (conj lt2_d path2)) =>
      or_intror (ex_intro _ lt2 (conj
        (H3 lt2 lt2_d)
        (NFA_path_compose _ _ _ _ _ _ path1 path2)))
    end
  end.

(* forward direction *)
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
    regex_match_to_path_result r i s next first :=
  match m
  with
  | mEps => fun H1 H2 => or_introl (conj eq_refl eq_refl)
  | mChar cs c c_in_cs => fun H1 H2 =>
    let A1 : LetterSet.S.In (cs , i) (d (annotate_helper i (Char cs)).(fst))
     := LetterSet.S.singleton_2 eq_refl in
    let A2 : StateSet.In i (find_default (next first) c)
     := H1 (cs , i) A1 c c_in_cs in
    or_intror (ex_intro _ (cs , i) (conj A1 (ex_intro _ i (conj A2 eq_refl))))
  | mAltl e f s mes => fun H1 H2 =>
    let Be : regex_match_to_path_result e i s next first
     := regex_match_to_path e i s next first mes
        (fun lt A => H1 lt (LetterSet.S.union_2 _ A))
        (fun lt1 lt2 A => H2 lt1 lt2 (Letter2Set.S.union_2 _ A)) in
    regex_match_to_path_result_weaken e (Alt e f) i i s next first
    (fun e_emp => orb_true_intro _ _ (or_introl e_emp))
    (fun lt lt_d => LetterSet.S.union_2 _ lt_d)
    Be
  | mAltr e f s mfs => fun H1 H2 =>
    let Bf : regex_match_to_path_result f _ s next first
     := regex_match_to_path f (annotate_helper i e).(snd) s next first mfs
        (fun lt A => H1 lt (LetterSet.S.union_3 _ A))
        (fun lt1 lt2 A => H2 lt1 lt2 (Letter2Set.S.union_3 _ A)) in
    regex_match_to_path_result_weaken f (Alt e f) _ i s next first
    (fun f_emp => orb_true_intro _ _ (or_intror f_emp))
    (fun lt lt_d => LetterSet.S.union_3 _ lt_d)
    Bf
  | mSeq e f s1 s2 mes1 mfs2 => fun H1 H2 =>
    let Be : regex_match_to_path_result e i s1 next first
     := regex_match_to_path e i s1 next first mes1
        (fun lt A => H1 lt (LetterSet.S.union_2 _ A))
        (fun lt1 lt2 A => H2 lt1 lt2
         (Letter2Set.S.union_2 _ (Letter2Set.S.union_2 _ A))) in
    regex_match_to_path_result_compose e f (Seq e f) i _ i s1 s2 next first
      (fun e_emp f_emp => andb_true_intro (conj e_emp f_emp))
      (fun lt f_emp lt_de => LetterSet.S.union_2 _
       match eq_sym f_emp in _ = b return LetterSet.S.In _ (if b then _ else _)
       with eq_refl => lt_de end)
      (fun lt lt_df => LetterSet.S.union_3 _ lt_df)
      (fun e_emp =>
        regex_match_to_path f _ s2 next first mfs2
            (fun lt lt_in_pf => H1 lt (LetterSet.S.union_3 _
             match eq_sym e_emp in _ = b
             return LetterSet.S.In lt (if b then _ else _)
             with eq_refl => lt_in_pf end))
            (fun lt1 lt2 A => H2 lt1 lt2
             (Letter2Set.S.union_2 _ (Letter2Set.S.union_3 _ A))))
      (fun elast elast_d =>
        regex_match_to_path f _ s2 next elast.(snd) mfs2
            (fun lt lt_in_pf => H2 elast lt (Letter2Set.S.union_3 _
             (LetterSet_prod_inc _ _ _ _ elast_d lt_in_pf)))
            (fun lt1 lt2 A => H2 lt1 lt2
             (Letter2Set.S.union_2 _ (Letter2Set.S.union_3 _ A))))
      Be
  | mStar_emp e => fun H1 H2 => or_introl _ (conj eq_refl eq_refl)
  | mStar_more e s1 s2 mes1 mses2 => fun H1 H2 =>
    let Be : regex_match_to_path_result e i s1 next first
     := regex_match_to_path e i s1 next first mes1 H1
        (fun lt1 lt2 A => H2 lt1 lt2 (Letter2Set.S.union_2 _ A)) in
    regex_match_to_path_result_compose
      e (Star e) (Star e) i i i s1 s2 next first
      (fun e_emp f_emp => eq_refl)
      (fun lt se_emp lt_de => lt_de)
      (fun lt lt_dse => lt_dse)
      (fun e_emp => regex_match_to_path (Star e) _ s2 next first mses2 H1 H2)
      (fun elast elast_d =>
        regex_match_to_path (Star e) _ s2 next elast.(snd) mses2
          (fun lt lt_in_pf => H2 elast lt (Letter2Set.S.union_3 _
           (LetterSet_prod_inc _ _ _ _ elast_d lt_in_pf)))
          H2)
      Be
  end.

Definition regex_match_to_path' r s (m : regex_match r s)
  : exists last : state,
    StateSet.In last (finals_d (annotate r) 0) /\
    NFA_path (compile r).(next) s 0 last
  := let B :=
       regex_match_to_path r 1 s (compile r).(next) 0 m
       Admit(* transitions to all first letters *)
       Admit(* transitions on all of f *)
     in match B with
     | or_introl (conj r_emp s_emp) => match s_emp with eq_refl =>
         ex_intro _ 0 (conj (if_l_first_final r 1 0 r_emp) eq_refl)
       end
     | or_intror (ex_intro _ lt (conj lt_d path)) =>
       ex_intro _ lt.(snd) (conj (d_in_finals r 1 0 lt lt_d) path)
     end.

(* This is the hard one *)
Definition regex_match_path_from_zero_iff
  : forall r s, regex_match r s <->
    exists last : state,
    StateSet.In last (finals_d (annotate r) 0) /\
    NFA_path (compile r).(next) s 0 last :=
  fun r s => conj
    (regex_match_to_path' r s)
    Admit(* reverse direction: induction on regex? *).

(* easy *)
Axiom compiled_NFA_path_zero_iff
  : forall r s,
    (exists last : state,
     StateSet.In last (compile r).(finals) /\
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
