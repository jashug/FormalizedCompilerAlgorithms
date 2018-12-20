Set Primitive Projections.
Set Uniform Inductive Parameters.
Unset Universe Minimization ToSet.

From Coq Require Import String Ascii ZArith.
From Coq Require Import FSets FMaps FMapAVL OrderedTypeEx.

Open Scope Z_scope.

From CompilerOrg Require Import NFA Regex.
Import LetterSet.Notation Letter2Set.Notation.

(* p should match the left hand side of H and not the right, gives any type *)
Local Notation "'discriminate' p H" :=
  (match H in _ = x return match x with p => True | _ => _ end
   with eq_refl => I end)
  (at level 10, p pattern).

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

(* ---------------------- Linear languages ---------------------- *)

Axiom Admit : forall {T}, T.

Fixpoint linear_inner
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst))
  (s : string) (first : Letter.t) : Prop :=
  match s with
  | EmptyString => LetterSet.S.In first (d ar)
  | String c s => exists mid : Letter.t,
    Letter2Set.S.In (first , mid) (f_ ar) /\
    linear_inner r i s mid
  end.

Definition linear_match
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst))
  (s : string) : Prop :=
  match s with
  | EmptyString => l ar = true
  | String c s => exists mid : Letter.t,
    LetterSet.S.In mid (p ar) /\
    linear_inner r i s mid
  end.

(* Lemmas showing that linear_match is closed under regular operations *)

Definition linear_match_emp_dest i s : ~ linear_match Empty i s
  := match s return linear_match Empty i s -> False with
     | EmptyString => fun H : false = true => discriminate false H
     | String c s => fun '(ex_intro _ _ (conj H _)) => LetterSet.S.empty_1 H
     end.

Definition linear_match_eps_intro i : linear_match Eps i EmptyString :=
  eq_refl.
Definition linear_match_eps_dest i s :
  linear_match Eps i s -> EmptyString = s :=
  Admit.

Definition linear_match_char_intro i cs c (c_in_cs : CharSet.In c cs) :
  linear_match (Char cs) i (String c EmptyString) :=
  ex_intro _ (cs , i) (conj (LetterSet.S.singleton_2 eq_refl)
                            (LetterSet.S.singleton_2 eq_refl)).
Definition linear_match_char_dest i cs s :
  linear_match (Char cs) i s ->
  exists c, CharSet.In c cs /\ String c EmptyString = s :=
  Admit.

Definition linear_match_alt_introl e f i s :
  linear_match e i s -> linear_match (Alt e f) i s :=
  Admit.
Definition linear_match_alt_intror e f i s :
  linear_match f (annotate_helper i e).(snd) s -> linear_match (Alt e f) i s :=
  Admit.
Definition linear_match_alt_dest e f i s :
  linear_match (Alt e f) i s ->
  linear_match e i s \/ linear_match f (annotate_helper i e).(snd) s :=
  Admit.

Definition linear_match_seq_intro e f i s1 s2 :
  linear_match e i s1 -> linear_match f (annotate_helper i e).(snd) s2 ->
  linear_match (Seq e f) i (s1 ++ s2) :=
  Admit.
Definition linear_match_seq_dest e f i s :
  linear_match (Seq e f) i s ->
  exists s1 s2, (s1 ++ s2)%string = s /\
  (linear_match e i s1 /\ linear_match f (annotate_helper i e).(snd) s2) :=
  Admit.

Definition linear_match_star_intro_emp e i :
  linear_match (Star e) i EmptyString :=
  eq_refl.
Definition linear_match_star_intro_more e i s1 s2 :
  linear_match e i s1 -> linear_match (Star e) i s2 ->
  linear_match (Star e) i (s1 ++ s2) :=
  Admit.
Definition linear_match_star_ind e i s
  (P : string -> Prop)
  (IH_emp : P EmptyString)
  (IH_more : forall s1 s2, linear_match e i s1 -> P s2 -> P (s1 ++ s2)%string) :
  linear_match (Star e) i s -> P s :=
  Admit.

Fixpoint regex_match_to_linear_match (r : regex CharSet.t) (i : Z) (s : string)
  (m : regex_match r s) : linear_match r i s :=
  match m with
  | mEps => linear_match_eps_intro i
  | mChar cs c c_in_cs => linear_match_char_intro i cs c c_in_cs
  | mAltl e f s mes => linear_match_alt_introl e f i s
    (regex_match_to_linear_match e _ s mes)
  | mAltr e f s mfs => linear_match_alt_intror e f i s
    (regex_match_to_linear_match f _ s mfs)
  | mSeq e f s1 s2 mes1 mfs2 => linear_match_seq_intro e f i s1 s2
    (regex_match_to_linear_match e _ s1 mes1)
    (regex_match_to_linear_match f _ s2 mfs2)
  | mStar_emp e => linear_match_star_intro_emp e i
  | mStar_more e s1 s2 mes1 mses2 => linear_match_star_intro_more e i s1 s2
    (regex_match_to_linear_match e _ s1 mes1)
    (regex_match_to_linear_match (Star e) _ s2 mses2)
  end.

Fixpoint linear_match_to_regex_match (r : regex CharSet.t) (i : Z) (s : string)
  : linear_match r i s -> regex_match r s :=
  match r with
  | Empty => fun H => match linear_match_emp_dest i s H with end
  | Eps => fun H => match linear_match_eps_dest i s H with eq_refl => mEps end
  | Char cs => fun H => match linear_match_char_dest i cs s H with
    | ex_intro _ c (conj c_in_cs s_is_c) => match s_is_c with eq_refl =>
      mChar cs c c_in_cs
    end end
  | Alt e f => fun H => match linear_match_alt_dest e f i s H with
    | or_introl mes => mAltl e f s (linear_match_to_regex_match e _ s mes)
    | or_intror mfs => mAltr e f s (linear_match_to_regex_match f _ s mfs)
    end
  | Seq e f => fun H => match linear_match_seq_dest e f i s H with
    | ex_intro _ s1 (ex_intro _ s2 (conj s_eq (conj mes1 mfs2))) =>
      match s_eq with eq_refl =>
        mSeq e f s1 s2
        (linear_match_to_regex_match e _ s1 mes1)
        (linear_match_to_regex_match f _ s2 mfs2)
    end end
  | Star e => linear_match_star_ind e i s (regex_match (Star e))
    (mStar_emp e)
    (fun s1 s2 mes1 => mStar_more e s1 s2
     (linear_match_to_regex_match e _ s1 mes1))
  end.

(* ---------------------- Proof below ---------------------- *)

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
     | String _ _ => fun (H : String _ _ = EmptyString) =>
       discriminate (String _ _) H
     end. *)

(* Fixpoint match_emp_l r i s (m : regex_match r s)
  : s = EmptyString -> l (annotate_helper i r).(fst) = true
  := match m in regex_match r s
     return s = EmptyString -> l (annotate_helper i r).(fst) = true
     with
     | mEps | mStar_more _ _ _ _ _ | mStar_emp _ => fun _ => eq_refl
     | mChar cs c _ => fun X => discriminate (String _ _) X
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

Definition LetterSet_prod_inc lt1 lt2 ls1 ls2 :
  LetterSet.S.In lt1 ls1 -> LetterSet.S.In lt2 ls2 ->
  Letter2Set.S.In (lt1 , lt2) (ls1 <*> ls2) :=
  fun H1 H2 =>
  match eq_sym (LetterSet.S.fold_1 ls1 _ _) in _ = res1
  return Letter2Set.S.In (lt1 , lt2) res1
  with eq_refl =>
    fold_left_inc_in (P := Letter2Set.S.In (lt1 , lt2)) _ _ _
    (fun s1 _ H => Letter2Set.S.union_3 _ H)
    _ (fun _ lt1' lt1eq => Letter2Set.S.union_2 _
      match eq_sym (LetterSet.S.fold_1 ls2 _ _) in _ = res2
      return Letter2Set.S.In (lt1 , lt2) res2
      with eq_refl =>
        fold_left_inc_in (P := Letter2Set.S.In (lt1 , lt2)) _ _ _
        (fun _ _ H => Letter2Set.S.union_3 _ H)
        _ (fun _ lt2' lt2eq => Letter2Set.S.union_2 _
           (Letter2Set.S.singleton_2 (x := (lt1' , lt2')) (y := (lt1 , lt2))
            (conj (eq_sym lt1eq) (eq_sym lt2eq))))
        (LetterSet.S.elements_1 H2)
      end)
    (LetterSet.S.elements_1 H1)
  end.

(* Consider changing around to exists lt, NFA_path /\ (empty \/ in d) *)
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

Fixpoint string_app_emp (s : string) : s = (s ++ "")%string :=
  match s with
  | EmptyString => eq_refl
  | String c s' => f_equal (String c) (string_app_emp s')
  end.

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

(* definable in terms of finals_iff below *)
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

(* characterize final states and transitions: *)
(* more annoying than anything: make sure these work for the reverse direction
   before proving (the directions are reversed from goal) *)
Axiom finals_iff : forall r state,
  StateSet.In state (compile r).(finals) <->
  (exists cs, LetterSet.S.In (cs , state) (d (annotate r))) \/
  (l (annotate r) = true /\ state = 0).

Axiom transitions_iff : forall r st1 st2 c,
  StateSet.In st2 (find_default ((compile r).(next) st1) c) <->
  (exists cs1 cs2,
   Letter2Set.S.In ((cs1 , st1) , (cs2 , st2)) (f_ (annotate r)) /\
   CharSet.In c cs2) \/
  (exists cs2,
   LetterSet.S.In (cs2 , st2) (p (annotate r)) /\
   CharSet.In c cs2 /\
   st1 = 0).

(* definable from transitions_iff *)
(* Definition compile_all_first_letters r
    lt (H1 : LetterSet.S.In lt (p (annotate r)))
    c (H2 : CharSet.In c lt.(fst))
  : StateSet.In lt.(snd) (find_states c (compile r) 0) :=
  match eq_sym (StateMap.find_1 (StateMap.add_1 _ _ eq_refl)) in _ = found
  return
    StateSet.In lt.(snd)
    (match CharMap.find c
     (match found with
      | Some ss => flatten_transitions ss
      | None => CharMap.empty _
      end)
     with Some ss => ss | None => StateSet.empty end)
  with eq_refl =>
    Admit
    : StateSet.In (snd lt)
      match CharMap.find c
        (flatten_transitions (transition_map_of_letter_set (p (annotate r))))
      with
      | Some ss => ss
      | None => StateSet.empty
      end
  end. *)
(* as an example *)
Definition compile_all_first_letters r
    lt (H1 : LetterSet.S.In lt (p (annotate r)))
    c (H2 : CharSet.In c lt.(fst))
  : StateSet.In lt.(snd) (find_states c (compile r) 0) :=
  proj2 (transitions_iff r 0 lt.(snd) c) (or_intror
    (ex_intro _ lt.(fst) (conj
      (match lt
       return LetterSet.S.In lt _ -> LetterSet.S.In (fst lt , snd lt) _
       with pair cs st => fun H => H end H1)
      (conj H2 eq_refl)))).

Definition regex_match_to_path' r s (m : regex_match r s)
  : exists last : state,
    StateSet.In last (compile r).(finals) /\
    NFA_path (compile r).(next) s 0 last
  := let B :=
       regex_match_to_path r 1 s (compile r).(next) 0 m
       (compile_all_first_letters r)
       Admit(* transitions on all of f *)
     in match B with
     | or_introl (conj r_emp s_emp) => match s_emp with eq_refl =>
         ex_intro _ 0 (conj (if_l_first_final r 1 0 r_emp) eq_refl)
       end
     | or_intror (ex_intro _ lt (conj lt_d path)) =>
       ex_intro _ lt.(snd) (conj (d_in_finals r 1 0 lt lt_d) path)
     end.

(* ---------------------- NFA -> regex ---------------------- *)

Definition in_range (r : regex CharSet.t) (i : Z) (s : state) :=
  i <= s /\ s < (annotate_helper i r).(snd).

Fixpoint NFA_path_by_f_to_d
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst)) (s : string)
  (next : state -> CharMap.t StateSet.t) (first : Letter.t) : Prop :=
  match s with
  | EmptyString => LetterSet.S.In first (d ar)
  | String c s => exists mid : Letter.t,
    StateSet.In mid.(snd) (find_default (next first.(snd)) c) /\
    Letter2Set.S.In (first , mid) (f_ ar) /\
    NFA_path_by_f_to_d r i s next mid
  end.

(* This defines a linear language *)
Definition faithful_NFA_path
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst)) (s : string)
  (next : state -> CharMap.t StateSet.t) (first : state) : Prop :=
  match s with
  | EmptyString => l ar = true
  | String c s => exists mid : Letter.t,
    StateSet.In mid.(snd) (find_default (next first) c) /\
    LetterSet.S.In mid (p ar) /\
    NFA_path_by_f_to_d r i s next mid
  end.

Fixpoint path_to_regex_match (r : regex CharSet.t) (i : Z) (s : string)
    (next : state -> CharMap.t StateSet.t) (first : state)
    :
    (* have steps from first land in p, and successive steps land in f, for
       steps in_range *)
    let ar := (annotate_helper i r).(fst) in
    regex_match_to_path_result r i s next first ->
    (* restrict right branch to be nonempty and have all following nodes in_range *)
    (* or move the step condition here? *)
    regex_match r s :=
  match r with
  | Empty => Admit(* impossible precondition *)
  | Eps => Admit(* s must be empty, since d is empty *)
  | Char cs => Admit(* can't be empty, since not l, so path ending in d, transitions give exactly on step *)
  | Alt e f => Admit(* if empty, that's fine. otherwise, look at first step, and discriminate by that *)
  | Seq e f => Admit(* split by where first enters f (uses a p e <*> d f transition *)
  | Star e => Admit(* split where uses a p e <*> d e transition *)
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

(* for reverse, induct on regex, splitting path by where it hits d *)

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
