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

Fixpoint string_app_emp (s : string) : s = (s ++ "")%string :=
  match s with
  | EmptyString => eq_refl
  | String c s' => f_equal (String c) (string_app_emp s')
  end.

(* The definition of equality on letters is too weak to use directly *)
Definition In_p {Γ} (r : regex Γ) (x : Γ) : Prop :=
  let fix In_p r := match r with
  | Empty | Eps => False
  | Char y => y = x
  | Alt e f => In_p e \/ In_p f
  | Seq e f => In_p e \/ (l e = true /\ In_p f)
  | Star e => In_p e
  end
  in In_p r.
Definition In_d {Γ} (r : regex Γ) (x : Γ) : Prop :=
  let fix In_d r := match r with
  | Empty | Eps => False
  | Char y => y = x
  | Alt e f => In_d e \/ In_d f
  | Seq e f => (l f = true /\ In_d e) \/ In_d f
  | Star e => In_d e
  end
  in In_d r.
Definition In_f {Γ} (r : regex Γ) (x1 x2 : Γ) : Prop :=
  let fix In_f r := match r with
  | Empty | Eps | Char _ => False
  | Alt e f => In_f e \/ In_f f
  | Seq e f => (In_f e \/ In_f f) \/ (In_d e x1 /\ In_p f x2)
  | Star e => In_f e \/ (In_d e x1 /\ In_p e x2)
  end
  in In_f r.

Definition In_regex {Γ} (r : regex Γ) (x : Γ) : Prop :=
  let fix In r := match r with
  | Empty | Eps => False
  | Char y => y = x
  | Alt e f | Seq e f => In e \/ In f
  | Star e => In e
  end
  in In r.

Fixpoint In_p_all {Γ} {r : regex Γ} {x : Γ} : In_p r x -> In_regex r x :=
  match r with
  | Empty | Eps => fun H => match H with end
  | Char y => fun H => H
  | Alt e f => fun H => match H with
    | or_introl H => or_introl (In_p_all H)
    | or_intror H => or_intror (In_p_all H)
    end
  | Seq e f => fun H => match H with
    | or_introl H => or_introl (In_p_all H)
    | or_intror (conj _ H) => or_intror (In_p_all H)
    end
  | Star e => In_p_all (r := e)
  end.
Fixpoint In_d_all {Γ} {r : regex Γ} {x : Γ} : In_d r x -> In_regex r x :=
  match r with
  | Empty | Eps => fun H => match H with end
  | Char y => fun H => H
  | Alt e f => fun H => match H with
    | or_introl H => or_introl (In_d_all H)
    | or_intror H => or_intror (In_d_all H)
    end
  | Seq e f => fun H => match H with
    | or_introl (conj _ H) => or_introl (In_d_all H)
    | or_intror H => or_intror (In_d_all H)
    end
  | Star e => In_d_all (r := e)
  end.
Fixpoint In_f_all {Γ} {r : regex Γ} {x y : Γ} :
  In_f r x y -> In_regex r x /\ In_regex r y :=
  match r return In_f r x y -> In_regex r x /\ In_regex r y with
  | Empty | Eps | Char _ => fun H => match H with end
  | Alt e f => fun H => match H with
    | or_introl H => let '(conj Hx Hy) := In_f_all H in
      conj (or_introl Hx) (or_introl Hy)
    | or_intror H => let '(conj Hx Hy) := In_f_all H in
      conj (or_intror Hx) (or_intror Hy)
    end
  | Seq e f => fun H => match H with
    | or_introl (or_introl H) => let '(conj Hx Hy) := In_f_all H in
      conj (or_introl Hx) (or_introl Hy)
    | or_introl (or_intror H) => let '(conj Hx Hy) := In_f_all H in
      conj (or_intror Hx) (or_intror Hy)
    | or_intror (conj Hx Hy) =>
      conj (or_introl (In_d_all Hx)) (or_intror (In_p_all Hy))
    end
  | Star e => fun H => match H with
    | or_introl H => In_f_all H
    | or_intror (conj Hx Hy) => conj (In_d_all Hx) (In_p_all Hy)
    end
  end.

Fixpoint annotate_increasing {Γ} (r : regex Γ) i :
  i <= (annotate_helper i r).(snd) :=
  match r with
  | Empty | Eps => Z.le_refl i
  | Char y => Z.le_succ_diag_r i
  | Alt e f | Seq e f => Z.le_trans _ _ _
    (annotate_increasing e _) (annotate_increasing f _)
  | Star e => annotate_increasing e i
  end.
Fixpoint In_bounded {Γ} (r : regex Γ) i x :
  In_regex (annotate_helper i r).(fst) x ->
  i <= x.(snd) /\ ~ (annotate_helper i r).(snd) <= x.(snd) :=
  match r return In_regex (annotate_helper i r).(fst) x ->
  i <= x.(snd) /\ ~ (annotate_helper i r).(snd) <= x.(snd) with
  | Empty | Eps => fun H => match H with end
  | Char y => fun H => match H with eq_refl =>
      conj (Z.le_refl i) (Z.nle_succ_diag_l i)
    end
  | Alt e f | Seq e f => fun H => match H with
    | or_introl H => let '(conj HL HR) := In_bounded e i x H in
      conj HL (fun HR' => HR (Z.le_trans _ _ _ (annotate_increasing f _) HR'))
    | or_intror H => let '(conj HL HR) := In_bounded f _ x H in
      conj (Z.le_trans _ _ _ (annotate_increasing e i) HL) HR
    end
  | Star e => In_bounded e i x
  end.
Definition In_annotate_exclusion {A Γ} {e f : regex Γ} {i x}
  (ae := (annotate_helper i e).(fst))
  (af := (annotate_helper (annotate_helper i e).(snd) f).(fst)) :
  In_regex ae x -> In_regex af x -> A :=
  fun H1 H2 => match
  match Z.le_decidable (annotate_helper i e).(snd) x.(snd) return False with
  | or_introl x_past_e => proj2 (In_bounded e i x H1) x_past_e
  | or_intror x_not_past_e => x_not_past_e (proj1 (In_bounded f _ x H2))
  end
  with end.

Inductive linear_step
  (c : ascii) (P : Letter.t -> Prop) (Q : Letter.t -> Prop) : Prop :=
| step : forall mid, CharSet.In c mid.(fst) -> P mid -> Q mid -> linear_step.
Arguments step {c P Q} mid _ _ _.

Fixpoint linear_inner
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst))
  (s : string) (first : Letter.t) : Prop :=
  match s with
  | EmptyString => In_d ar first
  | String c s => linear_step c (In_f ar first) (linear_inner r i s)
  end.

Definition linear_match
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst))
  (s : string) : Prop :=
  match s with
  | EmptyString => l ar = true
  | String c s => linear_step c (In_p ar) (linear_inner r i s)
  end.

(* Lemmas constructing linear_match *)

Definition linear_match_eps_intro i : linear_match Eps i EmptyString :=
  eq_refl.

Definition linear_match_char_intro i cs c (c_in_cs : CharSet.In c cs) :
  linear_match (Char cs) i (String c EmptyString) :=
  step (cs , i) c_in_cs eq_refl eq_refl.

(* matches are stable under language subsets *)
Definition linear_inner_weaken r1 r2 i1 i2
  (ar1 := (annotate_helper i1 r1).(fst)) (ar2 := (annotate_helper i2 r2).(fst))
  (IHd : forall lt, In_d ar1 lt -> In_d ar2 lt)
  (IHf : forall lt1 lt2, In_f ar1 lt1 lt2 -> In_f ar2 lt1 lt2)
  : forall s first, linear_inner r1 i1 s first -> linear_inner r2 i2 s first :=
  fix wk s first := match s with
  | EmptyString => IHd first
  | String c s => fun '(step mid c_in_mid first_mid_in_f rest) =>
    step mid c_in_mid (IHf first mid first_mid_in_f) (wk s mid rest)
  end.
Definition linear_match_weaken r1 r2 i1 i2
  (ar1 := (annotate_helper i1 r1).(fst)) (ar2 := (annotate_helper i2 r2).(fst))
  (IHl : l ar1 = true -> l ar2 = true)
  (IHp : forall lt, In_p ar1 lt -> In_p ar2 lt)
  (IHd : forall lt, In_d ar1 lt -> In_d ar2 lt)
  (IHf : forall lt1 lt2, In_f ar1 lt1 lt2 -> In_f ar2 lt1 lt2)
  : forall s, linear_match r1 i1 s -> linear_match r2 i2 s :=
  fun s => match s with
  | EmptyString => IHl
  | String c s => fun '(step mid c_in_mid mid_in_p rest) =>
    step mid c_in_mid (IHp mid mid_in_p)
    (linear_inner_weaken r1 r2 i1 i2 IHd IHf s mid rest)
  end.

Definition linear_match_alt_introl e f i s :
  linear_match e i s -> linear_match (Alt e f) i s :=
  linear_match_weaken e (Alt e f) _ _
  (fun le => orb_true_intro _ _ (or_introl le))
  (fun lt H => or_introl H) (fun lt H => or_introl H)
  (fun lt1 lt2 H => or_introl H) s.
Definition linear_match_alt_intror e f i s :
  linear_match f (annotate_helper i e).(snd) s -> linear_match (Alt e f) i s :=
  linear_match_weaken f (Alt e f) _ _
  (fun lf => orb_true_intro _ _ (or_intror lf))
  (fun lt H => or_intror H) (fun lt H => or_intror H)
  (fun lt1 lt2 H => or_intror H) s.

Definition linear_match_compose e f g i1 i2 i3 s1 s2
  (ae := (annotate_helper i1 e).(fst)) (af := (annotate_helper i2 f).(fst))
  (ag := (annotate_helper i3 g).(fst))
  (IHl : l ae && l af = true -> l ag = true)
  (IHp : forall lt, In_p ae lt \/ (l ae = true /\ In_p af lt) -> In_p ag lt)
  (IHd : forall lt, (l af = true /\ In_d ae lt) \/ In_d af lt -> In_d ag lt)
  (IHf : forall lt1 lt2, (In_f ae lt1 lt2 \/ In_f af lt1 lt2) \/
                         (In_d ae lt1 /\ In_p af lt2) -> In_f ag lt1 lt2) :
  linear_match e i1 s1 -> linear_match f i2 s2 ->
  linear_match g i3 (s1 ++ s2) :=
  match s1
  return
    linear_match e i1 s1 -> linear_match f i2 s2 ->
    linear_match g i3 (s1 ++ s2)
  with
  | EmptyString => fun e_emp => linear_match_weaken f g i2 i3
    (fun f_emp => IHl (andb_true_intro (conj e_emp f_emp)))
    (fun lt H => IHp lt (or_intror (conj e_emp H)))
    (fun lt H => IHd lt (or_intror H))
    (fun lt1 lt2 H => IHf lt1 lt2 (or_introl (or_intror H))) s2
  | String c1 s1 => fun '(step mid c_in_mid mid_in_pe rest1) mfs2 =>
    step mid c_in_mid (IHp mid (or_introl mid_in_pe))
    (match s2
     return linear_match f _ s2 -> linear_inner g i3 (s1 ++ s2) mid
     with
     | EmptyString => fun f_emp =>
       match string_app_emp s1 in _ = s1'
       return linear_inner g i3 s1' mid
       with eq_refl =>
         linear_inner_weaken e g _ _
         (fun lt H => IHd lt (or_introl (conj f_emp H)))
         (fun lt1 lt2 H => IHf lt1 lt2 (or_introl (or_introl H)))
         s1 mid rest1
       end
     | String c2 s2 => fun '(step mid2 c2_in_mid2 mid2_in_pf rest2) =>
       let fix rec s1 first
        : linear_inner e i1 s1 first ->
          linear_inner g i3 (s1 ++ String c2 s2) first
        := match s1 with
           | EmptyString => fun first_de =>
             step mid2 c2_in_mid2
             (IHf first mid2 (or_intror (conj first_de mid2_in_pf)))
             (linear_inner_weaken f g _ _
              (fun lt H => IHd lt (or_intror H))
              (fun lt1 lt2 H => IHf lt1 lt2 (or_introl (or_intror H)))
              s2 _ rest2)
           | String c s1 => fun '(step mid c_in_mid first_mid_in_fe rest) =>
             step mid c_in_mid
             (IHf first mid (or_introl (or_introl first_mid_in_fe)))
             (rec s1 mid rest)
           end in
       rec s1 mid rest1
     end mfs2)
  end.

Definition linear_match_seq_intro e f i s1 s2 :
  linear_match e i s1 -> linear_match f (annotate_helper i e).(snd) s2 ->
  linear_match (Seq e f) i (s1 ++ s2) :=
  linear_match_compose e f (Seq e f) _ _ _ s1 s2
  (fun H => H) (fun lt H => H) (fun lt H => H) (fun lt1 lt2 H => H).

Definition linear_match_star_intro_emp e i :
  linear_match (Star e) i EmptyString :=
  eq_refl.
Definition linear_match_star_intro_more e i s1 s2 :
  linear_match e i s1 -> linear_match (Star e) i s2 ->
  linear_match (Star e) i (s1 ++ s2) :=
  linear_match_compose e (Star e) (Star e) i i i s1 s2
  (fun _ => eq_refl)
  (fun lt H => match H with or_introl H | or_intror (conj _ H) => H end)
  (fun lt H => match H with or_introl (conj _ H) | or_intror H => H end)
  (fun lt1 lt2 H => match H with
   | or_introl (or_introl H) => or_introl H
   | or_introl (or_intror H) => H
   | or_intror H => or_intror H
   end).

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

(* lemmas destructing linear_match *)

Definition linear_match_emp_dest i s : ~ linear_match Empty i s
  := match s return linear_match Empty i s -> False with
     | EmptyString => fun H : false = true => discriminate false H
     | String c s => fun '(step _ _ H _) =>
       match H with end
     end.

Definition linear_match_eps_dest i s :
  linear_match Eps i s -> EmptyString = s :=
  match s with
  | EmptyString => fun _ => eq_refl
  | String c s => fun '(step mid _ H _) => match H with end
  end.

Definition linear_match_char_dest i cs s :
  linear_match (Char cs) i s ->
  exists c, CharSet.In c cs /\ String c EmptyString = s :=
  match s with
  | EmptyString => fun H => discriminate false H
  | String c EmptyString =>
    fun '(step mid c_in_mid mid_in_p rest) =>
    ex_intro _ c (conj
    match eq_sym mid_in_p in _ = cs return CharSet.In c cs.(fst)
    with eq_refl => c_in_mid end
    eq_refl)
  | String c (String _ _) => fun '(step _ _ _ (step _ _ H _)) =>
    match H with end
  end.


Fixpoint linear_inner_strip r1 r2 i1 i2 s first
  (ar1 := (annotate_helper i1 r1).(fst)) (ar2 := (annotate_helper i2 r2).(fst))
  (first_in_r2 : In_regex ar2 first)
  (IHd : forall lt, In_regex ar2 lt -> In_d ar1 lt -> In_d ar2 lt)
  (IHf : forall lt1 lt2, In_regex ar2 lt1 -> In_f ar1 lt1 lt2 ->
         In_f ar2 lt1 lt2) :
  linear_inner r1 i1 s first -> linear_inner r2 i2 s first :=
  match s return linear_inner r1 i1 s first -> linear_inner r2 i2 s first with
  | EmptyString => IHd first first_in_r2
  | String c s => fun '(step mid c_in_mid first_mid_f rest) =>
    let first_mid_r2 : In_f ar2 first mid
     := IHf first mid first_in_r2 first_mid_f in
    step mid c_in_mid first_mid_r2
    (linear_inner_strip r1 r2 i1 i2 s mid
     (proj2 (In_f_all first_mid_r2)) IHd IHf rest)
  end.
Fixpoint linear_inner_alt_destl e f i s first
  (ae := (annotate_helper i e).(fst)) (first_in_e : In_regex ae first) :
  linear_inner (Alt e f) i s first -> linear_inner e i s first :=
  linear_inner_strip (Alt e f) e _ _ s first first_in_e
  (fun lt lt_in_r2 lt_in_d1 => match lt_in_d1 with
   | or_introl l_in_de => l_in_de
   | or_intror l_in_df => In_annotate_exclusion lt_in_r2 (In_d_all l_in_df)
   end)
  (fun lt1 lt2 lt1_in_r2 lt1_lt2_in_f1 => match lt1_lt2_in_f1 with
   | or_introl lt1_lt2_in_fe => lt1_lt2_in_fe
   | or_intror lt1_lt2_in_ff => In_annotate_exclusion
     lt1_in_r2 (proj1 (In_f_all lt1_lt2_in_ff))
   end).
Fixpoint linear_inner_alt_destr e f i s first
  (af := (annotate_helper (annotate_helper i e).(snd) f).(fst))
  (first_in_f : In_regex af first) :
  linear_inner (Alt e f) i s first ->
  linear_inner f (annotate_helper i e).(snd) s first :=
  linear_inner_strip (Alt e f) f _ _ s first first_in_f
  (fun lt lt_in_r2 lt_in_d1 => match lt_in_d1 with
   | or_introl l_in_de => In_annotate_exclusion (In_d_all l_in_de) lt_in_r2
   | or_intror l_in_df => l_in_df
   end)
  (fun lt1 lt2 lt1_in_r2 lt1_lt2_in_f1 => match lt1_lt2_in_f1 with
   | or_introl lt1_lt2_in_fe => In_annotate_exclusion
     (proj1 (In_f_all lt1_lt2_in_fe)) lt1_in_r2
   | or_intror lt1_lt2_in_ff => lt1_lt2_in_ff
   end).
Definition linear_match_alt_dest e f i s :
  linear_match (Alt e f) i s ->
  linear_match e i s \/ linear_match f (annotate_helper i e).(snd) s :=
  match s
  return
    linear_match (Alt e f) i s ->
    linear_match e i s \/ linear_match f (annotate_helper i e).(snd) s
  with
  | EmptyString => fun H => match orb_prop _ _ H with
    | or_introl e_emp => or_introl e_emp
    | or_intror f_emp => or_intror f_emp
    end
  | String c s => fun '(step mid c_in_mid mid_in_p rest) =>
    match mid_in_p with
    | or_introl mid_in_pe => or_introl
      (step mid c_in_mid mid_in_pe
       (linear_inner_alt_destl e f i s mid (In_p_all mid_in_pe) rest))
    | or_intror mid_in_pf => or_intror
      (step mid c_in_mid mid_in_pf
       (linear_inner_alt_destr e f i s mid (In_p_all mid_in_pf) rest))
    end
  end.

Definition linear_match_seq_destr e f i s mid :
  In_p (fst (annotate_helper (snd (annotate_helper i e)) f)) mid ->
  linear_inner (Seq e f) i s mid ->
  linear_inner f (snd (annotate_helper i e)) s mid :=
  fun mid_in_pf =>
  linear_inner_strip (Seq e f) f i _ s mid (In_p_all mid_in_pf)
  (fun lt lt_in_f lt_in_d => match lt_in_d with
   | or_introl (conj _ lt_in_de) => In_annotate_exclusion
     (In_d_all lt_in_de) lt_in_f
   | or_intror lt_in_df => lt_in_df
   end)
  (fun lt1 lt2 lt1_in_f lt1_lt2_in_f => match lt1_lt2_in_f with
   | or_introl (or_introl lt1_lt2_in_ef) => In_annotate_exclusion
     (proj1 (In_f_all lt1_lt2_in_ef)) lt1_in_f
   | or_introl (or_intror lt1_lt2_in_ff) => lt1_lt2_in_ff
   | or_intror (conj lt1_in_de lt2_in_pf) => In_annotate_exclusion
     (In_d_all lt1_in_de) lt1_in_f
   end).
Definition linear_match_seq_dest e f i s :
  linear_match (Seq e f) i s ->
  exists s1 s2, (s1 ++ s2)%string = s /\
  (linear_match e i s1 /\ linear_match f (annotate_helper i e).(snd) s2) :=
  match s with
  | EmptyString => fun ef_emp => ex_intro _ EmptyString (ex_intro _ EmptyString
    (conj eq_refl (andb_prop _ _ ef_emp)))
  | String c s => fun '(step mid c_in_mid mid_in_p rest) =>
    match mid_in_p with
    | or_introl mid_in_pe =>
      let fix rec s first
          (first_in_e : In_regex (annotate_helper i e).(fst) first)
        : linear_inner (Seq e f) i s first ->
        exists s1 s2, (s1 ++ s2)%string = s /\
        (linear_inner e i s1 first /\
         linear_match f (annotate_helper i e).(snd) s2)
       := match s with
       | EmptyString => fun first_d => match first_d with
         | or_introl (conj f_emp first_de) =>
           ex_intro _ EmptyString (ex_intro _ EmptyString (conj eq_refl
             (conj first_de f_emp)))
         | or_intror first_df => In_annotate_exclusion
           first_in_e (In_d_all first_df)
         end
       | String c1 s1 => fun '(step mid c1_in_mid first_mid_f rest) =>
         match first_mid_f with
         | or_introl (or_introl first_mid_fe) =>
           let '(ex_intro _ s1 (ex_intro _ s2 (conj seq (conj me mf))))
            := rec s1 mid (proj2 (In_f_all first_mid_fe)) rest in
           ex_intro _ (String c1 s1) (ex_intro _ s2 (conj
             (f_equal (String c1) seq) (conj
             (step mid c1_in_mid first_mid_fe me)
             mf)))
         | or_introl (or_intror first_mid_ff) => In_annotate_exclusion
           first_in_e (proj1 (In_f_all first_mid_ff))
         | or_intror (conj first_de mid_pf) =>
           ex_intro _ EmptyString (ex_intro _ (String c1 s1)
             (conj eq_refl (conj first_de
              (step mid c1_in_mid mid_pf
               (linear_match_seq_destr e f i s1 mid mid_pf rest)))))
         end
       end in
      let '(ex_intro _ s1 (ex_intro _ s2 (conj seq (conj me mf))))
       := rec s mid (In_p_all mid_in_pe) rest in
      ex_intro _ (String c s1) (ex_intro _ s2 (conj (f_equal (String c) seq)
        (conj (step mid c_in_mid mid_in_pe me) mf)))
    | or_intror (conj e_emp mid_in_pf) =>
      ex_intro _ EmptyString (ex_intro _ (String c s) (conj eq_refl (conj e_emp
        (step mid c_in_mid mid_in_pf
         (linear_match_seq_destr e f i s mid mid_in_pf rest)))))
    end
  end.

Definition linear_match_star_ind e i s
  (ae := (annotate_helper i e).(fst))
  (P : string -> Prop)
  (IH_emp : P EmptyString)
  (IH_more : forall s1 s2, linear_match e i s1 -> P s2 -> P (s1 ++ s2)%string)
  : linear_match (Star e) i s -> P s :=
  let fix ind_inner s first
   : linear_inner (Star e) i s first ->
     exists s1 s2, (s1 ++ s2)%string = s /\ (linear_inner e i s1 first /\ P s2)
   := match s with
   | EmptyString => fun first_in_d =>
     ex_intro _ EmptyString (ex_intro _ EmptyString
     (conj eq_refl (conj first_in_d IH_emp)))
   | String c s => fun '(step mid c_in_mid first_mid_in_fse rest) =>
     let '(ex_intro _ s1 (ex_intro _ s2 (conj seq (conj s1_rest s2P))))
      := ind_inner s mid rest in
     match first_mid_in_fse with
     | or_introl first_mid_in_fe =>
       ex_intro _ (String c s1)%string (ex_intro _ s2 (conj
         (f_equal (String c) seq) (conj
         (step mid c_in_mid first_mid_in_fe s1_rest)
         s2P)))
     | or_intror (conj first_in_de mid_in_pe) =>
       ex_intro _ EmptyString (ex_intro _ (String c (s1 ++ s2)%string) (conj
         (f_equal (String c) seq) (conj
         first_in_de
         (IH_more (String c s1) s2 (step mid c_in_mid mid_in_pe s1_rest) s2P))))
     end
   end in
  match s return linear_match (Star e) i s -> P s with
  | EmptyString => fun _ => IH_emp
  | String c s => fun '(step mid c_in_mid mid_in_pe rest) =>
    let '(ex_intro _ s1 (ex_intro _ s2 (conj seq (conj s1_rest s2P))))
     := ind_inner s mid rest in
    let H : P (String c s1 ++ s2)%string
     := IH_more (String c s1) s2 (step mid c_in_mid mid_in_pe s1_rest) s2P in
    match seq with eq_refl => H end
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

Definition regex_match_iff_linear_match r i s :
  regex_match r s <-> linear_match r i s :=
  conj (regex_match_to_linear_match r i s) (linear_match_to_regex_match r i s).

Axiom Admit : forall {T}, T.

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
