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

(* ---------------------- Local languages ---------------------- *)

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

Fixpoint unique_fst_in_annotate {Γ} (r : regex Γ) i (lt : Γ * state) cs'
  : In_regex (annotate_helper i r).(fst) lt ->
    In_regex (annotate_helper i r).(fst) (cs' , lt.(snd)) ->
    lt = (cs' , lt.(snd))
  := 
     match r with
     | Empty | Eps => fun H => match H with end
     | Char y => fun H1 H2 => eq_trans (eq_sym H1) H2
     | Alt e f | Seq e f => fun H1 H2 => match H1 , H2 with
       | or_introl H1 , or_introl H2 =>
         unique_fst_in_annotate e i lt cs' H1 H2
       | or_intror H1 , or_intror H2 =>
         unique_fst_in_annotate f _ lt cs' H1 H2
       | or_introl H1 , or_intror H2 =>
         let H : False
          := proj2 (In_bounded e _ _ H1) (proj1 (In_bounded f _ _ H2)) in
         match H with end
       | or_intror H1 , or_introl H2 =>
         let H : False
          := proj2 (In_bounded e _ _ H2) (proj1 (In_bounded f _ _ H1)) in
         match H with end
       end
     | Star e => unique_fst_in_annotate e i lt cs'
     end.

Inductive local_step
  (c : ascii) (P : Letter.t -> Prop) (Q : Letter.t -> Prop) : Prop :=
| step : forall mid, CharSet.In c mid.(fst) -> P mid -> Q mid -> local_step.
Arguments step {c P Q} mid _ _ _.

Fixpoint local_inner
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst))
  (s : string) (first : Letter.t) : Prop :=
  match s with
  | EmptyString => In_d ar first
  | String c s => local_step c (In_f ar first) (local_inner r i s)
  end.

Definition local_match
  (r : regex CharSet.t) (i : Z) (ar := (annotate_helper i r).(fst))
  (s : string) : Prop :=
  match s with
  | EmptyString => l ar = true
  | String c s => local_step c (In_p ar) (local_inner r i s)
  end.

(* Lemmas constructing local_match *)

Definition local_match_eps_intro i : local_match Eps i EmptyString :=
  eq_refl.

Definition local_match_char_intro i cs c (c_in_cs : CharSet.In c cs) :
  local_match (Char cs) i (String c EmptyString) :=
  step (cs , i) c_in_cs eq_refl eq_refl.

(* matches are stable under language subsets *)
Definition local_inner_weaken r1 r2 i1 i2
  (ar1 := (annotate_helper i1 r1).(fst)) (ar2 := (annotate_helper i2 r2).(fst))
  (IHd : forall lt, In_d ar1 lt -> In_d ar2 lt)
  (IHf : forall lt1 lt2, In_f ar1 lt1 lt2 -> In_f ar2 lt1 lt2)
  : forall s first, local_inner r1 i1 s first -> local_inner r2 i2 s first :=
  fix wk s first := match s with
  | EmptyString => IHd first
  | String c s => fun '(step mid c_in_mid first_mid_in_f rest) =>
    step mid c_in_mid (IHf first mid first_mid_in_f) (wk s mid rest)
  end.
Definition local_match_weaken r1 r2 i1 i2
  (ar1 := (annotate_helper i1 r1).(fst)) (ar2 := (annotate_helper i2 r2).(fst))
  (IHl : l ar1 = true -> l ar2 = true)
  (IHp : forall lt, In_p ar1 lt -> In_p ar2 lt)
  (IHd : forall lt, In_d ar1 lt -> In_d ar2 lt)
  (IHf : forall lt1 lt2, In_f ar1 lt1 lt2 -> In_f ar2 lt1 lt2)
  : forall s, local_match r1 i1 s -> local_match r2 i2 s :=
  fun s => match s with
  | EmptyString => IHl
  | String c s => fun '(step mid c_in_mid mid_in_p rest) =>
    step mid c_in_mid (IHp mid mid_in_p)
    (local_inner_weaken r1 r2 i1 i2 IHd IHf s mid rest)
  end.

Definition local_match_alt_introl e f i s :
  local_match e i s -> local_match (Alt e f) i s :=
  local_match_weaken e (Alt e f) _ _
  (fun le => orb_true_intro _ _ (or_introl le))
  (fun lt H => or_introl H) (fun lt H => or_introl H)
  (fun lt1 lt2 H => or_introl H) s.
Definition local_match_alt_intror e f i s :
  local_match f (annotate_helper i e).(snd) s -> local_match (Alt e f) i s :=
  local_match_weaken f (Alt e f) _ _
  (fun lf => orb_true_intro _ _ (or_intror lf))
  (fun lt H => or_intror H) (fun lt H => or_intror H)
  (fun lt1 lt2 H => or_intror H) s.

Definition local_match_compose e f g i1 i2 i3 s1 s2
  (ae := (annotate_helper i1 e).(fst)) (af := (annotate_helper i2 f).(fst))
  (ag := (annotate_helper i3 g).(fst))
  (IHl : l ae && l af = true -> l ag = true)
  (IHp : forall lt, In_p ae lt \/ (l ae = true /\ In_p af lt) -> In_p ag lt)
  (IHd : forall lt, (l af = true /\ In_d ae lt) \/ In_d af lt -> In_d ag lt)
  (IHf : forall lt1 lt2, (In_f ae lt1 lt2 \/ In_f af lt1 lt2) \/
                         (In_d ae lt1 /\ In_p af lt2) -> In_f ag lt1 lt2) :
  local_match e i1 s1 -> local_match f i2 s2 ->
  local_match g i3 (s1 ++ s2) :=
  match s1
  return
    local_match e i1 s1 -> local_match f i2 s2 ->
    local_match g i3 (s1 ++ s2)
  with
  | EmptyString => fun e_emp => local_match_weaken f g i2 i3
    (fun f_emp => IHl (andb_true_intro (conj e_emp f_emp)))
    (fun lt H => IHp lt (or_intror (conj e_emp H)))
    (fun lt H => IHd lt (or_intror H))
    (fun lt1 lt2 H => IHf lt1 lt2 (or_introl (or_intror H))) s2
  | String c1 s1 => fun '(step mid c_in_mid mid_in_pe rest1) mfs2 =>
    step mid c_in_mid (IHp mid (or_introl mid_in_pe))
    (match s2
     return local_match f _ s2 -> local_inner g i3 (s1 ++ s2) mid
     with
     | EmptyString => fun f_emp =>
       match string_app_emp s1 in _ = s1'
       return local_inner g i3 s1' mid
       with eq_refl =>
         local_inner_weaken e g _ _
         (fun lt H => IHd lt (or_introl (conj f_emp H)))
         (fun lt1 lt2 H => IHf lt1 lt2 (or_introl (or_introl H)))
         s1 mid rest1
       end
     | String c2 s2 => fun '(step mid2 c2_in_mid2 mid2_in_pf rest2) =>
       let fix rec s1 first
        : local_inner e i1 s1 first ->
          local_inner g i3 (s1 ++ String c2 s2) first
        := match s1 with
           | EmptyString => fun first_de =>
             step mid2 c2_in_mid2
             (IHf first mid2 (or_intror (conj first_de mid2_in_pf)))
             (local_inner_weaken f g _ _
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

Definition local_match_seq_intro e f i s1 s2 :
  local_match e i s1 -> local_match f (annotate_helper i e).(snd) s2 ->
  local_match (Seq e f) i (s1 ++ s2) :=
  local_match_compose e f (Seq e f) _ _ _ s1 s2
  (fun H => H) (fun lt H => H) (fun lt H => H) (fun lt1 lt2 H => H).

Definition local_match_star_intro_emp e i :
  local_match (Star e) i EmptyString :=
  eq_refl.
Definition local_match_star_intro_more e i s1 s2 :
  local_match e i s1 -> local_match (Star e) i s2 ->
  local_match (Star e) i (s1 ++ s2) :=
  local_match_compose e (Star e) (Star e) i i i s1 s2
  (fun _ => eq_refl)
  (fun lt H => match H with or_introl H | or_intror (conj _ H) => H end)
  (fun lt H => match H with or_introl (conj _ H) | or_intror H => H end)
  (fun lt1 lt2 H => match H with
   | or_introl (or_introl H) => or_introl H
   | or_introl (or_intror H) => H
   | or_intror H => or_intror H
   end).

Fixpoint regex_match_to_local_match (r : regex CharSet.t) (i : Z) (s : string)
  (m : regex_match r s) : local_match r i s :=
  match m with
  | mEps => local_match_eps_intro i
  | mChar cs c c_in_cs => local_match_char_intro i cs c c_in_cs
  | mAltl e f s mes => local_match_alt_introl e f i s
    (regex_match_to_local_match e _ s mes)
  | mAltr e f s mfs => local_match_alt_intror e f i s
    (regex_match_to_local_match f _ s mfs)
  | mSeq e f s1 s2 mes1 mfs2 => local_match_seq_intro e f i s1 s2
    (regex_match_to_local_match e _ s1 mes1)
    (regex_match_to_local_match f _ s2 mfs2)
  | mStar_emp e => local_match_star_intro_emp e i
  | mStar_more e s1 s2 mes1 mses2 => local_match_star_intro_more e i s1 s2
    (regex_match_to_local_match e _ s1 mes1)
    (regex_match_to_local_match (Star e) _ s2 mses2)
  end.

(* lemmas destructing local_match *)

Definition local_match_emp_dest i s : ~ local_match Empty i s
  := match s return local_match Empty i s -> False with
     | EmptyString => fun H : false = true => discriminate false H
     | String c s => fun '(step _ _ H _) =>
       match H with end
     end.

Definition local_match_eps_dest i s :
  local_match Eps i s -> EmptyString = s :=
  match s with
  | EmptyString => fun _ => eq_refl
  | String c s => fun '(step mid _ H _) => match H with end
  end.

Definition local_match_char_dest i cs s :
  local_match (Char cs) i s ->
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


Fixpoint local_inner_strip r1 r2 i1 i2 s first
  (ar1 := (annotate_helper i1 r1).(fst)) (ar2 := (annotate_helper i2 r2).(fst))
  (first_in_r2 : In_regex ar2 first)
  (IHd : forall lt, In_regex ar2 lt -> In_d ar1 lt -> In_d ar2 lt)
  (IHf : forall lt1 lt2, In_regex ar2 lt1 -> In_f ar1 lt1 lt2 ->
         In_f ar2 lt1 lt2) :
  local_inner r1 i1 s first -> local_inner r2 i2 s first :=
  match s return local_inner r1 i1 s first -> local_inner r2 i2 s first with
  | EmptyString => IHd first first_in_r2
  | String c s => fun '(step mid c_in_mid first_mid_f rest) =>
    let first_mid_r2 : In_f ar2 first mid
     := IHf first mid first_in_r2 first_mid_f in
    step mid c_in_mid first_mid_r2
    (local_inner_strip r1 r2 i1 i2 s mid
     (proj2 (In_f_all first_mid_r2)) IHd IHf rest)
  end.
Fixpoint local_inner_alt_destl e f i s first
  (ae := (annotate_helper i e).(fst)) (first_in_e : In_regex ae first) :
  local_inner (Alt e f) i s first -> local_inner e i s first :=
  local_inner_strip (Alt e f) e _ _ s first first_in_e
  (fun lt lt_in_r2 lt_in_d1 => match lt_in_d1 with
   | or_introl l_in_de => l_in_de
   | or_intror l_in_df => In_annotate_exclusion lt_in_r2 (In_d_all l_in_df)
   end)
  (fun lt1 lt2 lt1_in_r2 lt1_lt2_in_f1 => match lt1_lt2_in_f1 with
   | or_introl lt1_lt2_in_fe => lt1_lt2_in_fe
   | or_intror lt1_lt2_in_ff => In_annotate_exclusion
     lt1_in_r2 (proj1 (In_f_all lt1_lt2_in_ff))
   end).
Fixpoint local_inner_alt_destr e f i s first
  (af := (annotate_helper (annotate_helper i e).(snd) f).(fst))
  (first_in_f : In_regex af first) :
  local_inner (Alt e f) i s first ->
  local_inner f (annotate_helper i e).(snd) s first :=
  local_inner_strip (Alt e f) f _ _ s first first_in_f
  (fun lt lt_in_r2 lt_in_d1 => match lt_in_d1 with
   | or_introl l_in_de => In_annotate_exclusion (In_d_all l_in_de) lt_in_r2
   | or_intror l_in_df => l_in_df
   end)
  (fun lt1 lt2 lt1_in_r2 lt1_lt2_in_f1 => match lt1_lt2_in_f1 with
   | or_introl lt1_lt2_in_fe => In_annotate_exclusion
     (proj1 (In_f_all lt1_lt2_in_fe)) lt1_in_r2
   | or_intror lt1_lt2_in_ff => lt1_lt2_in_ff
   end).
Definition local_match_alt_dest e f i s :
  local_match (Alt e f) i s ->
  local_match e i s \/ local_match f (annotate_helper i e).(snd) s :=
  match s
  return
    local_match (Alt e f) i s ->
    local_match e i s \/ local_match f (annotate_helper i e).(snd) s
  with
  | EmptyString => fun H => match orb_prop _ _ H with
    | or_introl e_emp => or_introl e_emp
    | or_intror f_emp => or_intror f_emp
    end
  | String c s => fun '(step mid c_in_mid mid_in_p rest) =>
    match mid_in_p with
    | or_introl mid_in_pe => or_introl
      (step mid c_in_mid mid_in_pe
       (local_inner_alt_destl e f i s mid (In_p_all mid_in_pe) rest))
    | or_intror mid_in_pf => or_intror
      (step mid c_in_mid mid_in_pf
       (local_inner_alt_destr e f i s mid (In_p_all mid_in_pf) rest))
    end
  end.

Definition local_match_seq_destr e f i s mid :
  In_p (fst (annotate_helper (snd (annotate_helper i e)) f)) mid ->
  local_inner (Seq e f) i s mid ->
  local_inner f (snd (annotate_helper i e)) s mid :=
  fun mid_in_pf =>
  local_inner_strip (Seq e f) f i _ s mid (In_p_all mid_in_pf)
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
Definition local_match_seq_dest e f i s :
  local_match (Seq e f) i s ->
  exists s1 s2, (s1 ++ s2)%string = s /\
  (local_match e i s1 /\ local_match f (annotate_helper i e).(snd) s2) :=
  match s with
  | EmptyString => fun ef_emp => ex_intro _ EmptyString (ex_intro _ EmptyString
    (conj eq_refl (andb_prop _ _ ef_emp)))
  | String c s => fun '(step mid c_in_mid mid_in_p rest) =>
    match mid_in_p with
    | or_introl mid_in_pe =>
      let fix rec s first
          (first_in_e : In_regex (annotate_helper i e).(fst) first)
        : local_inner (Seq e f) i s first ->
        exists s1 s2, (s1 ++ s2)%string = s /\
        (local_inner e i s1 first /\
         local_match f (annotate_helper i e).(snd) s2)
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
               (local_match_seq_destr e f i s1 mid mid_pf rest)))))
         end
       end in
      let '(ex_intro _ s1 (ex_intro _ s2 (conj seq (conj me mf))))
       := rec s mid (In_p_all mid_in_pe) rest in
      ex_intro _ (String c s1) (ex_intro _ s2 (conj (f_equal (String c) seq)
        (conj (step mid c_in_mid mid_in_pe me) mf)))
    | or_intror (conj e_emp mid_in_pf) =>
      ex_intro _ EmptyString (ex_intro _ (String c s) (conj eq_refl (conj e_emp
        (step mid c_in_mid mid_in_pf
         (local_match_seq_destr e f i s mid mid_in_pf rest)))))
    end
  end.

Definition local_match_star_ind e i s
  (ae := (annotate_helper i e).(fst))
  (P : string -> Prop)
  (IH_emp : P EmptyString)
  (IH_more : forall s1 s2, local_match e i s1 -> P s2 -> P (s1 ++ s2)%string)
  : local_match (Star e) i s -> P s :=
  let fix ind_inner s first
   : local_inner (Star e) i s first ->
     exists s1 s2, (s1 ++ s2)%string = s /\ (local_inner e i s1 first /\ P s2)
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
  match s return local_match (Star e) i s -> P s with
  | EmptyString => fun _ => IH_emp
  | String c s => fun '(step mid c_in_mid mid_in_pe rest) =>
    let '(ex_intro _ s1 (ex_intro _ s2 (conj seq (conj s1_rest s2P))))
     := ind_inner s mid rest in
    let H : P (String c s1 ++ s2)%string
     := IH_more (String c s1) s2 (step mid c_in_mid mid_in_pe s1_rest) s2P in
    match seq with eq_refl => H end
  end.

Fixpoint local_match_to_regex_match (r : regex CharSet.t) (i : Z) (s : string)
  : local_match r i s -> regex_match r s :=
  match r with
  | Empty => fun H => match local_match_emp_dest i s H with end
  | Eps => fun H => match local_match_eps_dest i s H with eq_refl => mEps end
  | Char cs => fun H => match local_match_char_dest i cs s H with
    | ex_intro _ c (conj c_in_cs s_is_c) => match s_is_c with eq_refl =>
      mChar cs c c_in_cs
    end end
  | Alt e f => fun H => match local_match_alt_dest e f i s H with
    | or_introl mes => mAltl e f s (local_match_to_regex_match e _ s mes)
    | or_intror mfs => mAltr e f s (local_match_to_regex_match f _ s mfs)
    end
  | Seq e f => fun H => match local_match_seq_dest e f i s H with
    | ex_intro _ s1 (ex_intro _ s2 (conj s_eq (conj mes1 mfs2))) =>
      match s_eq with eq_refl =>
        mSeq e f s1 s2
        (local_match_to_regex_match e _ s1 mes1)
        (local_match_to_regex_match f _ s2 mfs2)
    end end
  | Star e => local_match_star_ind e i s (regex_match (Star e))
    (mStar_emp e)
    (fun s1 s2 mes1 => mStar_more e s1 s2
     (local_match_to_regex_match e _ s1 mes1))
  end.

Definition regex_match_iff_local_match r i s :
  regex_match r s <-> local_match r i s :=
  conj (regex_match_to_local_match r i s) (local_match_to_regex_match r i s).

(* ---------------------- NFA paths ---------------------- *)

(* Fixpoint local_match_to_NFA_accept r s (cur : StateSet.t) (start : state)
  (start_in_cur : StateSet.In start cur)
  : local_match r start s ->
    let curNFA := {|
      start := cur;
      finals := (compile r).(finals);
      next := (compile r).(next)
    |} in accept curNFA s = true :=
  match s with
  | EmptyString => fun r_emp =>
    let cur_inter_final := StateSet.inter cur (compile r).(finals) in
    let H1 : StateSet.In start (compile r).(finals) :=
      match eq_sym r_emp in _ = b return StateSet.In start (if b then _ else _)
      with eq_refl => _ end in
    match StateSet.is_empty cur_inter_final as b
    return StateSet.is_empty cur_inter_final = b -> negb b = true with
    | false => fun _ => eq_refl
    | true => fun H =>
      match StateSet.is_empty_2 H (StateSet.inter_3 start_in_cur H1) with end
    end eq_refl
  | String c s => _
  end. *)

Check I.

(* 

Definition local_match_iff_NFA_accept r s :
  local_match r 1 s <-> accept (compile r) s = true :=
  match s return local_match r 1 s <-> accept (compile r) s = true with
  | EmptyString => iff_trans
    (conj
     (fun r_emp => ex_intro _ 0 (conj
      (StateSet.singleton_2 eq_refl)
      (Admit(* if_l_first_final below *))))
     (fun '(ex_intro _ st (conj st_in_s0 st_in_finals)) =>
      match StateSet.singleton_1 st_in_s0 in _ = st
      return StateSet.In st (compile r).(finals) -> l (annotate r) = true
      with eq_refl =>
        match l (annotate r) as b
        return StateSet.In 0 (if b then _ else _) -> b = true
        with
        | true => fun _ => eq_refl
        | false => fun H => Admit(* 0 not in positions (d (annotate r)) *)
        end
      end st_in_finals))
    (accept_emp_iff_some_cur_state_final r (StateSet.singleton 0))
  | String c s => conj
    (fun '(step mid c_in_mid mid_in_p rest) =>
     _)
    (Admit)
  end. *)

Definition find_default (cm : CharMap.t StateSet.t) (key : ascii) : StateSet.t
  := match CharMap.find key cm with
     | None => StateSet.empty
     | Some ss => ss
     end.

(* Go through NFA_path_accept *)
Fixpoint NFA_path
    (next : state -> CharMap.t StateSet.t) (finals : StateSet.t) (s : string)
    (first : state) : Prop :=
  match s with
  | EmptyString => StateSet.In first finals
  | String c s => exists mid : state,
      StateSet.In mid (find_default (next first) c) /\
      NFA_path next finals s mid
  end.
(* Fixpoint NFA_path_compose next s1 s2 first mid last
  : NFA_path next s1 first mid -> NFA_path next s2 mid last ->
    NFA_path next (s1 ++ s2) first last :=
  match s1 with
  | EmptyString => fun 'eq_refl p2 => p2
  | String c s => fun '(ex_intro _ mid (conj P p1)) p2 =>
    ex_intro _ mid (conj P (NFA_path_compose _ _ _ _ _ _ p1 p2))
  end. *)
(* Definition NFA_path_accept (n : NFA) (s : string) : Prop :=
  exists (first last : state),
  StateSet.In first n.(start) /\
  StateSet.In last n.(finals) /\
  NFA_path n.(next) s first last. *)

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
  (exists cs, In_d (annotate r) (cs , state)) \/
  (l (annotate r) = true /\ state = 0).

Axiom transitions_iff : forall r st1 st2 c,
  StateSet.In st2 (find_default ((compile r).(next) st1) c) <->
  (exists cs1 cs2,
   In_f (annotate r) (cs1 , st1) (cs2 , st2) /\
   CharSet.In c cs2) \/
  (exists cs2,
   In_p (annotate r) (cs2 , st2) /\
   CharSet.In c cs2 /\
   st1 = 0).

Definition expand_pair {A B : Type} {P : A * B -> Type} {p : A * B}
  : P p -> P (fst p , snd p)
  := match p with pair a b => fun H => H end.

Definition zero_not_in_annotated {A Γ r cs} : 
  In_regex (annotate (Γ := Γ) r) (cs , 0) -> A :=
  fun H => match proj1 (In_bounded r 1 (cs , 0) H) eq_refl with end.

Definition l_final_iff r :
  StateSet.In 0 (compile r).(finals) <-> l (annotate r) = true :=
  conj
  (fun H => match proj1 (finals_iff r 0) H with
   | or_introl (ex_intro _ cs ind) => zero_not_in_annotated (In_d_all ind)
   | or_intror (conj r_emp _) => r_emp
   end)
  (fun r_emp => proj2 (finals_iff r 0) (or_intror (conj r_emp eq_refl))).

Definition d_final_iff r lt (lt_in_r : In_regex (annotate r) lt) :
  StateSet.In lt.(snd) (compile r).(finals) <-> In_d (annotate r) lt :=
  iff_trans (finals_iff r lt.(snd))
  (conj
   (fun H => match H with
    | or_introl (ex_intro _ cs ind) =>
      match eq_sym (unique_fst_in_annotate r _ lt cs lt_in_r (In_d_all ind))
      in _ = lt return In_d _ lt with eq_refl => ind end
    | or_intror (conj _ st0) =>
      let H : In_regex _ (lt.(fst) , 0)
       := match st0 in _ = o return In_regex _ (_ , o)
          with eq_refl => expand_pair lt_in_r end
      in zero_not_in_annotated H
    end)
   (fun ind => or_introl (ex_intro _ lt.(fst)
    (expand_pair ind : In_d _ (fst lt , snd lt))))).

Definition initial_transitions_iff r st c :
  StateSet.In st (find_default ((compile r).(next) 0) c) <->
  (exists cs,
   In_p (annotate r) (cs , st) /\
   CharSet.In c cs) :=
  iff_trans (transitions_iff r 0 st c)
  (conj
   (fun H => match H with
    | or_introl (ex_intro _ cs0 (ex_intro _ _ (conj O_st_f _))) =>
      zero_not_in_annotated (proj1 (In_f_all O_st_f))
    | or_intror (ex_intro _ cs (conj inp (conj c_in_cs _))) =>
      ex_intro _ cs (conj inp c_in_cs)
    end)
   (fun '(ex_intro _ cs (conj inp c_in_cs)) => or_intror (ex_intro _ cs
    (conj inp (conj c_in_cs eq_refl))))).

Definition interior_transitions_iff r lt1 st2 c
  (lt1_in_r : In_regex (annotate r) lt1) :
  StateSet.In st2 (find_default ((compile r).(next) lt1.(snd)) c) <->
  (exists cs2,
   In_f (annotate r) lt1 (cs2 , st2) /\
   CharSet.In c cs2) :=
  iff_trans (transitions_iff r lt1.(snd) st2 c)
  (conj
   (fun H => match H with
    | or_introl (ex_intro _ cs1 (ex_intro _ cs2 (conj inf c_in_cs2))) =>
      match eq_sym (unique_fst_in_annotate r _ lt1 cs1 lt1_in_r 
                    (proj1 (In_f_all inf)))
      in _ = lt return exists cs2, In_f _ lt _ /\ _
      with eq_refl => ex_intro _ cs2 (conj inf c_in_cs2) end
    | or_intror (ex_intro _ _ (conj _ (conj _ st1_eq_0))) =>
      zero_not_in_annotated
      (match st1_eq_0 in _ = o return In_regex _ (_ , o)
       with eq_refl => expand_pair lt1_in_r end)
    end)
   (fun '(ex_intro _ cs2 (conj inf c_in_cs2)) => or_introl
    (ex_intro _ lt1.(fst) (ex_intro _ cs2
     (conj (expand_pair (P := fun lt => In_f _ lt _) inf) c_in_cs2))))).

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
    lt (H1 : In_p (annotate r) lt)
    c (H2 : CharSet.In c lt.(fst))
  : StateSet.In lt.(snd) (find_states c (compile r) 0) :=
  proj2 (transitions_iff r 0 lt.(snd) c) (or_intror
    (ex_intro _ lt.(fst) (conj
      (expand_pair H1)
      (conj H2 eq_refl)))).

(* Definition accept_emp_iff_some_cur_state_final r cur
  : (exists st, StateSet.In st cur /\ StateSet.In st (compile r).(finals)) <->
    negb (StateSet.is_empty (StateSet.inter cur (compile r).(finals))) = true :=
  conj
  (fun '(ex_intro _ st (conj H1 H2)) =>
   match StateSet.is_empty _ as b
   return StateSet.is_empty _ = b -> negb b = true with
   | false => fun _ => eq_refl
   | true => fun H =>
     match StateSet.is_empty_2 H (StateSet.inter_3 H1 H2) with end
   end eq_refl)
  (Admit). *)

(* easy, if we get the conversions right *)
Fixpoint local_inner_iff_NFA_path r s start
  (start_in_r : In_regex (annotate r) start) :
  local_inner r 1 s start <->
  NFA_path (compile r).(next) (compile r).(finals) s start.(snd) :=
  match s
  return
    local_inner r 1 s start <->
    NFA_path (compile r).(next) (compile r).(finals) s start.(snd)
  with
  | EmptyString =>
    iff_sym (d_final_iff r start start_in_r)
  | String c s => conj
    (fun '(step mid c_in_mid first_mid_f rest) =>
     ex_intro _ mid.(snd) (conj
       (proj2 (interior_transitions_iff r start mid.(snd) c start_in_r)
        (ex_intro _ mid.(fst) (conj (expand_pair first_mid_f) c_in_mid)))
       (proj1 (local_inner_iff_NFA_path r s mid
               (proj2 (In_f_all first_mid_f))) rest)))
    (fun '(ex_intro _ mid (conj first_mid_trans path)) =>
     let '(ex_intro _ cs2 (conj inf c_in_cs2))
      := proj1 (interior_transitions_iff r start mid c start_in_r)
         first_mid_trans in
     step (cs2 , mid) c_in_cs2 inf
       (proj2 (local_inner_iff_NFA_path r s (cs2 , mid) (proj2 (In_f_all inf)))
        (path : NFA_path _ _ _ mid)))
  end.
Definition local_match_iff_NFA_path_accept r s :
  local_match r 1 s <-> NFA_path (compile r).(next) (compile r).(finals) s 0 :=
  match s
  return
    local_match r 1 s <->
    NFA_path (compile r).(next) (compile r).(finals) s 0
  with
  | EmptyString => iff_sym (l_final_iff r)
  | String c s => conj
     (fun '(step mid c_in_mid mid_in_p rest) =>
      ex_intro _ mid.(snd) (conj
        (proj2 (initial_transitions_iff r mid.(snd) c)
         (ex_intro _ mid.(fst) (conj (expand_pair mid_in_p) c_in_mid)))
        (proj1 (local_inner_iff_NFA_path r s mid (In_p_all mid_in_p)) rest)))
     (fun '(ex_intro _ mid (conj O_to_mid path)) =>
      let '(ex_intro _ cs (conj mid_in_p c_in_cs))
       := proj1 (initial_transitions_iff r mid c) O_to_mid in
      step (cs , mid) c_in_cs mid_in_p
        (proj2 (local_inner_iff_NFA_path r s (cs , mid) (In_p_all mid_in_p))
         (path : NFA_path _ _ s mid)))
  end.

(* easy *)
Axiom compile_NFA_start_single : forall r s,
  NFA_path (compile r).(next) (compile r).(finals) s 0 <->
  exists st, StateSet.In st (compile r).(start) /\
             NFA_path (compile r).(next) (compile r).(finals) s st.

(* easy *)
Axiom NFA_accept_path_iff
  : forall n s,
    (exists st, StateSet.In st n.(start) /\
     NFA_path n.(next) n.(finals) s st) <->
    accept n s = true.

(* prove this without any axioms, then we have succeeded. *)
Definition Glushkov_correct : Glushkov_is_correct :=
  fun r s =>
  iff_trans (iff_trans (iff_trans
  (regex_match_iff_local_match r 1 s)
  (local_match_iff_NFA_path_accept r s))
  (compile_NFA_start_single r s))
  (NFA_accept_path_iff (compile r) s)
.
