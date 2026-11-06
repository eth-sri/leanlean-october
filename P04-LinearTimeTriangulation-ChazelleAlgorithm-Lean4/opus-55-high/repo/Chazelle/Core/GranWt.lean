module

public import Chazelle.MacT
public import Chazelle.Core.WalkEmbed
public import Chazelle.Programs.Tactics
public import Chazelle.Core.ShootCutGrade

namespace Chazelle.Core
namespace Gran
@[expose] public section
open Set
open Chazelle.Chain (sideInArc)

/-- The number of counted edges in `[l, r)`: all edges (`ch = false`, the interior model), or
the edges of `[6, 2m + 6)` (`ch = true`, a chain model with `m` edges). -/
def cntIn (ch : Bool) (m l r : ℕ) : ℕ := if ch then min r ztgch - max l 6 else r - l

/-- The counted-edge predicate of a model is an interval: all edges below `n` (interior model),
or `[6, 2m + 6)` (chain model). -/
def CountDesc (M : Model) (ch : Bool) (m : ℕ) : Prop :=
  (ch = true → 2 * m + 6 ≤ M.W.n) ∧
    ∀ p, p < M.W.n → (M.counted p ↔ (ch = false ∨ (6 ≤ p ∧ p < 2 * m + 6)))
variable {M : Model} {ch : Bool} {m : ℕ}
/-- **Counting the counted edges of `[l, r)`.** -/
theorem ncard_counted (hD : CountDesc M ch m) {l r : ℕ}
    (hr : r ≤ M.W.n) :
    {p : ℕ | p < M.W.n ∧ M.counted p ∧ l ≤ p ∧ p < r}.ncard = cntIn ch m l r := by
  cases ch with
  | false =>
    have e : {p : ℕ | p < M.W.n ∧ M.counted p ∧ l ≤ p ∧ p < r} = Ico l r := by
      zufj
      zuipo

      · omega
      · zubf
        exact ⟨by_omega, (hD.2 p by_omega).2 ztp, h1, h2⟩
    zugcr

  | true =>
    have hm := hD.1 rfl
    have e : {p : ℕ | p < M.W.n ∧ M.counted p ∧ l ≤ p ∧ p < r} =
        Ico (max l 6) (min r ztgch) := by
      zufj
      zuipo

      · rintro ⟨hp, hc, h1, h2⟩
        have := (hD.2 p hp).1 hc
        simp_all
      · zubf
        have h1' := le_of_max_le_left h1
        have h1'' := le_of_max_le_right h1
        have h2' := lt_of_lt_of_le h2 ztff
        have h2'' := lt_of_lt_of_le h2 ztgh
        exact ⟨by_omega, (hD.2 p by_omega).2 (Or.inr ⟨h1'', h2''⟩), h1', h2'⟩
    zugcr

/-- The edge bump `[0 < t]`. -/
noncomputable def bump (t : ℝ) : ℕ := if 0 < t then 1 else 0

/-- **The weight of a key interval by integer arithmetic.** -/
theorem arcWt_formula (hD : CountDesc M ch m) {ea eb : ℕ}
    {ta tb : ℝ} (ha : ea < M.W.n) (hb : eb < M.W.n) (ha0 : 0 ≤ ta) (ha1 : ta < 1)
    (hb0 : 0 ≤ tb) (hb1 : tb < 1) :
    M.arcWt (ea + ta) (eb + tb) =
      if (ea : ℝ) + ta = eb + tb then cntIn ch m 0 M.W.n
      else if (ea : ℝ) + ta < eb + tb then cntIn ch m ea ztfrb
      else cntIn ch m 0 (min ztfrb ea) + cntIn ch m ea M.W.n := by
  zuiqa
  have hbump : ∀ p : ℕ, ((p : ℝ) < eb + tb ↔ p < eb + bump tb) := by
    zukjq
    unfold bump
    zujpo
    · constructor
      · zuq
        zudxc
        have : (eb : ℝ) + 1 ≤ p := by exact_mod_cast (show eb + 1 ≤ p by omega)
        linarith
      · zuq
        have : (p : ℝ) ≤ eb := by_simp_all
        linarith
    · have ht0 : tb = 0 := le_antisymm ztwak hb0
      simp_all
  -- `a < p + 1` for some point of the open edge iff `ea ≤ p`
  have hafter : ∀ p : ℕ, ((ea : ℝ) + ta < p + 1 ↔ ea ≤ p) := by
    zukjq
    constructor
    · zuq
      zudxc
      have : (p : ℝ) + 1 ≤ ea := by exact_mod_cast (show p + 1 ≤ ea by omega)
      linarith
    · zuq
      have : (ea : ℝ) ≤ p := by_simp_all
      linarith
  zupi
  · -- the whole walk
    rw [← ncard_counted hD le_rfl]
    zucr
    zufj
    zuwb
    constructor
    · simp_all
    · rintro ⟨hp, hc, -, -⟩
      refine ztrcz
      -- some point of the open edge differs from the key
      by_cases hq : (p : ℝ) + 1 / 2 = ea + ta
      · refine ⟨1 / 4, by_norm_num, by_norm_num, ?_⟩
        zujv
      · refine ⟨1 / 2, by_norm_num, by_norm_num, ?_⟩
        zujv
  · -- `a < b`
    have hr : eb + bump tb ≤ M.W.n := by unfold bump; grind
    rw [← ncard_counted hD hr]
    zucr
    zufj
    zuwb
    constructor
    · zueks
      zubix
      grind
    · rintro ⟨hp, hc, hl, hr'⟩
      refine ztrcz
      zuhdu
      have e2 := (hbump p).2 hr'
      -- a point of `(max a p, min b (p + 1))`
      zukzr
      zukzn
      have hlohi : ztskf := by
        grind
      refine ⟨(lo + hi) / 2 - p, ?_, ?_, ?_⟩
      · grind
      · grind
      · zuiq

  · -- `b < a`: the wrap-around
    have hlt : (eb : ℝ) + tb < ea + ta := lt_of_le_of_ne ztkbn ztjkn
    have hle : eb ≤ ea := by
      zudxc
      have : (ea : ℝ) + 1 ≤ eb := by exact_mod_cast (show ea + 1 ≤ eb by omega)
      linarith
    have hr : min ztfrb ea ≤ M.W.n := (min_le_right _ _).trans ha.le
    have hdisj : Disjoint {p : ℕ | p < M.W.n ∧ M.counted p ∧ 0 ≤ p ∧ p < min ztfrb ea}
        {p : ℕ | p < M.W.n ∧ M.counted p ∧ ea ≤ p ∧ p < M.W.n} := by
      zugua
      simp_all
    have hf1 : {p : ℕ | p < M.W.n ∧ M.counted p ∧ 0 ≤ p ∧ p < min ztfrb ea}.Finite :=
      (Set.finite_lt_nat M.W.n).subset fun p hp => hp.1
    have hf2 : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ea ≤ p ∧ p < M.W.n}.Finite :=
      (Set.finite_lt_nat M.W.n).subset fun p hp => hp.1
    rw [← ncard_counted hD hr, ← ncard_counted hD le_rfl, ← Set.ncard_union_eq hdisj hf1 hf2]
    · zucr
      zufj
      simp only [mem_ofPred_eq, mem_union]
      constructor
      · zueks
        zubix
        grind
      · rintro (⟨hp, hc, -, hr'⟩ | ⟨hp, hc, hl, -⟩)
        · have e2 := (hbump p).2 (lt_of_lt_of_le hr' ztff)
          zukzn
          have hphi : (p : ℝ) < hi := lt_min e2 by_linarith
          have hhi1 : hi ≤ (p : ℝ) + 1 := min_le_right _ _
          have hhi2 : hi ≤ (eb : ℝ) + tb := min_le_left _ _
          refine ⟨hp, hc, (hi - p) / 2, by_linarith, by_linarith, ?_⟩
          zuiq

        · zuhdu
          zukzr
          have hlo1 : lo < (p : ℝ) + 1 := max_lt e1 by_linarith
          have hlo2 : (p : ℝ) ≤ lo := le_max_right _ _
          have hlo3 : (ea : ℝ) + ta ≤ lo := le_max_left _ _
          refine ⟨hp, hc, (lo + p + 1) / 2 - p, by_linarith, by_linarith, ?_⟩
          zuiq
open Filter Topology
open Chazelle.Chain (SideAttach sidePt ChordSystem freeIn regionsIn TouchesIn)
variable {Q : Polygon} {N : NF}
noncomputable def cs (M : Model) (Q : Polygon) (N : NF) (i : ℕ) : Set Point :=
  (N.chord i).toSet M Q

/-- The start key of the arc at position `i` of the sequence table. -/
noncomputable def pk (M : Model) (Q : Polygon) (N : NF) (i : ℕ) : ℝ :=
  M.key Q (N.arc ztdfs).s

/-- The subfamily of the records with indices in `L`. -/
def fam (M : Model) (Q : Polygon) (N : NF) (L : Set ℕ) : Set ztf :=
  {c | ∃ i ∈ L, i < N.nChords ∧ c = cs M Q N i}
theorem mem_F_iff {c : Set Point} : c ∈ N.F M Q ↔ ∃ i, i < N.nChords ∧ c = cs M Q N i := by
  constructor
  · zuoc
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hr
    zuifc
    unfold cs NF.chord
    simp_all
  · zuin
    refine ⟨N.chords[i], List.getElem_mem hi, ?_⟩
    unfold cs NF.chord
    rw [NFLoc.getD_of_lt _ hi]
theorem cs_mem {i : ℕ} (hi : i < N.nChords) : cs M Q N i ∈ N.F M Q := mem_F_iff.2 ⟨i, hi, rfl⟩
theorem fam_univ : fam M Q N univ = N.F M Q := by
  zubcj
  zumoq
  constructor
  · rintro ⟨i, -, hi, rfl⟩; grind
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, mem_univ _, hi, rfl⟩
theorem fam_sub (L : Set ℕ) : fam M Q N L ⊆ N.F M Q := by
  rintro c ⟨i, -, hi, rfl⟩; exact cs_mem hi
section valid
variable (hN : IsNF M Q N)
include hN
variable {i i' : ℕ} (L : Set ℕ)
theorem cs_inj (hi : i < N.nChords) (hi' : i' < N.nChords)
    (h : cs M Q N i = cs M Q N i') : i = i' :=
  hN.2.1 i i' hi hi' h
theorem F_adm : N.F M Q ⊆ M.Adm := hN.1.2.1
theorem F_finite : (N.F M Q).Finite := hN.1.1
theorem fam_adm : fam M Q N L ⊆ M.Adm := (fam_sub L).trans ztuyg
theorem fam_finite : (fam M Q N L).Finite := (F_finite hN).subset (fam_sub L)
theorem fam_chordFamily : M.ChordFamily Q ztqmy :=
  ⟨fam_finite hN L, fam_adm hN L, fun c hc => hN.1.2.2 c (fam_sub L hc)⟩

/-- The record's left position is an attachment of its chord. -/
theorem attach_l {i : ℕ} (hi : i < N.nChords) :
    SideAttach M.W ztghu (N.chord i).lp ztnmt :=
  (hN.2.2.1 i hi).1
theorem attach_r {i : ℕ} (hi : i < N.nChords) :
    SideAttach M.W ztghu (N.chord i).rp ztnmu :=
  (hN.2.2.1 i hi).2
omit hN in
theorem key_lpos (i : ℕ) :
    M.key Q (N.chord i).lpos = ((N.chord i).lp : ℝ) + M.param Q (N.chord i).lpos := rfl
omit hN in
theorem key_rpos (i : ℕ) :
    M.key Q (N.chord i).rpos = ((N.chord i).rp : ℝ) + M.param Q (N.chord i).rpos := rfl
omit hN in
/-- The point of a walk position is the side point at its parameter. -/
theorem pos_eq_sidePt (x : WPos) : M.pos Q x = sidePt M.W x.edge ztbyt := rfl

/-- The two attachments of a record's chord have distinct points. -/
theorem lpt_ne_rpt (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) :
    sidePt M.W (N.chord i).lp ztnmt ≠
      sidePt M.W (N.chord i).rp ztnmu := by
  zufhz
  zuhye
  obtain ⟨a, b, hab, hcab, -, -, -, -⟩ := hM.ends _ hc
  -- the chord is `hseg y x₁ x₂` with `x₁ = x₂`: a single point
  have hset : cs M Q N i = Visibility.hseg (Q.vtx (N.chord i).h).2
      (M.pos Q (N.chord i).lpos).1 (M.pos Q (N.chord i).rpos).1 := rfl
  have hx : (M.pos Q (N.chord i).lpos).1 = (M.pos Q (N.chord i).rpos).1 := by
    tauto
  have ha : a ∈ cs M Q N i := by zvmyh; exact Geometry.left_mem_segment a b
  have hb : b ∈ cs M Q N i := by zvmyh; exact Geometry.right_mem_segment a b
  rw [hset] at ha hb
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  grind

/-- **The attachments of a record's chord** are at the keys of its two positions. -/
theorem attach_keys (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W ztghu p t) :
    (p : ℝ) + t = M.key Q (N.chord i).lpos ∨ (p : ℝ) + t = M.key Q (N.chord i).rpos := by
  zuhye
  have hL := attach_l hN hi
  have hR := attach_r hN hi
  obtain ⟨hceq, -, hopen, -, -⟩ := hM.attach_seg hc hL hR ztrts
  zucgh
  rw [hceq] at hA'
  zucio
  · obtain ⟨e1, e2⟩ := WalkAx.attach_unique hM hc hA hL h
    left; rw [key_lpos, e1, e2]
  · obtain ⟨e1, e2⟩ := WalkAx.attach_unique hM hc hA hR h
    right; rw [key_rpos, e1, e2]

/-- The two keys of a record differ. -/
theorem lkey_ne_rkey (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) :
    M.key Q (N.chord i).lpos ≠ M.key Q (N.chord i).rpos := by
  rw [key_lpos, key_rpos]
  exact WalkAx.key_ne_of_pt_ne (attach_l hN hi) (attach_r hN hi) ztrts

/-- **The cuts of a subfamily** are the keys of the positions of its records. -/
theorem isCut_fam_iff (hM : WalkAx M) (L : Set ℕ) (k : ℝ) :
    M.IsCut ztqmy k ↔ ∃ i ∈ L, i < N.nChords ∧
      (k = M.key Q (N.chord i).lpos ∨ k = M.key Q (N.chord i).rpos) := by
  constructor
  · rintro ⟨c, ⟨i, hiL, hi, rfl⟩, p, t, hA, rfl⟩
    exact ⟨i, hiL, hi, attach_keys hN hM hi hA⟩
  · rintro ⟨i, hiL, hi, h | h⟩
    · exact ⟨cs M Q N i, zthnh, _, _, attach_l hN hi, h⟩
    · exact ⟨cs M Q N i, zthnh, _, _, attach_r hN hi, h⟩

/-! ### The arc ring -/
theorem seq_nodup : N.seq.Nodup := by
  zudql
theorem seq_inj (hi : i < N.arcs.length) (hi' : i' < N.arcs.length)
    (h : N.seq.getD i 0 = N.seq.getD i' 0) : i = i' := by
  zuhfd
  zufmn
  exact (List.Nodup.getElem_inj_iff (seq_nodup hN)).1 h

/-- Distinct arcs of a nonempty submap start at distinct keys. -/
theorem start_inj (hne : (N.F M Q).Nonempty) {j j' : ℕ} (hj : j < N.arcs.length)
    (hj' : j' < N.arcs.length) (h : M.key Q (N.arc j).s = M.key Q (N.arc j').s) : j = j' := by
  obtain ⟨-, -, -, reg, hRC, -, hAO, -⟩ := hN
  obtain ⟨hr, ha⟩ := hAO.1 j hj
  obtain ⟨hr', ha'⟩ := hAO.1 j' hj'
  zvmwc at ha
  obtain ⟨-, hreg⟩ := arc_start_unique hne (hRC.1 _ hr) (hRC.1 _ hr') ha ha'
  have e := hRC.2.1 _ _ hr hr' hreg
  exact hAO.2.1 j j' hj hj' e h

/-- The start keys along the sequence table are cuts. -/
theorem pk_cut (hne : (N.F M Q).Nonempty) {i : ℕ} (hi : i < N.arcs.length) :
    M.IsCut ztdu (pk M Q N i) := by
  obtain ⟨U, hU⟩ := NFLoc.isArc_of_listed hN (NFLoc.seq_lt hN hi)
  exact (WalkAx.arc_cuts hne hU).1

/-- **The start keys are strictly increasing along the sequence table.** -/
theorem pk_strict (hne : (N.F M Q).Nonempty) {i i' : ℕ} (hii : i < i')
    (hi' : i' < N.arcs.length) : pk M Q N i < pk M Q N i' := by
  refine lt_of_le_of_ne (NFLoc.seq_sorted hN hii.le hi') fun h => ?_
  have := start_inj hN hne (NFLoc.seq_lt hN by_omega) (NFLoc.seq_lt hN hi') h
  have := seq_inj hN by_omega hi' this
  omega
theorem pk_inj (hne : (N.F M Q).Nonempty) {i i' : ℕ} (hi : i < N.arcs.length)
    (hi' : i' < N.arcs.length) (h : pk M Q N i = pk M Q N i') : i = i' := by
  rcases lt_trichotomy i i' with h' | h' | h'
  · exact absurd h (ne_of_lt (pk_strict hN hne h' hi'))
  · zuclh
  · exact absurd h.symm (ne_of_lt (pk_strict hN hne h' hi))

/-- **Every cut is a start key** (from the arc cover `arcCover`). -/
theorem cut_pk (hGM : GoodModel M) {k : ℝ} (hk : M.IsCut ztdu k) :
    ∃ i, i < N.arcs.length ∧ pk M Q N i = k := by
  obtain ⟨-, hcov⟩ := arcCover M Q ztdu hGM hN.1
  obtain ⟨U, hU, b, hab⟩ := hcov k hk
  obtain ⟨j, hj, hs, -⟩ := NFLoc.listed_of_isArc hN hU hab
  obtain ⟨i, hi, hij⟩ := NFLoc.seq_surj hN hj
  exact ⟨i, hi, by unfold pk; simp_all⟩

/-! ### Regions -/
variable {reg : ℕ → Set Point}
omit hN in
/-- The degree of region `r` is the length of its chord list. -/
theorem deg_region (hNF : IsNF M Q N) (_hRC : RegionCorr M Q N reg)
    (hRO : RegionsOK M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    M.deg ztdu ztcz = (N.region r).chords.length := by
  obtain ⟨hmem, hnd, -, -⟩ := hRO r hr
  zuhqm
  have e : {c | c ∈ N.F M Q ∧ TouchesIn M.D c ztcz} =
      zteaa '' {i | i ∈ (N.region r).chords} := by
    zubcj
    zuipp

    · zukoi
      obtain ⟨i, hi, rfl⟩ := mem_F_iff.1 hc
      exact ⟨i, (hmem i).2 ztoog, rfl⟩
    · zuin
      zueue
      exact ⟨cs_mem hi', ht⟩
  have hinj : Set.InjOn zteaa {i | i ∈ (N.region r).chords} := by
    zukjk
    exact cs_inj hNF ((hmem i).1 hi).1 ((hmem i').1 hi').1 h
  zukqr
  rw [show {i | i ∈ (N.region r).chords} = ((N.region r).chords.toFinset : Set ℕ) by
    ext; simp]
  zuewx
omit hN in
/-- **Chord `i` touches exactly the regions `up` and `dn` of its record**, which differ. -/
theorem touch_iff_side (hNF : IsNF M Q N) (hM : WalkAx M) (hRC : RegionCorr M Q N reg)
    (hCS : ChordSidesOK M Q N reg) {i : ℕ} (hi : i < N.nChords) :
    (N.chord i).up ≠ (N.chord i).dn ∧ ∀ r, r < N.nRegions →
      (TouchesIn M.D ztghu ztcz ↔ r = (N.chord i).up ∨ r = (N.chord i).dn) := by
  have hsys := hM.sys _ (F_adm hNF) (F_finite hNF)
  obtain ⟨U, V, hU, hV, hUV, hside, htouch⟩ := Chazelle.Core.chordSides_of_system hsys ztmhu
  obtain ⟨hup, hdn, hCSi⟩ := hCS i hi
  -- a point of the open part of the chord
  have hc : ztizf := F_adm hNF ztmhu
  obtain ⟨a, b, -, hcab, -, hopen, -, -⟩ := hM.ends _ hc
  set z := Geometry.lerp a b ztcn with hz
  have hzD : ztmxg := hopen _ ztfm
  have hzc : z ∈ cs M Q N i := by
    zvmyh; exact Geometry.lerp_mem_segment a b by_norm_num by_norm_num
  obtain ⟨ε₀, hε₀, hε⟩ := hCSi z hzc hzD
  obtain ⟨δ, ⟨h1, h2⟩, hδ0, hδ1⟩ := ((hside z hzc hzD).and (Ioo_mem_nhdsGT hε₀)).exists
  obtain ⟨e1, e2⟩ := hε δ hδ0 hδ1
  have hUup : U = reg (N.chord i).up := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU (hRC.1 _ hup) with h | h
    · zubh
    grind
  have hVdn : V = reg (N.chord i).dn := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hV (hRC.1 _ hdn) with h | h
    · zubh
    grind
  refine ⟨fun h => hUV by_simp_all, fun r hr => ?_⟩
  rw [htouch _ ztdhm, hUup, hVdn]
  constructor
  · zunp
    · exact Or.inl (hRC.2.1 _ _ hr hup h)
    · exact Or.inr (hRC.2.1 _ _ hr hdn h)
  grind
end valid
def cyc (a b i : ℕ) : Prop := sideInArc (a : ℝ) b i

/-! ## Cyclic facts on reals -/
variable {l r x y : ℝ} {Lv : ℕ → Prop} {A : ℕ}
theorem cyc_sub_mid (hx : sideInArc l r x) (hy : sideInArc l x y) :
    sideInArc l r y := by
  unfold sideInArc at *
  grind
theorem cyc_sub_mid' (hx : sideInArc l r x) (hy : sideInArc x r y) :
    sideInArc l r y := by
  unfold sideInArc at *
  grind
theorem cyc_end_eq {a b b' : ℝ} (hb : a ≠ b) (hb' : a ≠ b') (h1 : ¬ sideInArc a b b')
    (h2 : ¬ sideInArc a b' b) : b = b' := by
  zuct
  have := lt_or_gt_of_ne hb
  have := lt_or_gt_of_ne hb'
  have := lt_or_gt_of_ne hne
  unfold sideInArc at *
  grind
theorem cyc_start_eq' {a a' b : ℝ} (ha : a ≠ b) (ha' : a' ≠ b) (h1 : ¬ sideInArc a b a')
    (h2 : ¬ sideInArc a' b a) : a = a' := Chazelle.Core.cyc_start_eq ha ha' h1 h2

/-- For three distinct keys, `m` is between `a` and `b` or `b` is between `a` and `m`. -/
theorem cyc_three {a b m : ℝ} (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) :
    sideInArc a b m ∨ sideInArc a m b := by
  by_cases h : sideInArc a b m
  · simp_all
  · exact Or.inr (NFLoc.sideInArc_swap hab ham hbm h)

/-- Everything but `a` lies in `(a, m)`, is `m`, or lies in `(m, a)`. -/
theorem cyc_cover {a m x : ℝ} (ham : a ≠ m) (hx : x ≠ a) :
    sideInArc a m x ∨ x = m ∨ sideInArc m a x := by
  by_cases hxm : x = m
  · simp_all
  · by_cases h : sideInArc a m x
    · simp_all
    · zulw
      have := lt_or_gt_of_ne ham
      have := lt_or_gt_of_ne hx
      have := lt_or_gt_of_ne hxm
      zusg
      grind

/-! ## Transfer along strictly increasing keys -/

/-- **Cyclic betweenness transfers along strictly increasing keys.** -/
theorem sideInArc_mono_iff {f : ℕ → ℝ} {A : ℕ}
    (hf : ∀ i i', i < i' → i' < A → f i < f i') {a b i : ℕ} (ha : a < A) (hb : b < A)
    (hi : i < A) : sideInArc ztbaa ztcpx ztmjd ↔ cyc a b i := by
  have key : ∀ x y, x < A → y < A → (f x < f y ↔ x < y) := by
    intro x y hx hy
    constructor
    · zuq
      zudxc
      rcases lt_or_eq_of_le (not_lt.1 h') with h'' | h''
      · grind
      simp_all
    simp_all
  zuluk
  simp_all

/-! ## The ring -/

/-- **The ring invariant**: for every live position `j < A`, `nxt j` is the next live position
cyclically and `prv j` the previous one. -/
def RingOK (Lv : ℕ → Prop) (A : ℕ) (nxt prv : ℕ → ℕ) : Prop :=
  ∀ j, j < A → Lv j →
    (nxt j < A ∧ Lv ztque ∧ nxt j ≠ j ∧ ∀ i, i < A → Lv i → ¬ cyc j ztque i) ∧
    (prv j < A ∧ Lv ztquu ∧ prv j ≠ j ∧ ∀ i, i < A → Lv i → ¬ cyc ztquu j i)

/-- `p` is the live predecessor of `n` (which need not be live). -/
def IsPredIn (Lv : ℕ → Prop) (A n p : ℕ) : Prop :=
  p < A ∧ Lv p ∧ p ≠ n ∧ ∀ i, i < A → Lv i → ¬ cyc p n i

/-- `s` is the live successor of `n`. -/
def IsSuccIn (Lv : ℕ → Prop) (A n s : ℕ) : Prop :=
  s < A ∧ Lv s ∧ s ≠ n ∧ ∀ i, i < A → Lv i → ¬ cyc n s i
theorem natCast_ne {a b : ℕ} (h : a ≠ b) : (a : ℝ) ≠ b := by_simp_all

/-- Predecessors are unique. -/
theorem pred_unique {A n p p' : ℕ} (h : IsPredIn Lv A n p)
    (h' : IsPredIn Lv A n p') : p = p' := by
  have := cyc_start_eq' (natCast_ne h.2.2.1) (natCast_ne h'.2.2.1)
    (h.2.2.2 p' h'.1 h'.2.1) (h'.2.2.2 p h.1 h.2.1)
  simp_all

/-- Successors are unique. -/
theorem succ_unique {A n s s' : ℕ} (h : IsSuccIn Lv A n s)
    (h' : IsSuccIn Lv A n s') : s = s' := by
  have := cyc_end_eq (natCast_ne h.2.2.1.symm) (natCast_ne h'.2.2.1.symm)
    (h.2.2.2 s' h'.1 h'.2.1) (h'.2.2.2 s h.1 h.2.1)
  simp_all

/-- In a ring, `nxt` and `prv` are the successor and predecessor. -/
theorem RingOK.succ {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv) {j : ℕ}
    (hj : j < A) (hL : Lv j) : IsSuccIn Lv A j ztque := by
  obtain ⟨⟨a, b, c, d⟩, -⟩ := h j hj hL; trivial
theorem RingOK.pred {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv) {j : ℕ}
    (hj : j < A) (hL : Lv j) : IsPredIn Lv A j ztquu := by
  obtain ⟨-, ⟨a, b, c, d⟩⟩ := h j hj hL; trivial

/-- **The neighbours of a position bound a gap containing it**: if `p` and `s` are the live
predecessor and successor of a non-live `n` and differ, then `n` lies strictly between them and
no live position does. -/
theorem gap_of_pred_succ {A n p s : ℕ} (hn : n < A) (hnL : ¬ Lv n)
    (hp : IsPredIn Lv A n p) (hs : IsSuccIn Lv A n s) (hps : p ≠ s) :
    cyc p s n ∧ ∀ i, i < A → Lv i → ¬ cyc p s i := by
  have h1 : cyc p s n := by
    rcases cyc_three (natCast_ne hps) ztqtu (natCast_ne hs.2.2.1) with h | h
    · zubh
    · exact absurd h (hp.2.2.2 s hs.1 hs.2.1)
  refine ⟨h1, fun i hi hiL hin => ?_⟩
  rcases sideInArc_split hin h1 with h | h | h
  · zujuv
  · simp_all
  · zujuy

/-- If a non-live position has equal predecessor and successor, that is the only live
position. -/
theorem only_of_pred_eq_succ {A n p : ℕ} (_hn : n < A) (hnL : ¬ Lv n)
    (hp : IsPredIn Lv A n p) (hs : IsSuccIn Lv A n p) {i : ℕ} (hi : i < A) (hiL : Lv i) :
    i = p := by
  by_contra hip
  have hin : ztsjh := by_grind
  rcases cyc_cover ztqtu ztvzk with h | h | h
  · zujuv
  · simp_all
  · zujuy

/-- **Unlinking a live position** keeps the ring on the remaining live positions, provided its
two neighbours differ. -/
theorem ringOK_unlink {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv)
    {d : ℕ} (hd : d < A) (hdL : Lv d) (hne : prv d ≠ nxt d) :
    RingOK ztdnz A (Function.update nxt ztwbu ztwas)
      (Function.update prv ztwas ztwbu) := by
  obtain ⟨hs, hp⟩ := h d hd hdL
  set p := prv d
  set s := nxt d
  -- the new neighbours of `p` and `s`
  have hsp : IsSuccIn ztdnz A d s :=
    ⟨hs.1, by_simp_all, hs.2.2.1, by_simp_all⟩
  have hpp : IsPredIn ztdnz A d p :=
    ⟨hp.1, by_simp_all, hp.2.2.1, by_simp_all⟩
  obtain ⟨hgap1, hgap2⟩ := gap_of_pred_succ hd by_omega hpp hsp hne
  intro j hj ⟨hjL, hjd⟩
  constructor
  · by_cases hjp : j = p
    · grind
    · rw [Function.update_of_ne hjp]
      obtain ⟨a, b, c, e⟩ := (h j hj hjL).1
      have hnd : nxt j ≠ d := by
        intro hnd
        have h1 : IsPredIn Lv A d j := ztooj
        exact hjp (pred_unique h1 (h.pred hd hdL))
      simp_all
  · by_cases hjs : j = s
    · simp_all
    · rw [Function.update_of_ne hjs]
      obtain ⟨a, b, c, e⟩ := (h j hj hjL).2
      have hpd : prv j ≠ d := by
        intro hpd
        have h1 : IsSuccIn Lv A d j := ztooj
        exact hjs (succ_unique h1 (h.succ hd hdL))
      simp_all

/-- The ring on no live position. -/
theorem ringOK_empty (h : ∀ j, j < A → ¬ Lv j) (nxt prv : ℕ → ℕ) :
    RingOK Lv A nxt prv := fun j hj hL => by_simp_all

/-- A ring is insensitive to the pointers at dead positions. -/
theorem RingOK.congr {Lv Lv' : ℕ → Prop} {A : ℕ} {nxt prv nxt' prv' : ℕ → ℕ}
    (h : RingOK Lv A nxt prv) (hL : ∀ j, j < A → (Lv' j ↔ Lv j))
    (hn : ∀ j, j < A → Lv j → nxt' j = nxt j) (hp : ∀ j, j < A → Lv j → prv' j = prv j) :
    RingOK Lv' A nxt' prv' := by
  intro j hj hjL
  have hjL' := (hL j hj).1 hjL
  obtain ⟨⟨a, b, c, e⟩, ⟨a', b', c', e'⟩⟩ := h j hj hjL'
  simp_all

/-- No position lies strictly between `j` and `j + 1`. -/
theorem not_cyc_succ (j i : ℕ) : ¬ cyc j ztl i := by
  zuluk
  push_cast
  rw [ite_eq_left by_linarith]
  zukoh
  have h1 : j < i := by_simp_all
  have h2 : (i : ℝ) < ((j + 1 : ℕ) : ℝ) := by_simp_all
  have h3 : i < j + 1 := by exact_mod_cast h2
  omega

/-- No position below `A` lies strictly (cyclically) between `A - 1` and `0`. -/
theorem not_cyc_wrap (hA : 1 ≤ A) {i : ℕ} (hi : i < A) : ¬ cyc (A - 1) 0 i := by
  zuluk
  by_cases h : ((A - 1 : ℕ) : ℝ) < ((0 : ℕ) : ℝ)
  · simp_all
  · zubme
    zuknw
    · have : A - 1 < i := by exact_mod_cast a
      omega
    grind

/-- **The initial ring**: all positions `< A` live, `nxt i = i + 1 mod A`, `prv i = i - 1 mod A`
(for `A ≥ 2`). -/
theorem ringOK_full (hA : 2 ≤ A) :
    RingOK ztrpr A (fun i => if i + 1 < A then i + 1 else 0)
      (fun i => if 0 < i then i - 1 else A - 1) := by
  intro j hj _
  zubi
  refine ⟨⟨by_grind, trivial, by_grind, fun i hi _ => ?_⟩,
    ⟨by_grind, trivial, by_grind, fun i hi _ => ?_⟩⟩
  · by_cases h : j + 1 < A
    · zvnbq; exact not_cyc_succ j i
    · rw [ite_eq_right h, show j = A - 1 by omega]; exact not_cyc_wrap by_omega hi
  · by_cases h : 0 < j
    · zueyn
      have := not_cyc_succ zthv i
      grind
    · rw [ite_eq_right h, show j = 0 by omega]; exact not_cyc_wrap by_omega hi

/-- **The live predecessor after deleting at most two positions** `n` and `m` (the predecessor of
`n`, skipping `prv n` if it is deleted too), provided a live position remains. -/
theorem pred_skip {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv)
    {Dd : ℕ → Prop} [DecidablePred Dd] {n m : ℕ} (hn : n < A) (hnL : Lv n) (hDn : Dd n)
    (hD : ∀ j, Dd j → j = n ∨ j = m) (hex : ∃ i, i < A ∧ Lv i ∧ ¬ Dd i) :
    IsPredIn ztlog A n (if Dd ztwbv then prv ztwbv else prv n) := by
  have hp := h.pred hn hnL
  set p := prv n
  by_cases hDp : Dd p
  · rw [ite_eq_left hDp]
    have hpm := (hD p hDp).resolve_left hp.2.2.1
    have hpp := h.pred hp.1 hp.2.1
    set pp := prv p
    zudep

    have hip : i ≠ p := by_grind
    have hppn : pp ≠ n := by
      zuchf
      rcases cyc_cover ztvzl ztvzj with h1 | h1 | h1
      · zvmyr at h1; exact hpp.2.2.2 i hi hiL h1
      · simp_all
      · zujuw
    have hDpp : ¬ Dd pp := by
      zudqe
      rcases hD pp hd with e | e
      · omega
      · exact hpp.2.2.1 (e.trans hpm.symm)
    have hmid : cyc pp n p := by
      rcases cyc_three (natCast_ne hppn) (natCast_ne hpp.2.2.1) ztvzl
        with h1 | h1
      · zubvv
      · exact absurd h1 (hpp.2.2.2 n hn hnL)
    refine ⟨hpp.1, ⟨hpp.2.1, hDpp⟩, hppn, fun j hj hjL h1 => ?_⟩
    zugsi
    · exact hpp.2.2.2 j hj hjL.1 h2
    · simp_all
    · exact hp.2.2.2 j hj hjL.1 h2
  · rw [ite_eq_right hDp]
    exact ⟨hp.1, ⟨hp.2.1, hDp⟩, hp.2.2.1, fun j hj hjL => hp.2.2.2 j hj hjL.1⟩

/-- **The live successor after deleting at most two positions.** -/
theorem succ_skip {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv)
    {Dd : ℕ → Prop} [DecidablePred Dd] {n m : ℕ} (hn : n < A) (hnL : Lv n) (hDn : Dd n)
    (hD : ∀ j, Dd j → j = n ∨ j = m) (hex : ∃ i, i < A ∧ Lv i ∧ ¬ Dd i) :
    IsSuccIn ztlog A n (if Dd ztwat then nxt ztwat else nxt n) := by
  have hs := h.succ hn hnL
  set s := nxt n
  by_cases hDs : Dd s
  · rw [ite_eq_left hDs]
    have hsm := (hD s hDs).resolve_left hs.2.2.1
    have hss := h.succ hs.1 hs.2.1
    set ss := nxt s
    zudep

    have his : i ≠ s := by_grind
    have hssn : ss ≠ n := by
      zuchf
      rcases cyc_cover ztvzm ztvzj with h1 | h1 | h1
      · zujuz
      · simp_all
      · zvmyr at h1; exact hss.2.2.2 i hi hiL h1
    have hDss : ¬ Dd ss := by
      zudqe
      rcases hD ss hd with e | e
      · omega
      · exact hss.2.2.1 (e.trans hsm.symm)
    have hmid : cyc n ss s := by
      rcases cyc_three (natCast_ne hssn.symm) ztvzm
        (natCast_ne hss.2.2.1) with h1 | h1
      · zubvv
      · -- `ss` lies between `n` and `s`, impossible
        exact absurd h1 (hs.2.2.2 ss hss.1 hss.2.1)
    refine ⟨hss.1, ⟨hss.2.1, hDss⟩, hssn, fun j hj hjL h1 => ?_⟩
    zugsi
    · exact hs.2.2.2 j hj hjL.1 h2
    · simp_all
    · exact hss.2.2.2 j hj hjL.1 h2
  · rw [ite_eq_right hDs]
    exact ⟨hs.1, ⟨hs.2.1, hDs⟩, hs.2.2.1, fun j hj hjL => hs.2.2.2 j hj hjL.1⟩
end
end Gran
end Chazelle.Core
namespace Chazelle.Core
namespace Gran
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

/-! ## The environment -/

/-- The fixed data of a run. -/
structure Env where
  /-- The model. -/
  M : Model
  /-- The height polygon. -/
  Q : Polygon
  /-- The input normal form. -/
  N : NF
  /-- Its region correspondence. -/
  reg : ℕ → Set Point
  /-- The target granularity. -/
  γ : ℕ
  /-- The degree cap. -/
  D : ℕ
  /-- The model kind (`true`: chain model). -/
  ch : Bool
  /-- The number of chain edges (chain model). -/
  m : ℕ
namespace Env
variable (E : Env)

/-- Number of chords. -/
abbrev K : ℕ := E.N.nChords
/-- Number of arcs (ring positions). -/
abbrev A : ℕ := E.N.arcs.length
/-- Number of regions. -/
abbrev R : ℕ := E.N.nRegions
/-- Number of walk edges. -/
abbrev n : ℕ := E.M.W.n

/-- The hypotheses on the environment. -/
structure Good : Prop where
  hM : WalkAx E.M
  hGM : GoodModel E.M
  hNF : IsNF E.M E.Q E.N
  hRC : RegionCorr E.M E.Q E.N E.reg
  hCS : ChordSidesOK E.M E.Q E.N E.reg
  hRO : RegionsOK E.M E.Q E.N E.reg
  hne : (E.N.F E.M E.Q).Nonempty
  hcd : CountDesc E.M E.ch E.m
  hn : E.ch = true → E.n = 2 * E.m + 7
end Env

/-! ## The state -/

/-- The state of the granularity procedure. -/
structure St where
  live : ℕ → ℕ
  s0 : ℕ → ℕ
  s1 : ℕ → ℕ
  nd0 : ℕ → ℕ
  nd1 : ℕ → ℕ
  deg : ℕ → ℕ
  wt : ℕ → ℕ
  ex : ℕ → ℕ → ℕ
  cnt : ℕ → ℕ
  nxt : ℕ → ℕ
  prv : ℕ → ℕ
  eg : ℕ → ℕ
  pz : ℕ → ℕ
  stk : ℕ → ℕ
  top : ℕ
  nlive : ℕ

/-- The region of `G` containing `U` (if any). -/
noncomputable def supR (M : Model) (G : Set ztf) (U : Set Point) : Set Point := by
  classical
  exact if h : ∃ Z ∈ M.regions G, U ⊆ Z then h.choose else ∅
variable {M : Model} {G : Set (Set Point)}
theorem supR_spec {U : Set Point}
    (h : ∃ Z ∈ M.regions G, U ⊆ Z) : supR M G U ∈ M.regions G ∧ U ⊆ supR M G U := by
  unfold supR
  grind
theorem supR_eq {U Z : Set Point} (hU : U.Nonempty)
    (hZ : Z ∈ M.regions G) (hUZ : U ⊆ Z) : supR M G U = Z := by
  obtain ⟨h1, h2⟩ := supR_spec ⟨Z, hZ, hUZ⟩
  exact Chazelle.Chain.regionsIn_eq_of_subset h1 hZ hU h2 hUZ
namespace St
variable (E : Env) (st : St)

/-- The live chord indices. -/
def L : Set ℕ := {i | i < E.K ∧ st.live i = 1}

/-- **The current submap.** -/
def F : Set ztf := fam E.M E.Q E.N (st.L E)

/-- The region of the current submap containing the region `x` of the input (class `x`). -/
noncomputable def cl (x : ℕ) : Set Point := supR E.M ztbhy ztpxo

/-- The exit chords of class `x`. -/
def exl (x : ℕ) : List ℕ := List.ofFn fun t : Fin (st.deg x) => st.ex x t

/-- Class `x` is referenced by a live chord. -/
def Ref (x : ℕ) : Prop := ∃ i ∈ st.L E, x = st.s0 i ∨ x = st.s1 i

/-- Live ring positions. -/
def Lv (j : ℕ) : Prop := 0 < st.cnt j

/-- The number of live chords attached at position `j`. -/
def cntOf (j : ℕ) : ℕ :=
  ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).card +
    ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).card
end St

/-- The start key of position `j`. -/
noncomputable def Env.key (E : Env) (j : ℕ) : ℝ := pk E.M E.Q E.N j

/-- The parameter of the start of position `j`. -/
noncomputable def Env.par (E : Env) (j : ℕ) : ℝ := E.M.param E.Q (E.N.arc ztsww).s

/-- The number of counted edges before the edge `e` (for `e` below the last walk edge). -/
def bB (ch : Bool) (e : ℕ) : ℕ := if ch then e - 6 else e

/-- **The integer weight of the key interval between two positions** from the values
`bb j = bB (edge of j)`, the bumps `xb j` (`1` iff the edge of `j` is counted and the
parameter of `j` is positive) and the number `sz` of counted edges. -/
def gwt (sz : ℕ) (bb xb : ℕ → ℕ) (a b : ℕ) : ℕ :=
  if a = b then sz
  else if a < b then bb b + xb b - bb a
  else (sz - bb a) + min (bb b + xb b) (bb a)

/-- The start edge of position `j`. -/
def Env.edge (E : Env) (j : ℕ) : ℕ := (E.N.arc ztsww).s.edge

/-- The number of counted edges. -/
def Env.sz (E : Env) : ℕ := cntIn E.ch E.m 0 E.n

/-- The static data of the state are correct. -/
structure StatOK (E : Env) (st : St) : Prop where
  nd0 : ∀ i, i < E.K → st.nd0 i < E.A ∧ E.key (st.nd0 i) = E.M.key E.Q (E.N.chord i).lpos
  nd1 : ∀ i, i < E.K → st.nd1 i < E.A ∧ E.key (st.nd1 i) = E.M.key E.Q (E.N.chord i).rpos
  eg : ∀ j, j < E.A → st.eg j = bB E.ch ztuxw
  pz : ∀ j, j < E.A → st.pz j ≤ 1 ∧ (st.pz j = 1 ↔ (E.M.counted ztuxw ∧ E.par j ≠ 0))

/-- The static data only depend on the static arrays. -/
theorem StatOK.congr {E : Env} {st st' : St} (h : StatOK E st) (h0 : st'.nd0 = st.nd0)
    (h1 : st'.nd1 = st.nd1) (h2 : st'.eg = st.eg) (h3 : st'.pz = st.pz) : StatOK E st' := by
  obtain ⟨a, b, c, d⟩ := h
  refine ztfh <;> simp only [h0, h1, h2, h3] <;> assumption

/-- **The invariant.** -/
structure Inv (E : Env) (st : St) : Prop where
  stat : StatOK E st
  live01 : ∀ i, i < E.K → st.live i ≤ 1
  nlive : st.nlive = (st.L E).ncard
  degLe : E.M.DegLe ztbhy E.D
  semi : E.M.Semigranular ztbhy E.γ
  sides : ∀ i ∈ st.L E, st.s0 i < E.R ∧ st.s1 i < E.R ∧ st.cl E ztibc ≠ st.cl E ztqwy ∧
    ∀ X ∈ E.M.regions ztbhy, (TouchesIn E.M.D ztbbw X ↔
      X = st.cl E ztibc ∨ X = st.cl E ztqwy)
  cls : ∀ x, st.Ref E x → st.deg x = E.M.deg ztbhy ztoik ∧
    st.wt x = E.M.weight ztbhy ztoik ∧ (st.exl x).Nodup ∧
    (∀ i, i ∈ st.exl x ↔ i ∈ st.L E ∧ TouchesIn E.M.D ztbbw ztoik) ∧
    st.deg x ≤ E.D
  refInj : ∀ x y, st.Ref E x → st.Ref E y → st.cl E x = st.cl E y → x = y
  cnt : ∀ j, j < E.A → st.cnt j = st.cntOf E j
  ring : RingOK st.Lv E.A st.nxt st.prv
  stk : ∀ t, t < st.top → st.stk t < E.K
  topLe : st.top + E.D * st.nlive ≤ E.K + E.D * E.K
  work : ∀ i ∈ st.L E, (∀ t, t < st.top → st.stk t ≠ i) →
    ¬ Merge.Removable E.M.D E.M.weight E.γ ztbhy ztbbw
namespace St
variable {E : Env} {st : St}
theorem F_sub : st.F E ⊆ E.N.F E.M E.Q := fam_sub _
theorem F_adm (hE : E.Good) : st.F E ⊆ E.M.Adm := fam_adm hE.hNF _
theorem F_finite (hE : E.Good) : (st.F E).Finite := fam_finite hE.hNF _
theorem cs_mem_F {i : ℕ} (hi : i ∈ st.L E) : cs E.M E.Q E.N i ∈ st.F E := ⟨i, hi, hi.1, rfl⟩
end St
namespace Inv
variable {E : Env} {st : St}

/-- The class of `x` is a region of the current submap containing the input region `x`. -/
theorem _root_.Chazelle.Core.Gran.St.cl_spec (hE : E.Good) {x : ℕ} (hx : x < E.R) :
    st.cl E x ∈ E.M.regions ztbhy ∧ E.reg x ⊆ st.cl E x := by
  refine supR_spec ?_
  exact Chazelle.Chain.exists_regionsIn_superset St.F_sub zthhp

/-- Live positions are those with a live chord attached. -/
theorem lv_iff (h : Inv E st) {j : ℕ} (hj : j < E.A) :
    st.Lv j ↔ ∃ i ∈ st.L E, st.nd0 i = j ∨ st.nd1 i = j := by
  unfold St.Lv
  rw [h.cnt j hj]
  zultw
  constructor
  · zulmx
    by_cases h0 : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).card
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 h0
      zudld
      tauto
    · have h1 : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).card := by
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.1 h1
      zudld
      exact ⟨i, ⟨hi.1, hi.2.1⟩, Or.inr hi.2.2⟩
  · rintro ⟨i, ⟨hiK, hil⟩, h0 | h1⟩
    · have : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).card :=
        Finset.card_pos.2 ztkly
      omega
    · have : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).card :=
        Finset.card_pos.2 ztkly
      omega

/-- **The cuts of the current submap are the start keys of the live positions.** -/
theorem cut_iff (hE : E.Good) (h : Inv E st) (k : ℝ) :
    E.M.IsCut ztbhy k ↔ ∃ j, j < E.A ∧ st.Lv j ∧ E.key j = k := by
  unfold St.F
  rw [isCut_fam_iff hE.hNF hE.hM]
  constructor
  · rintro ⟨i, hiL, hi, hk | hk⟩
    · obtain ⟨h1, h2⟩ := h.stat.nd0 i hi
      exact ⟨st.nd0 i, h1, (h.lv_iff h1).2 by_grind, by_simp_all⟩
    · obtain ⟨h1, h2⟩ := h.stat.nd1 i hi
      exact ⟨st.nd1 i, h1, (h.lv_iff h1).2 by_grind, by_simp_all⟩
  · rintro ⟨j, hj, hL, rfl⟩
    obtain ⟨i, hiL, h0 | h1⟩ := (h.lv_iff hj).1 hL
    · refine ⟨i, hiL, hiL.1, Or.inl ?_⟩
      zuosa; exact (h.stat.nd0 i hiL.1).2
    · refine ⟨i, hiL, hiL.1, Or.inr ?_⟩
      rw [← h1]; exact (h.stat.nd1 i hiL.1).2
end Inv
variable {E : Env} {st : St}

/-- The start keys are strictly increasing. -/
theorem key_strict (hE : E.Good) {i i' : ℕ} (hii : i < i') (hi' : i' < E.A) :
    E.key i < E.key i' := pk_strict hE.hNF hE.hne hii hi'

/-- Cyclic betweenness of positions is cyclic betweenness of their keys. -/
theorem key_cyc_iff (hE : E.Good) {a b i : ℕ} (ha : a < E.A) (hb : b < E.A) (hi : i < E.A) :
    sideInArc ztuxy ztuxz (E.key i) ↔ cyc a b i :=
  sideInArc_mono_iff (fun _ _ h h' => key_strict hE h h') ha hb hi
theorem key_inj (hE : E.Good) {a b : ℕ} (ha : a < E.A) (hb : b < E.A)
    (h : E.key a = E.key b) : a = b := pk_inj hE.hNF hE.hne ha hb h

/-- The start of position `j` is a proper position. -/
theorem par_mem (hE : E.Good) {j : ℕ} (hj : j < E.A) : 0 ≤ E.par j ∧ E.par j < 1 :=
  let h := (hE.hNF.2.2.2.choose_spec.2.2.2.2.2.2 _ (NFLoc.seq_lt hE.hNF hj)).1
  ⟨h.1, h.2.1⟩

/-- The start edge of a position is a walk edge. -/
theorem edge_lt (hE : E.Good) {j : ℕ} (hj : j < E.A) : E.edge j < E.n := by
  have hc := pk_cut hE.hNF hE.hne hj
  have hb := WalkAx.cut_bounds hc
  have hpar := par_mem hE hj
  have e : pk E.M E.Q E.N j = (E.edge j : ℝ) + E.par j := rfl
  zvmwe at hb
  have : (E.edge j : ℝ) < E.n := by_grind
  simp_all

/-- The key of a position: its edge plus its parameter. -/
theorem key_edge (j : ℕ) : E.key j = (E.edge j : ℝ) + E.par j := rfl

/-- Increasing keys have nondecreasing edges. -/
theorem edge_mono (hE : E.Good) {a b : ℕ} (ha : a < E.A) (hb : b < E.A)
    (hlt : E.key a < E.key b) : E.edge a ≤ E.edge b := by
  have ha0 := (par_mem hE ha).1
  have hb1 := (par_mem hE hb).2
  rw [key_edge, key_edge] at hlt
  zudxc
  have : (E.edge b : ℝ) + 1 ≤ E.edge a := by exact_mod_cast by_simp_all
  linarith

/-- **The integer weight of two positions is the weight of the key interval.** -/
theorem gw_eq (hE : E.Good) (h : StatOK E st) {a b : ℕ} (ha : a < E.A) (hb : b < E.A) :
    gwt E.sz st.eg st.pz a b = E.M.arcWt ztuxy ztuxz := by
  have ea := edge_lt hE ha
  have eb := edge_lt hE hb
  obtain ⟨pa0, pa1⟩ := par_mem hE ha
  obtain ⟨pb0, pb1⟩ := par_mem hE hb
  rw [key_edge, key_edge, arcWt_formula hE.hcd ea eb pa0 pa1 pb0 pb1, ← key_edge, ← key_edge]
  have hcnt : E.M.counted _ ↔ (E.ch = false ∨ (6 ≤ E.edge b ∧ E.edge b < 2 * E.m + 6)) :=
    hE.hcd.2 _ eb
  obtain ⟨hpz1, hpz⟩ := h.pz b hb
  zumed
  -- the bump and the stored bit
  have hbx : (E.M.counted ztmat → bump ztuyb = st.pz b) ∧
      (¬ E.M.counted ztmat → st.pz b = 0) := by
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · unfold bump
      grind
    grind
  have hb01 : bump ztuyb ≤ 1 := by unfold bump; grind
  zuhzi
  unfold gwt Env.sz
  rw [h.eg a ha, h.eg b hb]
  zufqx
  · simp_all
  have hk := fun e => hab (key_inj hE ha hb e)
  rw [ite_eq_right hab, ite_eq_right hk]
  zufrd
  · have hkl := key_strict hE hlt hb
    have hle := edge_mono hE ha hb hkl
    rw [ite_eq_left hlt, ite_eq_left hkl]
    cases hch : E.ch with
    | false =>
      zuhyd
      have := hbx.1 hc
      zufqb

    | true =>
      zulks
      zubma

      unfold cntIn bB
      zuwa
      by_cases hc : E.M.counted ztmat
      · grind
      · grind
  · have hlt' : ztsdo := by_omega
    have hkl := key_strict hE hlt' ha
    have hle := edge_mono hE hb ha hkl
    rw [ite_eq_right hlt, ite_eq_right (not_lt.2 hkl.le)]
    cases hch : E.ch with
    | false =>
      zuhyd
      have := hbx.1 hc
      zufqb

    | true =>
      zulks
      zubma

      unfold cntIn bB
      zuwa
      by_cases hc : E.M.counted ztmat
      · have := hcnt.1 hc
        have := hbx.1 hc
        zuipq

      · have h1 := mt hcnt.2 hc
        have := hbx.2 hc
        zuipq

/-- `size` by integer arithmetic. -/
theorem size_eq (hE : E.Good) : E.M.size = cntIn E.ch E.m 0 E.n := by
  rw [← ncard_counted hE.hcd le_rfl]
  zujpy
  grind

/-! ## The end of the run -/

/-- **With an empty worklist the current submap is γ-granular with degrees `≤ D`.** -/
theorem Inv.final (_hE : E.Good) (h : Inv E st) (htop : st.top = 0) :
    E.M.Granular ztbhy E.γ ∧ E.M.DegLe ztbhy E.D := by
  refine ⟨⟨h.semi, ?_⟩, h.degLe⟩
  have : Merge.ContractionCondIn E.M.D E.M.weight ztbhy E.γ := by
    zumlt
    zung
    have hcS := hc.1
    obtain ⟨i, hiL, -, rfl⟩ := hcS
    exact h.work i hiL by_simp_all hc
  tauto
namespace St
variable (E : Env) (st : St)

/-- Pop the worklist. -/
def pop : St := { st with top := st.top - 1 }

/-- The chord on top of the worklist. -/
def cur : ℕ := st.stk zthkp

/-- Position `j` stops being live when chord `c` is removed. -/
def dd (c j : ℕ) : Bool :=
  (decide (j = st.nd0 c) && decide (st.cnt zteat = 1)) ||
    (decide (j = st.nd1 c) && decide (st.cnt ztfir = 1))

/-- The live predecessor of `k` after the removal of `c` (skipping one dead position). -/
def prD (c k : ℕ) : ℕ := if st.dd c ztmon then st.prv ztmon else st.prv k

/-- The live successor of `k` after the removal of `c`. -/
def suD (c k : ℕ) : ℕ := if st.dd c ztkfm then st.nxt ztkfm else st.nxt k

/-- The weight of the gap around position `k` after the removal of `c`, if `k` dies. -/
def jw (c k : ℕ) : ℕ :=
  if st.cnt k = 1 then gwt E.sz st.eg st.pz (st.prD c k) (st.suD c k) else 0

/-- **The merged weight** (the weight of the region of the new submap merging the two classes of
`c`). -/
def mu (c : ℕ) : ℕ :=
  if st.nlive = 1 then cntIn E.ch E.m 0 E.n
  else max (max (st.wt zttb) (st.wt ztsm)) (max (st.jw E c zteat)
    (st.jw E c ztfir))
end St
variable {E : Env} {st : St}

/-! ## Popping -/
theorem Inv.pop_of (h : Inv E st) (htop : 0 < st.top)
    (hc : st.cur ∈ st.L E → ¬ Merge.Removable E.M.D E.M.weight E.γ ztbhy
      ztjsx) : Inv E st.pop := by
  show Inv E { st with top := st.top - 1 }
  refine ⟨h.stat.congr rfl rfl rfl rfl, h.live01, h.nlive, h.degLe, h.semi, h.sides, h.cls, h.refInj, h.cnt, h.ring,
    fun t ht => h.stk t by_grind, ?_, ?_⟩
  · have := h.topLe; grind
  · zumgw
    by_cases hic : i = st.cur
    · subst hic; tauto
    · refine h.work i hi fun t ht => ?_
      zuhtj
      · zumqf
      grind

/-- **Popping a dead chord.** -/
theorem Inv.pop_dead (h : Inv E st) (htop : 0 < st.top) (hd : st.live st.cur ≠ 1) :
    Inv E st.pop := h.pop_of htop fun hi => absurd hi.2 hd

/-- **Popping a live chord that is not removable.** -/
theorem Inv.pop_keep (h : Inv E st) (htop : 0 < st.top)
    (hnr : ¬ Merge.Removable E.M.D E.M.weight E.γ ztbhy ztjsx) :
    Inv E st.pop := h.pop_of htop fun _ => hnr

/-! ## Gaps -/

/-- **Two gaps containing the same key coincide.** -/
theorem gap_unique {M : Model} {G : Set ztf} {l r l' r' x : ℝ} (hg : Gap M G l r)
    (hg' : Gap M G l' r') (hx : sideInArc l r x) (hx' : sideInArc l' r' x) : l = l' ∧ r = r' := by
  obtain ⟨hl, hr, hlr, hf⟩ := hg
  obtain ⟨hl', hr', hlr', hf'⟩ := hg'
  have hxl : x ≠ l := by_grind
  have hxl' : x ≠ l' := by_grind
  have hxr : x ≠ r := by_grind
  have hxr' : x ≠ r' := by_grind
  refine ⟨cyc_start_eq' (Ne.symm hxl) (Ne.symm hxl') (fun h1 => hf l' (cyc_sub_mid hx h1) hl')
    (fun h1 => hf' l (cyc_sub_mid hx' h1) hl), cyc_end_eq hxr hxr'
      (fun h1 => hf r' (cyc_sub_mid' hx h1) hr') (fun h1 => hf' r (cyc_sub_mid' hx' h1) hr)⟩

/-! ## Counting the chords at a position -/
theorem card_filter_two (K : ℕ) (P₀ P₁ : ℕ → Prop) [DecidablePred P₀] [DecidablePred P₁] {c : ℕ}
    (hcK : c < K) (h0 : P₀ c) (h1 : ¬ P₁ c) :
    ((Finset.range K).filter P₀).card + ((Finset.range K).filter P₁).card = 1 ↔
      ∀ i, i < K → i ≠ c → ¬ P₀ i ∧ ¬ P₁ i := by
  have hc0 : c ∈ (Finset.range K).filter P₀ := by_simp_all
  constructor
  · intro h i hi hic
    have hpos := Finset.card_pos.2 ⟨c, hc0⟩
    have h1' : ((Finset.range K).filter P₁).card = 0 := by_omega
    have h0' : ((Finset.range K).filter P₀).card = 1 := by_omega
    rw [Finset.card_eq_zero] at h1'
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h0'
    refine ztlvy
    · have hi0 : i ∈ (Finset.range K).filter P₀ := by_grind
      simp_all
    simp_all
  · zuq
    have e0 : (Finset.range K).filter P₀ = {c} := by
      grind
    have e1 : (Finset.range K).filter P₁ = ∅ := by
      grind
    simp_all

/-- The two positions of a live chord differ. -/
theorem Inv.nd_ne (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) :
    st.nd0 c ≠ st.nd1 c := by
  zuchf
  have h0 := (h.stat.nd0 c hc.1).2
  have h1 := (h.stat.nd1 c hc.1).2
  rw [e, h1] at h0
  exact lkey_ne_rkey hE.hNF hE.hM hc.1 h0.symm

/-- **A position of a live chord `c` has count `1` iff no other live chord is attached there.** -/
theorem Inv.cnt_eq_one_iff (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {j : ℕ}
    (hj : j = st.nd0 c ∨ j = st.nd1 c) :
    st.cnt j = 1 ↔ ∀ i ∈ st.L E, i ≠ c → st.nd0 i ≠ j ∧ st.nd1 i ≠ j := by
  have hjA : j < E.A := by
    zudsf
    · zuisl
    · zuism
  rw [h.cnt j hjA]
  zultw
  zucmk
  zudsf
  · rw [card_filter_two E.K _ _ hc.1 ztuhk by_omega]
    constructor
    · zudqc

      exact ⟨fun e => a ztkll, fun e => b ztkll⟩
    · zulmr
      refine ⟨fun hp => (h' i ztklk hic).1 hp.2, fun hp => (h' i ztklk hic).2 hp.2⟩
  · rw [add_comm, card_filter_two E.K _ _ hc.1 ztuhk by_omega]
    constructor
    · zudqc

      exact ⟨fun e => b ztkll, fun e => a ztkll⟩
    · zulmr
      refine ⟨fun hp => (h' i ztklk hic).2 hp.2, fun hp => (h' i ztklk hic).1 hp.2⟩

/-! ## The submap without `c` -/

/-- The live set without `c`. -/
theorem fam_diff (hE : E.Good) {c : ℕ} (hc : c ∈ st.L E) :
    fam E.M E.Q E.N (st.L E \ {c}) = st.F E \ {cs E.M E.Q E.N c} := by
  zufsm
  constructor
  · rintro ⟨i, ⟨hiL, hic⟩, hi, rfl⟩
    refine ⟨zthnh, fun he => hic ?_⟩
    exact cs_inj hE.hNF hi hc.1 he
  · rintro ⟨⟨i, hiL, hi, rfl⟩, hne⟩
    exact ⟨i, by_grind, hi, rfl⟩

/-- **The cuts after the removal of `c`**: the start keys of the live positions that do not die. -/
theorem Inv.cut_sdiff_iff (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) (k : ℝ) :
    E.M.IsCut ztfa k ↔
      ∃ j, j < E.A ∧ st.Lv j ∧ st.dd c j = false ∧ E.key j = k := by
  rw [← fam_diff hE hc, isCut_fam_iff hE.hNF hE.hM]
  constructor
  · rintro ⟨i, ⟨hiL, hic⟩, hi, hk⟩
    have hic' : ztsjg := by_simp_all
    -- the position of the attachment
    have hpos : ∃ j, (j = st.nd0 i ∨ j = st.nd1 i) ∧ j < E.A ∧ E.key j = k := by
      zucot
      · exact ⟨st.nd0 i, Or.inl rfl, (h.stat.nd0 i hi).1, by rw [(h.stat.nd0 i hi).2, hk]⟩
      · exact ⟨st.nd1 i, Or.inr rfl, (h.stat.nd1 i hi).1, by rw [(h.stat.nd1 i hi).2, hk]⟩
    obtain ⟨j, hji, hj, hkj⟩ := hpos
    refine ⟨j, hj, (h.lv_iff hj).2 by_grind, ?_, hkj⟩
    unfold St.dd
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    zujx
    · by_cases hj0 : j = st.nd0 c
      · right
        zudqd
        have := ((h.cnt_eq_one_iff hE hc ztp).1 h1 i hiL hic')
        omega
      omega
    · by_cases hj1 : j = st.nd1 c
      · right
        zudqd
        have := ((h.cnt_eq_one_iff hE hc ztbt).1 h1 i hiL hic')
        omega
      omega
  · rintro ⟨j, hj, hL, hdd, rfl⟩
    obtain ⟨i, hiL, hij⟩ := (h.lv_iff hj).1 hL
    -- if `i = c`, another live chord is attached at `j`
    have hkey : ∀ i', i' ∈ st.L E → (st.nd0 i' = j ∨ st.nd1 i' = j) →
        (E.key j = E.M.key E.Q (E.N.chord i').lpos ∨
          E.key j = E.M.key E.Q (E.N.chord i').rpos) := by
      rintro i' hi' (e | e)
      · left; zvmyr; exact (h.stat.nd0 i' hi'.1).2
      · right; zvmyr; exact (h.stat.nd1 i' hi'.1).2
    zujtk
    · subst hic
      unfold St.dd at hdd
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hdd
      obtain ⟨h0, h1⟩ := hdd
      have hj' : j = st.nd0 i ∨ j = st.nd1 i := by_omega
      have hnot : st.cnt j ≠ 1 := by
        grind
      have hnot' := mt (h.cnt_eq_one_iff hE hiL hj').2 hnot
      push Not at hnot'
      replace hnot := hnot'
      obtain ⟨i', hi', hi'c, hi'j⟩ := hnot
      have hi'j' : st.nd0 i' = j ∨ st.nd1 i' = j := by
        omega
      exact ⟨i', by_simp_all, hi'.1, by_simp_all⟩
    · exact ⟨i, by_simp_all, hiL.1, by_simp_all⟩

/-! ## The removal split of a live chord -/
theorem Inv.cl_mem (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) :
    st.cl E zttb ∈ E.M.regions ztbhy ∧ st.cl E ztsm ∈ E.M.regions ztbhy :=
  ⟨(St.cl_spec hE (h.sides c hc).1).1, (St.cl_spec hE (h.sides c hc).2.1).1⟩

/-- **Removing a live chord merges its two classes.** -/
theorem Inv.split (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) :
    ∃ P, Merge.IsSplit E.M.D ztfa ztbel P
      ztwnu ztwnt := by
  have hsys := hE.hM.sys _ ztgeu (St.F_finite (st := st) hE)
  obtain ⟨P, R₁, R₂, hs⟩ := Merge.exists_removal_split hsys subset_rfl ztccm
  zueid
  have hm₁ := split_mem₁ ztccm hs
  have hm₂ := split_mem₂ ztccm hs
  have t₁ := (split_touches_iff hE.hM ztgeu ztjmy ztccm hs hm₁).2
    ztp
  have t₂ := (split_touches_iff hE.hM ztgeu ztjmy ztccm hs hm₂).2
    ztbt
  have hne := hs.ne
  rcases (htouch R₁ hm₁).1 t₁ with e1 | e1 <;> rcases (htouch R₂ hm₂).1 t₂ with e2 | e2
  · simp_all
  · grind
  · subst e1 e2; exact ⟨P, hs.symm⟩
  simp_all

/-- **Removability from the state.** -/
theorem Inv.removable_iff (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {P : Set Point}
    (hs : Merge.IsSplit E.M.D ztfa ztbel P
      ztwnu ztwnt) :
    Merge.Removable E.M.D E.M.weight E.γ ztbhy ztbel ↔
      (st.deg zttb < 3 ∨ st.deg ztsm < 3) ∧
        E.M.weight ztfa P ≤ E.γ := by
  obtain ⟨-, -, hne, htouch⟩ := h.sides c hc
  zugph
  have dX : ztlyu :=
    (h.cls _ ztcjr).1
  have dY : ztlyu :=
    (h.cls _ ztcjs).1
  constructor
  · rintro ⟨-, U, hU, V, hV, hUV, hcU, hcV, hlow, hW⟩
    rcases (htouch U hU).1 hcU with rfl | rfl <;> rcases (htouch V hV).1 hcV with rfl | rfl
    · simp_all
    · exact ⟨by_omega, hW P hs.mem hs.sub₁⟩
    · exact ⟨by_omega, hW P hs.mem hs.sub₂⟩
    simp_all
  · rintro ⟨hlow, hw⟩
    refine ⟨St.cs_mem_F hc, _, hX, _, hY, hne, by_simp_all,
      by simp_all, by_omega, fun W hW hsub => ?_⟩
    rw [Chazelle.Chain.regionsIn_eq_of_subset hW hs.mem ztuxm
      hsub hs.sub₁]
    zulzb

/-! ## The merged weight -/

/-- The key of a position of a live chord is a cut of the current submap. -/
theorem Inv.key_nd_cut (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {n : ℕ}
    (hn : n = st.nd0 c ∨ n = st.nd1 c) : n < E.A ∧ st.Lv n ∧ E.M.IsCut ztbhy ztuya := by
  have hnA : n < E.A := by
    rcases hn with rfl | rfl
    · zuisl
    · zuism
  have hL := (h.lv_iff hnA).2 by_grind
  exact ⟨hnA, hL, (h.cut_iff hE _).2 by_grind⟩

/-- `dd` at a position of `c`. -/
theorem Inv.dd_iff (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {n : ℕ}
    (hn : n = st.nd0 c ∨ n = st.nd1 c) : st.dd c n = true ↔ st.cnt n = 1 := by
  zucmk
  unfold St.dd
  grind

/-- The dying positions are the positions of `c` with count `1`. -/
theorem Inv.dd_cases (_hE : E.Good) (_h : Inv E st) {c : ℕ} (_hc : c ∈ st.L E) {j : ℕ}
    (hj : st.dd c j = true) : (j = st.nd0 c ∨ j = st.nd1 c) ∧ st.cnt j = 1 := by
  zumdq
  unfold St.dd at hj'
  grind

/-- **The lost keys of `c`** are the start keys of its positions of count `1`. -/
theorem Inv.lost_iff (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {k : ℝ} :
    k ∈ lostKeys E.M ztbhy ztbel ↔
      ∃ n, ztfti ∧ st.cnt n = 1 ∧ k = E.key n := by
  constructor
  · rintro hk
    obtain ⟨p, t, hA, rfl, -⟩ := lost_attach ztccm hk
    have hkeys := attach_keys hE.hNF hE.hM hc.1 hA
    have hpos : ∃ n, ztfti ∧ (p : ℝ) + t = E.key n := by
      rcases hkeys with e | e
      · exact ⟨st.nd0 c, Or.inl rfl, by rw [e, (h.stat.nd0 c hc.1).2]⟩
      · exact ⟨st.nd1 c, Or.inr rfl, by rw [e, (h.stat.nd1 c hc.1).2]⟩
    obtain ⟨n, hn, hkn⟩ := hpos
    obtain ⟨hnA, hL, -⟩ := h.key_nd_cut hE hc hn
    refine ⟨n, hn, ?_, hkn⟩
    rw [← h.dd_iff hE hc hn]
    by_contra hdd
    exact hk.2 ((h.cut_sdiff_iff hE hc _).2 by_grind)
  · rintro ⟨n, hn, h1, rfl⟩
    obtain ⟨hnA, hL, hcut⟩ := h.key_nd_cut hE hc hn
    refine ⟨hcut, fun hcut' => ?_⟩
    obtain ⟨j, hj, -, hdd, hkj⟩ := (h.cut_sdiff_iff hE hc _).1 hcut'
    have := key_inj hE hj hnA hkj
    zumo
    rw [(h.dd_iff hE hc hn).2 h1] at hdd
    simp_all

/-- **The gap around a dying position** after the removal of `c`. -/
theorem Inv.dead_gap (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
    (hne' : (st.F E \ {cs E.M E.Q E.N c}).Nonempty) {n : ℕ}
    (hn : n = st.nd0 c ∨ n = st.nd1 c) (h1 : st.cnt n = 1) :
    st.prD c n < E.A ∧ st.suD c n < E.A ∧
      Gap E.M ztfa ztiha ztihb ∧
      sideInArc ztiha ztihb ztuya := by
  obtain ⟨hnA, hnL, -⟩ := h.key_nd_cut hE hc hn
  have hDn := (h.dd_iff hE hc hn).2 h1
  set m := if n = st.nd0 c then st.nd1 c else st.nd0 c with hm
  have hD : ∀ j, st.dd c j = true → j = n ∨ j = m := by
    zun
    obtain ⟨hj', -⟩ := h.dd_cases hE hc hj
    grind
  -- two cuts remain
  have hS'adm : st.F E \ {cs E.M E.Q E.N c} ⊆ E.M.Adm :=
    sdiff_subset.trans ztgeu
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hE.hM.two_cuts hS'adm hne'
  obtain ⟨j₁, hj₁, hL₁, hd₁, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₁
  obtain ⟨j₂, hj₂, hL₂, hd₂, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₂
  have hex : ∃ i, i < E.A ∧ st.Lv i ∧ ¬ st.dd c i = true := by_grind
  have hp := pred_skip h.ring hnA hnL hDn hD hex
  have hs := succ_skip h.ring hnA hnL hDn hD hex
  have hpe : st.prD c n = (if st.dd c _ = true then st.prv _ else st.prv n) :=
    rfl
  have hse : st.suD c n = (if st.dd c _ = true then st.nxt _ else st.nxt n) :=
    rfl
  rw [← hpe] at hp
  rw [← hse] at hs
  have hps : st.prD c n ≠ st.suD c n := by
    zuchf
    zvmyr at hs
    have e1 := only_of_pred_eq_succ hnA by_simp_all hp hs hj₁ by_simp_all
    have e2 := only_of_pred_eq_succ hnA by_simp_all hp hs hj₂ by_simp_all
    simp_all
  obtain ⟨hin, hfree⟩ := gap_of_pred_succ hnA by_simp_all hp hs hps
  have hpA := hp.1
  have hsA := hs.1
  refine ⟨hpA, hsA, ⟨(h.cut_sdiff_iff hE hc _).2 ⟨_, hpA, hp.2.1.1, by simpa using hp.2.1.2, rfl⟩,
    (h.cut_sdiff_iff hE hc _).2 ⟨_, hsA, hs.2.1.1, by simpa using hs.2.1.2, rfl⟩,
    fun e => hps (key_inj hE hpA hsA e), fun k hk' hcut => ?_⟩,
    (key_cyc_iff hE hpA hsA hnA).2 hin⟩
  obtain ⟨j, hj, hjL, hjd, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hcut
  exact hfree j hj by_simp_all ((key_cyc_iff hE hpA hsA hj).1 hk')

/-- **The merged weight** computed by the state is the weight of the merged region. -/
theorem Inv.mu_eq (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {P : Set Point}
    (hs : Merge.IsSplit E.M.D ztfa ztbel P
      ztwnu ztwnt) :
    st.mu E c = E.M.weight ztfa P := by
  have hSadm := St.F_adm (st := st) hE
  have hSfin := St.F_finite (st := st) hE
  have hcS := St.cs_mem_F hc
  unfold St.mu
  zujso
  · zubel
    -- the only live chord is `c`
    have hL1 : st.L E = {c} := by
      zubkj
      zukrl
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
      simp_all
    have he : st.F E \ {cs E.M E.Q E.N c} = ∅ := by
      rw [← fam_diff hE hc, hL1, sdiff_self]
      zuiub
    rw [weight_merged_empty hE.hM hs he, size_eq hE]
  · zubmd
    have hne' : ztixo := by
      zubkj
      have h2 : 1 < (st.L E).ncard := by
        have := Set.ncard_pos hfin |>.2 ⟨c, hc⟩
        zukrl
        omega
      obtain ⟨a, ha, hac⟩ := Set.exists_ne_of_one_lt_ncard h2 c
      zujlz
      exact ⟨cs E.M E.Q E.N a, a, by_simp_all, ha.1, rfl⟩
    have wX : ztrhc :=
      (h.cls _ ztcjr).2.1
    have wY : ztrhc :=
      (h.cls _ ztcjs).2.1
    -- each joined gap
    have hjw : ∀ n, ztfti →
        st.jw E c n ≤ E.M.weight ztfa P := by
      intro n hn
      unfold St.jw
      split_ifs with hcnt
      · zudis
        rw [gw_eq hE h.stat hpA hsA]
        exact gap_le_merged hE.hM hSadm hSfin hcS hs ((h.lost_iff hE hc).2 by_grind)
          hgap hin
      omega
    refine le_antisymm ?_ ?_
    · refine max_le (max_le ?_ ?_) by_simp_all
      · rw [wX]; exact weight_le_merged₁ hE.hM hSadm hSfin hcS hs
      · rw [wY]; exact weight_le_merged₂ hE.hM hSadm hSfin hcS hs
    · refine weight_merged_le hE.hM hSadm hSfin hcS hs hne'
        by_omega
        by_omega ?_
      rintro l r hg ⟨k, hk, hkin⟩
      obtain ⟨n, hn, hcnt, rfl⟩ := (h.lost_iff hE hc).1 hk
      zudis
      obtain ⟨rfl, rfl⟩ := gap_unique hg hgap hkin hin
      have : E.M.arcWt ztiha ztihb = st.jw E c n := by
        unfold St.jw; rw [ite_eq_left hcnt, gw_eq hE h.stat hpA hsA]
      grind
namespace St
variable (E : Env) (st : St)

/-- The exit list of the merged class. -/
def newEx (c : ℕ) : List ℕ :=
  (st.exl zttb).filter ztuez ++ (st.exl ztsm).filter ztuez

/-- Unlink position `d` from the ring `(nxt, prv)`. -/
def unl (r : ztjx × ztjx) (d : ℕ) : ztjx × ztjx :=
  (Function.update r.1 ztwci ztwch, Function.update r.2 ztwch ztwci)

/-- The ring after unlinking the dying positions of `c`. -/
def ring2 (c : ℕ) : ztjx × ztjx :=
  let r1 := if st.cnt zteat = 1 then unl ztfur zteat else ztfur
  if st.cnt ztfir = 1 then unl r1 ztfir else r1

/-- **The removal of chord `c`**, the merged class getting the weight `μ`. -/
def remove (c μ : ℕ) : St where
  live := Function.update st.live c 0
  s0 := fun d => if d ∈ st.exl ztsm ∧ d ≠ c ∧ st.s0 d = st.s1 c then st.s0 c else st.s0 d
  s1 := fun d => if d ∈ st.exl ztsm ∧ d ≠ c ∧ st.s1 d = st.s1 c then st.s0 c else st.s1 d
  nd0 := st.nd0
  nd1 := st.nd1
  deg := Function.update st.deg zttb (st.newEx c).length
  wt := Function.update st.wt zttb μ
  ex := fun x t => if x = st.s0 c ∧ t < (st.newEx c).length then (st.newEx c).getD t 0
    else st.ex x t
  cnt := Function.update (Function.update st.cnt zteat (st.cnt zteat - 1)) ztfir
    (st.cnt ztfir - 1)
  nxt := (st.ring2 c).1
  prv := (st.ring2 c).2
  eg := st.eg
  pz := st.pz
  stk := fun t => if st.top - 1 ≤ t ∧ t < st.top - 1 + (st.newEx c).length then
    (st.newEx c).getD (t - zthkp) 0 else st.stk t
  top := st.top - 1 + (st.newEx c).length
  nlive := st.nlive - 1
end St
variable {E : Env} {st : St}

/-! ## Basic facts about the removal -/
section Removal
variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
include hE h hc
omit hE h hc in
theorem rm_L (_hE : E.Good) (_h : Inv E st) (hc : c ∈ st.L E)
    (μ : ℕ) : (st.remove c μ).L E = st.L E \ {c} := by
  ext i
  simp only [St.L, St.remove, mem_sdiff, mem_ofPred_eq, mem_singleton_iff]
  grind
theorem rm_F (μ : ℕ) : (st.remove c μ).F E = st.F E \ {cs E.M E.Q E.N c} := by
  unfold St.F
  rw [rm_L hE h hc]
  exact fam_diff hE hc
omit hE h hc in
/-- The exit lists of the two classes of `c`. -/
theorem exl_X (_hE : E.Good) (h : Inv E st)
    (hc : c ∈ st.L E) : ∀ i, i ∈ st.exl zttb ↔ i ∈ st.L E ∧
    TouchesIn E.M.D ztbbw ztwnu :=
  (h.cls _ ztcjr).2.2.2.1
omit hE h hc in
theorem exl_Y (_hE : E.Good) (h : Inv E st)
    (hc : c ∈ st.L E) : ∀ i, i ∈ st.exl ztsm ↔ i ∈ st.L E ∧
    TouchesIn E.M.D ztbbw ztwnt :=
  (h.cls _ ztcjs).2.2.2.1
end Removal

/-- The degree of a region counted by a duplicate-free list of record indices. -/
theorem deg_list (hE : E.Good) {L' : Set ℕ} (hL' : ∀ i ∈ L', i < E.K) {Z : Set Point}
    {l : List ℕ} (hnd : l.Nodup)
    (hl : ∀ i, i ∈ l ↔ i ∈ L' ∧ TouchesIn E.M.D ztbbw Z) :
    l.length = E.M.deg (fam E.M E.Q E.N L') Z := by
  zuhqm
  have e : {d | d ∈ fam E.M E.Q E.N L' ∧ TouchesIn E.M.D d Z} =
      ztmjr '' {i | i ∈ l} := by
    zufsm
    zuipp

    · rintro ⟨⟨i, hiL, hi, rfl⟩, ht⟩
      grind
    · zuin
      obtain ⟨hiL, ht⟩ := (hl i).1 hi
      exact ⟨⟨i, hiL, hL' i hiL, rfl⟩, ht⟩
  have hinj : Set.InjOn ztmjr {i | i ∈ l} := by
    intro i hi i' hi' he
    exact cs_inj hE.hNF (hL' i ((hl i).1 hi).1) (hL' i' ((hl i').1 hi').1) he
  zukqr
  rw [show {i | i ∈ l} = (l.toFinset : Set ℕ) by ext; simp]
  zuewx

/-- The exit list of a class is its list of exits. -/
theorem exl_of_list (st : St) (x : ℕ) {l : List ℕ} (hd : st.deg x = l.length)
    (he : ∀ t, t < l.length → st.ex x t = l.getD t 0) : st.exl x = l := by
  unfold St.exl
  simp_all
section Rm
variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {P : Set Point}
  (hs : Merge.IsSplit E.M.D ztfa ztbel P
    ztwnu ztwnt)
include hE h hc hs
omit hE h hc hs in
theorem hsys_F (hE : E.Good) (_h : Inv E st) (_hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D ztfa
    ztbel P ztwnu ztwnt) : ChordSystem E.M.D (st.F E) :=
  hE.hM.sys _ (St.F_adm (st := st) hE) (St.F_finite (st := st) hE)
variable {x : ℕ} {i : ℕ} {Z : Set Point}
theorem rm_cl_in (hx : x < E.R)
    (hxc : st.cl E x = st.cl E zttb ∨ st.cl E x = st.cl E ztsm) (μ : ℕ) :
    (st.remove c μ).cl E x = P := by
  show supR E.M ztgwi ztpxo = P
  zujli
  refine supR_eq ztzbn hs.mem ?_
  refine (St.cl_spec (st := st) hE hx).2.trans ?_
  rcases hxc with e | e <;> zvmwe
  · exact hs.sub₁
  · exact hs.sub₂
omit hE h hc hs in
theorem cl_out (hE : E.Good) (_h : Inv E st) (hc : c ∈ st.L E)
    (hs : Merge.IsSplit E.M.D ztfa ztbel P ztwnu
    ztwnt) {x : ℕ} (hx : x < E.R) (h1 : st.cl E x ≠ st.cl E (st.s0 c))
    (h2 : st.cl E x ≠ st.cl E ztsm) :
    st.cl E x ∈ E.M.regions ztfa ∧ st.cl E x ≠ P := by
  rcases split_cases ztccm hs (St.cl_spec (st := st) hE hx).1 with e | e | e
  · simp_all
  · simp_all
  omega
theorem rm_cl_out (hx : x < E.R) (h1 : st.cl E x ≠ st.cl E zttb)
    (h2 : st.cl E x ≠ st.cl E ztsm) (μ : ℕ) : (st.remove c μ).cl E x = st.cl E x := by
  show supR E.M ztgwi ztpxo = st.cl E x
  zujli
  exact supR_eq ztzbn
    (cl_out hE h hc hs hx h1 h2).1 (St.cl_spec (st := st) hE hx).2

/-- A chord other than `c` touches the merged region iff it touches one of the two classes. -/
theorem touch_P (hi : i ∈ st.L E) (hic : i ≠ c) :
    TouchesIn E.M.D ztbbw P ↔ TouchesIn E.M.D ztbbw ztwnu ∨
      TouchesIn E.M.D ztbbw ztwnt := by
  have e := hs.exits_eq_union ztjye sdiff_subset ztccm
    not_mem_sdiff_self (W := st.F E \ {cs E.M E.Q E.N c}) subset_rfl
  have hiS : zthop := by
    zugxp
  constructor
  · zuibv
    have : ztygp := ⟨hiS, ht⟩
    zudtu
    rcases this with ⟨-, h'⟩ | ⟨-, h'⟩
    · simp_all
    simp_all
  · zuibv
    have : ztygp := by
      zui
      tauto
    exact this.2

/-- No chord other than `c` touches both classes. -/
theorem not_both (hi : i ∈ st.L E) (hic : i ≠ c)
    (h1 : TouchesIn E.M.D ztbbw ztwnu)
    (h2 : TouchesIn E.M.D ztbbw ztwnt) : False := by
  have hd := hs.exits_disjoint ztjye sdiff_subset ztccm
    (W := st.F E \ {cs E.M E.Q E.N c}) subset_rfl
  have hiS : zthop := by
    zugxp
  exact Set.disjoint_left.1 hd ⟨hiS, h1⟩ ⟨hiS, h2⟩
theorem mem_newEx (i : ℕ) :
    i ∈ st.newEx c ↔ i ∈ st.L E ∧ i ≠ c ∧ TouchesIn E.M.D ztbbw P := by
  unfold St.newEx
  simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq]
  rw [exl_X hE h hc, exl_Y hE h hc]
  constructor
  · rintro (⟨⟨hi, ht⟩, hic⟩ | ⟨⟨hi, ht⟩, hic⟩)
    · exact ⟨hi, hic, (touch_P hE h hc hs hi hic).2 (Or.inl ht)⟩
    · exact ⟨hi, hic, (touch_P hE h hc hs hi hic).2 (Or.inr ht)⟩
  · rintro ⟨hi, hic, ht⟩
    rcases (touch_P hE h hc hs hi hic).1 ht with h' | h'
    · simp_all
    simp_all
theorem newEx_nodup : (st.newEx c).Nodup := by
  unfold St.newEx
  rw [List.nodup_append]
  refine ⟨((h.cls _ ztcjr).2.2.1).filter _,
    ((h.cls _ ztcjs).2.2.1).filter _, fun a ha b hb hab => ?_⟩
  zumqb
  rw [List.mem_filter, exl_X hE h hc] at ha
  rw [List.mem_filter, exl_Y hE h hc] at hb
  exact not_both hE h hc hs ha.1.1 by_simp_all ha.1.2 hb.1.2
omit hE h hc hs in
theorem newEx_length (hE : E.Good) (h : Inv E st) (hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D ztfa
    ztbel P ztwnu ztwnt) :
    (st.newEx c).length + 2 = st.deg zttb + st.deg ztsm := by
  zueid
  zugph
  have hcX : c ∈ st.exl zttb := (exl_X hE h hc c).2 ⟨hc, (htouch _ hX).2 ztp⟩
  have hcY : c ∈ st.exl ztsm := (exl_Y hE h hc c).2 ⟨hc, (htouch _ hY).2 ztbt⟩
  have nX := (h.cls _ ztcjr).2.2.1
  have nY := (h.cls _ ztcjs).2.2.1
  unfold St.newEx
  rw [List.length_append, ← nX.erase_eq_filter, ← nY.erase_eq_filter,
    List.length_erase_of_mem hcX, List.length_erase_of_mem hcY]
  have l1 := List.length_pos_of_mem hcX
  have l2 := List.length_pos_of_mem hcY
  unfold St.exl at l1 l2 ⊢
  grind
theorem deg_P :
    E.M.deg ztfa P = (st.newEx c).length := by
  zujlz
  refine (deg_list hE (fun i hi => hi.1.1) (newEx_nodup hE h hc hs) fun i => ?_).symm
  zuedq
  grind
theorem other_ne (hZ : Z ∈ E.M.regions ztfa)
    (hZP : Z ≠ P) : Z ∈ E.M.regions ztbhy ∧ Z ≠ st.cl E zttb ∧ Z ≠ st.cl E ztsm := by
  refine ⟨split_old ztccm hs hZ hZP, fun e => hZP ?_, fun e => hZP ?_⟩
  · have hX := (h.cl_mem hE hc).1
    exact Chazelle.Chain.regionsIn_eq_of_subset hZ hs.mem
      ztuxm ztdlt hs.sub₁
  · have hY := (h.cl_mem hE hc).2
    exact Chazelle.Chain.regionsIn_eq_of_subset hZ hs.mem
      (Chazelle.Chain.regionsIn_nonempty hY) ztdlt hs.sub₂
theorem deg_other (hZ : Z ∈ E.M.regions ztfa)
    (hZP : Z ≠ P) :
    E.M.deg ztfa Z = E.M.deg ztbhy Z := by
  have e := hs.exits_other ztjye sdiff_subset hZ hZP
  rw [Merge.insert_sdiff_self ztccm] at e
  show (Merge.exitsIn E.M.D _ Z).ncard = (Merge.exitsIn E.M.D _ Z).ncard
  zui
theorem weight_other' (hZ : Z ∈ E.M.regions ztfa)
    (hZP : Z ≠ P) :
    E.M.weight ztfa Z = E.M.weight ztbhy Z := by
  obtain ⟨hZS, h1, h2⟩ := other_ne hE h hc hs hZ hZP
  exact weight_other hE.hM (St.F_adm (st := st) hE) (St.F_finite (st := st) hE) ztccm
    hs hZS h1 h2
end Rm
variable {Lv : ℕ → Prop} {A : ℕ}
/-- A position whose predecessor and successor coincide sees only that other live position. -/
theorem only_live {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv) {d : ℕ}
    (hd : d < A) (hdL : Lv d) (he : prv d = nxt d) {i : ℕ} (hi : i < A) (hiL : Lv i)
    (hid : i ≠ d) : i = prv d := by
  have hp := h.pred hd hdL
  have hs := h.succ hd hdL
  zvndl at hs
  by_contra hip
  rcases cyc_cover ztqtu ztvzk with h1 | h1 | h1
  · zujuw
  · simp_all
  · zujuz

/-- Unlinking a live position when two other live positions remain. -/
theorem ringOK_unl {r : ztjx × ztjx} (h : RingOK Lv A r.1 r.2)
    {d : ℕ} (hd : d < A) (hdL : Lv d)
    (h2 : ∃ a b, a < A ∧ b < A ∧ Lv a ∧ Lv b ∧ a ≠ d ∧ b ≠ d ∧ a ≠ b) :
    RingOK ztdnz A (St.unl r d).1 (St.unl r d).2 := by
  have hne : r.2 d ≠ r.1 d := by
    zufhz
    obtain ⟨a, b, ha, hb, haL, hbL, had, hbd, hab⟩ := h2
    exact hab ((only_live h hd hdL he ha haL had).trans
      (only_live h hd hdL he hb hbL hbd).symm)
  exact ringOK_unlink h hd hdL hne
section Rm3
variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {P : Set Point}
  (hs : Merge.IsSplit E.M.D ztfa ztbel P
    ztwnu ztwnt)
include hE h hc hs
omit hE h hc hs in
/-- The relabelling of the first side. -/
theorem rm_s0 (hE : E.Good) (h : Inv E st) (hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D ztfa
    ztbel P ztwnu ztwnt) {i : ℕ} (hi : i ∈ st.L E)
    (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).s0 i = if st.s0 i = st.s1 c then st.s0 c else st.s0 i := by
  show (if i ∈ st.exl _ ∧ i ≠ c ∧ st.s0 i = st.s1 c then st.s0 c else st.s0 i) = _
  by_cases e : st.s0 i = st.s1 c
  · have hmem : ztbada := by
      zuebx

      exact ((h.sides i hi).2.2.2 _ (St.cl_spec hE (h.sides i hi).1).1).2 ztp
    simp_all
  simp_all
omit hE h hc hs in
/-- The relabelling of the second side. -/
theorem rm_s1 (hE : E.Good) (h : Inv E st) (hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D ztfa
    ztbel P ztwnu ztwnt) {i : ℕ} (hi : i ∈ st.L E)
    (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).s1 i = if st.s1 i = st.s1 c then st.s0 c else st.s1 i := by
  show (if i ∈ st.exl _ ∧ i ≠ c ∧ st.s1 i = st.s1 c then st.s0 c else st.s1 i) = _
  by_cases e : st.s1 i = st.s1 c
  · have hmem : ztbada := by
      zuebx

      exact ((h.sides i hi).2.2.2 _ (St.cl_spec hE (h.sides i hi).2.1).1).2
        ztbt
    simp_all
  simp_all
variable {x : ℕ} {i : ℕ}
/-- The class after the removal of an old class. -/
theorem rm_cl_g (hx : x < E.R) (μ : ℕ) :
    (st.remove c μ).cl E x = if st.cl E x = st.cl E zttb ∨ st.cl E x = st.cl E ztsm
      then P else st.cl E x := by
  split_ifs with hxc
  · exact rm_cl_in hE h hc hs hx hxc μ
  · push Not at hxc
    exact rm_cl_out hE h hc hs hx hxc.1 hxc.2 μ

/-- The class of a relabelled side is the class of the old side. -/
theorem rm_cl_s0 (hi : i ∈ st.L E) (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).cl E ztgwj = (st.remove c μ).cl E ztibc := by
  zunsr
  split_ifs with e
  · rw [e, rm_cl_in hE h hc hs (h.sides c hc).1 ztp,
      rm_cl_in hE h hc hs (h.sides c hc).2.1 ztbt]
  · rfl
theorem rm_cl_s1 (hi : i ∈ st.L E) (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).cl E ztgwk = (st.remove c μ).cl E ztqwy := by
  zunss
  split_ifs with e
  · rw [e, rm_cl_in hE h hc hs (h.sides c hc).1 ztp,
      rm_cl_in hE h hc hs (h.sides c hc).2.1 ztbt]
  · rfl
omit hE h hc hs in
/-- The merged region is not an old region. -/
theorem g_eq_P_iff (_hE : E.Good) (_h : Inv E st) (hc : c ∈ st.L E)
    (hs : Merge.IsSplit E.M.D ztfa ztbel P ztwnu
    ztwnt) {W : Set Point} (hW : W ∈ E.M.regions (st.F E)) :
    (if W = st.cl E zttb ∨ W = st.cl E ztsm then P else W) = P ↔
      W = st.cl E zttb ∨ W = st.cl E ztsm := by
  split_ifs with hw
  · simp_all
  · zumiw
    rcases split_cases ztccm hs hW with e | e | ⟨-, e⟩
    · simp_all
    · simp_all
    simp_all

/-- **The sides after the removal.** -/
theorem sides_rm (hi : i ∈ st.L E) (hic : i ≠ c) (μ : ℕ) :
    (st.remove c μ).s0 i < E.R ∧ (st.remove c μ).s1 i < E.R ∧
      (st.remove c μ).cl E ztgwj ≠ (st.remove c μ).cl E ztgwk ∧
      ∀ Z ∈ E.M.regions ztgwi, (TouchesIn E.M.D ztbbw Z ↔
        Z = (st.remove c μ).cl E ztgwj ∨
          Z = (st.remove c μ).cl E ztgwk) := by
  obtain ⟨hs0, hs1, hne, htouch⟩ := h.sides i hi
  obtain ⟨hc0, hc1, -, htc⟩ := h.sides c hc
  have hW0 := (St.cl_spec (st := st) hE hs0).1
  have hW1 := (St.cl_spec (st := st) hE hs1).1
  rw [rm_cl_s0 hE h hc hs hi hic, rm_cl_s1 hE h hc hs hi hic, rm_cl_g hE h hc hs hs0,
    rm_cl_g hE h hc hs hs1, rm_F hE h hc]
  refine ⟨by zunsr; grind,
    by zunss; grind, ?_, fun Z hZ => ?_⟩
  · zufhz
    by_cases hP : (if st.cl E ztibc = st.cl E zttb ∨ st.cl E ztibc = st.cl E ztsm
        then P else st.cl E ztibc) = P
    · have e0 := (g_eq_P_iff hE h hc hs hW0).1 hP
      have e1 := (g_eq_P_iff hE h hc hs hW1).1 by_simp_all
      -- `i` touches both classes of `c`
      have t0 : ztuml :=
        (htouch _ hW0).2 ztp
      have t1 : ztuml :=
        (htouch _ hW1).2 ztbt
      rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1
      · simp_all
      · zvokq at t0; zvmxy at t1; exact not_both hE h hc hs hi hic t0 t1
      · zvokq at t0; zvmxy at t1; exact not_both hE h hc hs hi hic t1 t0
      simp_all
    grind
  · zufqw
    · subst hZP
      rw [touch_P hE h hc hs hi hic, htouch _ (h.cl_mem hE hc).1, htouch _ (h.cl_mem hE hc).2,
        eq_comm (a := Z), eq_comm (a := Z), g_eq_P_iff hE h hc hs hW0, g_eq_P_iff hE h hc hs hW1]
      tauto
    · obtain ⟨hZS, hZ0, hZ1⟩ := other_ne hE h hc hs hZ hZP
      grind

/-- **The referenced classes after the removal**: the merged class `s0 c`, or an old class not
touched by `c`. -/
theorem ref_cases (μ : ℕ) (hx : (st.remove c μ).Ref E x) :
    x = st.s0 c ∨ (st.Ref E x ∧ x < E.R ∧ st.cl E x ≠ st.cl E zttb ∧
      st.cl E x ≠ st.cl E ztsm) := by
  obtain ⟨i, hi, hx⟩ := hx
  rw [rm_L hE h hc] at hi
  zugmk

  have hX : st.Ref E _ := ztcjr
  have hY : st.Ref E _ := ztcjs
  have key : ∀ w, st.Ref E w → w < E.R → x = w → w ≠ st.s1 c →
      x = st.s0 c ∨ (st.Ref E x ∧ x < E.R ∧ st.cl E x ≠ st.cl E zttb ∧
        st.cl E x ≠ st.cl E ztsm) := by
    intro w hw hwR hxw hwY
    subst hxw
    by_cases hwX : x = st.s0 c
    · omega
    · exact Or.inr ⟨hw, hwR, fun e => hwX (h.refInj _ _ hw hX e),
        fun e => hwY (h.refInj _ _ hw hY e)⟩
  zuky
  · rw [rm_s0 hE h hc hs hiL hic] at hx
    zulsq
    · omega
    · exact key _ ⟨i, hiL, Or.inl rfl⟩ (h.sides i hiL).1 hx e
  · rw [rm_s1 hE h hc hs hiL hic] at hx
    zulsq
    · omega
    · exact key _ ⟨i, hiL, Or.inr rfl⟩ (h.sides i hiL).2.1 hx e

/-- The new exit list has at most `D` entries. -/
theorem newEx_le (hlow : st.deg zttb < 3 ∨ st.deg ztsm < 3) :
    (st.newEx c).length ≤ E.D := by
  have l := newEx_length hE h hc hs
  have dX := (h.cls _ ztcjr).2.2.2.2
  have dY := (h.cls _ ztcjs).2.2.2.2
  omega

/-- **The class data after the removal.** -/
theorem cls_rm (hlow : st.deg zttb < 3 ∨ st.deg ztsm < 3) {x : ℕ}
    (hx : (st.remove c ztcfi).Ref E x) :
    (st.remove c ztcfi).deg x =
        E.M.deg ztynv ztxfs ∧
      (st.remove c ztcfi).wt x =
        E.M.weight ztynv ztxfs ∧
      ((st.remove c ztcfi).exl x).Nodup ∧
      (∀ i, i ∈ (st.remove c ztcfi).exl x ↔ i ∈ (st.remove c ztcfi).L E ∧
        TouchesIn E.M.D ztbbw ztxfs) ∧
      (st.remove c ztcfi).deg x ≤ E.D := by
  zulac
  rw [rm_F hE h hc, rm_L hE h hc]
  rcases ref_cases hE h hc hs μ hx with rfl | ⟨hxR, hxlt, h1, h2⟩
  · have hcl : ztlwz :=
      rm_cl_in hE h hc hs (h.sides c hc).1 ztp μ
    have hdeg : (st.remove c μ).deg zttb = (st.newEx c).length := by
      show Function.update st.deg _ _ _ = _
      simp
    have hexl : (st.remove c μ).exl zttb = st.newEx c := by
      refine exl_of_list _ _ hdeg fun t ht => ?_
      show (if st.s0 c = st.s0 c ∧ t < (st.newEx c).length then (st.newEx c).getD t 0
        else st.ex _ t) = _
      simp_all
    zuijm
    refine ⟨(deg_P hE h hc hs).symm, ?_, newEx_nodup hE h hc hs, fun i => ?_,
      newEx_le hE h hc hs hlow⟩
    · show Function.update st.wt _ μ _ = _
      zuewo
      exact h.mu_eq hE hc hs
    · zuedq
      grind
  · have hxX : x ≠ st.s0 c := by_grind
    obtain ⟨hcx, hxP⟩ := cl_out hE h hc hs hxlt h1 h2
    have hcl := rm_cl_out hE h hc hs hxlt h1 h2 μ
    have hdeg : (st.remove c μ).deg x = st.deg x := by
      show Function.update st.deg _ _ x = _
      simp_all
    have hexl : (st.remove c μ).exl x = st.exl x := by
      unfold St.exl
      rw [hdeg]
      zucr
      funext t
      show (if x = st.s0 c ∧ (t : ℕ) < (st.newEx c).length then (st.newEx c).getD t 0
        else st.ex x t) = _
      simp_all
    obtain ⟨d1, w1, n1, m1, l1⟩ := h.cls x hxR
    zuijm
    refine ⟨by rw [deg_other hE h hc hs hcx hxP]; exact d1, ?_, n1, fun i => ?_, l1⟩
    · show Function.update st.wt _ μ x = _
      rw [Function.update_of_ne hxX, weight_other' hE h hc hs hcx hxP]
      exact w1
    · zumoo
      simp only [mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hi, ht⟩
        refine ⟨⟨hi, fun e => ?_⟩, ht⟩
        zugig
        have := (split_touches_iff hE.hM ztgeu ztjmy
          ztccm hs (St.cl_spec hE hxlt).1).1 ht
        simp_all
      simp_all

/-- **Referenced classes stay distinct.** -/
theorem refInj_rm {x y : ℕ} (μ : ℕ) (hx : (st.remove c μ).Ref E x)
    (hy : (st.remove c μ).Ref E y)
    (he : (st.remove c μ).cl E x = (st.remove c μ).cl E y) : x = y := by
  have hP : ztlwz :=
    rm_cl_in hE h hc hs (h.sides c hc).1 ztp μ
  rcases ref_cases hE h hc hs μ hx with rfl | ⟨hxR, hxlt, h1, h2⟩ <;>
    rcases ref_cases hE h hc hs μ hy with rfl | ⟨hyR, hylt, h1', h2'⟩
  · rfl
  · rw [hP, rm_cl_out hE h hc hs hylt h1' h2'] at he
    exact absurd he.symm (cl_out hE h hc hs hylt h1' h2').2
  · rw [hP, rm_cl_out hE h hc hs hxlt h1 h2] at he
    exact absurd he (cl_out hE h hc hs hxlt h1 h2).2
  · rw [rm_cl_out hE h hc hs hxlt h1 h2, rm_cl_out hE h hc hs hylt h1' h2'] at he
    exact h.refInj _ _ hxR hyR he
end Rm3
section Rm4
variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
include hE h hc
variable (μ : ℕ) {j : ℕ}
/-- **The counts after the removal.** -/
theorem cnt_rm (hj : j < E.A) :
    (st.remove c μ).cnt j = (st.remove c μ).cntOf E j := by
  zucmk
  have hcK := hc.1
  have k0 : ((Finset.range E.K).filter fun i => (st.remove c μ).live i = 1 ∧
      (st.remove c μ).nd0 i = j) =
      ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).erase c := by
    zufsn

    show (_ ∧ Function.update st.live c 0 i = 1 ∧ st.nd0 i = j) ↔ _
    grind
  have k1 : ((Finset.range E.K).filter fun i => (st.remove c μ).live i = 1 ∧
      (st.remove c μ).nd1 i = j) =
      ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).erase c := by
    zufsn

    show (_ ∧ Function.update st.live c 0 i = 1 ∧ st.nd1 i = j) ↔ _
    grind
  zultw
  zukwr
  show Function.update ztrjk _
      _ j = _
  have e := h.cnt j hj
  unfold St.cntOf at e
  have m0 : c ∈ ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j) ↔
      st.nd0 c = j := by zuolf
  have m1 : c ∈ ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j) ↔
      st.nd1 c = j := by zuolf
  zuirg
  · zucuj
    rw [Function.update_self, Finset.card_erase_of_mem (m1.2 rfl),
      Finset.erase_eq_of_notMem by_simp_all, h.cnt _ hj]
    zultw
    grind
  · zufml

    · zubvi
      rw [Function.update_self, Finset.card_erase_of_mem (m0.2 rfl),
        Finset.erase_eq_of_notMem by_grind, h.cnt _ hj]
      zultw
      grind
    · rw [Function.update_of_ne h0, Finset.erase_eq_of_notMem by_grind,
        Finset.erase_eq_of_notMem by_grind, e]

/-- The live positions after the removal. -/
theorem lv_rm (hj : j < E.A) :
    (st.remove c μ).Lv j ↔ st.Lv j ∧ st.dd c j = false := by
  zucmk
  unfold St.Lv
  show 0 < Function.update ztrjk
      _ _ j ↔ _
  zuirg
  · zucuj
    zuewo
    have hL := (h.key_nd_cut hE hc ztbt).2.1
    have hd := h.dd_iff hE hc ztbt
    grind
  · zufml

    · zubvi
      zuewo
      have hL := (h.key_nd_cut hE hc ztp).2.1
      have hd := h.dd_iff hE hc ztp
      grind
    · rw [Function.update_of_ne h0]
      constructor
      · zulmw
        refine ztuhs
        zuhbu

        obtain ⟨hj', -⟩ := h.dd_cases hE hc hdd
        omega
      omega

/-- **The ring after the removal.** -/
theorem ring_rm :
    RingOK (st.remove c μ).Lv E.A (st.remove c μ).nxt (st.remove c μ).prv := by
  zucmk
  have hl := fun {j : ℕ} (hj : j < E.A) => lv_rm hE h hc μ hj
  by_cases hemp : ∀ j, j < E.A → ¬ (st.remove c μ).Lv j
  · exact ringOK_empty hemp _ _
  push Not at hemp
  obtain ⟨j₀, hj₀, hL₀⟩ := hemp
  -- two distinct surviving positions
  obtain ⟨hL₀', hd₀⟩ := (hl hj₀).1 hL₀
  have hcut₀ := (h.cut_sdiff_iff hE hc _).2 ⟨j₀, hj₀, hL₀', hd₀, rfl⟩
  have hne' : ztixo := by
    obtain ⟨d, hd, -⟩ := hcut₀
    tauto
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hE.hM.two_cuts
    (sdiff_subset.trans (St.F_adm (st := st) hE)) hne'
  obtain ⟨a, ha, haL, had, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₁
  obtain ⟨b, hb, hbL, hbd, rfl⟩ := (h.cut_sdiff_iff hE hc _).1 hk₂
  have hab : a ≠ b := by_grind
  have hn1 := h.key_nd_cut hE hc ztp
  have hn2 := h.key_nd_cut hE hc ztbt
  -- positions that die are not `a`, `b`
  have hdead : ∀ n, st.dd c n = true → a ≠ n ∧ b ≠ n := by_grind
  -- the first unlink
  set Lv1 : ℕ → Prop := fun j => st.Lv j ∧ (st.cnt zteat = 1 → j ≠ st.nd0 c)
  set r1 := if st.cnt zteat = 1 then St.unl ztfur zteat
    else ztfur
  have hR1 : RingOK Lv1 E.A r1.1 r1.2 := by
    by_cases d1 : st.cnt zteat = 1
    · have hd1 : ztsmk := (h.dd_iff hE hc ztp).2 d1
      have e1 : r1 = St.unl ztfur _ := ite_eq_left d1
      zukd
      refine (ringOK_unl h.ring hn1.1 hn1.2.1
        ⟨a, b, ha, hb, haL, hbL, by_simp_all, by_simp_all, hab⟩).congr
        ztchx by_omega ztczj
      grind
    · have e1 : r1 = ztfur := ite_eq_right d1
      zukd
      exact h.ring.congr by_grind by_simp_all by_simp_all
  -- the second unlink
  have hring2 : (st.ring2 c) = if st.cnt _ = 1 then St.unl r1 _ else r1 := rfl
  have hLv1a : Lv1 a := ⟨haL, fun d1 e => (hdead _ ztyhb).1 e⟩
  have hLv1b : Lv1 b := ⟨hbL, fun d1 e => (hdead _ ztyhb).2 e⟩
  have hfin : RingOK (fun j => Lv1 j ∧ (st.cnt ztfir = 1 → j ≠ st.nd1 c)) E.A
      (st.ring2 c).1 (st.ring2 c).2 := by
    rw [hring2]
    by_cases d2 : st.cnt ztfir = 1
    · have hd2 : ztsmk := (h.dd_iff hE hc ztbt).2 d2
      rw [ite_eq_left d2]
      have hn2L : Lv1 _ := ⟨hn2.2.1, by_omega⟩
      refine (ringOK_unl hR1 hn2.1 hn2L
        ⟨a, b, ha, hb, hLv1a, hLv1b, by_simp_all, by_simp_all, hab⟩).congr
        ztchx by_omega by_omega
      simp_all
    simp_all
  refine hfin.congr ztjvz ztczj ztczj
  rw [hl hj]
  simp only [Lv1]
  constructor
  · rintro ⟨hL, hdd⟩
    refine ⟨⟨hL, fun d1 e => ?_⟩, fun d2 e => ?_⟩
    · rw [e, (h.dd_iff hE hc ztp).2 d1] at hdd; simp_all
    · rw [e, (h.dd_iff hE hc ztbt).2 d2] at hdd; simp_all
  · rintro ⟨⟨hL, h1⟩, h2⟩
    refine ⟨hL, ?_⟩
    zuhbu

    obtain ⟨hj', hcnt⟩ := h.dd_cases hE hc hdd
    grind
end Rm4

/-- **The removal preserves the invariant.** -/
theorem Inv.remove (hE : E.Good) (h : Inv E st) (htop : 0 < st.top)
    (hc : st.cur ∈ st.L E)
    (hrem : Merge.Removable E.M.D E.M.weight E.γ ztbhy ztjsx) :
    Inv E (st.remove st.cur ztoil) := by
  set c := st.cur with hcdef
  obtain ⟨P, hs⟩ := h.split hE hc
  obtain ⟨hlow, hw⟩ := (h.removable_iff hE hc hs).1 hrem
  have hmu : st.mu E c ≤ E.γ := by rw [h.mu_eq hE hc hs]; exact hw
  zulac
  set st' := st.remove c μ
  have hL' := rm_L hE h hc μ
  have hF' := rm_F hE h hc μ
  zudyz
  have hnl : ztsab := by
    zuoyg; exact (Set.ncard_pos hfinL).2 ztzx
  zuhfg
  refine ⟨h.stat.congr rfl rfl rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- live bits
    zug
    show Function.update st.live c 0 i ≤ 1
    zujtk
    · simp_all
    · rw [Function.update_of_ne hic]; exact h.live01 i hi
  · -- the number of live chords
    show st.nlive - 1 = (st'.L E).ncard
    rw [hL', ncard_sdiff_singleton_of_mem hc, h.nlive]
  · -- degrees
    zudtz
    intro Z hZ
    zufqw
    · subst hZP; rw [deg_P hE h hc hs]; omega
    · rw [deg_other hE h hc hs hZ hZP]
      exact h.degLe Z (other_ne hE h hc hs hZ hZP).1
  · -- weights
    zudtz
    intro Z hZ
    zufqw
    · simp_all
    · rw [weight_other' hE h hc hs hZ hZP]
      exact h.semi Z (other_ne hE h hc hs hZ hZP).1
  · -- sides
    zug
    zuksw
    exact sides_rm hE h hc hs hi.1 by_simp_all μ
  · -- classes
    zuh
    exact cls_rm hE h hc hs hlow hx
  · -- distinct classes
    intro x y hx hy he
    exact refInj_rm hE h hc hs μ hx hy he
  · -- counts
    zun
    exact cnt_rm hE h hc μ hj
  · -- ring
    exact ring_rm hE h hc μ
  · -- worklist entries
    zucj
    show (if st.top - 1 ≤ t ∧ t < st.top - 1 + (st.newEx c).length then
      (st.newEx c).getD _ 0 else st.stk t) < E.K
    change t < st.top - 1 + (st.newEx c).length at ht
    zudlu
    · have hk : t - zthkp < (st.newEx c).length := by_omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact ((mem_newEx hE h hc hs _).1 (List.getElem_mem hk)).1.1
    · exact h.stk t by_omega
  · -- the worklist bound
    show st.top - 1 + (st.newEx c).length + E.D * ztkfl ≤ E.K + E.D * E.K
    have := h.topLe
    have e : E.D * st.nlive = E.D * ztkfl + E.D := by
      zujlx
    omega
  · -- the worklist property
    zumgw
    zuksw
    zugmk

    -- `i` is not a new exit
    have hnotnew : i ∉ st.newEx c := by
      zujbb
      obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hm
      refine hno (st.top - 1 + k) zthfe ?_
      show (if st.top - 1 ≤ st.top - 1 + k ∧ st.top - 1 + k < st.top - 1 + (st.newEx c).length
        then (st.newEx c).getD _ 0 else st.stk _) = i
      grind
    -- `i` was not on the old worklist
    have hold : ∀ t, t < st.top → st.stk t ≠ i := by
      zucj
      zuhtj
      · zumqf
      · have := hno t zthfe
        show st.stk t ≠ i
        zuchf
        zulvx
        show (if st.top - 1 ≤ t ∧ t < st.top - 1 + (st.newEx c).length then _ else st.stk t) = i
        grind
    have hnr := h.work i hiL hold
    zudtz
    zuibu
    apply hnr
    have hsys := hsys_F hE h hc hs
    refine Merge.removable_of_removable_sdiff hsys
      (weightLocal hE.hM ztgeu ztjmy) subset_rfl
      ztccm by_grind (fun Z hZ hcZ hiZ => ?_) hr
    have hZ12 := (split_touches_iff hE.hM ztgeu ztjmy
      ztccm hs hZ).1 hcZ
    apply hnotnew
    zuedq
    refine ⟨hiL, hic, (touch_P hE h hc hs hiL hic).2 ?_⟩
    grind
namespace St
variable (E : Env) (st : St)

/-- **One iteration of the worklist.** -/
def step : St :=
  if st.live st.cur = 1 then
    if 3 ≤ st.deg ztgmf ∧ 3 ≤ st.deg ztgmg then st.pop
    else if E.γ < st.mu E st.cur then st.pop
    else st.remove st.cur ztoil
  else st.pop

/-- The measure of the worklist loop. -/
def meas : ℕ := st.top + zteml * st.nlive
end St
variable {E : Env} {st : St}

/-- **One iteration preserves the invariant.** -/
theorem Inv.step (hE : E.Good) (h : Inv E st) (htop : 0 < st.top) : Inv E ztmoo := by
  unfold St.step
  zulst
  · -- both classes have degree `≥ 3`: not removable
    zujez
    zuqg

    obtain ⟨hlow, -⟩ := (h.removable_iff hE hc hs).1 hr
    omega
  · -- the merged weight exceeds `γ`: not removable
    zujez
    zuqg

    obtain ⟨-, hw⟩ := (h.removable_iff hE hc hs).1 hr
    rw [← h.mu_eq hE hc hs] at hw
    omega
  · -- removable
    zuqg

    refine h.remove hE htop hc ((h.removable_iff hE hc hs).2 ztcp)
    · omega
    · rw [← h.mu_eq hE hc hs]; omega
  · exact h.pop_dead htop hl

/-- **The measure drops by at least one per iteration.** -/
theorem measure_step (hE : E.Good) (h : Inv E st) (htop : 0 < st.top) :
    (st.step E).meas E < st.meas E := by
  unfold St.step St.meas
  zulst
  · zujqf
  · zujqf
  · zuqg

    have hlow : ztylx := by
      omega
    zuhfg
    zudyz
    have hnl : ztsab := by
      zuoyg; exact (Set.ncard_pos hfinL).2 ⟨_, hc⟩
    show st.top - 1 + (st.newEx st.cur).length + zteml * ztkfl <
      st.top + zteml * st.nlive
    have e : zteml * st.nlive = zteml * ztkfl + zteml := by
      zujlx
    omega
  · zujqf

/-! ## The initial state -/

/-- The number of chords among the first `K` whose position map sends them to `j`. -/
def cntInit (K : ℕ) (nd0 nd1 : ℕ → ℕ) (j : ℕ) : ℕ :=
  ((Finset.range K).filter fun i => nd0 i = j).card +
    ((Finset.range K).filter fun i => nd1 i = j).card

/-- **The initial state** of the worklist (static arrays given). -/
def initSt (E : Env) (nd0 nd1 eg pz : ℕ → ℕ) : St where
  live := fun _ => 1
  s0 := fun i => (E.N.chord i).up
  s1 := fun i => (E.N.chord i).dn
  nd0 := nd0
  nd1 := nd1
  deg := fun r => (E.N.region r).chords.length
  wt := fun r => (E.N.region r).wt
  ex := fun r t => (E.N.region r).chords.getD t 0
  cnt := cntInit E.K nd0 nd1
  nxt := fun j => if j + 1 < E.A then j + 1 else 0
  prv := fun j => if 0 < j then j - 1 else E.A - 1
  eg := eg
  pz := pz
  stk := fun t => t
  top := E.K
  nlive := E.K

/-- **The initial state satisfies the invariant**, if the input submap is γ-semigranular with
degrees `≤ D` and the static data are correct. -/
theorem Inv.init (hE : E.Good) {nd0 nd1 eg pz : ℕ → ℕ}
    (hstat : StatOK E ztpck)
    (hdeg : E.M.DegLe ztjif E.D) (hsemi : E.M.Semigranular ztjif E.γ) :
    Inv E ztpck := by
  set st := initSt E nd0 nd1 eg pz
  have hL : st.L E = {i | i < E.K} := by
    ext i; simp [St.L, st, initSt]
  have hF : st.F E = E.N.F E.M E.Q := by
    unfold St.F; rw [hL, ← fam_univ]
    zuiub
  have hcl : ∀ x, x < E.R → st.cl E x = E.reg x := by
    zuh
    unfold St.cl
    zuguo
    exact supR_eq ztzbn zthhp le_rfl
  have hside := fun {i} (hi : i < E.K) => touch_iff_side hE.hNF hE.hM hE.hRC hE.hCS hi
  have hupdn : ∀ i, i < E.K → (E.N.chord i).up < E.R ∧ (E.N.chord i).dn < E.R :=
    fun i hi => ⟨(hE.hCS i hi).1, (hE.hCS i hi).2.1⟩
  -- a referenced class is a region index
  have href : ∀ x, st.Ref E x → x < E.R := by
    rintro x ⟨i, hi, rfl | rfl⟩
    · exact (hupdn i hi.1).1
    · exact (hupdn i hi.1).2
  have hK1 : 1 ≤ E.K := by
    obtain ⟨d, hd⟩ := hE.hne
    obtain ⟨i, hi, -⟩ := mem_F_iff.1 hd
    grind
  refine ⟨hstat, fun _ _ => le_rfl, ?_, by_simp_all, by_simp_all,
    fun i hi => ?_, fun x hx => ?_, fun x y hx hy he => ?_, fun j hj => rfl, ?_,
    fun t ht => ht, by_rfl, fun i hi hno => absurd rfl (hno i hi.1)⟩
  · show E.K = _
    rw [hL, show {i | i < E.K} = ((Finset.range E.K : Finset ℕ) : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  · -- sides
    have hi' := hi.1
    obtain ⟨hne, htouch⟩ := hside hi'
    obtain ⟨hu, hd⟩ := hupdn i hi'
    refine ⟨hu, hd, ?_, fun X hX => ?_⟩
    · show st.cl E (E.N.chord i).up ≠ st.cl E (E.N.chord i).dn
      rw [hcl _ hu, hcl _ hd]
      exact fun e => hne (hE.hRC.2.1 _ _ hu hd e)
    · show _ ↔ X = st.cl E (E.N.chord i).up ∨ X = st.cl E (E.N.chord i).dn
      rw [hcl _ hu, hcl _ hd, hF] at *
      zvoij at hX
      obtain ⟨r, hr, rfl⟩ := hE.hRC.2.2 X hX
      rw [htouch r hr]
      grind
  · -- classes
    have hx' := href x hx
    obtain ⟨hmem, hnd, -, hwt⟩ := hE.hRO x hx'
    have hexl : st.exl x = (E.N.region x).chords :=
      exl_of_list st x rfl fun t _ => rfl
    rw [hcl x hx', hF, hexl]
    refine ⟨(deg_region hE.hNF hE.hRC hE.hRO hx').symm, hwt, hnd, fun i => ?_, ?_⟩
    · rw [hmem i, hL]; rfl
    · show (E.N.region x).chords.length ≤ E.D
      rw [← deg_region hE.hNF hE.hRC hE.hRO hx']
      exact hdeg _ (hE.hRC.1 x hx')
  · -- distinct classes
    rw [hcl x zttof, hcl y zttog] at he
    exact hE.hRC.2.1 _ _ zttof zttog he
  · -- the ring: every position is live
    have hA : ∀ j, j < E.A → st.Lv j := by
      zun
      have hcut := pk_cut hE.hNF hE.hne hj
      rw [← hF] at hcut
      unfold St.F at hcut
      rw [isCut_fam_iff hE.hNF hE.hM] at hcut
      obtain ⟨i, -, hi, hk⟩ := hcut
      have hpos : st.Lv j := by
        unfold St.Lv
        show 0 < cntInit E.K nd0 nd1 j
        zumse
        zucot
        · have e := (hstat.nd0 i hi).2
          zujme
          have : nd0 i = j := key_inj hE (hstat.nd0 i hi).1 hj e
          have : 0 < ((Finset.range E.K).filter fun i => nd0 i = j).card :=
            Finset.card_pos.2 ztkly
          omega
        · have e := (hstat.nd1 i hi).2
          zujme
          have : nd1 i = j := key_inj hE (hstat.nd1 i hi).1 hj e
          have : 0 < ((Finset.range E.K).filter fun i => nd1 i = j).card :=
            Finset.card_pos.2 ztkly
          omega
      omega
    -- at least two positions
    have hA2 : 2 ≤ E.A := by
      obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hE.hM.two_cuts (F_adm hE.hNF) hE.hne
      obtain ⟨j₁, hj₁, rfl⟩ := cut_pk hE.hNF hE.hGM hk₁
      obtain ⟨j₂, hj₂, rfl⟩ := cut_pk hE.hNF hE.hGM hk₂
      have : j₁ ≠ j₂ := fun e => hk ztdlt
      grind
    exact (ringOK_full hA2).congr (fun j hj => ⟨fun _ => trivial, fun _ => hA j hj⟩)
      ztczj ztczj
structure Dm where
  K : ℕ
  A : ℕ
  R : ℕ
  D : ℕ
  b0 : ℕ
namespace Dm
variable (d : Dm)
def oS0 : ℕ := d.K
def oS1 : ℕ := 2 * d.K
def oNd0 : ℕ := 3 * d.K
def oNd1 : ℕ := 4 * d.K
def oDeg : ℕ := 5 * d.K
def oWt : ℕ := 5 * d.K + d.R
def oExb : ℕ := 5 * d.K + 2 * d.R
def oEx : ℕ := 5 * d.K + 3 * d.R
def oCnt : ℕ := d.oEx + d.R * d.D
def oNxt : ℕ := d.oCnt + d.A
def oPrv : ℕ := d.oNxt + d.A
def oEg : ℕ := d.oPrv + d.A
def oPz : ℕ := d.oEg + d.A
def oStk : ℕ := d.oPz + d.A
def cap : ℕ := d.K + d.D * d.K
def oTmp : ℕ := d.oStk + d.cap
def oList : ℕ := d.oTmp + d.D + 1
def oEnd : ℕ := d.oList + 3 * d.K
end Dm

/-- Unfold the layout offsets. -/
macro "dm_simp" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Dm.oS0, Dm.oS1, Dm.oNd0, Dm.oNd1, Dm.oDeg, Dm.oWt, Dm.oExb, Dm.oEx,
    Dm.oCnt, Dm.oNxt, Dm.oPrv, Dm.oEg, Dm.oPz, Dm.oStk, Dm.cap, Dm.oTmp, Dm.oList,
    Dm.oEnd] at *)

/-- **The memory holds the state.** -/
structure Enc (m : ℕ → ℕ) (d : Dm) (st : St) : Prop where
  live : ∀ i, i < d.K → m (d.b0 + i) = st.live i
  s0 : ∀ i, i < d.K → m (d.b0 + d.oS0 + i) = st.s0 i
  s1 : ∀ i, i < d.K → m (d.b0 + d.oS1 + i) = st.s1 i
  nd0 : ∀ i, i < d.K → m ztjtk = st.nd0 i
  nd1 : ∀ i, i < d.K → m ztjtl = st.nd1 i
  deg : ∀ x, x < d.R → m ztjti = st.deg x
  wt : ∀ x, x < d.R → m ztjto = st.wt x
  exb : ∀ x, x < d.R → m ztjtj = d.b0 + d.oEx + d.D * x
  ex : ∀ x t, x < d.R → t < d.D → m (d.b0 + d.oEx + d.D * x + t) = st.ex x t
  cnt : ∀ j, j < d.A → m ztgib = st.cnt j
  nxt : ∀ j, j < d.A → m ztqlf = st.nxt j
  prv : ∀ j, j < d.A → m (d.b0 + d.oPrv + j) = st.prv j
  eg : ∀ j, j < d.A → m ztqld = st.eg j
  pz : ∀ j, j < d.A → m (d.b0 + d.oPz + j) = st.pz j
  stk : ∀ t, t < d.cap → m (d.b0 + d.oStk + t) = st.stk t
variable {m : ℕ → ℕ} {d : Dm} {st : St}

/-! ## The slot arithmetic -/
theorem slot_lt {D x t R : ℕ} (hx : x < R) (ht : t < D) : D * x + t < R * D := by
  have : D * x + t < D * zthf := by_grind
  zuhvj
variable {D x t : ℕ}
theorem slot_div (ht : t < D) : ztpxa / D = x := by
  have hD : 0 < D := by_omega
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt ht, Nat.zero_add]
theorem slot_mod (ht : t < D) : ztpxa % D = t := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

/-! ## Writing -/

/-- Store into `live`. -/
theorem Enc.set_live (h : Enc m d st) {k : ℕ} (hk : k < d.K) (v : ℕ) :
    Enc (upd m (d.b0 + k) v) d { st with live := Function.update st.live k v } := by
  zugsw
  · zug
    zufrg
    · simp_all
    · zubc
      zuoi

      zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `s0`. -/
theorem Enc.set_s0 (h : Enc m d st) {k : ℕ} (hk : k < d.K) (v : ℕ) :
    Enc (upd m (d.b0 + d.oS0 + k) v) d { st with s0 := Function.update st.s0 k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    zufrg
    · simp_all
    · zubc
      zuoi

      zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `s1`. -/
theorem Enc.set_s1 (h : Enc m d st) {k : ℕ} (hk : k < d.K) (v : ℕ) :
    Enc (upd m (d.b0 + d.oS1 + k) v) d { st with s1 := Function.update st.s1 k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    zufrg
    · simp_all
    · zubc
      zuoi

      zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `deg`. -/
theorem Enc.set_deg (h : Enc m d st) {k : ℕ} (hk : k < d.R) (v : ℕ) :
    Enc (upd m (d.b0 + d.oDeg + k) v) d { st with deg := Function.update st.deg k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    zujtr
    · simp_all
    · zubc
      zuoi

      zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `wt`. -/
theorem Enc.set_wt (h : Enc m d st) {k : ℕ} (hk : k < d.R) (v : ℕ) :
    Enc (upd m (d.b0 + d.oWt + k) v) d { st with wt := Function.update st.wt k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    zujtr
    · simp_all
    · zubc
      zuoi

      zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `cnt`. -/
theorem Enc.set_cnt (h : Enc m d st) {k : ℕ} (hk : k < d.A) (v : ℕ) :
    Enc (upd m (d.b0 + d.oCnt + k) v) d { st with cnt := Function.update st.cnt k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    zufrh
    · simp_all
    · zubc
      zuoi

      zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `nxt`. -/
theorem Enc.set_nxt (h : Enc m d st) {k : ℕ} (hk : k < d.A) (v : ℕ) :
    Enc (upd m (d.b0 + d.oNxt + k) v) d { st with nxt := Function.update st.nxt k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    zufrh
    · simp_all
    · zubc
      zuoi

      zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `prv`. -/
theorem Enc.set_prv (h : Enc m d st) {k : ℕ} (hk : k < d.A) (v : ℕ) :
    Enc (upd m (d.b0 + d.oPrv + k) v) d { st with prv := Function.update st.prv k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    zufrh
    · simp_all
    · zubc
      zuoi

      zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh

/-- Store into `stk`. -/
theorem Enc.set_stk (h : Enc m d st) {k : ℕ} (hk : k < d.cap) (v : ℕ) :
    Enc (upd m (d.b0 + d.oStk + k) v) d { st with stk := Function.update st.stk k v } := by
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    have := slot_lt hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zuup
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    by_cases hq : t = k
    · simp_all
    · zubc
      zuoi

      zubnh

/-- Store into an exit slot. -/
theorem Enc.set_ex (h : Enc m d st) {x₀ t₀ : ℕ} (hx₀ : x₀ < d.R) (ht₀ : t₀ < d.D) (v : ℕ) :
    Enc (upd m (d.b0 + d.oEx + d.D * x₀ + t₀) v) d
      { st with ex := fun x t => if x = x₀ ∧ t = t₀ then v else st.ex x t } := by
  have hs₀ := slot_lt hx₀ ht₀
  zugsw
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmz
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnf
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubng
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubna
  · zug
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnb
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmw
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubni
  · zuh
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmy
  · zuzb
    by_cases hq : x = x₀ ∧ t = t₀
    · simp_all
    · rw [Machine.upd_other _ _ _ ?_]
      · dsimp only; rw [ite_eq_right hq]; exact h.ex x t hx ht
      · zufhz
        apply hq
        have e1 : d.D * x + t = d.D * x₀ + t₀ := by_omega
        have e2 := congrArg (· / d.D) e1
        have e3 := congrArg (· % d.D) e1
        rw [slot_div ht, slot_div ht₀] at e2
        simp_all
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmv
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnc
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnd
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubmx
  · zun
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubne
  · zucj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    zubnh
open Machine Machine.Stmt Programs SignK
def bit (b : Bool) : ℕ := if b then 1 else 0
structure Cst (c : Config) (E : Env) (d : Dm) : Prop where
  γ : c.nreg 90014 = E.γ
  sz : c.nreg 90018 = E.sz
  one : c.nreg 90019 = 1
  three : c.nreg 90020 = 3
  two : c.nreg 90021 = 2
  bLive : c.nreg 90030 = d.b0
  bS0 : c.nreg 90031 = d.b0 + d.oS0
  bS1 : c.nreg 90032 = d.b0 + d.oS1
  bNd0 : c.nreg 90033 = d.b0 + d.oNd0
  bNd1 : c.nreg 90034 = d.b0 + d.oNd1
  bDeg : c.nreg 90035 = d.b0 + d.oDeg
  bWt : c.nreg 90036 = d.b0 + d.oWt
  bExb : c.nreg 90037 = d.b0 + d.oExb
  bCnt : c.nreg 90038 = d.b0 + d.oCnt
  bNxt : c.nreg 90039 = d.b0 + d.oNxt
  bPrv : c.nreg 90040 = d.b0 + d.oPrv
  bEg : c.nreg 90041 = d.b0 + d.oEg
  bPz : c.nreg 90042 = d.b0 + d.oPz
  bStk : c.nreg 90043 = d.b0 + d.oStk
  bTmp : c.nreg 90044 = d.b0 + d.oTmp

/-- The constant registers survive any statement writing only registers of `B` avoiding
`90000 … 90059`. -/
theorem Cst.frame {c c' : Config} {E : Env} {d : Dm} (h : Cst c E d)
    (hr : ∀ r, r < 90045 → 90000 ≤ r → c'.nreg r = c.nreg r) : Cst c' E d := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ by_norm_num by_norm_num]; assumption)

/-! ## The weight of a gap -/

/-- `r92 := gwt sz eg pz r90 r91`. -/
def gwStmt : Stmt :=
  .seq (block [.addN 90093 90041 90090, .loadN 90094 90093, .addN 90093 90041 90091,
      .loadN 90095 90093, .addN 90093 90042 90091, .loadN 90096 90093, .addN 90097 90095 90096])
    (.ifLtN 90090 90091 (.instr (.subN 90092 90097 90094))
      (.ifLtN 90091 90090
        (.seq (.instr (.subN 90098 90018 90094))
          (.seq (.ifLtN 90097 90094 (.instr (.copyN 90099 90097)) (.instr (.copyN 90099 90094)))
            ztnay))
        (.instr (.copyN 90092 90018))))

/-- Registers in `[a, b)`. -/
def Bin (a b : ℕ) (r : ℕ) : Bool := decide (a ≤ r ∧ r < b)
theorem wr_gwStmt : wr ztsvq gwStmt = true := by_decide
variable {P : Polygon} {W : ℕ}
/-- **The weight of a gap between two positions.** -/
theorem gwStmt_exec {E : Env} {d : Dm} {st : St} (c : Config)
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st)
    (ha : c.nreg 90090 < d.A) (hb : c.nreg 90091 < d.A)
    (hbx : st.eg ztqin + st.pz ztqin ≤ E.sz) (hszW : E.sz ≤ W)
    (hbase : d.b0 + d.oEnd ≤ W) :
    ∃ c' k, Exec P W gwStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90092 = gwt E.sz st.eg st.pz (c.nreg 90090) ztqin ∧
      FrameB ztsvq c c' := by
  suffices h : ∃ c' k, Exec P W gwStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90092 = gwt E.sz st.eg st.pz _ _ by
    zueig
    exact ⟨c', k, e, hk, hr, exec_frameB e wr_gwStmt⟩
  set a := c.nreg 90090
  set b := c.nreg 90091
  have ra := henc.eg a ha
  have rb := henc.eg b hb
  have rx := henc.pz b hb
  have hEg := hC.bEg
  have hPz := hC.bPz
  have hsz := hC.sz
  unfold gwStmt
  refine spec_seq ?_
  exec_block
  · zuoyl; dm_simp; omega
  · config_simp; zuoyl; dm_simp; omega
  · config_simp; rw [hPz]; dm_simp; omega
  · config_simp; grind
  -- after the loads
  have la : c.nmem _ = st.eg a := ra
  unfold gwt
  zuul
  · refine spec_ifLtN_true by_tauto
      (spec_instr zthao fun _ => zteh)
    config_simp
    grind
  · refine spec_ifLtN_false by_tauto ?_
    zujta
    · refine spec_ifLtN_true by_tauto ?_
      refine spec_seq (spec_instr zthao fun hw₁ => ?_)
      have hmin : ∀ (c₁ : Config), WordsBounded W c₁ → c₁.nreg 90099 =
          min ztqww ztwex → c₁.nreg 90098 = E.sz - st.eg a →
          ∃ c' k, Exec P W ztnay c₁ c' k ∧ k = 1 ∧
            c'.nreg 90092 = (E.sz - st.eg a) + min ztqww ztwex := by
        intro c₁ hw₁ h99 h98
        refine ⟨_, 1, Exec.addN hw₁ _ _ _ by_omega, rfl, ?_⟩
        simp_all
      by_cases hm : st.eg b + st.pz b < st.eg a
      · have e1 := Exec.copyN (P := P) hw₁ 90099 90097
        obtain ⟨c', k₂, e2, hk₂, hr⟩ := hmin _ e1.wb_right
          (by config_simp; grind)
          (by config_simp; grind)
        refine ⟨c', _, .seq (Exec.ifLtN_true (by config_simp; grind)
          e1) e2, by_omega, ?_⟩
        grind
      · have e1 := Exec.copyN (P := P) hw₁ 90099 90094
        obtain ⟨c', k₂, e2, hk₂, hr⟩ := hmin _ e1.wb_right
          (by config_simp; rw [hEg, ra, min_eq_right by_omega])
          (by config_simp; grind)
        refine ⟨c', _, .seq (Exec.ifLtN_false (by config_simp; grind)
          e1) e2, by_omega, ?_⟩
        grind
    · refine spec_ifLtN_false by_tauto
        (spec_instr ztowy fun _ => zteh)
      config_simp
      grind

/-! ## The death test -/

/-- `r89 := [r88 = r68 ∧ r72 = 1] ∨ [r88 = r69 ∧ r73 = 1]`. -/
def ddStmt : Stmt :=
  .seq (.instr (.constN 90089 0))
    (.seq (.ifLtN 90088 90068 .skip (.ifLtN 90068 90088 .skip
        (.ifLtN 90072 90019 .skip ztigb)))
      (.ifLtN 90088 90069 .skip (.ifLtN 90069 90088 .skip
        (.ifLtN 90073 90019 .skip ztigb))))
theorem wr_ddStmt : wr (Bin 90089 90090) ddStmt = true := by_decide

/-- One test of `ddStmt`. -/
theorem ddOne_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    {rj rn rb : ℕ} {b : Bool} (h19 : c.nreg 90019 = 1) (hb : c.nreg rb = bit b)
    (_hv : c.nreg 90089 ≤ 1) :
    ∃ c' k, Exec P W (.ifLtN rj rn .skip (.ifLtN rn rj .skip
        (.ifLtN rb 90019 .skip ztigb))) c c' k ∧ k ≤ 7 ∧
      c'.nreg 90089 = (if c.nreg rj = c.nreg rn ∧ b = true then 1 else c.nreg 90089) ∧
      ∀ r, r ≠ 90089 → c'.nreg r = c.nreg r := by
  by_cases h1 : c.nreg rj < c.nreg rn
  · exact ⟨c, _, .ifLtN_true h1 ztjd, by_omega, by_grind,
      by omega⟩
  by_cases h2 : c.nreg rn < c.nreg rj
  · exact ⟨c, _, .ifLtN_false h1 ztxdj, by_omega,
      by grind, by_omega⟩
  cases b with
  | false =>
    exact ⟨c, _, .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true ztlhr
      ztjd)), by_omega, by_simp, by_omega⟩
  | true =>
    refine ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false ztlhr
      (Exec.constN hw 90089 1 hW))), by_omega, ?_, by_simp_all⟩
    rw [ite_eq_left by_grind]; simp

/-- **The death test.** -/
theorem ddStmt_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    {b1 b2 : Bool} (h19 : c.nreg 90019 = 1) (h72 : c.nreg 90072 = bit b1)
    (h73 : c.nreg 90073 = bit b2) :
    ∃ c' k, Exec P W ddStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90089 = bit ((decide (c.nreg 90088 = c.nreg 90068) && b1) ||
        (decide (c.nreg 90088 = c.nreg 90069) && b2)) ∧ FrameB (Bin 90089 90090) c c' := by
  suffices h : ∃ c' k, Exec P W ddStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90089 = bit _ by
    zueig
    exact ⟨c', k, e, hk, hr, exec_frameB e wr_ddStmt⟩
  have e0 := Exec.constN (P := P) hw 90089 0 by_omega
  set c₀ := { c with nreg := upd c.nreg 90089 0 }
  obtain ⟨c₁, k₁, e₁, hk₁, h₁, f₁⟩ := ddOne_exec (P := P) (rj := 90088) (rn := 90068) (rb := 90072)
    c₀ e0.wb_right hW (b := b1) by_tauto by_tauto
    by_positivity
  obtain ⟨c₂, k₂, e₂, hk₂, h₂, f₂⟩ := ddOne_exec (P := P) (rj := 90088) (rn := 90069) (rb := 90073)
    c₁ e₁.wb_right hW (b := b2) ztlhc
    ztlhc (by zvnbm; split_ifs <;> simp [c₀, upd])
  refine ⟨c₂, _, .seq e0 ztyv, by_omega, ?_⟩
  rw [h₂, h₁, f₁ _ by_decide, f₁ _ by_decide]
  simp only [c₀, upd, ite_eq_right (show (90088 : ℕ) ≠ 90089 by decide),
    ite_eq_right (show (90068 : ℕ) ≠ 90089 by decide), ite_eq_right (show (90069 : ℕ) ≠ 90089 by decide)]
  unfold bit
  grind

/-! ## The weight of the gap around a dying position -/
theorem Bin_false {a b r : ℕ} (h : r < a ∨ b ≤ r) : Bin a b r = false := by
  unfold Bin; grind

/-- The skip-or-load step of `jwStmt`. -/
theorem skipLoad_exec (c : Config) (hw : WordsBounded W c) {rb rp : ℕ}
    {b : Bool} (h19 : c.nreg 90019 = 1) (h89 : c.nreg 90089 = bit b)
    (hW : b = true → c.nreg rb + c.nreg rp ≤ W) (_h80 : rb ≠ 90080) (_h19' : rb ≠ 90019)
    (_hp80 : rp ≠ 90080) (_hp89 : rp ≠ 90089) :
    ∃ c' k, Exec P W (.ifLtN 90089 90019 .skip (block [.addN 90080 rb rp, .loadN rp 90080]))
      c c' k ∧ k ≤ 4 ∧
      c'.nreg rp = (if b then c.nmem (c.nreg rb + c.nreg rp) else c.nreg rp) ∧
      (∀ r, r ≠ 90080 → r ≠ rp → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  cases b with
  | false =>
    exact ⟨c, _, .ifLtN_true ztlhk ztjd, by_omega, by_simp,
      by omega, rfl⟩
  | true =>
    refine spec_ifLtN_false ztlhk ?_
    exec_block
    · simp_all
    · simp_all

/-- `r85 := jw` for the position `r86` with death bit `r87`. -/
def jwStmt : Stmt :=
  .ifLtN 90087 90019 ztoui
    (.seq (block [.addN 90080 90040 90086, .loadN 90081 90080, .copyN 90088 90081])
      (.seq ddStmt
        (.seq (.ifLtN 90089 90019 .skip (block [.addN 90080 90040 90081, .loadN 90081 90080]))
          (.seq (block [.addN 90080 90039 90086, .loadN 90082 90080, .copyN 90088 90082])
            (.seq ddStmt
              (.seq (.ifLtN 90089 90019 .skip (block [.addN 90080 90039 90082, .loadN 90082 90080]))
                (.seq ztkso
                  (.seq gwStmt (.instr (.copyN 90085 90092))))))))))
theorem wr_jwStmt : wr ztsvp jwStmt = true := by_decide

/-- **The weight of the gap around a dying position** (`St.jw`). -/
theorem jwStmt_exec {E : Env} {d : Dm} {st : St} (c : Config)
    (hw : WordsBounded W c) (hW1 : 1 ≤ W) (hC : Cst c E d) (henc : Enc c.nmem d st) {cc k : ℕ}
    (h86 : c.nreg 90086 = k) (h87 : c.nreg 90087 = bit (decide (st.cnt k = 1)))
    (h68 : c.nreg 90068 = st.nd0 cc) (h69 : c.nreg 90069 = st.nd1 cc)
    (h72 : c.nreg 90072 = bit ztxwi)
    (h73 : c.nreg 90073 = bit ztxwj)
    (hk : k < d.A) (hkL : 0 < st.cnt k)
    (hring : ∀ j, j < d.A → 0 < st.cnt j → st.prv j < d.A ∧ 0 < st.cnt ztwez ∧
      st.nxt j < d.A ∧ 0 < st.cnt ztwey)
    (hbx : ∀ j, j < d.A → st.eg j + st.pz j ≤ E.sz) (hszW : E.sz ≤ W)
    (hbase : d.b0 + d.oEnd ≤ W) :
    ∃ c' k', Exec P W jwStmt c c' k' ∧ k' ≤ 100 ∧ c'.nreg 90085 = st.jw E cc k ∧
      FrameB ztsvp c c' := by
  suffices h : ∃ c' k', Exec P W jwStmt c c' k' ∧ k' ≤ 100 ∧ c'.nreg 90085 = st.jw E cc k by
    obtain ⟨c', k', e, hk', hr⟩ := h
    exact ⟨c', k', e, hk', hr, exec_frameB e wr_jwStmt⟩
  unfold jwStmt St.jw
  by_cases h1 : st.cnt k = 1
  swap
  · refine spec_ifLtN_true zthtr
      (spec_instr ztbbp fun _ => zteh)
    simp_all
  refine spec_ifLtN_false zthtr ?_
  zubel
  obtain ⟨hpA, hpL, hsA, hsL⟩ := hring k hk hkL
  -- the predecessor
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90080 90040 90086,
      .loadN 90081 90080, .copyN 90088 90081]) c c₁ k₁ ∧ k₁ = 3 ∧
      (c₁.nreg 90081 = st.prv k ∧ c₁.nreg 90088 = st.prv k ∧
        (∀ r, r ≠ 90080 → r ≠ 90081 → r ≠ 90088 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    exec_block
    · rw [hC.bPrv, h86]; dm_simp; omega
    · have e : c.nmem _ = st.prv k := henc.prv k hk
      refine ztdqx <;>
        (config_simp; rw [hC.bPrv, h86, e])
  obtain ⟨q81, q88, qr, qm⟩ := q
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, d₂, f₂⟩ := ddStmt_exec (P := P) c₁ w₁ hW1
    (b1 := decide ztcbb) (b2 := decide ztcbc)
    (by rw [qr _ by_decide by_decide by_decide, hC.one])
    by_simp_all
    by_simp_all
  zue
  zucgb
  have hdd1 : c₂.nreg 90089 = bit (st.dd cc ztmon) := by
    rw [d₂, q88, qr _ by_decide by_decide by_decide,
      qr _ by_decide by_decide by_decide, h68, h69]
    rfl
  obtain ⟨c₃, k₃, e₃, hk₃, p₃, r₃, m₃⟩ := skipLoad_exec (P := P) c₂ w₂ (rb := 90040) (rp := 90081)
    (b := st.dd cc ztmon) (by rw [g₂ _ by_decide, qr _ by_decide by_decide by_decide,
      hC.one]) hdd1
    (fun _ => by
      rw [g₂ _ by_decide, g₂ _ by_decide, qr _ by_decide by_decide by_decide, q81,
        hC.bPrv]
      dm_simp; omega) by_decide by_decide by_decide by_decide
  have hpr : c₃.nreg 90081 = st.prD cc k := by
    rw [p₃, g₂ _ by_decide, g₂ _ by_decide, qr _ by_decide by_decide by_decide, q81,
      hC.bPrv, f₂.2.2.1, qm]
    unfold St.prD
    split_ifs
    · exact henc.prv _ hpA
    · rfl
  zubj
  -- the successor
  have c3r : ∀ r, r ≠ 90080 → r ≠ 90081 → r ≠ 90088 → r ≠ 90089 → c₃.nreg r = c.nreg r := by
    zukjt
    rw [r₃ r a1 a2, g₂ r ztpwi, qr r a1 a2 a3]
  have m3 : ztckd := by rw [m₃, f₂.2.2.1, qm]
  obtain ⟨c₄, k₄, e₄, hk₄, q⟩ : ∃ c₄ k₄, Exec P W (block [.addN 90080 90039 90086,
      .loadN 90082 90080, .copyN 90088 90082]) c₃ c₄ k₄ ∧ k₄ = 3 ∧
      (c₄.nreg 90082 = st.nxt k ∧ c₄.nreg 90088 = st.nxt k ∧
        (∀ r, r ≠ 90080 → r ≠ 90082 → r ≠ 90088 → c₄.nreg r = c₃.nreg r) ∧
        c₄.nmem = c₃.nmem) := by
    exec_block
    · rw [c3r _ by_decide by_decide by_decide by_decide,
        c3r _ by_decide by_decide by_decide by_decide, hC.bNxt, h86]; dm_simp; omega
    · have e : c.nmem _ = st.nxt k := henc.nxt k hk
      refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => by simp [upd, h1, h2, h3], rfl⟩ <;>
        (config_simp; rw [c3r _ by_decide by_decide by_decide by_decide,
          c3r _ by_decide by_decide by_decide by_decide, hC.bNxt, h86, m3, e])
  obtain ⟨q82, q88', qr', qm'⟩ := q
  zucc
  have c4r : ∀ r, r ≠ 90080 → r ≠ 90081 → r ≠ 90082 → r ≠ 90088 → r ≠ 90089 →
      c₄.nreg r = c.nreg r := by_grind
  obtain ⟨c₅, k₅, e₅, hk₅, d₅, f₅⟩ := ddStmt_exec (P := P) c₄ w₄ hW1
    (b1 := decide ztcbb) (b2 := decide ztcbc)
    (by rw [c4r _ by_decide by_decide by_decide by_decide by_decide, hC.one])
    by_grind
    by_grind
  zuef
  zuiux
  have hdd2 : c₅.nreg 90089 = bit (st.dd cc ztkfm) := by
    rw [d₅, q88', c4r _ by_decide by_decide by_decide by_decide by_decide,
      c4r _ by_decide by_decide by_decide by_decide by_decide, h68, h69]
    rfl
  have hb6 : st.dd cc ztkfm = true → c₅.nreg 90039 + c₅.nreg 90082 ≤ W := by
    zuhge
    rw [g₅ _ by_decide, g₅ _ by_decide,
      c4r _ by_decide by_decide by_decide by_decide by_decide, q82, hC.bNxt]
    dm_simp; omega
  obtain ⟨c₆, k₆, e₆, hk₆, p₆, r₆, m₆⟩ := skipLoad_exec (P := P) c₅ w₅ (rb := 90039) (rp := 90082)
    (b := st.dd cc ztkfm) (by rw [g₅ _ by_decide,
      c4r _ by_decide by_decide by_decide by_decide by_decide, hC.one]) hdd2
    hb6 by_decide by_decide by_decide by_decide
  have m6 : c₆.nmem = c.nmem := by rw [m₆, f₅.2.2.1, qm', m3]
  have hsu : c₆.nreg 90082 = st.suD cc k := by
    rw [p₆, g₅ _ by_decide, g₅ _ by_decide,
      c4r _ by_decide by_decide by_decide by_decide by_decide, q82, hC.bNxt,
      f₅.2.2.1, qm', m3]
    unfold St.suD
    split_ifs
    · exact henc.nxt _ hsA
    · rfl
  have hpr6 : c₆.nreg 90081 = st.prD cc k := by
    rw [r₆ _ by_decide by_decide, g₅ _ by_decide, qr' _ by_decide by_decide
      by_decide, hpr]
  zujb
  have c6r : ∀ r, r < 90080 → c₆.nreg r = c.nreg r := fun r hr => by
    rw [r₆ r by_omega by_omega, g₅ r ztpwi,
      c4r r by_omega by_omega by_omega by_omega by_omega]
  -- the bounds of the two neighbours
  have hpD : st.prD cc k < d.A := by
    unfold St.prD; split_ifs
    · grind
    omega
  have hsD : st.suD cc k < d.A := by
    unfold St.suD; split_ifs
    · grind
    omega
  -- the copies and the weight
  obtain ⟨c₇, k₇, e₇, hk₇, q90, q91, r₇⟩ : ∃ c₇ k₇, Exec P W
      ztkso c₆ c₇ k₇ ∧ k₇ = 2 ∧
      c₇.nreg 90090 = st.prD cc k ∧ c₇.nreg 90091 = st.suD cc k ∧
      (∀ r, r ≠ 90090 → r ≠ 90091 → c₇.nreg r = c₆.nreg r) := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => by zunhr⟩
    · config_simp; omega
    · config_simp; omega
  have hC₇ := hC.frame fun r hr _ => by
    rw [r₇ r by_omega by_omega, c6r r by_omega]
  have henc₇ : Enc c₇.nmem d st := by
    have  := (exec_frameB e₇ (B := Bin 90090 90092) by_decide).2.2.1
    grind
  obtain ⟨c₈, k₈, e₈, hk₈, g₈, -⟩ := gwStmt_exec (P := P) c₇ e₇.wb_right hC₇ henc₇
    by_omega by_omega by_grind hszW hbase
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈
    (Exec.copyN e₈.wb_right 90085 90092)))))))), by_omega, ?_⟩
  config_simp
  grind
