module

public import Chazelle.MacT
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.OracleBook

namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt SideAttach)
open Chazelle.Visibility (rayPt OpenEdgePt)
namespace Brute
variable {A B : Point} {a v b : Point} {i : ℕ}
theorem sideDot_key (h : sideCross B A = 0) :
    sideDot B A * A.2 = B.2 * ztnit := by
  unfold sideCross at h; unfold sideDot
  grind
theorem sideCcw_horiz_same (hAB : 0 < A.2 * B.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    sideCcw B (ztwn : Point) A ↔ sideCross B A ≤ 0 := by
  zubam

  have hB0 : ztsan := by rintro h; simp_all
  zubat
  zufqe
  zujhy

  · rintro (⟨h1, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exfalso
      have := mul_pos h2 h3
      nlinarith
    · grind
    · simp_all
    simp_all
  · zuq
    zubuf
    · zuhl
      zulov
      zux

      have h1 : -σ * B.2 * ztokz = -(A.2 * B.2) := by_nlinarith
      have h2 : -σ * B.2 ≠ 0 := by_simp_all
      have h3 : σ * A.2 ≠ 0 := by_simp_all
      have h4 : -σ * B.2 < 0 := by_grind
      have h5 : σ * A.2 < 0 := by_grind
      nlinarith [mul_pos_of_neg_of_neg h4 h5]
    · zubef
      have hk := sideDot_key h
      zuker
      refine ⟨h, ?_, by_simp_all⟩
      by_contra hd
      zumil
      have : sideDot B A * A.2 * A.2 ≤ 0 ∨ True := Or.inr trivial
      zuevm
      · have hb : ztkzu := by
          by_contra hb; push Not at hb
          have := hb.lt_or_eq; rcases this with hb | hb
          · nlinarith
          simp_all
        nlinarith [mul_neg_of_neg_of_pos hb hpos]
      · have hb : ztpho := by
          simp_all
        nlinarith [mul_pos hb hpos]
theorem sideCcw_horiz_opp (hAB : A.2 * B.2 < 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    sideCcw B (ztwn : Point) A ↔ 0 < -σ * B.2 := by
  zubam

  zuker
  have hsame : 0 < σ * A.2 → 0 < -σ * B.2 := by
    zuq
    zulgq
    zuca
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h.le hc]
  have hsame' : 0 < -σ * B.2 → 0 < σ * A.2 := by
    zuq
    zulgq
    zuca
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h.le]
  zufqe
  zujhy

  · rintro (⟨-, h2, -⟩ | ⟨-, h2 | h2⟩ | ⟨-, -, h2⟩ | ⟨h1, h2, -⟩)
    · zucvi
    · zucvi
    · simp_all
    · zucvi
    · exfalso
      zulkh
      zuevm
      · zufgl

      · zufgk

  · zuq
    rcases lt_trichotomy (sideCross B A) 0 with h1 | h1 | h1
    · grind
    · zurx
      refine ⟨h1, ?_, h⟩
      zulkh
      zuevm
      · zufgl

      · zufgk

    grind

/-- The emission rule at a corner `a → v → b` for the horizontal direction `σ`. -/
def emitR (a v b : Point) (σ : ℝ) : Prop :=
  if ztojo then ¬ 0 < det a v b else (σ = 1 ↔ b.2 < v.2)

/-- **The horizontal directions in the left sector of a corner** whose neighbours are at other
heights. -/
theorem sideLeftOf_horiz (ha : a.2 ≠ v.2) (hb : b.2 ≠ v.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : sideLeftOf a v b ztczx ↔ emitR a v b σ := by
  unfold sideLeftOf emitR
  rw [FuseMath.rayPt_sub_one]
  have hA : (a - v).2 = a.2 - v.2 := rfl
  zujzc
  have hA0 := sub_ne_zero.2 ha
  have hB0 := sub_ne_zero.2 hb
  by_cases hs : ztojo
  · rw [ite_eq_left hs]
    have hAB : 0 < (a - v).2 * (b - v).2 := by
      zuexr

      · have : ztmud := by
          grind
        exact mul_pos_of_neg_of_neg h1 this
      simp_all
    rw [sideCcw_horiz_same hAB hσ, Chain.sideCross_corner]
    simp
  · zulqj
    have hAB : (a - v).2 * (b - v).2 < 0 := by
      zuexr

      · have : ztrzi := by
          grind
        exact mul_neg_of_neg_of_pos h1 this
      · have : ztmud := by
          grind
        exact mul_neg_of_pos_of_neg h1 this
    rw [sideCcw_horiz_opp hAB hσ, hB]
    zur
    · simp
    grind

/-! ## The corners of the walk of a chain model -/
variable {C : Chain}

/-- The chain vertex at tour position `i`. -/
noncomputable def vPt (C : Chain) (i : ℕ) : Point := C.vertex ztlx

/-- The walk vertex before tour position `i` (the top of the slit before position `0`). -/
noncomputable def prevPt (C : Chain) (i : ℕ) : Point :=
  if i = 0 then C.slitTop else C.vertex (C.sideIdx C.sideBeta ztei)

/-- The walk vertex after tour position `i` (the top of the slit after position `2m`). -/
noncomputable def nextPt (C : Chain) (i : ℕ) : Point :=
  if i = 2 * C.m then C.slitTop else C.vertex ztwlt
theorem walk_vtx_tour (hi : i ≤ 2 * C.m) : (chainModel C).W.vtx ztcy = vPt C i :=
  C.sideWalk_vtx_tour C.sideBeta hi
theorem walk_n : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n C.sideBeta
theorem walk_prev (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx ((i + 6 + (chainModel C).W.n - 1) % (chainModel C).W.n) = prevPt C i := by
  rw [walk_n, show i + 6 + ztz - 1 = (i + 5) + ztz by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt by_omega]
  unfold prevPt
  zus
  · subst h; rfl
  · rw [show i + 5 = ztei + 6 by omega]; exact C.sideWalk_vtx_tour _ by_omega
theorem walk_next (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx ztysm = nextPt C i := by
  unfold nextPt
  zus
  · subst h; exact C.sideWalk_vtx_wrap C.sideBeta
  · rw [walk_n, Nat.mod_eq_of_lt by_omega, show i + 6 + 1 = ztg + 6 by ring]
    exact C.sideWalk_vtx_tour _ by_omega
theorem vPt_zero : vPt C 0 = C.top := C.sideTour_zero _
theorem vPt_two_m : vPt C ztbb = C.top := C.sideTour_two_m _

/-- Consecutive tour vertices are at different heights. -/
theorem vPt_succ_ne (hDH : DistinctHeights C.P) (i : ℕ) : (vPt C ztg).2 ≠ (vPt C i).2 := by
  have hl := C.sideIdx_le C.sideBeta i
  have hl' := C.sideIdx_le C.sideBeta ztg
  zukfk
  exact ChainObs.vertex_snd_ne hDH hl' hl by_omega
theorem prevPt_ne (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (prevPt C i).2 ≠ (vPt C i).2 := by
  unfold prevPt
  zus
  · subst h; rw [vPt_zero]; exact ne_of_gt C.top_snd_lt_radius
  · have := vPt_succ_ne hDH ztei
    rw [show i - 1 + 1 = i by omega] at this
    tauto
theorem nextPt_ne (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (nextPt C i).2 ≠ (vPt C i).2 := by
  unfold nextPt
  zus
  · subst h; rw [vPt_two_m]; exact ne_of_gt C.top_snd_lt_radius
  · exact vPt_succ_ne hDH i

/-- **The horizontal directions leaving the walk vertex `i + 6` into its left sector.** -/
theorem corner_iff (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    sideLeft (chainModel C).W ztcy 0 (rayPt ztfve σ 1) ↔
      emitR zthjh ztfve zthiu σ := by
  rw [Chain.sideLeft_zero, walk_prev hi, walk_vtx_tour hi, walk_next hi]
  exact sideLeftOf_horiz (prevPt_ne hDH hi) (nextPt_ne hDH hi) hσ

/-- At tour position `0` only the direction east is emitted. -/
theorem emitR_zero (hDH : DistinctHeights C.P) {σ : ℝ} :
    emitR (prevPt C 0) (vPt C 0) (nextPt C 0) σ ↔ σ = 1 := by
  have hn : (nextPt C 0).2 < (vPt C 0).2 := by
    have hne := nextPt_ne hDH (i := 0) by_omega
    have : (nextPt C 0).2 ≤ C.top.2 := by
      unfold nextPt; zunlo
      exact C.vertex_snd_le_top ztbdw
    rw [vPt_zero] at hne ⊢
    grind
  have hp : (vPt C 0).2 < (prevPt C 0).2 := by
    rw [vPt_zero]; unfold prevPt; rw [ite_eq_left rfl]; exact C.top_snd_lt_radius
  unfold emitR
  grind

/-- At tour position `2m` only the direction west is emitted. -/
theorem emitR_two_m (hDH : DistinctHeights C.P) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    emitR (prevPt C ztbb) (vPt C ztbb) (nextPt C ztbb) σ ↔ σ = -1 := by
  have hp : (prevPt C ztbb).2 < (vPt C ztbb).2 := by
    have hne := prevPt_ne hDH le_rfl
    have : (prevPt C ztbb).2 ≤ C.top.2 := by
      unfold prevPt; zunlo
      exact C.vertex_snd_le_top ztbdw
    rw [vPt_two_m] at hne ⊢
    grind
  have hn : (vPt C ztbb).2 < (nextPt C ztbb).2 := by
    rw [vPt_two_m]; unfold nextPt; rw [ite_eq_left rfl]; exact C.top_snd_lt_radius
  unfold emitR
  grind

/-! ## Positions of the walk at a chain vertex -/

/-- **A position of the walk at a chain vertex is a tour vertex** (parameter `0`). -/
theorem pos_of_vertex (hP : C.P.Simple) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel C).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) {k : ℕ} (hk : k ≤ C.m)
    (h : sidePt (chainModel C).W p t = C.vertex k) :
    t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx C.sideBeta i = k := by
  zudhv
  zugei
  have hbox := (Chain.mem_box_iff.1 ztyhi)
  zubo
  zubnz
  have hvt := C.vertex_snd_le_top hk
  have habs1 := abs_lt.1 hbox.1
  have habs2 := abs_lt.1 hbox.2
  unfold sidePt at h
  zukve
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [Geometry.lerp_fst, Geometry.lerp_snd] at hx hy
  zucn
  rw [hW] at hx hy h
  have hwrap := C.sideWalk_vtx_wrap C.sideBeta
  rw [C.sideWalk_n] at hwrap
  have h6 : ztoqa := by
    zucqc
  zufrf
  · exfalso
    interval_cases p
    · zugci
      zuhox
    · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hx
      simp_all
    · zufmo

    · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hx
      simp_all
    · zugch
      zuhox
    · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 6 from rfl, h6] at hy
      zujnl
      nlinarith
  by_cases hpl : p = 2 * C.m + 6
  · subst hpl
    rw [hwrap, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m] at hy
    zujnl
    have ht : ztbhh := by
      zuct
      have : ztfkp := by_grind
      nlinarith
    zucfb
    refine ⟨rfl, 2 * C.m, le_rfl, rfl, ?_⟩
    have e : C.top = C.vertex k := by
      have := h
      rw [C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m] at this
      simp_all
    rw [C.sideIdx_two_m]
    exact C.sideVertex_inj hP C.topIdx_le hk e
  · set i := p - 6 with hi
    have hpi : p = i + 6 := by_omega
    have hi2 : ztdrl := by_omega
    rw [hpi] at h
    rw [Nat.mod_eq_of_lt by_omega, show i + 6 + 1 = ztg + 6 by ring,
      C.sideWalk_vtx_tour _ by_omega, C.sideWalk_vtx_tour _ by_omega] at h
    zumqk
    set k₁ := C.sideIdx C.sideBeta i
    set k₂ := C.sideIdx C.sideBeta _
    have hk₁ : k₁ ≤ C.m := C.sideIdx_le _ _
    have hk₂ : k₂ ≤ C.m := C.sideIdx_le _ _
    have ht : ztbhh := by
      zuct
      have ht' : ztfkp := by_grind
      -- the point is in the open part of a chain edge
      obtain ⟨kk, hkk, t', ht'0, ht'1, hlerp⟩ : ∃ kk, kk < C.m ∧ ∃ t', 0 < t' ∧ t' < 1 ∧
          Geometry.lerp (C.vertex k₁) (C.vertex k₂) t =
            Geometry.lerp (C.vertex kk) (C.vertex zthij) t' := by
        rcases C.sideTour_step C.sideBeta i with hs | hs
        · exact ⟨k₁, by_omega, t, ht', ht1, by_grind⟩
        · refine ⟨k₂, by_omega, 1 - t, by_linarith, by_linarith, ?_⟩
          rw [← Geometry.lerp_symm, show k₁ = k₂ + 1 by omega]
      have hopen : OpenEdgePt C.P (C.edgeIdx kk) ztib := by
        refine ⟨t', ⟨ht'0, ht'1⟩, ?_⟩
        rw [← h, hlerp]
        unfold Chain.vertex
        rw [C.edgeIdx_succ]
      exact hopen.ne_vtx hP ztmal ztcsx rfl
    zucfb
    refine ⟨rfl, i, hi2.le, hpi, ?_⟩
    have e : C.vertex k₁ = C.vertex k := by simpa [Geometry.lerp] using h
    exact C.sideVertex_inj hP hk₁ hk e

/-! ## The top index and the orientation bit -/

/-- The top index is the index of any topmost vertex (distinct heights). -/
theorem topIdx_eq_of_max (hDH : DistinctHeights C.P) {j : ℕ} (hj : j ≤ C.m)
    (htop : ∀ i, i ≤ C.m → (C.vertex i).2 ≤ (C.vertex j).2) : C.topIdx = j := by
  have h1 := C.topIdx_min hj htop
  zulhl
  have h3 := htop C.topIdx C.topIdx_le
  zuct
  exact ChainObs.vertex_snd_ne hDH C.topIdx_le hj hne zttrw

/-- **The orientation bit** in terms of sign tests, for a top vertex that is not the first
vertex (`a` is the vertex before the top, `b` the one after; `b` may be outside the chain). -/
theorem sideCcw_up {h : ℝ} (hh : 0 < h) (ha : a.2 < v.2) (hb : b.2 ≠ v.2) :
    sideCcw ztfd ztbdn ztgg ↔
      zthqo ∨ ztgrh ∨
      zthwi ∨ ztkvs := by
  zuhdt
  have e2 : ztyzc := by
    zule
  have e3 : ztyzb := by
    zule
  have e4 : sideDot ztfd ztbdn = h * ztcet := by
    unfold sideDot; zvnhb; ring
  have p2 : 0 < h * ztry ↔ v.1 < b.1 := by
    simp_all
  have p3 : 0 < h * ztdin ↔ a.1 < v.1 := by
    simp_all
  have hA : (a - v).2 < 0 := by_simp_all
  -- the dot product at a straight corner
  have hdot : det a v b = 0 → (sideDot ztfd ztgg < 0 ↔ v.2 < b.2) ∧
      (0 < sideDot ztfd ztgg ↔ b.2 < v.2) := by
    zudqe
    have hk := sideDot_key (A := a - v) (B := b - v) by_simp_all
    have hpos : 0 < (a - v).1 ^ 2 + (a - v).2 ^ 2 := by_nlinarith
    zujzc
    rw [hB] at hk
    constructor
    · constructor
      · intro hc; by_contra hc'; push Not at hc'; nlinarith [mul_nonneg (sub_nonneg.2 hc') hpos.le]
      · zugod
        nlinarith [mul_pos (sub_pos.2 hc) hpos, mul_nonpos_of_nonneg_of_nonpos hc' hA.le]
    · constructor
      · zugod
        rcases hc'.lt_or_eq with hc' | hc'
        · nlinarith [mul_pos (sub_pos.2 hc') hpos]
        simp_all
      · zuchg
        nlinarith [mul_neg_of_neg_of_pos (sub_neg.2 hc) hpos]
  zufqe
  rw [e1, e2, e3, e4, p2, p3]
  constructor
  · grind
  · rintro (h1 | h1 | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · simp_all
    · simp_all
    · simp_all
    · refine Or.inr (Or.inr (Or.inr ⟨h1, by_simp_all, Or.inr ?_⟩))
      nlinarith [mul_neg_of_pos_of_neg hh (sub_neg.2 h2)]

/-- The orientation bit is `false` when the top is the first vertex. -/
theorem sideBeta_of_top_zero (h0 : C.topIdx = 0) : C.sideBeta = false := by
  cases hb : C.sideBeta with
  | false => rfl
  | true =>
    have := C.sideBeta_eq_true_iff.1 hb
    rw [h0, show (0 : ℕ) - 1 = 0 from rfl] at this
    have e : C.vertex 0 - C.top = 0 := by unfold Chain.top; simp_all
    zudtu
    unfold sideCcw sideCross sideDot at this
    simp at this

/-- **The orientation bit** for a top vertex that is not the first vertex. -/
theorem sideBeta_iff (hDH : DistinctHeights C.P) (h0 : 0 < C.topIdx) :
    C.sideBeta = true ↔
      (0 < det ztxux C.top ztxuw ∧
          C.top.1 < (C.vertex ztbao).1 ∧ (C.vertex ztbap).1 < C.top.1) ∨
        (det ztxux C.top ztxuw < 0 ∧
          (C.top.1 < (C.vertex ztbao).1 ∨ (C.vertex ztbap).1 < C.top.1)) ∨
        (det ztxux C.top ztxuw = 0 ∧
          C.top.2 < (C.vertex ztbao).2 ∧ C.top.1 < (C.vertex ztbao).1) ∨
        (det ztxux C.top ztxuw = 0 ∧
          (C.vertex ztbao).2 < C.top.2) := by
  zumlc
  have hsl : ztzon := by
    zulbb
  zumog
  have ha : ztxsv := by
    have hne := ChainObs.vertex_snd_ne hDH (j := C.topIdx - 1) (by
      have := C.topIdx_le; omega) C.topIdx_le by_omega
    exact lt_of_le_of_ne (C.vertex_snd_le_top (by have := C.topIdx_le; omega)) hne
  have hb : (C.vertex ztbao).2 ≠ C.top.2 := by
    zuchf
    have hlt1 : C.edgeIdx ztbao < C.P.n := C.edgeIdx_lt _
    have hlt2 : C.edgeIdx C.topIdx < C.P.n := C.edgeIdx_lt _
    refine hDH _ _ hlt1 hlt2 ?_ e
    intro e'
    have hs := C.edgeIdx_succ C.topIdx
    zvmwg at hs
    have hx := C.edgeIdx_lt C.topIdx
    zudzh
    generalize C.edgeIdx C.topIdx = x at hs hx
    rcases Nat.lt_or_ge zthf C.P.n with h1 | h1
    · zvnnn at hs; omega
    · rw [show x + 1 = C.P.n by omega, Nat.mod_self] at hs; omega
  exact sideCcw_up ztqem ha hb
end Brute
open Chazelle.Visibility (xAt)
namespace Brute
variable {C : Chain}

/-- The chain edge `j` straddles the height of the vertex `v_k` (strictly). -/
def Strad (C : Chain) (j k : ℕ) : Prop :=
  ((C.vertex j).2 < (C.vertex k).2 ∧ (C.vertex k).2 < (C.vertex ztl).2) ∨
    ((C.vertex ztl).2 < (C.vertex k).2 ∧ (C.vertex k).2 < (C.vertex j).2)

/-- The abscissa of (the line of) chain edge `j` at the height of `v_k`. -/
noncomputable def edgeXk (C : Chain) (j k : ℕ) : ℝ :=
  xAt ztemc (C.vertex ztl) (C.vertex k).2

/-- Chain edge `j` is a candidate for the chord of `v_k` in direction `σ`. -/
def Cand (C : Chain) (k : ℕ) (σ : ℝ) (j : ℕ) : Prop :=
  j < C.m ∧ Strad C j k ∧ 0 < σ * ztkvv
open Classical in
/-- **The scan**: the first candidate among the chain edges `< J` with the nearest point
(strictly nearer points replace the current one). -/
noncomputable def scan (C : Chain) (k : ℕ) (σ : ℝ) : ℕ → Option ℕ
  | 0 => none
  | j + 1 =>
    if Cand C k σ j then
      (match scan C k σ j with
        | none => some j
        | some b => if σ * edgeXk C j k < σ * edgeXk C b k then some j else some b)
    else scan C k σ j
variable {k : ℕ} {σ : ℝ}
theorem scan_some : ∀ {J b : ℕ}, scan C k σ J = some b →
    b < J ∧ Cand C k σ b ∧ ∀ j, j < J → Cand C k σ j → σ * edgeXk C b k ≤ σ * edgeXk C j k
  | 0, b, h => by_tauto
  | J + 1, b, h => by
    zuhra

    · rcases hr : scan C k σ J with _ | b'
      · zukvw
        zufbb
        zubst
        refine ⟨by_omega, hc, fun j hj hcj => ?_⟩
        zujdi
        · have := scan_none_aux hr j hj
          simp_all
        simp
      · zukvw
        obtain ⟨hb'J, hb'c, hb'min⟩ := scan_some hr
        grind
    · obtain ⟨h1, h2, h3⟩ := scan_some h
      grind
where
  scan_none_aux : ∀ {J : ℕ}, scan C k σ J = none → ∀ j, j < J → ¬ Cand C k σ j
    | 0, _, j, hj => by_omega
    | J + 1, h, j, hj => by
      zuhra

      · grind
      · zujdi
        · exact scan_none_aux h j hj
        omega
theorem scan_none {J : ℕ} (h : scan C k σ J = none) :
    ∀ j, j < J → ¬ Cand C k σ j :=
  scan_some.scan_none_aux h

/-! ## The far end of a vertex chord -/
theorem xAt_mem_edge (hDH : DistinctHeights C.P) {j k : ℕ} (hj : j < C.m)
    (hs : Strad C j k) : ((edgeXk C j k, (C.vertex k).2) : Point) ∈ C.chainEdge j := by
  have hne : ztybz :=
    ChainObs.vertex_snd_ne hDH by_omega by_omega by_omega
  rw [C.chainEdge_eq, Visibility.mem_segment_iff_xAt hne]
  refine ⟨⟨?_, ?_⟩, rfl⟩ <;> rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only
  · grind
  · grind
  · grind
  grind

/-- **The far end of a vertex chord** is the nearest candidate point, or on the box. -/
theorem far_end (hDH : DistinctHeights C.P) {k : ℕ} (hk : k ≤ C.m) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : C.DirFree k σ) :
    (∀ b, scan C k σ C.m = some b →
      C.chordEnd k σ = (edgeXk C b k, (C.vertex k).2) ∧ Cand C k σ b) ∧
    (scan C k σ C.m = none → C.chordEnd k σ = (σ * C.radius, (C.vertex k).2)) := by
  obtain ⟨hpos, hend, hint⟩ := C.chord_spec hk hσ hf
  zubgl
  set v := C.vertex k with hv
  have he1 : (C.chordEnd k σ).1 = v.1 + σ * C.chordParam k σ := rfl
  have he2 : (C.chordEnd k σ).2 = v.2 := rfl
  -- candidates are not nearer than the end
  have hA : ∀ j, Cand C k σ j → C.chordParam k σ ≤ σ * ztpaz := by
    intro j ⟨hj, hs, hx⟩
    zube

    have hin := hint _ hx hlt
    have hpt : rayPt v σ (σ * ztpaz) = ((edgeXk C j k, v.2) : Point) := by
      ext
      · zufbw
      · rfl
    zvmxe at hin
    exact C.not_mem_set_of_mem_dom hin ztmqr
  -- an end on the chain is a candidate point
  have hB : C.chordEnd k σ ∈ C.set → ∃ j, Cand C k σ j ∧ edgeXk C j k = (C.chordEnd k σ).1 := by
    rintro ⟨j, hj, hmem⟩
    have hne : ztybz :=
      ChainObs.vertex_snd_ne hDH by_omega by_omega by_omega
    rw [C.chainEdge_eq, Visibility.mem_segment_iff_xAt hne] at hmem
    obtain ⟨⟨hm1, hm2⟩, hx⟩ := hmem
    have hnev := C.chordEnd_ne_vertex hk hσ hf
    have hne1 : (C.vertex j).2 ≠ v.2 := by
      zuchf
      apply hnev
      have : j = k := by
        zugjq
      zumo
      ext
      · rw [hx, he2, ← e, Visibility.xAt_left]
      omega
    have hne2 : (C.vertex ztl).2 ≠ v.2 := by
      zuchf
      apply hnev
      have : j + 1 = k := by
        zugjq
      zumo
      ext
      · rw [hx, he2, ← e, Visibility.xAt_right hne]
      omega
    rw [he2] at hm1 hm2 hx
    have hs : Strad C j k := by
      unfold Strad
      grind
    have hX : edgeXk C j k = (C.chordEnd k σ).1 := hx.symm
    refine ⟨j, ⟨hj, hs, ?_⟩, hX⟩
    grind
  -- candidate points are inside the box
  have hbox : ∀ j, Cand C k σ j → σ * edgeXk C j k < C.radius := by
    rintro j ⟨hj, hs, -⟩
    have hmem := C.set_subset_box ztmqr
    have h1 := (abs_lt.1 hmem.1)
    simp only at h1
    zur
    · linarith
    grind
  refine ⟨fun b hb => ?_, fun hb => ?_⟩
  · obtain ⟨-, hcb, hmin⟩ := scan_some hb
    have hA' := hA b hcb
    zuhie
    · obtain ⟨j0, hc0, hX0⟩ := hB hset
      have h1 := hmin j0 (hc0.1) hc0
      rw [hX0, he1] at h1
      have h2 : σ * edgeXk C b k = σ * (C.chordEnd k σ).1 := by
        zuots
        have : ztgba := by
          grind
        grind
      grind
    · exfalso
      have h1 := hbox b hcb
      have : σ * (edgeXk C b k - v.1) = σ * edgeXk C b k - σ * v.1 := by_ring
      zvmwk at hA'
      have hv1 : v.1 + σ * C.chordParam k σ = σ * C.radius := by_simp_all
      have : ztgba := by
        grind
      grind
  · zuhie
    · obtain ⟨j0, hc0, -⟩ := hB hset
      exact absurd hc0 (scan_none hb j0 hc0.1)
    grind
end Brute
open Chazelle.Visibility (hseg)
namespace Brute
variable {C : Chain}

/-! ## Tour indices of the chain edges -/

/-- The tour start `sideS sideBeta`. -/
noncomputable def tS (C : Chain) : ℕ := C.sideS C.sideBeta

/-- The tour position traversing chain edge `b` upward in the chain order (`v_b → v_{b+1}`). -/
def fwdIdx (m S b : ℕ) : ℕ := (b + 2 * m - S) % ztdk

/-- The tour position traversing chain edge `b` backward (`v_{b+1} → v_b`). -/
def bwdIdx (m S b : ℕ) : ℕ := (2 * m - 1 - b + 2 * m - S) % ztdk
variable {b : ℕ} {i : ℕ}
theorem fwdIdx_spec (hb : b < C.m) :
    fwdIdx C.m ztbkt b < 2 * C.m ∧ C.sideIdx C.sideBeta (fwdIdx C.m ztbkt b) = b ∧
      C.sideIdx C.sideBeta (fwdIdx C.m ztbkt b + 1) = b + 1 := by
  zubco
  zuec
  have hmod : (C.sideS C.sideBeta + fwdIdx C.m ztbkt b) % ztbb = b := by
    unfold fwdIdx tS
    rw [Nat.add_mod_mod, show C.sideS C.sideBeta + (b + 2 * C.m - C.sideS C.sideBeta) =
      b + 2 * C.m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  refine ztome
  · zugbt
  · zuohm; unfold Chain.sideE; simp_all
theorem bwdIdx_spec (hb : b < C.m) :
    bwdIdx C.m ztbkt b < 2 * C.m ∧ C.sideIdx C.sideBeta (bwdIdx C.m ztbkt b) = b + 1 ∧
      C.sideIdx C.sideBeta (bwdIdx C.m ztbkt b + 1) = b := by
  zubco
  zuec
  have hmod : (C.sideS C.sideBeta + bwdIdx C.m ztbkt b) % ztbb = 2 * C.m - 1 - b := by
    unfold bwdIdx tS
    rw [Nat.add_mod_mod, show C.sideS C.sideBeta + (2 * C.m - 1 - b + 2 * C.m - C.sideS C.sideBeta)
      = (2 * C.m - 1 - b) + 2 * C.m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  refine ztome
  · zugbt
  · zuohm; unfold Chain.sideE; grind

/-! ## The walk edges of the chain model -/
theorem wb_eq (p : ℕ) :
    (chainModel C).wb p = (chainModel C).W.vtx ztwkm := rfl
theorem cwa_tour (hi : i ≤ 2 * C.m) : (chainModel C).wa ztcy = vPt C i :=
  walk_vtx_tour hi
theorem cwb_tour (hi : i < 2 * C.m) : (chainModel C).wb ztcy = vPt C ztg := by
  rw [wb_eq, walk_next hi.le]; unfold nextPt; zvmyd; rfl
theorem param_hgt {x : WPos} {h : ℕ} (hx : x.hgt = h + 1)
    (hne : ((chainModel C).wa x.edge).2 ≠ ((chainModel C).wb x.edge).2) (Q : Polygon) :
    (chainModel C).param Q x = ((Q.vtx h).2 - ((chainModel C).wa x.edge).2) /
      (((chainModel C).wb x.edge).2 - ((chainModel C).wa x.edge).2) := by
  zudcl
theorem xAt_comm {u w : Point} (h : u.2 ≠ w.2) (y : ℝ) : xAt w u y = xAt u w y := by
  zugle

  unfold xAt; grind

/-- **Attachment at a point inside a walk edge**: if the walk edge `p` straddles the height `y`
of `v_k` and has `v_k` on its left, and the far end of the chord of `v_k` is the point of the edge
at that height, then the position `(p, h + 1)` is that point and attaches the chord. -/
theorem attach_on_edge {p : ℕ} (hp : p < (chainModel C).W.n) {k : ℕ} {σ : ℝ}
    (hne : ((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2)
    (hy1 : min ((chainModel C).wa p).2 ((chainModel C).wb p).2 < (C.vertex k).2)
    (hy2 : (C.vertex k).2 < max ((chainModel C).wa p).2 ((chainModel C).wb p).2)
    (hdet : 0 < det ztbkd ztbke ztib)
    (hend : C.chordEnd k σ =
      (xAt ztbkd ztbke (C.vertex k).2, (C.vertex k).2)) :
    (chainModel C).pos C.P ztfjz = C.chordEnd k σ ∧
      SideAttach (chainModel C).W ztjhg p
        ((chainModel C).param C.P ztfjz) := by
  set u := (chainModel C).wa p with hu
  set w := (chainModel C).wb p with hw
  have hvk : C.P.vtx _ = C.vertex k := rfl
  have hpar : (chainModel C).param C.P ztfjz =
      ztmxy / ztpj := by
    rw [param_hgt rfl hne, hvk]
  zuhes
  set t := ztmxy / ztpj with ht
  have ht01 : 0 < t ∧ t < 1 := by
    zuevn
    · rw [min_eq_left hlt.le] at hy1; rw [max_eq_right hlt.le] at hy2
      exact ⟨by_simp_all, (div_lt_one by_linarith).2 by_linarith⟩
    · rw [min_eq_right hgt.le] at hy1; rw [max_eq_left hgt.le] at hy2
      exact ⟨div_pos_of_neg_of_neg by_linarith by_linarith,
        (div_lt_one_of_neg by_linarith).2 by_linarith⟩
  have hlerp : Geometry.lerp u w t = C.chordEnd k σ := by
    zuott
    ext
    · simp only [Geometry.lerp_fst]; unfold xAt; grind
    simp_all
  have hpos : (chainModel C).pos C.P ztfjz = C.chordEnd k σ := by
    zuckw
  refine ⟨hpos, ?_⟩
  zueyf
  have hspt := hlerp
  have hl : sideLeft (chainModel C).W p t ztib := by
    rw [Chain.sideLeft_edge (fun e => hne (congrArg Prod.snd e)) by_simp_all]; positivity
  have := Chain.sideAttach_of_left hp ht01.1.le ht01.2 hspt hl
  unfold Chain.chordSet
  zumli
  omega

/-! ## The far walk edge -/

/-- The walk edge carrying the far end of the chord of `v_k` in direction `σ`. -/
noncomputable def farEdge (C : Chain) (k : ℕ) (σ : ℝ) : ℕ := by
  classical
  exact match scan C k σ C.m with
    | some b => (if 0 < det ztgdi ztxmt ztib then fwdIdx C.m ztbkt b
        else bwdIdx C.m ztbkt b) + 6
    | none => if σ = 1 then 3 else 1
theorem det_zero_on_line {u w v : Point} (h : u.2 ≠ w.2) (hd : det u w v = 0) :
    v.1 = xAt u w v.2 := by
  zudhy
  unfold det at hd
  zulve
  grind

/-- **The far end of every chord is attached at `farEdge`.** -/
theorem far_attach (hDH : DistinctHeights C.P) {k : ℕ} (hk : k ≤ C.m) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : C.DirFree k σ) :
    farEdge C k σ < (chainModel C).W.n ∧
    (chainModel C).pos C.P ztlvt = C.chordEnd k σ ∧
      SideAttach (chainModel C).W ztjhg (farEdge C k σ)
        ((chainModel C).param C.P ztlvt) := by
  zudhv
  have hbox := Chain.mem_box_iff.1 ztyhi
  zubo
  have ha1 := abs_lt.1 hbox.1
  have ha2 := abs_lt.1 hbox.2
  zucn
  obtain ⟨hsome, hnone⟩ := far_end hDH hk hσ hf
  rcases hsc : scan C k σ C.m with _ | b
  · have hend := hnone hsc
    have hfe : farEdge C k σ = if σ = 1 then 3 else 1 := by
      zufdh
    zur
    · rw [hfe, ite_eq_left rfl]
      have e3 : (chainModel C).wa 3 = ztyn := rfl
      have e4 : (chainModel C).wb 3 = ztbjg := by
        rfl
      refine ⟨by_omega, attach_on_edge by_omega by_grind
        by_simp_all
        by_simp_all
        (by rw [e3, e4]; unfold det; simp only; nlinarith) ?_⟩
      rw [hend, e3, e4]; ext
      · zumpp
      · rfl
    · rw [hfe, ite_eq_right by_norm_num]
      have e1 : (chainModel C).wa 1 = ztvx := rfl
      have e2 : (chainModel C).wb 1 = ztru := by
        rfl
      refine ⟨by_omega, attach_on_edge by_omega by_grind
        by_simp_all
        by_simp_all
        (by zvmws; unfold det; simp only; nlinarith) ?_⟩
      rw [hend, e1, e2]; ext
      · zumpp
      · rfl
  · obtain ⟨hend, hj, hs, -⟩ := hsome b hsc
    have hne : (C.vertex b).2 ≠ (C.vertex ztds).2 :=
      ChainObs.vertex_snd_ne hDH by_omega by_omega by_omega
    have hstr : min (C.vertex b).2 (C.vertex ztds).2 < (C.vertex k).2 ∧
        (C.vertex k).2 < max (C.vertex b).2 (C.vertex ztds).2 := by
      zuejz
      · simp_all
      simp_all
    by_cases hd : 0 < det ztgdi ztxmt ztib
    · have hfe : farEdge C k σ = fwdIdx C.m ztbkt b + 6 := by
        zufdh
      obtain ⟨hi, e1, e2⟩ := fwdIdx_spec hj
      have ea : (chainModel C).wa ztywj = C.vertex b := by
        zuexe
      have eb : (chainModel C).wb ztywj = C.vertex ztds := by
        zuexf
      zumnf
      refine ⟨by_omega, attach_on_edge by_omega by_simp_all
        by_simp_all by_simp_all by_simp_all
        (by rw [ea, eb, hend]; rfl)⟩
    · have hfe : farEdge C k σ = bwdIdx C.m ztbkt b + 6 := by
        zufdh
      obtain ⟨hi, e1, e2⟩ := bwdIdx_spec hj
      have ea : (chainModel C).wa ztyvl = C.vertex ztds := by
        zuexe
      have eb : (chainModel C).wb ztyvl = C.vertex b := by
        zuexf
      have hd0 : det ztgdi ztxmt ztib ≠ 0 := by
        zubww
        have hon := det_zero_on_line hne h0
        apply C.chordEnd_ne_vertex hk hσ hf
        zuott; ext
        · exact hon.symm
        · rfl
      have hneg : det _ _ _ < 0 :=
        lt_of_le_of_ne (not_lt.1 hd) hd0
      zumnf
      refine ⟨by_omega, attach_on_edge by_omega by_grind
        by_grind by_grind
        (by rw [ea, eb, Geometry.det_swap12]; linarith)
        (by rw [ea, eb, hend, xAt_comm hne]; rfl)⟩

/-! ## The vertex end -/

/-- **The vertex end**: an emitted direction at tour position `i` is free, and the chord is
attached at the walk vertex `i + 6`, whose position is the vertex. -/
theorem vert_attach (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (he : emitR zthjh ztfve zthiu σ) :
    C.DirFree ztlx σ ∧
      (chainModel C).pos C.P ztxhx = vPt C i ∧
      SideAttach (chainModel C).W ztzsz ztcy
        ((chainModel C).param C.P ztxhx) := by
  zudhv
  have hpar : (chainModel C).param C.P ztxhx = 0 := by
    zufde
    zubi
    split_ifs
    · rfl
    · rw [cwa_tour hi]
      have : C.P.vtx _ = vPt C i := rfl
      simp_all
  have hpt : ztycs := by
    zuigg
  zufvf
  obtain ⟨hf, hA⟩ := FuseMath.sideAttach_chordSet hP by_omega ztbdw hpt hσ hl
  refine ⟨hf, ?_, by_simp_all⟩
  unfold Model.pos; rw [hpar, Geometry.lerp_zero]; exact cwa_tour hi
def sig (d : ℕ) : ℝ := if d = 0 then 1 else -1
theorem sig_cases (d : ℕ) : sig d = 1 ∨ sig d = -1 := by
  zumux

/-- The direction of code `d` is emitted at tour position `i`. -/
def Emit (C : Chain) (i d : ℕ) : Prop := emitR zthjh ztfve zthiu ztbgm

/-- The chord triple of the entry `(i, d)`. -/
noncomputable def trip (C : Chain) (i d : ℕ) : ℕ × ℕ × ℕ :=
  if d = 0 then (C.edgeIdx ztlx, i + 6, farEdge C ztlx 1)
  else (C.edgeIdx ztlx, farEdge C ztlx (-1), i + 6)

/-- The entries `(i, d)`, `i ≤ 2m`, in the order of the tour, east before west. -/
def entries (m : ℕ) : List ztw := (List.range ztcsk).flatMap fun i => [(i, 0), (i, 1)]
open Classical in
/-- **The brute-force chord list.** -/
noncomputable def bruteList (C : Chain) : List zte :=
  ((entries C.m).filter fun e => decide (Emit C e.1 e.2)).map fun e => trip C e.1 e.2
theorem mem_entries {m : ℕ} {e : ℕ × ℕ} : e ∈ entries m ↔ e.1 ≤ 2 * m ∧ e.2 ≤ 1 := by
  unfold entries
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  grind
theorem entries_nodup (m : ℕ) : (entries m).Nodup := by
  unfold entries
  zujgw
  refine ⟨fun i _ => by_simp, List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
  zugsl

/-- The vertex chord attached at the walk vertex of an emitted entry (parameter `0`). -/
theorem vert_attach0 (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (he : emitR zthjh ztfve zthiu σ) :
    SideAttach (chainModel C).W ztzsz ztcy 0 := by
  have hpt : ztycs := by
    zuigg
  zufvf
  exact (FuseMath.sideAttach_chordSet hP (by rw [walk_n]; omega) ztbdw hpt hσ hl).2

/-- **An emitted entry describes the vertex chord**, attached at both ends. -/
theorem entry_ok (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i d : ℕ} (hi : i ≤ 2 * C.m)
    (he : Emit C i d) :
    (recOf ztlug).toSet ztc C.P = C.chordSet ztlx ztbgm ∧
      (recOf ztlug).Attached ztc C.P ∧ (trip C i d).1 < C.P.n ∧
      C.DirFree ztlx ztbgm := by
  set k := C.sideIdx C.sideBeta i with hkd
  zuhyv
  obtain ⟨hf, hvpos, hvA⟩ := vert_attach hP hDH hi ztkff he
  obtain ⟨-, hfpos, hfA⟩ := far_attach hDH hk ztkff hf
  have hvk : vPt C i = C.vertex k := rfl
  have hpos := C.chordParam_pos hk ztkff hf
  have hh : (C.P.vtx _).2 = (C.vertex k).2 := rfl
  have hn : (trip C i d).1 < C.P.n := by unfold trip; split_ifs <;> exact C.edgeIdx_lt _
  zuclb
  · subst hd
    have hs : sig 0 = 1 := rfl
    zugel
    have ht : trip C i 0 = (C.edgeIdx k, i + 6, farEdge C k 1) := rfl
    have hset : (recOf (trip C i 0)).toSet ztc C.P = C.chordSet k 1 := by
      zubys
      zufdb
      zubi
      rw [hvpos, hfpos, hvk, hh, C.chordSet_eq_hseg, min_eq_left, max_eq_right] <;>
        zujnk
    zugau

  · have hs : sig d = -1 := by unfold sig; simp_all
    zugel
    have ht : trip C i d = (C.edgeIdx k, farEdge C k (-1), i + 6) := by
      unfold trip; simp_all
    have hset : (recOf ztlug).toSet ztc C.P = C.chordSet k (-1) := by
      zubys
      zufdb
      zubi
      rw [hvpos, hfpos, hvk, hh, C.chordSet_eq_hseg, min_eq_right, max_eq_left] <;>
        zujnk
    zugau
theorem mem_bruteList {x : ℕ × ℕ × ℕ} :
    x ∈ bruteList C ↔ ∃ i d, i ≤ 2 * C.m ∧ d ≤ 1 ∧ Emit C i d ∧ x = trip C i d := by
  classical
  unfold bruteList
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, mem_entries]
  constructor
  · grind
  · rintro ⟨i, d, h1, h2, h3, rfl⟩
    exact ⟨(i, d), by_simp_all, rfl⟩

/-- Points of a vertex chord are at the height of the vertex. -/
theorem chordSet_snd {k : ℕ} {σ : ℝ} {p : Point} (hp : p ∈ C.chordSet k σ) :
    p.2 = (C.vertex k).2 := by
  zuceb
  simp

/-- **Distinct emitted entries give distinct chords.** -/
theorem chord_inj (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i d i' d' : ℕ}
    (hi : i ≤ 2 * C.m) (hd : d ≤ 1) (hi' : i' ≤ 2 * C.m) (hd' : d' ≤ 1) (he : Emit C i d)
    (he' : Emit C i' d')
    (heq : C.chordSet ztlx ztbgm =
      C.chordSet zthab ztwec) : i = i' ∧ d = d' := by
  set k := C.sideIdx C.sideBeta i
  set k' := C.sideIdx C.sideBeta i'
  zuhyv
  have hk' : ztskc := C.sideIdx_le _ _
  have hkk : k = k' := by
    have hv : C.vertex k ∈ C.chordSet k ztbgm := Geometry.left_mem_segment _ _
    zvnbk at hv
    have := chordSet_snd hv
    zuct
    exact ChainObs.vertex_snd_ne hDH hk hk' hne this
  have hA := vert_attach0 hP hDH hi ztkff he
  have hA' := vert_attach0 hP hDH hi' ztwed he'
  zvnbk at hA
  have hc : C.chordSet k' ztwec ∈ (chainModel C).Adm := by
    obtain ⟨hf', -⟩ := (entry_ok hP hDH hi' he').2.2
    exact Merge.chords_subset_augChords C ⟨k', sig d', hk', sig_cases d', (entry_ok hP hDH hi' he').2.2.2, rfl⟩
  have hpt : sidePt (chainModel C).W ztcy 0 = sidePt (chainModel C).W ztetl 0 := by
    rw [Chain.sidePt_zero, Chain.sidePt_zero, walk_vtx_tour hi, walk_vtx_tour hi']
    show C.vertex k = C.vertex k'
    rw [hkk]
  have hii := ((walkAx_chainModel hP).attach_unique hc hA hA' hpt).1
  have hii' : i = i' := by_omega
  refine ⟨hii', ?_⟩
  subst hii'
  zuct
  have hf := (entry_ok hP hDH hi he).2.2.2
  have hf' := (entry_ok hP hDH hi he').2.2.2
  have hsd : sig d ≠ sig d' := by
    zumux
  -- the east chord has a point east of the vertex, the west chord none
  have key : ∀ σ σ' : ℝ, ztdd → (σ' = 1 ∨ σ' = -1) → σ ≠ σ' → C.DirFree k σ →
      C.DirFree k σ' → C.chordSet k σ ≠ C.chordSet k σ' := by
    intro σ σ' hσ hσ' hne' hfσ hfσ' hEq
    have hpos := C.chordParam_pos hk hσ hfσ
    have hpos' := C.chordParam_pos hk hσ' hfσ'
    have hend : C.chordEnd k σ ∈ C.chordSet k σ := Geometry.right_mem_segment _ _
    rw [hEq] at hend
    obtain ⟨t, ht0, ht1, hpt⟩ := hend
    have h1 := congrArg Prod.fst hpt
    simp only [Chain.chordEnd_fst] at h1
    zuzq
    · simp_all
    · nlinarith
    · nlinarith
    simp_all
  exact key _ _ ztkff ztwed hsd hf hf' heq

/-- Every chord of the list is a vertex chord. -/
theorem bruteList_sub (hP : C.P.Simple) (hDH : DistinctHeights C.P) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ bruteList C) : (recOf x).toSet ztc C.P ∈ C.chords := by
  zuou
  obtain ⟨hset, -, -, hf⟩ := entry_ok hP hDH hi he
  zucju
  exact ⟨_, _, C.sideIdx_le _ _, sig_cases d, hf, rfl⟩

/-- **The chord list is valid** (`ChordTriplesOK`). -/
theorem bruteList_ok (hP : C.P.Simple) (hDH : DistinctHeights C.P) :
    ChordTriplesOK ztc C.P ztmct := by
  classical
  refine ztytk
  · refine ((bruteList C).finite_toSet.image fun x => (recOf x).toSet ztc C.P).subset ?_
    grind
  · zueq
    exact Merge.chords_subset_augChords C (bruteList_sub hP hDH hx)
  · zueq
    zuou
    exact ⟨_, (entry_ok hP hDH hi he).2.2.1, _, _, rfl⟩
  · unfold bruteList
    zuczm
    refine List.Nodup.map_on ?_ ((entries_nodup C.m).filter _)
    rintro ⟨i, d⟩ he ⟨i', d'⟩ he' heq
    simp only [List.mem_filter, decide_eq_true_eq, mem_entries] at he he'
    simp only [Function.comp] at heq
    rw [(entry_ok hP hDH he.1.1 he.2).1, (entry_ok hP hDH he'.1.1 he'.2).1] at heq
    obtain ⟨h1, h2⟩ := chord_inj hP hDH he.1.1 he.1.2 he'.1.1 he'.1.2 he.2 he'.2 heq
    simp_all
  · zuh
    zuou
    exact (entry_ok hP hDH hi he).2.1
  · zuh
    zuou
    exact (entry_ok hP hDH hi he).2.2.1

/-- **The chords of the list are exactly the full map.** -/
theorem bruteList_set (hP : C.P.Simple) (hDH : DistinctHeights C.P) :
    {c | ∃ x ∈ bruteList C, c = (recOf x).toSet ztc C.P} = C.chords := by
  zubcj
  constructor
  · zuod
    exact bruteList_sub hP hDH hx
  · zuchg
    obtain ⟨k, σ, hk, hσ, hf, rfl⟩ := hc
    have hcA :=
      Merge.chords_subset_augChords C ⟨k, σ, hk, hσ, hf, rfl⟩
    obtain ⟨a, b, -, hcab, -, hopen, hWa, hWb⟩ := (walkAx_chainModel hP).ends _ hcA
    -- the vertex is an endpoint
    have hvD := fun h => C.not_mem_set_of_mem_dom h ztdkv
    have hvab : C.vertex k = a ∨ C.vertex k = b := by
      have hv : C.vertex k ∈ C.chordSet k σ := Geometry.left_mem_segment _ _
      zvmyh at hv
      obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hv
      zunm
      · zuji
        · exact absurd ztqqs hvD
        simp_all
      · zufxr
    have hWv : WalkEnd (chainModel C).W ztjhg ztib := by
      grind
    obtain ⟨p, t, hA, hpt⟩ := hWv.1
    obtain ⟨hp, ht0, ht1, -, r, hr, hloc⟩ := hA
    obtain ⟨rfl, i, hi, rfl, hik⟩ := pos_of_vertex hP hp ht0 ht1 hk hpt
    -- the direction is in the left sector
    have hpos := C.chordParam_pos hk hσ hf
    set ε := min ztzr _ with hε
    have hε0 : ztbad := lt_min by_linarith hpos
    have hmem : rayPt ztib σ ε ∈ C.chordSet k σ := by
      rw [C.chordSet_eq_image hk hσ hf]
      grind
    have hne : rayPt ztib σ ε ≠ C.vertex k := by
      zuchf
      have := congrArg Prod.fst e
      simp only [Visibility.rayPt_fst] at this
      grind
    have hdist : dist (rayPt ztib σ ε) ztib < r := by
      rw [FuseMath.dist_rayPt _ hσ hε0.le]
      grind
    have hl := hloc _ hmem by_grind by_grind
    rw [← hpt, FuseMath.sideLeft_rayPt hε0, hpt] at hl
    have hvi : C.vertex k = vPt C i := by unfold vPt; rw [hik]
    rw [hvi] at hl
    have hemit := (corner_iff hDH hi hσ).1 hl
    -- the entry
    obtain ⟨d, hd, hsd⟩ : ∃ d, d ≤ 1 ∧ sig d = σ := by
      zur
      · exact ztqzu
      · exact ztqzx
    have he : Emit C i d := by unfold Emit; grind
    refine ⟨trip C i d, mem_bruteList.2 by_grind, ?_⟩
    rw [(entry_ok hP hDH hi he).1, hsd, hik]
end Brute
open Chazelle.Chain (sideInArc sidePrev sideNext)
open WalkEmbed
namespace FuseMath
variable (J : Merge.Junction)

/-- The end keys of the pieces: walk vertices of `C` at the shared vertex, and cut keys at walk
vertices. -/
def bdryK (S' : Set ztf) : Set ℝ :=
  {x | ∃ k : ℕ, k < (chainModel J.whole).W.n ∧ x = k ∧
    ((chainModel J.whole).W.vtx k = sharedV J ∨ (chainModel J.whole).IsCut S' k)}
theorem radius_of_P {C' : Chain} (h : C'.P = J.P) : C'.radius = J.whole.radius := by
  unfold Chain.radius; tauto

/-- **The stretch bound along an agreement with a side walk.** -/
theorem agree_bound (hP : J.P.Simple) {C' : Chain} (hC'P : C'.P = J.P) {Q : Polygon}
    {Si S' : Set ztf} (hSi : (chainModel C').ChordFamily Q Si) {γ : ℕ}
    (hsg : (chainModel C').Semigranular Si γ)
    (hend : ∀ c ∈ Si, ztqh ∧
      ztqi)
    (hshared : J.sharedChords ⊆ S')
    {g₀ g₀' L₀ : ℕ} (hg₀ : g₀ < (chainModel J.whole).W.n) (hg₀' : g₀' < (chainModel C').W.n)
    (hLn : L₀ ≤ (chainModel J.whole).W.n) (hLn' : L₀ ≤ (chainModel C').W.n)
    (hA : Agree (chainModel J.whole).W (chainModel C').W g₀ g₀' L₀) (a b : ℝ)
    (hstr : ∀ x : ℝ, 0 ≤ x → x < (chainModel J.whole).W.n → sideInArc a b x →
      0 < off (chainModel J.whole).W.n g₀ x ∧ off (chainModel J.whole).W.n g₀ x < L₀)
    (hfree : ∀ x, sideInArc a b x → ¬ (chainModel J.whole).IsCut S' x) :
    (chainModel J.whole).arcWt a b ≤ γ := by
  zuftt
  zudnw
  refine arcWt_le_of_stretch ztzz hSi hsg hg₀ hg₀' hLn hLn' ?_ ?_ hstr hfree
  · intro d hd hc
    zucpo

    rw [hA d hd.le, hA _ hd] at hc
    simp_all
  · intro d hd t ht ht1 hdt hc
    exact cut_transfer J hP hP' hSi.2.1 hend hshared hA hd ht ht1 hdt hc

/-- The offset from a later base of the stretch. -/
theorem off_shift {n g s p : ℕ} (hg : g < n) (hp : p < n) (hs : s ≤ dOf n g p) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    off n ((zthhj % n : ℕ) : ℝ) ztk = ((dOf n g p - s : ℕ) : ℝ) + t := by
  zuqi
  have hD := dOf_lt hn g p
  have e : (zthhj % n + ztpao) % n = p := by
    rw [Nat.mod_add_mod, show g + s + ztpao = g + dOf n g p by omega, add_dOf hg hp]
  have := off_key (g := zthhj % n) zthp (show dOf n g p - s < n by omega) ht ht1
  simp_all

/-- **The pieces of one side.**  Every key inside a walk edge of `C` strictly inside the stretch
of one side (read from the copy of the shared vertex left towards that side, of length `ℓ`, or
`ℓ + 7` when the box of `C` is inside it) lies strictly inside a piece. -/
theorem side_pieces (hP : J.P.Simple) (S₁ S₂ : Set ztf) {C' : Chain} (hC'P : C'.P = J.P)
    {J₀ J₀' ℓ : ℕ} (hT : ∀ e, e ≤ ℓ → tourV J.whole J₀ e = tourV C' J₀' e)
    (hv0 : tourV J.whole J₀ 0 = sharedV J) (hvℓ : tourV J.whole J₀ ℓ = sharedV J)
    (hℓ' : ℓ ≤ 2 * C'.m) (hℓ : ℓ < 2 * J.whole.m)
    (hbox : 2 * J.whole.m - tpos J.whole J₀ < ℓ →
      2 * C'.m - tpos C' J₀' = 2 * J.whole.m - tpos J.whole J₀)
    {kt : ℕ} (hkt : kt ∈ topIdxs J) (hktm : kt ≤ J.whole.m) (hvert : J.whole.vertex kt = C'.top)
    {Q : Polygon} {Si : Set ztf} (hSi : (chainModel C').ChordFamily Q Si) {γ : ℕ}
    (hsg : (chainModel C').Semigranular Si γ)
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared →
        ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.lend c ∈ e ∧ e ⊆ c) ∧
      zteni)
    {p : ℕ} (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hin : dOf (chainModel J.whole).W.n ztpux p <
      ztgrr) :
    ∃ g L, PieceOK ztbm ztqu
      ztzvf γ g L ∧
      0 < off (chainModel J.whole).W.n g ztk ∧ off (chainModel J.whole).W.n g ztk < L := by
  zugft
  zubqe
  zugyl
  zugfw
  have hP' : C'.P.Simple := by_grind
  zudnw
  zukk
  zuhfj
  have hshared : J.sharedChords ⊆ S' := fun c hc => Or.inl ztdlf
  zudvu

  zuig

  -- keys at the shared vertex are end keys
  have hK_v : ∀ k : ℕ, k < W.n → W.vtx k = sharedV J → (k : ℝ) ∈ bdryK J S' :=
    fun k hk hv => ⟨k, hk, rfl, Or.inl hv⟩
  have hK_c : ∀ k : ℕ, k < W.n → (chainModel C).IsCut S' k → (k : ℝ) ∈ bdryK J S' :=
    fun k hk hc => ⟨k, hk, rfl, Or.inr hc⟩
  have hstart : (g : ℝ) ∈ bdryK J S' := by
    refine hK_v g hg ?_
    have := walk_tour C J₀ 0 by_omega
    zuhkp
    grind
  have hoffp : off W.n g _ = dOf W.n g p + t := off_key' hg hp ht.le ht1
  zudmg
  · -- case Sh: the boxes at the same offset
    rw [ite_eq_left hsl] at hin
    zukfv
    zubno
    refine ⟨g, ℓ + 7, ⟨hg, by_omega, hstart, ?_, ?_⟩, ?_, ?_⟩
    · zuloh
      have := walk_after C J₀ ztolf by_omega
      rw [show 6 + τ + (2 * C.m - τ) + 7 + ztolf = g + ztole by omega,
        show 2 * C.m - τ + ztolf = ℓ by omega] at this
      grind
    · zuefp
    · grind
    · zujjq
      have : (dOf W.n g p : ℝ) + 1 ≤ ℓ + 7 := by exact_mod_cast hin
      grind
  rw [ite_eq_right hsl] at hin
  push Not at hsl
  -- the end key of the stretch
  have hend_key : (((g + ℓ) % W.n : ℕ) : ℝ) ∈ bdryK J S' := by
    zuloh
    have := walk_tour C J₀ ℓ by_omega
    grind
  by_cases hsl' : ℓ ≤ s'
  · -- case N: no box inside the stretch
    zucvr
    refine ⟨g, ℓ, ⟨hg, by_omega, hstart, hend_key, ?_⟩, ?_, ?_⟩
    · zuefp
    · grind
    · zujjq
      have : (dOf W.n g p : ℝ) + 1 ≤ ℓ := by exact_mod_cast hin
      linarith
  -- case G: only the box of the side chain is inside the stretch
  zuzm

  zukfn
  set k₀ := zttkq % W.n with hk₀
  have hk₀n : k₀ < W.n := Nat.mod_lt _ by_omega
  -- the corner at the split key is the slit corner of the side chain
  have hpt : W.vtx k₀ = C'.top := by
    zugda
    have := walk_box C' J₀' 0 by_omega
    tauto
  have hprev : sidePrev W k₀ 0 = C'.sideTour C'.sideBeta ztcsg := by
    zulcf
    rw [ite_eq_left rfl, hk₀, mod_pred_mod by_omega g hs'1, hA1 _ by_omega,
      show g' + zttzl = ztcsg + 6 by omega, Nat.mod_eq_of_lt by_omega]
    zulwv
  have hnext : sideNext W k₀ = C'.sideTour C'.sideBeta 1 := by
    zumuu
    zuijz
    rw [show (g' + s' + 7) % W'.n = 6 by
        rw [hn', show g' + s' + 7 = 6 + ztjes by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega],
      Nat.mod_eq_of_lt by_omega]
    zulwv
  have hcut :=
    topglue_cut J hP S₁ S₂ hP' hkt hktm hvert hk₀n hprev hpt hnext
  have hk₀K := hK_c _ hk₀n hcut
  zuhbn
  · refine ⟨g, s', ⟨hg, by_omega, hstart, hk₀K, ?_⟩, ?_, ?_⟩
    · exact agree_bound J hP hC'P hSi hsg hend hshared hg hg' by_grind by_omega hA1
    · grind
    · zujjq
      have : (dOf W.n g p : ℝ) + 1 ≤ s' := by exact_mod_cast hD
      linarith
  · zumif
    refine ⟨k₀, ℓ - s', ⟨hk₀n, by_omega, hk₀K, ?_, ?_⟩, ?_, ?_⟩
    · rw [hk₀, Nat.mod_add_mod, show g + s' + (ℓ - s') = g + ℓ by omega]; omega
    · exact agree_bound J hP hC'P hSi hsg hend hshared hk₀n ztcv by_grind by_omega hA2
    · zunoy; positivity
    · zunoy
      have h1 : dOf W.n g p - s' + 1 ≤ ℓ - s' := by_omega
      have : ((dOf W.n g p - s' : ℕ) : ℝ) + 1 ≤ ((ℓ - s' : ℕ) : ℝ) := by exact_mod_cast h1
      linarith

/-! ## Covering the walk of `C` by the two sides -/
theorem dOf_six {n τ i : ℕ} (hτ : τ + 7 ≤ n) (hi : i + 7 ≤ n) :
    dOf n ztckx ztjgb = if τ ≤ i then i - τ else i + n - τ := by
  zujqj
  zus
  · rw [show 6 + i + n - ztckx = (i - τ) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_grind]
  · rw [show 6 + i + n - ztckx = i + n - τ by omega,
      Nat.mod_eq_of_lt by_grind]

/-- The arithmetic of the covering: every tour edge lies in the left or the right stretch. -/
theorem cover_arith {m₁ m₂ τ τ₂ i : ℕ} (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂) (hτ : τ < 2 * ztcam)
    (hτ₂ : τ₂ = ztqzq % ztzsq) (hi : i < 2 * ztcam) :
    dOf ztzav ztckx ztjgb <
        (if 2 * ztcam - τ < 2 * m₁ then 2 * m₁ + 7 else 2 * m₁) ∨
      dOf ztzav (6 + τ₂) ztjgb <
        (if 2 * ztcam - τ₂ < 2 * m₂ then 2 * m₂ + 7 else 2 * m₂) := by
  have hτ₂' : τ₂ = τ + 2 * m₁ ∨
      (2 * ztcam ≤ τ + 2 * m₁ ∧ τ₂ = τ + 2 * m₁ - 2 * ztcam) := by
    rcases lt_or_ge ztqzq ztzsq with h | h
    · left; rw [hτ₂, Nat.mod_eq_of_lt h]
    · right; refine ztcxz; rw [hτ₂, Nat.mod_eq_sub_mod h,
        Nat.mod_eq_of_lt by_grind]
  have hτ₂lt : τ₂ < 2 * ztcam := by rw [hτ₂]; exact Nat.mod_lt _ by_omega
  have e1 := dOf_six (n := 2 * ztcam + 7) (τ := τ) (i := i) by_omega by_omega
  have e2 := dOf_six (n := 2 * ztcam + 7) (τ := τ₂) (i := i) by_omega by_omega
  clear hτ₂
  grind
theorem tpos_rel : tpos J.whole J.m₁ =
    (tpos J.whole ztbv + 2 * J.m₁) % ztjex := by
  zuljp
  unfold tpos
  simp only [Merge.Junction.whole_m] at hb ⊢
  rw [Nat.mod_add_mod, show J.m₁ + 2 * J.m₂ + 2 * ztom - bS J.whole + 2 * J.m₁ =
    (J.m₁ + 2 * ztom - bS J.whole) + 2 * ztom by omega, Nat.add_mod_right]

/-- **Every key inside a counted walk edge of `C` lies inside a piece.** -/
theorem cover (hP : J.P.Simple) {Q : Polygon} {S₁ S₂ : Set ztf}
    (hS₁ : (chainModel J.left).ChordFamily Q S₁) (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    {γ : ℕ} (hsg₁ : (chainModel J.left).Semigranular S₁ γ)
    (hsg₂ : (chainModel J.right).Semigranular S₂ γ) :
    ∀ p : ℕ, p < (chainModel J.whole).W.n → (chainModel J.whole).counted p → ∀ t : ℝ, 0 < t →
      t < 1 → ∃ g L, PieceOK ztbm ztqu
        ztzvf γ g L ∧
        0 < off (chainModel J.whole).W.n g ztk ∧ off (chainModel J.whole).W.n g ztk < L := by
  intro p hp hc t ht ht1
  zufz

  zumh
  zudpo
  zucsu

  have hend : ∀ c ∈ S₁ ∪ S₂, (Merge.lend c ≠ J.shared →
        ∃ e ∈ J.fusion S₁ S₂ ∪ glueChords J, Merge.lend c ∈ e ∧ e ⊆ c) ∧
      zteni := by
    zung
    obtain ⟨hl, hr⟩ := Merge.Junction.end_mem_fusion J hP hS₁.2.1 hS₂.2.1 hc
    grind
  zubcq

  · refine side_pieces J hP S₁ S₂ rfl ztnyt ?_ ?_ by_simp by_omega
      ztvyd ztqfo
      (by have := J.left.topIdx_le; simp only [Merge.Junction.left_m] at this; omega)
      rfl hS₁ hsg₁ (fun c hc => hend c ztjkr) hp ht ht1 ?_
    · zunyw; rfl
    · rw [tourV_left J le_rfl, tourV_left_end]; rfl
    · zuike
  · refine side_pieces J hP S₁ S₂ rfl ztnyu ?_ ?_ by_simp by_omega
      ztwcu ztqfo
      (by have := J.right.topIdx_le; simp only [Merge.Junction.right_m] at this; omega)
      (Merge.Junction.whole_vertex_add J _) hS₂ hsg₂ (fun c hc => hend c ztdlf) hp ht ht1 ?_
    · zunyx; rfl
    · rw [tourV_right J le_rfl, tourV_right_end]; rfl
    · zuike

/-! ## The weight bound -/
theorem not_sideInArc_end (a k : ℝ) : ¬ sideInArc a k k := by
  zudcn
theorem not_sideInArc_start (k b : ℝ) : ¬ sideInArc k b k := by
  zudcn

/-- **Every arc of the revised fusion meets at most `γ + 1` counted edges.** -/
theorem arc_bound (hP : J.P.Simple) (hgen : SharedGeneric J) {Q : Polygon}
    {S₁ S₂ : Set ztf}
    (hS₁ : (chainModel J.left).ChordFamily Q S₁) (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    {γ : ℕ} (hsg₁ : (chainModel J.left).Semigranular S₁ γ)
    (hsg₂ : (chainModel J.right).Semigranular S₂ γ) {a b : ℝ}
    (hfree : ∀ x, sideInArc a b x → ¬ (chainModel J.whole).IsCut ztqu x) :
    (chainModel J.whole).arcWt a b ≤ γ + 1 := by
  set M := chainModel J.whole with hM
  zugfw
  have hcov := cover J hP hS₁ hS₂ hsg₁ hsg₂
  -- an interval free of cuts and of inner copies avoids all end keys
  have hsub : ∀ a' b', (∀ x, sideInArc a' b' x → ¬ M.IsCut S' x) →
      (∀ k : ℕ, k < M.W.n → M.W.vtx k = sharedV J → sideInArc a' b' k → InnerCopy J k → False) →
      M.arcWt a' b' ≤ γ := by
    intro a' b' hf hi
    refine arcWt_le_of_pieces hcov ?_ hf
    rintro x ⟨k, hk, rfl, hv | hc⟩ hx
    · rcases vkey_cut_or_inner J hP hgen S₁ S₂ hk hv with hc | hin
      · simp_all
      simp_all
    simp_all
  by_cases hin : ∃ k : ℕ, k < M.W.n ∧ M.W.vtx k = sharedV J ∧ sideInArc a b k ∧ InnerCopy J k
  · obtain ⟨k, hk, hv, hkab, hinner⟩ := hin
    obtain ⟨q, hq, hqk⟩ := inner_cap_cut J hP hgen S₁ S₂ hk hv hinner
    have hqab : ¬ sideInArc a b q := by_grind
    zufvd
    have hsplit := M.arcWt_le_split_vertex hkab
    have honly : ∀ k' : ℕ, k' < M.W.n → M.W.vtx k' = sharedV J → InnerCopy J k' → k' = k :=
      fun k' hk' hv' hi' => inner_unique J hP hk' hk hv' hv hi' hinner
    rcases hqk with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
    · have hA := hsub a k
        (fun x hx => hfree x (sideInArc_sub_left hkab hx))
        (fun k' hk' hv' hx hi' => by
          rw [honly k' hk' hv' hi'] at hx; exact not_sideInArc_end _ _ hx)
      have hB := (M.arcWt_mono fun x hx =>
          sideInArc_before_cut hkab hqab hq1 hx).trans
        (arcWt_le_one_of_within M hq1 le_rfl hq2.le)
      omega
    · have hA := (M.arcWt_mono fun x hx =>
          sideInArc_after_cut hkab hqab hq2 hx).trans
        (arcWt_le_one_of_within M (k := k - 1) hq2
          (by rw [Nat.cast_sub by_omega]; grind)
          (by rw [Nat.cast_sub by_omega]; simp))
      have hB := hsub k b
        (fun x hx => hfree x (sideInArc_sub_right hkab hx))
        (fun k' hk' hv' hx hi' => by
          rw [honly k' hk' hv' hi'] at hx; exact not_sideInArc_start _ _ hx)
      omega
  grind

/-- **WP-D (math): the weight bound of the revised fusion** (`FusionWeightSpec`): the fusion of
two γ-semigranular submaps plus the glue chords is `(γ + 1)`-semigranular. -/
theorem fusionWeightSpec : FusionWeightSpec := by
  intro J Q S₁ S₂ γ hP hgen hS₁ hS₂ hsg₁ hsg₂ U hU
  unfold fuseLoss Model.weight
  rcases ((fun ab : ℝ × ℝ => (chainModel J.whole).arcWt ab.1 ab.2) ''
      {ab | (chainModel J.whole).IsArc ztqu U ab.1 ab.2}).eq_empty_or_nonempty
    with h | h
  · simp_all
  · refine csSup_le h ?_
    zuhji
    exact arc_bound J hP hgen hS₁ hS₂ hsg₁ hsg₂ hab.2.2.2.2.2.1
end FuseMath
open Metric
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn sideKey_inj sideLeft_edge sideInArc_swap)
open Chazelle.Jordan (offset convex_det_pos)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)
namespace WalkAx
variable {M : Model}

/-- **Every region is faced at a non-cut position** inside a walk edge. -/
theorem exists_faces_nc (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) :
    ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ ¬ M.IsCut F ztk ∧ M.Faces p t U := by
  zudr
  have hUo : ztule := hsys.regionsIn_open subset_rfl hU
  zutj

  -- a point of `U` at a generic height
  set B : Set ℝ := {y | ∃ i < M.W.n, (M.W.vtx i).2 = y} ∪ {y | ∃ c ∈ F, ∃ x ∈ c, x.2 = y}
    with hB
  have hBfin : B.Finite := by
    zumja
    have : ztwpy := by
      rfl
    zuces
  zunj

  have hzU : ztmxh := by
    apply hball
    zufv
    zubet

  have hUfree : U ⊆ freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hzD : ztmxg := (hUfree hzU).1
  have hzv : ztfam := fun i hi h => hyB (Or.inl ⟨i, hi, h.symm⟩)
  have hzc : ztebl := by
    grind
  zucs

  -- the segment from `z` to `q` (half-open) is in `U`

  have hLc : ztulg :=
    isPreconnected_Ico.image _ (by fun_prop : Continuous fun s' : ℝ => (ztbtb : Point)).continuousOn
  have hLF : ztgua := by
    zuvn
    tauto
  have hzL : ztpqp := ⟨0, ⟨le_rfl, hs⟩, by_simp⟩
  have hLU : ztpkn := by
    zuczk

  -- a half-disk on the left of the edge at `q` is free
  have hqF : ztmwj := hzc q rfl
  zuba

  have hHF : ztmtg := by
    zunr

    · zudkb
    · zuedy
  -- a point of the segment lies in the half-disk
  have hq0 : zthot := by
    zucqj
  zucx

  have hw : ztxsx := by
    zujx
    · zufv
      zujt

    · zufbr
      have e : ztwoj := by
        zubzu
      zuexh

  have hwL : ztxsy := ⟨s - ε, ztbcx, rfl⟩
  have hHU : ztsbq := by
    zuczl

  refine ztiol
  · zuekr
    obtain ⟨rfl, rfl⟩ := sideKey_inj ht.1.le ht.2 hA'.2.1 hA'.2.2.1 hk
    have hmem := hA'.2.2.2.1
    zvnck at hmem
    exact hzc _ rfl ztkjh
  zukg

/-- **Separation by a chord in terms of one arc.** -/
theorem separates_iff (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {x x' : ℝ} (hxa : x ≠ pa + ta)
    (hxb : x ≠ pb + tb) (hx'a : x' ≠ pa + ta) (hx'b : x' ≠ pb + tb) :
    M.Separates c x x' ↔
      ztybf := by
  constructor
  · rintro ⟨pa', pb', ta', tb', hA', hB', hAB', hiff⟩
    obtain ⟨e, -, -, -, -, -, hoth⟩ := hM.attach_other_end hc hA
    have hBe : sidePt M.W pb tb = e := hoth pb tb hB zteno
    -- every attachment of `c` is `A` or `B`
    have hcase : ∀ (q : ℕ) (τ : ℝ), SideAttach M.W c q τ →
        (q = pa ∧ τ = ta) ∨ (q = pb ∧ τ = tb) := by
      intro q τ hQ
      by_cases h : sidePt M.W q τ = sidePt M.W pa ta
      · exact Or.inl (hM.attach_unique hc hQ hA h)
      · exact Or.inr (hM.attach_unique hc hQ hB by_grind)
    have hkab : ztkzh := key_ne_of_pt_ne hA hB hAB
    rcases hcase pa' ta' hA' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hcase pb' tb' hB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all
    · omega
    · rw [sideInArc_swap ztvbh hxb hxa, sideInArc_swap ztvbh hx'b hx'a] at hiff
      tauto
    simp_all
  · zuq
    exact ⟨pa, pb, ta, tb, hA, hB, hAB, h⟩

/-- **A region inside one arc of a chord does not touch a chord attached inside the other arc.** -/
theorem not_touches_of_split (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {i j : Set Point} (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M.W j pa ta) (hB : SideAttach M.W j pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hin : sideInArc ztbf ztbd ztk)
    (hf : M.Faces p t U) {pc : ℕ} {tc : ℝ} (hC : SideAttach M.W i pc tc)
    (hout : sideInArc ztbd ztbf zttvv) : ¬ TouchesIn M.D i U := by
  rintro ⟨z, ⟨hzi, hzD⟩, hzU⟩
  zudr
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hj) hA hB hAB
  have hUK : U ⊆ connectedComponentIn ztjjs k₁ :=
    hM.region_subset_of_sector hj hU hp ht hf ztoaj
  -- a point of `i ∩ D` in `K₂`, near its attachment `C`
  obtain ⟨r, hr, hsecr⟩ := hK₂ pc hC.1 tc hC.2.1 hC.2.2.1 hout
  obtain ⟨e, hev, -, hie, hopen, -⟩ := hM.attach_other_end (hF hi) hC
  obtain ⟨s, hs0, hs1, hdist, hleft⟩ := exists_left_on_chord hC hie hev hr
  set x := lerp (sidePt M.W pc tc) e s
  have hxi : x ∈ i ∩ M.D := ⟨by zuoyw; exact lerp_mem_segment _ _ hs0.le hs1.le,
    hopen s ztdxi⟩
  have hxK : x ∈ connectedComponentIn ztjjs k₂ := hsecr _ by_tauto hleft
  have hsub : i ∩ M.D ⊆ M.D \ j := fun y hy =>
    ⟨hy.2, fun hyj => hsys.inter_subset_compl hi hj hij ⟨hy.1, hyj⟩ hy.2⟩
  have hcon := (hsys.chord_inter_nonempty_isPreconnected hi).2.subset_connectedComponentIn
    hxi hsub
  have hzK : z ∈ connectedComponentIn ztjjs k₂ := by
    zuorw; grind
  have hopenK : IsOpen (connectedComponentIn ztjjs k₂) :=
    (hM.isOpen.sdiff (hsys.isClosed_chord hj)).connectedComponentIn
  obtain ⟨u, huK, huU⟩ := mem_closure_iff.1 hzU _ hopenK hzK
  zufqo
  rw [connectedComponentIn_eq (hUK huU), connectedComponentIn_eq huK]
end WalkAx
open Chazelle.Visibility (rayPt_fst rayPt_snd)
namespace OracleQ
variable (z : Point) (σ a b : ℝ) (C : Chain) {F : Set (Set Point)} {V : Set Point} (Q : Polygon) (h : ℕ)
/-- Rays compose: moving `a` then `b` along the direction `σ`. -/
theorem rayPt_rayPt : rayPt ztrvd σ b = rayPt z σ ztth := by
  zudln
  grind

/-- Moving `a` along `σ`, then `b` along `-σ`. -/
theorem rayPt_rayPt_neg :
    rayPt ztrvd (-σ) b = rayPt z σ zttem := by
  zudln
  grind

/-- The parameter of a horizontal ray is determined by its point. -/
theorem rayPt_injective {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Function.Injective (rayPt z σ) := by
  intro a b h
  have := congrArg Prod.fst h
  zudv
  grind

/-! ## Answers -/

/-- **Above the top of the chain, the ray misses it.** -/
theorem noHit_of_above (C : Chain) {z : Point} (hz : C.top.2 < z.2) (σ : ℝ) :
    NoHit C.set z σ := by
  intro t _ hmem
  have := C.snd_le_top_of_mem_set hmem
  zueze

/-- **A hit on the chain is the answer.**  For a free direction below the top, if the first point
of the ray off the domain is on the chain, it is the first hit of the chain. -/
theorem firstHit_chain_of_hit {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hfree : Merge.FreeAt C z σ)
    (hmem : rayPt z σ ztbtm ∈ C.set) : FirstHit C.set z σ ztbtm :=
  Sweep.firstHit_of_compl_dom C hz hσ hfree C.set_subset_dom_compl hmem

/-- **A hit off the chain means no hit.**  For a free direction below the top, if the first point
of the ray off the domain is not on the chain (it is on a vertical side of the box), the ray
misses the chain. -/
theorem noHit_chain_of_hit {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hfree : Merge.FreeAt C z σ)
    (hmem : rayPt z σ ztbtm ∉ C.set) : NoHit C.set z σ := by
  obtain ⟨hT, hnd, hdom⟩ := Merge.hit_of_freeAt C hz hσ hfree
  zuckj
  have hout : rayPt z σ T ∉ Chain.box C.radius := by
    rcases (Merge.not_mem_dom_iff C by_simp_all).1 hnd with h | h
    · zubh
    simp_all
  have hin : rayPt z σ _ ∈ Chain.box C.radius :=
    C.dom_subset_box ztxoe
  intro t ht htC
  have hbt := C.set_subset_box htC
  rcases lt_trichotomy t T with hlt | heq | hgt
  · exact C.not_mem_set_of_mem_dom by_simp_all htC
  · simp_all
  · -- the box is convex: `T` lies between `T / 2` and `t`, both inside the box
    apply hout
    simp only [Chain.mem_box_iff, rayPt_fst, rayPt_snd] at hin hbt ⊢
    refine ⟨?_, hin.2⟩
    zvncj at hin hbt ⊢
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith [hin.1.1, hin.1.2, hbt.1.1, hbt.1.2]

/-! ## The first hit through an interval of the domain -/

/-- **Characterisation of the first-hit parameter**: if the ray is in the domain on `(0, T)` and
leaves it at `T`, then `C.hitParam z σ = T`. -/
theorem hitParam_eq_of_interval (C : Chain) {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ C.dom) (hend : rayPt z σ T ∉ C.dom) :
    C.hitParam z σ = T := by
  have hfree : Merge.FreeAt C z σ := by
    zuhda

  obtain ⟨h1, h2, h3⟩ := Merge.hit_of_freeAt C hz hσ hfree
  grind

/-- A point of the ray at a parameter of the interval `(a, s)` of a region is in the domain. -/
theorem mem_dom_of_region
    (hV : V ∈ (chainModel C).regions F) {x : Point} (hx : x ∈ V) : x ∈ C.dom :=
  (Chazelle.Chain.regionsIn_subset (D := C.dom) hV hx).1

/-- The ray hits the region `V` at `x`: `x` lies on (the point set of) an arc of `V`. -/
def ArcHit (C : Chain) (F : Set ztf) (V : Set Point) (x : Point) : Prop :=
  ∃ a b, (chainModel C).IsArc F V a b ∧ x ∈ (chainModel C).arcSet a b

/-- **Leaving a region forward.**  If the ray is in the region `V` on `(a, s)` and off the domain
at `s`, the point at `s` lies on an arc of `V`. -/
theorem arcHit_left (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {V : Set Point} (hV : V ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {a s : ℝ} (has : a < s)
    (hin : ∀ t, a < t → t < s → rayPt z σ t ∈ V) (hs : rayPt z σ s ∉ C.dom) :
    ArcHit C F V ztbwc := by
  set z' := rayPt z σ a with hz'
  zukhh
  have hini : ∀ᶠ u in 𝓝[>] (0 : ℝ), rayPt z' σ u ∈ V := by
    filter_upwards [Ioo_mem_nhdsGT ztwfu] with u hu
    zukwm
    grind
  obtain ⟨x, y, harc, hmem⟩ := Sweep.local_shoot C hP hFam hV hz'2 hσ hini
  have hhit : C.hitParam z' σ = s - a := by
    refine hitParam_eq_of_interval C hz'2 hσ ztwfu ztpbw ?_
    · zukwm
      zulfp
    · rw [hz', rayPt_rayPt, add_sub_cancel]
      zujux
  rw [hhit, hz', rayPt_rayPt, add_sub_cancel] at hmem
  exact ztopv

/-- **Leaving a region backward.**  If the ray is in the region `V` on `(s, b)` and off the domain
at `s`, the point at `s` lies on an arc of `V`. -/
theorem arcHit_right (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {V : Set Point} (hV : V ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {s b : ℝ} (hsb : s < b)
    (hin : ∀ t, s < t → t < b → rayPt z σ t ∈ V) (hs : rayPt z σ s ∉ C.dom) :
    ArcHit C F V ztbwc := by
  set z' := rayPt z σ b with hz'
  zukhh
  zukv
  have hini : ∀ᶠ u in 𝓝[>] (0 : ℝ), rayPt z' (-σ) u ∈ V := by
    filter_upwards [Ioo_mem_nhdsGT ztwga] with u hu
    zukwn
    grind
  obtain ⟨x, y, harc, hmem⟩ := Sweep.local_shoot C hP hFam hV hz'2 hnσ hini
  have hhit : C.hitParam z' (-σ) = b - s := by
    refine hitParam_eq_of_interval C hz'2 hnσ ztwga ztpbw ?_
    · zukwn
      zulfp
    · rw [hz', rayPt_rayPt_neg, sub_sub_cancel]
      zujux
  rw [hhit, hz', rayPt_rayPt_neg, sub_sub_cancel] at hmem
  exact ztopv

/-! ## Crossing adjacency and the path of regions along a ray -/

/-- **Crossing adjacency**: the regions `A` and `B` face each other across a point `x` of the
chain along a horizontal line (the points just behind `x` are in `A`, those just after it in `B`).
These are the adjacencies of faces of `S*` through an edge of the chain (p. 514); the graph built
by the preprocessing must contain them. -/
def CrossAdj (C : Chain) (A B : Set Point) : Prop :=
  ∃ x ∈ C.set, ∃ σ : ℝ, ztdd ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∈ A) ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∈ B)

/-- **A step of the ray** before the parameter `T`: the ray crosses the chain at a parameter
`s ∈ (0, T)` from the region `A` into the region `B`, and both regions have an arc through the
crossing point. -/
def RayStep (C : Chain) (F : Set ztf) (z : Point) (σ T : ℝ) (A B : Set Point) : Prop :=
  A ∈ (chainModel C).regions F ∧ B ∈ (chainModel C).regions F ∧ CrossAdj C A B ∧
    ∃ s, 0 < s ∧ s < T ∧ ArcHit C F A ztbwc ∧ ArcHit C F B ztbwc

/-- A point of the ray in the box, off the chain and off the chords, below the top, is free. -/
theorem mem_freeIn_of_ray (C : Chain) {F : Set ztf} {z : Point} (hz : z.2 ≤ C.top.2)
    {σ t : ℝ} (hbox : rayPt z σ t ∈ Chain.box C.radius) (hC : rayPt z σ t ∉ C.set)
    (hF : rayPt z σ t ∉ ⋃₀ F) : rayPt z σ t ∈ freeIn C.dom F := by
  refine ⟨?_, hF⟩
  by_contra hd
  rcases (Merge.not_mem_dom_iff C by_simp_all).1 hd with h | h
  · simp_all
  simp_all

/-- A free open interval of the ray meeting a region lies in it. -/
theorem interval_subset_region
    (hV : V ∈ (chainModel C).regions F) {z : Point} {σ a b : ℝ}
    (hfree : ∀ t, a < t → t < b → rayPt z σ t ∈ freeIn C.dom F) {t₀ : ℝ} (ht₀a : a < t₀)
    (ht₀b : t₀ < b) (hin : rayPt z σ t₀ ∈ V) : ∀ t, a < t → t < b → rayPt z σ t ∈ V := by
  have hV' : V ∈ regionsIn C.dom F := hV
  have hc : IsPreconnected (rayPt z σ '' Ioo a b) :=
    isPreconnected_Ioo.image _ (Chazelle.Visibility.continuous_rayPt z σ).continuousOn
  have hsub := Sweep.subset_region hV' hc by_grind
    by_grind hin
  grind

/-- A free open interval of the ray lies in one region. -/
theorem exists_region_of_interval {z : Point} {σ a b : ℝ}
    (hab : a < b) (hfree : ∀ t, a < t → t < b → rayPt z σ t ∈ freeIn C.dom F) :
    ∃ V ∈ (chainModel C).regions F, ∀ t, a < t → t < b → rayPt z σ t ∈ V := by
  have hm : rayPt z σ ztwwr ∈ freeIn C.dom F := by_grind
  refine ⟨_, Chazelle.Chain.mem_regionsIn hm, ?_⟩
  exact interval_subset_region C (Chazelle.Chain.mem_regionsIn hm) hfree by_linarith
    by_linarith (mem_connectedComponentIn hm)

/-- **The last crossing before `t₁`**: for a finite set `X` of parameters and `t₁ > 0` there is
`s ∈ [0, t₁)`, either `0` or a positive element of `X`, with no element of `X` in `(s, t₁)`. -/
theorem exists_gap {X : Set ℝ} (hX : X.Finite) {t₁ : ℝ} (ht₁ : 0 < t₁) :
    ∃ s, 0 ≤ s ∧ s < t₁ ∧ (s = 0 ∨ (0 < s ∧ s ∈ X)) ∧ ∀ t, s < t → t < t₁ → t ∉ X := by
  by_cases hne : (X ∩ Ioo 0 t₁).Nonempty
  · obtain ⟨s, hs, hmax⟩ := Set.exists_max_image _ id (hX.inter_of_left _) hne
    refine ⟨s, hs.2.1.le, hs.2.2, by_simp_all, fun t hst ht1 htX => ?_⟩
    have := hmax t by_grind
    grind
  · refine ⟨0, le_rfl, ht₁, Or.inl rfl, fun t ht0 ht1 htX => hne ⟨t, htX, ht0, ht1⟩⟩

/-- **The regions met by a ray form a path** (nondegenerate rays).  Let the ray from `z` (below
the top of the chain) stay in the box on `(0, T)`, meet the chain at finitely many parameters and
avoid the chords of `F` on `(0, T)`.  If its initial part lies in the region `U` and its part just
before `t₁ ≤ T` in the region `R`, then `U` and `R` are joined by a chain of `RayStep`s. -/
theorem ray_path (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {T : ℝ}
    (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hfin : {t : ℝ | rayPt z σ t ∈ C.set}.Finite)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ F)
    {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    (hUi : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∀ (n : ℕ) (t₁ : ℝ) (R : Set Point), ({t : ℝ | rayPt z σ t ∈ C.set} ∩ Ioo 0 t₁).ncard = n →
      0 < t₁ → t₁ ≤ T → R ∈ (chainModel C).regions F →
      (∀ᶠ t in 𝓝[<] t₁, rayPt z σ t ∈ R) → Relation.ReflTransGen ztoxs U R := by
  set X := {t : ℝ | rayPt z σ t ∈ C.set} with hXdef
  zugok
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t₁ R hn ht₁ ht₁T hR hRi
  obtain ⟨s, hs0, hst, hsX, hgap⟩ := exists_gap hfin ht₁
  have hfree : ∀ t, s < t → t < t₁ → rayPt z σ t ∈ freeIn C.dom F := fun t h1 h2 =>
    mem_freeIn_of_ray C hz by_grind by_grind
      by_grind
  obtain ⟨t', ht'R, ht'⟩ := (hRi.and (Ioo_mem_nhdsLT hst)).exists
  have hRall := interval_subset_region C hR hfree ht'.1 ht'.2 ht'R
  rcases hsX with rfl | ⟨hspos, hsX⟩
  · -- no crossing: the ray is in one region on `(0, t₁)`
    obtain ⟨t'', ht''U, ht''⟩ := (hUi.and (Ioo_mem_nhdsGT ht₁)).exists
    zuixf
    zuiww
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU' hR' with e | hdis
    · zui
    grind
  · -- the last crossing `s`: the region `A` just before it
    obtain ⟨s', hs'0, hs's, -, hgap'⟩ := exists_gap hfin hspos
    have hfree' : ∀ t, s' < t → t < s → rayPt z σ t ∈ freeIn C.dom F := fun t h1 h2 =>
      mem_freeIn_of_ray C hz by_grind by_grind
        by_grind
    obtain ⟨A, hA, hAall⟩ := exists_region_of_interval C hs's hfree'
    have hfinI : (X ∩ Ioo 0 t₁).Finite := hfin.inter_of_left _
    have hlt : (X ∩ Ioo 0 s).ncard < n := by
      zulrd
      refine Set.ncard_lt_ncard ⟨by_grind, fun hsub => ?_⟩
        hfinI
      exact lt_irrefl s (hsub by_grind).2.2
    have hpath := ih _ hlt s A rfl hspos by_linarith hA
      (by filter_upwards [Ioo_mem_nhdsLT hs's] with t ht; grind)
    have hsdom := (C.set_subset_dom_compl hsX)
    refine hpath.tail ⟨hA, hR, ⟨rayPt z σ s, hsX, σ, hσ, ?_, ?_⟩, s, hspos, by_linarith,
      arcHit_left C hP hFam hA hz hσ hs's hAall hsdom,
      arcHit_right C hP hFam hR hz hσ hst hRall hsdom⟩
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hs's)] with u hu
      rw [rayPt_rayPt_neg]
      grind
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hst)] with u hu
      rw [rayPt_rayPt]
      grind

/-- The initial part of a free ray avoiding the chords lies in a region. -/
theorem exists_initial_region {z : Point} {σ : ℝ}
    (hfree : Merge.FreeAt C z σ) (hnoF : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∉ ⋃₀ F) :
    ∃ U ∈ (chainModel C).regions F, ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hfree.and hnoF)
  obtain ⟨U, hU, hall⟩ := exists_region_of_interval C (z := z) (σ := σ) (F := F) hu
    fun t h1 h2 => ⟨(hsub ztwo).1, (hsub ztwo).2⟩
  refine ztraf
  filter_upwards [Ioo_mem_nhdsGT hu] with t ht
  simp_all

/-- The part of a nondegenerate ray just before `T` lies in a region (the region `R` of the query,
which the implementation finds by double identification at the hit point, or on the side of the
box). -/
theorem exists_final_region {z : Point} (hz : z.2 ≤ C.top.2)
    {σ T : ℝ} (hT : 0 < T) (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hfin : {t : ℝ | rayPt z σ t ∈ C.set}.Finite)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ F) :
    ∃ R ∈ (chainModel C).regions F, ∀ᶠ t in 𝓝[<] T, rayPt z σ t ∈ R := by
  obtain ⟨s, hs0, hsT, -, hgap⟩ := exists_gap hfin hT
  obtain ⟨R, hR, hall⟩ := exists_region_of_interval C hsT fun t h1 h2 =>
    mem_freeIn_of_ray C hz (hbox t by_linarith h2) (hgap t h1 h2) (hnoF t by_linarith h2)
  refine ⟨R, hR, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hsT] with t ht
  simp_all

/-! ## Nondegeneracy -/

/-- **Finitely many crossings**: if no edge of the chain is horizontal, a horizontal ray meets the
chain at finitely many parameters. -/
theorem finite_crossings (C : Chain)
    (hne : ∀ k, k < C.m → (C.vertex k).2 ≠ (C.vertex zts).2) (z : Point) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : {t : ℝ | rayPt z σ t ∈ C.set}.Finite := by
  have hsub : {t : ℝ | rayPt z σ t ∈ C.set} ⊆
      ⋃ k ∈ Finset.range C.m, {t : ℝ | rayPt z σ t ∈ C.chainEdge k} := by
    rintro t ⟨k, hk, hmem⟩
    simp only [Finset.mem_range, mem_iUnion, mem_ofPred_eq]
    grind
  refine Set.Finite.subset (Set.Finite.biUnion by_simp_all fun k hk => ?_) hsub
  refine Set.Subsingleton.finite fun a ha b hb => ?_
  have hk := Finset.mem_range.1 hk
  simp only [mem_ofPred_eq, C.chainEdge_eq] at ha hb
  obtain ⟨s₁, -, -, h₁⟩ := ha
  obtain ⟨s₂, -, -, h₂⟩ := hb
  have hy1 := congrArg Prod.snd h₁
  have hy2 := congrArg Prod.snd h₂
  simp only [rayPt_snd] at hy1 hy2
  have hd : (C.vertex _).2 - (C.vertex k).2 ≠ 0 := sub_ne_zero.2 (hne k hk).symm
  have hs : s₁ = s₂ := by
    simp_all
  apply rayPt_injective z hσ
  simp_all

/-- Distinct vertex heights of the ambient polygon: no edge of the chain is horizontal. -/
theorem vertex_snd_ne (C : Chain) (hD : DistinctHeights C.P) {k : ℕ} :
    (C.vertex k).2 ≠ (C.vertex zts).2 := by
  unfold Chain.vertex
  zudzh
  refine hD _ _ ztcsx ztmal ?_
  unfold Chain.edgeIdx
  zuq
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  rw [show C.s + zts - zttw = 1 by omega, Nat.one_mod_eq_one.2 by_omega] at h1
  omega

/-! ## The cluster argument (p. 515) -/

/-- **Labels along a path avoiding `D*`**: if the label is constant along the walks of `G` that
avoid `D*`, and every step of a path joins equal or adjacent nodes outside `D*`, then the ends of
the path are equal, or both outside `D*` with the same label. -/
theorem label_of_path {ι : Type*} (G : SimpleGraph ι) (Dm : ι → Prop) (ℓ : ι → ℕ)
    (hlab : ∀ u v (w : G.Walk u v), ztgnr → ℓ u = ℓ v)
    {r : ι → ι → Prop} (hr : ∀ a b, r a b → ¬ Dm a ∧ ¬ Dm b ∧ ztnqs)
    {i j : ι} (h : Relation.ReflTransGen r i j) : i = j ∨ (¬ Dm i ∧ ¬ Dm j ∧ ℓ i = ℓ j) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, hbc'⟩ := hr _ _ hbc
    have hℓ : ℓ b = ℓ c := by
      rcases hbc' with e | hadj
      · zui
      · refine hlab _ _ (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil) ?_
        simp_all
    rcases ih with e | ⟨hi, -, hl⟩
    · simp_all
    · grind

/-! ## Degenerate starts: along a chord, and from the box -/

/-- The ray from a point of the closed box at a height inside the box stays in the box until it
reaches the side of the box in its direction (parameter `r - σ z.1`). -/
theorem rayPt_mem_box (C : Chain) {z : Point} (hz1 : |z.1| ≤ C.radius) (hz2 : |z.2| < C.radius)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {t : ℝ} (ht : 0 < t) (htT : t < C.radius - σ * z.1) :
    rayPt z σ t ∈ Chain.box C.radius := by
  zujfw
  zudlo
  rw [abs_le] at hz1
  zumlw
  rcases hσ with rfl | rfl <;> constructor <;> linarith [hz1.1, hz1.2]

/-- The walk of the chain model has `2 m + 7` edges. -/
theorem walk_n : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n C.sideBeta

/-- The key of the box position of a rightward query from the height of vertex `h`. -/
theorem key_box_left :
    (chainModel C).key Q ⟨1, h + 1⟩ = 1 + (C.radius - (Q.vtx h).2) / ztekt := by
  zubo
  have h2 : ztcse % (chainModel C).W.n = 2 := by_rfl
  zultv
  simp only [h2]
  show ((1 : ℕ) : ℝ) + (if ((C.sideWalk C.sideBeta).vtx 1).2 = ((C.sideWalk C.sideBeta).vtx 2).2
    then 0 else ((Q.vtx h).2 - ((C.sideWalk C.sideBeta).vtx 1).2) /
      (((C.sideWalk C.sideBeta).vtx 2).2 - ((C.sideWalk C.sideBeta).vtx 1).2)) = _
  rw [C.sideWalk_vtx_one, C.sideWalk_vtx_two]
  grind

/-- The key of the box position of a leftward query from the height of vertex `h`. -/
theorem key_box_right :
    (chainModel C).key Q ⟨3, h + 1⟩ = 3 + ((Q.vtx h).2 + C.radius) / ztekt := by
  zubo
  have h4 : ztjfq % (chainModel C).W.n = 4 := by_rfl
  zultv
  simp only [h4]
  show ((3 : ℕ) : ℝ) + (if ((C.sideWalk C.sideBeta).vtx 3).2 = ((C.sideWalk C.sideBeta).vtx 4).2
    then 0 else ((Q.vtx h).2 - ((C.sideWalk C.sideBeta).vtx 3).2) /
      (((C.sideWalk C.sideBeta).vtx 4).2 - ((C.sideWalk C.sideBeta).vtx 3).2)) = _
  rw [C.sideWalk_vtx_three, C.sideWalk_vtx_four]
  grind

/-! ## The first naive scan -/

/-- The scan bound from a first hit: before the first hit on a set, the ray avoids it. -/
theorem avoid_of_firstHitOpt {A : Set Point} {z : Point} {σ : ℝ} {o : Option ℝ}
    (h : Sweep.FirstHitOpt A z σ o) {T : ℝ} (hT : ∀ t, o = some t → T ≤ t) :
    ∀ s, 0 < s → s < T → rayPt z σ s ∉ A := by
  intro s hs0 hsT hmem
  cases o with
  | none => exact h s hs0 hmem
  | some t => exact h.2.2 s hs0 by_grind hmem

/-! ## The cluster argument with nodes (arcs) instead of regions -/

/-- **The cluster argument, node version.**  The nodes `ι` of the graph `G` carry regions `rg`
(several nodes per region, e.g. the arcs of the region; scanning a node means scanning its whole
region, so `hD` speaks of the region of a node of `D*`).  The nodes of one region are connected
inside the region (`hconn`), and two regions facing each other across the chain have adjacent
nodes (`hG`).  If the ray starts in `U`, ends just before `T` in the region of the node `iR`, and
hits no region of a node of `D*` before `T`, then `U` has a node in `D*` or in the cluster of
`iR`. -/
theorem cluster_query_nodes (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {ι : Type*} (rg : ι → Set Point)
    (G : SimpleGraph ι)
    (hconn : ∀ a b, rg a = rg b →
      Relation.ReflTransGen (fun u v => G.Adj u v ∧ rg u = rg a ∧ rg v = rg a) a b)
    (hG : ∀ A B, A ∈ (chainModel C).regions F → B ∈ (chainModel C).regions F → A ≠ B →
      CrossAdj C A B → ∃ a b, rg a = A ∧ rg b = B ∧ G.Adj a b)
    (Dm : ι → Prop) (ℓ : ι → ℕ)
    (hlab : ∀ u v (w : G.Walk u v), ztgnr → ℓ u = ℓ v)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 0 < T)
    (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hfin : {t : ℝ | rayPt z σ t ∈ C.set}.Finite)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ F)
    (hD : ∀ i, Dm i → ∀ s, 0 < s → s < T → ¬ ArcHit C F (rg i) ztbwc)
    {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    (hUi : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) {iR : ι}
    (hR : rg iR ∈ (chainModel C).regions F) (hRi : ∀ᶠ t in 𝓝[<] T, rayPt z σ t ∈ rg iR) :
    ∃ iU, rg iU = U ∧ (Dm iU ∨ (¬ Dm iU ∧ ℓ iU = ℓ iR)) := by
  have hpath := ray_path C hP hFam hz hσ hbox hfin hnoF hU hUi _ T _ rfl hT le_rfl hR hRi
  -- the node relation along the ray
  let S : ι → ι → Prop := fun a b => ztnqs ∧ ¬ Dm a ∧ ¬ Dm b
  -- nodes of a region hit before `T` are not in `D*`
  have hnotD : ∀ V, ztxin →
      ∀ v, rg v = V → ¬ Dm v := by
    grind
  -- inside a region hit before `T`, nodes are joined by `S`-paths
  have hinside : ∀ V, ztxin →
      ∀ a b, rg a = V → rg b = V → Relation.ReflTransGen S a b := by
    intro V hV a b ha hb
    have hc := hconn a b ztvuj
    refine Relation.ReflTransGen.mono (fun u v huv => ?_) _ _ hc
    obtain ⟨hadj, hu, hv⟩ := huv
    exact ⟨Or.inr hadj, hnotD V hV u (hu.trans ha), hnotD V hV v (hv.trans ha)⟩
  have key : ∀ V, Relation.ReflTransGen ztoxs U V →
      V = U ∨ ∀ v, rg v = V → ∃ u, rg u = U ∧ Relation.ReflTransGen S u v := by
    intro V hUV
    induction hUV with
    | refl => exact Or.inl rfl
    | @tail W X _ hWX ih =>
      obtain ⟨hWr, hXr, hcr, s, hs0, hsT, hWa, hXa⟩ := hWX
      have hWhit : ∃ s, 0 < s ∧ s < T ∧ ArcHit C F W _ := ⟨s, hs0, hsT, hWa⟩
      have hXhit : ∃ s, 0 < s ∧ s < T ∧ ArcHit C F X _ := ⟨s, hs0, hsT, hXa⟩
      by_cases hWX : W = X
      · grind
      · right
        obtain ⟨a, b, ha, hb, hab⟩ := hG W X hWr hXr hWX hcr
        have hstep : S a b := by_grind
        zuml
        have hbv := hinside X hXhit b v hb hv
        rcases ih with e | ih
        · zugig
          exact ⟨a, ha, (Relation.ReflTransGen.single hstep).trans hbv⟩
        · obtain ⟨u, hu, hua⟩ := ih a ha
          exact ⟨u, hu, (hua.tail hstep).trans hbv⟩
  rcases key _ hpath with e | h
  · grind
  · obtain ⟨u, hu, hpu⟩ := h iR rfl
    refine ⟨u, hu, ?_⟩
    rcases label_of_path G Dm ℓ hlab by_grind hpu with
      e | ⟨h1, -, h3⟩
    · grind
    grind
end OracleQ
open Chazelle.Chain (sideE)
open Chazelle.Geometry (lerp_zero)
namespace OracleQ
variable (C : Chain)

/-- The chain point with coordinate `(k, τ)`. -/
noncomputable def cp (k : ℕ) (τ : ℝ) : Point := lerp ztib ztwkj τ

/-- A valid chain coordinate: `k < m`, `τ ∈ [0, 1)`, or the last vertex `(m, 0)`. -/
def CCoord (k : ℕ) (τ : ℝ) : Prop := (k < C.m ∧ 0 ≤ τ ∧ τ < 1) ∨ (k = C.m ∧ τ = 0)
theorem cp_zero (k : ℕ) : cp C k 0 = C.vertex k := lerp_zero _ _

/-- **The chain is injective in its coordinate.** -/
theorem cp_inj (hP : C.P.Simple) {k k' : ℕ} {τ τ' : ℝ} (h : CCoord C k τ) (h' : CCoord C k' τ')
    (heq : cp C k τ = cp C k' τ') : k = k' ∧ τ = τ' := by
  have hk : ztidw := by rcases h with h | h <;> omega
  have hk' : ztskc := by rcases h' with h | h <;> omega
  rcases eq_or_lt_of_le (show 0 ≤ τ by rcases h with h | h <;> [exact h.2.1; exact le_of_eq h.2.symm])
    with hτ | hτ <;>
  rcases eq_or_lt_of_le (show 0 ≤ τ' by rcases h' with h | h <;> [exact h.2.1; exact le_of_eq h.2.symm])
    with hτ' | hτ'
  · subst hτ; subst hτ'
    rw [cp_zero, cp_zero] at heq
    exact ⟨C.sideVertex_inj hP hk hk' heq, rfl⟩
  · exfalso
    subst hτ
    zucas
    have hτ1 : τ' < 1 := by rcases h' with h | h <;> [exact h.2.2; zuozq]
    zukqk
    exact C.sideOpen_ne_vertex hP by_simp_all heq.symm
  · exfalso
    subst hτ'
    zuqh

    zukqk
    exact C.sideOpen_ne_vertex hP by_simp_all heq
  · zuqh

    zucas
    have hτ1' : τ' < 1 := by rcases h' with h | h <;> [exact h.2.2; zuozq]
    by_cases hkk : k = k'
    · subst hkk
      zubee
      zukee
      unfold cp lerp at heq
      grind
    · exfalso
      apply C.sideOpen_not_mem_chainEdge hP hkm hk'm ztvbi ⟨hτ, hτ1⟩
      show cp C k τ ∈ C.chainEdge k'
      rw [heq, C.chainEdge_eq]
      exact Geometry.lerp_mem_segment _ _ hτ'.le hτ1'.le

/-- The tour index on the double circle: `j = (S + i) mod 2 m`. -/
noncomputable def tj (i : ℕ) : ℕ := ztwz % ztbb

/-- **The tour coordinate** of the tour position `(i, t)`: `u = j + t`. -/
noncomputable def tu (i : ℕ) (t : ℝ) : ℝ := (tj C i : ℝ) + t
variable (i : ℕ)
theorem tj_lt : tj C i < 2 * C.m := Nat.mod_lt _ C.two_m_pos

/-- The chain coordinate of a tour position. -/
noncomputable def tk (i : ℕ) (t : ℝ) : ℕ × ℝ :=
  if tj C i < C.m then (tj C i, t)
  else if t = 0 then (2 * C.m - tj C i, 0) else (2 * C.m - tj C i - 1, 1 - t)
theorem tk_coord {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    CCoord C (tk C i t).1 (tk C i t).2 := by
  zudoo
  unfold tk CCoord
  grind

/-- **The point of a tour position** in chain coordinates. -/
theorem tour_pt (hi : i < 2 * C.m) (t : ℝ) :
    sidePt ztcs ztcy t = cp C (tk C i t).1 (tk C i t).2 := by
  rw [C.sidePt_tour C.sideBeta hi]
  zueev
  zuhds
  have e2 : C.sideIdx C.sideBeta _ = sideE C.m ztkfu := C.sideIdx_succ C.sideBeta i
  zudoo
  zubt
  zuea
  unfold tk cp
  zuccs

  have sE3 : zthpv := fun x hx => by
    zudma

  zupi
  · grind
  · simp_all
  · zubi
    rw [Geometry.lerp_symm, sE3 _ by_omega, sE3 j by_omega]
    grind

/-- **Two tour positions have the same point iff their tour coordinates are equal or opposite.** -/
theorem same_point (hP : C.P.Simple) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m) {t t' : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (heq : sidePt ztcs ztcy t = sidePt ztcs ztetl t') :
    tu C i t = tu C i' t' ∨ tu C i t + tu C i' t' = 2 * C.m := by
  rw [tour_pt C i hi, tour_pt C i' hi'] at heq
  obtain ⟨hk, hτ⟩ := cp_inj C hP (tk_coord C i ht ht1) (tk_coord C i' ht' ht1') heq
  zudoo
  have hj' := tj_lt C i'
  unfold tu
  unfold tk at hk hτ
  split_ifs at hk hτ with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only at hk hτ
  all_goals first
    | (left
       have hc : (tj C i : ℝ) = tj C i' := by exact_mod_cast (by omega : tj C i = tj C i')
       linarith)
    | (right
       have hc : (tj C i : ℝ) + tj C i' = 2 * C.m := by
         exact_mod_cast (by omega : tj C i + tj C i' = 2 * C.m)
       linarith)
    | (right
       have hc : (tj C i : ℝ) + tj C i' + 1 = 2 * C.m := by
         exact_mod_cast (by omega : tj C i + tj C i' + 1 = 2 * C.m)
       linarith)
    | (exfalso; linarith)

/-! ## Positions at a point of the chain -/

/-- **Every walk position whose point is on the chain is a tour position** (or the closing vertex
`2 m + 6`, the top again). -/
theorem pos_on_chain {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hx : sidePt ztcs p t ∈ C.set) :
    ztbxy ∨ (p = 2 * C.m + 6 ∧ t = 0) := by
  zujst
  · exact absurd hx (C.sideWalk_box_pt C.sideBeta ztmbw ht ht1).1
  · zugjn
    · subst hl
      rcases eq_or_lt_of_le ht with h0 | h0
      · simp_all
      · exact absurd hx (C.sideWalk_box_pt C.sideBeta by_simp_all ht ht1).1
    omega

/-- The closing vertex of the walk is the top, like the first tour vertex. -/
theorem sidePt_last :
    sidePt ztcs ztcc 0 = sidePt ztcs ztfmo 0 := by
  rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour C.sideBeta le_rfl,
    Chain.sideTour_two_m, zero_add, C.sideWalk_vtx_six]

/-- The tour coordinate in terms of the key: `tu i t = S + (6 + i + t) - 6 - 2 m q`. -/
theorem tu_eq (t : ℝ) :
    ∃ q : ℕ, tu C i t = (C.sideS C.sideBeta : ℝ) + i + t - 2 * C.m * q := by
  refine ⟨ztwz / ztbb, ?_⟩
  unfold tu tj
  have h := Nat.mod_add_div ztwz ztbb
  have h' : ((ztwz % ztbb : ℕ) : ℝ) + (2 * C.m : ℕ) *
      ((ztwz / ztbb : ℕ) : ℝ) = (C.sideS C.sideBeta : ℝ) + i := by
    exact_mod_cast h
  grind

/-- **The mirror of a chain point**: two distinct walk keys `κ ≠ κ'` (positions with parameters in
`[0, 1)`) of the same point of the chain satisfy `κ + κ' ≡ 12 - 2 S (mod 2 m)`, or they are the
two visits `6`, `2 m + 6` of the top at the ends of the tour. -/
theorem mirror_sum (hP : C.P.Simple) {p p' : ℕ} (hp : p < 2 * C.m + 7) (hp' : p' < 2 * C.m + 7)
    {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (hx : sidePt ztcs p t ∈ C.set)
    (heq : sidePt ztcs p t = sidePt ztcs p' t')
    (hne : (p : ℝ) + t ≠ p' + t') :
    (∃ n : ℤ, ztdj + ztjg = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * n) ∨
      ((p : ℝ) + t = 6 ∧ (p' : ℝ) + t' = 2 * C.m + 6) ∨
      ((p : ℝ) + t = 2 * C.m + 6 ∧ (p' : ℝ) + t' = 6) := by
  have hx' : sidePt _ p' t' ∈ C.set := heq ▸ hx
  zubt
  -- normalise each position to a tour position `(i, t)` with `i < 2 m` and a shift `e ∈ {0, 2m}`
  have norm : ∀ {p : ℕ} {t : ℝ}, p < 2 * C.m + 7 → 0 ≤ t → t < 1 →
      sidePt ztcs p t ∈ C.set →
      ∃ i : ℕ, ∃ e : ℕ, i < 2 * C.m ∧ ztlnc ∧ (p : ℝ) + t = 6 + i + t + e ∧
        sidePt ztcs p t = sidePt ztcs ztcy t ∧
        (e = 2 * C.m → i = 0 ∧ t = 0) := by
    intro p t hp ht ht1 hx
    zucyu
    · refine ⟨p - 6, 0, by_omega, Or.inl rfl, ?_, by_simp_all, by_omega⟩
      simp_all
    · zufcz
      refine ⟨0, 2 * C.m, by_omega, Or.inr rfl, by_grind, sidePt_last C, by_simp_all⟩
  obtain ⟨i, e, hi, he, hk, hpt, he2⟩ := norm hp ht ht1 hx
  obtain ⟨i', e', hi', he', hk', hpt', he2'⟩ := norm hp' ht' ht1' hx'
  have heq' : sidePt ztcs ztcy t = sidePt ztcs ztetl t' := by
    grind
  obtain ⟨q, hq⟩ := tu_eq C i t
  obtain ⟨q', hq'⟩ := tu_eq C i' t'
  rcases same_point C hP hi hi' ht ht1 ht' ht1' heq' with h | h
  · -- equal tour coordinates: the keys differ by a multiple of `2 m`, hence are `6` and `2 m + 6`
    have hdiff : ((i : ℝ) + t) - (i' + t') = 2 * C.m * ztdel := by
      grind
    -- `|(i + t) - (i' + t')| < 2 m`, so the multiple is `0`
    have hlt1 : (i : ℝ) + t < 2 * C.m := by
      have : (i : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hi
      linarith
    have hlt2 : (i' : ℝ) + t' < 2 * C.m := by
      have : (i' : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hi'
      linarith
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hi0' : (0 : ℝ) ≤ i' := Nat.cast_nonneg i'
    zufvl
    have hqq : (q : ℤ) = q' := by
      have h1 : 2 * (C.m : ℝ) * ztdel < 2 * C.m := by_linarith
      have h2 : -(2 * (C.m : ℝ)) < 2 * C.m * ztdel := by_linarith
      have h3 : ztdel < 1 := by_nlinarith
      have h4 : -1 < ztdel := by_nlinarith
      have h5 : ((q : ℤ) : ℝ) - ((q' : ℤ) : ℝ) < 1 := by_omega
      have h6 : -1 < ((q : ℤ) : ℝ) - ((q' : ℤ) : ℝ) := by_omega
      have h7 : (q : ℤ) - q' < 1 := by exact_mod_cast h5
      have h8 : -1 < (q : ℤ) - q' := by exact_mod_cast h6
      omega
    have hqq' : (q : ℝ) = q' := by exact_mod_cast hqq
    have hsame : (i : ℝ) + t = i' + t' := by_grind
    -- so the keys differ only by the shifts `e, e'`
    right
    zuevk
    · grind
    · obtain ⟨rfl, rfl⟩ := he2' rfl
      grind
    · obtain ⟨rfl, rfl⟩ := he2 rfl
      grind
    grind
  · -- opposite tour coordinates
    left
    have hsum : ((C.sideS C.sideBeta : ℝ) + i + t - 2 * C.m * q) + ((C.sideS C.sideBeta : ℝ) + i' + t' - 2 * C.m * q') = 2 * C.m := by
      grind
    zuevk
    · refine ⟨1 + q + q', ?_⟩
      zudad
    · refine ztolo
      zudad
    · refine ztolo
      zudad
    grind
theorem interleave_absurd (P : ℝ → Prop) (hconv : ∀ x y z, x < y → y < z → P x → P z → P y)
    {x₁ x₂ x₃ x₄ : ℝ}
    (hord : ztkhh ∨ ztkhi)
    (h13 : P x₁ ↔ P x₃) (h24 : P x₂ ↔ P x₄) (h12 : P x₁ ↔ ¬ P x₂) : False := by
  grind

/-- **A chord of the walk cannot separate interleaved pairs of keys** (none of the keys at its
ends). -/
theorem sideInArc_interleave {a b x₁ x₂ x₃ x₄ : ℝ}
    (_hne : ∀ x ∈ ({x₁, x₂, x₃, x₄} : Set ℝ), x ≠ a ∧ x ≠ b)
    (hord : ztkhh ∨ ztkhi)
    (h13 : sideInArc a b x₁ ↔ sideInArc a b x₃) (h24 : sideInArc a b x₂ ↔ sideInArc a b x₄)
    (h12 : sideInArc a b x₁ ↔ ¬ sideInArc a b x₂) : False := by
  zuul
  · refine interleave_absurd _ (fun x y z hxy hyz hx hz => ?_) hord h13 h24 h12
    unfold sideInArc at *
    grind
  · -- the complement of the arc is the convex set `[b, a]` (away from the ends)
    let P : ℝ → Prop := fun x => ¬ sideInArc a b x
    have hP : ∀ x ∈ ({x₁, x₂, x₃, x₄} : Set ℝ), P x ↔ (b ≤ x ∧ x ≤ a) := by
      zuh
      simp only [P, sideInArc, ite_eq_right hab, not_or, not_lt]
      grind
    grind

/-- **Pairs of keys of chain points do not interleave.**  Keys lie in `[lo, lo + L]`; each pair
has its sum congruent to `K` modulo `L`, or is the pair of the two ends `lo`, `lo + L`. -/
theorem mirror_noncross {L K lo : ℝ} (hL : 0 < L) {k₁ k₂ k₃ k₄ : ℝ}
    (hr : ∀ k ∈ ({k₁, k₂, k₃, k₄} : Set ℝ), lo ≤ k ∧ k ≤ lo + L)
    (P13 : (∃ n : ℤ, k₁ + k₃ = K + L * n) ∨ (k₁ = lo ∧ k₃ = lo + L) ∨ (k₁ = lo + L ∧ k₃ = lo))
    (P24 : (∃ n : ℤ, k₂ + k₄ = K + L * n) ∨ (k₂ = lo ∧ k₄ = lo + L) ∨ (k₂ = lo + L ∧ k₄ = lo))
    (hord : (k₁ < k₂ ∧ k₂ < k₃ ∧ k₃ < k₄) ∨ (k₄ < k₁ ∧ k₁ < k₂ ∧ k₂ < k₃)) : False := by
  have r1 := hr k₁ by_simp
  have r2 := hr k₂ by_simp
  have r3 := hr k₃ by_simp
  have r4 := hr k₄ by_simp
  rcases P13 with ⟨n, hn⟩ | ⟨e1, e3⟩ | ⟨e1, e3⟩
  · rcases P24 with ⟨n', hn'⟩ | ⟨e2, e4⟩ | ⟨e2, e4⟩
    · -- the two sums differ by a multiple of `L` strictly between `-L` and `L`, and not by `0`
      have hdiff : (k₂ + k₄) - (k₁ + k₃) = L * ((n' : ℝ) - n) := by_grind
      have key : ∀ z : ℤ, 0 < L * (z : ℝ) → L * (z : ℝ) < L → False := by
        zumhs
        have h3 : (0 : ℝ) < z := by
          simp_all
        have h4 : (z : ℝ) < 1 := by
          simp_all
        have h5 : (0 : ℤ) < z := by_simp_all
        have h6 : z < (1 : ℤ) := by exact_mod_cast h4
        omega
      rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact key (n' - n) by_grind by_grind
      · exact key (n - n') by_grind by_grind
    · grind
    grind
  · grind
  grind

/-! ## The arcs of a normal form in the order of the table -/
section ArcOrder
variable {M : Model} {Q : Polygon} {N : NF}

/-- The arc at spine position `p`. -/
def sj (N : NF) (p : ℕ) : ℕ := N.seq.getD p 0

/-- The start key of the arc at spine position `p`. -/
noncomputable def sk (M : Model) (Q : Polygon) (N : NF) (p : ℕ) : ℝ :=
  M.key Q (N.arc ztmh).s

/-- The end key of the arc at spine position `p`. -/
noncomputable def ek (M : Model) (Q : Polygon) (N : NF) (p : ℕ) : ℝ :=
  M.key Q (N.arc ztmh).e

/-- The arc at a spine position is an arc of the region it records. -/
theorem isArc_sj (hN : IsNF M Q N) {p : ℕ} (hp : p < N.arcs.length) :
    ∃ reg : ℕ → Set Point, RegionCorr M Q N reg ∧ ArcsOK M Q N reg ∧
      M.IsArc ztdu (reg (N.arc ztmh).reg) ztcja ztchs := by
  zuzl
  exact ⟨reg, hR, hA, (hA.1 _ ztctk).2⟩

/-- The table has no repetition. -/
theorem seq_nodup (hN : IsNF M Q N) : N.seq.Nodup := by
  zudql
theorem sj_inj (hN : IsNF M Q N) {p q : ℕ} (hp : p < N.arcs.length) (hq : q < N.arcs.length)
    (h : sj N p = sj N q) : p = q := by
  zuhfd
  unfold sj at h
  zufmn
  exact (seq_nodup hN).getElem_inj_iff.1 h

/-- **Start keys strictly increase along the table** (nonempty family). -/
theorem starts_lt (hN : IsNF M Q N) (_hGM : GoodModel M) (hne : (N.F M Q).Nonempty) {p q : ℕ}
    (hpq : p < q) (hq : q < N.arcs.length) : sk M Q N p < sk M Q N q := by
  have hle := NFLoc.seq_sorted hN hpq.le hq
  zujfc
  obtain ⟨reg, hR, hA, harc⟩ := isArc_sj hN ztfhw
  have harc' : M.IsArc _ (reg (N.arc (sj N q)).reg) ztkfh ztjus :=
    (hA.1 _ ztjkg).2
  set a := sk M Q N p
  set b := ek M Q N p
  set b' := ek M Q N q
  zvnbo at harc'
  zufjq
  obtain ⟨-, hcb', hab'⟩ := WalkAx.arc_cuts hne harc'
  zuixy
  have hfree' := harc'.2.2.2.2.2.1
  -- the two ends coincide
  have hbb : b = b' := by
    by_contra hbb
    zuirh
    · simp_all
    · exact hfree' b (NFLoc.sideInArc_swap hab hab' hbb h1) hcb
  rw [← hbb] at harc'
  -- a common position faced by both regions
  obtain ⟨pp, hpp, t, ht, hin, -, hfac⟩ := WalkAx.exists_pos_in_arc hne harc
  have hfac' := harc'.2.2.2.2.2.2 pp t hpp ht.1 ht.2 hin
  have hRp := hR.1 _ (hA.1 _ ztypl).1
  have hRq := hR.1 _ (hA.1 _ ztjkg).1
  have hU := WalkAx.faces_unique hRp hRq hfac hfac'
  have hreg := hR.2.1 _ _ (hA.1 _ ztypl).1
    (hA.1 _ ztjkg).1 hU
  have hj := hA.2.1 _ _ ztypl ztjkg hreg heq
  exact absurd (sj_inj hN ztfhw hq hj) hpq.ne

/-- **The interior of an arc lies before the starts of later arcs.** -/
theorem interior_lt_start (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p q : ℕ} (hpq : p < q) (hq : q < N.arcs.length) {κ : ℝ}
    (hκ : sideInArc ztcja ztchs κ) : κ < sk M Q N q := by
  zuoa

  zucux
  zugrh
  rcases eq_or_lt_of_le hge with he | hlt'
  · simp_all
  · zulde
    zucri

/-- **The interior of an arc that is not the last lies after its start.** -/
theorem start_lt_interior (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p q : ℕ} (hpq : p < q) (hq : q < N.arcs.length) {κ : ℝ}
    (hκ : sideInArc ztcja ztchs κ) (_hκn : κ < M.W.n) : sk M Q N p < κ := by
  zuoa

  zuhrc

  · simp_all
  · zukmw
    · zubvv
    · exfalso
      zulde
      zufdq
      simp_all

/-- **The last arc**: its interior lies after its start or before every start. -/
theorem last_interior (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p q : ℕ} (hpq : p < q) (hq : q < N.arcs.length) {κ : ℝ}
    (hκ : sideInArc ztkfh ztjus κ) : sk M Q N q < κ ∨ κ < sk M Q N p := by
  obtain ⟨reg, -, -, harc⟩ := isArc_sj hN hq
  obtain ⟨reg', -, -, harc'⟩ := isArc_sj hN ztfhw
  zuixy
  have hcp := (WalkAx.arc_cuts hne harc').1
  have hlt := starts_lt hN hGM hne hpq hq
  zuhrc

  · simp_all
  · zukmw
    · simp_all
    · right
      zucux
      zugrh
      apply hfree _ _ hcp
      zuiq

/-- **Four arcs in the order of the table**: their interior keys are in cyclic order. -/
theorem order4 (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p₁ p₂ p₃ p₄ : ℕ} (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < N.arcs.length) {κ₁ κ₂ κ₃ κ₄ : ℝ}
    (hκ₁ : sideInArc (sk M Q N p₁) (ek M Q N p₁) κ₁) (hκ₂ : sideInArc (sk M Q N p₂) (ek M Q N p₂) κ₂)
    (hκ₃ : sideInArc (sk M Q N p₃) (ek M Q N p₃) κ₃) (hκ₄ : sideInArc (sk M Q N p₄) (ek M Q N p₄) κ₄)
    (hn₁ : κ₁ < M.W.n) (hn₂ : κ₂ < M.W.n) (hn₃ : κ₃ < M.W.n) :
    (κ₁ < κ₂ ∧ κ₂ < κ₃ ∧ κ₃ < κ₄) ∨ (κ₄ < κ₁ ∧ κ₁ < κ₂ ∧ κ₂ < κ₃) := by
  have a1 := start_lt_interior hN hGM hne h12 by_omega hκ₁ hn₁
  have b1 := interior_lt_start hN hGM hne h12 by_omega hκ₁
  have a2 := start_lt_interior hN hGM hne h23 by_omega hκ₂ hn₂
  have b2 := interior_lt_start hN hGM hne h23 by_omega hκ₂
  have a3 := start_lt_interior hN hGM hne h34 h4 hκ₃ hn₃
  have b3 := interior_lt_start hN hGM hne h34 h4 hκ₃
  rcases last_interior hN hGM hne (h12.trans (h23.trans h34)) h4 hκ₄ with c | c
  · grind
  grind
end ArcOrder

/-! ## The two pages do not cross -/
section Pages
variable {M : Model} {Q : Polygon} {N : NF}

/-- The region index of the arc at spine position `p`. -/
def rgi (N : NF) (p : ℕ) : ℕ := (N.arc ztmh).reg

/-- **An inner (star) chord**: two spine positions of arcs of the same region, the first being
the first arc of the region on the spine. -/
def StarOK (N : NF) (c : ℕ × ℕ) : Prop :=
  c.1 < c.2 ∧ c.2 < N.arcs.length ∧ rgi N c.1 = rgi N c.2 ∧
    ∀ q, q < N.arcs.length → rgi N q = rgi N c.1 → c.1 ≤ q
theorem key_lt_n {M : Model} {pp : ℕ} (hpp : pp < M.W.n) {t : ℝ} (ht : t < 1) :
    (pp : ℝ) + t < M.W.n := by
  have : (pp : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hpp
  linarith

/-- **The regions of the arcs do not interleave on the spine** (non-crossing partition, from the
cut structure: a chord separating two regions separates their keys). -/
theorem regions_noninterleave (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p₁ p₂ p₃ p₄ : ℕ} (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < N.arcs.length) (hr13 : rgi N p₁ = rgi N p₃) (hr24 : rgi N p₂ = rgi N p₄) :
    rgi N p₁ = rgi N p₂ := by
  have hp1 : p₁ < N.arcs.length := by_omega
  have hp2 : p₂ < N.arcs.length := by_omega
  have hp3 : p₃ < N.arcs.length := by_omega
  zuzl
  -- interior positions of the four arcs (facing the regions of the common witness `reg`)
  have pick : ∀ p, p < N.arcs.length → ∃ pp < M.W.n, ∃ t ∈ Ioo (0 : ℝ) 1,
      sideInArc ztcja ztchs zttwh ∧ ¬ M.IsCut ztdu zttwh ∧
        M.Faces pp t (reg ztdvx) := by
    zuda
    have harc := (hA.1 _ ztctk).2
    obtain ⟨pp, hpp, t, ht, h1, h2, h3⟩ := WalkAx.exists_pos_in_arc hne harc
    exact ⟨pp, hpp, t, ht, h1, h2, h3⟩
  obtain ⟨q₁, hq₁, t₁, ht₁, i₁, c₁, f₁⟩ := pick p₁ hp1
  obtain ⟨q₂, hq₂, t₂, ht₂, i₂, c₂, f₂⟩ := pick p₂ hp2
  obtain ⟨q₃, hq₃, t₃, ht₃, i₃, c₃, f₃⟩ := pick p₃ hp3
  obtain ⟨q₄, hq₄, t₄, ht₄, i₄, c₄, f₄⟩ := pick p₄ h4
  have hord := order4 hN hGM hne h12 h23 h34 h4 i₁ i₂ i₃ i₄ (key_lt_n hq₁ ht₁.2)
    (key_lt_n hq₂ ht₂.2) (key_lt_n hq₃ ht₃.2)
  by_contra hne12
  have hRg : ∀ p, p < N.arcs.length → reg ztdvx ∈ M.regions _ := fun p hp =>
    hR.1 _ (hA.1 _ ztctk).1
  have hlt : ∀ p, p < N.arcs.length → rgi N p < N.nRegions := fun p hp =>
    (hA.1 _ ztctk).1
  have hCS := (cutStructure M Q _ hGM hN.1).2.2
  -- the regions of the first two arcs differ
  have hdiff : reg _ ≠ reg _ := fun h =>
    hne12 (hR.2.1 _ _ by_grind by_grind h)
  have hsep := mt (hCS q₁ q₂ t₁ t₂ _ _ by_grind by_grind hq₁ hq₂ ht₁.1 ht₁.2 ht₂.1 ht₂.2
    c₁ c₂ f₁ f₂).2 hdiff
  push Not at hsep
  obtain ⟨c, hc, pa, pb, ta, tb, hAa, hAb, hpt, hiff⟩ := hsep
  have h13 := (hCS q₁ q₃ t₁ t₃ _ _ by_grind by_grind hq₁ hq₃ ht₁.1 ht₁.2 ht₃.1 ht₃.2
    c₁ c₃ f₁ f₃).1 by_grind c hc
  have h24 := (hCS q₂ q₄ t₂ t₄ _ _ by_grind by_grind hq₂ hq₄ ht₂.1 ht₂.2 ht₄.1 ht₄.2
    c₂ c₄ f₂ f₄).1 by_grind c hc
  have e13 : sideInArc ztbf ztbd (q₁ + t₁) ↔ sideInArc ztbf ztbd (q₃ + t₃) := by
    zumv
    exact h13 zthnl
  have e24 : sideInArc ztbf ztbd (q₂ + t₂) ↔ sideInArc ztbf ztbd (q₄ + t₄) := by
    zumv
    exact h24 zthnl
  have hcutA : M.IsCut _ _ := ⟨c, hc, pa, ta, hAa, rfl⟩
  have hcutB : M.IsCut _ _ := ⟨c, hc, pb, tb, hAb, rfl⟩
  refine sideInArc_interleave ?_ hord e13 e24 hiff
  zuh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · zulfx
  · zulfx
  · zulfx
  · zulfx

/-- **The inner (star) page does not cross.** -/
theorem stars_nonCross (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {L : List ztw} (hL : ∀ c ∈ L, StarOK N c) : OracleBook.NonCross L := by
  zufhx
  obtain ⟨hc12, hc2, hcr, hcmin⟩ := hL c hc
  obtain ⟨hc'12, hc'2, hc'r, hc'min⟩ := hL c' hc'
  have hreg := regions_noninterleave hN hGM hne h1 h2 h3 hc'2 hcr hc'r
  grind

/-- **An outer (zipper) chord**: two spine positions whose arcs contain, in their interiors, keys
of two positions at the same point of the chain. -/
def ZipOK (C : Chain) (Q : Polygon) (N : NF) (c : ℕ × ℕ) : Prop :=
  c.1 < c.2 ∧ c.2 < N.arcs.length ∧
    ∃ p₁ p₂ : ℕ, ∃ t₁ t₂ : ℝ, p₁ < (chainModel C).W.n ∧ p₂ < (chainModel C).W.n ∧
      0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
      Chazelle.Chain.sidePt (chainModel C).W p₁ t₁ ∈ C.set ∧
      Chazelle.Chain.sidePt (chainModel C).W p₁ t₁ = Chazelle.Chain.sidePt (chainModel C).W p₂ t₂ ∧
      sideInArc (sk ztc Q N c.1) (ek ztc Q N c.1) ztdhz ∧
      sideInArc (sk ztc Q N c.2) (ek ztc Q N c.2) ztoeu

/-- The keys of positions at a point of the chain lie in `[6, 2 m + 6]`. -/
theorem key_range (C : Chain) {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hx : Chazelle.Chain.sidePt ztcs p t ∈ C.set) :
    6 ≤ (p : ℝ) + t ∧ (p : ℝ) + t ≤ 6 + 2 * C.m := by
  zucyu
  · zudxr

  · subst h1; grind

/-- **The outer (zipper) page does not cross.** -/
theorem zips_nonCross (C : Chain) (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {L : List ztw} (hL : ∀ c ∈ L, ZipOK C Q N c) : OracleBook.NonCross L := by
  zuiv
  have hn := walk_n C
  zufhx
  obtain ⟨hc12, hc2, pa, pb, ta, tb, hpa, hpb, hta, hta1, htb, htb1, hxa, hab, ia, ib⟩ := hL c hc
  obtain ⟨hc'12, hc'2, pc, pd, tc, td, hpc, hpd, htc, htc1, htd, htd1, hxc, hcd, ic, id⟩ :=
    hL c' hc'
  have hord := order4 hN hGM hne h1 h2 h3 hc'2 ia ic ib id (key_lt_n hpa hta1)
    (key_lt_n hpc htc1) (key_lt_n hpb htb1)
  zvmxq at hpa hpb hpc hpd
  have hxb : Chazelle.Chain.sidePt (chainModel C).W pb tb ∈ C.set := by_simp_all
  have hxd : Chazelle.Chain.sidePt (chainModel C).W pd td ∈ C.set := by_simp_all
  have ra := key_range C hpa hta hta1 hxa
  have rb := key_range C hpb htb htb1 hxb
  have rc := key_range C hpc htc htc1 hxc
  have rd := key_range C hpd htd htd1 hxd
  have hneab : ztkzh := by
    grind
  have hnecd : (pc : ℝ) + tc ≠ pd + td := by
    grind
  have m1 := mirror_sum C hP hpa hpb hta hta1 htb htb1 hxa hab hneab
  have m2 := mirror_sum C hP hpc hpd htc htc1 htd htd1 hxc hcd hnecd
  refine mirror_noncross (L := 2 * C.m) (K := 12 - 2 * C.sideS C.sideBeta) (lo := 6)
    by_grind ?_ ?_ ?_ hord
  · zugf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    grind
  · grind
  grind
end Pages
def ZipRel (C : Chain) (Q : Polygon) (N : NF) (p q : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, ∃ t₁ t₂ : ℝ, p₁ < (chainModel C).W.n ∧ p₂ < (chainModel C).W.n ∧
    0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
    sidePt (chainModel C).W p₁ t₁ ∈ C.set ∧
    sidePt (chainModel C).W p₁ t₁ = sidePt (chainModel C).W p₂ t₂ ∧
    sideInArc ztwlo ztwnk ztdhz ∧
    sideInArc ztwlp ztwkp ztoeu
theorem ZipRel.symm {C : Chain} {Q : Polygon} {N : NF} {p q : ℕ} (h : ZipRel C Q N p q) :
    ZipRel C Q N q p := by
  obtain ⟨p₁, p₂, t₁, t₂, h1, h2, h3, h4, h5, h6, hx, he, i1, i2⟩ := h
  exact ⟨p₂, p₁, t₂, t₁, h2, h1, h5, h6, h3, h4, he ▸ hx, he.symm, i2, i1⟩
variable (C : Chain) {F : Set (Set Point)}
/-- **A crossing point lies on no chord**: the points of the line just before and just after
it are in regions. -/
theorem not_mem_chord_of_crossAdj
    (hF : F ⊆ Merge.augChords C) {A B : Set Point} (hA : A ∈ (chainModel C).regions F)
    (hB : B ∈ (chainModel C).regions F) {x : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hAe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∈ A)
    (hBe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∈ B) : ∀ c ∈ F, x ∉ c := by
  intro c hc hxc
  obtain ⟨y, a, b, h, -, rfl, -, -⟩ := Merge.augChords_spec ztlz
  obtain ⟨hy, ha, hb⟩ := hxc
  have hA' : A ∈ regionsIn C.dom F := hA
  have hB' : B ∈ regionsIn C.dom F := hB
  -- points of the chord in either direction are free, which is impossible
  have hfreeA : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∉ ⋃₀ F :=
    hAe.mono fun t ht => (Chazelle.Chain.regionsIn_subset hA' ht).2
  have hfreeB : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∉ ⋃₀ F :=
    hBe.mono fun t ht => (Chazelle.Chain.regionsIn_subset hB' ht).2
  have hab := h.lt
  -- one of the two directions runs along the chord
  have hmem : ∀ τ : ℝ, ztoi → (∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x τ t ∉ ⋃₀ F) →
      (τ = 1 → b ≤ x.1) ∧ (τ = -1 → x.1 ≤ a) := by
    intro τ hτ hfree
    constructor
    · zumgv

      zube

      zudjd

    · zumgv

      zube

      zudjd

  zukv
  have e1 := hmem σ hσ hfreeB
  have e2 := hmem (-σ) hnσ hfreeA
  grind

/-- **Both regions of a crossing have an arc through the crossing point.** -/
theorem arcHit_of_crossAdj (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {A B : Set Point}
    (hA : A ∈ (chainModel C).regions F) (hB : B ∈ (chainModel C).regions F)
    {x : Point} (hx : x ∈ C.set) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hAe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∈ A)
    (hBe : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∈ B) : ArcHit C F A x ∧ ArcHit C F B x := by
  have hz : x.2 ≤ C.top.2 := C.snd_le_top_of_mem_set hx
  have hxd : x ∉ C.dom := fun h => C.not_mem_set_of_mem_dom h hx
  zukv
  have e0 : ∀ τ : ℝ, rayPt x τ 0 = x := fun τ => by_simp
  obtain ⟨εA, hεA, hsubA⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hAe
  obtain ⟨εB, hεB, hsubB⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hBe
  have h1 := arcHit_right C hP hFam hA hz hnσ (s := 0) (b := εA) hεA
    (fun t h0 h1 => hsubA zteyi) by_simp_all
  have h2 := arcHit_right C hP hFam hB hz hσ (s := 0) (b := εB) hεB
    (fun t h0 h1 => hsubB zteyi) by_simp_all
  simp_all

/-- **An arc through a point of the chain off the chords contains in its interior the key of a
position at that point** (for a nonempty family). -/
theorem interior_of_arcHit (hne : F.Nonempty) {V : Set Point}
    {a b : ℝ} (harc : (chainModel C).IsArc F V a b) {x : Point} (hx : x ∈ C.set)
    (hxF : ∀ c ∈ F, x ∉ c) (hmem : x ∈ (chainModel C).arcSet a b) :
    ∃ p : ℕ, ∃ t : ℝ, p < (chainModel C).W.n ∧ 0 ≤ t ∧ t < 1 ∧
      sidePt (chainModel C).W p t = x ∧ sideInArc a b ztk := by
  zufjq
  obtain ⟨p, t, hp, ht0, ht1, hkey, rfl⟩ := hmem
  -- a key of a position at `x` is not a cut
  have hnocut : ∀ (q : ℕ) (s : ℝ), 0 ≤ s → s < 1 → sidePt (chainModel C).W q s =
      Geometry.lerp ztbkd ztbke t →
      ¬ (chainModel C).IsCut F ztej := by
    rintro q s hs0 hs1 hq ⟨c, hc, q', s', hatt, hk⟩
    obtain ⟨-, hs'0, hs'1, hin, -⟩ := hatt
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hs0 hs1 hs'0 hs'1 hk
    simp_all
  zucyq
  · -- the end of the walk edge: the start of the next one
    zucuj
    by_cases hlast : p + 1 < (chainModel C).W.n
    · have hpt : sidePt (chainModel C).W ztr 0 =
          Geometry.lerp ztbkd ztbke 1 := by
        zukow
        show (chainModel C).W.vtx ztr = (chainModel C).W.vtx ztwkm
        zulpj
      grind
    · exfalso
      have hp1 : p + 1 = (chainModel C).W.n := by_omega
      have hv : Geometry.lerp ztbkd ztbke 1 = C.slitTop := by
        zujgn
        show (C.sideWalk C.sideBeta).vtx ztwqw = C.slitTop
        have : ztr % (C.sideWalk C.sideBeta).n = 0 := by
          show ztr % (chainModel C).W.n = 0
          simp_all
        zukyt
      zvmyq at hx
      have := C.snd_le_top_of_mem_set hx
      zudbt
      zujca
  · have hnc := hnocut p t ht0 h1 rfl
    refine ⟨p, t, hp, ht0, h1, rfl, ?_⟩
    grind

/-- **The bridge from crossings to zipper edges.**  If two distinct regions face each other
across the chain, arcs of them at two spine positions meet at a point of the chain
(`ZipRel`). -/
theorem cross_zip (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF ztc Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr ztc Q N reg) (hA : ArcsOK ztc Q N reg)
    {A B : Set Point} (hAr : A ∈ (chainModel C).regions ztwjh)
    (hBr : B ∈ (chainModel C).regions ztwjh) (hAB : A ≠ B)
    (hcr : CrossAdj C A B) :
    ∃ p q, p < N.arcs.length ∧ q < N.arcs.length ∧ reg ztdvx = A ∧ reg (rgi N q) = B ∧
      ZipRel C Q N p q := by
  set F := N.F ztc Q
  have hFam : (chainModel C).ChordFamily Q F := hN.1
  zuoj
  obtain ⟨x, hx, σ, hσ, hAe, hBe⟩ := hcr
  -- the family is nonempty: otherwise there is a single region
  have hne : F.Nonempty := by
    by_contra hF
    zukpw
    obtain ⟨hfin, hcard, -⟩ := regionTree _ Q F hGM hFam
    zuczy

    simp_all
  have hxF := not_mem_chord_of_crossAdj C hFam.2.1 hAr hBr hσ hAe hBe
  obtain ⟨hitA, hitB⟩ := arcHit_of_crossAdj C hP hFam hAr hBr hx hσ hAe hBe
  -- the arcs of the two regions through `x`, located on the spine
  have locate : ∀ V, V ∈ (chainModel C).regions F → ArcHit C F V x →
      ∃ p, p < N.arcs.length ∧ reg ztdvx = V ∧ ∃ p₁ : ℕ, ∃ t₁ : ℝ,
        p₁ < (chainModel C).W.n ∧ 0 ≤ t₁ ∧ t₁ < 1 ∧ sidePt (chainModel C).W p₁ t₁ = x ∧
        sideInArc ztwlo ztwnk ztdhz := by
    intro V hV ⟨a, b, harc, hmem⟩
    obtain ⟨p₁, t₁, hp₁, ht₀, ht₁, hpt, hin⟩ := interior_of_arcHit C hne harc hx hxF hmem
    obtain ⟨r, hr, rfl⟩ := hR.2.2 V hV
    zubhi

    refine ⟨p, hp, ?_, p₁, t₁, hp₁, ht₀, ht₁, hpt, ?_⟩
    · show reg (N.arc ztbjk).reg = reg r
      simp_all
    · show sideInArc ((chainModel C).key Q (N.arc ztbjk).s)
        ((chainModel C).key Q (N.arc ztbjk).e) ztdhz
      simp_all
  obtain ⟨p, hp, hpA, p₁, t₁, hp₁, h10, h11, hpt₁, hin₁⟩ := locate A hAr hitA
  obtain ⟨q, hq, hqB, p₂, t₂, hp₂, h20, h21, hpt₂, hin₂⟩ := locate B hBr hitB
  exact ⟨p, q, hp, hq, hpA, hqB, p₁, p₂, t₁, t₂, hp₁, hp₂, h10, h11, h20, h21,
    hpt₁ ▸ hx, hpt₁.trans hpt₂.symm, hin₁, hin₂⟩
end OracleQ
open OracleBook
namespace OracleQ
def BookAdj (B : BookData) (u v : ℕ) : Prop :=
  ∃ d, d < 2 * B.E ∧ View.tail B.N ztbgk = u ∧ View.head B.N ztbgk = v

/-- **The graph of the book map** on its spine vertices. -/
def bookGraph (B : BookData) : SimpleGraph ztuyi where
  Adj u v := u ≠ v ∧ (BookAdj B u v ∨ BookAdj B v u)
  symm := ⟨by
    grind⟩
  loopless := ztpfk

/-- Spine-adjacent positions (the pair `u < v` is a spine edge). -/
def SpineAdj (N u v : ℕ) : Prop := v = u + 1 ∨ (u = 0 ∧ v + 1 = N)
variable {B : BookData} {u v : ℕ}
theorem bookAdj_view {v : View} (hv : B.ViewOK v) :
    BookAdj B (View.tail B.N v) zttdz := by
  obtain ⟨d, hd, hdv⟩ := BookData.exists_view hv
  exact ⟨d, hd, by zuozr, by zuozr⟩
theorem bookAdj_spineAdj (huv : u < v) (hv : v < B.N)
    (h : SpineAdj B.N u v) : BookAdj B u v ∨ BookAdj B v u := by
  rcases h with rfl | ⟨rfl, hN⟩
  · left
    have := bookAdj_view (B := B) (v := .spF u) (by show u < B.N; omega)
    zuhpl
    rwa [Nat.mod_eq_of_lt hv] at this
  · right
    have := bookAdj_view (B := B) (v := .spF v) by_tauto
    zuhpl
    simp_all
theorem bookGraph_adj_of_mem {c : ℕ × ℕ} (hc : c ∈ B.I ∨ c ∈ B.O)
    (h12 : c.1 < c.2) (h2 : c.2 < B.N) :
    (bookGraph B).Adj ⟨c.1, by_omega⟩ ⟨c.2, h2⟩ := by
  refine ⟨fun h => by_grind, Or.inl ?_⟩
  zunk
  · exact bookAdj_view (B := B) (v := .inP c) hc
  · exact bookAdj_view (B := B) (v := .outP c) hc
theorem bookGraph_adj_of_spine (huv : u < v) (hv : v < B.N)
    (h : SpineAdj B.N u v) : (bookGraph B).Adj ⟨u, by_omega⟩ ztbbl :=
  ⟨fun h => by_grind, bookAdj_spineAdj huv hv h⟩

/-- A reflexive-transitive closure of a symmetric relation is symmetric. -/
theorem rtg_symm {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (hr _ _ hbc)).trans ih

/-! ## The book data of a normal form -/
variable (C : Chain) (Q : Polygon) (N : NF)

/-- **Completeness of the inner page**: every arc is joined to the first arc of its region (by a
star chord or a spine edge). -/
def StarComplete (B : BookData) : Prop :=
  ∀ p, p < N.arcs.length → ∃ m, m < N.arcs.length ∧ rgi N m = rgi N p ∧
    (∀ q, q < N.arcs.length → rgi N q = rgi N p → m ≤ q) ∧
    (m = p ∨ (m, p) ∈ B.I ∨ SpineAdj B.N m p)

/-- **Completeness of the outer page**: arcs meeting at a point of the chain are joined (by a
zipper chord or a spine edge). -/
def ZipComplete (B : BookData) : Prop :=
  ∀ p q, p < q → q < N.arcs.length → ZipRel C Q N p q → ztkca ∈ B.O ∨ SpineAdj B.N p q

/-- **The requirements on the book data built by the preprocessing.** -/
structure GraphOK (B : BookData) : Prop where
  three_le : 3 ≤ B.N
  arcs_le : N.arcs.length ≤ B.N
  I_nodup : B.I.Nodup
  O_nodup : B.O.Nodup
  I_ok : ∀ c ∈ B.I, ChordOK B.N c
  O_ok : ∀ c ∈ B.O, ChordOK B.N c
  I_star : ∀ c ∈ B.I, StarOK N c
  O_zip : ∀ c ∈ B.O, ZipOK C Q N c
  I_complete : StarComplete N B
  O_complete : ZipComplete C Q N B
variable {C Q N}

/-- **The book data of the preprocessing is valid**, hence planar. -/
theorem valid_of_graphOK (hP : C.P.Simple) (hN : IsNF ztc Q N)
    (hne : (N.F ztc Q).Nonempty) {B : BookData} (hB : GraphOK C Q N B) : B.Valid :=
  ⟨hB.three_le, hB.I_nodup, hB.O_nodup, hB.I_ok, hB.O_ok,
    stars_nonCross hN ztxgi hne hB.I_star, zips_nonCross C hP hN hne hB.O_zip⟩

/-- The region of a node: the region of its arc, or `∅` for padding. -/
noncomputable def rgNode (reg : ℕ → Set Point) (N : NF) (B : BookData) (v : Fin B.N) :
    Set Point :=
  if v.1 < N.arcs.length then reg (rgi N v.1) else ∅

/-- **The nodes of a region are connected inside the region.** -/
theorem conn_of_graphOK (hN : IsNF ztc Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr ztc Q N reg) (hA : ArcsOK ztc Q N reg)
    {B : BookData} (hB : GraphOK C Q N B) (a b : Fin B.N)
    (hab : rgNode reg N B a = rgNode reg N B b) :
    Relation.ReflTransGen (fun u v => (bookGraph B).Adj u v ∧ rgNode reg N B u = rgNode reg N B a ∧
      rgNode reg N B v = rgNode reg N B a) a b := by
  zugyb
  have hnemp : ∀ p, p < A → reg ztdvx ≠ ∅ := by
    intro p hp h
    have hU : reg ztdvx ∈ (chainModel C).regions ztwjh :=
      hR.1 _ (hA.1 _ ztctk).1
    have hne' : (reg ztdvx).Nonempty := Chazelle.Chain.regionsIn_nonempty (D := (chainModel C).D) hU
    simp_all
  by_cases ha : a.1 < A <;> by_cases hb : b.1 < A
  · -- both arcs: through the first arc of the region
    have hr : rgi N a.1 = rgi N b.1 := by
      have h' : reg (rgi N a.1) = reg (rgi N b.1) := by
        unfold rgNode at hab; grind
      exact hR.2.1 _ _ (hA.1 _ (NFLoc.seq_lt hN ha)).1 (hA.1 _ (NFLoc.seq_lt hN hb)).1 h'
    obtain ⟨m, hm, hmr, hmin, hlink⟩ := hB.I_complete a.1 ha
    obtain ⟨m', hm', hm'r, hmin', hlink'⟩ := hB.I_complete b.1 hb
    have hmm : m = m' := le_antisymm (hmin m' hm' (hm'r.trans hr.symm))
      (hmin' m hm (hmr.trans hr))
    subst hmm
    have hmN : m < B.N := lt_of_lt_of_le hm hB.arcs_le
    let mv : Fin B.N := ⟨m, hmN⟩
    have hrg : ∀ v : Fin B.N, v.1 < A → rgi N v.1 = rgi N a.1 →
        rgNode reg N B v = rgNode reg N B a := by
      intro v hv h
      unfold rgNode; grind
    have hmv : rgNode reg N B mv = rgNode reg N B a := hrg mv hm hmr
    -- a node of the region is joined to `mv` by one edge (or equals it)
    have link : ∀ v : Fin B.N, v.1 < A → rgi N v.1 = rgi N a.1 →
        (m = v.1 ∨ zttsv ∈ B.I ∨ SpineAdj B.N m v.1) → m ≤ v.1 →
        mv = v ∨ ((bookGraph B).Adj mv v ∧ rgNode reg N B mv = rgNode reg N B a ∧
          rgNode reg N B v = rgNode reg N B a) := by
      intro v hv hvr hl hle
      rcases hl with h | h | h
      · grind
      · right
        have hc := hB.I_star _ h
        refine ⟨?_, hmv, hrg v hv hvr⟩
        exact bookGraph_adj_of_mem (c := zttsv) zteg hc.1 v.2
      · right
        have h3 := hB.three_le
        have hlt : m < v.1 := by rcases h with h | h <;> omega
        exact ⟨bookGraph_adj_of_spine hlt v.2 h, hmv, hrg v hv hvr⟩
    have la := link a ha rfl hlink (hmin a.1 ha rfl)
    have lb := link b hb hr.symm hlink' (hmin' b.1 hb rfl)
    have hsym : ∀ u v, (bookGraph B).Adj u v ∧ rgNode reg N B u = rgNode reg N B a ∧
        rgNode reg N B v = rgNode reg N B a → (bookGraph B).Adj v u ∧
        rgNode reg N B v = rgNode reg N B a ∧ rgNode reg N B u = rgNode reg N B a :=
      fun u v ⟨h1, h2, h3⟩ => ztrcp
    have p1 : Relation.ReflTransGen (fun u v => (bookGraph B).Adj u v ∧ rgNode reg N B u = rgNode reg N B a ∧
        rgNode reg N B v = rgNode reg N B a) a mv := by
      grind
    grind
  · zujvo

  · zujvo

  · -- both padding: along the spine
    have hpad : ∀ v : Fin B.N, ¬ v.1 < A → rgNode reg N B v = rgNode reg N B a := by
      intro v hv; unfold rgNode; grind
    have step : ∀ k, ∀ u : Fin B.N, ¬ u.1 < A → ∀ v : Fin B.N, v.1 = u.1 + k →
        Relation.ReflTransGen (fun u v => (bookGraph B).Adj u v ∧
          rgNode reg N B u = rgNode reg N B a ∧ rgNode reg N B v = rgNode reg N B a) u v := by
      zugoi
      induction k with
      | zero => intro u _ v hv; rw [Fin.ext (show v.1 = u.1 by omega)]
      | succ k ih =>
        intro u hu v hv
        have hwN : u.1 + k < B.N := by_omega
        let w : Fin B.N := ⟨u.1 + k, hwN⟩
        refine (ih u hu w rfl).tail ⟨?_, hpad w by_grind,
          hpad v by_omega⟩
        have hv' : v.1 = w.1 + 1 := by_omega
        have := bookGraph_adj_of_spine (B := B) (u := w.1) (v := v.1) by_omega v.2 (Or.inl hv')
        zufep
    rcases le_total a.1 b.1 with hle | hle
    · exact step ztbco a ha b by_omega
    · have := step zttev b hb a by_omega
      exact rtg_symm (fun u v ⟨h1, h2, h3⟩ => ztrcp) this

/-- **Regions facing each other across the chain have adjacent nodes.** -/
theorem cross_of_graphOK (hP : C.P.Simple) (hN : IsNF ztc Q N) {reg : ℕ → Set Point}
    (hR : RegionCorr ztc Q N reg) (hA : ArcsOK ztc Q N reg)
    {B : BookData} (hB : GraphOK C Q N B) (U V : Set Point)
    (hU : U ∈ (chainModel C).regions ztwjh)
    (hV : V ∈ (chainModel C).regions ztwjh) (hUV : U ≠ V)
    (hcr : CrossAdj C U V) :
    ∃ a b : Fin B.N, rgNode reg N B a = U ∧ rgNode reg N B b = V ∧ (bookGraph B).Adj a b := by
  obtain ⟨p, q, hp, hq, hpU, hqV, hz⟩ := cross_zip C hP hN hR hA hU hV hUV hcr
  have hpN : p < B.N := lt_of_lt_of_le hp hB.arcs_le
  have hqN : q < B.N := lt_of_lt_of_le hq hB.arcs_le
  refine ⟨ztopb, ztujg, by unfold rgNode; simp_all,
    by unfold rgNode; simp_all, ?_⟩
  have hpq : p ≠ q := fun h => hUV by_simp_all
  zuevo
  · rcases hB.O_complete p q hlt hq hz with h | h
    · exact bookGraph_adj_of_mem (c := ztkca) ztbho hlt hqN
    · exact bookGraph_adj_of_spine hlt hqN h
  · have hz' := hz.symm
    have : (bookGraph B).Adj ztujg ztopb := by
      rcases hB.O_complete q p hlt hp hz' with h | h
      · exact bookGraph_adj_of_mem (c := (q, p)) ztbho hlt hpN
      · exact bookGraph_adj_of_spine hlt hpN h
    tauto

/-! ## The map in memory -/

/-! ## From the arcs to the scanned edges -/
end OracleQ
namespace OracleQ
section Cand
variable {M : Model} {Q : Polygon} {N : NF}

/-- The next spine position (cyclically). -/
def succP (A p : ℕ) : ℕ := if p + 1 < A then p + 1 else 0

/-- The previous spine position (cyclically). -/
def predP (A p : ℕ) : ℕ := if p = 0 then A - 1 else p - 1
variable {A p : ℕ}
theorem predP_succP (hp : p < A) : predP A (succP A p) = p := by
  unfold succP predP
  grind
theorem succP_lt (hp : p < A) : succP A p < A := by unfold succP; grind
theorem predP_lt (hp : p < A) : predP A p < A := by unfold predP; grind
theorem succP_inj {A p q : ℕ} (hp : p < A) (hq : q < A) (h : succP A p = succP A q) : p = q := by
  have := congrArg (predP A) h
  rwa [predP_succP hp, predP_succP hq] at this
variable (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
include hN hGM hne
omit hGM hne in
theorem sk_mono {p q : ℕ} (hpq : p ≤ q) (hq : q < N.arcs.length) : sk M Q N p ≤ sk M Q N q :=
  NFLoc.seq_sorted hN hpq hq
omit hGM in
/-- The arc at a spine position is an arc of a nonempty family: its ends are distinct cuts. -/
theorem arc_facts {p : ℕ} (hp : p < N.arcs.length) :
    M.IsCut ztdu ztcja ∧ M.IsCut ztdu ztchs ∧ sk M Q N p ≠ ek M Q N p ∧
      (∀ x, sideInArc ztcja ztchs x → ¬ M.IsCut ztdu x) := by
  zueji
  obtain ⟨h1, h2, h3⟩ := WalkAx.arc_cuts hne harc
  exact ⟨h1, h2, h3, harc.2.2.2.2.2.1⟩

/-- **Distinct arcs have disjoint interiors.** -/
theorem interior_unique {p q : ℕ} (hp : p < N.arcs.length) (hq : q < N.arcs.length) {κ : ℝ}
    (h1 : sideInArc ztcja ztchs κ) (h2 : sideInArc ztkfh ztjus κ) :
    p = q := by
  by_contra hpq
  zuevo
  · have a := interior_lt_start hN hGM hne hlt hq h1
    have b := start_lt_interior hN hGM hne hlt hq h1 (by
      linarith [a, (isArc_sj hN hq).choose_spec.2.2.2.1])
    rcases last_interior hN hGM hne hlt hq h2 with c | c <;> linarith
  · have a := interior_lt_start hN hGM hne hlt hp h2
    have b := start_lt_interior hN hGM hne hlt hp h2 (by
      linarith [a, (isArc_sj hN hp).choose_spec.2.2.2.1])
    rcases last_interior hN hGM hne hlt hp h1 with c | c <;> linarith

/-- **Distinct arcs have distinct starts.** -/
theorem start_unique {p q : ℕ} (hp : p < N.arcs.length) (hq : q < N.arcs.length)
    (h : sk M Q N p = sk M Q N q) : p = q := by
  by_contra hpq
  zuevo
  · exact absurd h (starts_lt hN hGM hne hlt hq).ne
  · exact absurd h (starts_lt hN hGM hne hlt hp).ne'

/-- **The arc ending at a cut is followed by the arc starting there.** -/
theorem end_start_adj {p q : ℕ} (hp : p < N.arcs.length) (hq : q < N.arcs.length)
    (h : ek M Q N p = sk M Q N q) : q = succP N.arcs.length p := by
  zugyb
  zueah
  unfold succP
  zulsu
  · zubzg

    -- the arc `p` does not wrap
    have hnw : sk M Q N p < ek M Q N p := by
      zukr
      zueoy
    have hge : ek M Q N p ≤ sk M Q N r := by
      zux

      zueoy
    rcases eq_or_lt_of_le hge with e | e
    · exact (start_unique hN hGM hne hq hr (h.symm.trans e)).trans rfl
    · exfalso
      rcases le_or_gt q p with hqp | hqp
      · have := sk_mono hN hqp hp; linarith
      · have := sk_mono hN (show r ≤ q by omega) hq; linarith
  · have hpA : p + 1 = A := by_omega
    zujda
    · omega
    · have h0 : ztrzd := by_omega
      have hcr := (arc_facts hN hne h0).1
      have h0p := starts_lt hN hGM hne hp0 hp
      have hqp := sk_mono hN (show q ≤ p by omega) hp
      have hwr : ¬ sk M Q N p < ek M Q N p := by_simp_all
      have hlt : ek M Q N p < sk M Q N p := by_grind
      have hle : ek M Q N p ≤ sk M Q N 0 := by
        zux

        zueoy
      have h0q := sk_mono hN (Nat.zero_le q) hq
      exact start_unique hN hGM hne hq h0 by_linarith

/-- **Distinct arcs have distinct ends** (every cut starts an arc, `arcCover`). -/
theorem end_unique {p q : ℕ} (hp : p < N.arcs.length) (hq : q < N.arcs.length)
    (h : ek M Q N p = ek M Q N q) : p = q := by
  zumq

  zufkm
  have hsr : ztlbg := by
    show M.key Q (N.arc ztnne).s = _
    simp_all
  have e1 := end_start_adj hN hGM hne hp hr hsr.symm
  have e2 := end_start_adj hN hGM hne hq hr by_simp_all
  exact succP_inj hp hq (e1.symm.trans e2)

/-- **Candidate arcs.**  If the key `κ` is in the closed arc at spine position `t`, and `j` is an
answer of double identification for `κ`, then `t` is `j`, its successor or its predecessor. -/
theorem candidate {t j : ℕ} (ht : t < N.arcs.length) (hj : j < N.arcs.length) {κ : ℝ}
    (hin : sideInArc (sk M Q N t) (ek M Q N t) κ ∨ κ = sk M Q N t ∨ κ = ek M Q N t)
    (hloc1 : ¬ M.IsCut ztdu κ → N.F M Q = ∅ ∨ sideInArc ztevn zteru κ)
    (hloc2 : M.IsCut ztdu κ → sk M Q N j = κ ∨ ek M Q N j = κ) :
    t = j ∨ t = succP N.arcs.length j ∨ t = predP N.arcs.length j := by
  obtain ⟨hct, hcte, -, hfree⟩ := arc_facts hN hne ht
  rcases hin with h | h | h
  · have hnc := hfree κ h
    rcases hloc1 hnc with h' | h'
    · simp_all
    · exact Or.inl (interior_unique hN hGM hne ht hj h h')
  · zujdu
    · exact Or.inl (start_unique hN hGM hne ht hj by_simp_all)
    · exact Or.inr (Or.inl (end_start_adj hN hGM hne hj ht ztvro))
  · zujdu
    · have := end_start_adj hN hGM hne ht hj ztqoz
      zulw
      rw [this, predP_succP ht]
    · exact Or.inl (end_unique hN hGM hne ht hj ztqoz)
end Cand

/-! ## Scanned edges -/
section Scan
variable (C : Chain) (Q : Polygon) (N : NF)

/-- The number of walk edges scanned for the arc at spine position `p`, minus one: from the edge
before the start edge to the edge after the end edge (the whole walk for a wrapping arc). -/
noncomputable def scanLen (p : ℕ) : ℕ :=
  (if sk ztc Q N p < ek ztc Q N p
    then (N.arc ztmh).e.edge - (N.arc ztmh).s.edge
    else (N.arc ztmh).e.edge + (chainModel C).W.n - (N.arc ztmh).s.edge) + 2

/-- The `k`-th scanned walk edge of the arc at spine position `p`. -/
def scanIdx (n : ℕ) (N : NF) (p k : ℕ) : ℕ := ((N.arc ztmh).s.edge + n - 1 + k) % n

/-- **The scanned points** of the arc at spine position `p`: the tour edges among the scanned
walk edges. -/
noncomputable def scanSet (p : ℕ) : Set Point :=
  {x | ∃ k, k ≤ scanLen C Q N p ∧ ∃ i, i < 2 * C.m ∧
    scanIdx (chainModel C).W.n N p k = i + 6 ∧
    x ∈ Chazelle.segment ztnjy ztyoq}
theorem scanSet_subset (p : ℕ) : scanSet C Q N p ⊆ C.set := by
  rintro x ⟨k, -, i, hi, -, hx⟩
  unfold Chain.sideTour at hx
  zuidg
  · have hk : C.sideIdx C.sideBeta i < C.m := by
      have := C.sideIdx_le C.sideBeta ztg; omega
    refine ztrah
    zumlb
    simp_all
  · have hk : C.sideIdx C.sideBeta ztg < C.m := by
      have := C.sideIdx_le C.sideBeta i; omega
    refine ztrah
    rw [C.chainEdge_eq, h]
    zufks
    exact ⟨1 - s, by_linarith, by_linarith, by_grind⟩

/-- **The scanned edges cover the chain points of an arc**: a point of the chain on the closed
point set of the arc at spine position `p` (whose ends are proper positions) lies on a scanned
tour edge. -/
theorem mem_scan {p : ℕ}
    (hs : ProperPos ztc Q Q.n (N.arc ztmh).s)
    (he : ProperPos ztc Q Q.n (N.arc ztmh).e)
    (hse : (N.arc ztmh).s.edge < (chainModel C).W.n)
    (hee : (N.arc ztmh).e.edge < (chainModel C).W.n)
    {x : Point} (hxC : x ∈ C.set)
    (hx : x ∈ (chainModel C).arcSet ztwlo ztwnk) :
    x ∈ scanSet C Q N p := by
  set n := (chainModel C).W.n with hn
  have hn7 : ztppf := walk_n C
  zudvt

  set a := sk _ Q N p with ha
  set b := ek _ Q N p with hb
  have hak : a = se + (chainModel C).param Q (N.arc _).s := rfl
  have hbk : b = ee + (chainModel C).param Q (N.arc _).e := rfl
  obtain ⟨hs0, hs1, -⟩ := hs
  obtain ⟨he0, he1, -⟩ := he
  obtain ⟨q, t, hq, ht0, ht1, hkey, rfl⟩ := hx
  -- normalise to a parameter in `[0, 1)`
  obtain ⟨q', t', hq', ht0', ht1', hpt, hkey'⟩ : ∃ q' t', q' < n ∧ 0 ≤ t' ∧ t' < 1 ∧
      sidePt (chainModel C).W q' t' = Geometry.lerp ztosl ztosm t ∧
      (q' : ℝ) + t' = q + t := by
    zucyq
    · zucuj
      by_cases hlast : q + 1 < n
      · refine ⟨q + 1, 0, hlast, le_rfl, one_pos, ?_, by_simp⟩
        zukow
        show (chainModel C).W.vtx _ = (chainModel C).W.vtx _
        zulpj
      · exfalso
        have hq1 : q + 1 = n := by_omega
        have hv : Geometry.lerp ztosl ztosm 1 = C.slitTop := by
          zujgn
          show (C.sideWalk C.sideBeta).vtx ztwtw = C.slitTop
          have : ztfo % (C.sideWalk C.sideBeta).n = 0 := by
            show ztfo % n = 0
            simp_all
          zukyt
        zvmyq at hxC
        have := C.snd_le_top_of_mem_set hxC
        zudbt
        zujca
    · exact ⟨q, t, hq, ht0, h1, rfl, rfl⟩
  rw [← hkey'] at hkey
  zvnbr at hxC ⊢
  -- the edge `q'` is among the scanned ones, at index `k ≥ 1`
  have hq'R : (q' : ℝ) ≤ q' + t' := by_linarith
  have hfl : ∀ (e : ℕ) (u : ℝ) (v : ℕ) (w : ℝ), 0 ≤ u → u < 1 → 0 ≤ w → w < 1 →
      (e : ℝ) + u ≤ v + w → e ≤ v := by
    intro e u v w hu hu1 hw hw1 h
    zux

    have : (v : ℝ) + 1 ≤ e := by exact_mod_cast hc
    linarith
  obtain ⟨k, hk1, hkl, hidx⟩ : ∃ k, 1 ≤ k ∧ k + 1 ≤ scanLen C Q N p ∧
      scanIdx n N p k = q' := by
    unfold scanLen scanIdx
    have hscan := by_omega
    zuul
    · rw [ite_eq_left hab]
      have hk' : a ≤ q' + t' ∧ (q' : ℝ) + t' ≤ b := by
        zulux

      zueqb
      zueqc
      refine ztkml
      rw [show se + n - 1 + ztquw = q' + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hq']
    · rw [ite_eq_right hab]
      have hk' : a ≤ q' + t' ∨ (q' : ℝ) + t' ≤ b := by
        zulux

      rcases hk' with h | h
      · zueqb
        refine ztkml
        rw [show se + n - 1 + ztquw = q' + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hq']
      · zueqc
        refine ⟨q' + n - se + 1, by_omega, by_omega, ?_⟩
        rw [show se + n - 1 + (q' + n - se + 1) = q' + n + n by omega, Nat.add_mod_right,
          Nat.add_mod_right, Nat.mod_eq_of_lt hq']
  -- the edge is a tour edge (or the closing vertex, the top)
  rw [hn7] at hq'
  rcases pos_on_chain C hq' ht0' ht1' hxC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨k, by_omega, q' - 6, by_omega, by_simp_all, ?_⟩
    have := C.sidePt_tour C.sideBeta (i := q' - 6) by_omega t'
    rw [show q' - 6 + 6 = q' by omega] at this
    show sidePt ztcs q' t' ∈ _
    zubk
    exact Geometry.lerp_mem_segment _ _ ht0' ht1'.le
  · zufcz
    refine ⟨k - 1, by_omega, 2 * C.m - 1, by have := C.one_le; omega, ?_, ?_⟩
    · unfold scanIdx at hidx ⊢
      have hkn : (se + n - 1 + ztie) % n = (se + n - 1 + k + n - 1) % n := by
        rw [show se + n - 1 + k + n - 1 = se + n - 1 + ztie + n by omega, Nat.add_mod_right]
      rw [hkn, Nat.add_sub_assoc by_omega, Nat.add_mod, hidx, hn7]
      have := C.one_le
      rw [Nat.mod_eq_of_lt (show 2 * C.m + 7 - 1 < 2 * C.m + 7 by omega),
        show 2 * C.m + 6 + (2 * C.m + 7 - 1) = (2 * C.m - 1 + 6) + ztz by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    · show sidePt ztcs _ 0 ∈ _
      rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour C.sideBeta le_rfl,
        show 2 * C.m - 1 + 1 = 2 * C.m by have := C.one_le; omega]
      zuisp
end Scan

/-! ## The empty family -/

/-- With the empty family, a normal form has at most one arc. -/
theorem arcs_le_one_of_empty {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N)
    (hGM : GoodModel M) (hF : N.F M Q = ∅) : N.arcs.length ≤ 1 := by
  zuzl
  obtain ⟨-, hcard, -⟩ := regionTree M Q ztdu hGM hN.1
  zuczy

  zux

  have h0 := hA.1 0 by_omega
  have h1 := hA.1 1 by_omega
  have hr0 : reg (N.arc 0).reg = U := by
    have := hR.1 _ h0.1; simp_all
  have hr1 : reg (N.arc 1).reg = U := by
    have := hR.1 _ h1.1; simp_all
  have hreg := hR.2.1 _ _ h0.1 h1.1 (hr0.trans hr1.symm)
  have hk : ∀ j, j < N.arcs.length → M.key Q (N.arc j).s = 0 := by
    zun
    rcases (hA.1 j hj).2.2.2.2.2.1 with ⟨hc, -⟩ | ⟨-, h, -⟩
    · obtain ⟨c, hc, -⟩ := hc; simp_all
    omega
  have := hA.2.1 0 1 by_omega by_omega hreg by_grind
  omega
