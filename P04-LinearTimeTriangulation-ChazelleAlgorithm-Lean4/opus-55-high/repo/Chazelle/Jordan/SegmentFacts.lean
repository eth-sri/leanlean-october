module

public import Chazelle.MacT
public import Chazelle.Spec
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.LocallyConstant.Basic
public import Chazelle.Core.Lemma41Cover
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Data.Nat.ModEq
public import Chazelle.Programs.Tactics

namespace Chazelle.Jordan
public section
open Set
variable {u v p : Point}
/-- Membership in a segment, unfolded. -/
theorem mem_segment_iff :
    p ∈ segment u v ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = ztxye :=
  Iff.rfl

/-- The first endpoint lies on the segment. -/
theorem left_mem_segment (u v : Point) : u ∈ segment u v :=
  ⟨0, le_rfl, zero_le_one, by_simp⟩

/-- The second endpoint lies on the segment. -/
theorem right_mem_segment (u v : Point) : v ∈ segment u v :=
  ⟨1, zero_le_one, le_rfl, by_simp⟩
theorem segment_subset_comm {u v : Point} : segment u v ⊆ segment v u := by
  rintro p ⟨t, ht0, ht1, rfl⟩
  refine ztlva
  grind

/-- A segment does not depend on the order of its endpoints. -/
theorem segment_comm (u v : Point) : segment u v = segment v u :=
  Subset.antisymm segment_subset_comm segment_subset_comm

/-- A point of a segment with `u.1 < v.1` has abscissa between the endpoints and lies on the
line through them (division-free form). -/
theorem mem_segment_iff_of_lt (huv : u.1 < v.1) :
    p ∈ segment u v ↔
      u.1 ≤ p.1 ∧ p.1 ≤ v.1 ∧ ztkcb * ztmu = ztgv * zttvj := by
  constructor
  · zuly
    zuixu
    zusk
    · simp_all
    · zubi
      nlinarith
    grind
  · rintro ⟨h0, h1, hl⟩
    zuixu
    refine ⟨zttvj / ztmu, div_nonneg by_linarith hd.le,
      (div_le_one hd).2 by_linarith, ?_⟩
    grind

/-- Membership in a vertical segment: same abscissa and ordinate between the endpoints. -/
theorem mem_segment_of_vertical (huv : u.1 = v.1) (hp : p.1 = u.1)
    (h0 : u.2 ≤ p.2) (h1 : p.2 ≤ v.2) : p ∈ segment u v := by
  by_cases hd : u.2 = v.2
  · zumkq
    grind
  · have hd' : ztrzp := sub_pos.2 (lt_of_le_of_ne (h0.trans h1) hd)
    refine ⟨ztkcb / ztgv, div_nonneg by_linarith hd'.le,
      (div_le_one hd').2 by_linarith, ?_⟩
    grind

/-- A point of a vertical segment has the common abscissa of the endpoints. -/
theorem fst_eq_of_mem_segment_vertical (huv : u.1 = v.1) (hp : p ∈ segment u v) :
    p.1 = u.1 := by
  zuceb
  simp_all

/-- A segment is the continuous image of `[0,1]`, hence compact. -/
theorem isCompact_segment (u v : Point) : IsCompact ztuac := by
  have : segment u v =
      (fun t : ℝ => (ztxye : Point)) '' Icc 0 1 := by
    zufj
    simp only [mem_segment_iff, mem_image, mem_Icc]
    grind
  zubk
  exact isCompact_Icc.image ztepq

/-- A segment is a closed set. -/
theorem isClosed_segment (u v : Point) : IsClosed ztuac :=
  (isCompact_segment u v).isClosed

/-- The boundary of a polygon as a finite union of edges. -/
theorem boundary_eq_biUnion (P : Polygon) :
    P.boundary = ⋃ i ∈ Finset.range P.n, P.edge i := by
  zufj
  simp [Polygon.boundary]

/-- Every edge of a polygon is closed. -/
theorem isClosed_edge (P : Polygon) (i : ℕ) : IsClosed (P.edge i) :=
  isClosed_segment _ _

/-- The boundary of a polygon is a closed set (a finite union of closed segments). -/
theorem isClosed_boundary (P : Polygon) : IsClosed P.boundary := by
  rw [boundary_eq_biUnion]
  exact isClosed_biUnion_finset fun i _ => isClosed_edge P i

/-- The complement of the boundary of a polygon is open. -/
theorem isOpen_boundary_compl (P : Polygon) : IsOpen P.boundaryᶜ :=
  (isClosed_boundary P).isOpen_compl
end
@[expose] public section
open Set Filter Topology

/-! ### Definitions -/

/-- The edge `u v` straddles the abscissa of `z` (half-open rule): exactly one endpoint has
abscissa `≤ z.1`. -/
def straddles (z u v : Point) : Prop :=
  (u.1 ≤ z.1 ∧ z.1 < v.1) ∨ (v.1 ≤ z.1 ∧ z.1 < u.1)

/-- The edge `u v` crosses the upward vertical ray from `z`: it straddles the abscissa of `z`
and `z` is strictly below the line through `u` and `v` at abscissa `z.1` (division-free form,
oriented left to right). -/
def crosses (z u v : Point) : Prop :=
  (u.1 ≤ z.1 ∧ z.1 < v.1 ∧ ztoko * ztmu < ztgv * ztuew) ∨
  (v.1 ≤ z.1 ∧ z.1 < u.1 ∧ ztuex * ztucm < zthks * ztokm)
noncomputable instance instDecidableStraddles (z u v : Point) : Decidable (straddles z u v) :=
  inferInstanceAs ztdta
noncomputable instance instDecidableCrosses (z u v : Point) : Decidable ztrnx :=
  inferInstanceAs ztdta

/-- The crossing bit of the edge `u v` at `z`. -/
noncomputable def crossBit (z u v : Point) : Bool := decide ztrnx

/-- The crossing indicator of the edge `u v` at `z`, in `ZMod 2`. -/
noncomputable def crossInd (z u v : Point) : ZMod 2 := if crosses z u v then 1 else 0

/-- Indicator (in `ZMod 2`) that the point `w` has the abscissa of `z` and lies strictly above
`z`.  This is the change of the crossing bit of an edge with endpoint `w` when the test point
moves to the left across the abscissa of `w`. -/
noncomputable def aboveInd (z w : Point) : ZMod 2 := if w.1 = z.1 ∧ z.2 < w.2 then 1 else 0

/-- The number of edges of `P` crossing the upward ray from `z`, modulo 2. -/
noncomputable def crossSum (P : Polygon) (z : Point) : ZMod 2 :=
  ∑ i ∈ Finset.range P.n, crossInd z ztdn ztwir

/-- The crossing parity of `z` with respect to `P`: `true` iff an odd number of edges cross
the upward ray from `z`. -/
noncomputable def parity (P : Polygon) (z : Point) : Bool := decide (crossSum P z = 1)

/-! ### Basic lemmas -/
variable {z u v : Point} (x : ZMod 2) {P : Polygon}
/-- `crosses` does not depend on the direction of the edge. -/
theorem crosses_comm : crosses z u v ↔ crosses z v u :=
  Or.comm
theorem crosses_straddles (h : crosses z u v) : straddles z u v := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · tauto
  tauto

/-- For an edge oriented left to right, `crosses` reduces to its first disjunct. -/
theorem crosses_iff_of_lt (huv : u.1 < v.1) :
    crosses z u v ↔
      u.1 ≤ z.1 ∧ z.1 < v.1 ∧ ztoko * ztmu < ztgv * ztuew := by
  constructor
  · rintro (h | ⟨h1, h2, -⟩)
    · zubh
    grind
  tauto

/-- A vertical (or degenerate) edge never crosses. -/
theorem not_crosses_of_eq (huv : u.1 = v.1) : ¬ crosses z u v := by
  rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> linarith

/-- An edge entirely to the right of `z` does not cross. -/
theorem not_crosses_of_lt (hu : z.1 < u.1) (hv : z.1 < v.1) :
    ¬ crosses z u v := by
  rintro (⟨h1, -, -⟩ | ⟨h1, -, -⟩) <;> linarith

/-- An edge entirely at or to the left of `z` does not cross. -/
theorem not_crosses_of_le (hu : u.1 ≤ z.1) (hv : v.1 ≤ z.1) :
    ¬ crosses z u v := by
  rintro (⟨-, h2, -⟩ | ⟨-, h2, -⟩) <;> linarith

/-- An edge entirely strictly below `z` does not cross. -/
theorem not_crosses_of_below (hu : u.2 < z.2) (hv : v.2 < z.2) :
    ¬ crosses z u v := by
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · zueib
  · zueic
theorem crossInd_comm : crossInd z u v = crossInd z v u := by
  simp only [crossInd]
  exact if_congr crosses_comm rfl rfl
theorem crossInd_of_crosses (h : crosses z u v) : crossInd z u v = 1 :=
  ite_eq_left h
theorem crossInd_of_not_crosses (h : ¬ crosses z u v) : crossInd z u v = 0 :=
  ite_eq_right h
theorem aboveInd_of_ne {z w : Point} (h : w.1 ≠ z.1) : aboveInd z w = 0 := by
  simp [aboveInd, h]
theorem aboveInd_of_le {z w : Point} (h : w.2 ≤ z.2) : aboveInd z w = 0 := by
  simp [aboveInd, not_lt.2 h]
theorem aboveInd_of_lt {z w : Point} (h1 : w.1 = z.1) (h2 : z.2 < w.2) : aboveInd z w = 1 := by
  simp [aboveInd, h1, h2]
theorem zmod_two_add_self : x + x = 0 := by
  grind
theorem zmod_two_add_one_ne : x + 1 ≠ x := by
  simp
theorem zmod_two_decide_eq_one_iff (a b : ZMod 2) :
    (decide (a = 1) = decide (b = 1)) ↔ a = b := by
  revert a b; decide

/-- Two points have the same parity iff they have the same crossing sum. -/
theorem parity_eq_iff {z z' : Point} :
    parity P z = parity P z' ↔ crossSum P z = crossSum P z' :=
  zmod_two_decide_eq_one_iff _ _
theorem parity_eq_false_iff {z : Point} :
    parity P z = false ↔ crossSum P z = 0 := by
  simp only [parity, decide_eq_false_iff_not]
  generalize crossSum P z = a
  revert a
  decide

/-! ### Local behaviour of a single edge -/

/-- For a vertical edge and a point off it, the two endpoint contributions cancel. -/
theorem aboveInd_add_aboveInd_of_eq (huv : u.1 = v.1) (hz : z ∉ segment u v) :
    aboveInd z u + aboveInd z v = 0 := by
  by_cases hu : u.1 = z.1
  · have hv : v.1 = z.1 := by_simp_all
    by_cases h1 : z.2 < u.2 <;> by_cases h2 : z.2 < v.2
    · rw [aboveInd_of_lt hu h1, aboveInd_of_lt hv h2]; decide
    · exact absurd (mem_segment_of_vertical huv.symm hv.symm ztkbn h1.le)
        ztqwa
    · exact absurd (mem_segment_of_vertical huv hu.symm ztmmr h2.le) hz
    · rw [aboveInd_of_le ztmmr, aboveInd_of_le ztkbn]; decide
  · rw [aboveInd_of_ne hu, aboveInd_of_ne by_simp_all]; decide

/-- The affine function whose sign decides "below the line through `u` and `v`". -/
theorem continuous_lineFun (u v : Point) :
    Continuous fun z' : Point => ztueq * ztmu - ztgv * ztuep := by
  fun_prop

/-- Local behaviour of the crossing indicator of a left-to-right edge near a point off it. -/
theorem crossInd_eventually_of_lt (huv : u.1 < v.1) (hz : z ∉ segment u v) :
    ∀ᶠ z' in 𝓝 z, crossInd z' u v =
      crossInd z u v + if z'.1 < z.1 then aboveInd z u + aboveInd z v else 0 := by
  set L : Point → ℝ := fun z' => ztueq * ztmu - ztgv * ztuep with hL
  have hLc := continuous_lineFun u v
  have hLt : Tendsto L _ _ := hLc.tendsto z
  have hfst : Tendsto (fun z' : Point => z'.1) (𝓝 z) _ := continuous_fst.tendsto z
  have hcr : ∀ z' : Point, crosses z' u v ↔ u.1 ≤ z'.1 ∧ z'.1 < v.1 ∧ L z' < 0 := by
    intro z'
    zuhkw
    simp_all
  have hvz := huv.ne'
  rcases lt_trichotomy z.1 u.1 with hA | hB | hC
  · -- z strictly to the left of the edge
    filter_upwards [hfst.eventually_lt_const hA] with z' hz'
    rw [crossInd_of_not_crosses by_simp_all,
      crossInd_of_not_crosses by_simp_all,
      aboveInd_of_ne hA.ne', aboveInd_of_ne by_grind]
    simp
  · -- z on the abscissa of u
    have hzu2 : z.2 ≠ u.2 := by
      zuq
      apply hz
      have : z = u := by_grind
      zvmwk; exact left_mem_segment u v
    have hLz : L z = ztoko * ztmu := by_simp_all
    zuhet
    have hav : aboveInd z v = 0 := aboveInd_of_ne by_simp_all
    rcases lt_or_gt_of_ne hzu2 with h1 | h1
    · -- u above z: the bit is 1 at and to the right of z, 0 to the left
      zudyk
      have hau := aboveInd_of_lt hB.symm h1
      have hcz : crosses z u v := by_simp_all
      filter_upwards [hfst.eventually_lt_const (hB ▸ huv), hLt.eventually_lt_const hLneg]
        with z' hz'1 hz'2
      rw [crossInd_of_crosses hcz, hau, hav]
      zufre
      · rw [crossInd_of_not_crosses by_simp_all,
          ite_eq_left hlt]
        decide
      · rw [crossInd_of_crosses by_simp_all, ite_eq_right hlt]
        decide
    · -- u below z: the bit is 0 near z
      zujzm
      have hau := aboveInd_of_le h1.le
      zuhuu
      rw [crossInd_of_not_crosses by_grind,
        crossInd_of_not_crosses by_grind,
        hau, hav]
      simp
  · rcases lt_trichotomy z.1 v.1 with hC1 | hD | hE
    · -- strictly between the abscissae of the endpoints
      have hLz : L z ≠ 0 := by
        zuq
        apply hz
        zuhna
        grind
      have hau := aboveInd_of_ne hC.ne
      have hav := aboveInd_of_ne hC1.ne'
      rw [hau, hav]
      rcases lt_or_gt_of_ne hLz with h1 | h1
      · filter_upwards [hfst.eventually_const_lt hC, hfst.eventually_lt_const hC1,
          hLt.eventually_lt_const h1] with z' hz'1 hz'2 hz'3
        rw [crossInd_of_crosses by_grind,
          crossInd_of_crosses by_grind]
        simp
      · filter_upwards [hLt.eventually_const_lt h1] with z' hz'
        rw [crossInd_of_not_crosses by_grind,
          crossInd_of_not_crosses by_grind]
        simp
    · -- z on the abscissa of v
      have hzv2 : z.2 ≠ v.2 := by
        zuq
        apply hz
        have : z = v := by_grind
        zvmwk; exact right_mem_segment u v
      have hLz : L z = ztuex * ztmu := by_grind
      zuhet
      have hau : aboveInd z u = 0 := aboveInd_of_ne by_grind
      have hcz : ¬ crosses z u v := by_simp_all
      rcases lt_or_gt_of_ne hzv2 with h1 | h1
      · -- v above z: the bit is 1 to the left of z, 0 at and to the right
        zudyk
        have hav := aboveInd_of_lt hD.symm h1
        filter_upwards [hfst.eventually_const_lt hC, hLt.eventually_lt_const hLneg]
          with z' hz'1 hz'2
        rw [crossInd_of_not_crosses hcz, hau, hav]
        zufre
        · rw [crossInd_of_crosses by_grind, ite_eq_left hlt]
          decide
        · rw [crossInd_of_not_crosses by_grind,
            ite_eq_right hlt]
          decide
      · -- v below z: the bit is 0 near z
        zujzm
        have hav := aboveInd_of_le h1.le
        zuhuu
        rw [crossInd_of_not_crosses by_grind,
          crossInd_of_not_crosses hcz, hau, hav]
        simp
    · -- z strictly to the right of the edge
      filter_upwards [hfst.eventually_const_lt hE] with z' hz'
      rw [crossInd_of_not_crosses by_grind,
        crossInd_of_not_crosses by_grind,
        aboveInd_of_ne hC.ne, aboveInd_of_ne hE.ne]
      simp

/-- **Local behaviour of one edge.**  For `z` off the edge `u v`, the crossing indicator at a
nearby point `z'` is the indicator at `z`, plus, when `z'` is strictly to the left of `z`,
the number (mod 2) of endpoints of the edge that have abscissa `z.1` and lie above `z`.  In
particular the bit is unchanged to the right of `z` and above/below `z`. -/
theorem crossInd_eventually (hz : z ∉ segment u v) :
    ∀ᶠ z' in 𝓝 z, crossInd z' u v =
      crossInd z u v + if z'.1 < z.1 then aboveInd z u + aboveInd z v else 0 := by
  rcases lt_trichotomy u.1 v.1 with h | h | h
  · exact crossInd_eventually_of_lt h hz
  · have h0 := aboveInd_add_aboveInd_of_eq h hz
    filter_upwards with z'
    rw [crossInd_of_not_crosses ztwad, crossInd_of_not_crosses ztwad,
      h0]
    simp
  · have hz' := segment_comm u v ▸ hz
    filter_upwards [crossInd_eventually_of_lt h hz'] with z' hz'
    rw [crossInd_comm, hz', ← crossInd_comm, add_comm (aboveInd z v)]

/-! ### Telescoping around the closed walk -/

/-- Cyclic reindexing of a sum over `range n`. -/
theorem sum_range_succ_mod {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f (ztg % n) = ∑ i ∈ Finset.range n, f i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ' f, Nat.mod_self]
    zucr
    zufql
    zug
    zucpk
    zuey

/-- The endpoint contributions telescope around the closed walk. -/
theorem sum_aboveInd_edges (P : Polygon) (z : Point) :
    ∑ i ∈ Finset.range P.n, (aboveInd z ztdn + aboveInd z ztwir) = 0 := by
  rw [Finset.sum_add_distrib, sum_range_succ_mod (fun i => aboveInd z _) P.n]
  grind

/-- **Local constancy of the crossing sum** off the boundary. -/
theorem crossSum_eventually_eq (P : Polygon) {z : Point} (hz : z ∉ P.boundary) :
    ∀ᶠ z' in 𝓝 z, crossSum P z' = crossSum P z := by
  have h : ∀ i ∈ Finset.range P.n, ∀ᶠ z' in 𝓝 z,
      crossInd z' _ _ =
        crossInd z _ ztwir +
          if z'.1 < z.1 then aboveInd z _ + aboveInd z _ else 0 :=
    fun i hi => crossInd_eventually fun hmem => hz ⟨i, Finset.mem_range.1 hi, hmem⟩
  rw [← Filter.eventually_all_finset] at h
  filter_upwards [h] with z' hz'
  zulbm
  rw [Finset.sum_congr rfl hz', Finset.sum_add_distrib]
  zufre
  · simp only [ite_eq_left hlt]
    rw [sum_aboveInd_edges, add_zero]
  simp_all

/-- **Local constancy of the parity** off the boundary. -/
theorem parity_eventually_eq (P : Polygon) {z : Point} (hz : z ∉ P.boundary) :
    ∀ᶠ z' in 𝓝 z, parity P z' = parity P z := by
  filter_upwards [crossSum_eventually_eq P hz] with z' hz'
  exact parity_eq_iff.2 hz'

/-- The parity is continuous (into the discrete space `Bool`) on the complement of the
boundary. -/
theorem continuousOn_parity (P : Polygon) : ContinuousOn (parity P) P.boundaryᶜ := by
  rw [(isOpen_boundary_compl P).continuousOn_iff]
  zugh
  exact continuousAt_const.congr_of_eventuallyEq (parity_eventually_eq P hz)

/-- **Constancy on connected sets**: the parity is constant on every preconnected set avoiding
the boundary. -/
theorem parity_eq_of_isPreconnected (P : Polygon) {S : Set Point} (hS : IsPreconnected S)
    (hSb : S ⊆ P.boundaryᶜ) {x y : Point} (hx : x ∈ S) (hy : y ∈ S) :
    parity P x = parity P y :=
  hS.constant ((continuousOn_parity P).mono hSb) hx hy

/-! ### Flip across an edge -/

/-- Crossing a non-vertical edge vertically at a non-endpoint point flips its bit: for every
`ε > 0`, the point above does not cross, the point below does, and neither lies on the edge. -/
theorem crossInd_flip_edge (huv : u.1 ≠ v.1) (hz : z ∈ segment u v)
    (hzu : z ≠ u) (hzv : z ≠ v) {ε : ℝ} (hε : 0 < ε) :
    ztgd ∉ segment u v ∧ ztfr ∉ segment u v ∧
      crossInd ztgd u v + 1 = crossInd ztfr u v := by
  -- reduce to the left-to-right orientation
  suffices key : ∀ u v : Point, u.1 < v.1 → z ∈ segment u v → z ≠ u → z ≠ v →
      ztgd ∉ segment u v ∧ ztfr ∉ segment u v ∧
        crossInd ztgd u v + 1 = crossInd ztfr u v by
    rcases lt_or_gt_of_ne huv with h | h
    · exact key u v h hz hzu hzv
    · obtain ⟨h1, h2, h3⟩ := key v u h ztqwa hzv hzu
      zvnln at h1 h2
      rw [crossInd_comm, h3, crossInd_comm]
      grind
  intro u v huv hz hzu hzv
  rw [mem_segment_iff_of_lt huv] at hz
  obtain ⟨h0, h1, hl⟩ := hz
  zuhet
  have h0' : u.1 < z.1 := by
    zukkm
    · zubh
    · exfalso; apply hzu
      have : z.2 = u.2 := by
        grind
      grind
  have h1' : z.1 < v.1 := by
    zucop
    · zubh
    · exfalso; apply hzv
      have : z.2 = v.2 := by
        grind
      grind
  zusk
  · zuhna
    zubcb

  · zuhna
    zubcb

  · have hnc : ¬ crosses ztgd u v := by
      zuhkw
      zubcb

    have hc : crosses ztfr u v := by
      zuhkw
      refine ⟨h0, h1', ?_⟩
      zubi
      nlinarith [mul_pos hε hd]
    rw [crossInd_of_not_crosses hnc, crossInd_of_crosses hc, zero_add]

/-- **Flip.**  Let `z` be a point of edge `i` of `P` that is not an endpoint of that edge,
with edge `i` non-vertical and `z` on no other edge.  Then for all sufficiently small `ε > 0`
the points `(z.1, z.2 ± ε)` lie off the boundary and have different parities. -/
theorem parity_flip (P : Polygon) {i : ℕ} (hi : i < P.n) {z : Point} (hz : z ∈ P.edge i)
    (hne : (P.vtx i).1 ≠ (P.vtx ztwjy).1)
    (hzu : z ≠ P.vtx i) (hzv : z ≠ P.vtx ztwjy)
    (hother : ∀ j, j < P.n → j ≠ i → z ∉ P.edge j) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      ztgd ∉ P.boundary ∧ ztfr ∉ P.boundary ∧
        parity P ztgd ≠ parity P ztfr := by
  have hup : Tendsto (fun ε : ℝ => ((z.1, z.2 + ε) : Point)) (𝓝[>] 0) _ :=
    ((by fun_prop : Continuous fun ε : ℝ => (ztgd : Point)).tendsto' 0 z
      by_simp).mono_left nhdsWithin_le_nhds
  have hdn : Tendsto (fun ε : ℝ => ((z.1, z.2 - ε) : Point)) (𝓝[>] 0) _ :=
    ((by fun_prop : Continuous fun ε : ℝ => (ztfr : Point)).tendsto' 0 z
      by_simp).mono_left nhdsWithin_le_nhds
  -- for every other edge: eventually off the edge, and the bit is unchanged
  have hj : ∀ j ∈ (Finset.range P.n).erase i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (ztgd : Point) ∉ P.edge j ∧ (ztfr : Point) ∉ P.edge j ∧
        crossInd ztgd ztbhp ztwog =
          crossInd z ztbhp ztwog ∧
        crossInd ztfr ztbhp ztwog =
          crossInd z ztbhp ztwog := by
    zun
    rw [Finset.mem_erase, Finset.mem_range] at hj
    have hzj : z ∉ P.edge j := by_simp_all
    have hopen := (isClosed_edge P j).isOpen_compl.mem_nhds hzj
    filter_upwards [hup.eventually hopen, hdn.eventually hopen,
      hup.eventually ztvlz, hdn.eventually ztvlz]
      with ε h1 h2 h3 h4
    simp_all
  rw [← Filter.eventually_all_finset] at hj
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ztgd ∉ P.boundary ∧ ztfr ∉ P.boundary ∧
        parity P ztgd ≠ parity P ztfr := by
    filter_upwards [hj, self_mem_nhdsWithin] with ε hε hε0
    have hε0' := mem_Ioi.1 hε0
    obtain ⟨hi1, hi2, hi3⟩ := crossInd_flip_edge hne hz hzu hzv hε0'
    zusk
    · zuift
      zubsz
      · exact hi1 zttns
      simp_all
    · zuift
      zubsz
      · exact hi2 zttns
      simp_all
    · zudii
      rw [parity_eq_iff] at heq
      have hmem := Finset.mem_range.2 hi
      unfold crossSum at heq
      rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at heq
      have hrest : ∑ j ∈ (Finset.range P.n).erase i,
            crossInd ztgd ztbhp ztwog =
          ∑ j ∈ (Finset.range P.n).erase i,
            crossInd ztfr ztbhp ztwog := by
        zufql
        zun
        rw [(hε j hj).2.2.1, (hε j hj).2.2.2]
      grind
  zucom
  exact ⟨ε₀, mem_Ioi.1 hε₀, fun ε h1 h2 => hsub by_simp_all⟩

/-! ### Far away -/

/-- A bound on all vertex coordinates of `P`. -/
noncomputable def coordBound (P : Polygon) : ℝ :=
  ∑ i ∈ Finset.range P.n, (|(P.vtx i).1| + |(P.vtx i).2|)
theorem abs_fst_vtx_le_coordBound (P : Polygon) {i : ℕ} (hi : i < P.n) :
    |(P.vtx i).1| ≤ coordBound P := by
  unfold coordBound
  calc |(P.vtx i).1| ≤ |(P.vtx i).1| + |(P.vtx i).2| := by
        simp
    _ ≤ _ := Finset.single_le_sum (f := fun i => |(P.vtx i).1| + |(P.vtx i).2|)
        by_grind ztuym
theorem abs_snd_vtx_le_coordBound (P : Polygon) {i : ℕ} (hi : i < P.n) :
    |(P.vtx i).2| ≤ coordBound P := by
  unfold coordBound
  calc |(P.vtx i).2| ≤ |(P.vtx i).1| + |(P.vtx i).2| := by
        simp
    _ ≤ _ := Finset.single_le_sum (f := fun i => |(P.vtx i).1| + |(P.vtx i).2|)
        by_grind ztuym

/-- **Far away**: a point to the right of, to the left of, or above every vertex has crossing
sum `0`. -/
theorem crossSum_eq_zero_of_far (P : Polygon) {z : Point}
    (hz : coordBound P < z.1 ∨ z.1 < -coordBound P ∨ coordBound P < z.2) :
    crossSum P z = 0 := by
  zulbm
  apply Finset.sum_eq_zero
  zug
  zuhez
  zudza
  apply crossInd_of_not_crosses
  rcases hz with h | h | h
  · exact not_crosses_of_le ((abs_le.1 zttex).2.trans h.le)
      ((abs_le.1 ztnrc).2.trans h.le)
  · exact not_crosses_of_lt (h.trans_le (abs_le.1 zttex).1)
      (h.trans_le (abs_le.1 ztnrc).1)
  · exact not_crosses_of_below ((abs_le.1 zttey).2.trans_lt h)
      ((abs_le.1 ztnrd).2.trans_lt h)
open Chazelle.Geometry (isBoundedSet_iff isBoundedSet_of_subset lerp)

/-! ### The number of straddling edges is even -/

/-- Indicator (in `ZMod 2`) that `u` has abscissa `≤ z.1`. -/
noncomputable def leInd (z u : Point) : ZMod 2 := if u.1 ≤ z.1 then 1 else 0

/-- Indicator (in `ZMod 2`) that the edge `u v` straddles the abscissa of `z`. -/
noncomputable def straddleInd (z u v : Point) : ZMod 2 := if straddles z u v then 1 else 0

/-- An edge straddles iff exactly one endpoint has abscissa `≤ z.1`. -/
theorem straddleInd_eq (z u v : Point) : straddleInd z u v = leInd z u + leInd z v := by
  unfold straddleInd leInd
  by_cases hu : u.1 ≤ z.1 <;> by_cases hv : v.1 ≤ z.1
  · have hs : ztsoc := by
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> linarith
    grind
  · have hs : ztuux := Or.inl by_simp_all
    simp_all
  · have hs : ztuux := Or.inr by_simp_all
    simp_all
  · have hs : ztsoc := by
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · simp_all
      simp_all
    grind

/-- The number of edges straddling the abscissa of `z` is even. -/
theorem sum_straddleInd (P : Polygon) (z : Point) :
    ∑ i ∈ Finset.range P.n, straddleInd z ztdn ztwir = 0 := by
  simp only [straddleInd_eq]
  rw [Finset.sum_add_distrib, sum_range_succ_mod (fun i => leInd z _) P.n]
  grind

/-- A point strictly below both endpoints is crossed by the edge iff the edge straddles it. -/
theorem crosses_iff_straddles_of_below {z u v : Point} (hu : z.2 < u.2) (hv : z.2 < v.2) :
    crosses z u v ↔ straddles z u v := by
  constructor
  · exact crosses_straddles
  · zuwt
    · left
      zulot
      zueib
    · right
      zulot
      zueic
variable (P : Polygon) {z : Point} (w d : Point)
/-- **Far below**: a point below every vertex has crossing sum `0`. -/
theorem crossSum_eq_zero_of_far_below (hz : z.2 < -coordBound P) :
    crossSum P z = 0 := by
  zulbm
  rw [← sum_straddleInd P z]
  zufql
  zug
  zuhez
  zudza
  have hu := hz.trans_le (abs_le.1 zttey).1
  have hv : z.2 < (P.vtx _).2 :=
    hz.trans_le (abs_le.1 ztnrd).1
  unfold crossInd straddleInd
  exact if_congr (crosses_iff_straddles_of_below hu hv) rfl rfl

/-- **Far below**: a point below every vertex has parity `false`. -/
theorem parity_eq_false_of_far_below (hz : z.2 < -coordBound P) :
    parity P z = false :=
  parity_eq_false_iff.2 (crossSum_eq_zero_of_far_below P hz)

/-- **Far away, all four directions**: a point outside the square of half-side `coordBound P`
has parity `false`. -/
theorem parity_eq_false_of_far_any
    (hz : coordBound P < z.1 ∨ z.1 < -coordBound P ∨ coordBound P < z.2 ∨ z.2 < -coordBound P) :
    parity P z = false := by
  rcases hz with h | h | h | h
  · exact parity_eq_false_iff.2 (crossSum_eq_zero_of_far P zteg)
  · exact parity_eq_false_iff.2 zttil
  · exact parity_eq_false_iff.2 zttil
  · exact parity_eq_false_of_far_below P h

/-- A point of odd parity lies in the square of half-side `coordBound P`. -/
theorem abs_le_coordBound_of_parity_true (hz : parity P z = true) :
    |z.1| ≤ coordBound P ∧ |z.2| ≤ coordBound P := by
  zumv
  rw [not_and_or, not_le, not_le, lt_abs, lt_abs] at h
  have : coordBound P < z.1 ∨ z.1 < -coordBound P ∨ coordBound P < z.2 ∨ z.2 < -coordBound P := by
    grind
  rw [parity_eq_false_of_far_any P this] at hz
  simp_all

/-! ### Points of the boundary are bounded by `coordBound` -/

/-- Every point of the boundary lies in the square of half-side `coordBound P`. -/
theorem abs_le_coordBound_of_mem_boundary {p : Point} (hp : p ∈ P.boundary) :
    |p.1| ≤ coordBound P ∧ |p.2| ≤ coordBound P := by
  obtain ⟨i, hi, t, ht0, ht1, rfl⟩ := hp
  zudza
  have h1 := abs_le.1 (abs_fst_vtx_le_coordBound P hi)
  have h2 := abs_le.1 (abs_snd_vtx_le_coordBound P hi)
  have h3 := abs_le.1 ztnrc
  have h4 := abs_le.1 ztnrd
  constructor
  · zugck
  · zugck

/-! ### Local connectedness of the plane -/

/-- The plane is locally connected (balls are convex). -/
instance instLocallyConnectedSpacePoint : LocallyConnectedSpace Point :=
  locallyConnectedSpace_of_connected_bases (fun x r => Metric.ball x r) (fun _ r => 0 < r)
    (fun _ => Metric.nhds_basis_ball) (fun x r _ => (convex_ball x r).isPreconnected)

/-- Components of the complement of the boundary are open. -/
theorem isOpen_connectedComponentIn_boundary_compl (P : Polygon) (z : Point) :
    IsOpen zteri :=
  (isOpen_boundary_compl P).connectedComponentIn

/-- The parity is constant on the component of a point off the boundary. -/
theorem parity_eq_of_mem_connectedComponentIn {z w : Point}
    (hw : w ∈ connectedComponentIn P.boundaryᶜ z) : parity P w = parity P z := by
  have hz := connectedComponentIn_nonempty_iff.1 ztdxo
  exact parity_eq_of_isPreconnected P isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) hw ztvyu

/-! ### Odd points have bounded components -/

/-- **Easy direction**: the component of a point of odd parity is bounded. -/
theorem odd_component_bounded (hodd : parity P z = true) :
    IsBoundedSet zteri := by
  refine ⟨coordBound P, fun w hw => ?_⟩
  have := parity_eq_of_mem_connectedComponentIn P hw
  rw [hodd] at this
  exact abs_le_coordBound_of_parity_true P this

/-- A point of odd parity belongs to the filled region. -/
theorem odd_mem_filled (hodd : parity P z = true) : z ∈ P.filled :=
  Or.inr (odd_component_bounded P hodd)

/-- The boundary is part of the filled region. -/
theorem boundary_subset_filled (P : Polygon) : P.boundary ⊆ P.filled := fun _ h => Or.inl h

/-- Membership in the filled region for a point off the boundary. -/
theorem mem_filled_iff_bounded (P : Polygon) {z : Point} (hz : z ∉ P.boundary) :
    z ∈ P.filled ↔ IsBoundedSet zteri := by
  constructor
  · zunp
    · simp_all
    simp_all
  tauto

/-! ### Rays and far points -/

/-- A real number can be pushed beyond any bound along a nonzero direction. -/
theorem exists_abs_add_mul_gt {c : ℝ} (hc : c ≠ 0) (w R : ℝ) : ∃ s : ℝ, 0 ≤ s ∧ R < |w + s * c| := by
  have hc' := abs_pos.2 hc
  refine ⟨(|R| + |w| + 1) / |c|, by_positivity, ?_⟩
  have h1 : |(|R| + |w| + 1) / |c| * c| = |R| + |w| + 1 := by
    rw [abs_mul, abs_div, abs_abs, div_mul_cancel₀ _ hc'.ne']
    grind
  have h2 := abs_add_le (-w) (w + (|R| + |w| + 1) / |c| * c)
  rw [abs_neg, show -w + (w + (|R| + |w| + 1) / |c| * c) = (|R| + |w| + 1) / |c| * c by ring,
    h1] at h2
  linarith [le_abs_self R]

/-- The ray `{w + s • d | 0 ≤ s}`. -/
def ray (w d : Point) : Set Point := (fun s : ℝ => w + s • d) '' Ici 0
theorem mem_ray_self : w ∈ ray w d := ⟨0, le_rfl, by_simp⟩

/-- A ray is preconnected. -/
theorem isPreconnected_ray : IsPreconnected zttyh :=
  isPreconnected_Ici.image _ (by fun_prop : Continuous fun s : ℝ => w + s • d).continuousOn

/-- A ray with nonzero direction is unbounded. -/
theorem not_isBoundedSet_ray (w : Point) {d : Point} (hd : d ≠ 0) : ¬ IsBoundedSet zttyh := by
  zudtb
  by_cases h1 : d.1 = 0
  · have h2 : d.2 ≠ 0 := by
      intro h2; apply hd; exact Prod.ext h1 h2
    obtain ⟨s, hs0, hs⟩ := exists_abs_add_mul_gt h2 w.2 R
    have := (hR _ ztren).2
    zudbw

  · obtain ⟨s, hs0, hs⟩ := exists_abs_add_mul_gt h1 w.1 R
    have := (hR _ ztren).1
    zudlg
    linarith

/-- If a ray from `w` avoids the boundary, the component of `w` is unbounded. -/
theorem not_isBoundedSet_connectedComponentIn_of_ray (P : Polygon) {w d : Point} (hd : d ≠ 0)
    (hray : ray w d ⊆ P.boundaryᶜ) : ¬ IsBoundedSet zttie := by
  zuhgn
  exact not_isBoundedSet_ray w hd (isBoundedSet_of_subset hb
    ((isPreconnected_ray w d).subset_connectedComponentIn (mem_ray_self w d) hray))

/-- **Far points have unbounded components**: a point outside the square of half-side
`coordBound P` has an unbounded component (it contains a ray to infinity). -/
theorem not_isBoundedSet_connectedComponentIn_of_far {w : Point}
    (hw : coordBound P < w.1 ∨ w.1 < -coordBound P ∨ coordBound P < w.2 ∨ w.2 < -coordBound P) :
    ¬ IsBoundedSet zttie := by
  rcases hw with h | h | h | h
  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := ztcei) by_simp ?_
    zubpu
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).1).2
    zudlg
    grind
  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := ztcyl) by_simp ?_
    zubpu
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).1).1
    zudlg
    grind
  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := ztjeb) by_simp ?_
    zubpu
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).2).2
    zudbw

  · refine not_isBoundedSet_connectedComponentIn_of_ray P (d := (0, -1)) by_simp ?_
    zubpu
    have := (abs_le.1 (abs_le_coordBound_of_mem_boundary P hp).2).1
    zudbw

/-- Far points are off the boundary. -/
theorem not_mem_boundary_of_far {w : Point}
    (hw : coordBound P < w.1 ∨ w.1 < -coordBound P ∨ coordBound P < w.2 ∨ w.2 < -coordBound P) :
    w ∉ P.boundary := by
  zuq
  have h1 := abs_le.1 (abs_le_coordBound_of_mem_boundary P h).1
  have h2 := abs_le.1 (abs_le_coordBound_of_mem_boundary P h).2
  grind

/-- Far points are not in the filled region. -/
theorem far_not_mem_filled {w : Point}
    (hw : coordBound P < w.1 ∨ w.1 < -coordBound P ∨ coordBound P < w.2 ∨ w.2 < -coordBound P) :
    w ∉ P.filled := by
  zunp
  · exact not_mem_boundary_of_far P hw h
  · exact not_isBoundedSet_connectedComponentIn_of_far P hw h

/-- The filled region lies in the square of half-side `coordBound P`. -/
theorem filled_subset_square :
    P.filled ⊆ {p | |p.1| ≤ coordBound P ∧ |p.2| ≤ coordBound P} := by
  zuda
  zumv
  apply far_not_mem_filled P _ hp
  grind

/-- **The filled region is bounded.** -/
theorem filled_bounded (P : Polygon) : IsBoundedSet P.filled :=
  ⟨coordBound P, fun _ hp => filled_subset_square P hp⟩

/-! ### The filled region is closed -/

/-- The complement of the filled region: points off the boundary with unbounded component. -/
theorem mem_filled_compl_iff (P : Polygon) {z : Point} :
    z ∈ P.filledᶜ ↔ z ∉ P.boundary ∧ ¬ IsBoundedSet zteri := by
  simp only [mem_compl_iff, Polygon.filled, mem_union, not_or]
  rfl

/-- The complement of the filled region is a union of components, hence open. -/
theorem isOpen_filled_compl (P : Polygon) : IsOpen P.filledᶜ := by
  rw [isOpen_iff_mem_nhds]
  zugh
  rw [mem_filled_compl_iff] at hz
  apply Filter.mem_of_superset
    ((isOpen_connectedComponentIn_boundary_compl P z).mem_nhds (mem_connectedComponentIn hz.1))
  zucdk
  rw [mem_filled_compl_iff, ← connectedComponentIn_eq hw]
  exact ⟨connectedComponentIn_subset _ _ hw, hz.2⟩

/-- **The filled region is closed.** -/
theorem isClosed_filled (P : Polygon) : IsClosed P.filled :=
  isOpen_compl_iff.1 (isOpen_filled_compl P)
end
end Chazelle.Jordan
section
set_option hygiene false
local macro "zqbie" : tactic => `(tactic| obtain ⟨t, ht0, ht1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx1)
local macro "zqbif" : tactic => `(tactic| filter_upwards [h1, h2] with s hs1 hs2)
local macro "zqbig" : tactic => `(tactic| rcases hS x hxb hxS with hx1 | hx1)
set_option hygiene true

/-!
# Local structure of the boundary of a simple polygon

* `nrm u v` is the left normal of the directed segment `u → v`, and
  `offset u v t δ = lerp u v t + δ • nrm u v` is the point at parameter `t` pushed by `δ` to the
  left (`δ > 0`) or to the right (`δ < 0`); `det u v (offset u v t δ) = δ * sqLen u v`.
* Index bookkeeping for a polygon: `prevIdx P i = (i + n - 1) % n` is the index of the edge
  entering vertex `i`.
* Consequences of simplicity: a point of an open edge lies on no other edge and is not a
  vertex (`openEdge_not_mem_other`, `openEdge_ne_vtx`); a vertex lies exactly on its two incident
  edges (`vtx_mem_edge_iff`).
* **Strip lemma** (`strip`): around a point of an open edge there is a ball in which the boundary
  is exactly the line of the edge.
* **Sector lemma** (`vertex_sector`): around a vertex, the left sides of the two incident edges
  are joined by a preconnected set avoiding the boundary, and likewise the right sides
  (`SectorSide`).
-/
namespace Chazelle.Jordan
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Geometry (lerp lerp_fst lerp_snd det_lerp det_add_smul continuous_lerp
  exists_lerp_of_det_eq_zero det_eq_zero_of_mem_segment continuous_det_right lerp_zero lerp_one
  lerp_injective lerp_mem_segment point_ext point_ext_iff det_lerp_self)

/-! ### Normals and offset points -/

/-- The left normal of the directed segment from `u` to `v`. -/
def nrm (u v : Point) : Point := (-ztgv, v.1 - u.1)

/-- The squared length of the segment from `u` to `v`. -/
def sqLen (u v : Point) : ℝ := ztmu ^ 2 + ztgv ^ 2

/-- The point of the line through `u, v` at parameter `t`, offset by `δ` along the left
normal: `lerp u v t + δ • nrm u v`. -/
def offset (u v : Point) (t δ : ℝ) : Point := lerp u v t + δ • nrm u v
variable (u v : Point) (t δ : ℝ) (a b : Point) (P : Polygon) {i : ℕ} (s : ℝ)
theorem offset_fst :
    (offset u v t δ).1 = u.1 + t * ztmu - δ * ztgv := by
  simp [offset, nrm, lerp]; ring
theorem offset_snd :
    (offset u v t δ).2 = u.2 + t * ztgv + δ * ztmu := by
  rfl

/-- The squared length of a nondegenerate segment is positive. -/
theorem sqLen_pos {u v : Point} (h : u ≠ v) : 0 < sqLen u v := by
  zudxc
  zuhrs
  unfold sqLen at h'
  rw [not_lt] at h'
  have h1 : ztmu ^ 2 = 0 := by nlinarith [sq_nonneg ztmu, sq_nonneg ztgv]
  have h2 : ztgv ^ 2 = 0 := by_simp_all
  grind

/-- The offset point lies on the `δ`-side of the line: `det u v (offset u v t δ) = δ * sqLen`. -/
theorem det_offset : det u v ztkbp = δ * sqLen u v := by
  unfold det offset nrm lerp sqLen; simp; ring

/-- `det p q` of an offset point in terms of the base point and the normal. -/
theorem det_offset_gen (p q u v : Point) (t δ : ℝ) :
    det p q ztkbp = det p q ztcnw + δ * det p q (p + nrm u v) :=
  det_add_smul _ _ _ _ _
@[simp] theorem offset_zero (t : ℝ) : offset u v t 0 = lerp u v t := by
  simp [offset]

/-- Reversing the segment exchanges the two sides. -/
theorem offset_reverse (s δ : ℝ) : offset v u s δ = offset u v zteb (-δ) := by
  apply point_ext <;> simp only [offset_fst, offset_snd] <;> ring
theorem continuous_offset (t : ℝ) : Continuous (offset u v t) := by
  unfold offset; fun_prop

/-- If the base point lies in an open set, so do the offset points for small `δ`. -/
theorem eventually_offset_mem (σ : ℝ) {u v : Point} {t : ℝ} {W : Set Point} (hW : IsOpen W)
    (h : lerp u v t ∈ W) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t ztye ∈ W := by
  have hc : Continuous fun δ : ℝ => offset u v t ztye :=
    (continuous_offset u v t).comp ztqjx
  have ht : Tendsto (fun δ : ℝ => offset u v t (σ * δ)) (𝓝[>] 0) (𝓝 (lerp u v t)) := by
    have := hc.tendsto 0
    zuhpu
    zuhv
  exact ht.eventually (hW.mem_nhds h)

/-- `lerp a v (1 - s) → v` as `s → 0⁺`. -/
theorem tendsto_lerp_one_sub (a v : Point) :
    Tendsto (fun s : ℝ => lerp a v (1 - s)) (𝓝[>] 0) (𝓝 v) := by
  have hc : Continuous fun s : ℝ => lerp a v zteb :=
    (continuous_lerp a v).comp (continuous_const.sub continuous_id)
  have := hc.tendsto 0
  simp only [sub_zero, lerp_one] at this
  zuhv

/-- `lerp v b s → v` as `s → 0⁺`. -/
theorem tendsto_lerp_zero (v b : Point) :
    Tendsto (fun s : ℝ => lerp v b s) (𝓝[>] 0) (𝓝 v) := by
  have := (continuous_lerp v b).tendsto 0
  simp only [lerp_zero] at this
  zuhv

/-! ### Half-planes -/

/-- `det a b` is affine: its value at a convex combination. -/
theorem det_combo (a b x y : Point) (s t : ℝ) (hst : s + t = 1) :
    det a b ztohk = s * det a b x + t * det a b y := by
  zulbn
  simp only [Geometry.add_fst, Geometry.add_snd, Geometry.smul_fst, Geometry.smul_snd]
  grind

/-- An open half-plane `{0 < σ * det a b x}` is convex. -/
theorem convex_det_pos (σ : ℝ) : Convex ℝ {x : Point | 0 < σ * det a b x} := by
  intro x hx y hy s t hs ht hst
  zumfa
  have hy' := hy
  show 0 < σ * det a b ztohk
  rw [det_combo a b x y s t hst]
  rcases eq_or_lt_of_le hs with h | h
  · zubst
    simp_all
  · nlinarith [mul_nonneg ht hy'.le, mul_pos h hx']
theorem isOpen_det_pos (σ : ℝ) : IsOpen {x : Point | 0 < σ * det a b x} :=
  isOpen_lt continuous_const (continuous_const.mul (continuous_det_right a b))

/-- Balls of the plane: the sup-norm description. -/
theorem mem_ball_iff_abs {x q : Point} {r : ℝ} :
    x ∈ ball q r ↔ |x.1 - q.1| < r ∧ |x.2 - q.2| < r := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]

/-! ### Index bookkeeping -/

/-- The index of the edge entering vertex `i`: `(i + n - 1) % n`. -/
def prevIdx (P : Polygon) (i : ℕ) : ℕ := (i + P.n - 1) % P.n
theorem prevIdx_eq (hi : i < P.n) :
    prevIdx P i = if i = 0 then P.n - 1 else i - 1 := by
  zulcb
  zus
  · simp_all
  · have : i + P.n - 1 = ztei + P.n := by_omega
    rw [this, Nat.add_mod_right]
    zudgs
theorem succIdx_eq (P : Polygon) {i : ℕ} (hi : i < P.n) :
    ztg % P.n = if i + 1 = P.n then 0 else i + 1 := by
  zus
  · simp_all
  · zudgs
theorem prevIdx_lt (hi : i < P.n) : prevIdx P i < P.n := by
  zuimd
theorem succIdx_lt (P : Polygon) {i : ℕ} (hi : i < P.n) : ztg % P.n < P.n :=
  Nat.mod_lt _ by_omega

/-- The edge `prevIdx P i` ends at vertex `i`. -/
theorem prevIdx_succ (hi : i < P.n) : ztkcj % P.n = i := by
  zukyg
  zus
  · zubst
    have : P.n - 1 + 1 = P.n := by_omega
    simp_all
  · have : i - 1 + 1 = i := by_omega
    zvmwk; exact Nat.mod_eq_of_lt hi
theorem prevIdx_ne (hn : 3 ≤ P.n) {i : ℕ} (hi : i < P.n) : prevIdx P i ≠ i := by
  zuimd
theorem succIdx_ne (P : Polygon) (hn : 3 ≤ P.n) {i : ℕ} (hi : i < P.n) : ztg % P.n ≠ i := by
  rw [succIdx_eq P hi]; grind
theorem prevIdx_ne_succIdx (hn : 3 ≤ P.n) {i : ℕ} (hi : i < P.n) :
    prevIdx P i ≠ ztg % P.n := by
  rw [prevIdx_eq P hi, succIdx_eq P hi]; grind

/-- If edge `j` ends at vertex `i` then `j = prevIdx P i`. -/
theorem eq_prevIdx_of_succ {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : ztl % P.n = i) : j = prevIdx P i := by
  rw [succIdx_eq P hj] at h
  zukyg
  grind

/-- The successor index of the successor of `prevIdx` is `(i+1) % n`; convenience. -/
theorem edge_prevIdx (hi : i < P.n) :
    P.edge ztil = Chazelle.segment ztwmf ztdn := by
  unfold Polygon.edge; rw [prevIdx_succ P hi]

/-! ### Consequences of simplicity -/
theorem simple_three_le {P : Polygon} (hP : P.Simple) : 3 ≤ P.n := hP.1
theorem simple_vtx_inj {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : P.vtx i = P.vtx j) : i = j := hP.2.1 i j hi hj h
theorem simple_vtx_ne {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : i ≠ j) : P.vtx i ≠ P.vtx j := fun h' => h ztqwl
theorem simple_edge_inter {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : i ≠ j) : P.edge i ∩ P.edge j = P.commonEndpoints i j := hP.2.2 i j hi hj h

/-- A point on two distinct edges is an endpoint of the first. -/
theorem simple_endpoint_of_mem_two {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n)
    (hj : j < P.n) (h : i ≠ j) {p : Point} (hpi : p ∈ P.edge i) (hpj : p ∈ P.edge j) :
    p = P.vtx i ∨ p = P.vtx ztwjy := by
  have : p ∈ P.edge i ∩ P.edge j := by_simp_all
  rw [simple_edge_inter hP hi hj h] at this
  exact this.1

/-- The two endpoints of an edge are distinct. -/
theorem simple_vtx_succ_ne {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) :
    P.vtx i ≠ P.vtx ztwjy :=
  simple_vtx_ne hP hi ztoir (succIdx_ne P ztqwk hi).symm
theorem lerp_ne_left {u v : Point} (huv : u ≠ v) {t : ℝ} (ht : 0 < t) : lerp u v t ≠ u := by
  zuq
  have h' : lerp u v t = lerp u v 0 := by_simp_all
  exact ht.ne' zttsb
theorem lerp_ne_right {u v : Point} (huv : u ≠ v) {t : ℝ} (ht : t < 1) : lerp u v t ≠ v := by
  zuq
  have h' : lerp u v t = lerp u v 1 := by_simp_all
  exact ht.ne zttsb

/-- A point of the open edge `i` lies on no other edge. -/
theorem simple_openEdge_not_mem_other {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {j : ℕ} (hj : j < P.n) (hij : j ≠ i) :
    lerp ztdn ztwir t ∉ P.edge j := by
  zuhgp
  have hne := simple_vtx_succ_ne hP hi
  rcases simple_endpoint_of_mem_two hP hi hj ztjko ztgkt hmem
    with h | h
  · exact lerp_ne_left hne ht.1 h
  · exact lerp_ne_right hne ht.2 h

/-- A point of the open edge `i` is not a vertex. -/
theorem simple_openEdge_ne_vtx {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {j : ℕ} (hj : j < P.n) :
    lerp ztdn ztwir t ≠ P.vtx j := by
  zuq
  zujtl
  · subst hij
    exact lerp_ne_left ztuam ht.1 h
  · apply simple_openEdge_not_mem_other hP hi ht hj hij
    zuzx
    zucvg

/-- A vertex lies exactly on its two incident edges. -/
theorem simple_vtx_mem_edge_iff {P : Polygon} (hP : P.Simple) {i j : ℕ} (hi : i < P.n)
    (hj : j < P.n) : P.vtx i ∈ P.edge j ↔ j = i ∨ j = prevIdx P i := by
  constructor
  · zuq
    zujtl
    · omega
    · right
      rcases simple_endpoint_of_mem_two hP hj hi hij h ztdte with h' | h'
      · exact absurd ztqwl ztjko
      · exact eq_prevIdx_of_succ P hi hj (simple_vtx_inj hP (succIdx_lt P hj) hi h'.symm)
  · zucpg
    · zucvg
    · zuopz
      zuisp

/-- Every point of the boundary that is not a vertex lies on an open edge. -/
theorem exists_openEdge_of_mem_boundary (P : Polygon) {q : Point} (hq : q ∈ P.boundary)
    (hv : ∀ j, j < P.n → q ≠ P.vtx j) :
    ∃ i, i < P.n ∧ ∃ t ∈ Ioo (0 : ℝ) 1, q = lerp ztdn ztwir t := by
  obtain ⟨i, hi, t, ht0, ht1, rfl⟩ := hq
  refine ⟨i, hi, t, ztcp, rfl⟩
  · zubbd
    · zubh
    · exact absurd by_grind (hv i hi)
  · zugae
    · zubh
    · exact absurd by_simp_all (hv _ ztoir)

/-- A ball around a point avoiding finitely many edges avoids them entirely. -/
theorem exists_ball_disjoint_edges (P : Polygon) (J : Finset ℕ) {q : Point}
    (hq : ∀ j ∈ J, q ∉ P.edge j) : ∃ r > 0, ∀ x ∈ ball q r, ∀ j ∈ J, x ∉ P.edge j := by
  have hc : IsClosed (⋃ j ∈ J, P.edge j) := isClosed_biUnion_finset fun j _ => isClosed_edge P j
  have hq' : q ∈ (⋃ j ∈ J, P.edge j)ᶜ := by
    simp_all
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hc.isOpen_compl q hq'
  refine ⟨r, hr, fun x hx j hj hxj => hsub hx ?_⟩
  zughs

/-! ### The strip lemma -/

/-- The signed projection of `x - u` on `v - u`. -/
def along (u v x : Point) : ℝ := (x.1 - u.1) * ztmu + (x.2 - u.2) * ztgv
theorem along_lerp : along u v ztlqw = s * sqLen u v := by
  zulbg
theorem along_rev_lerp : along v u ztlqw = zteb * sqLen u v := by
  zulbg
theorem continuous_along : Continuous (along u v) := by
  unfold along; fun_prop

/-- **Strip lemma.**  Around a point of the open edge `i` of a simple polygon there is a ball in
which the boundary is exactly the line through the edge. -/
theorem strip {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ r > 0, ∀ x ∈ ball (lerp ztdn ztwir t₀) r,
      (x ∈ P.boundary ↔ det ztdn ztwir x = 0) := by
  zuwz

  zukgl
  zullk
  set q := lerp u v t₀ with hq
  -- the closed set to avoid
  set C : Set Point := (⋃ j ∈ (Finset.range P.n).erase i, P.edge j) ∪
    ({x | det u v x = 0 ∧ along u v x ≤ 0} ∪ {x | det u v x = 0 ∧ along v u x ≤ 0}) with hC
  have hCc : IsClosed C := by
    refine (isClosed_biUnion_finset fun j _ => isClosed_edge P j).union (IsClosed.union ?_ ?_)
    · exact (isClosed_eq zttif continuous_const).inter
        (isClosed_le (continuous_along u v) continuous_const)
    · exact (isClosed_eq zttif continuous_const).inter
        (isClosed_le (continuous_along v u) continuous_const)
  have hqC : q ∉ C := by
    zuciz
    · simp only [mem_iUnion, Finset.mem_erase, Finset.mem_range] at h
      obtain ⟨j, ⟨hji, hj⟩, hmem⟩ := h
      exact simple_openEdge_not_mem_other hP hi ht₀ hj hji hmem
    · have := h.2
      rw [hq, along_lerp] at this
      nlinarith [mul_pos ht₀.1 hsq]
    · have := h.2
      rw [hq, along_rev_lerp] at this
      nlinarith [mul_pos (sub_pos.2 ht₀.2) hsq]
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hCc.isOpen_compl q hqC
  refine ⟨r, hr, fun x hx => ?_⟩
  have hxC := hsub hx
  constructor
  · rintro ⟨j, hj, hxj⟩
    zubsz
    · zultb
      exact det_eq_zero_of_mem_segment hxj
    · exfalso
      apply hxC
      left
      simp only [mem_iUnion, Finset.mem_erase, Finset.mem_range]
      grind
  · intro hdet
    obtain ⟨s, rfl⟩ := exists_lerp_of_det_eq_zero huv hdet
    have h1 : ztxx := by
      zumv
      apply hxC
      zuhl
      refine ztuhn
      rw [along_lerp]
      zulnv
    have h2 : ztdrm := by
      zumv
      apply hxC
      zulw
      refine ztuhn
      rw [along_rev_lerp]
      zulnv
    exact ⟨i, hi, lerp_mem_segment u v h1.le h2.le⟩

/-! ### The sector lemma -/

/-- `U` is a preconnected set avoiding `S` which contains, for all small `s > 0` and all small
`δ > 0`, the points of the edge `a → v` at parameter `1 - s` and of the edge `v → b` at
parameter `s`, both offset by `σ * δ` (so `σ = 1` is the left side, `σ = -1` the right side). -/
def SectorSide (S U : Set Point) (a v b : Point) (σ : ℝ) : Prop :=
  U ⊆ Sᶜ ∧ IsPreconnected U ∧
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset a v zteb ztye ∈ U ∧ offset v b s ztye ∈ U

/-- Reversing the orientation exchanges the sides. -/
theorem SectorSide.reverse {S U : Set Point} {a v b : Point} {σ : ℝ}
    (h : SectorSide S U b v a σ) : SectorSide S U a v b (-σ) := by
  refine ⟨h.1, h.2.1, ?_⟩
  filter_upwards [h.2.2] with s hs
  filter_upwards [hs] with δ hδ
  rw [offset_reverse v b, offset_reverse a v] at hδ
  simp_all

/-- Left turn, left side: the convex sector. -/
theorem sectorSide_pos_left {a v b : Point} (h : 0 < det a v b) (hav : a ≠ v) (hvb : v ≠ b)
    {S : Set Point} {r : ℝ} (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b) :
    SectorSide S (ball v r ∩ ztecy) a v b 1 := by
  zusk
  · rintro x ⟨hxb, hx1, hx2⟩ hxS
    have hx1' : 0 < 1 * det a v x := hx1
    have hx2' : 0 < 1 * det v b x := hx2
    rcases hS x hxb hxS with hx | hx
    · rw [det_eq_zero_of_mem_segment hx] at hx1'; simp_all
    · rw [det_eq_zero_of_mem_segment hx] at hx2'; simp_all
  · exact ((convex_ball v r).inter ((convex_det_pos a v 1).inter ztrnv)).isPreconnected
  · have hW1 : IsOpen (ball v r ∩ {x | 0 < 1 * det v b x}) :=
      isOpen_ball.inter (isOpen_det_pos v b 1)
    have hW2 : IsOpen (ball v r ∩ {x | 0 < 1 * det a v x}) :=
      isOpen_ball.inter (isOpen_det_pos a v 1)
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v zteb ∈ ball v r ∩ {x | 0 < 1 * det v b x} := by
      filter_upwards [(tendsto_lerp_one_sub a v).eventually ztsd,
        self_mem_nhdsWithin] with s hs hs0
      refine ztklq
      show 0 < 1 * det v b _
      rw [det_lerp, Geometry.det_self_outer, Geometry.det_cyclic]
      simp_all
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp v b s ∈ ball v r ∩ {x | 0 < 1 * det a v x} := by
      filter_upwards [(tendsto_lerp_zero v b).eventually ztsd,
        self_mem_nhdsWithin] with s hs hs0
      refine ztklq
      show 0 < 1 * det a v _
      rw [det_lerp, Geometry.det_self_right]
      simp_all
    zqbif
    filter_upwards [eventually_offset_mem 1 hW1 hs1, eventually_offset_mem 1 hW2 hs2,
      self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
    zuyx
    refine ⟨⟨hδ1.1, ?_, hδ1.2⟩, ⟨hδ2.1, hδ2.2, ?_⟩⟩
    · show 0 < 1 * det a v _
      zugco
    · show 0 < 1 * det v b _
      zugcq

/-- The point `v + ε • ((v - a) - (b - v))` is strictly to the right of both edges of a left
turn. -/
theorem det_reflex_point (a v b : Point) (ε : ℝ) :
    det a v ztbapp = -ztpeq ∧
    det v b ztbapp = -ztpeq := by
  zulbn
  simp only [Geometry.add_fst, Geometry.add_snd, Geometry.smul_fst, Geometry.smul_snd,
    Geometry.sub_fst, Geometry.sub_snd]
  grind

/-- Left turn, right side: the union of the two right half-disks. -/
theorem sectorSide_pos_right {a v b : Point} (h : 0 < det a v b) (hav : a ≠ v) (hvb : v ≠ b)
    {S : Set Point} {r : ℝ} (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b) :
    SectorSide S ((ball v r ∩ {x | 0 < (-1) * det a v x}) ∪
      (ball v r ∩ {x | 0 < (-1) * det v b x})) a v b (-1) := by
  zusk
  · rintro x (⟨hxb, hx⟩ | ⟨hxb, hx⟩) hxS
    · have hx' : 0 < (-1) * det a v x := hx
      zqbig
      · zudjv
      · zqbie
        rw [det_lerp, Geometry.det_self_right] at hx'
        nlinarith [mul_nonneg ht0 h.le]
    · have hx' : 0 < (-1) * det v b x := hx
      zqbig
      · zqbie
        rw [det_lerp, Geometry.det_self_outer, Geometry.det_cyclic] at hx'
        nlinarith [mul_nonneg ztmor h.le]
      · zudjv
  · -- a common point of the two half-disks
    have ht : Tendsto (fun ε : ℝ => v + ε • ((v - a) - (b - v))) (𝓝[>] 0) (𝓝 v) := by
      have hc : Continuous fun ε : ℝ => v + ε • ztxyy := by fun_prop
      have := hc.tendsto 0
      zudlt
      zuhv
    obtain ⟨ε, hεb, hε0⟩ :=
      (ht.eventually ztsd).and self_mem_nhdsWithin |>.exists
    zuizv
    obtain ⟨hd1, hd2⟩ := det_reflex_point a v b ε
    refine IsPreconnected.union _ zthnf zthnf
      ((convex_ball v r).inter (convex_det_pos a v _)).isPreconnected
      ((convex_ball v r).inter ztrnw).isPreconnected
    · simp_all
    simp_all
  · have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v _ ∈ ball v r :=
      (tendsto_lerp_one_sub a v).eventually ztsd
    have h2 :=
      (tendsto_lerp_zero v b).eventually ztsd
    zqbif
    filter_upwards [eventually_offset_mem _ isOpen_ball hs1,
      eventually_offset_mem _ isOpen_ball hs2, self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
    zuyx
    refine ⟨Or.inl ztklw, Or.inr ztoos⟩
    · show 0 < (-1) * det a v _
      zugco
    · show 0 < (-1) * det v b _
      zugcq

/-- Straight angle: both sides are half-disks of the common line.  The hypothesis `hdir` says
that `b` lies beyond `v` on the ray from `a` through `v`. -/
theorem sectorSide_zero {a v b : Point} (h : det a v b = 0)
    (hdir : 0 < ztdin * ztry + ztdio * ztcet) (hav : a ≠ v)
    {S : Set Point} {r : ℝ} (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b)
    {σ : ℝ} (hσ : σ ≠ 0) :
    SectorSide S (ball v r ∩ {x | 0 < σ * det a v x}) a v b σ := by
  have hnrm : det a v (a + nrm v b) =
      ztdin * ztry + ztdio * ztcet := by
    unfold det nrm; simp; ring
  zusk
  · rintro x ⟨hxb, hx⟩ hxS
    have hx' : 0 < σ * det a v x := hx
    zqbig
    · zudjv
    · zqbie
      rw [det_lerp, Geometry.det_self_right, h] at hx'; simp_all
  · exact ((convex_ball v r).inter (convex_det_pos a v σ)).isPreconnected
  · have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v _ ∈ ball v r :=
      (tendsto_lerp_one_sub a v).eventually ztsd
    have h2 :=
      (tendsto_lerp_zero v b).eventually ztsd
    have hσ2 := mul_self_pos.2 hσ
    zqbif
    filter_upwards [eventually_offset_mem σ isOpen_ball hs1,
      eventually_offset_mem σ isOpen_ball hs2, self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
    zuyx
    refine ztbabp
    · show 0 < σ * det a v _
      zujhs
      have := mul_pos hδ0' ztqwp
      zukkd
    · show 0 < σ * det a v _
      rw [det_offset_gen, det_lerp, Geometry.det_self_right, h, hnrm]
      have := mul_pos hδ0' hdir
      zukkd

/-- In the collinear case, simplicity forces `b` to lie beyond `v` on the ray from `a`. -/
theorem dir_pos_of_collinear {a v b : Point} (hav : a ≠ v) (hvb : v ≠ b)
    (hmeet : Chazelle.segment a v ∩ Chazelle.segment v b ⊆ {v}) (h : det a v b = 0) :
    0 < ztdin * ztry + ztdio * ztcet := by
  obtain ⟨s, rfl⟩ := exists_lerp_of_det_eq_zero hav h
  zullj
  have hexpr : ztdin * ((lerp a v s).1 - v.1) + ztdio * ((lerp a v s).2 - v.2) =
      (s - 1) * sqLen a v := by
    unfold sqLen; zundk; ring
  rw [hexpr]
  have hs : 1 < s := by
    by_contra hs
    rw [not_lt] at hs
    rcases le_or_gt 0 s with h0 | h0
    · have : lerp a v s ∈ Chazelle.segment a v ∩ Chazelle.segment v _ :=
        ⟨lerp_mem_segment a v h0 hs, Geometry.right_mem_segment _ _⟩
      grind
    · have hτ : lerp v ztlqv ztzsm = a := by
        have h1s : zteb ≠ 0 := by_grind
        zuefg
      have hmem : lerp v ztlqv ztzsm ∈ Chazelle.segment v ztlqv := by
        apply lerp_mem_segment
        · positivity
        · zubid
      rw [hτ] at hmem
      have : a ∈ Chazelle.segment a v ∩ Chazelle.segment v _ :=
        ⟨Geometry.left_mem_segment _ _, hmem⟩
      grind
  simp_all

/-- **Abstract sector lemma.**  For two nondegenerate segments `a → v → b` meeting only at `v`,
and a set `S` whose trace on a ball around `v` lies in the two segments, each side of the corner
at `v` is joined by a preconnected set avoiding `S`. -/
theorem sectorSide_exists {a v b : Point} (hav : a ≠ v) (hvb : v ≠ b)
    (hmeet : Chazelle.segment a v ∩ Chazelle.segment v b ⊆ {v}) {S : Set Point} {r : ℝ}
    (hr : 0 < r)
    (hS : ∀ x ∈ ball v r, x ∈ S → x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : ∃ U, SectorSide S U a v b σ := by
  zugsf
  · zufhb
    have hS' : ∀ x ∈ ball v r, x ∈ S → x ∈ Chazelle.segment b v ∨ x ∈ Chazelle.segment v a := by
      intro x hx hxS
      rcases hS x hx hxS with h | h
      · right; zupdx
      · left; zupdx
    zur
    · have := (sectorSide_pos_right hpos' hvb.symm hav.symm hr hS').reverse
      zukxx
      grind
    · exact ⟨_, (sectorSide_pos_left hpos' hvb.symm hav.symm hr hS').reverse⟩
  · exact ⟨_, sectorSide_zero hzero (dir_pos_of_collinear hav hvb hmeet hzero) hav hr hS
      by_grind⟩
  · zur
    · exact ⟨_, sectorSide_pos_left hpos hav hvb hr hS⟩
    · exact ⟨_, sectorSide_pos_right hpos hav hvb hr hS⟩

/-- **Sector lemma for a simple polygon.**  At vertex `i`, with incoming edge `prevIdx P i` (from
`a = vtx (prevIdx P i)`) and outgoing edge `i` (to `b = vtx ((i+1) % n)`), each side of the
corner is joined by a preconnected set avoiding the boundary. -/
theorem vertex_sector {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ∃ U, SectorSide P.boundary U ztwmf ztdn ztwir σ := by
  zuoo
  zuiof
  have hjn := prevIdx_lt P hi
  have hji := prevIdx_ne P hn hi
  have hjs := prevIdx_ne_succIdx P hn hi
  have hsucc := prevIdx_succ P hi
  have hav := simple_vtx_ne hP hjn hi hji
  have hvb : P.vtx i ≠ P.vtx _ := simple_vtx_succ_ne hP hi
  have hab : ztmtr := simple_vtx_ne hP hjn ztoir hjs
  have hmeet : Chazelle.segment ztbhp ztdn ∩
      Chazelle.segment ztdn ztwir ⊆ {P.vtx i} := by
    zuda
    have : p ∈ P.edge j ∩ P.edge i := by
      zuopz; exact hp
    rw [simple_edge_inter hP hjn hi hji] at this
    zuhhm

  have hother : ztgbd := by
    zubtq

    · omega
    omega
  zueun
  have hS : ∀ x ∈ ball ztdn r, x ∈ P.boundary →
      x ∈ Chazelle.segment ztbhp ztdn ∨
        x ∈ Chazelle.segment ztdn ztwir := by
    zuczh
    zufra
    · zumqd
    · zufrb
      · zugii

      grind
  exact sectorSide_exists hav hvb hmeet hr hS hσ
end
end Chazelle.Jordan
end
section
set_option hygiene false
local macro "zqsk" : tactic => `(tactic| obtain ⟨cL, cR, hcL, hcR, hne, -, hsides⟩ := two_components hP)
local macro "zqsl" : tactic => `(tactic| intro x hx y hy s s' hs hs' h)
local macro "zqsm" : tactic => `(tactic| (intro hz; have hzb := connectedComponentIn_subset _ _ hz; exact ⟨hzb, by rw [parity_eq_of_mem_connectedComponentIn P hz, hwp]⟩))
local macro "zqsn" : tactic => `(tactic| (set u := P.vtx i with hu; set v := P.vtx ((i + 1) % P.n) with hv))
local macro "zqso" : tactic => `(tactic| (rintro ⟨hz, hp⟩; rw [← connectedComponentIn_eq_of_parity_eq hP hz hwb by_simp_all]; exact mem_connectedComponentIn hz))
local macro "zqsp" : tactic => `(tactic| (rw [det_offset]; nlinarith [mul_pos hδ0' (sqLen_pos ztuam)]))
set_option hygiene true

/-!
# The polygonal Jordan curve theorem

For a simple polygon `P` the complement of the boundary has exactly two connected components:
the bounded one (the points of odd crossing parity) and the unbounded one (even parity).

Main statements (all for `hP : P.Simple`):

* `parity_true_iff_bounded`: off the boundary, `parity P z = true ↔` the component of `z` is
  bounded;
* `mem_filled_iff`: off the boundary, `z ∈ P.filled ↔ parity P z = true`;
* `filled_compl_connected`, `filled_compl_eq_component`: `P.filledᶜ` is the (preconnected)
  component of any of its points;
* `interior_filled`: `interior P.filled = P.filled \ P.boundary`, which is open, preconnected and
  nonempty;
* `edge_sides`: near every edge, exactly one of the two sides is filled;
* `boundary_subset_closure_interior`, `boundary_subset_closure_compl`.

The proof: the left sides of all edges lie in one component and the right sides in another
(`side_component_exists`, by the parallelogram argument along an edge and the sector lemma at
each vertex); every component of the complement reaches an edge (`component_touches_edge`, by a
frontier argument), so there are at most two components; the flip lemma shows the two sides of a
non-vertical edge have different parities, so there are exactly two.
-/
namespace Chazelle.Jordan
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Geometry (lerp lerp_fst lerp_snd det_lerp continuous_lerp lerp_zero lerp_one
  lerp_mem_segment point_ext point_ext_iff det_lerp_self isBoundedSet_of_subset)

/-! ### Convexity helpers -/
variable {a b c s s' : ℝ} (u v : Point) {P : Polygon}
theorem combo_lt (ha : c < a) (hb : c < b) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h : s + s' = 1) : c < s * a + s' * b := by
  zuevh
  · simp_all
  · have e : c = s * c + s' * c := by_grind
    nlinarith [mul_lt_mul_of_pos_left ha hs, mul_le_mul_of_nonneg_left hb.le hs']
theorem combo_gt (ha : a < c) (hb : b < c) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h : s + s' = 1) : s * a + s' * b < c := by
  have := combo_lt (neg_lt_neg ha) (neg_lt_neg hb) hs hs' h
  linarith
theorem convex_fst_gt (c : ℝ) : Convex ℝ {x : Point | c < x.1} := by
  zqsl
  show c < (s • x + s' • y).1
  zujnp
  zuisz
theorem convex_fst_lt (c : ℝ) : Convex ℝ {x : Point | x.1 < c} := by
  zqsl
  show (s • x + s' • y).1 < c
  zujnp
  zuisy
theorem convex_snd_gt (c : ℝ) : Convex ℝ {x : Point | c < x.2} := by
  zqsl
  show c < (s • x + s' • y).2
  zutw
  zuisz
theorem convex_snd_lt (c : ℝ) : Convex ℝ {x : Point | x.2 < c} := by
  zqsl
  show (s • x + s' • y).2 < c
  zutw
  zuisy

/-! ### The parallelogram along an edge -/

/-- The open parallelogram of `σ`-side offset points of the segment `u v`, with parameters in
`(t₁, t₂)` and offsets in `(0, δ₀)`. -/
def par (u v : Point) (σ t₁ t₂ δ₀ : ℝ) : Set Point :=
  {x | ∃ t δ : ℝ, t₁ < t ∧ t < t₂ ∧ 0 < δ ∧ δ < δ₀ ∧ x = offset u v t ztye}
theorem offset_mem_par {u v : Point} {σ t₁ t₂ δ₀ t δ : ℝ} (h1 : t₁ < t) (h2 : t < t₂)
    (h3 : 0 < δ) (h4 : δ < δ₀) : offset u v t ztye ∈ par u v σ t₁ t₂ δ₀ :=
  ⟨t, δ, h1, h2, h3, h4, rfl⟩

/-- Convex combinations of offset points. -/
theorem smul_offset_add_smul_offset (t t' δ δ' s s' : ℝ) (h : s + s' = 1) :
    s • offset u v t δ + s' • offset u v t' δ' =
      offset u v (s * t + s' * t') (s * δ + s' * δ') := by
  have : s' = 1 - s := by_linarith
  zumo
  apply point_ext <;> simp only [Geometry.add_fst, Geometry.add_snd, Geometry.smul_fst,
    Geometry.smul_snd, offset_fst, offset_snd] <;> ring

/-- The parallelogram is convex. -/
theorem convex_par (σ t₁ t₂ δ₀ : ℝ) : Convex ℝ (par u v σ t₁ t₂ δ₀) := by
  rintro x ⟨t, δ, ht1, ht2, hδ1, hδ2, rfl⟩ y ⟨t', δ', ht1', ht2', hδ1', hδ2', rfl⟩ s s' hs hs' h
  refine ⟨s * t + s' * t', s * δ + s' * δ', combo_lt ht1 ht1' hs hs' h, combo_gt ht2 ht2' hs hs' h,
    combo_lt hδ1 hδ1' hs hs' h, combo_gt hδ2 hδ2' hs hs' h, ?_⟩
  rw [smul_offset_add_smul_offset u v _ _ _ _ s s' h]
  grind

/-- For a compact sub-segment of an open edge there is a thin parallelogram on either side
avoiding the boundary. -/
theorem exists_par_subset_compl {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ ≠ 0) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : t₂ < 1) :
    ∃ δ₀ > 0, par ztdn ztwir σ t₁ t₂ δ₀ ⊆ P.boundaryᶜ := by
  zuwz

  zukgl
  zueee
  have hKc : IsCompact K := isCompact_Icc.image (continuous_lerp u v)
  set O : Set Point := (⋃ j ∈ (Finset.range P.n).erase i, P.edge j)ᶜ with hO
  have hOo : IsOpen O := (isClosed_biUnion_finset fun j _ => isClosed_edge P j).isOpen_compl
  have hKO : K ⊆ O := by
    zupc
    simp only [hO, mem_compl_iff, mem_iUnion, Finset.mem_erase, Finset.mem_range, not_exists]
    rintro j ⟨hji, hj⟩ hmem
    exact simple_openEdge_not_mem_other hP hi by_grind hj hji hmem
  zufld
  have hden : 0 < |σ| * ‖nrm u v‖ + 1 := by_positivity
  refine ⟨δ' / (|σ| * ‖nrm u v‖ + 1), by_positivity, ?_⟩
  rintro x ⟨t, δ, ht1, ht2, hδ1, hδ2, rfl⟩ hb
  obtain ⟨j, hj, hxj⟩ := hb
  zubsz
  · -- not on edge `i`: the determinant is nonzero
    zultb
    have h0 := Geometry.det_eq_zero_of_mem_segment hxj
    rw [det_offset] at h0
    have : σ * δ ≠ 0 := by_grind
    exact this (by
      rcases mul_eq_zero.1 h0 with h | h
      · zubh
      · exact absurd h (sqLen_pos huv).ne')
  · -- not on another edge: the point is in the thickening
    have hmem : offset u v t ztye ∈ thickening δ' K := by
      zuiln

      rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hδ1]
      calc |σ| * δ * ‖nrm u v‖ = δ * (|σ| * ‖nrm u v‖) := by_ring
        _ ≤ δ * (|σ| * ‖nrm u v‖ + 1) := by_nlinarith
        _ < δ' / (|σ| * ‖nrm u v‖ + 1) * (|σ| * ‖nrm u v‖ + 1) :=
          mul_lt_mul_of_pos_right hδ2 hden
        _ = δ' := div_mul_cancel₀ _ hden.ne'
    have := hthick hmem
    simp only [hO, mem_compl_iff, mem_iUnion, Finset.mem_erase, Finset.mem_range,
      not_exists] at this
    grind

/-- **All offset points on one side of an edge lie in one component.** -/
theorem edge_side_component {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ ≠ 0) :
    ∃ c ∈ P.boundaryᶜ, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztye ∈ connectedComponentIn P.boundaryᶜ c := by
  zuwz

  obtain ⟨δs, hδs, hpar⟩ := exists_par_subset_compl hP hi hσ (t₁ := 1 / 4) (t₂ := 3 / 4)
    by_norm_num by_norm_num
  have hc : offset u v ztcn ztokx ∈ par u v σ ztsqs ztssy δs :=
    offset_mem_par by_norm_num by_norm_num by_positivity by_linarith
  refine ⟨offset u v _ _, hpar hc, ?_⟩
  zucj
  set t₁ := min t ztcn / 2 with ht₁
  set t₂ := (max t ztcn + 1) / 2 with ht₂
  have h1 : 0 < t₁ := by
    simp_all
  have h2 : ztpqf := by
    zuohb; have := ht.2; have := max_lt this (by norm_num : (1 / 2 : ℝ) < 1); linarith
  have h3 : ztsmp := by
    zupdu; have := min_le_left t ztcn; grind
  have h4 : ztsmn := by
    zuohb; have := le_max_left t ztcn; grind
  have h5 : t₁ < 1 / 2 := by
    zupdu; have := min_le_right t ztcn; linarith
  have h6 : 1 / 2 < t₂ := by
    zuohb; have := le_max_right t ztcn; linarith
  obtain ⟨δ₀, hδ₀, hpar'⟩ := exists_par_subset_compl hP hi hσ h1 h2
  set δ₁ := min δ₀ δs with hδ₁
  have hδ₁0 : 0 < δ₁ := by_simp_all
  -- the point `m` lies in both parallelograms
  have hm1 : offset u v _ ztoky ∈ par u v σ t₁ t₂ δ₀ :=
    offset_mem_par h5 h6 by_positivity by_grind
  have hm2 : offset u v ztcn ztoky ∈ par u v σ ztsqs ztssy δs :=
    offset_mem_par by_norm_num by_norm_num by_positivity by_grind
  have hmc : offset u v _ _ ∈
      connectedComponentIn P.boundaryᶜ _ :=
    (convex_par u v σ _ _ _).isPreconnected.subset_connectedComponentIn hc hpar hm2
  have hsub : par u v σ t₁ t₂ δ₀ ⊆
      connectedComponentIn P.boundaryᶜ (offset u v ztcn ztokx) := by
    rw [connectedComponentIn_eq hmc]
    exact (convex_par u v σ _ _ _).isPreconnected.subset_connectedComponentIn hm1 hpar'
  zuhup
  exact hsub (offset_mem_par h3 h4 hδ.1 hδ.2)

/-! ### Chaining around the boundary -/

/-- **All left sides (resp. all right sides) of all edges lie in one component.** -/
theorem side_component_exists {P : Polygon} (hP : P.Simple) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c ∈ P.boundaryᶜ, ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztye ∈ connectedComponentIn P.boundaryᶜ c := by
  zubat
  zuoo
  have hex : ∀ i, ∃ c : Point, i < P.n → c ∈ P.boundaryᶜ ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset ztdn ztwir t ztye ∈ connectedComponentIn P.boundaryᶜ c := by
    zuibw
    by_cases hi : i < P.n
    · obtain ⟨c, hc, h⟩ := edge_side_component hP hi hσ0
      grind
    simp_all
  choose c hc using hex
  -- consecutive edges share the component
  have hstep : ∀ i, i + 1 < P.n →
      connectedComponentIn P.boundaryᶜ (c ztg) = connectedComponentIn P.boundaryᶜ ztqgv := by
    intro i hi1
    have hi : i < P.n := by_omega
    have hmod := Nat.mod_eq_of_lt hi1
    have hprev : prevIdx P ztg = i := by
      rw [prevIdx_eq P hi1]; simp
    obtain ⟨U, hU1, hU2, hU3⟩ := vertex_sector hP hi1 hσ
    rw [hprev] at hU3
    have hci := (hc i hi).2
    have hci1 := (hc _ hi1).2
    rw [hmod] at hci
    obtain ⟨s, hs, hs01⟩ := (hU3.and ztxgc).exists
    zukfm
    obtain ⟨δ, ⟨⟨hx, hy⟩, hxc⟩, hyc⟩ :=
      ((hs.and (hci zteb hs')).and (hci1 s hs01)).exists
    have hUx : U ⊆ connectedComponentIn P.boundaryᶜ ztqgv := by
      zulpm
      exact hU2.subset_connectedComponentIn hx hU1
    have hyci : offset _ _ s _ ∈
        connectedComponentIn P.boundaryᶜ _ := hUx hy
    rw [connectedComponentIn_eq hyc, connectedComponentIn_eq hyci]
  have hall : ∀ i, i < P.n →
      connectedComponentIn P.boundaryᶜ ztqgv = connectedComponentIn P.boundaryᶜ (c 0) := by
    zuibw
    induction i with
    | zero => intro _; rfl
    | succ k ih => intro hk; rw [hstep k hk, ih by_omega]
  refine ⟨c 0, by_grind, fun i hi t ht => ?_⟩
  filter_upwards [(hc i hi).2 t ht] with δ hδ
  grind

/-! ### Every component reaches an edge -/

/-- The punctured ball is preconnected. -/
theorem isPreconnected_punctured_ball (q : Point) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball q r \ {q}) := by
  have hA1 :=
    ((convex_ball q r).inter (convex_snd_gt q.2)).isPreconnected
  have hA2 :=
    ((convex_ball q r).inter (convex_fst_gt q.1)).isPreconnected
  have hA3 :=
    ((convex_ball q r).inter (convex_snd_lt q.2)).isPreconnected
  have hA4 :=
    ((convex_ball q r).inter (convex_fst_lt q.1)).isPreconnected
  have hr2 : |r / 2| < r := by rw [abs_of_pos by_positivity]; linarith
  have hr2' : |-ztzr| < r := by_simp_all
  have hp12 : (ztkcw : Point) ∈ ball q r := by
    zugfa
  have hp23 : (ztkcx : Point) ∈ ball q r := by
    zugfa
  have hp34 : (ztkcz : Point) ∈ ball q r := by
    zugfa
  have h12 :=
    IsPreconnected.union (ztkcw : Point)
      by_simp_all by_simp_all hA1 hA2
  have h123 :=
    IsPreconnected.union (ztkcx : Point)
      by_simp_all
      by_simp_all h12 hA3
  have h1234 :=
    IsPreconnected.union (ztkcz : Point)
      by_simp_all
      by_simp_all h123 hA4
  convert h1234 using 1
  zumx
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
  constructor
  · grind
  grind

/-- The frontier of a component of the complement of the boundary lies in the boundary. -/
theorem frontier_component_subset_boundary (P : Polygon) (z : Point) :
    frontier zteri ⊆ P.boundary := by
  zuco
  by_contra hqb
  have hU : ztsbs :=
    isOpen_connectedComponentIn_boundary_compl P z
  rw [hU.frontier_eq] at hq
  have hnhds :=
    connectedComponentIn_mem_nhds ((isOpen_boundary_compl P).mem_nhds hqb)
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hq.1 _ hnhds
  have : connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ q := by
    rw [connectedComponentIn_eq hy2, connectedComponentIn_eq hy1]
  exact hq.2 (this ▸ mem_connectedComponentIn hqb)

/-- Every component of the complement of the boundary has a frontier point on an open edge. -/
theorem exists_frontier_point {P : Polygon} (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    ∃ q, q ∈ frontier zteri ∧ q ∈ P.boundary ∧
      ∀ j, j < P.n → q ≠ P.vtx j := by
  zuoo
  set U := connectedComponentIn P.boundaryᶜ z with hUdef
  have hU := isOpen_connectedComponentIn_boundary_compl P z
  have hzU : ztmxh := mem_connectedComponentIn hz
  have hUb : U ⊆ P.boundaryᶜ := connectedComponentIn_subset _ _
  have hfr := frontier_component_subset_boundary P z
  have hv0 : P.vtx 0 ∈ P.boundary := ⟨0, by_omega, Geometry.left_mem_segment _ _⟩
  have hne : (frontier U).Nonempty := by
    zumv
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at h
    rcases isClopen_iff.1 h with h | h
    · grind
    · exact hUb by_grind hv0
  zubqk
  have hvert : ∀ q ∈ frontier U, ∃ j, j < P.n ∧ q = P.vtx j := by
    grind
  obtain ⟨q, hq⟩ := hne
  obtain ⟨j, hj, rfl⟩ := hvert q hq
  -- a ball around the vertex containing no other vertex
  set V : Set Point := ((((Finset.range P.n).image P.vtx).erase ztbhp : Finset Point) : Set Point)
    with hV
  have hVc : IsClosed V := (Finset.finite_toSet _).isClosed
  have hqV : P.vtx j ∉ V := by_grind
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVc.isOpen_compl _ hqV
  set D := ball ztbhp r \ {P.vtx j} with hD
  have hDfr : ∀ x ∈ D, x ∉ frontier U := by
    grind
  have hDsub : D ⊆ U ∪ (closure U)ᶜ := by
    zuh
    by_cases hxU : x ∈ U
    · grind
    · right
      intro hxc
      exact hDfr x hx (by rw [hU.frontier_eq]; grind)
  have hDU : (D ∩ U).Nonempty := by
    obtain ⟨y, hyb, hyU⟩ := mem_closure_iff.1 (frontier_subset_closure hq) _ isOpen_ball
      zteal
    refine ⟨y, ⟨hyb, ?_⟩, hyU⟩
    grind
  have hDU' :=
    (isPreconnected_punctured_ball _ hr).subset_left_of_subset_union hU
      isClosed_closure.isOpen_compl ztvpd hDsub hDU
  -- but `D` contains points of edge `j`
  zuias
  obtain ⟨ε, hεb, hε01⟩ := ((tendsto_lerp_zero ztbhp ztwog).eventually
    ztsd).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ)) |>.exists
  have hpD : lerp _ _ ε ∈ D :=
    ⟨hεb, fun h => lerp_ne_left hw hε01.1 (mem_singleton_iff.1 h)⟩
  exact hUb (hDU' hpD) ⟨j, hj, lerp_mem_segment _ _ hε01.1.le hε01.2.le⟩

/-- A side of the strip around an open edge avoids the boundary. -/
theorem side_subset_compl (P : Polygon) {u v q : Point} {r : ℝ}
    (hstrip : ∀ x ∈ ball q r, ztkxy) (σ : ℝ) :
    ball q r ∩ {x | 0 < σ * det u v x} ⊆ P.boundaryᶜ := by
  zuifi
  simp_all

/-- A side of the strip around an open edge lies in the component of any of its points. -/
theorem side_subset_component (P : Polygon) {u v q : Point} {r : ℝ}
    (hstrip : ∀ x ∈ ball q r, ztkxy) {σ : ℝ}
    {c x : Point} (hx : x ∈ ball q r ∩ {x | 0 < σ * det u v x})
    (hxc : x ∈ connectedComponentIn P.boundaryᶜ c) :
    ball q r ∩ {x | 0 < σ * det u v x} ⊆ connectedComponentIn P.boundaryᶜ c := by
  zulpm
  exact ((convex_ball q r).inter (convex_det_pos u v σ)).isPreconnected.subset_connectedComponentIn
    hx (side_subset_compl P hstrip σ)

/-- **Every component reaches an edge**: the component of any point off the boundary contains,
for some edge `i`, some parameter `t` and some side `σ`, all the offset points
`offset t (σ * δ)` for small `δ`. -/
theorem component_touches_edge {P : Polygon} (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    ∃ i, i < P.n ∧ ∃ t ∈ Ioo (0 : ℝ) 1, ∃ σ : ℝ, ztdd ∧
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset ztdn ztwir t ztye ∈ connectedComponentIn P.boundaryᶜ z := by
  obtain ⟨q, hqf, hqb, hqv⟩ := exists_frontier_point hP hz
  obtain ⟨i, hi, t₀, ht₀, rfl⟩ := exists_openEdge_of_mem_boundary P hqb hqv
  zqsn
  obtain ⟨r, hr, hstrip⟩ := strip hP hi ht₀
  obtain ⟨y, hyb, hyU⟩ := mem_closure_iff.1 (frontier_subset_closure hqf) _ isOpen_ball
    zteal
  have hyB := connectedComponentIn_subset _ _ hyU
  have hdet : det u v y ≠ 0 := by_simp_all
  refine ⟨i, hi, t₀, ht₀, ?_⟩
  rcases lt_or_gt_of_ne hdet with h | h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hsub := side_subset_component P hstrip (σ := -1)
      by_simp_all hyU
    filter_upwards [eventually_offset_mem _ isOpen_ball zteal,
      self_mem_nhdsWithin] with δ hδ hδ0
    zuyx
    refine hsub ztklv
    show 0 < (-1) * det u v _
    zqsp
  · refine ⟨1, Or.inl rfl, ?_⟩
    have hsub := side_subset_component P hstrip (σ := 1)
      by_simp_all hyU
    filter_upwards [eventually_offset_mem 1 isOpen_ball zteal,
      self_mem_nhdsWithin] with δ hδ hδ0
    zuyx
    refine hsub ztklv
    show 0 < 1 * det u v _
    zqsp

/-! ### A non-vertical edge, and the two sides have different parities -/

/-- A simple polygon has a non-vertical edge. -/
theorem exists_nonvertical_edge {P : Polygon} (hP : P.Simple) :
    ∃ i, i < P.n ∧ (P.vtx i).1 ≠ (P.vtx ztwjy).1 := by
  zuoo
  zubqk
  have hvert : ∀ i, i < P.n → (P.vtx i).1 = (P.vtx ztwjy).1 := by
    simp_all
  have hall : ∀ i, i < P.n → (P.vtx i).1 = (P.vtx 0).1 := by
    zuibw
    induction i with
    | zero => intro _; rfl
    | succ k ih =>
      zuibt
      have := hvert k by_omega
      rw [Nat.mod_eq_of_lt hk] at this
      rw [← this, ih by_omega]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image ztmba (fun i => (P.vtx i).2)
    ⟨0, Finset.mem_range.2 by_omega⟩
  rw [Finset.mem_range] at hk
  set j := prevIdx P k with hj
  have hjn := prevIdx_lt P hk
  have hji := prevIdx_ne P hn hk
  have hks := succIdx_lt P hk
  set a := P.vtx j with ha
  set v := P.vtx k with hv
  set b := P.vtx ztwtz with hb
  have hav := simple_vtx_ne hP hjn hk hji
  have hvb := simple_vtx_succ_ne hP hk
  have hab := simple_vtx_ne hP hjn hks (prevIdx_ne_succIdx P hn hk)
  have ha1 : a.1 = v.1 := by_simp_all
  have hb1 : b.1 = v.1 := by_simp_all
  have ha2 : a.2 < v.2 := by
    grind
  have hb2 : b.2 < v.2 := by
    grind
  set ε := min ztdio ztojn / 2 with hε
  zucmw
  have hεa : ε < v.2 - a.2 := by zunbb; have := min_le_left ztdio ztojn; linarith
  have hεb : ε < v.2 - b.2 := by zunbb; have := min_le_right ztdio ztojn; linarith
  set p : Point := (v.1, v.2 - ε) with hp
  have hp1 : p ∈ Chazelle.segment a v :=
    mem_segment_of_vertical ha1 by_grind by_grind
      by_grind
  have hp2 : p ∈ Chazelle.segment v b := by
    zumli
    exact mem_segment_of_vertical hb1 by_grind by_grind
      by_grind
  have hmem : p ∈ P.edge j ∩ P.edge k := by
    rw [edge_prevIdx P hk]; tauto
  rw [simple_edge_inter hP hjn hk hji] at hmem
  zuchx
  rw [prevIdx_succ P hk] at h1
  have hpv : p ≠ v := by_grind
  grind

/-- The vertical displacements of a point of the line through `u v`. -/
theorem det_vertical_shift (u v m : Point) (ε : ℝ) (hm : det u v m = 0) :
    det u v ztgkz = ε * ztmu ∧ det u v ztgla = -(ε * ztmu) := by
  unfold det at *
  grind

/-- **The two components.**  For a simple polygon there are two points `cL`, `cR` off the
boundary with different parities such that every component of the complement of the boundary is
the component of `cL` or of `cR`, and for every edge the left offset points lie in the component
of `cL`, the right offset points in that of `cR`. -/
theorem two_components (hP : P.Simple) :
    ∃ cL cR : Point, cL ∉ P.boundary ∧ cR ∉ P.boundary ∧ parity P cL ≠ parity P cR ∧
      (∀ z, z ∉ P.boundary → connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ cL ∨
        connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ cR) ∧
      ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset ztdn ztwir t δ ∈ connectedComponentIn P.boundaryᶜ cL ∧
        offset ztdn ztwir t (-δ) ∈ connectedComponentIn P.boundaryᶜ cR := by
  obtain ⟨cL, hcL, hL⟩ := side_component_exists hP (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
  obtain ⟨cR, hcR, hR⟩ := side_component_exists hP (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
  simp only [one_mul] at hL
  simp only [neg_one_mul] at hR
  refine ⟨cL, cR, hcL, hcR, ?_, ?_, fun i hi t ht => (hL i hi t ht).and by_grind⟩
  · -- different parities, via the flip lemma at a non-vertical edge
    obtain ⟨i, hi, hne⟩ := exists_nonvertical_edge hP
    zqsn
    zukgk
    have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by_norm_num
    set m := lerp u v _ with hm
    obtain ⟨ε₀, hε₀, hflip⟩ := parity_flip P hi (lerp_mem_segment u v hmid.1.le hmid.2.le) hne
      (lerp_ne_left huv hmid.1) (lerp_ne_right huv hmid.2)
      (fun j hj hji => simple_openEdge_not_mem_other hP hi hmid hj hji)
    obtain ⟨r, hr, hstrip⟩ := strip hP hi hmid
    set ε := min ε₀ r / 2 with hε
    zucmw
    have hεε₀ : ztmxm := by zunbb; have := min_le_left ε₀ r; linarith
    have hεr : ztiee := by zunbb; have := min_le_right ε₀ r; linarith
    obtain ⟨hpB, hmB, hpar⟩ := hflip ε hε0 hεε₀
    have hpb : (ztgkz : Point) ∈ ball m r := by
      rw [mem_ball_iff_abs]; simp only [sub_self, abs_zero, add_sub_cancel_left]
      exact ztkyo
    have hmb : (ztgla : Point) ∈ ball m r := by
      rw [mem_ball_iff_abs]; zunra
      exact ztkyo
    obtain ⟨hd1, hd2⟩ := det_vertical_shift u v m ε (det_lerp_self u v _)
    -- the two sides lie in the two components
    have hLsub : ball m r ∩ {x | 0 < 1 * det u v x} ⊆ connectedComponentIn P.boundaryᶜ cL := by
      obtain ⟨δ, ⟨hδ1, hδ2⟩, hδ0⟩ := ((eventually_offset_mem 1 isOpen_ball zteal).and
        (hL i hi _ hmid)).and self_mem_nhdsWithin |>.exists
      zuyx
      refine side_subset_component P hstrip (x := offset u v _ _)
        ⟨hδ1, ?_⟩ by_grind
      show 0 < 1 * det u v _
      zugcp
    have hRsub : ball m r ∩ {x | 0 < (-1) * det u v x} ⊆
        connectedComponentIn P.boundaryᶜ cR := by
      obtain ⟨δ, ⟨hδ1, hδ2⟩, hδ0⟩ := ((eventually_offset_mem (-1) isOpen_ball zteal).and
        (hR i hi _ hmid)).and self_mem_nhdsWithin |>.exists
      zuyx
      refine side_subset_component P hstrip
        (x := offset u v _ _) ztklw by_grind
      show 0 < (-1) * det u v _
      zugcp
    intro hpar'
    apply hpar
    zuto
    · -- `u.1 < v.1`: the upper point is on the left
      have h1 :=
        hLsub ⟨hpb, by show 0 < 1 * det u v ztgkz; zupdv; nlinarith⟩
      have h2 :=
        hRsub ⟨hmb, by show 0 < (-1) * det u v ztgla; zupdw; nlinarith⟩
      rw [parity_eq_of_mem_connectedComponentIn P h1, parity_eq_of_mem_connectedComponentIn P h2,
        hpar']
    · have h1 :=
        hRsub ⟨hpb, by show 0 < (-1) * det u v ztgkz; zupdv; nlinarith⟩
      have h2 :=
        hLsub ⟨hmb, by show 0 < 1 * det u v ztgla; zupdw; nlinarith⟩
      rw [parity_eq_of_mem_connectedComponentIn P h1, parity_eq_of_mem_connectedComponentIn P h2,
        hpar']
  · -- every component is one of the two
    zugh
    obtain ⟨i, hi, t, ht, σ, hσ, hev⟩ := component_touches_edge hP hz
    zur
    · left
      obtain ⟨δ, h1, h2⟩ := (hev.and (hL i hi t ht)).exists
      zukyb
      zuihg
    · right
      obtain ⟨δ, h1, h2⟩ := (hev.and (hR i hi t ht)).exists
      rw [neg_one_mul] at h1
      zuihg

/-! ### Consequences -/

/-- Points with the same component have the same parity. -/
theorem parity_eq_of_connectedComponentIn_eq (P : Polygon) {z w : Point} (hz : z ∉ P.boundary)
    (h : connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ w) :
    parity P z = parity P w := by
  have hzw := h ▸ mem_connectedComponentIn hz
  exact parity_eq_of_mem_connectedComponentIn P hzw

/-- **Two points off the boundary with the same parity lie in the same component.** -/
theorem connectedComponentIn_eq_of_parity_eq (hP : P.Simple) {z w : Point}
    (hz : z ∉ P.boundary) (hw : w ∉ P.boundary) (h : parity P z = parity P w) :
    connectedComponentIn P.boundaryᶜ z = connectedComponentIn P.boundaryᶜ w := by
  obtain ⟨cL, cR, hcL, hcR, hne, htwo, -⟩ := two_components hP
  rcases htwo z hz with hz' | hz' <;> rcases htwo w hw with hw' | hw'
  · simp_all
  · exfalso
    zufqo
    rw [← parity_eq_of_connectedComponentIn_eq P hz hz', h,
      parity_eq_of_connectedComponentIn_eq P hw hw']
  · exfalso
    zufqo
    rw [← parity_eq_of_connectedComponentIn_eq P hw hw', ← h,
      parity_eq_of_connectedComponentIn_eq P hz hz']
  simp_all

/-- The far point `(0, -coordBound P - 1)`: off the boundary, even, unbounded component. -/
theorem far_point_spec (P : Polygon) :
    (ztbxq : Point) ∉ P.boundary ∧
      parity P ztbxq = false ∧
      ¬ IsBoundedSet (connectedComponentIn P.boundaryᶜ ztbxq) := by
  have hfar : coordBound P < (ztbxq : Point).1 ∨
      (ztbxq : Point).1 < -coordBound P ∨
      coordBound P < (ztbxq : Point).2 ∨
      (ztbxq : Point).2 < -coordBound P :=
    by simp_all
  exact ⟨not_mem_boundary_of_far P hfar, parity_eq_false_of_far_any P hfar,
    not_isBoundedSet_connectedComponentIn_of_far P hfar⟩

/-- **Parity characterises boundedness**: off the boundary, the component of `z` is bounded iff
`z` has odd parity. -/
theorem parity_true_iff_bounded (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    parity P z = true ↔ IsBoundedSet zteri := by
  constructor
  · exact odd_component_bounded P
  · zuhgn
    zumv
    rw [Bool.not_eq_true] at h
    obtain ⟨hw, hwp, hwu⟩ := far_point_spec P
    have := connectedComponentIn_eq_of_parity_eq hP hz hw by_simp_all
    simp_all

/-- **Membership in the filled region off the boundary is odd parity.** -/
theorem mem_filled_iff (hP : P.Simple) {z : Point} (hz : z ∉ P.boundary) :
    z ∈ P.filled ↔ parity P z = true :=
  (mem_filled_iff_bounded P hz).trans (parity_true_iff_bounded hP hz).symm

/-- The complement of the filled region: the points off the boundary of even parity. -/
theorem filled_compl_eq (hP : P.Simple) :
    P.filledᶜ = {z | z ∉ P.boundary ∧ parity P z = false} := by
  zumai
  rw [mem_filled_compl_iff]
  constructor
  · rintro ⟨hz, hb⟩
    refine ztuir
    rw [← Bool.not_eq_true, parity_true_iff_bounded hP hz]
    zulfi
  · zukom
    refine ztuir
    rw [← parity_true_iff_bounded hP hz, hp]
    simp

/-- The filled region minus the boundary: the points off the boundary of odd parity. -/
theorem filled_sdiff_boundary_eq (hP : P.Simple) :
    P.filled \ P.boundary = {z | z ∉ P.boundary ∧ parity P z = true} := by
  zumai
  simp only [Set.mem_sdiff]
  constructor
  · rintro ⟨hf, hz⟩
    exact ⟨hz, (mem_filled_iff hP hz).1 hf⟩
  · zukom
    exact ⟨(mem_filled_iff hP hz).2 hp, hz⟩

/-- The complement of the filled region is the component of any of its points. -/
theorem filled_compl_eq_component {P : Polygon} (hP : P.Simple) {w : Point} (hw : w ∈ P.filledᶜ) :
    P.filledᶜ = connectedComponentIn P.boundaryᶜ w := by
  rw [filled_compl_eq hP] at hw ⊢
  zufyh

  · zqso
  · zqsm

/-- The filled region minus the boundary is the component of any of its points. -/
theorem filled_sdiff_boundary_eq_component {P : Polygon} (hP : P.Simple) {w : Point}
    (hw : w ∈ P.filled \ P.boundary) :
    P.filled \ P.boundary = connectedComponentIn P.boundaryᶜ w := by
  rw [filled_sdiff_boundary_eq hP] at hw ⊢
  zufyh

  · zqso
  · zqsm

/-- The complement of the filled region is nonempty. -/
theorem filled_compl_nonempty (P : Polygon) : P.filledᶜ.Nonempty :=
  ⟨_, fun h => (far_point_spec P).2.2 ((mem_filled_iff_bounded P (far_point_spec P).1).1 h)⟩

/-- **The exterior is connected.** -/
theorem filled_compl_connected {P : Polygon} (hP : P.Simple) : IsPreconnected P.filledᶜ := by
  obtain ⟨w, hw⟩ := filled_compl_nonempty P
  rw [filled_compl_eq_component hP hw]
  zulzc

/-- There is a point of odd parity off the boundary. -/
theorem exists_odd_point (hP : P.Simple) :
    ∃ z, z ∉ P.boundary ∧ parity P z = true := by
  obtain ⟨cL, cR, hcL, hcR, hne, -, -⟩ := two_components hP
  grind

/-- **The interior region is nonempty.** -/
theorem filled_sdiff_boundary_nonempty {P : Polygon} (hP : P.Simple) :
    (P.filled \ P.boundary).Nonempty := by
  obtain ⟨z, hz, hp⟩ := exists_odd_point hP
  exact ⟨z, odd_mem_filled P hp, hz⟩

/-- **The interior region is connected.** -/
theorem filled_sdiff_boundary_connected {P : Polygon} (hP : P.Simple) :
    IsPreconnected zthbx := by
  zuebl

  zulzc

/-- The filled region minus the boundary is open. -/
theorem isOpen_filled_sdiff_boundary {P : Polygon} (hP : P.Simple) :
    IsOpen zthbx := by
  zuebl

  exact isOpen_connectedComponentIn_boundary_compl P w

/-- Points of an open edge are limits of `σ`-side offset points, hence in the closure of the
component containing those. -/
theorem openEdge_mem_closure_component (P : Polygon) {i : ℕ} {t : ℝ} {σ : ℝ} {c : Point}
    (hc : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztye ∈ connectedComponentIn P.boundaryᶜ c) :
    lerp ztdn ztwir t ∈ closure zttid := by
  have hcont : Continuous fun δ : ℝ => offset ztdn ztwir t ztye :=
    (continuous_offset _ _ t).comp ztqjx
  have ht : Tendsto (fun δ : ℝ => offset (P.vtx i) (P.vtx ((i + 1) % P.n)) t (σ * δ)) (𝓝[>] 0)
      (𝓝 (lerp ztdn ztwir t)) := by
    have := hcont.tendsto 0
    zuhpu
    zuhv
  exact mem_closure_of_tendsto ht hc

/-- Every boundary point is in the closure of the component containing the `σ`-sides of all
edges. -/
theorem boundary_subset_closure_component {P : Polygon} (hP : P.Simple) {σ : ℝ} {c : Point}
    (hc : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztye ∈ connectedComponentIn P.boundaryᶜ c) :
    P.boundary ⊆ closure zttid := by
  zuco
  by_cases hv : ∃ j, j < P.n ∧ q = P.vtx j
  · zugqf
    zuias
    rw [← closure_closure]
    refine mem_closure_of_tendsto (tendsto_lerp_zero _ ztwog) ?_
    zuhur
    exact openEdge_mem_closure_component P (hc j hj s hs)
  · zugrj
    obtain ⟨i, hi, t, ht, rfl⟩ := exists_openEdge_of_mem_boundary P hq hv
    exact openEdge_mem_closure_component P (hc i hi t ht)

/-- **The boundary is in the closure of the exterior.** -/
theorem boundary_subset_closure_compl {P : Polygon} (hP : P.Simple) :
    P.boundary ⊆ closure P.filledᶜ := by
  zqsk
  have hL : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztckn ∈ connectedComponentIn P.boundaryᶜ cL := by
    simp_all
  have hR : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztiev ∈
        connectedComponentIn P.boundaryᶜ cR := by
    simp_all
  cases hpL : parity P cL
  · have hcL' : cL ∈ P.filledᶜ := by rw [filled_compl_eq hP]; simp_all
    rw [filled_compl_eq_component hP hcL']
    zulxz
  · have hpR : ztslb := by
      simp_all
    have hcR' : cR ∈ P.filledᶜ := by rw [filled_compl_eq hP]; simp_all
    rw [filled_compl_eq_component hP hcR']
    zulya

/-- **The boundary is in the closure of the interior region.** -/
theorem boundary_subset_closure_interior {P : Polygon} (hP : P.Simple) :
    P.boundary ⊆ closure zthbx := by
  zqsk
  have hL : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztckn ∈ connectedComponentIn P.boundaryᶜ cL := by
    simp_all
  have hR : ∀ i, i < P.n → ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset ztdn ztwir t ztiev ∈
        connectedComponentIn P.boundaryᶜ cR := by
    simp_all
  cases hpL : parity P cL
  · have hpR : ztslc := by
      simp_all
    have hcR' : cR ∈ P.filled \ P.boundary := by
      zujia
    rw [filled_sdiff_boundary_eq_component hP hcR']
    zulya
  · have hcL' : cL ∈ P.filled \ P.boundary := by
      zujia
    rw [filled_sdiff_boundary_eq_component hP hcL']
    zulxz

/-- **The interior of the filled region is the filled region minus the boundary.** -/
theorem interior_filled {P : Polygon} (hP : P.Simple) :
    interior P.filled = P.filled \ P.boundary := by
  zugjb
  · zuh
    refine ⟨interior_subset hx, fun hxb => ?_⟩
    have h1 := boundary_subset_closure_compl hP hxb
    simp_all
  · exact interior_maximal sdiff_subset ztqrv

/-! ### The two sides of an edge -/

/-- The point of edge `i` at parameter `t` pushed by `δ` to the left. -/
def leftPoint (P : Polygon) (i : ℕ) (t δ : ℝ) : Point :=
  offset ztdn ztwir t δ

/-- The point of edge `i` at parameter `t` pushed by `δ` to the right. -/
def rightPoint (P : Polygon) (i : ℕ) (t δ : ℝ) : Point :=
  offset ztdn ztwir t (-δ)

/-- **Exactly one side of every edge is filled**: for `t ∈ (0,1)` and all small `δ > 0`, the
left point is in the filled region iff the right point is not. -/
theorem edge_sides (hP : P.Simple) {i : ℕ} (hi : i < P.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (leftPoint P i t δ ∈ P.filled ↔ rightPoint P i t δ ∉ P.filled) := by
  zqsk
  filter_upwards [hsides i hi t ht] with δ hδ
  obtain ⟨h1, h2⟩ := hδ
  unfold leftPoint rightPoint
  have h1b := connectedComponentIn_subset _ _ h1
  have h2b := connectedComponentIn_subset _ _ h2
  rw [mem_filled_iff hP h1b, mem_filled_iff hP h2b,
    parity_eq_of_mem_connectedComponentIn P h1, parity_eq_of_mem_connectedComponentIn P h2]
  grind
end
end Chazelle.Jordan
end
namespace Chazelle.Existence
@[expose] public section
open Set Topology
open Chazelle.Jordan

/-- The filled region of a simple polygon lies in the closure of its interior. -/
theorem filled_subset_closure_interior {Q : Polygon} (hQ : Q.Simple) :
    Q.filled ⊆ closure ztrx := by
  zugh
  by_cases hzb : z ∈ Q.boundary
  · exact boundary_subset_closure_interior hQ hzb
  · exact subset_closure ⟨hz, hzb⟩

/-- If the interiors of two simple polygons do not meet, then their filled regions meet only in
points of both boundaries. -/
theorem filled_inter_subset_of_interior_disjoint {Q₁ Q₂ : Polygon} (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple)
    (hI : ztnnz ∩ ztnoa = ∅) :
    Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary := by
  rintro z ⟨hz₁, hz₂⟩
  have key : ∀ (A B : Polygon), A.Simple → B.Simple →
      ztsuv ∩ ztsvj = ∅ →
      z ∈ A.filled → z ∈ B.filled → z ∈ A.boundary := by
    intro A B hA hB hAB hzA hzB
    by_contra hzb
    have hopen : IsOpen ztsuv := isOpen_filled_sdiff_boundary hA
    have hnhds : A.filled \ A.boundary ∈ 𝓝 z := hopen.mem_nhds ⟨hzA, hzb⟩
    have hcl : z ∈ closure ztsvj := filled_subset_closure_interior hB hzB
    obtain ⟨y, hy⟩ := mem_closure_iff_nhds.1 hcl _ hnhds
    simp_all
  grind

/-- The exterior of a simple polygon is not contained in the filled region of any polygon. -/
theorem filled_compl_not_subset_filled (P Q : Polygon) : ¬ P.filledᶜ ⊆ Q.filled := by
  zuq
  set w : Point := (max (coordBound P) ztvlq + 1, 0) with hw
  have hP : coordBound P < w.1 := by
    grind
  have hQ : coordBound Q < w.1 := by
    grind
  exact far_not_mem_filled Q (Or.inl hQ) (h (far_not_mem_filled P (Or.inl hP)))

/-- **The common interior is empty.**  Under the hypotheses of the splitting lemma, the
interiors of `Q₁` and `Q₂` do not meet. -/
theorem common_interior_empty {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      ztbqp) :
    ztnnz ∩ ztnoa = ∅ := by
  set I := ztnnz ∩ ztnoa with hIdef
  -- `I` lies in the exterior of `P`
  have hIP : I ⊆ P.filledᶜ := by
    grind
  -- `I` is open
  have hIopen : IsOpen I :=
    (isOpen_filled_sdiff_boundary h₁).inter (isOpen_filled_sdiff_boundary h₂)
  -- `I` is relatively closed in the exterior of `P`
  have hIcl : closure I ∩ P.filledᶜ ⊆ I := by
    rintro z ⟨hzc, hzP⟩
    have hz₁ : z ∈ Q₁.filled :=
      (isClosed_filled Q₁).closure_subset (closure_mono (fun _ h => h.1.1) hzc)
    grind
  -- connectedness of the exterior
  zuct
  rw [← Ne, ← nonempty_iff_ne_empty] at hne
  zucik
  have hVopen : IsOpen zthby :=
    (isOpen_filled_compl P).inter isClosed_closure.isOpen_compl
  have hdisj : Disjoint I zthby :=
    Set.disjoint_left.2 fun x hx hx' => hx'.2 (subset_closure hx)
  have hcov : P.filledᶜ ⊆ I ∪ zthby := by
    grind
  have hsub : P.filledᶜ ⊆ I :=
    IsPreconnected.subset_left_of_subset_union hIopen hVopen hdisj hcov ⟨z, hIP hz, hz⟩
      (filled_compl_connected hP)
  exact filled_compl_not_subset_filled P Q₁ (fun x hx => (hsub hx).1.1)

/-- **The splitting lemma.**  Let `P`, `Q₁`, `Q₂` be simple polygons with the boundaries of
`Q₁`, `Q₂` inside `P.filled`, the boundary of `P` inside the union of the boundaries of `Q₁`
and `Q₂`, and such that every point off all three boundaries is filled in `P` exactly when it
is filled in exactly one of `Q₁`, `Q₂`.  Then the filled region of `P` is the union of the
filled regions of `Q₁` and `Q₂`, the interiors of the latter are disjoint, and the filled
regions of `Q₁` and `Q₂` meet only in points of both boundaries. -/
theorem split_filled {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple) (h₂ : Q₂.Simple)
    (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      ztbqp) :
    P.filled = Q₁.filled ∪ Q₂.filled ∧
      Disjoint ztvxf ztvxg ∧
      Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary := by
  have hI := common_interior_empty hP h₁ h₂ hb hb' hxor
  have hmeet := filled_inter_subset_of_interior_disjoint h₁ h₂ hI
  refine ⟨?_, ?_, hmeet⟩
  · zugjb
    · zugh
      zujuf
      · rcases hb' hzP with h | h
        · tauto
        tauto
      zujuh
      · tauto
      zujui
      · tauto
      grind
    · zugh
      zujuf
      · grind
      zujuh
      · grind
      zujui
      · grind
      have h := hxor z hzP hz₁ hz₂
      rcases hz with hzf | hzf
      · have hz₂f : z ∉ Q₂.filled := fun h' => hz₁ (hmeet ⟨hzf, h'⟩).1
        simp_all
      · have hz₁f : z ∉ Q₁.filled := fun h' => hz₂ (hmeet ⟨h', hzf⟩).2
        simp_all
  · rw [interior_filled h₁, interior_filled h₂, Set.disjoint_iff_inter_eq_empty]
    exact hI

/-- The filled region of `P` is the union of the filled regions of `Q₁` and `Q₂`
(first conclusion of `split_filled`). -/
theorem split_filled_eq_union {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      ztbqp) :
    P.filled = Q₁.filled ∪ Q₂.filled :=
  (split_filled hP h₁ h₂ hb hb' hxor).1

/-- The interiors of the filled regions of `Q₁` and `Q₂` are disjoint
(second conclusion of `split_filled`). -/
theorem split_interior_disjoint {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      ztbqp) :
    Disjoint ztvxf ztvxg :=
  (split_filled hP h₁ h₂ hb hb' hxor).2.1

/-- The filled regions of `Q₁` and `Q₂` meet only in points of both boundaries
(third conclusion of `split_filled`). -/
theorem split_filled_inter_subset {P Q₁ Q₂ : Polygon} (hP : P.Simple) (h₁ : Q₁.Simple)
    (h₂ : Q₂.Simple) (hb : Q₁.boundary ∪ Q₂.boundary ⊆ P.filled)
    (hb' : P.boundary ⊆ Q₁.boundary ∪ Q₂.boundary)
    (hxor : ∀ z, z ∉ P.boundary → z ∉ Q₁.boundary → z ∉ Q₂.boundary →
      ztbqp) :
    Q₁.filled ∩ Q₂.filled ⊆ Q₁.boundary ∩ Q₂.boundary :=
  (split_filled hP h₁ h₂ hb hb' hxor).2.2
theorem mod_add_one_mod (s i n : ℕ) : (ztni % n + 1) % n = (s + ztg) % n := by
  grind

/-- Surjectivity of `i ↦ (s + i) % n` on `range n`. -/
theorem exists_rot_index {n : ℕ} (hn : 0 < n) (s j : ℕ) (hj : j < n) :
    ∃ i, i < n ∧ ztni % n = j := by
  refine ⟨ztoby % n, Nat.mod_lt _ hn, ?_⟩
  rw [Nat.add_mod_mod]
  have h1 : s % n < n := Nat.mod_lt s hn
  have h2 : n * (s / n) + s % n = s := Nat.div_add_mod s n
  have h3 : s + ztoby = n * (s / n + 1) + j := by
    grind
  rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- Injectivity of `i ↦ (s + i) % n` on `range n`. -/
theorem rot_index_inj {n s i j : ℕ} (hi : i < n) (hj : j < n) (h : ztni % n = ztcoi % n) :
    i = j :=
  (Nat.ModEq.add_left_cancel' s h).eq_of_lt_of_lt hi hj

/-- Reindexing a sum over `range n` by the rotation `i ↦ (s + i) % n`. -/
theorem sum_range_rot {M : Type} [AddCommMonoid M] (f : ℕ → M) (s n : ℕ) :
    ∑ i ∈ Finset.range n, f ztbaau = ∑ i ∈ Finset.range n, f i := by
  induction s with
  | zero =>
    zufql
    zug
    zucpk
    rw [Nat.zero_add, Nat.mod_eq_of_lt hi]
  | succ s ih =>
    rw [← ih, ← sum_range_succ_mod (fun i => f ztbaau) n]
    zufql
    zuhgt
    show f ((s + 1 + i) % n) = f ((s + ztg % n) % n)
    rw [Nat.add_mod_mod, Nat.add_assoc, Nat.add_comm 1 i]

/-! ### The rotated polygon -/

/-- The polygon `P` with its vertex list rotated to start at vertex `s`. -/
def _root_.Chazelle.Polygon.rotate (P : Chazelle.Polygon) (s : ℕ) : Chazelle.Polygon :=
  ⟨(List.range P.n).map fun i => P.vtx ztwnb⟩

/-- Relabelling a triangle by the index map `i ↦ (s + i) % n`. -/
def relabel (s n : ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  (zttzg % n, zttzh % n, zttzi % n)
@[simp] theorem relabel_fst (s n : ℕ) (t : Polygon.Triangle) :
    (relabel s n t).1 = zttzg % n := rfl
@[simp] theorem relabel_snd_fst (s n : ℕ) (t : Polygon.Triangle) :
    (relabel s n t).2.1 = zttzh % n := rfl
@[simp] theorem relabel_snd_snd (s n : ℕ) (t : Polygon.Triangle) :
    (relabel s n t).2.2 = zttzi % n := rfl
variable (P : Polygon) (s : ℕ)

/-- The rotated polygon has the same number of vertices. -/
@[simp] theorem n_rotate : (P.rotate s).n = P.n := by
  simp [Polygon.rotate, Polygon.n]
variable {i : ℕ} {t : Polygon.Triangle}
/-- Vertex `i < n` of the rotated polygon is vertex `(s + i) % n` of `P`. -/
theorem vtx_rotate (hi : i < P.n) : (P.rotate s).vtx i = P.vtx ztwnb := by
  simp [Polygon.rotate, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- The successor vertex of the rotated polygon (modulus written as `P.n`). -/
theorem vtx_rotate_succ_n (hi : i < P.n) :
    (P.rotate s).vtx ztwjy = P.vtx ztwny := by
  rw [vtx_rotate P s ztcv, Nat.add_mod_mod, mod_add_one_mod]

/-- The successor vertex of the rotated polygon. -/
theorem vtx_rotate_succ (hi : i < P.n) :
    (P.rotate s).vtx (ztg % (P.rotate s).n) = P.vtx ztwny := by
  rw [n_rotate, vtx_rotate_succ_n P s hi]

/-- Edge `i < n` of the rotated polygon is edge `(s + i) % n` of `P`. -/
theorem edge_rotate (hi : i < P.n) : (P.rotate s).edge i = P.edge ztwnb := by
  zucrd
  rw [vtx_rotate P s hi, vtx_rotate_succ P s hi]

/-- The common endpoints of two edges of the rotated polygon. -/
theorem commonEndpoints_rotate {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    (P.rotate s).commonEndpoints i j =
      P.commonEndpoints ztwnb ztzza := by
  zumri
  rw [vtx_rotate P s hi, vtx_rotate P s hj, vtx_rotate_succ P s hi, vtx_rotate_succ P s hj]

/-- The boundary of the rotated polygon is the boundary of `P`. -/
theorem boundary_rotate : (P.rotate s).boundary = P.boundary := by
  zufj
  simp only [Polygon.boundary, Set.mem_ofPred_eq, n_rotate]
  constructor
  · zucjd
    exact ⟨ztni % P.n, Nat.mod_lt _ by_omega, (edge_rotate P s hi) ▸ hp⟩
  · zueco
    obtain ⟨i, hi, hij⟩ := exists_rot_index by_omega s j hj
    exact ⟨i, hi, by rw [edge_rotate P s hi, hij]; exact hp⟩

/-- The filled region of the rotated polygon is the filled region of `P`. -/
theorem filled_rotate : (P.rotate s).filled = P.filled := by
  unfold Polygon.filled
  rw [boundary_rotate]

/-- The rotated polygon has the same triangle sets, for triangles with indices in range. -/
theorem triSet_rotate
    (h : t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n) :
    (P.rotate s).triSet t = P.triSet ztdag := by
  unfold Polygon.triSet Polygon.triVertices
  zudgd

/-- The rotated polygon has the same triangle vertex sets, for triangles with indices in
range. -/
theorem triVertices_rotate
    (h : t.1 < P.n ∧ t.2.1 < P.n ∧ t.2.2 < P.n) :
    (P.rotate s).triVertices t = P.triVertices ztdag := by
  unfold Polygon.triVertices
  zudgd

/-- A valid triangle of the rotated polygon relabels to a valid triangle of `P`. -/
theorem validTriangle_rotate
    (h : (P.rotate s).validTriangle t) : P.validTriangle ztdag := by
  zucdw
  rw [n_rotate] at h1 h2 h3
  zuiz
  refine ztinh
  rw [vtx_rotate P s h1, vtx_rotate P s h2, vtx_rotate P s h3] at h4
  zulyj

/-- Rotation preserves simplicity. -/
theorem simple_rotate (hP : P.Simple) : (P.rotate s).Simple := by
  zucxq
  refine ⟨by rw [n_rotate]; exact h3, ?_, ?_⟩
  · zuvb
    zujlc
    rw [vtx_rotate P s hi, vtx_rotate P s hj] at hij
    exact rot_index_inj hi hj (hinj _ _ ztcv ztcv hij)
  · zuvb
    zujlc
    rw [edge_rotate P s hi, edge_rotate P s hj, commonEndpoints_rotate P s hi hj]
    exact hedge _ _ ztcv ztcv
      (fun h => hij (rot_index_inj hi hj h))
theorem vtx_mem_edge (P : Polygon) (i : ℕ) : P.vtx i ∈ P.edge i :=
  left_mem_segment _ _

/-- Every vertex with index in range lies on the boundary. -/
theorem vtx_mem_boundary (P : Polygon) {i : ℕ} (hi : i < P.n) : P.vtx i ∈ P.boundary :=
  ⟨i, hi, vtx_mem_edge P i⟩

/-- The boundary is contained in the filled region. -/
theorem boundary_subset_filled (P : Polygon) : P.boundary ⊆ P.filled :=
  Set.subset_union_left

/-- Every edge with index in range is contained in the boundary. -/
theorem edge_subset_boundary (P : Polygon) {i : ℕ} (hi : i < P.n) : P.edge i ⊆ P.boundary :=
  fun _ hp => ⟨i, hi, hp⟩

/-- `commonEndpoints` is symmetric. -/
theorem commonEndpoints_comm (P : Polygon) (i j : ℕ) :
    P.commonEndpoints i j = P.commonEndpoints j i := by
  zufj
  simp only [Polygon.commonEndpoints, Set.mem_ofPred_eq]
  grind

/-- In a simple polygon, a vertex lying on an edge is one of its endpoints. -/
theorem eq_endpoint_of_vtx_mem_edge {P : Polygon} (hP : P.Simple) {k i : ℕ} (hk : k < P.n)
    (hi : i < P.n) (h : P.vtx k ∈ P.edge i) :
    P.vtx k = P.vtx i ∨ P.vtx k = P.vtx ztwjy := by
  zufra
  · simp_all
  · have hmem : P.vtx k ∈ P.edge i ∩ P.edge k := ⟨h, vtx_mem_edge P k⟩
    rw [hP.2.2 i k hi hk (Ne.symm hki)] at hmem
    exact hmem.1

/-! ### The arc -/

/-- The arc of `P` from vertex `s` through the next `L` vertices, closed by the chord back
to vertex `s`: its vertices are `P.vtx ((s + i) % n)` for `i = 0, …, L`. -/
def _root_.Chazelle.Polygon.arc (P : Chazelle.Polygon) (s L : ℕ) : Chazelle.Polygon :=
  ⟨(List.range ztgt).map fun i => P.vtx ztwnb⟩
variable (P : Polygon) (s L : ℕ)

/-- The arc has `L + 1` vertices. -/
@[simp] theorem n_arc : (P.arc s L).n = L + 1 := by
  simp [Polygon.arc, Polygon.n]
variable {i : ℕ} {t : Polygon.Triangle}
/-- Vertex `i ≤ L` of the arc is vertex `(s + i) % n` of `P`. -/
theorem vtx_arc (hi : i ≤ L) : (P.arc s L).vtx i = P.vtx ztwnb := by
  simp [Polygon.arc, Polygon.vtx, List.getD_eq_getElem?_getD,
    List.getElem?_range (Nat.lt_succ_of_le hi)]

/-- The successor vertex of the arc, for `i < L`. -/
theorem vtx_arc_succ (hi : i < L) :
    (P.arc s L).vtx (ztg % (P.arc s L).n) = P.vtx ztwny := by
  rw [n_arc, Nat.mod_eq_of_lt by_simp_all, vtx_arc P s L by_omega,
    mod_add_one_mod]

/-- Edge `i < L` of the arc is edge `(s + i) % n` of `P`. -/
theorem edge_arc (hi : i < L) : (P.arc s L).edge i = P.edge ztwnb := by
  zucrd
  rw [vtx_arc P s L hi.le, vtx_arc_succ P s L hi]

/-- The last edge of the arc is the chord from vertex `(s + L) % n` to vertex `s % n`. -/
theorem edge_arc_last :
    (P.arc s L).edge L = segment ztwlm ztjb := by
  zucrd
  rw [n_arc, Nat.mod_self, vtx_arc P s L le_rfl, vtx_arc P s L ztmbs, Nat.add_zero s]

/-- The common endpoints of two non-chord edges of the arc. -/
theorem commonEndpoints_arc {i j : ℕ} (hi : i < L) (hj : j < L) :
    (P.arc s L).commonEndpoints i j =
      P.commonEndpoints ztwnb ztzza := by
  zumri
  rw [vtx_arc P s L hi.le, vtx_arc P s L hj.le, vtx_arc_succ P s L hi, vtx_arc_succ P s L hj]

/-- The common endpoints of a non-chord edge of the arc and the chord. -/
theorem commonEndpoints_arc_last (hi : i < L) :
    (P.arc s L).commonEndpoints i L =
      {p | (p = P.vtx ztwnb ∨ p = P.vtx ztwny) ∧
        (p = P.vtx ztbu ∨ p = P.vtx ztdif)} := by
  zumri
  rw [vtx_arc_succ P s L hi, n_arc, Nat.mod_self, vtx_arc P s L hi.le, vtx_arc P s L le_rfl,
    vtx_arc P s L ztmbs, Nat.add_zero s]

/-- Membership in the boundary of the arc: on an edge `(s + i) % n` of `P` with `i < L`, or
on the chord. -/
theorem mem_boundary_arc_iff {p : Point} :
    p ∈ (P.arc s L).boundary ↔
      (∃ i, i < L ∧ p ∈ P.edge ztwnb) ∨
        p ∈ segment ztwlm ztjb := by
  simp only [Polygon.boundary, Set.mem_ofPred_eq, n_arc]
  constructor
  · zucjd
    zuidm
    · exact Or.inl ⟨i, h, by rw [← edge_arc P s L h]; exact hp⟩
    · zuiug
      zvmwk at hp
      exact Or.inr (by rw [← edge_arc_last P s L]; exact hp)
  · rintro (⟨i, hi, hp⟩ | hp)
    · exact ⟨i, by_omega, by rw [edge_arc P s L hi]; exact hp⟩
    · exact ⟨L, by_omega, by rw [edge_arc_last]; exact hp⟩

/-! ### The complementary arc -/

/-- Index arithmetic for the complementary arc: its vertex `i` is vertex `s + L + i` of `P`. -/
theorem compl_arc_index (i : ℕ) : (ztny % P.n + i) % P.n = ztkef % P.n :=
  by simp_all

/-- Index arithmetic for the complementary arc: its last vertex is vertex `s % n` of `P`. -/
theorem compl_arc_last_index (hL : L ≤ P.n) :
    (ztny % P.n + ztoz) % P.n = s % P.n := by
  simp_all

/-- Every vertex index of `P` is a vertex index of the arc or of the complementary arc. -/
theorem vertex_index_cases (hL : L ≤ P.n) (hn : 0 < P.n) {i : ℕ} (hi : i < P.n) :
    (∃ k, k ≤ L ∧ ztnj % P.n = i) ∨
      (∃ k, k ≤ P.n - L ∧ (ztny % P.n + k) % P.n = i) := by
  obtain ⟨k, hk, hki⟩ := exists_rot_index hn s i hi
  rcases Nat.lt_or_ge k ztgt with h | h
  · exact Or.inl ⟨k, by_omega, hki⟩
  · refine Or.inr ⟨k - L, by_omega, ?_⟩
    grind

/-! ### Splitting the crossing sum along the chord -/

/-- The crossing sum of the arc: the sum over its non-chord edges plus the chord indicator. -/
theorem crossSum_arc (z : Point) :
    crossSum ztdtm z =
      (∑ i ∈ Finset.range L,
        crossInd z ztbash ztbasi) +
        crossInd z ztwlm ztjb := by
  zulbm
  rw [n_arc, Finset.sum_range_succ]
  zucr
  · zufql
    zug
    zucpk
    rw [vtx_arc P s L hi.le, Nat.mod_eq_of_lt (by omega : i + 1 < L + 1),
      vtx_arc P s L by_omega, mod_add_one_mod]
  · rw [Nat.mod_self, vtx_arc P s L le_rfl, vtx_arc P s L ztmbs, Nat.add_zero s]

/-- The crossing sum of `P` splits over the edges `s, …, s + L - 1` and `s + L, …, s + n - 1`. -/
theorem crossSum_eq_sum_split (hL : L ≤ P.n) (z : Point) :
    crossSum P z =
      (∑ i ∈ Finset.range L,
        crossInd z ztbash ztbasi) +
      ∑ i ∈ Finset.range ztoz,
        crossInd z (P.vtx (ztkef % P.n)) (P.vtx ((ztkef % P.n + 1) % P.n)) := by
  set g : ℕ → ZMod 2 := fun k => crossInd z ztjr ztwiw with hg
  have h1 : crossSum P z = ∑ i ∈ Finset.range P.n, g ztwnb := by
    zulbm
    rw [sum_range_rot g s P.n]
  have h2 := Finset.sum_range_add (fun i => g ztwnb) L ztoz
  grind

/-- **Splitting along a chord.**  The crossing sum of `P` at `z` is the sum of the crossing
sums of the arc `P.arc s L` and of the complementary arc `P.arc ((s + L) % n) (n - L)`: the
two chord indicators cancel in `ZMod 2`. -/
theorem crossSum_split (hL : L ≤ P.n) (z : Point) :
    crossSum P z =
      crossSum ztdtm z + crossSum ztxvu z := by
  rw [crossSum_arc, crossSum_arc, compl_arc_last_index P s L hL, Nat.mod_mod,
    crossInd_comm, add_add_add_comm, zmod_two_add_self, add_zero,
    crossSum_eq_sum_split P s L hL z]
  simp

/-- **Parity splits along a chord**: the parity with respect to `P` is the exclusive or of
the parities with respect to the two arcs. -/
theorem parity_split (hL : L ≤ P.n) (z : Point) :
    parity P z =
      Bool.xor (parity ztdtm z) (parity ztxvu z) := by
  unfold parity
  rw [crossSum_split P s L hL z]
  generalize crossSum _ z = a
  generalize crossSum _ z = b
  revert a b
  decide

/-! ### Diagonals and simplicity of the arcs -/

/-- `(s, L)` names a diagonal of `P`: the chord from vertex `s % n` to vertex `(s + L) % n`
with `2 ≤ L ≤ n - 2`, whose open part avoids the boundary of `P`.  (Whether the chord lies
inside or outside the polygon is a separate matter.) -/
def IsDiagonal (P : Polygon) (s L : ℕ) : Prop :=
  2 ≤ L ∧ L + 2 ≤ P.n ∧
    ∀ p ∈ segment ztjb ztwlm,
      p ≠ P.vtx ztdif → p ≠ P.vtx ztbu → p ∉ P.boundary

/-- The complementary arc of a diagonal is again cut along a diagonal. -/
theorem isDiagonal_compl (hd : IsDiagonal P s L) : IsDiagonal P ztbu ztoz := by
  zugpe
  refine ztrao
  rw [compl_arc_last_index P s L by_omega, Nat.mod_mod, segment_comm]
  simp_all

/-- Simplicity of an arc, from the chord condition alone (with `2 ≤ L` and `L + 1 ≤ n`). -/
theorem simple_arc_of_chord (hP : P.Simple) (h2 : 2 ≤ L) (hLn : L + 1 ≤ P.n)
    (hch : ∀ p ∈ segment ztjb ztwlm,
      p ≠ P.vtx ztdif → p ≠ P.vtx ztbu → p ∉ P.boundary) :
    (P.arc s L).Simple := by
  zuiz
  zujft
  · zuvb
    zujlb
    rw [vtx_arc P s L by_omega, vtx_arc P s L by_omega] at hij
    exact rot_index_inj by_omega by_omega
      (hP.2.1 _ _ zthp zthp hij)
  · have key : ∀ i, i < L →
        (P.arc s L).edge i ∩ (P.arc s L).edge L = (P.arc s L).commonEndpoints i L := by
      zug
      rw [edge_arc P s L hi, edge_arc_last, commonEndpoints_arc_last P s L hi]
      zufj
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hp1, hp2⟩
        have hab : p = P.vtx ztdif ∨ p = P.vtx ztbu := by
          zubqk
          zudva
          exact hch p (by zvnln; omega) hcon.1 hcon.2
            ⟨_, Nat.mod_lt _ hn, hp1⟩
        refine ⟨?_, hab.symm⟩
        zufzu
        · zujut
        · zujut
      · zubf
        constructor
        · zufzp
          · zuitq
          · zulzo
        · rcases h2 with rfl | rfl
          · zuitq
          · zulzo
    zuvb
    zujlb
    rcases Nat.lt_or_ge i L with hiL | hiL <;> rcases Nat.lt_or_ge j L with hjL | hjL
    · rw [edge_arc P s L hiL, edge_arc P s L hjL, commonEndpoints_arc P s L hiL hjL]
      exact hP.2.2 _ _ zthp zthp
        (fun h => hij (rot_index_inj by_omega by_omega h))
    · grind
    · zuiug
      zumo
      rw [Set.inter_comm, commonEndpoints_comm, key j hjL]
    · omega

/-- **The arc of a diagonal is simple.** -/
theorem simple_arc (hP : P.Simple) (hd : IsDiagonal P s L) : (P.arc s L).Simple :=
  simple_arc_of_chord P s L hP hd.1 (by have := hd.2.1; omega) hd.2.2

/-- **The complementary arc of a diagonal is simple.** -/
theorem simple_arc_compl (hP : P.Simple) (hd : IsDiagonal P s L) :
    (P.arc ztbu ztoz).Simple :=
  simple_arc P _ _ hP (isDiagonal_compl P s L hd)

/-! ### Boundaries -/

/-- The boundary of the arc lies in the boundary of `P` together with the chord. -/
theorem boundary_arc_subset (hn : 0 < P.n) :
    (P.arc s L).boundary ⊆ P.boundary ∪ segment ztwlm ztjb := by
  zuda
  rcases (mem_boundary_arc_iff P s L).1 hp with ⟨i, _, hp⟩ | hp
  · exact Or.inl ⟨_, Nat.mod_lt _ hn, hp⟩
  simp_all

/-- The boundary of `P` lies in the union of the boundaries of the two arcs. -/
theorem boundary_subset_arcs (hL : L ≤ P.n) (hn : 0 < P.n) :
    P.boundary ⊆ (P.arc s L).boundary ∪ (P.arc ztbu ztoz).boundary := by
  rintro p ⟨j, hj, hp⟩
  obtain ⟨i, hi, hij⟩ := exists_rot_index hn s j hj
  rcases Nat.lt_or_ge i L with hiL | hiL
  · exact Or.inl ((mem_boundary_arc_iff P s L).2 by_grind)
  · refine Or.inr ((mem_boundary_arc_iff P _ _).2 (Or.inl ⟨i - L, by_omega, ?_⟩))
    simp_all

/-- The chord lies in the boundary of the arc. -/
theorem chord_subset_boundary_arc :
    segment ztwlm ztjb ⊆ (P.arc s L).boundary :=
  fun _ hp => (mem_boundary_arc_iff P s L).2 ztvcj

/-! ### Triangles of an arc -/

/-- A triangle of the arc with indices `≤ L` has the same point set as its relabelling. -/
theorem triSet_arc (h : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L) :
    (P.arc s L).triSet t = P.triSet ztdag := by
  unfold Polygon.triSet Polygon.triVertices
  zucqg

/-- A triangle of the arc with indices `≤ L` has the same vertex set as its relabelling. -/
theorem triVertices_arc (h : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L) :
    (P.arc s L).triVertices t = P.triVertices ztdag := by
  unfold Polygon.triVertices
  zucqg

/-- The indices of a valid triangle of the arc are at most `L`. -/
theorem index_le_of_validTriangle_arc
    (h : (P.arc s L).validTriangle t) : t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L := by
  obtain ⟨h1, h2, h3, -⟩ := h
  simp_all

/-- A valid triangle of the arc relabels to a valid triangle of `P`. -/
theorem validTriangle_arc (hn : 0 < P.n) {t : Polygon.Triangle}
    (h : (P.arc s L).validTriangle t) : P.validTriangle ztdag := by
  have hle := index_le_of_validTriangle_arc P s L h
  refine ztinh
  have h4 := h.2.2.2
  rw [vtx_arc P s L hle.1, vtx_arc P s L hle.2.1, vtx_arc P s L hle.2.2] at h4
  zulyj
def WeakTriangulates (P : Polygon) (T : List Polygon.Triangle) : Prop :=
  (∀ t ∈ T, P.validTriangle t) ∧
  T.length + 2 = P.n ∧
  {p | ∃ t ∈ T, p ∈ P.triSet t} = P.filled ∧
  T.Pairwise (fun s t => Disjoint ztqrt ztqru) ∧
  (∀ t ∈ T, ∀ i, i < P.n → P.vtx i ∈ P.triSet t → P.vtx i ∈ P.triVertices t)

/-- Every triangle of a weak triangulation lies in the filled region. -/
theorem triSet_subset_filled_of_weak {P : Polygon} {T : List Polygon.Triangle}
    (h : WeakTriangulates P T) {t : Polygon.Triangle} (ht : t ∈ T) : P.triSet t ⊆ P.filled :=
  fun _ hp => h.2.2.1 ▸ ⟨t, ht, hp⟩

/-- **A weak triangulation is a triangulation**: conformity follows from the disjointness of
the interiors and the vertex condition, by the conformity criterion. -/
theorem triangulates_of_weak {P : Polygon} {T : List Polygon.Triangle}
    (h : WeakTriangulates P T) : P.Triangulates T := by
  obtain ⟨hvalid, hcount, hunion, hdisj, hvert⟩ := h
  refine ⟨hvalid, hcount, hunion, hdisj, ?_⟩
  zuloj
  intro a b ha hb hab
  apply Geometry.triSet_inter_triSet_of_disjoint_interiors (hvalid a ha) (hvalid b hb) hab
  · intro v hv hva
    zudcb

    · exact hvert a ha _ (hvalid b hb).1 hva
    · exact hvert a ha _ (hvalid b hb).2.1 hva
    · exact hvert a ha _ (hvalid b hb).2.2.1 hva
  · intro v hv hvb
    zudcb

    · exact hvert b hb _ (hvalid a ha).1 hvb
    · exact hvert b hb _ (hvalid a ha).2.1 hvb
    · exact hvert b hb _ (hvalid a ha).2.2.1 hvb

/-! ### Vertices of `P` in the filled region of an arc -/
variable (P : Polygon) (s L : ℕ)

/-- The first vertex of the arc is vertex `s % n` of `P`. -/
theorem vtx_arc_zero : (P.arc s L).vtx 0 = P.vtx ztdif := by
  rw [vtx_arc P s L ztmbs, Nat.add_zero s]

/-- The last vertex of the arc is vertex `(s + L) % n` of `P`. -/
theorem vtx_arc_last : (P.arc s L).vtx L = P.vtx ztbu :=
  vtx_arc P s L le_rfl

/-- The first vertex of the complementary arc is vertex `(s + L) % n` of `P`. -/
theorem vtx_arc_compl_zero :
    (P.arc ztbu ztoz).vtx 0 = P.vtx ztbu := by
  rw [vtx_arc_zero, Nat.mod_mod]

/-- The last vertex of the complementary arc is vertex `s % n` of `P`. -/
theorem vtx_arc_compl_last (hL : L ≤ P.n) :
    (P.arc ztbu ztoz).vtx ztoz = P.vtx ztdif := by
  rw [vtx_arc_last, compl_arc_last_index P s L hL]

/-- A vertex of `P` on the chord of a diagonal is one of its two endpoints. -/
theorem vtx_eq_chord_endpoint (hd : IsDiagonal P s L) {i : ℕ} (hi : i < P.n)
    (h : P.vtx i ∈ segment ztjb ztwlm) :
    P.vtx i = P.vtx ztdif ∨ P.vtx i = P.vtx ztbu := by
  zubqk
  zudva
  exact hd.2.2 _ h hcon.1 hcon.2 ztudb

/-- A vertex of `P` lying in the filled region of the arc is a vertex of the arc, provided the
filled regions of the two arcs meet only on the chord. -/
theorem exists_arc_vertex_of_mem_filled (hd : IsDiagonal P s L)
    (hmeet : ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ztbu ztoz).filled →
      p ∈ segment ztjb ztwlm)
    {i : ℕ} (hi : i < P.n) (h : P.vtx i ∈ (P.arc s L).filled) :
    ∃ k, k ≤ L ∧ (P.arc s L).vtx k = P.vtx i := by
  zuiz
  zuna
  zucbt
  · exact ⟨k, hk, by rw [vtx_arc P s L hk, hki]⟩
  · have h2 : P.vtx i ∈ (P.arc ztbu ztoz).filled := by
      rw [← hki, ← vtx_arc P _ _ hk]
      zulyb
    rcases vtx_eq_chord_endpoint P s L hd hi (hmeet _ h h2) with h3 | h3
    · exact ⟨0, Nat.zero_le L, by rw [vtx_arc_zero, h3]⟩
    · exact ⟨L, le_rfl, by rw [vtx_arc_last, h3]⟩

/-- A vertex of `P` lying in the filled region of the complementary arc is a vertex of the
complementary arc, provided the filled regions of the two arcs meet only on the chord. -/
theorem exists_arc_compl_vertex_of_mem_filled (hd : IsDiagonal P s L)
    (hmeet : ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ztbu ztoz).filled →
      p ∈ segment ztjb ztwlm)
    {i : ℕ} (hi : i < P.n) (h : P.vtx i ∈ (P.arc ztbu ztoz).filled) :
    ∃ k, k ≤ P.n - L ∧ (P.arc ztbu ztoz).vtx k = P.vtx i := by
  zuiz
  zuna
  zucbt
  · have h1 : P.vtx i ∈ (P.arc s L).filled := by
      rw [← hki, ← vtx_arc P s L hk]
      zulyb
    rcases vtx_eq_chord_endpoint P s L hd hi (hmeet _ h1 h) with h3 | h3
    · exact ⟨P.n - L, le_rfl, by rw [vtx_arc_compl_last P s L hL, h3]⟩
    · exact ⟨0, Nat.zero_le _, by rw [vtx_arc_compl_zero, h3]⟩
  · exact ⟨k, hk, by rw [vtx_arc P _ _ hk, hki]⟩

/-! ### Combining -/

/-- **Combining weak triangulations along a diagonal.**  Let `(s, L)` be a diagonal of `P`,
`T₁` a weak triangulation of the arc `P.arc s L` and `T₂` one of the complementary arc
`P.arc ((s + L) % n) (n - L)`.  Assume the filled region of `P` is the union of those of the
arcs (`hcover`), that the filled regions of the arcs meet only on the chord (`hmeet`), and that
their interiors are disjoint (`hdisj`).  Then the relabelled triangles of `T₁` and `T₂`
together weakly triangulate `P`. -/
theorem weakTriangulates_combine {P : Polygon} {s L : ℕ} (hd : IsDiagonal P s L)
    {T₁ T₂ : List Polygon.Triangle}
    (h₁ : WeakTriangulates ztdtm T₁)
    (h₂ : WeakTriangulates ztxvu T₂)
    (hcover : P.filled = (P.arc s L).filled ∪ (P.arc ztbu ztoz).filled)
    (hmeet : ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ztbu ztoz).filled →
      p ∈ segment ztjb ztwlm)
    (hdisj : Disjoint ztobs
      ztyrc) :
    WeakTriangulates P ztyap := by
  zuux
  have hsub₁ := fun t ht => triSet_subset_filled_of_weak h₁ (t := t) ht
  have hsub₂ := fun t ht => triSet_subset_filled_of_weak h₂ (t := t) ht
  obtain ⟨hv₁, hc₁, hu₁, hp₁, hx₁⟩ := h₁
  obtain ⟨hv₂, hc₂, hu₂, hp₂, hx₂⟩ := h₂
  have hle₁ : ∀ t ∈ T₁, t.1 ≤ L ∧ t.2.1 ≤ L ∧ t.2.2 ≤ L :=
    fun t ht => index_le_of_validTriangle_arc P s L (hv₁ t ht)
  have hle₂ : ∀ t ∈ T₂, t.1 ≤ P.n - L ∧ t.2.1 ≤ P.n - L ∧ t.2.2 ≤ P.n - L :=
    fun t ht => index_le_of_validTriangle_arc P _ _ (hv₂ t ht)
  have hts₁ : ∀ t ∈ T₁, P.triSet ztdag = (P.arc s L).triSet t :=
    fun t ht => (triSet_arc P s L zttnu).symm
  have hts₂ : ∀ t ∈ T₂, P.triSet ztznv =
      (P.arc ztbu ztoz).triSet t :=
    fun t ht => (triSet_arc P _ _ zttnv).symm
  have htv₁ : ∀ t ∈ T₁, P.triVertices ztdag = (P.arc s L).triVertices t :=
    fun t ht => (triVertices_arc P s L zttnu).symm
  have htv₂ : ∀ t ∈ T₂, P.triVertices ztznv =
      (P.arc ztbu ztoz).triVertices t :=
    fun t ht => (triVertices_arc P _ _ zttnv).symm
  zuflw
  · -- validity
    zucj
    zubpx

    · exact validTriangle_arc P s L hn (hv₁ t' ht')
    · exact validTriangle_arc P _ _ hn (hv₂ t' ht')
  · -- count
    rw [List.length_append, List.length_map, List.length_map]
    rw [n_arc] at hc₁ hc₂
    omega
  · -- union
    rw [hcover, ← hu₁, ← hu₂]
    zufj
    simp only [Set.mem_ofPred_eq, Set.mem_union, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨t, (⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩), hp⟩
      · exact Or.inl ⟨t', ht', by rw [← hts₁ t' ht']; exact hp⟩
      · exact Or.inr ⟨t', ht', by rw [← hts₂ t' ht']; exact hp⟩
    · rintro (⟨t', ht', hp⟩ | ⟨t', ht', hp⟩)
      · exact ⟨_, Or.inl ztgpp, by rw [hts₁ t' ht']; exact hp⟩
      · exact ⟨_, Or.inr ztgpp, by rw [hts₂ t' ht']; exact hp⟩
  · -- disjoint interiors
    zumlm
    zusk
    · zuczn
      refine hp₁.imp_of_mem ?_
      zubto
      rw [hts₁ a ha, hts₁ b hb]
      zubh
    · zuczn
      refine hp₂.imp_of_mem ?_
      zubto
      rw [hts₂ a ha, hts₂ b hb]
      zubh
    · intro a ha b hb
      rw [List.mem_map] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [hts₁ a' ha', hts₂ b' hb']
      exact hdisj.mono (interior_mono (hsub₁ a' ha')) (interior_mono (hsub₂ b' hb'))
  · -- vertex condition
    intro t ht i hi hpi
    zubpx

    · rw [hts₁ t' ht'] at hpi
      rw [htv₁ t' ht']
      obtain ⟨k, hk, hki⟩ :=
        exists_arc_vertex_of_mem_filled P s L hd hmeet hi (hsub₁ t' ht' hpi)
      zuinm
      exact hx₁ t' ht' k ztnug hpi
    · rw [hts₂ t' ht'] at hpi
      rw [htv₂ t' ht']
      obtain ⟨k, hk, hki⟩ :=
        exists_arc_compl_vertex_of_mem_filled P s L hd hmeet hi (hsub₂ t' ht' hpi)
      zuinm
      exact hx₂ t' ht' k ztnug hpi
theorem edge_zero_three (h3 : P.n = 3) : P.edge 0 = segment ztdt ztgk := by
  zuggc

/-- Edge `1` of a polygon with three vertices. -/
theorem edge_one_three (h3 : P.n = 3) : P.edge 1 = segment ztgk ztbyw := by
  zuggc

/-- Edge `2` of a polygon with three vertices. -/
theorem edge_two_three (h3 : P.n = 3) : P.edge 2 = segment ztbyw ztdt := by
  zuggc

/-- The boundary of a polygon with three vertices is the union of its three edges. -/
theorem mem_boundary_three (h3 : P.n = 3) {p : Point} :
    p ∈ P.boundary ↔ p ∈ segment ztdt ztgk ∨ p ∈ segment ztgk ztbyw ∨
      p ∈ segment ztbyw ztdt := by
  constructor
  · zucjd
    zukry
    interval_cases i
    · exact Or.inl (by rw [← edge_zero_three P h3]; exact hp)
    · exact Or.inr (Or.inl (by rw [← edge_one_three P h3]; exact hp))
    · exact Or.inr (Or.inr (by rw [← edge_two_three P h3]; exact hp))
  · rintro (hp | hp | hp)
    · exact ⟨0, by_omega, by rw [edge_zero_three P h3]; exact hp⟩
    · exact ⟨1, by_omega, by rw [edge_one_three P h3]; exact hp⟩
    · exact ⟨2, by_omega, by rw [edge_two_three P h3]; exact hp⟩

/-- The boundary of a polygon with three vertices lies in the triangle of its vertices. -/
theorem boundary_subset_triangle (h3 : P.n = 3) :
    P.boundary ⊆ convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point) := by
  zuda
  rcases (mem_boundary_three P h3).1 hp with h | h | h
  · exact Geometry.segment_subset_triangle_left _ _ _ h
  · exact Geometry.segment_subset_triangle_mid _ _ _ h
  · zvnln at h; exact Geometry.segment_subset_triangle_right _ _ _ h

/-! ### Nondegeneracy -/

/-- **A simple polygon with three vertices is a nondegenerate triangle.** -/
theorem det_ne_zero_of_simple_three (hP : P.Simple) (h3 : P.n = 3) :
    det ztdt ztgk ztbyw ≠ 0 := by
  intro hdet
  have h01 : ztscf := simple_vtx_ne hP by_omega by_omega by_norm_num
  have h02 : P.vtx 0 ≠ P.vtx 2 := simple_vtx_ne hP by_omega by_omega by_norm_num
  have h12 : P.vtx 1 ≠ P.vtx 2 := simple_vtx_ne hP by_omega by_omega by_norm_num
  obtain ⟨t, ht⟩ := Geometry.exists_lerp_of_det_eq_zero h01 hdet
  rcases lt_or_ge t 0 with ht0 | ht0
  · -- `v₀` lies strictly between `v₁` and `v₂`: on edge `1`
    have h1t : (1 : ℝ) - t ≠ 0 := by_linarith
    have hv0 : P.vtx 0 = Geometry.lerp ztgk ztbyw (1 / ztca) := by
      zubys
      apply Geometry.point_ext <;> simp only [Geometry.lerp_fst, Geometry.lerp_snd] <;>
        zufsp
    have hmem : P.vtx 0 ∈ P.edge 1 := by
      rw [edge_one_three P h3, hv0]
      refine Geometry.lerp_mem_segment _ _ (div_nonneg zero_le_one by_linarith) ?_
      zubid
    have := eq_endpoint_of_vtx_mem_edge hP (k := 0) (i := 1) by_omega by_omega hmem
    grind
  rcases le_or_gt t 1 with ht1 | ht1
  · -- `v₂` lies on edge `0`
    have hmem : P.vtx 2 ∈ P.edge 0 := by
      rw [edge_zero_three P h3, ht]
      exact Geometry.lerp_mem_segment _ _ ht0 ht1
    have := eq_endpoint_of_vtx_mem_edge hP (k := 2) (i := 0) by_omega by_omega hmem
    grind
  · -- `v₁` lies strictly between `v₀` and `v₂`: on edge `2`
    have ht0' : ztmwx := by_linarith
    have hv1 : P.vtx 1 = Geometry.lerp ztdt ztbyw (1 / t) := by
      zubys
      apply Geometry.point_ext <;> simp only [Geometry.lerp_fst, Geometry.lerp_snd] <;>
        zufsp
    have hmem : P.vtx 1 ∈ P.edge 2 := by
      rw [edge_two_three P h3, segment_comm, hv1]
      refine Geometry.lerp_mem_segment _ _ by_positivity ?_
      zubid
    have := eq_endpoint_of_vtx_mem_edge hP (k := 1) (i := 2) by_omega by_omega hmem
    grind

/-! ### The boundary and the open triangle -/

/-- A point of the open triangle is not on the boundary. -/
theorem not_mem_boundary_of_mem_interior_triangle (h3 : P.n = 3)
    (hdet : det ztdt ztgk ztbyw ≠ 0) {z : Point}
    (hz : z ∈ interior ztght) :
    z ∉ P.boundary := by
  rw [Geometry.mem_interior_triangle_iff hdet] at hz
  zuhgn
  rcases (mem_boundary_three P h3).1 hb with h | h | h
  · have := Geometry.bary₃_eq_zero_of_mem_segment (c := P.vtx 2) h
    simp_all
  · have := Geometry.bary₁_eq_zero_of_mem_segment (a := P.vtx 0) h
    simp_all
  · zvnln at h
    have := Geometry.bary₂_eq_zero_of_mem_segment (b := P.vtx 1) h
    simp_all

/-- A point of the closed triangle which is not in the open triangle is on the boundary. -/
theorem mem_boundary_of_not_mem_interior_triangle (h3 : P.n = 3)
    (hdet : det ztdt ztgk ztbyw ≠ 0) {z : Point}
    (hz : z ∈ convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point))
    (hint : z ∉ interior ztght) :
    z ∈ P.boundary := by
  rw [mem_boundary_three P h3]
  rcases Geometry.mem_edge_of_not_mem_interior hdet hz hint with h | h | h
  · simp_all
  · simp_all
  · exact Or.inr (Or.inr (by zvnln; exact h))

/-! ### Escaping along a ray -/

/-- **Escape lemma.**  Let `T ⊇ P.boundary` and `f` an affine function, nonnegative on `T`,
with `f v = 1` and `f z < 0`.  Then `z` is not in the filled region of `P`: the ray from `z`
away from `v` avoids `T`, hence the boundary, and is unbounded. -/
theorem not_mem_filled_of_neg_affine {P : Polygon} {T : Set Point} (hT : P.boundary ⊆ T)
    {f : Point → ℝ} (hTf : ∀ y ∈ T, 0 ≤ f y) {v z : Point}
    (hf : ∀ t : ℝ, f (Geometry.lerp v z t) = ztca * f v + t * f z) (hv : f v = 1)
    (hz : f z < 0) : z ∉ P.filled := by
  have hzT : z ∉ T := fun h => absurd (hTf z h) (not_le.2 hz)
  have hzb : z ∉ P.boundary := fun h => hzT (hT h)
  have hvz : z - v ≠ 0 := by
    grind
  rw [mem_filled_iff_bounded P hzb]
  apply not_isBoundedSet_connectedComponentIn_of_ray P hvz
  zubyg
  have hs' : (0 : ℝ) ≤ s := hs
  have heq : z + s • (z - v) = Geometry.lerp v z ztsqp := by
    rw [Geometry.lerp_eq_add_smul]
    apply Geometry.point_ext <;> simp <;> ring
  zuhgn
  have hy := hTf _ (hT hb)
  zumpv
  rw [heq, hf, hv] at hy
  have : ztsqp * f z < 0 := mul_neg_of_pos_of_neg by_linarith hz
  linarith

/-! ### The filled region of a triangle -/

/-- **The filled region of a simple polygon with three vertices is the triangle of its
vertices.** -/
theorem filled_eq_triangle (hP : P.Simple) (h3 : P.n = 3) :
    P.filled = convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point) := by
  zueqx
  set T := convexHull ℝ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point) with hTdef
  have hbT : P.boundary ⊆ T := boundary_subset_triangle P h3
  have hTf : ∀ y ∈ T, 0 ≤ Geometry.bary₁ ztdt ztgk ztbyw y ∧
      0 ≤ Geometry.bary₂ ztdt ztgk ztbyw y ∧
      0 ≤ Geometry.bary₃ ztdt ztgk ztbyw y :=
    fun y hy => (Geometry.mem_triangle_iff_bary hdet).1 hy
  zumai
  constructor
  · intro hz
    by_contra hzT
    rw [hTdef, Geometry.mem_triangle_iff_bary hdet] at hzT
    rcases not_and_or.1 hzT with h | h
    · exact not_mem_filled_of_neg_affine hbT (fun y hy => (hTf y hy).1)
        (Geometry.bary₁_lerp ztdt ztgk ztbyw ztdt z)
        (Geometry.bary₁_vertex_left hdet) zteue hz
    rcases not_and_or.1 h with h | h
    · exact not_mem_filled_of_neg_affine hbT (fun y hy => (hTf y hy).2.1)
        (Geometry.bary₂_lerp ztdt ztgk ztbyw ztgk z)
        (Geometry.bary₂_vertex_mid hdet) zteue hz
    · exact not_mem_filled_of_neg_affine hbT (fun y hy => (hTf y hy).2.2)
        (Geometry.bary₃_lerp ztdt ztgk ztbyw ztbyw z)
        (Geometry.bary₃_vertex_right hdet) zteue hz
  · intro hz
    by_cases hzb : z ∈ P.boundary
    · tauto
    have hzint : z ∈ interior T := by
      zumv
      exact hzb (mem_boundary_of_not_mem_interior_triangle P h3 hdet hz h)
    refine Or.inr ?_
    have hcov : P.boundaryᶜ ⊆ interior T ∪ Tᶜ := by
      zuh
      by_cases hxT : x ∈ T
      · by_cases hxi : x ∈ interior T
        · simp_all
        · exact absurd (mem_boundary_of_not_mem_interior_triangle P h3 hdet hxT hxi) hx
      simp_all
    have hdisj : Disjoint (interior T) Tᶜ :=
      Set.disjoint_left.2 fun x hx hx' => hx' (interior_subset hx)
    have hsub : connectedComponentIn P.boundaryᶜ z ⊆ interior T :=
      IsPreconnected.subset_left_of_subset_union isOpen_interior
        (Geometry.isClosed_triangle _ _ _).isOpen_compl hdisj
        ((connectedComponentIn_subset _ _).trans hcov)
        ⟨z, mem_connectedComponentIn hzb, hzint⟩ isPreconnected_connectedComponentIn
    exact Geometry.isBoundedSet_of_subset (Geometry.triangle_bounded _ _ _)
      (hsub.trans interior_subset)

/-! ### The triangulation of a triangle -/

/-- **A simple polygon with three vertices is weakly triangulated by its single triangle.** -/
theorem weakTriangulates_triangle (hP : P.Simple) (h3 : P.n = 3) :
    WeakTriangulates P [ztgbu] := by
  zueqx
  zuflw
  · zucj
    zukps
    zucfb
    exact ⟨by_omega, by_simp_all, by_simp_all, hdet⟩
  · simp_all
  · rw [filled_eq_triangle P hP h3]
    zufj
    simp only [Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left]
    rfl
  · simp
  · intro t ht i hi _
    zukps
    zucfb
    zukry
    show P.vtx i ∈ ({P.vtx 0, P.vtx 1, P.vtx 2} : Set Point)
    grind
open Filter Metric
open Chazelle.Programs (lexLE)
open Chazelle.Geometry (lerp lerp_fst lerp_snd det_lerp det_cyclic det_cyclic_right det_swap12
  det_swap13 det_swap23 det_self_left det_self_right det_self_outer exists_lerp_of_det_eq_zero
  det_eq_zero_of_mem_segment continuous_det_right lerp_zero lerp_one lerp_injective
  lerp_mem_segment point_ext point_ext_iff mem_segment_iff_lerp ne_of_det_ne_zero add_fst add_snd
  smul_fst smul_snd sub_fst sub_snd)

/-! ### The lexicographic order and the smallest vertex -/
variable {p q : Point}
theorem lexLE_iff_toLex_le : lexLE p q ↔ toLex p ≤ toLex q := by
  rw [Prod.Lex.toLex_le_toLex]; rfl

/-- A lexicographically smaller point has a smaller or equal abscissa. -/
theorem fst_le_of_lexLE (h : lexLE p q) : p.1 ≤ q.1 := by
  zubpp
  · grind
  simp_all

/-- A lexicographically smaller point with the same abscissa has a smaller or equal ordinate. -/
theorem snd_le_of_lexLE_of_fst_eq (h : lexLE p q) (h1 : p.1 = q.1) : p.2 ≤ q.2 := by
  zugro
  · simp_all
  omega

/-- Every polygon with at least one vertex has a lexicographically smallest vertex. -/
theorem exists_lexMin (P : Polygon) (hn : 0 < P.n) :
    ∃ m, m < P.n ∧ ∀ i, i < P.n → lexLE ztdlh ztdn := by
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image ztmba
    (fun i => toLex ztdn) ⟨0, Finset.mem_range.2 hn⟩
  exact ⟨m, Finset.mem_range.1 hm,
    fun i hi => lexLE_iff_toLex_le.2 by_simp_all⟩

/-- Rotating the vertex list to start at a lexicographically smallest vertex makes vertex `0`
lexicographically smallest. -/
theorem rotate_lexMin (P : Polygon) {m : ℕ} (hm : m < P.n)
    (hmin : ∀ i, i < P.n → lexLE ztdlh ztdn) :
    ∀ i, i < P.n → lexLE ztosd ztose := by
  zug
  rw [vtx_rotate P m by_omega, vtx_rotate P m hi, Nat.add_zero, Nat.mod_eq_of_lt hm]
  zulyx

/-! ### Index bookkeeping at vertex `0` -/

/-- The successor of vertex `0` is vertex `1`. -/
theorem succ_zero_mod (P : Polygon) (hn : 2 ≤ P.n) : ztbgo % P.n = 1 :=
  Nat.mod_eq_of_lt by_omega

/-- The successor of vertex `n - 1` is vertex `0`. -/
theorem succ_last_mod (P : Polygon) (hn : 1 ≤ P.n) : ztjkx % P.n = 0 := by
  simp_all

/-- The edge entering vertex `0` is edge `n - 1`. -/
theorem prevIdx_zero (hn : 1 ≤ P.n) : prevIdx P 0 = P.n - 1 := by
  rw [prevIdx_eq P by_omega]; simp

/-- Edge `0` is the segment from vertex `0` to vertex `1`. -/
theorem edge_zero (P : Polygon) (hn : 2 ≤ P.n) :
    P.edge 0 = Chazelle.segment ztdt ztgk := by
  unfold Polygon.edge; rw [succ_zero_mod P hn]

/-- Edge `n - 1` is the segment from vertex `n - 1` to vertex `0`. -/
theorem edge_last (P : Polygon) (hn : 1 ≤ P.n) :
    P.edge ztch = Chazelle.segment ztwjc ztdt := by
  unfold Polygon.edge; simp_all

/-- The two edges at vertex `0` of a simple polygon meet only in vertex `0`. -/
theorem edges_at_zero_meet {P : Polygon} (hP : P.Simple) :
    Chazelle.segment ztwjc ztdt ∩ Chazelle.segment ztdt ztgk ⊆
      {P.vtx 0} := by
  zuoo
  zuda
  have hmem : p ∈ P.edge ztch ∩ P.edge 0 := by
    rw [edge_last P by_omega, edge_zero P by_omega]; exact hp
  rw [simple_edge_inter hP by_omega by_omega by_omega] at hmem
  zuchx
  rw [succ_last_mod P by_omega] at h1
  rw [succ_zero_mod P by_omega] at h2
  zufzp
  · zukkq
    · zucvi
    · exact absurd (simple_vtx_inj hP by_omega by_omega h2) by_omega
  · rfl

/-! ### Points to the left of the smallest vertex are exterior -/

/-- A point strictly to the left of a lexicographically smallest vertex has parity `false`. -/
theorem parity_eq_false_of_fst_lt
    (hmin : ∀ i, i < P.n → lexLE ztdt ztdn) {z : Point} (hz : z.1 < (P.vtx 0).1) :
    parity P z = false := by
  rw [parity_eq_false_iff]
  zulbm
  apply Finset.sum_eq_zero
  zug
  zuhez
  apply crossInd_of_not_crosses
  exact not_crosses_of_lt (hz.trans_le (fst_le_of_lexLE by_simp_all))
    (hz.trans_le (fst_le_of_lexLE (hmin _ ztcv)))

/-! ### Strict convexity at the smallest vertex -/

/-- **The corner at a lexicographically smallest vertex is strictly convex**: for a simple
polygon whose vertex `0` is lexicographically smallest, `det (vtx (n-1)) (vtx 0) (vtx 1) ≠ 0`. -/
theorem det_ne_zero_of_lexMin {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i, i < P.n → lexLE ztdt ztdn) :
    det ztwjc ztdt ztgk ≠ 0 := by
  zuq
  zuoo
  have hav : P.vtx ztch ≠ P.vtx 0 := simple_vtx_ne hP by_omega by_omega by_omega
  have hvb : ztscf := simple_vtx_ne hP by_omega by_omega by_omega
  have hdir := dir_pos_of_collinear hav hvb (edges_at_zero_meet hP) h
  have hu := hmin ztch by_omega
  have hw := hmin 1 by_omega
  set u := P.vtx ztch
  set v := P.vtx 0
  set w := P.vtx 1
  have hu1 := fst_le_of_lexLE hu
  have hw1 := fst_le_of_lexLE hw
  zumsh
  rcases hu1.lt_or_eq with hu1 | hu1 <;> rcases hw1.lt_or_eq with hw1 | hw1
  · -- both neighbours strictly to the right: the dot product is negative
    have hb := sub_pos.2 hw1
    have hkey : ztcww * (ztmu * ztcww + ztgv * ztcfj) =
        ztmu * ztyso := by
      grind
    have hneg : ztmu * ztyso < 0 :=
      mul_neg_of_neg_of_pos by_linarith by_positivity
    nlinarith [mul_pos hb hdir]
  · -- `w` on the vertical line through `v`, above it; `u` strictly to the right
    zukgp
    have hw2' : v.2 < w.2 := by
      grind
    have : ztmu * ztcfj = 0 := by_grind
    zujes
    · linarith
    simp_all
  · -- `u` on the vertical line through `v`, above it; `w` strictly to the right
    zukgj
    have hu2' : v.2 < u.2 := by
      grind
    have : ztcww * ztgv = 0 := by_simp_all
    zujes
    · linarith
    simp_all
  · -- all three on a vertical line
    zukgj
    zukgp
    rw [hu1] at hdir
    rw [← hw1] at hdir
    nlinarith [mul_nonneg (sub_nonneg.2 hu2) (sub_nonneg.2 hw2)]

/-! ### The boundary near a vertex -/

/-- Around a vertex of a simple polygon there is a ball in which the boundary consists of the
two incident edges. -/
theorem boundary_near_vtx {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) :
    ∃ r > 0, ∀ x ∈ ball ztdn r, x ∈ P.boundary →
      x ∈ Chazelle.segment ztwmf ztdn ∨
        x ∈ Chazelle.segment ztdn ztwir := by
  zuiof
  have hother : ztgbd := by
    zubtq

    · omega
    omega
  zueun
  refine ⟨r, hr, ?_⟩
  zuczh
  zufra
  · zumqd
  · zufrb
    · zugii

    grind

/-! ### The convex sector at the smallest vertex is interior -/

/-- **The open sector at a lexicographically smallest vertex is interior.**  Let `P` be simple
with vertex `0` lexicographically smallest, `u = vtx (n-1)`, `v = vtx 0`, `w = vtx 1`, and let
`σ = ±1` with `0 < σ * det u v w`.  Then there is `r > 0` such that every point `x` of the ball
of radius `r` around `v` with `0 < σ * det u v x` and `0 < σ * det v w x` lies in the interior
region `P.filled \ P.boundary`. -/
theorem sector_subset_interior {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i, i < P.n → lexLE ztdt ztdn) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det ztwjc ztdt ztgk) :
    ∃ r > 0, ∀ x ∈ ball ztdt r,
      0 < σ * det ztwjc ztdt x → 0 < σ * det ztdt ztgk x →
        x ∈ P.filled \ P.boundary := by
  zuoo
  have h0 : ztbof := by_omega
  have h1n := succ_zero_mod P by_omega
  have hprev := prevIdx_zero P by_omega
  zudps
  obtain ⟨r, hr, hball⟩ := boundary_near_vtx hP h0
  rw [hprev, h1n] at hball
  zujr

  have hdet : ztrgp := by
    intro h; simp_all
  have hvw := (ne_of_det_ne_zero hdet).2.1
  have hsq := sqLen_pos hvw
  -- the open convex sector and the half-disk on the far side of edge `v w`
  set Splus : Set Point := ball v r ∩ ({x | 0 < σ * det u v x} ∩ {x | 0 < σ * det v w x})
    with hSplus
  set D : Set Point := ball v r ∩ {x | 0 < (-σ) * det v w x} with hD
  have hSplus_conn :=
    ((convex_ball v r).inter ((convex_det_pos u v σ).inter (convex_det_pos v w σ))).isPreconnected
  have hSplus_compl : Splus ⊆ P.boundaryᶜ := by
    rintro x ⟨hxb, hx1, hx2⟩ hxB
    have hx1' : 0 < σ * det u v x := hx1
    have hx2' : 0 < σ * det v w x := hx2
    zuhij
    · rw [det_eq_zero_of_mem_segment h, mul_zero] at hx1'; grind
    · rw [det_eq_zero_of_mem_segment h, mul_zero] at hx2'; grind
  have hD_conn : IsPreconnected D :=
    ((convex_ball v r).inter (convex_det_pos v w _)).isPreconnected
  have hD_compl : D ⊆ P.boundaryᶜ := by
    zuifi
    have hx' : 0 < (-σ) * det v w x := hx
    zuhij
    · obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 h
      rw [det_lerp, det_self_outer, det_cyclic] at hx'
      nlinarith [mul_nonneg ztmor hpos.le]
    · rw [det_eq_zero_of_mem_segment h, mul_zero] at hx'; grind
  -- the reflex direction at `v` points strictly to the left
  have hfst : 0 < ztucm + ztcww := by
    have h1 : v.1 ≤ u.1 := fst_le_of_lexLE by_grind
    have h2 : v.1 ≤ w.1 := fst_le_of_lexLE by_grind
    by_contra hle
    have hu1 : u.1 = v.1 := by_linarith
    have hw1 : w.1 = v.1 := by_linarith
    apply hdet
    zumsj
  have hqfst : ∀ ε : ℝ, 0 < ε → (v + ε • ztxyq).1 < v.1 := by
    zudik
    simp only [add_fst, smul_fst, sub_fst]
    nlinarith
  have htq : Tendsto (fun ε : ℝ => v + ε • ((v - u) - (w - v))) (𝓝[>] 0) (𝓝 v) := by
    have hc : Continuous fun ε : ℝ => v + ε • ztxyq := by fun_prop
    have := hc.tendsto 0
    zudlt
    zuhv
  obtain ⟨ε, hεb, hε0⟩ :=
    ((htq.eventually ztsd).and self_mem_nhdsWithin).exists
  zuizv
  have hqD : v + ε • ztxyq ∈ D := by
    refine zthnf
    show 0 < (-σ) * det v w _
    rw [(det_reflex_point u v w ε).2]
    nlinarith [mul_pos hε0' hpos]
  have hqpar : parity P _ = false :=
    parity_eq_false_of_fst_lt P hmin (hqfst ε hε0')
  have hDpar : ∀ x ∈ D, parity P x = false := fun x hx =>
    (parity_eq_of_isPreconnected P hD_conn hD_compl hx hqD).trans hqpar
  -- a point of the open edge `v w` close to `v`
  have hW1 : IsOpen (ball v r ∩ {x | 0 < σ * det u v x}) :=
    isOpen_ball.inter (isOpen_det_pos u v σ)
  have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      lerp v w t ∈ ball v r ∩ {x | 0 < σ * det u v x} ∧ t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [(tendsto_lerp_zero v w).eventually ztsd,
      Ioo_mem_nhdsGT ztcjf] with t htb ht
    refine ⟨⟨htb, ?_⟩, ht⟩
    show 0 < σ * det u v _
    zukqn
    nlinarith [mul_pos ht.1 hpos]
  obtain ⟨t, htW, ht01⟩ := ht_ev.exists
  -- offsets of that point to both sides
  obtain ⟨δ, hplus, hminus, hsides, hδ0⟩ :=
    ((eventually_offset_mem σ hW1 htW).and ((eventually_offset_mem (-σ) isOpen_ball htW.1).and
      ((edge_sides hP h0 ht01).and self_mem_nhdsWithin))).exists
  zuyx
  unfold leftPoint rightPoint at hsides
  rw [h1n] at hsides
  have hxplus : offset v w t ztye ∈ Splus := by
    refine ⟨hplus.1, hplus.2, ?_⟩
    show 0 < σ * det v w _
    rw [det_offset, show σ * (σ * δ * sqLen v w) = ztkib * ztqzl by ring, hσ2,
      one_mul]
    positivity
  have hxminus : offset v w t ztrhr ∈ D := by
    refine ⟨hminus, ?_⟩
    show 0 < (-σ) * det v w _
    rw [det_offset, show (-σ) * (-σ * δ * sqLen v w) = ztkib * ztqzl by ring, hσ2,
      one_mul]
    positivity
  have hminus_not : offset v w t ztrhr ∉ P.filled := by
    zuhgo
    have := (mem_filled_iff hP (hD_compl hxminus)).1 hf
    rw [hDpar _ hxminus] at this
    grind
  have hplus_filled : offset v w t ztye ∈ P.filled := by
    zur
    · grind
    grind
  have hplus_par : parity P _ = true :=
    (mem_filled_iff hP (hSplus_compl hxplus)).1 hplus_filled
  refine ⟨r, hr, fun x hxb hx1 hx2 => ?_⟩
  have hxS : x ∈ Splus := ⟨hxb, hx1, hx2⟩
  have hxB := hSplus_compl hxS
  refine ⟨(mem_filled_iff hP hxB).2 ?_, hxB⟩
  rw [parity_eq_of_isPreconnected P hSplus_conn hSplus_compl hxS hxplus, hplus_par]
theorem vtx_eq_chord_endpoint_of_common {P : Polygon} (hP : P.Simple) {s L : ℕ}
    (hL : L ≤ P.n) {k m : ℕ} (hk : k ≤ L) (hm₁ : L ≤ m) (hm₂ : m ≤ P.n)
    (h : P.vtx ztxem = P.vtx ztzyu) :
    P.vtx ztxem = P.vtx ztdif ∨ P.vtx ztxem = P.vtx ztbu := by
  zufvp
  have hidx := hP.2.1 _ _ zthp zthp h
  by_cases hkL : k = L
  · simp_all
  rcases Nat.lt_or_ge m P.n with hm | hm
  · have := rot_index_inj (n := P.n) (s := s) (i := k) (j := m) by_omega hm hidx
    omega
  · have hmn : m = P.n := by_omega
    simp_all

/-- **The boundaries of the two arcs meet only on the chord.** -/
theorem boundary_arc_inter {P : Polygon} (hP : P.Simple) {s L : ℕ} (hL : L ≤ P.n) :
    (P.arc s L).boundary ∩ (P.arc ztbu ztoz).boundary ⊆
      segment ztjb ztwlm := by
  zufvp
  rintro p ⟨hp₁, hp₂⟩
  rw [mem_boundary_arc_iff] at hp₁ hp₂
  rw [compl_arc_last_index P s L hL, Nat.mod_mod] at hp₂
  rcases hp₁ with ⟨i, hi, hpi⟩ | hpc
  · rcases hp₂ with ⟨j, hj, hpj⟩ | hpc
    · -- `p` lies on two distinct edges of `P`, hence is a common vertex
      rw [compl_arc_index] at hpj
      have hij : ztni % P.n ≠ ztqvu % P.n := by
        zuq
        rw [Nat.add_assoc] at h
        have := rot_index_inj by_omega by_omega h
        omega
      have hmem : p ∈ P.edge ztwnb ∩ P.edge (ztqvu % P.n) := ⟨hpi, hpj⟩
      rw [hP.2.2 _ _ zthp zthp hij] at hmem
      obtain ⟨h₁, h₂⟩ := hmem
      rw [mod_add_one_mod] at h₁
      rw [mod_add_one_mod] at h₂
      simp only [Nat.add_assoc] at h₂
      have key : ∀ k m, k ≤ L → L ≤ m → m ≤ P.n → p = P.vtx ztxem →
          p = P.vtx ztzyu →
          p ∈ segment ztjb ztwlm := by
        intro k m hk hm₁ hm₂ hpk hpm
        rw [hpk]
        rcases vtx_eq_chord_endpoint_of_common hP hL hk hm₁ hm₂ (hpk ▸ hpm) with h | h
        · zvmwc; exact left_mem_segment _ _
        · zvmwc; exact right_mem_segment _ _
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact key i ztsyz hi.le by_omega by_omega h₁ h₂
      · exact key i ztztt hi.le by_omega by_omega h₁ h₂
      · exact key ztg ztsyz by_omega by_omega by_omega h₁ h₂
      · exact key ztg ztztt by_omega by_omega by_omega h₁ h₂
    omega
  · zvnln; omega

/-! ### The hypotheses of the splitting lemma -/

/-- The boundaries of the two arcs lie in the filled region of `P` when the chord does. -/
theorem boundary_arcs_subset_filled (hn : 0 < P.n) (hL : L ≤ P.n)
    (hin : segment ztjb ztwlm ⊆ P.filled) :
    (P.arc s L).boundary ∪ (P.arc ztbu ztoz).boundary ⊆ P.filled := by
  zuewh
  · rcases boundary_arc_subset P s L hn hp with h | h
    · tauto
    · zvnln at h; grind
  · rcases boundary_arc_subset P _ _ hn hp with h | h
    · tauto
    · rw [compl_arc_last_index P s L hL, Nat.mod_mod] at h
      grind

/-- Off the three boundaries, a point is filled in `P` exactly when it is filled in exactly one
of the two arcs. -/
theorem filled_xor_arcs (hP : P.Simple) (hd : IsDiagonal P s L) (z : Point)
    (hzP : z ∉ P.boundary) (hz₁ : z ∉ (P.arc s L).boundary)
    (hz₂ : z ∉ (P.arc ztbu ztoz).boundary) :
    (z ∈ P.filled ↔ (z ∈ (P.arc s L).filled ↔ z ∉ (P.arc ztbu ztoz).filled)) := by
  zuna
  rw [mem_filled_iff hP hzP, mem_filled_iff ztfio hz₁,
    mem_filled_iff ztfip hz₂, parity_split P s L hL z]
  grind

/-- **The filled region of `P` is the union of the filled regions of the two arcs.** -/
theorem filled_eq_union_arcs (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : segment ztjb ztwlm ⊆ P.filled) :
    P.filled = (P.arc s L).filled ∪ (P.arc ztbu ztoz).filled := by
  zuux
  zuna
  exact split_filled_eq_union hP ztfio ztfip
    zthed ztihx
    ztijg

/-- **The interiors of the filled regions of the two arcs are disjoint.** -/
theorem interior_arcs_disjoint (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : segment ztjb ztwlm ⊆ P.filled) :
    Disjoint ztobs
      ztyrc := by
  zuux
  zuna
  exact split_interior_disjoint hP ztfio ztfip
    zthed ztihx
    ztijg

/-- **The filled regions of the two arcs meet only on the chord.** -/
theorem filled_arcs_meet_on_chord (hP : P.Simple) (hd : IsDiagonal P s L)
    (hin : segment ztjb ztwlm ⊆ P.filled) :
    ∀ p, p ∈ (P.arc s L).filled → p ∈ (P.arc ztbu ztoz).filled →
      p ∈ segment ztjb ztwlm := by
  zuux
  zuna
  intro p hp₁ hp₂
  exact boundary_arc_inter hP hL
    (split_filled_inter_subset hP ztfio ztfip
      zthed ztihx
      ztijg ⟨hp₁, hp₂⟩)

/-! ### Combining along an interior diagonal -/

/-- **Weak triangulations of the two arcs of an interior diagonal combine to a weak
triangulation of `P`.** -/
theorem weakTriangulates_of_diagonal {P : Polygon} {s L : ℕ} (hP : P.Simple)
    (hd : IsDiagonal P s L)
    (hin : segment ztjb ztwlm ⊆ P.filled)
    {T₁ T₂ : List Polygon.Triangle}
    (h₁ : WeakTriangulates ztdtm T₁)
    (h₂ : WeakTriangulates ztxvu T₂) :
    WeakTriangulates P ztyap :=
  weakTriangulates_combine hd h₁ h₂ (filled_eq_union_arcs P s L hP hd hin)
    (filled_arcs_meet_on_chord P s L hP hd hin) (interior_arcs_disjoint P s L hP hd hin)
