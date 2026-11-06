module

public import Chazelle.Mountain.Decompose
public import Chazelle.Mountain.Stack

/-!
# Pieces of the mountain decomposition, local extrema and monotone chains

This file sets up the statement of the mountain decomposition theorem (the final open
obligation of `Chazelle.Mountain.Decompose`) and proves its combinatorial part.

## Definitions

* `IsLocMin Q k`, `IsLocMax Q k`: vertex `k` of `Q` is a strict `ylexLT`-local minimum
  (maximum): both cyclic neighbours are strictly `ylexLT`-greater (smaller).
* `ChainInc Q a`: the vertices `Q.vtx ((a+1) % n), …, Q.vtx a`, in cyclic order starting after
  vertex `a`, are strictly `ylexLT`-increasing; `ChainDec Q a`: strictly decreasing.
* `IsMountainAt Q a := Q.Simple ∧ a < Q.n ∧ ChainInc Q a`: `Q` is a monotone mountain with base
  the edge `a` (from the maximum `Q.vtx a` to the minimum `Q.vtx ((a+1) % n)`);
  `isMountainAt_iff`: this is `IsMountain (Q.rotate ((a + 1) % Q.n))` (`Chazelle.Mountain.Stack`).
* `IsMonoAt Q a`: the same up to orientation (`ChainInc Q a ∨ ChainDec Q a`).
* `IsPiece P l`: `l` is a face of the subdivision of `P` by `allDiagonals P`.

## Combinatorics (`chain_of_extrema`, `isMonoAt_of_extrema`)

For a cyclic sequence of pairwise distinct points, if every strict local minimum is at
position `m` and every strict local maximum is at position `M`, and `m`, `M` are cyclically
adjacent, then the sequence is strictly monotone from `m` to `M` the long way round.  (The
global minimum is a local minimum, hence at `m`; walking from `m`, the first descent would be a
local maximum other than `M`.)
-/

namespace Chazelle.Mountain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly vtx_subPoly_getD subPoly_rotate subPoly_range)
open Chazelle.Existence (vtx_mem_boundary simple_rotate n_rotate vtx_rotate)

/-! ### Generic cyclic combinatorics -/

section Cyclic

variable {α : Type}

/-- A strict total order given by a relation: transitive, irreflexive, total on distinct
elements. -/
structure StrictTotal (r : α → α → Prop) : Prop where
  trans : ∀ x y z, r x y → r y z → r x z
  irrefl : ∀ x, ¬ r x x
  total : ∀ x y, x ≠ y → r x y ∨ r y x

/-- `ylexLT` is a strict total order. -/
theorem strictTotal_ylexLT : StrictTotal ylexLT :=
  ⟨fun _ _ _ h1 h2 => ylexLT_trans h1 h2, ylexLT_irrefl, fun p q h => by
    rcases ylexLT_trichotomy p q with h' | h' | h'
    · exact Or.inl h'
    · exact absurd h' h
    · exact Or.inr h'⟩

/-- A finite injective sequence has a strictly smallest element. -/
theorem exists_minimal_idx {r : α → α → Prop} (hr : StrictTotal r) {f : ℕ → α} {n : ℕ}
    (hn : 0 < n) (hinj : ∀ i j, i < n → j < n → f i = f j → i = j) :
    ∃ k < n, ∀ j < n, j ≠ k → r (f k) (f j) := by
  induction n with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, by omega, fun j hj hjk => by omega⟩
    · obtain ⟨k, hk, hmin⟩ := ih hN (fun i j hi hj h => hinj i j (by omega) (by omega) h)
      have hne : f k ≠ f N := fun h => by
        have := hinj k N (by omega) (by omega) h
        omega
      rcases hr.total _ _ hne with h | h
      · refine ⟨k, by omega, fun j hj hjk => ?_⟩
        rcases Nat.lt_or_ge j N with hjN | hjN
        · exact hmin j hjN hjk
        · obtain rfl : j = N := by omega
          exact h
      · refine ⟨N, by omega, fun j hj hjk => ?_⟩
        have hjN : j < N := by omega
        by_cases hjk' : j = k
        · subst hjk'; exact h
        · exact hr.trans _ _ _ h (hmin j hjN hjk')

/-- Cyclic predecessor is different from the index (for `2 ≤ n`). -/
theorem pred_mod_ne {n k : ℕ} (hn : 2 ≤ n) (hk : k < n) : (k + n - 1) % n ≠ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show k + n - 1 = (k - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Cyclic successor is different from the index (for `2 ≤ n`). -/
theorem succ_mod_ne {n k : ℕ} (hn : 2 ≤ n) (hk : k < n) : (k + 1) % n ≠ k := by
  by_cases h : k + 1 = n
  · rw [h, Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

end Cyclic

/-! ### Local extrema and monotone chains of a polygon -/

/-- Vertex `k` of `Q` is a strict `ylexLT`-local minimum: both cyclic neighbours are strictly
greater. -/
def IsLocMin (Q : Polygon) (k : ℕ) : Prop :=
  k < Q.n ∧ ylexLT (Q.vtx k) (Q.vtx (prevIdx Q k)) ∧ ylexLT (Q.vtx k) (Q.vtx ((k + 1) % Q.n))

/-- The vertices `Q.vtx ((a+1) % n), Q.vtx ((a+2) % n), …, Q.vtx a` (all vertices, cyclically,
starting after `a`) are strictly `ylexLT`-increasing. -/
def ChainInc (Q : Polygon) (a : ℕ) : Prop :=
  ∀ p, p + 1 < Q.n → ylexLT (Q.vtx ((a + 1 + p) % Q.n)) (Q.vtx ((a + 1 + (p + 1)) % Q.n))

/-- The vertices `Q.vtx ((a+1) % n), …, Q.vtx a` are strictly `ylexLT`-decreasing. -/
def ChainDec (Q : Polygon) (a : ℕ) : Prop :=
  ∀ p, p + 1 < Q.n → ylexLT (Q.vtx ((a + 1 + (p + 1)) % Q.n)) (Q.vtx ((a + 1 + p) % Q.n))

/-- **`Q` is a monotone mountain with base edge `a`**: `Q` is simple and the chain from vertex
`(a + 1) % n` (the minimum) around to vertex `a` (the maximum) is strictly `ylexLT`-increasing,
so the base edge `a` joins the maximum to the minimum. -/
def IsMountainAt (Q : Polygon) (a : ℕ) : Prop := Q.Simple ∧ a < Q.n ∧ ChainInc Q a

/-- `Q` is a monotone mountain with base edge `a`, in one of the two orientations. -/
def IsMonoAt (Q : Polygon) (a : ℕ) : Prop :=
  Q.Simple ∧ a < Q.n ∧ (ChainInc Q a ∨ ChainDec Q a)

/-- Simplicity transfers back along a rotation. -/
theorem simple_of_simple_rotate {Q : Polygon} {s : ℕ} (h : (Q.rotate s).Simple) : Q.Simple := by
  have e : Q.rotate s = subPoly Q ((List.range Q.n).rotate s) := by
    rw [subPoly_rotate, subPoly_range]
  rw [e] at h
  have := simple_subPoly_of_rotate Q h
  rwa [subPoly_range] at this

/-- **`IsMountainAt` is the stack algorithm's `IsMountain` after rotation**: the rotation of
`Q` starting at the minimum `(a + 1) % n` is a monotone mountain in the sense of
`Chazelle.Mountain.IsMountain`. -/
theorem isMountainAt_iff {Q : Polygon} {a : ℕ} (ha : a < Q.n) :
    IsMountainAt Q a ↔ IsMountain (Q.rotate ((a + 1) % Q.n)) := by
  have key : ∀ i, i < Q.n → (Q.rotate ((a + 1) % Q.n)).vtx i = Q.vtx ((a + 1 + i) % Q.n) := by
    intro i hi
    rw [vtx_rotate Q _ hi, Nat.mod_add_mod]
  constructor
  · rintro ⟨hQ, -, hc⟩
    refine ⟨simple_rotate Q _ hQ, fun i hi => ?_⟩
    rw [n_rotate] at hi
    rw [key i (by omega), key (i + 1) hi]
    exact hc i hi
  · rintro ⟨hR, hc⟩
    refine ⟨simple_of_simple_rotate hR, ha, fun p hp => ?_⟩
    have := hc p (by rwa [n_rotate])
    rwa [key p (by omega), key (p + 1) hp] at this

/-- The global `ylexLT`-minimum of a simple polygon is a strict local minimum. -/
theorem exists_isLocMin {Q : Polygon} (hQ : Q.Simple) :
    ∃ k, IsLocMin Q k ∧ ∀ j < Q.n, j ≠ k → ylexLT (Q.vtx k) (Q.vtx j) := by
  have h3 := hQ.1
  obtain ⟨k, hk, hmin⟩ := exists_minimal_idx strictTotal_ylexLT (f := Q.vtx) (by omega)
    (fun i j hi hj h => hQ.2.1 i j hi hj h)
  exact ⟨k, ⟨hk, hmin _ (prevIdx_lt Q hk) (pred_mod_ne (by omega) hk),
    hmin _ (Nat.mod_lt _ (by omega)) (succ_mod_ne (by omega) hk)⟩, hmin⟩

/-! ### Pieces -/

/-- The cyclic edge `x → y` of an index list is an edge of `P` (in either direction) or an
inserted diagonal (in either orientation). -/
def IsPieceEdge (P : Polygon) (x y : ℕ) : Prop :=
  y = (x + 1) % P.n ∨ x = (y + 1) % P.n ∨ (x, y) ∈ allDiagonals P ∨ (y, x) ∈ allDiagonals P

/-- **A piece of the subdivision of `P` by `allDiagonals P`**: a list of at least three distinct
vertex indices whose cyclic edges are edges of `P` or inserted diagonals, spanning a simple
polygon whose interior avoids the boundary of `P` and every inserted diagonal, and whose filled
region lies in that of `P`. -/
structure IsPiece (P : Polygon) (l : List ℕ) : Prop where
  nodup : l.Nodup
  lt : ∀ x ∈ l, x < P.n
  three_le : 3 ≤ l.length
  edges : ∀ k < l.length, IsPieceEdge P (l.getD k 0) (l.getD ((k + 1) % l.length) 0)
  simple : (subPoly P l).Simple
  not_boundary : ∀ p ∈ interior (subPoly P l).filled, p ∉ P.boundary
  not_diag : ∀ d ∈ allDiagonals P, ∀ p ∈ interior (subPoly P l).filled, p ∉ diagSeg P d
  filled_subset : (subPoly P l).filled ⊆ P.filled

/-- The segment of a piece edge is contained in the boundary of `P` (edge case) or is the
segment of an inserted diagonal. -/
theorem IsPieceEdge.segment_cases {P : Polygon} {x y : ℕ} (hx : x < P.n) (hy : y < P.n)
    (h : IsPieceEdge P x y) :
    Chazelle.segment (P.vtx x) (P.vtx y) ⊆ P.boundary ∨
      ∃ d ∈ allDiagonals P, Chazelle.segment (P.vtx x) (P.vtx y) = diagSeg P d := by
  rcases h with h | h | h | h
  · left; rw [h]; exact Chazelle.Existence.edge_subset_boundary P hx
  · left; rw [h, Geometry.segment_comm]; exact Chazelle.Existence.edge_subset_boundary P hy
  · exact Or.inr ⟨_, h, rfl⟩
  · exact Or.inr ⟨_, h, by rw [diagSeg, Geometry.segment_comm]⟩

/-! ### (b) Free points are dense in the interior -/

/-- Every point of a chord is at the height of a vertex. -/
theorem chordUnion_snd {P : Polygon} {p : Point} (hp : p ∈ chordUnion P) :
    ∃ k < P.n, p.2 = (P.vtx k).2 := by
  obtain ⟨S, hS, hpS⟩ := hp
  obtain ⟨i, σ, hi, -, -, rfl⟩ := hS
  refine ⟨i, hi, ?_⟩
  obtain ⟨t, -, -, rfl⟩ := hpS
  simp [chordEnd_snd]

/-- A finite family of reals has a positive lower bound on its positive members. -/
theorem exists_pos_le_of_pos (f : ℕ → ℝ) (n : ℕ) : ∃ g > 0, ∀ j < n, 0 < f j → g ≤ f j := by
  induction n with
  | zero => exact ⟨1, one_pos, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨g, hg, hle⟩ := ih
    by_cases h : 0 < f N
    · refine ⟨min g (f N), lt_min hg h, fun j hj hfj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact (min_le_left _ _).trans (hle j hj hfj)
      · exact min_le_right _ _
    · refine ⟨g, hg, fun j hj hfj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hle j hj hfj
      · exact absurd hfj h

/-- **(b) Free points are dense in the interior.**  Every open set containing an interior point
of a simple polygon contains a free point (interior, off every chord); it can be taken directly
above the given point. -/
theorem exists_free_of_isOpen {P : Polygon} (hP : P.Simple) {U : Set Point} (hU : IsOpen U)
    {z : Point} (hz : z ∈ U) (hzi : z ∈ P.filled \ P.boundary) :
    ∃ p ∈ U, p ∈ freeRegion P ∧ p.1 = z.1 ∧ z.2 < p.2 := by
  have hV : IsOpen (U ∩ (P.filled \ P.boundary)) := hU.inter (isOpen_filled_sdiff_boundary hP)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV z ⟨hz, hzi⟩
  have hfin : (((Finset.range P.n).image (fun k => (P.vtx k).2 - z.2) : Finset ℝ) :
      Set ℝ).Finite := Finset.finite_toSet _
  obtain ⟨s, hs, hsnot⟩ := ((Set.Ioo_infinite hε).sdiff hfin).nonempty
  have hmem : ((z.1, z.2 + s) : Point) ∈ ball z ε := by
    rw [mem_ball_iff_abs]
    simp only [sub_self, abs_zero, add_sub_cancel_left]
    exact ⟨hε, by rw [abs_of_pos hs.1]; exact hs.2⟩
  refine ⟨(z.1, z.2 + s), (hball hmem).1, ⟨(hball hmem).2, ?_⟩, rfl, by
    simp only; linarith [hs.1]⟩
  intro hc
  obtain ⟨k, hk, hks⟩ := chordUnion_snd hc
  apply hsnot
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  exact ⟨k, hk, by simp only at hks; linarith⟩

/-! ### (c) The regions touching a vertex -/

/-- If the point `lerp p v t` (`t < 1`) lies on the segment `[v, c]`, then `p` lies on `[v, c]`
or is at least as far from `v` as `c`. -/
theorem mem_segment_or_far {p v c : Point} {t : ℝ} (ht1 : t < 1)
    (hx : Geometry.lerp p v t ∈ Chazelle.segment v c) :
    p ∈ Chazelle.segment v c ∨ dist c v ≤ dist p v := by
  obtain ⟨s, hs0, hs1, hxs⟩ := hx
  have h1t : 0 < 1 - t := by linarith
  have e1 : p.1 - v.1 = (s / (1 - t)) * (c.1 - v.1) := by
    have := congrArg Prod.fst hxs
    simp only [Geometry.lerp] at this
    field_simp
    linarith
  have e2 : p.2 - v.2 = (s / (1 - t)) * (c.2 - v.2) := by
    have := congrArg Prod.snd hxs
    simp only [Geometry.lerp] at this
    field_simp
    linarith
  have hμ : 0 ≤ s / (1 - t) := div_nonneg hs0 h1t.le
  rcases le_or_gt (s / (1 - t)) 1 with hle | hgt
  · left
    refine ⟨s / (1 - t), hμ, hle, ?_⟩
    rw [Geometry.point_ext_iff]
    constructor <;> simp only <;> linarith
  · right
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, e1, e2,
      abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s / (1 - t))]
    apply max_le_max <;> nlinarith [abs_nonneg (c.1 - v.1), abs_nonneg (c.2 - v.2)]

/-- **(c) Every free point near a vertex sees the vertex.**  Around a vertex `v` of a simple
polygon there is a ball such that for every free point `p` in it, `v` lies in the closure of the
region of `p`. -/
theorem exists_ball_vtx_mem_closure {P : Polygon} (hP : P.Simple) {k : ℕ} (hk : k < P.n) :
    ∃ r > 0, ∀ p ∈ ball (P.vtx k) r, p ∈ freeRegion P →
      P.vtx k ∈ closure (connectedComponentIn (freeRegion P) p) := by
  have hn := simple_three_le hP
  set v := P.vtx k
  set a := P.vtx (prevIdx P k)
  set b := P.vtx ((k + 1) % P.n)
  obtain ⟨r₁, hr₁, hball⟩ := Chazelle.Existence.boundary_near_vtx hP hk
  have hav : 0 < dist a v :=
    dist_pos.2 (simple_vtx_ne hP (prevIdx_lt P hk) hk (prevIdx_ne P hn hk))
  have hbv : 0 < dist b v := dist_pos.2 (simple_vtx_succ_ne hP hk).symm
  obtain ⟨g, hg, hgle⟩ := exists_pos_le_of_pos (fun j => |(P.vtx j).2 - v.2|) P.n
  set r := min (min r₁ (dist a v)) (min (dist b v) g)
  have hr0 : 0 < r := lt_min (lt_min hr₁ hav) (lt_min hbv hg)
  have hrr₁ : r ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hra : r ≤ dist a v := (min_le_left _ _).trans (min_le_right _ _)
  have hrb : r ≤ dist b v := (min_le_right _ _).trans (min_le_left _ _)
  have hrg : r ≤ g := (min_le_right _ _).trans (min_le_right _ _)
  -- the case of a point at a different height
  have key : ∀ p ∈ ball v r, p ∈ freeRegion P → p.2 ≠ v.2 →
      v ∈ closure (connectedComponentIn (freeRegion P) p) := by
    intro p hp hpf hpy
    have hpv : dist p v < r := hp
    set S := Geometry.lerp p v '' Ico (0 : ℝ) 1
    have hSball : S ⊆ ball v r := by
      rintro _ ⟨t, ht, rfl⟩
      rw [Geometry.lerp_eq_smul_add_smul]
      exact (convex_ball v r) hp (mem_ball_self hr0) (by linarith [ht.2]) ht.1 (by ring)
    have hSb : ∀ x ∈ S, x ∉ P.boundary := by
      rintro _ ⟨t, ht, rfl⟩ hxb
      rcases hball _ (ball_subset_ball hrr₁ (hSball ⟨t, ht, rfl⟩)) hxb with hx | hx
      · rw [Geometry.segment_comm] at hx
        rcases mem_segment_or_far ht.2 hx with h | h
        · apply hpf.1.2
          refine ⟨prevIdx P k, prevIdx_lt P hk, ?_⟩
          rwa [edge_prevIdx P hk, Geometry.segment_comm]
        · linarith
      · rcases mem_segment_or_far ht.2 hx with h | h
        · exact hpf.1.2 ⟨k, hk, h⟩
        · linarith
    have hSc : IsPreconnected S :=
      isPreconnected_Ico.image _ (Geometry.continuous_lerp p v).continuousOn
    have hpS : p ∈ S := ⟨0, ⟨le_rfl, one_pos⟩, Geometry.lerp_zero p v⟩
    have hSi : S ⊆ P.filled \ P.boundary :=
      subset_interior_of_isPreconnected hP hSc hSb hpS hpf.1
    have hSf : S ⊆ freeRegion P := by
      intro x hx
      refine ⟨hSi hx, fun hxc => ?_⟩
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨j, hj, hjy⟩ := chordUnion_snd hxc
      have hxv := hSball ⟨t, ht, rfl⟩
      rw [mem_ball_iff_abs] at hxv
      have hne : (Geometry.lerp p v t).2 - v.2 ≠ 0 := by
        rw [Geometry.lerp_snd]
        have : p.2 + t * (v.2 - p.2) - v.2 = (1 - t) * (p.2 - v.2) := by ring
        rw [this]
        exact mul_ne_zero (by linarith [ht.2]) (sub_ne_zero.2 hpy)
      have h1 := hgle j hj (by
        show 0 < |(P.vtx j).2 - v.2|
        rw [← hjy]; exact abs_pos.2 hne)
      have h1' : g ≤ |(Geometry.lerp p v t).2 - v.2| := by rwa [hjy]
      linarith [hxv.2]
    have hsub : S ⊆ connectedComponentIn (freeRegion P) p :=
      hSc.subset_connectedComponentIn hpS hSf
    have htend : Tendsto (Geometry.lerp p v) (𝓝[<] 1) (𝓝 v) := by
      have := ((Geometry.continuous_lerp p v).tendsto 1)
      rw [Geometry.lerp_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hsub ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
  refine ⟨r, hr0, fun p hp hpf => ?_⟩
  by_cases hpy : p.2 = v.2
  · -- move up inside the region of `p`
    have hCo : IsOpen (connectedComponentIn (freeRegion P) p) :=
      (isOpen_freeRegion hP).connectedComponentIn
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 (hCo.inter isOpen_ball) p
      ⟨mem_connectedComponentIn hpf, hp⟩
    have hp' : ((p.1, p.2 + δ / 2) : Point) ∈ ball p δ := by
      rw [mem_ball_iff_abs]
      simp only [sub_self, abs_zero, add_sub_cancel_left]
      exact ⟨hδ, by rw [abs_of_pos (by linarith)]; linarith⟩
    obtain ⟨hp'C, hp'b⟩ := hδsub hp'
    have hp'f : ((p.1, p.2 + δ / 2) : Point) ∈ freeRegion P := connectedComponentIn_subset _ _ hp'C
    have := key _ hp'b hp'f (by simp only; rw [hpy]; linarith)
    rwa [← connectedComponentIn_eq hp'C] at this
  · exact key p hp hpf hpy

/-- **(c) The trapezoid of a free point near a vertex.**  Around a vertex `v = P.vtx k` there is a
ball such that every free point `p` in it has trapezoid data `D` (with `D.q = p`) whose region
contains `p` and has `v` in its closure, and then `k` is a vertex of the closed bottom side or
of the closed top side of the trapezoid. -/
theorem exists_ball_vtx_trapData {P : Polygon} (hP : P.Simple) {k : ℕ} (hk : k < P.n) :
    ∃ r > 0, ∀ p ∈ ball (P.vtx k) r, p ∈ freeRegion P →
      ∃ D : TrapData P, D.q = p ∧ p ∈ D.region ∧ P.vtx k ∈ closure D.region ∧
        (k ∈ sideVtxSet P D.i D.j D.y₁ ∨ k ∈ sideVtxSet P D.i D.j D.y₂) := by
  obtain ⟨r, hr, h⟩ := exists_ball_vtx_mem_closure hP hk
  refine ⟨r, hr, fun p hp hpf => ?_⟩
  obtain ⟨i, j, y₁, y₂, hT, hreg⟩ := exists_isTrap_region_eq hP hpf
  let D : TrapData P := ⟨p, i, j, y₁, y₂, hpf, hT⟩
  have hDreg : D.region = connectedComponentIn (freeRegion P) p := hreg.symm
  have hvc : P.vtx k ∈ closure D.region := by rw [hDreg]; exact h p hp hpf
  exact ⟨D, rfl, hT.q_mem hP hpf.1, hvc, D.vtx_mem_closure_region hk hvc⟩

/-- A vertex in the closure of a region, strictly below one of its points, is on the closed
bottom side. -/
theorem TrapData.mem_bot_of_lt {P : Polygon} (D : TrapData P) {k : ℕ}
    (hk : k < P.n) (hv : P.vtx k ∈ closure D.region) {p : Point} (hp : p ∈ D.region)
    (hlt : (P.vtx k).2 < p.2) : k ∈ sideVtxSet P D.i D.j D.y₁ := by
  rcases D.vtx_mem_closure_region hk hv with h | h
  · exact h
  · exfalso
    have := hp.2.1
    rw [← h.2.1] at this
    linarith

/-- A vertex in the closure of a region, strictly above one of its points, is on the closed top
side. -/
theorem TrapData.mem_top_of_lt {P : Polygon} (D : TrapData P) {k : ℕ}
    (hk : k < P.n) (hv : P.vtx k ∈ closure D.region) {p : Point} (hp : p ∈ D.region)
    (hlt : p.2 < (P.vtx k).2) : k ∈ sideVtxSet P D.i D.j D.y₂ := by
  rcases D.vtx_mem_closure_region hk hv with h | h
  · exfalso
    have := hp.1
    rw [← h.2.1] at this
    linarith
  · exact h

/-! ### (d) The segment attached at a vertex of a side -/

/-- A point of the plane at the height of a vertex set strictly between two abscissae. -/
theorem horiz_mem_segment {a b p : Point} (ha : a.2 = p.2) (hb : b.2 = p.2)
    (h1 : min a.1 b.1 ≤ p.1) (h2 : p.1 ≤ max a.1 b.1) : p ∈ Chazelle.segment a b := by
  rw [segment_horizontal_eq_hseg (ha.trans hb.symm)]
  exact ⟨ha.symm, h1, h2⟩

/-- **The gap lemma.**  Let `m`, `k` be vertices at the same height `y₀`, `m` to the left of `k`,
with no vertex strictly between them at that height, and suppose that just above (`ε = 1`) or
just below (`ε = -1`) every point strictly between them there are only points of a set `U` of
interior points.  Then `m` and `k` are adjacent (the segment is a horizontal edge), or the segment
is a vertex-to-vertex chord in both directions. -/
theorem gap_adjacent_or_chord {P : Polygon} (hP : P.Simple) {y₀ ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {U : Set Point} (hU : U ⊆ P.filled \ P.boundary) {m k : ℕ} (hm : m < P.n) (hk : k < P.n)
    (hmy : (P.vtx m).2 = y₀) (hky : (P.vtx k).2 = y₀) (hlt : (P.vtx m).1 < (P.vtx k).1)
    (hnear : ∀ x, (P.vtx m).1 < x → x < (P.vtx k).1 →
      ∀ᶠ p' in 𝓝 ((x, y₀) : Point), 0 < ε * (p'.2 - y₀) → p' ∈ U)
    (hgap : ∀ j < P.n, (P.vtx j).2 = y₀ → (P.vtx m).1 < (P.vtx j).1 →
      (P.vtx j).1 < (P.vtx k).1 → False) :
    (k = (m + 1) % P.n ∨ m = (k + 1) % P.n) ∨ ((k, m) ∈ vtxChords P ∧ (m, k) ∈ vtxChords P) := by
  have hmk : m ≠ k := by rintro rfl; exact lt_irrefl _ hlt
  by_cases hB : ∃ x, (P.vtx m).1 < x ∧ x < (P.vtx k).1 ∧ ((x, y₀) : Point) ∈ P.boundary
  · -- a boundary point in the gap: the segment is a horizontal edge
    left
    obtain ⟨x, hx1, hx2, hxb⟩ := hB
    have hnv : ∀ j, j < P.n → ((x, y₀) : Point) ≠ P.vtx j := by
      intro j hj h
      have h1 : (P.vtx j).1 = x := (congrArg Prod.fst h).symm
      have h2 : (P.vtx j).2 = y₀ := (congrArg Prod.snd h).symm
      exact hgap j hj h2 (by rwa [h1]) (by rwa [h1])
    obtain ⟨g, hg, t, ht, hxe⟩ := exists_openEdge_of_mem_boundary P hxb hnv
    by_cases hh : NonHoriz P g
    · exact absurd (side_edge_false hε hU (e := (x, y₀)) rfl (hnear x hx1 hx2) hg hh
        ⟨t, ht, hxe⟩) not_false
    · unfold NonHoriz at hh
      push Not at hh
      set e1 := P.vtx g
      set e2 := P.vtx ((g + 1) % P.n)
      have hx1e : x = e1.1 + t * (e2.1 - e1.1) := congrArg Prod.fst hxe
      have hy1e : y₀ = e1.2 + t * (e2.2 - e1.2) := congrArg Prod.snd hxe
      have he1y : e1.2 = y₀ := by rw [hy1e, ← hh]; ring
      have he2y : e2.2 = y₀ := by rw [← hh, he1y]
      have hne12 : e1.1 ≠ e2.1 := by
        intro h
        exact simple_vtx_succ_ne hP hg (Geometry.point_ext h (he1y.trans he2y.symm))
      have hg1 := succIdx_lt P hg
      -- the endpoints of the edge are not in the gap
      have hout1 : ¬ ((P.vtx m).1 < e1.1 ∧ e1.1 < (P.vtx k).1) :=
        fun h => hgap g hg he1y h.1 h.2
      have hout2 : ¬ ((P.vtx m).1 < e2.1 ∧ e2.1 < (P.vtx k).1) :=
        fun h => hgap _ hg1 he2y h.1 h.2
      have hmem : ∀ c : ℕ, c < P.n → (P.vtx c).2 = y₀ →
          (P.vtx m).1 ≤ (P.vtx c).1 → (P.vtx c).1 ≤ (P.vtx k).1 → P.vtx c ∈ P.edge g := by
        intro c hc hcy hc1 hc2
        apply horiz_mem_segment (he1y.trans hcy.symm) (he2y.trans hcy.symm)
        · rcases lt_or_gt_of_ne hne12 with h12 | h12
          · rw [min_eq_left h12.le]
            by_contra hcon
            push Not at hcon
            have : e1.1 < x := by rw [hx1e]; nlinarith [ht.1]
            exact hout1 ⟨by linarith, by linarith⟩
          · rw [min_eq_right h12.le]
            by_contra hcon
            push Not at hcon
            have : e2.1 < x := by rw [hx1e]; nlinarith [ht.2]
            exact hout2 ⟨by linarith, by linarith⟩
        · rcases lt_or_gt_of_ne hne12 with h12 | h12
          · rw [max_eq_right h12.le]
            by_contra hcon
            push Not at hcon
            have : x < e2.1 := by rw [hx1e]; nlinarith [ht.2]
            exact hout2 ⟨by linarith, by linarith⟩
          · rw [max_eq_left h12.le]
            by_contra hcon
            push Not at hcon
            have : x < e1.1 := by rw [hx1e]; nlinarith [ht.1]
            exact hout1 ⟨by linarith, by linarith⟩
      have hkg := (simple_vtx_mem_edge_iff hP hk hg).1 (hmem k hk hky hlt.le le_rfl)
      have hmg := (simple_vtx_mem_edge_iff hP hm hg).1 (hmem m hm hmy le_rfl hlt.le)
      rcases hkg with hkg | hkg <;> rcases hmg with hmg | hmg
      · exact absurd (hmg.symm.trans hkg) hmk
      · right
        rw [← hkg, hmg, prevIdx_succ P hm]
      · left
        rw [← prevIdx_succ P hk, ← hkg, hmg]
      · exfalso
        apply hmk
        rw [← prevIdx_succ P hm, ← prevIdx_succ P hk, ← hmg, ← hkg]
  · -- no boundary point in the gap: a vertex-to-vertex chord
    right
    push Not at hB
    have hint : ∀ x, (P.vtx m).1 < x → x < (P.vtx k).1 →
        ((x, y₀) : Point) ∈ P.filled \ P.boundary := by
      intro x hx1 hx2
      refine ⟨?_, hB x hx1 hx2⟩
      have htend : Tendsto (fun s : ℝ => ((x, y₀ + ε * s) : Point)) (𝓝[>] 0) (𝓝 (x, y₀)) := by
        have hc : Continuous fun s : ℝ => ((x, y₀ + ε * s) : Point) := by fun_prop
        have := hc.tendsto 0
        simp only [mul_zero, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have hcl : ((x, y₀) : Point) ∈ closure U := by
        refine mem_closure_of_tendsto htend ?_
        filter_upwards [htend.eventually (hnear x hx1 hx2), self_mem_nhdsWithin] with s hs hs0
        apply hs
        have hs0' : (0 : ℝ) < s := hs0
        simp only [add_sub_cancel_left]
        rcases hε with rfl | rfl <;> nlinarith
      exact (isClosed_filled P).closure_subset (closure_mono (fun _ h => (hU h).1) hcl)
    have hd : 0 < (P.vtx k).1 - (P.vtx m).1 := by linarith
    constructor
    · -- the chord of `k` to the left ends at `m`
      have hdir : DirInterior P k (-1) := by
        unfold DirInterior
        filter_upwards [Ioo_mem_nhdsGT hd] with t ht
        have : rayPt (P.vtx k) (-1) t = (((P.vtx k).1 - t, y₀) : Point) := by
          rw [Geometry.point_ext_iff]; simp [hky]; ring
        rw [this]
        exact hint _ (by linarith [ht.2]) (by linarith [ht.1])
      have hpar : chordParam P k (-1) = (P.vtx k).1 - (P.vtx m).1 := by
        apply chordParam_eq_of_first P k (-1) hd
        · have : rayPt (P.vtx k) (-1) ((P.vtx k).1 - (P.vtx m).1) = P.vtx m := by
            rw [Geometry.point_ext_iff]; simp [hky, hmy]
          rw [this]; exact vtx_mem_boundary P hm
        · intro s hs0 hs1
          have : rayPt (P.vtx k) (-1) s = (((P.vtx k).1 - s, y₀) : Point) := by
            rw [Geometry.point_ext_iff]; simp [hky]; ring
          rw [this]
          exact hB _ (by linarith) (by linarith)
      refine ⟨hk, hm, -1, Or.inr rfl, hdir, ?_⟩
      rw [Geometry.point_ext_iff]
      simp [chordEnd, hpar, hky, hmy]
    · -- the chord of `m` to the right ends at `k`
      have hdir : DirInterior P m 1 := by
        unfold DirInterior
        filter_upwards [Ioo_mem_nhdsGT hd] with t ht
        have : rayPt (P.vtx m) 1 t = (((P.vtx m).1 + t, y₀) : Point) := by
          rw [Geometry.point_ext_iff]; simp [hmy]
        rw [this]
        exact hint _ (by linarith [ht.1]) (by linarith [ht.2])
      have hpar : chordParam P m 1 = (P.vtx k).1 - (P.vtx m).1 := by
        apply chordParam_eq_of_first P m 1 hd
        · have : rayPt (P.vtx m) 1 ((P.vtx k).1 - (P.vtx m).1) = P.vtx k := by
            rw [Geometry.point_ext_iff]; simp [hky, hmy]
          rw [this]; exact vtx_mem_boundary P hk
        · intro s hs0 hs1
          have : rayPt (P.vtx m) 1 s = (((P.vtx m).1 + s, y₀) : Point) := by
            rw [Geometry.point_ext_iff]; simp [hmy]
          rw [this]
          exact hB _ (by linarith) (by linarith)
      refine ⟨hm, hk, 1, Or.inl rfl, hdir, ?_⟩
      rw [Geometry.point_ext_iff]
      simp [chordEnd, hpar, hky, hmy]

/-- **(d) The attached segment at a vertex of the closed top side.**  If vertex `k` lies on the
closed top side of the trapezoid `D`, some vertex `m` strictly `ylexLT`-below `k` is joined to
`k` by an edge of `P` or an inserted diagonal: when `k` is the top vertex, the bottom vertex
(through the trapezoid diagonal, or the side edge when they are adjacent); otherwise the next
vertex to the left on the top side (through a horizontal edge or a vertex-to-vertex chord). -/
theorem TrapData.attached_top {P : Polygon} (hP : P.Simple) (D : TrapData P) {k : ℕ}
    (hk : k ∈ sideVtxSet P D.i D.j D.y₂) :
    ∃ m < P.n, ylexLT (P.vtx m) (P.vtx k) ∧ IsPieceEdge P k m := by
  by_cases htop : k = D.top
  · subst htop
    refine ⟨D.bot, D.bot_lt hP, ylexLT_of_snd_lt (D.bot_snd_lt_top_snd hP), ?_⟩
    by_cases hna : D.NonAdj
    · exact Or.inr (Or.inr (Or.inl (Or.inl (D.diag_mem_trapDiagonals hna))))
    · unfold TrapData.NonAdj at hna
      rw [not_and_or, not_not, not_not] at hna
      rcases hna with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · obtain ⟨htmem, htmin⟩ := D.isTrap.topVtx_spec hP D.free
    have hkt : (P.vtx D.top).1 < (P.vtx k).1 := by
      refine lt_of_le_of_ne (htmin k hk) (fun h => htop ?_)
      exact simple_vtx_inj hP hk.1 htmem.1
        (Geometry.point_ext h.symm (hk.2.1.trans htmem.2.1.symm))
    set S : Set ℕ := {j | j ∈ sideVtxSet P D.i D.j D.y₂ ∧ (P.vtx j).1 < (P.vtx k).1}
    have hSfin : S.Finite := (sideVtxSet_finite P D.i D.j D.y₂).subset fun _ h => h.1
    have hSne : S.Nonempty := ⟨D.top, htmem, hkt⟩
    obtain ⟨hmS, hmmax⟩ := rightmostVtx_spec P hSfin hSne
    set m := rightmostVtx P S
    refine ⟨m, hmS.1.1, Or.inr ⟨hmS.1.2.1.trans hk.2.1.symm, hmS.2⟩, ?_⟩
    have hres := gap_adjacent_or_chord hP (Or.inr rfl) (D.region_subset_interior hP)
      hmS.1.1 hk.1 hmS.1.2.1 hk.2.1 hmS.2
      (fun x hx1 hx2 => D.isTrap.near_top (by linarith [hmS.1.2.2.1]) (by linarith [hk.2.2.2]))
      (fun j hj hjy hj1 hj2 => by
        have hjS : j ∈ S := ⟨⟨hj, hjy, by linarith [hmS.1.2.2.1], by linarith [hk.2.2.2]⟩, hj2⟩
        linarith [hmmax j hjS])
    rcases hres with (h | h) | ⟨h, -⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-! ### The `ylexLT` half-planes -/

/-- Points of a segment from `a` towards a `ylexLE`-larger point are `ylexLE`-above `a`. -/
theorem ylexLE_of_mem_segment {a b p : Point} (hab : ylexLE a b)
    (hp : p ∈ Chazelle.segment a b) : ylexLE a p := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  rcases hab with h | ⟨h1, h2⟩
  · rcases ht0.lt_or_eq with ht | ht
    · left; simp only; nlinarith
    · right; subst ht; simp
  · right; simp only; constructor
    · rw [h1]; ring
    · nlinarith

/-- Moving from `x` towards a strictly `ylexLT`-smaller point decreases strictly. -/
theorem ylexLT_lerp_lower {x c : Point} (hc : ylexLT c x) {s : ℝ} (hs : 0 < s) :
    ylexLT (Geometry.lerp x c s) x := by
  rcases hc with h | ⟨h1, h2⟩
  · left; simp only [Geometry.lerp_snd]; nlinarith
  · right; simp only [Geometry.lerp_snd, Geometry.lerp_fst]
    exact ⟨by rw [h1]; ring, by nlinarith⟩

/-- The strict `ylexLT`-lower set of a point is convex. -/
theorem convex_ylexLT_lower (x : Point) : Convex ℝ {y : Point | ylexLT y x} := by
  intro y hy z hz a b ha hb hab
  change ylexLT _ _ at hy
  change ylexLT _ _ at hz
  show (a • y + b • z).2 < x.2 ∨ ((a • y + b • z).2 = x.2 ∧ (a • y + b • z).1 < x.1)
  have e2 : a * x.2 + b * x.2 = x.2 := by rw [← add_mul, hab, one_mul]
  have e1 : a * x.1 + b * x.1 = x.1 := by rw [← add_mul, hab, one_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rcases hy with hy | ⟨hy1, hy2⟩ <;> rcases hz with hz | ⟨hz1, hz2⟩
      · left
        linarith [mul_lt_mul_of_pos_left hy ha', mul_lt_mul_of_pos_left hz hb']
      · left
        rw [hz1]; linarith [mul_lt_mul_of_pos_left hy ha']
      · left
        rw [hy1]; linarith [mul_lt_mul_of_pos_left hz hb']
      · right
        rw [hy1, hz1]
        exact ⟨e2, by linarith [mul_lt_mul_of_pos_left hy2 ha', mul_lt_mul_of_pos_left hz2 hb']⟩
    · subst hb'
      have : a = 1 := by linarith
      subst this; simpa [ylexLT] using hy
  · subst ha'
    have : b = 1 := by linarith
    subst this; simpa [ylexLT] using hz

/-- Near a vertex of a simple polygon both of whose neighbours are `ylexLT`-greater, the
`ylexLT`-lower half-ball avoids the boundary. -/
theorem lower_halfBall_not_boundary {Q : Polygon} (hQ : Q.Simple) {k : ℕ} (hk : IsLocMin Q k) :
    ∃ r > 0, ∀ y ∈ ball (Q.vtx k) r, ylexLT y (Q.vtx k) → y ∉ Q.boundary := by
  obtain ⟨r, hr, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hk.1
  refine ⟨r, hr, fun y hy hlt hyb => ?_⟩
  rcases hball y hy hyb with h | h
  · rw [Geometry.segment_comm] at h
    exact not_ylexLE_of_ylexLT hlt (ylexLE_of_mem_segment (ylexLE_of_ylexLT hk.2.1) h)
  · exact not_ylexLE_of_ylexLT hlt (ylexLE_of_mem_segment (ylexLE_of_ylexLT hk.2.2) h)

/-! ### Pieces have no reflex local extrema -/

/-- The interior region of a piece lies in the interior region of `P`. -/
theorem IsPiece.interior_subset {P : Polygon} {l : List ℕ} (hl : IsPiece P l) :
    (subPoly P l).filled \ (subPoly P l).boundary ⊆ P.filled \ P.boundary := by
  intro y hy
  refine ⟨hl.filled_subset hy.1, hl.not_boundary y ?_⟩
  rwa [interior_filled hl.simple]

/-- A point of the segment attached at a vertex of a piece that is interior to the piece yields
a contradiction. -/
theorem IsPiece.not_mem_attached {P : Polygon} {l : List ℕ} (hl : IsPiece P l) {K m : ℕ}
    (hK : K < P.n) (hm : m < P.n) (he : IsPieceEdge P K m) {y : Point}
    (hy : y ∈ Chazelle.segment (P.vtx K) (P.vtx m))
    (hyi : y ∈ (subPoly P l).filled \ (subPoly P l).boundary) : False := by
  have hyi' : y ∈ interior (subPoly P l).filled := by rwa [interior_filled hl.simple]
  rcases he.segment_cases hK hm with h | ⟨d, hd, h⟩
  · exact hl.not_boundary y hyi' (h hy)
  · exact hl.not_diag d hd y hyi' (by rwa [← h])

/-- **A piece has no reflex local minimum.**  If vertex `k` of a piece `Q = subPoly P l` is a
strict `ylexLT`-local minimum, then near `Q.vtx k` no point strictly `ylexLT`-below it is
interior to `Q` (the interior of `Q` near a local minimum lies above it).  Otherwise a free point
of `P` just below the vertex lies in a trapezoid having the vertex on its closed top side, and the
attached edge or inserted diagonal (`TrapData.attached_top`) enters the interior of `Q`. -/
theorem IsPiece.locMin_lower_exterior {P : Polygon} (hP : P.Simple) {l : List ℕ}
    (hl : IsPiece P l) {k : ℕ} (hk : IsLocMin (subPoly P l) k) :
    ∃ r > 0, ∀ y ∈ ball ((subPoly P l).vtx k) r, ylexLT y ((subPoly P l).vtx k) →
      y ∉ (subPoly P l).filled \ (subPoly P l).boundary := by
  set Q := subPoly P l with hQdef
  have hQ : Q.Simple := hl.simple
  have hkQ : k < l.length := by have := hk.1; rwa [hQdef, n_subPoly] at this
  set K := l.getD k 0 with hKdef
  have hK : K < P.n := by
    apply hl.lt
    rw [hKdef, EarClip.getD_eq_getElem_of_lt _ _ hkQ]
    exact List.getElem_mem hkQ
  have hxK : Q.vtx k = P.vtx K := vtx_subPoly_getD P l hkQ
  obtain ⟨r₁, hr₁, hr₁b⟩ := lower_halfBall_not_boundary hQ hk
  obtain ⟨r₂, hr₂, hr₂D⟩ := exists_ball_vtx_trapData hP hK
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun y₀ hy₀ hy₀lt hy₀i => ?_⟩
  set x := Q.vtx k
  set r := min r₁ r₂
  -- the lower half-ball is interior to `Q`
  have hB : ∀ y ∈ ball x r, ylexLT y x → y ∈ Q.filled \ Q.boundary := by
    have hconv : Convex ℝ (ball x r ∩ {y | ylexLT y x}) := (convex_ball x r).inter (convex_ylexLT_lower x)
    intro y hy hylt
    exact subset_interior_of_isPreconnected hQ hconv.isPreconnected
      (fun z hz => hr₁b z (ball_subset_ball (min_le_left _ _) hz.1) hz.2) ⟨hy₀, hy₀lt⟩ hy₀i
      ⟨hy, hylt⟩
  -- a free point of `P` just below `x`
  have hWo : IsOpen (ball x r ∩ {y : Point | y.2 < x.2}) :=
    isOpen_ball.inter (isOpen_lt continuous_snd continuous_const)
  have hr0 : 0 < r := lt_min hr₁ hr₂
  have hz : ((x.1, x.2 - r / 2) : Point) ∈ ball x r ∩ {y : Point | y.2 < x.2} := by
    refine ⟨?_, by simp only [Set.mem_ofPred_eq]; linarith⟩
    rw [mem_ball_iff_abs]
    simp only [sub_self, abs_zero]
    refine ⟨hr0, ?_⟩
    rw [show x.2 - r / 2 - x.2 = -(r / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hzi : ((x.1, x.2 - r / 2) : Point) ∈ P.filled \ P.boundary :=
    hl.interior_subset (hB _ hz.1 (Or.inl hz.2))
  obtain ⟨p, ⟨hpb, hpy⟩, hpf, -, -⟩ := exists_free_of_isOpen hP hWo hz hzi
  obtain ⟨D, -, hpD, hvD, -⟩ := hr₂D p (by rw [← hxK]; exact ball_subset_ball (min_le_right _ _) hpb) hpf
  have hKtop : K ∈ sideVtxSet P D.i D.j D.y₂ :=
    D.mem_top_of_lt hK hvD hpD (by rwa [← hxK])
  obtain ⟨m, hm, hmlt, hme⟩ := D.attached_top hP hKtop
  rw [← hxK] at hmlt
  -- a point of the attached segment close to `x`
  have htend : Tendsto (Geometry.lerp x (P.vtx m)) (𝓝[>] 0) (𝓝 x) := by
    have := (Geometry.continuous_lerp x (P.vtx m)).tendsto 0
    rw [Geometry.lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨s, hsb, hs⟩ := ((htend.eventually (isOpen_ball.mem_nhds (mem_ball_self hr0))).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  apply hl.not_mem_attached hK hm hme (y := Geometry.lerp x (P.vtx m) s)
  · rw [← hxK]; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le
  · exact hB _ hsb (ylexLT_lerp_lower hmlt hs.1)

end

end Chazelle.Mountain
