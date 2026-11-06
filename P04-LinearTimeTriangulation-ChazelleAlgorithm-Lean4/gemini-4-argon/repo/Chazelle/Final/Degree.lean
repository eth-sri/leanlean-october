module

public import Chazelle.Final.Interface
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Bounded degree of the inserted diagonals

For a simple polygon `P` and a vertex `v`, at most `10` inserted diagonals (`allDiagonals P`,
see `Chazelle.Mountain.Decompose`) are incident to `v`:

* at most `3` trapezoid diagonals `(top, bot)` with `top = v`: such a trapezoid has `v` on its
  closed top side (`topRegions`), and at most three regions do (`topRegions_ncard_le`);
* at most `3` with `bot = v` (`botRegions_ncard_le`);
* at most `2` vertex-to-vertex chords starting at `v` (one per direction) and at most `2` ending
  at `v` (one per direction: a second chord in the same direction would pass through the first
  vertex, `chord_src_unique`).

**Why at most three regions.**  Near `v` the boundary consists of the two edges at `v`
(`Chazelle.Existence.boundary_near_vtx`), and no chord meets the lines at heights close to but
different from `v.2`.  Fix such a height `h` just below `v`; on the horizontal segment at height
`h` inside a small ball around `v`, the boundary is at most the two points where the edges at `v`
cross height `h` (`fst_eq_crossX`).  Every region having `v` on its closed top side meets this
segment away from these two points (`trapData_eventually_below`), and two such points in the same
one of the three complementary intervals are joined by a free horizontal segment, hence lie in
the same region (`ncard_le_three_of_near`).

## Main results

* `card_incident_le`: `(incident P v).ncard ≤ 10` (ordered pairs), and
  `ncard_sortPair_incident_le` (unordered pairs);
* `sum_ncard_incident`, `sum_ncard_incident_le`: `Σ_{v < n} deg v = 2 · #allDiagonals P ≤
  2 (4 n + 1)`;
* `countP_diagList_le`, `sum_countP_diagList_le`: the same bounds for the final-stage input
  `diagList P T C` (`Chazelle.Final.Interface`).
-/

namespace Chazelle.Final

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan (mem_ball_iff_abs prevIdx simple_vtx_inj)
open Chazelle.Existence (vtx_mem_boundary boundary_near_vtx)
open Chazelle.Visibility
open Chazelle.Mountain

/-! ### Elementary facts -/

/-- Every point of a chord is at the height of a vertex. -/
theorem height_of_mem_chordUnion {P : Polygon} {p : Point} (hp : p ∈ chordUnion P) :
    ∃ k < P.n, p.2 = (P.vtx k).2 := by
  obtain ⟨S, hS, hpS⟩ := hp
  obtain ⟨i, σ, hi, -, -, rfl⟩ := hS
  refine ⟨i, hi, ?_⟩
  obtain ⟨t, -, -, rfl⟩ := hpS
  simp [chordEnd_snd]

/-- The abscissa at height `h` of the line through `v` and `a` (meaningful when
`a.2 ≠ v.2`). -/
noncomputable def crossX (v a : Point) (h : ℝ) : ℝ := v.1 + (h - v.2) / (a.2 - v.2) * (a.1 - v.1)

/-- A point of the segment `[v, a]` at a height different from `v.2` has abscissa
`crossX v a h`. -/
theorem fst_eq_crossX {v a p : Point} (hp : p ∈ Chazelle.segment v a) (hh : p.2 ≠ v.2) :
    p.1 = crossX v a p.2 := by
  obtain ⟨t, -, -, rfl⟩ := hp
  simp only at hh ⊢
  have hne : a.2 - v.2 ≠ 0 := by
    intro h0
    apply hh
    rw [h0, mul_zero, add_zero]
  unfold crossX
  rw [show v.2 + t * (a.2 - v.2) - v.2 = t * (a.2 - v.2) by ring, mul_div_assoc, div_self hne,
    mul_one]

/-- An open interval contains a point different from two given reals. -/
theorem exists_Ioo_avoid {lo hi : ℝ} (h : lo < hi) (c₁ c₂ : ℝ) :
    ∃ x, lo < x ∧ x < hi ∧ x ≠ c₁ ∧ x ≠ c₂ := by
  by_cases hA : lo + (hi - lo) / 4 ≠ c₁ ∧ lo + (hi - lo) / 4 ≠ c₂
  · exact ⟨_, by linarith, by linarith, hA.1, hA.2⟩
  by_cases hB : lo + (hi - lo) / 2 ≠ c₁ ∧ lo + (hi - lo) / 2 ≠ c₂
  · exact ⟨_, by linarith, by linarith, hB.1, hB.2⟩
  by_cases hC : lo + 3 * (hi - lo) / 4 ≠ c₁ ∧ lo + 3 * (hi - lo) / 4 ≠ c₂
  · exact ⟨_, by linarith, by linarith, hC.1, hC.2⟩
  exfalso
  rw [not_and_or, not_not, not_not] at hA hB hC
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rcases hC with hC | hC <;> linarith

/-- The position of `x` relative to two cut points `m ≤ M`: `0` left of `m`, `1` between them,
`2` right of `M`. -/
noncomputable def piece3 (m M x : ℝ) : Fin 3 := if x < m then 0 else if x < M then 1 else 2

/-- Two points off the cut points, in the same piece: everything between them avoids the cut
points. -/
theorem piece3_between_aux {m M x x' z : ℝ} (hmM : m ≤ M) (hxm : x ≠ m) (hxM : x ≠ M)
    (hxm' : x' ≠ m) (hxM' : x' ≠ M) (h : piece3 m M x = piece3 m M x')
    (hz1 : min x x' ≤ z) (hz2 : z ≤ max x x') : z ≠ m ∧ z ≠ M := by
  unfold piece3 at h
  by_cases ha : x < m
  · by_cases hb : x' < m
    · have := max_lt ha hb
      constructor <;> intro hz <;> linarith
    · rw [ite_eq_left ha, ite_eq_right hb] at h
      split_ifs at h <;> exact absurd h (by decide)
  · by_cases hb : x' < m
    · rw [ite_eq_right ha, ite_eq_left hb] at h
      split_ifs at h <;> exact absurd h (by decide)
    · rw [ite_eq_right ha, ite_eq_right hb] at h
      have h1 : m < x := lt_of_le_of_ne (not_lt.1 ha) (Ne.symm hxm)
      have h2 : m < x' := lt_of_le_of_ne (not_lt.1 hb) (Ne.symm hxm')
      by_cases hc : x < M
      · by_cases hd : x' < M
        · have h3 := lt_min h1 h2
          have h4 := max_lt hc hd
          constructor <;> intro hz <;> linarith
        · rw [ite_eq_left hc, ite_eq_right hd] at h
          exact absurd h (by decide)
      · by_cases hd : x' < M
        · rw [ite_eq_right hc, ite_eq_left hd] at h
          exact absurd h (by decide)
        · have h5 : M < x := lt_of_le_of_ne (not_lt.1 hc) (Ne.symm hxM)
          have h6 : M < x' := lt_of_le_of_ne (not_lt.1 hd) (Ne.symm hxM')
          have h3 := lt_min h5 h6
          constructor <;> intro hz <;> linarith

/-- Two points off two cut points `c₁`, `c₂`, in the same piece: everything between them avoids
the cut points. -/
theorem piece3_between {c₁ c₂ x x' z : ℝ} (hx1 : x ≠ c₁) (hx2 : x ≠ c₂) (hx1' : x' ≠ c₁)
    (hx2' : x' ≠ c₂) (h : piece3 (min c₁ c₂) (max c₁ c₂) x = piece3 (min c₁ c₂) (max c₁ c₂) x')
    (hz1 : min x x' ≤ z) (hz2 : z ≤ max x x') : z ≠ c₁ ∧ z ≠ c₂ := by
  rcases le_total c₁ c₂ with hc | hc
  · rw [min_eq_left hc, max_eq_right hc] at h
    exact piece3_between_aux hc hx1 hx2 hx1' hx2' h hz1 hz2
  · rw [min_eq_right hc, max_eq_left hc] at h
    obtain ⟨h1, h2⟩ := piece3_between_aux hc hx2 hx1 hx2' hx1' h hz1 hz2
    exact ⟨h2, h1⟩

/-! ### At most three regions near a vertex on one side -/

/-- **At most three regions touch a vertex from one side.**  Let `F` be a filter of heights
converging to `v.2` from one side (or both), `v = P.vtx k`.  If each region of a family meets,
for all heights `h` eventually along `F`, the horizontal line at height `h` arbitrarily close to
`v` and away from any two prescribed abscissae, then the family has at most three members. -/
theorem ncard_le_three_of_near {P : Polygon} (hP : P.Simple) {k : ℕ} (hk : k < P.n)
    (F : Filter ℝ) [F.NeBot] (hF : F ≤ 𝓝[≠] (P.vtx k).2) {S : Set (Set Point)}
    (hS : S ⊆ regions P)
    (hnear : ∀ R ∈ S, ∀ r > 0, ∀ c₁ c₂ : ℝ → ℝ, ∀ᶠ h in F,
      ∃ x, |x - (P.vtx k).1| < r ∧ ((x, h) : Point) ∈ R ∧ x ≠ c₁ h ∧ x ≠ c₂ h) :
    S.ncard ≤ 3 := by
  obtain ⟨r, hr, hball⟩ := boundary_near_vtx hP hk
  set v := P.vtx k
  set a := P.vtx (prevIdx P k)
  set b := P.vtx ((k + 1) % P.n)
  have hSfin : S.Finite := (regions_finite hP).subset hS
  have hF' : F ≤ 𝓝 v.2 := hF.trans nhdsWithin_le_nhds
  -- a common height `h`
  have hev1 : ∀ᶠ h in F, ∀ R ∈ S, ∃ x, |x - v.1| < r ∧ ((x, h) : Point) ∈ R ∧
      x ≠ crossX v a h ∧ x ≠ crossX v b h :=
    hSfin.eventually_all.2 fun R hR => hnear R hR r hr _ _
  have hev2 : ∀ᶠ h in F, h ≠ v.2 := Filter.mem_of_superset (hF self_mem_nhdsWithin) fun _ h => h
  have hev3 : ∀ᶠ h in F, |h - v.2| < r := by
    refine hF' (Filter.mem_of_superset (Metric.ball_mem_nhds v.2 hr) fun h hh => ?_)
    rwa [Metric.mem_ball, Real.dist_eq] at hh
  have hev4 : ∀ᶠ h in F, ∀ j ∈ Iio P.n, (P.vtx j).2 ≠ h := by
    refine (Set.finite_Iio P.n).eventually_all.2 fun j _ => ?_
    by_cases hj : (P.vtx j).2 = v.2
    · filter_upwards [hev2] with h hh
      rw [hj]
      exact Ne.symm hh
    · filter_upwards [hF' (eventually_ne_nhds (Ne.symm hj))] with h hh
      exact Ne.symm hh
  obtain ⟨h, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  choose! x hx using h1
  set c₁ := crossX v a h
  set c₂ := crossX v b h
  -- two witnesses in the same piece lie in the same region
  have key : ∀ R ∈ S, ∀ R' ∈ S, piece3 (min c₁ c₂) (max c₁ c₂) (x R) =
      piece3 (min c₁ c₂) (max c₁ c₂) (x R') → R = R' := by
    intro R hR R' hR' hpiece
    obtain ⟨hxR1, hxR2, hxR3, hxR4⟩ := hx R hR
    obtain ⟨hxR1', hxR2', hxR3', hxR4'⟩ := hx R' hR'
    set T : Set Point := (fun z : ℝ => ((z, h) : Point)) '' Icc (min (x R) (x R'))
      (max (x R) (x R'))
    have hTc : IsPreconnected T :=
      isPreconnected_Icc.image _ (Continuous.continuousOn (by fun_prop))
    have hpT : ((x R, h) : Point) ∈ T := ⟨x R, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩
    have hpT' : ((x R', h) : Point) ∈ T := ⟨x R', ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
    have hTb : ∀ q ∈ T, q ∉ P.boundary := by
      rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩ hqb
      have hzne := piece3_between hxR3 hxR4 hxR3' hxR4' hpiece hz1 hz2
      have hqball : ((z, h) : Point) ∈ ball v r := by
        rw [mem_ball_iff_abs]
        refine ⟨?_, h3⟩
        rw [abs_lt] at hxR1 hxR1' ⊢
        have := lt_min (by linarith : v.1 - r < x R) (by linarith : v.1 - r < x R')
        have := max_lt (by linarith : x R < v.1 + r) (by linarith : x R' < v.1 + r)
        constructor <;> simp only <;> linarith
      rcases hball _ hqball hqb with hq | hq
      · rw [Geometry.segment_comm] at hq
        exact hzne.1 (fst_eq_crossX hq h2)
      · exact hzne.2 (fst_eq_crossX hq h2)
    have hRfree : ((x R, h) : Point) ∈ freeRegion P := regions_subset (hS hR) hxR2
    have hTi : T ⊆ P.filled \ P.boundary :=
      subset_interior_of_isPreconnected hP hTc hTb hpT hRfree.1
    have hTf : T ⊆ freeRegion P := by
      intro q hq
      refine ⟨hTi hq, fun hqc => ?_⟩
      obtain ⟨j, hj, hjy⟩ := height_of_mem_chordUnion hqc
      obtain ⟨z, -, rfl⟩ := hq
      exact h4 j hj hjy.symm
    have hsub := hTc.subset_connectedComponentIn hpT hTf
    have hRcc : R = connectedComponentIn (freeRegion P) ((x R, h) : Point) := by
      obtain ⟨z₀, -, hz₀⟩ := hS hR
      rw [hz₀] at hxR2 ⊢
      exact connectedComponentIn_eq hxR2
    have hmem : ((x R', h) : Point) ∈ R := by
      rw [hRcc]
      exact hsub hpT'
    rcases regions_eq_or_disjoint (hS hR) (hS hR') with e | e
    · exact e
    · exact absurd hxR2' (Set.disjoint_left.1 e hmem)
  have hinj : InjOn (fun R => piece3 (min c₁ c₂) (max c₁ c₂) (x R)) S :=
    fun R hR R' hR' e => key R hR R' hR' e
  calc S.ncard ≤ (univ : Set (Fin 3)).ncard :=
        ncard_le_ncard_of_injOn _ (fun _ _ => mem_univ _) hinj (toFinite _)
    _ = 3 := by rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### The regions touching a vertex from below and from above -/

/-- **A trapezoid with `v` on its closed top side reaches `v` from below**: for all heights `h`
slightly below `v.2`, it contains a point `(x, h)` with `x` within `r` of `v.1` and different from
two prescribed abscissae. -/
theorem trapData_eventually_below {P : Polygon} (hP : P.Simple) (D : TrapData P) {k : ℕ}
    (hk : k ∈ sideVtxSet P D.i D.j D.y₂) {r : ℝ} (hr : 0 < r) (c₁ c₂ : ℝ → ℝ) :
    ∀ᶠ h in 𝓝[<] (P.vtx k).2, ∃ x, |x - (P.vtx k).1| < r ∧ ((x, h) : Point) ∈ D.region ∧
      x ≠ c₁ h ∧ x ≠ c₂ h := by
  obtain ⟨-, hky, hk1, hk2⟩ := hk
  rw [hky]
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have e2 : ∀ᶠ h in 𝓝 D.y₂, edgeX P D.i h < (P.vtx k).1 + r :=
    (continuous_edgeX P D.i).continuousAt.eventually_lt continuousAt_const (by linarith)
  have e3 : ∀ᶠ h in 𝓝 D.y₂, (P.vtx k).1 - r < edgeX P D.j h :=
    continuousAt_const.eventually_lt (continuous_edgeX P D.j).continuousAt (by linarith)
  filter_upwards [Ioo_mem_nhdsLT h12, nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e3]
    with h hh hh3 hh4
  have hij := D.isTrap.edgeX_lt hP D.free hh.1 hh.2
  have hlohi : max (edgeX P D.i h) ((P.vtx k).1 - r) < min (edgeX P D.j h) ((P.vtx k).1 + r) :=
    max_lt (lt_min hij hh3) (lt_min hh4 (by linarith))
  obtain ⟨x, hx1, hx2, hxc1, hxc2⟩ := exists_Ioo_avoid hlohi (c₁ h) (c₂ h)
  have l1 := le_max_left (edgeX P D.i h) ((P.vtx k).1 - r)
  have l2 := le_max_right (edgeX P D.i h) ((P.vtx k).1 - r)
  have u1 := min_le_left (edgeX P D.j h) ((P.vtx k).1 + r)
  have u2 := min_le_right (edgeX P D.j h) ((P.vtx k).1 + r)
  refine ⟨x, ?_, ⟨hh.1, hh.2, by show edgeX P D.i h < x; linarith,
    by show x < edgeX P D.j h; linarith⟩, hxc1, hxc2⟩
  rw [abs_lt]
  constructor <;> linarith

/-- **A trapezoid with `v` on its closed bottom side reaches `v` from above.** -/
theorem trapData_eventually_above {P : Polygon} (hP : P.Simple) (D : TrapData P) {k : ℕ}
    (hk : k ∈ sideVtxSet P D.i D.j D.y₁) {r : ℝ} (hr : 0 < r) (c₁ c₂ : ℝ → ℝ) :
    ∀ᶠ h in 𝓝[>] (P.vtx k).2, ∃ x, |x - (P.vtx k).1| < r ∧ ((x, h) : Point) ∈ D.region ∧
      x ≠ c₁ h ∧ x ≠ c₂ h := by
  obtain ⟨-, hky, hk1, hk2⟩ := hk
  rw [hky]
  have h12 : D.y₁ < D.y₂ := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have e2 : ∀ᶠ h in 𝓝 D.y₁, edgeX P D.i h < (P.vtx k).1 + r :=
    (continuous_edgeX P D.i).continuousAt.eventually_lt continuousAt_const (by linarith)
  have e3 : ∀ᶠ h in 𝓝 D.y₁, (P.vtx k).1 - r < edgeX P D.j h :=
    continuousAt_const.eventually_lt (continuous_edgeX P D.j).continuousAt (by linarith)
  filter_upwards [Ioo_mem_nhdsGT h12, nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e3]
    with h hh hh3 hh4
  have hij := D.isTrap.edgeX_lt hP D.free hh.1 hh.2
  have hlohi : max (edgeX P D.i h) ((P.vtx k).1 - r) < min (edgeX P D.j h) ((P.vtx k).1 + r) :=
    max_lt (lt_min hij hh3) (lt_min hh4 (by linarith))
  obtain ⟨x, hx1, hx2, hxc1, hxc2⟩ := exists_Ioo_avoid hlohi (c₁ h) (c₂ h)
  have l1 := le_max_left (edgeX P D.i h) ((P.vtx k).1 - r)
  have l2 := le_max_right (edgeX P D.i h) ((P.vtx k).1 - r)
  have u1 := min_le_left (edgeX P D.j h) ((P.vtx k).1 + r)
  have u2 := min_le_right (edgeX P D.j h) ((P.vtx k).1 + r)
  refine ⟨x, ?_, ⟨hh.1, hh.2, by show edgeX P D.i h < x; linarith,
    by show x < edgeX P D.j h; linarith⟩, hxc1, hxc2⟩
  rw [abs_lt]
  constructor <;> linarith

/-- The regions whose trapezoid has vertex `k` on its closed top side. -/
def topRegions (P : Polygon) (k : ℕ) : Set (Set Point) :=
  {R | ∃ D : TrapData P, D.region = R ∧ k ∈ sideVtxSet P D.i D.j D.y₂}

/-- The regions whose trapezoid has vertex `k` on its closed bottom side. -/
def botRegions (P : Polygon) (k : ℕ) : Set (Set Point) :=
  {R | ∃ D : TrapData P, D.region = R ∧ k ∈ sideVtxSet P D.i D.j D.y₁}

/-- The regions touching a vertex from below are regions. -/
theorem topRegions_subset {P : Polygon} (hP : P.Simple) (k : ℕ) : topRegions P k ⊆ regions P := by
  rintro _ ⟨D, rfl, -⟩
  exact D.region_mem_regions hP

/-- The regions touching a vertex from above are regions. -/
theorem botRegions_subset {P : Polygon} (hP : P.Simple) (k : ℕ) : botRegions P k ⊆ regions P := by
  rintro _ ⟨D, rfl, -⟩
  exact D.region_mem_regions hP

/-- **At most three regions have a given vertex on the closed top side of their trapezoid.** -/
theorem topRegions_ncard_le {P : Polygon} (hP : P.Simple) (k : ℕ) : (topRegions P k).ncard ≤ 3 := by
  by_cases hk : k < P.n
  · refine ncard_le_three_of_near hP hk (𝓝[<] (P.vtx k).2)
      (nhdsWithin_mono _ fun _ h => ne_of_lt h) (topRegions_subset hP k) ?_
    rintro _ ⟨D, rfl, hD⟩ r hr c₁ c₂
    exact trapData_eventually_below hP D hD hr c₁ c₂
  · have : topRegions P k = ∅ := by
      ext R
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨D, -, hD⟩
      exact hk hD.1
    rw [this, ncard_empty]
    omega

/-- **At most three regions have a given vertex on the closed bottom side of their trapezoid.** -/
theorem botRegions_ncard_le {P : Polygon} (hP : P.Simple) (k : ℕ) : (botRegions P k).ncard ≤ 3 := by
  by_cases hk : k < P.n
  · refine ncard_le_three_of_near hP hk (𝓝[>] (P.vtx k).2)
      (nhdsWithin_mono _ fun _ h => ne_of_gt h) (botRegions_subset hP k) ?_
    rintro _ ⟨D, rfl, hD⟩ r hr c₁ c₂
    exact trapData_eventually_above hP D hD hr c₁ c₂
  · have : botRegions P k = ∅ := by
      ext R
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨D, -, hD⟩
      exact hk hD.1
    rw [this, ncard_empty]
    omega

/-! ### Counting the incident diagonals -/

/-- The inserted diagonals incident to vertex `v` (as ordered pairs). -/
def incident (P : Polygon) (v : ℕ) : Set (ℕ × ℕ) :=
  {d | d ∈ allDiagonals P ∧ (d.1 = v ∨ d.2 = v)}

/-- The set of incident diagonals is finite. -/
theorem incident_finite {P : Polygon} (hP : P.Simple) (v : ℕ) : (incident P v).Finite :=
  (allDiagonals_finite hP).subset fun _ h => h.1

/-- The trapezoid-diagonal map `d ↦ regionOfDiag P d` is injective. -/
theorem regionOfDiag_injOn {P : Polygon} (hP : P.Simple) :
    InjOn (regionOfDiag P) (trapDiagonals P) := by
  intro d hd d' hd' heq
  obtain ⟨D, -, rfl, hD⟩ := regionOfDiag_spec hd
  obtain ⟨D', -, rfl, hD'⟩ := regionOfDiag_spec hd'
  rw [hD, hD'] at heq
  exact TrapData.diag_eq_of_region_eq hP D D' heq

/-- **At most three trapezoid diagonals have top vertex `v`.** -/
theorem ncard_trapDiagonals_fst_le {P : Polygon} (hP : P.Simple) (v : ℕ) :
    {d | d ∈ trapDiagonals P ∧ d.1 = v}.ncard ≤ 3 := by
  refine le_trans (ncard_le_ncard_of_injOn (regionOfDiag P) ?_
    ((regionOfDiag_injOn hP).mono fun _ h => h.1)
    ((regions_finite hP).subset (topRegions_subset hP v))) (topRegions_ncard_le hP v)
  rintro d ⟨hd, rfl⟩
  obtain ⟨D, -, rfl, hD⟩ := regionOfDiag_spec hd
  exact ⟨D, hD.symm, D.isTrap.topVtx_mem hP D.free⟩

/-- **At most three trapezoid diagonals have bottom vertex `v`.** -/
theorem ncard_trapDiagonals_snd_le {P : Polygon} (hP : P.Simple) (v : ℕ) :
    {d | d ∈ trapDiagonals P ∧ d.2 = v}.ncard ≤ 3 := by
  refine le_trans (ncard_le_ncard_of_injOn (regionOfDiag P) ?_
    ((regionOfDiag_injOn hP).mono fun _ h => h.1)
    ((regions_finite hP).subset (botRegions_subset hP v))) (botRegions_ncard_le hP v)
  rintro d ⟨hd, rfl⟩
  obtain ⟨D, -, rfl, hD⟩ := regionOfDiag_spec hd
  exact ⟨D, hD.symm, D.isTrap.botVtx_mem hP D.free⟩

/-- **At most two vertex-to-vertex chords start at `v`** (one per direction). -/
theorem ncard_vtxChords_fst_le {P : Polygon} (hP : P.Simple) (v : ℕ) :
    {d | d ∈ vtxChords P ∧ d.1 = v}.ncard ≤ 2 := by
  have hsub : {d | d ∈ vtxChords P ∧ d.1 = v} ⊆
      {(v, vtxIndex P (chordEnd P v 1)), (v, vtxIndex P (chordEnd P v (-1)))} := by
    rintro d ⟨hd, rfl⟩
    obtain ⟨-, hd2, σ, hσ, -, hend⟩ := hd
    have e : d = (d.1, vtxIndex P (chordEnd P d.1 σ)) := by
      rw [hend, vtxIndex_vtx hP hd2]
    rcases hσ with rfl | rfl
    · exact Or.inl e
    · exact Or.inr e
  calc _ ≤ ({(v, vtxIndex P (chordEnd P v 1)), (v, vtxIndex P (chordEnd P v (-1)))} :
        Set (ℕ × ℕ)).ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ ({(v, vtxIndex P (chordEnd P v (-1)))} : Set (ℕ × ℕ)).ncard + 1 := ncard_insert_le _ _
    _ = 2 := by rw [ncard_singleton]

/-- **Two chords in the same direction ending at the same point start at the same vertex**: a
second chord would pass through the first vertex, but open chords are interior. -/
theorem chord_src_unique {P : Polygon} (hP : P.Simple) {i i' : ℕ} (hi : i < P.n)
    (hi' : i' < P.n) {σ : ℝ} (hd : DirInterior P i σ) (hd' : DirInterior P i' σ)
    (h : chordEnd P i σ = chordEnd P i' σ) : i = i' := by
  have hx : (P.vtx i).1 + σ * chordParam P i σ = (P.vtx i').1 + σ * chordParam P i' σ :=
    congrArg Prod.fst h
  have hy : (P.vtx i).2 = (P.vtx i').2 := by simpa using congrArg Prod.snd h
  have hpos := chordParam_pos hP hi hd
  have hpos' := chordParam_pos hP hi' hd'
  rcases lt_trichotomy (chordParam P i σ) (chordParam P i' σ) with hlt | heq | hgt
  · exfalso
    have hmem := (chord_spec hP hi' hd').2.2 (chordParam P i' σ - chordParam P i σ)
      (by linarith) (by linarith)
    have he : rayPt (P.vtx i') σ (chordParam P i' σ - chordParam P i σ) = P.vtx i := by
      refine Prod.ext ?_ ?_
      · show (P.vtx i').1 + σ * (chordParam P i' σ - chordParam P i σ) = (P.vtx i).1
        rw [mul_sub]
        linarith
      · exact hy.symm
    rw [he] at hmem
    exact hmem.2 (vtx_mem_boundary P hi)
  · apply simple_vtx_inj hP hi hi'
    refine Prod.ext ?_ hy
    rw [heq] at hx
    linarith
  · exfalso
    have hmem := (chord_spec hP hi hd).2.2 (chordParam P i σ - chordParam P i' σ)
      (by linarith) (by linarith)
    have he : rayPt (P.vtx i) σ (chordParam P i σ - chordParam P i' σ) = P.vtx i' := by
      refine Prod.ext ?_ ?_
      · show (P.vtx i).1 + σ * (chordParam P i σ - chordParam P i' σ) = (P.vtx i').1
        rw [mul_sub]
        linarith
      · exact hy
    rw [he] at hmem
    exact hmem.2 (vtx_mem_boundary P hi')

/-- The vertex-to-vertex chords in direction `σ` ending at `v` form a subsingleton. -/
theorem ncard_vtxChords_snd_dir_le {P : Polygon} (hP : P.Simple) (v : ℕ) (σ : ℝ) :
    {d | d ∈ vtxChords P ∧ d.2 = v ∧ DirInterior P d.1 σ ∧
      chordEnd P d.1 σ = P.vtx d.2}.ncard ≤ 1 := by
  rw [ncard_le_one_iff ((vtxChords_finite hP).subset fun _ h => h.1)]
  rintro d d' ⟨hd, hdv, hdir, hend⟩ ⟨hd', hdv', hdir', hend'⟩
  have h1 : d.1 = d'.1 := chord_src_unique hP hd.1 hd'.1 hdir hdir'
    (by rw [hend, hend', hdv, hdv'])
  exact Prod.ext h1 (hdv.trans hdv'.symm)

/-- **At most two vertex-to-vertex chords end at `v`** (one per direction). -/
theorem ncard_vtxChords_snd_le {P : Polygon} (hP : P.Simple) (v : ℕ) :
    {d | d ∈ vtxChords P ∧ d.2 = v}.ncard ≤ 2 := by
  have hsub : {d | d ∈ vtxChords P ∧ d.2 = v} ⊆
      {d | d ∈ vtxChords P ∧ d.2 = v ∧ DirInterior P d.1 1 ∧ chordEnd P d.1 1 = P.vtx d.2} ∪
      {d | d ∈ vtxChords P ∧ d.2 = v ∧ DirInterior P d.1 (-1) ∧
        chordEnd P d.1 (-1) = P.vtx d.2} := by
    rintro d ⟨hd, hdv⟩
    obtain ⟨-, -, σ, hσ, hdir, hend⟩ := id hd
    rcases hσ with rfl | rfl
    · exact Or.inl ⟨hd, hdv, hdir, hend⟩
    · exact Or.inr ⟨hd, hdv, hdir, hend⟩
  calc _ ≤ _ := ncard_le_ncard hsub
        ((vtxChords_finite hP).subset (by rintro d (h | h) <;> exact h.1))
    _ ≤ _ := ncard_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (ncard_vtxChords_snd_dir_le hP v 1)
        (ncard_vtxChords_snd_dir_le hP v (-1))

/-- **Bounded degree**: at most `10` inserted diagonals are incident to any vertex of a simple
polygon (at most `3 + 3` trapezoid diagonals, `2 + 2` vertex-to-vertex chords). -/
theorem card_incident_le {P : Polygon} (hP : P.Simple) (v : ℕ) : (incident P v).ncard ≤ 10 := by
  set A := {d | d ∈ trapDiagonals P ∧ d.1 = v}
  set B := {d | d ∈ trapDiagonals P ∧ d.2 = v}
  set C := {d | d ∈ vtxChords P ∧ d.1 = v}
  set E := {d | d ∈ vtxChords P ∧ d.2 = v}
  have hsub : incident P v ⊆ (A ∪ B) ∪ (C ∪ E) := by
    rintro d ⟨hd | hd, h | h⟩
    · exact Or.inl (Or.inl ⟨hd, h⟩)
    · exact Or.inl (Or.inr ⟨hd, h⟩)
    · exact Or.inr (Or.inl ⟨hd, h⟩)
    · exact Or.inr (Or.inr ⟨hd, h⟩)
  have hfin : ((A ∪ B) ∪ (C ∪ E)).Finite := by
    refine (allDiagonals_finite hP).subset ?_
    rintro d ((h | h) | (h | h))
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inr h.1
  calc (incident P v).ncard ≤ ((A ∪ B) ∪ (C ∪ E)).ncard := ncard_le_ncard hsub hfin
    _ ≤ (A ∪ B).ncard + (C ∪ E).ncard := ncard_union_le _ _
    _ ≤ (A.ncard + B.ncard) + (C.ncard + E.ncard) :=
        Nat.add_le_add (ncard_union_le _ _) (ncard_union_le _ _)
    _ ≤ (3 + 3) + (2 + 2) :=
        Nat.add_le_add (Nat.add_le_add (ncard_trapDiagonals_fst_le hP v)
          (ncard_trapDiagonals_snd_le hP v))
          (Nat.add_le_add (ncard_vtxChords_fst_le hP v) (ncard_vtxChords_snd_le hP v))
    _ = 10 := by norm_num

/-! ### Degrees in the final-stage input -/

/-- **Bounded degree in the final-stage input**: at most `10` members of `diagList P T C` are
incident to any vertex `v`. -/
theorem countP_diagList_le {P : Polygon} (hP : P.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) (v : ℕ) :
    (diagList P T C).countP (fun d => decide (d.1 = v ∨ d.2 = v)) ≤ 10 := by
  classical
  rw [List.countP_eq_length_filter]
  set l := (diagList P T C).filter (fun d => decide (d.1 = v ∨ d.2 = v)) with hl
  have hnd : l.Nodup := (diagList_nodup P T C).filter _
  have hsub : (l.toFinset : Set (ℕ × ℕ)) ⊆ sortPair '' incident P v := by
    intro d hd
    rw [Finset.mem_coe, List.mem_toFinset, hl, List.mem_filter, decide_eq_true_iff] at hd
    obtain ⟨hd, hv⟩ := hd
    obtain ⟨e, he, hed⟩ := (diagList_spec hP hT hC d).1 hd
    refine ⟨e, ⟨he, ?_⟩, hed⟩
    rw [sortPair_eq_iff (allDiagonals_lt hP he).2.2] at hed
    obtain ⟨-, rfl | rfl⟩ := hed
    · exact hv
    · rcases hv with h | h
      · exact Or.inr h
      · exact Or.inl h
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = (l.toFinset : Set (ℕ × ℕ)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (sortPair '' incident P v).ncard :=
        ncard_le_ncard hsub ((incident_finite hP v).image _)
    _ ≤ (incident P v).ncard := ncard_image_le (incident_finite hP v)
    _ ≤ 10 := card_incident_le hP v

end

end Chazelle.Final
