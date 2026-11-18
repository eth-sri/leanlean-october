module

public import Chazelle.Mountain.Orientation
public import Chazelle.Existence.Convex
public import Chazelle.Split.Once

/-!
# The wedge test at a vertex of a simple polygon

Let `Q` be a simple polygon, `a = Q.vtx k` a vertex with neighbours `p = Q.vtx (prevIdx Q k)` and
`q = Q.vtx (k + 1)`, and `s = ±1` a side.  The **wedge test** `wedgeTest s p a q x` is the
arithmetic (sign-of-`det`) description of the open sector at `a` lying on the `s`-side of both
edges `p → a` and `a → q`:

* strictly convex corner (`0 < s * det p a q`): `0 < s * det p a x ∧ 0 < s * det a q x`;
* strictly reflex corner (`s * det p a q < 0`): `0 < s * det p a x ∨ 0 < s * det a q x`;
* straight corner (`det p a q = 0`): `0 < s * det a q x`.

With `s = orient Q` this is the interior angle of `Q` at `a`, with `s = -orient Q` the exterior
angle.

## Main results

* `sector_spec`: near `a`, every point passing the `s`-test is off the boundary, and it is filled
  iff `s = orient Q` (the sector is connected, avoids the boundary, and contains offset points of
  the edge `a → q` on the `s`-side).
* `wedgeTest_lerp`: the test for `lerp a b ε` (`ε > 0`) is the test for `b` — it only depends on
  the direction from `a`.
* `eventually_interior_of_wedge` (**wedge ⇒ interior**): if `b` passes the `orient Q`-test, then
  `lerp a b ε` is interior for all small `ε > 0`; `exists_interior_of_wedge` gives such an
  `ε ∈ (0, 1)`.
* `wedge_of_interior` (**interior ⇒ wedge**): if the whole open segment from `a` to `b ≠ a` is
  interior, then `b` passes the `orient Q`-test.
* `wedge_of_isDiag`: for a simple sub-polygon `subPoly P l` and an interior diagonal
  `d` of it (`Chazelle.Split.IsDiag`), the far endpoint `P.vtx d.2` passes the
  `orient (subPoly P l)`-test at the position of `d.1` in `l`.
* `orient_arcList`, `orient_splitFst`, `orient_splitSnd`: the two pieces of a split inherit the
  orientation of the split polygon.
-/

namespace Chazelle.Final

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan (prevIdx prevIdx_lt prevIdx_ne prevIdx_succ edge_prevIdx simple_vtx_ne
  simple_vtx_succ_ne simple_three_le convex_det_pos isOpen_det_pos det_reflex_point sqLen
  sqLen_pos det_offset offset eventually_offset_mem tendsto_lerp_zero mem_filled_iff
  parity_eq_of_isPreconnected interior_filled succIdx_lt)
open Chazelle.Geometry (lerp det_lerp det_cyclic det_self_left det_self_right det_self_outer
  det_eq_zero_of_mem_segment exists_lerp_of_det_eq_zero mem_segment_iff_lerp lerp_zero lerp_one
  point_ext segment_comm)
open Chazelle.Mountain (orient orient_eq orient_ne_zero sign_eq_or_eq_neg eventually_offset_orient
  orient_eq_of_filled_subset)

/-! ### The test -/

/-- **The wedge test** at the corner `p → a → q` on the side `s`: the point `x` lies in the open
sector at `a` on the `s`-side of the corner (see the module docstring). -/
def wedgeTest (s : ℝ) (p a q x : Point) : Prop :=
  if 0 < s * det p a q then 0 < s * det p a x ∧ 0 < s * det a q x
  else if s * det p a q < 0 then 0 < s * det p a x ∨ 0 < s * det a q x
  else 0 < s * det a q x

/-- The sign logic of the wedge test, on the three determinants `D = det p a q`,
`L₁ = det p a x`, `L₂ = det a q x`. -/
def wedgeSign (s D L₁ L₂ : ℝ) : Prop :=
  if 0 < s * D then 0 < s * L₁ ∧ 0 < s * L₂
  else if s * D < 0 then 0 < s * L₁ ∨ 0 < s * L₂
  else 0 < s * L₂

/-- The sign logic, normalised: failing the test on both sides for `(c, a₁, a₂)`. -/
theorem wedgeSign_cases_aux (c a₁ a₂ : ℝ)
    (h₁ : ¬ (if 0 < c then 0 < a₁ ∧ 0 < a₂ else if c < 0 then 0 < a₁ ∨ 0 < a₂ else 0 < a₂))
    (h₂ : ¬ (if 0 < -c then 0 < -a₁ ∧ 0 < -a₂ else if -c < 0 then 0 < -a₁ ∨ 0 < -a₂
      else 0 < -a₂)) :
    (a₂ = 0 ∧ 0 ≤ a₁ * c) ∨ (a₁ = 0 ∧ 0 ≤ a₂ * c) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hc' : 0 < -c := by linarith
    rw [ite_eq_right (by linarith), ite_eq_left hc] at h₁
    rw [ite_eq_left hc'] at h₂
    push Not at h₁ h₂
    by_cases hL : a₂ = 0
    · exact Or.inl ⟨hL, by nlinarith⟩
    · have ha₂ : a₂ < 0 := lt_of_le_of_ne h₁.2 hL
      have ha₁ : a₁ = 0 :=
        le_antisymm h₁.1 (by by_contra h; push Not at h; linarith [h₂ (by linarith)])
      exact Or.inr ⟨ha₁, by nlinarith⟩
  · simp only [lt_irrefl, ite_false, neg_zero] at h₁ h₂
    exact Or.inl ⟨by linarith, by simp⟩
  · rw [ite_eq_left hc] at h₁
    rw [ite_eq_right (by linarith), ite_eq_left (by linarith)] at h₂
    push Not at h₁ h₂
    by_cases hL : a₂ = 0
    · exact Or.inl ⟨hL, by nlinarith⟩
    · have ha₂ : 0 < a₂ := lt_of_le_of_ne (by linarith [h₂.2]) (Ne.symm hL)
      have ha₁ : a₁ = 0 :=
        le_antisymm (by by_contra h; push Not at h; linarith [h₁ h]) (by linarith [h₂.1])
      exact Or.inr ⟨ha₁, by nlinarith⟩

/-- **Failing both sides.**  If the determinants fail the wedge sign logic on both sides `s` and
`-s`, then the point lies on one of the two lines through the apex (`L₂ = 0` or `L₁ = 0`), with
the stated sign of the other determinant relative to `D`. -/
theorem wedgeSign_cases {s D L₁ L₂ : ℝ} (hs : s = 1 ∨ s = -1) (h₁ : ¬ wedgeSign s D L₁ L₂)
    (h₂ : ¬ wedgeSign (-s) D L₁ L₂) :
    (L₂ = 0 ∧ 0 ≤ L₁ * D) ∨ (L₁ = 0 ∧ 0 ≤ L₂ * D) := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  unfold wedgeSign at h₁ h₂
  simp only [neg_mul] at h₂
  rcases wedgeSign_cases_aux (s * D) (s * L₁) (s * L₂) h₁ h₂ with ⟨e, h⟩ | ⟨e, h⟩
  · refine Or.inl ⟨(mul_eq_zero.1 e).resolve_left hs0, ?_⟩
    rw [show s * L₁ * (s * D) = (s * s) * (L₁ * D) by ring, hss, one_mul] at h
    exact h
  · refine Or.inr ⟨(mul_eq_zero.1 e).resolve_left hs0, ?_⟩
    rw [show s * L₂ * (s * D) = (s * s) * (L₂ * D) by ring, hss, one_mul] at h
    exact h

/-- The wedge test only depends on the direction from the apex: for `ε > 0` the point
`lerp a b ε` passes iff `b` passes. -/
theorem wedgeTest_lerp (s : ℝ) (p a q b : Point) {ε : ℝ} (hε : 0 < ε) :
    wedgeTest s p a q (lerp a b ε) ↔ wedgeTest s p a q b := by
  have h1 : det p a (lerp a b ε) = ε * det p a b := by
    rw [det_lerp, det_self_right]; ring
  have h2 : det a q (lerp a b ε) = ε * det a q b := by
    rw [det_lerp, det_self_outer]; ring
  have k : ∀ u : ℝ, 0 < s * (ε * u) ↔ 0 < s * u := by
    intro u
    rw [show s * (ε * u) = ε * (s * u) by ring]
    exact ⟨fun h => pos_of_mul_pos_right h hε.le, fun h => mul_pos hε h⟩
  unfold wedgeTest
  rw [h1, h2, k, k]

/-- A point on the segment `p a` or `a q` fails the wedge test (on either side). -/
theorem not_wedgeTest_of_mem_edges {s : ℝ} {p a q x : Point}
    (hx : x ∈ Chazelle.segment p a ∨ x ∈ Chazelle.segment a q) : ¬ wedgeTest s p a q x := by
  have hc : det a q p = det p a q := det_cyclic p a q
  rcases hx with hx | hx
  · obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hx
    have e1 : det p a (lerp p a t) = 0 := by rw [det_lerp]; simp
    have e2 : det a q (lerp p a t) = (1 - t) * det p a q := by
      rw [det_lerp, det_self_outer, hc]; ring
    unfold wedgeTest
    rw [e1, e2, mul_zero]
    split_ifs with h h'
    · exact fun h'' => lt_irrefl _ h''.1
    · rintro (h'' | h'')
      · exact lt_irrefl _ h''
      · nlinarith
    · intro h''
      have : s * det p a q = 0 := by linarith [not_lt.1 h, not_lt.1 h']
      nlinarith
  · obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_lerp.1 hx
    have e1 : det p a (lerp a q t) = t * det p a q := by
      rw [det_lerp, det_self_right]; ring
    have e2 : det a q (lerp a q t) = 0 := by rw [det_lerp]; simp
    unfold wedgeTest
    rw [e1, e2, mul_zero]
    split_ifs with h h'
    · exact fun h'' => lt_irrefl _ h''.2
    · rintro (h'' | h'')
      · nlinarith
      · exact lt_irrefl _ h''
    · exact lt_irrefl _

/-! ### The sector near a vertex -/

section Sector

variable {Q : Polygon} (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n)
include hQ hk

/-- **The sector at a vertex.**  For `s = ±1` there is a ball around `a = Q.vtx k` in which every
point passing the `s`-wedge test at the corner `vtx (k-1) → a → vtx (k+1)` is off the boundary,
and is filled exactly when `s = orient Q`. -/
theorem sector_spec {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ r > 0, ∀ x ∈ ball (Q.vtx k) r,
      wedgeTest s (Q.vtx (prevIdx Q k)) (Q.vtx k) (Q.vtx ((k + 1) % Q.n)) x →
        x ∉ Q.boundary ∧ (x ∈ Q.filled ↔ s = orient Q) := by
  have hn := simple_three_le hQ
  obtain ⟨r, hr, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hk
  set p := Q.vtx (prevIdx Q k) with hp
  set a := Q.vtx k with ha
  set q := Q.vtx ((k + 1) % Q.n) with hq
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have haq : a ≠ q := simple_vtx_succ_ne hQ hk
  set S : Set Point := ball a r ∩ {x | wedgeTest s p a q x} with hS
  -- the sector avoids the boundary
  have hSb : S ⊆ Q.boundaryᶜ := by
    rintro x ⟨hxb, hxw⟩ hxB
    exact not_wedgeTest_of_mem_edges (hball x hxb hxB) hxw
  -- the sector is preconnected
  have hSc : IsPreconnected S := by
    by_cases hc : 0 < s * det p a q
    · have e : S = ball a r ∩ ({x | 0 < s * det p a x} ∩ {x | 0 < s * det a q x}) := by
        ext x; simp only [hS, mem_inter_iff, Set.mem_ofPred_eq, wedgeTest, hc, ite_true]
      rw [e]
      exact ((convex_ball a r).inter ((convex_det_pos p a s).inter
        (convex_det_pos a q s))).isPreconnected
    · by_cases hc' : s * det p a q < 0
      · have e : S = (ball a r ∩ {x | 0 < s * det p a x}) ∪ (ball a r ∩ {x | 0 < s * det a q x}) := by
          ext x; simp only [hS, mem_inter_iff, mem_union, Set.mem_ofPred_eq, wedgeTest, hc, hc',
            ite_true, ite_false]
          tauto
        rw [e]
        -- a common point of the two half-disks
        have htq : Tendsto (fun ε : ℝ => a + ε • ((a - p) - (q - a))) (𝓝[>] 0) (𝓝 a) := by
          have hcont : Continuous fun ε : ℝ => a + ε • ((a - p) - (q - a)) := by fun_prop
          have := hcont.tendsto 0
          simp only [zero_smul, add_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        obtain ⟨ε, hεb, hε0⟩ :=
          ((htq.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))).and
            self_mem_nhdsWithin).exists
        have hε0' : (0 : ℝ) < ε := hε0
        obtain ⟨e1, e2⟩ := det_reflex_point p a q ε
        refine IsPreconnected.union (a + ε • ((a - p) - (q - a))) ⟨hεb, ?_⟩ ⟨hεb, ?_⟩
          ((convex_ball a r).inter (convex_det_pos p a s)).isPreconnected
          ((convex_ball a r).inter (convex_det_pos a q s)).isPreconnected
        · show 0 < s * det p a (a + ε • ((a - p) - (q - a)))
          rw [e1]; nlinarith
        · show 0 < s * det a q (a + ε • ((a - p) - (q - a)))
          rw [e2]; nlinarith
      · have e : S = ball a r ∩ {x | 0 < s * det a q x} := by
          ext x; simp only [hS, mem_inter_iff, Set.mem_ofPred_eq, wedgeTest, hc, hc', ite_false]
        rw [e]
        exact ((convex_ball a r).inter (convex_det_pos a q s)).isPreconnected
  -- a point of the sector whose membership is known
  set U : Set Point := ball a r ∩ {x | 0 < s * det p a q → 0 < s * det p a x} with hU
  have hUo : IsOpen U := by
    by_cases hc : 0 < s * det p a q
    · have e : U = ball a r ∩ {x | 0 < s * det p a x} := by
        ext x; simp only [hU, mem_inter_iff, Set.mem_ofPred_eq]; tauto
      rw [e]; exact isOpen_ball.inter (isOpen_det_pos p a s)
    · have e : U = ball a r := by
        ext x; simp only [hU, mem_inter_iff, Set.mem_ofPred_eq]; tauto
      rw [e]; exact isOpen_ball
  have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), lerp a q t ∈ U ∧ t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [(tendsto_lerp_zero a q).eventually (isOpen_ball.mem_nhds (mem_ball_self hr)),
      Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t htb ht
    refine ⟨⟨htb, fun hc => ?_⟩, ht⟩
    show 0 < s * det p a (lerp a q t)
    rw [det_lerp, det_self_right]
    nlinarith [mul_pos ht.1 hc]
  obtain ⟨t, htU, ht01⟩ := ht_ev.exists
  obtain ⟨δ, hδU, hδor, hδ0⟩ := ((eventually_offset_mem s hUo htU).and
    ((eventually_offset_orient hQ hk ht01).and self_mem_nhdsWithin)).exists
  have hδ0' : (0 : ℝ) < δ := hδ0
  set y := offset a q t (s * δ) with hy
  have hyS : y ∈ S := by
    refine ⟨hδU.1, ?_⟩
    have hdet : 0 < s * det a q y := by
      rw [hy, det_offset, show s * (s * δ * sqLen a q) = (s * s) * (δ * sqLen a q) by ring, hss,
        one_mul]
      exact mul_pos hδ0' (sqLen_pos haq)
    show wedgeTest s p a q y
    unfold wedgeTest
    split_ifs with hc hc'
    · exact ⟨hδU.2 hc, hdet⟩
    · exact Or.inr hdet
    · exact hdet
  have hyb : y ∉ Q.boundary := hSb hyS
  have hyf : y ∈ Q.filled ↔ s = orient Q := by
    rcases sign_eq_or_eq_neg hs (orient_eq Q) with e | e
    · refine iff_of_true ?_ e
      rw [hy, e]; exact hδor.1.1
    · refine iff_of_false ?_ ?_
      · rw [hy, e, neg_mul]; exact hδor.2
      · intro e'
        have : orient Q = 0 := by linarith
        exact orient_ne_zero Q this
  refine ⟨r, hr, fun x hxb hxw => ?_⟩
  have hxS : x ∈ S := ⟨hxb, hxw⟩
  have hxB : x ∉ Q.boundary := hSb hxS
  refine ⟨hxB, ?_⟩
  rw [mem_filled_iff hQ hxB, parity_eq_of_isPreconnected Q hSc hSb hxS hyS,
    ← mem_filled_iff hQ hyb]
  exact hyf

/-- Along a direction passing the `s`-test, the points `lerp a b ε` near `a` are off the boundary
and filled exactly when `s = orient Q`. -/
theorem eventually_wedge {s : ℝ} (hs : s = 1 ∨ s = -1) {b : Point}
    (hw : wedgeTest s (Q.vtx (prevIdx Q k)) (Q.vtx k) (Q.vtx ((k + 1) % Q.n)) b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), lerp (Q.vtx k) b ε ∉ Q.boundary ∧
      (lerp (Q.vtx k) b ε ∈ Q.filled ↔ s = orient Q) := by
  obtain ⟨r, hr, hsec⟩ := sector_spec hQ hk hs
  filter_upwards [(tendsto_lerp_zero (Q.vtx k) b).eventually
    (isOpen_ball.mem_nhds (mem_ball_self hr)), self_mem_nhdsWithin] with ε hεb hε0
  exact hsec _ hεb ((wedgeTest_lerp _ _ _ _ _ hε0).2 hw)

/-- **Wedge ⇒ interior.**  If `b` passes the interior-side (`orient Q`) wedge test at vertex `k`,
then `lerp a b ε` is interior for all small `ε > 0`. -/
theorem eventually_interior_of_wedge {b : Point}
    (hw : wedgeTest (orient Q) (Q.vtx (prevIdx Q k)) (Q.vtx k) (Q.vtx ((k + 1) % Q.n)) b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), lerp (Q.vtx k) b ε ∈ Q.filled \ Q.boundary := by
  filter_upwards [eventually_wedge hQ hk (orient_eq Q) hw] with ε hε
  exact ⟨hε.2.2 rfl, hε.1⟩

/-- **Wedge ⇒ interior**, as an existence statement: some `lerp a b ε` with `ε ∈ (0, 1)` is
interior. -/
theorem exists_interior_of_wedge {b : Point}
    (hw : wedgeTest (orient Q) (Q.vtx (prevIdx Q k)) (Q.vtx k) (Q.vtx ((k + 1) % Q.n)) b) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, lerp (Q.vtx k) b ε ∈ Q.filled \ Q.boundary := by
  obtain ⟨ε, h1, h2⟩ := ((eventually_interior_of_wedge hQ hk hw).and
    (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  exact ⟨ε, h2, h1⟩

/-- **Interior ⇒ wedge.**  If `b ≠ a` and every point `lerp a b ε`, `ε ∈ (0, 1)`, of the open
segment from `a = Q.vtx k` to `b` is interior, then `b` passes the interior-side (`orient Q`)
wedge test at vertex `k`. -/
theorem wedge_of_interior {b : Point} (hba : b ≠ Q.vtx k)
    (hin : ∀ ε ∈ Ioo (0 : ℝ) 1, lerp (Q.vtx k) b ε ∈ Q.filled \ Q.boundary) :
    wedgeTest (orient Q) (Q.vtx (prevIdx Q k)) (Q.vtx k) (Q.vtx ((k + 1) % Q.n)) b := by
  have hn := simple_three_le hQ
  set p := Q.vtx (prevIdx Q k) with hp
  set a := Q.vtx k with ha
  set q := Q.vtx ((k + 1) % Q.n) with hq
  have hpa : p ≠ a := simple_vtx_ne hQ (prevIdx_lt Q hk) hk (prevIdx_ne Q hn hk)
  have haq : a ≠ q := simple_vtx_succ_ne hQ hk
  have hbd : ∀ ε ∈ Ioo (0 : ℝ) 1, lerp a b ε ∉ Q.boundary := fun ε hε => (hin ε hε).2
  have seg_aq : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → lerp a q t ∈ Q.boundary := fun t h0 h1 =>
    ⟨k, hk, mem_segment_iff_lerp.2 ⟨t, h0, h1, rfl⟩⟩
  have seg_ap : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → lerp a p t ∈ Q.boundary := fun t h0 h1 =>
    ⟨prevIdx Q k, prevIdx_lt Q hk, by
      rw [edge_prevIdx Q hk, segment_comm]; exact mem_segment_iff_lerp.2 ⟨t, h0, h1, rfl⟩⟩
  -- a direction along an edge leaves the open segment on the boundary
  have ray : ∀ w : Point, (∀ t : ℝ, 0 ≤ t → t ≤ 1 → lerp a w t ∈ Q.boundary) →
      ∀ μ : ℝ, 0 < μ → b = lerp a w μ → False := by
    intro w hw μ hμ hb
    have e : lerp a b (1 / (μ + 1)) = lerp a w (μ / (μ + 1)) := by
      rw [hb]
      apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
        field_simp <;> ring
    have h1 : 1 / (μ + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h2 : μ / (μ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    exact hbd _ ⟨by positivity, h1⟩ (by rw [e]; exact hw _ (by positivity) h2)
  -- the case of a point on the line through `a` and `q`
  have line_case : det a q b = 0 → 0 ≤ det p a b * det p a q → False := by
    intro hL2 hL1
    obtain ⟨μ, hμ⟩ := exists_lerp_of_det_eq_zero haq hL2
    have eL1 : det p a b = μ * det p a q := by rw [hμ, det_lerp, det_self_right]; ring
    rw [eL1] at hL1
    rcases lt_trichotomy μ 0 with h | h | h
    · have hDD : det p a q * det p a q ≤ 0 := by nlinarith
      have hD : det p a q = 0 := mul_self_eq_zero.1 (le_antisymm hDD (mul_self_nonneg _))
      have hD' : det a q p = 0 := by rw [det_cyclic]; exact hD
      obtain ⟨ν, hν⟩ := exists_lerp_of_det_eq_zero haq hD'
      rcases lt_trichotomy ν 0 with hν0 | hν0 | hν0
      · have hν' : ν ≠ 0 := hν0.ne
        refine ray p seg_ap (μ / ν) (div_pos_of_neg_of_neg h hν0) ?_
        rw [hμ, hν]
        apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
          field_simp <;> ring
      · exact hpa (by rw [hν, hν0, lerp_zero])
      · -- the two edges at `a` would overlap
        set t := min ν 1 / 2 with ht
        have ht0 : 0 < t := by rw [ht]; exact div_pos (lt_min hν0 one_pos) two_pos
        have htν : t < ν := by rw [ht]; linarith [min_le_left ν 1]
        have ht1 : t ≤ 1 := by rw [ht]; linarith [min_le_right ν 1]
        have hz1 : lerp a q t ∈ Q.edge k := mem_segment_iff_lerp.2 ⟨t, ht0.le, ht1, rfl⟩
        have hν' : ν ≠ 0 := hν0.ne'
        have hz2 : lerp a q t ∈ Q.edge (prevIdx Q k) := by
          rw [edge_prevIdx Q hk, segment_comm, ← hp, ← ha]
          refine mem_segment_iff_lerp.2 ⟨t / ν, by positivity,
            by rw [div_le_one hν0]; exact htν.le, ?_⟩
          rw [hν]
          apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
            field_simp <;> ring
        have hint := Chazelle.Jordan.simple_edge_inter hQ (prevIdx_lt Q hk) hk
          (prevIdx_ne Q hn hk)
        have hz : lerp a q t ∈ Q.commonEndpoints (prevIdx Q k) k := by
          rw [← hint]; exact ⟨hz2, hz1⟩
        have hz1' := hz.1
        rw [prevIdx_succ Q hk] at hz1'
        rcases hz1' with e | e
        · rw [← hp, hν] at e
          exact absurd (Chazelle.Geometry.lerp_injective haq e) htν.ne
        · have e' : lerp a q t = lerp a q 0 := by rw [lerp_zero]; exact e
          exact absurd (Chazelle.Geometry.lerp_injective haq e') ht0.ne'
    · exact hba (by rw [hμ, h, lerp_zero])
    · exact ray q seg_aq μ h hμ
  by_contra hw
  by_cases hw' : wedgeTest (-orient Q) p a q b
  · have hs' : -orient Q = 1 ∨ -orient Q = -1 := by
      rcases orient_eq Q with h | h <;> rw [h] <;> norm_num
    obtain ⟨ε, ⟨-, hf⟩, hε⟩ := ((eventually_wedge hQ hk hs' hw').and
      (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have e := hf.1 (hin ε hε).1
    exact orient_ne_zero Q (by linarith)
  · rcases wedgeSign_cases (orient_eq Q) hw hw' with ⟨hL2, hL1⟩ | ⟨hL1, hL2⟩
    · exact line_case hL2 hL1
    · obtain ⟨μ, hμ⟩ := exists_lerp_of_det_eq_zero hpa hL1
      have eL2 : det a q b = (1 - μ) * det p a q := by
        rw [hμ, det_lerp, det_self_outer, det_cyclic]; ring
      rw [eL2] at hL2
      rcases lt_trichotomy μ 1 with h | h | h
      · refine ray p seg_ap (1 - μ) (by linarith) ?_
        rw [hμ]
        apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
          ring
      · exact hba (by rw [hμ, h, lerp_one])
      · have hDD : det p a q * det p a q ≤ 0 := by nlinarith
        have hD : det p a q = 0 := mul_self_eq_zero.1 (le_antisymm hDD (mul_self_nonneg _))
        exact line_case (by rw [eL2, hD, mul_zero]) (by rw [hD, mul_zero])

/-- **Exclusion.**  If the open segment from `a = Q.vtx k` to `b` lies in a set `U` disjoint from
the interior of `Q` (e.g. the interior of another piece of a subdivision), then `b` fails the
interior-side wedge test of `Q` at vertex `k`. -/
theorem not_wedge_of_disjoint {b : Point} {U : Set Point}
    (hU : ∀ ε ∈ Ioo (0 : ℝ) 1, lerp (Q.vtx k) b ε ∈ U) (hdisj : Disjoint U (Q.filled \ Q.boundary)) :
    ¬ wedgeTest (orient Q) (Q.vtx (prevIdx Q k)) (Q.vtx k) (Q.vtx ((k + 1) % Q.n)) b := by
  intro hw
  obtain ⟨ε, hε, hin⟩ := exists_interior_of_wedge hQ hk hw
  exact Set.disjoint_left.1 hdisj (hU ε hε) hin

end Sector

/-! ### Diagonals of sub-polygons -/

section SubPoly

open Chazelle.Split (IsDiag innerSeg arcList splitFst splitSnd diagLen diagLen_spec splitPair_split
  getD_arcList length_arcList getD_idxOf)
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD)

variable {P : Polygon}

/-- The open segment of an interior diagonal of a simple sub-polygon is interior. -/
theorem isDiag_lerp_mem_interior {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    lerp (P.vtx d.1) (P.vtx d.2) ε ∈ (subPoly P l).filled \ (subPoly P l).boundary := by
  have hmem : lerp (P.vtx d.1) (P.vtx d.2) ε ∈ innerSeg (P.vtx d.1) (P.vtx d.2) := ⟨ε, hε, rfl⟩
  have hseg := Chazelle.Split.innerSeg_subset _ _ hmem
  obtain ⟨h1, h2⟩ := Chazelle.Split.ne_of_mem_innerSeg (hd.vtx_ne P hQ) hmem
  exact ⟨hd.2.2.2.2 hseg, hd.2.2.2.1 _ hseg h1 h2⟩

/-- **The diagonal passes the wedge test at its first endpoint.**  For a simple sub-polygon
`Q = subPoly P l`, an interior diagonal `d` of it and a position `i` of `d.1` in `l`, the point
`P.vtx d.2` passes the interior-side (`orient Q`) wedge test at the corner
`Q.vtx (i - 1) → Q.vtx i → Q.vtx (i + 1)`. -/
theorem wedge_of_isDiag {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d)
    {i : ℕ} (hi : i < l.length) (hx : l.getD i 0 = d.1) :
    wedgeTest (orient (subPoly P l)) ((subPoly P l).vtx (prevIdx (subPoly P l) i))
      ((subPoly P l).vtx i) ((subPoly P l).vtx ((i + 1) % (subPoly P l).n)) (P.vtx d.2) := by
  have hi' : i < (subPoly P l).n := by rw [n_subPoly]; exact hi
  have ha : (subPoly P l).vtx i = P.vtx d.1 := by rw [vtx_subPoly_getD P l hi, hx]
  refine wedge_of_interior hQ hi' (by rw [ha]; exact (hd.vtx_ne P hQ).symm) ?_
  intro ε hε
  rw [ha]
  exact isDiag_lerp_mem_interior hQ hd hε

/-- **Orientation of an arc.**  If `subPoly P l` and the sub-polygon of an arc `arcList l s L`
(`1 ≤ L < l.length`) are simple and the arc's filled region lies in that of `subPoly P l`, they
have the same orientation (they share the directed edge `l[s] → l[s+1]`). -/
theorem orient_arcList {l : List ℕ} (hQ : (subPoly P l).Simple) {s L : ℕ} (hs : s < l.length)
    (hL1 : 1 ≤ L) (hL : L < l.length) (hA : (subPoly P (arcList l s L)).Simple)
    (hsub : (subPoly P (arcList l s L)).filled ⊆ (subPoly P l).filled) :
    orient (subPoly P (arcList l s L)) = orient (subPoly P l) := by
  have hlen := length_arcList (s := s) hL
  have hn1 : ((0 + 1) % (subPoly P (arcList l s L)).n) = 1 := by
    rw [n_subPoly, hlen]; exact Nat.mod_eq_of_lt (by omega)
  refine (orient_eq_of_filled_subset hA hQ (i := 0) (j := s) (by rw [n_subPoly, hlen]; omega)
    (by rw [n_subPoly]; exact hs) ?_ ?_ hsub).symm
  · rw [vtx_subPoly_getD P _ (by rw [hlen]; omega), vtx_subPoly_getD P _ hs,
      getD_arcList hL (Nat.zero_le _), Nat.add_zero, Nat.mod_eq_of_lt hs]
  · rw [hn1, vtx_subPoly_getD P _ (by rw [hlen]; omega), n_subPoly,
      vtx_subPoly_getD P _ (Nat.mod_lt _ (by omega)), getD_arcList hL hL1]

/-- **The first piece of a split inherits the orientation.** -/
theorem orient_splitFst {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    orient (subPoly P (splitFst l d)) = orient (subPoly P l) := by
  obtain ⟨hL1, hLn, -⟩ := diagLen_spec hd.1 hd.2.1 hd.2.2.1
  have hsp := splitPair_split hQ hd
  exact orient_arcList hQ (List.idxOf_lt_length_of_mem hd.1) hL1 hLn hsp.simple₁
    hsp.filled_subset

/-- **The second piece of a split inherits the orientation.** -/
theorem orient_splitSnd {l : List ℕ} (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    orient (subPoly P (splitSnd l d)) = orient (subPoly P l) := by
  obtain ⟨hL1, hLn, -⟩ := diagLen_spec hd.1 hd.2.1 hd.2.2.1
  have hsp := splitPair_split hQ hd
  exact orient_arcList hQ (List.idxOf_lt_length_of_mem hd.2.1) (by omega) (by omega)
    hsp.simple₂ hsp.symm.filled_subset

end SubPoly

end

end Chazelle.Final
