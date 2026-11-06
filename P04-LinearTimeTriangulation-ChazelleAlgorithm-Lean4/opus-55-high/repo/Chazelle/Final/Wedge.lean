module

public import Chazelle.MacT
public import Chazelle.Existence.Diagonal
public import Chazelle.Jordan.SegmentFacts
public import Chazelle.Programs.Tactics
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

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
  · have hc' : 0 < -c := by_linarith
    rw [ite_eq_right by_linarith, ite_eq_left hc] at h₁
    rw [ite_eq_left hc'] at h₂
    zufzm

    · exact Or.inl ⟨hL, by_nlinarith⟩
    · have ha₂ : a₂ < 0 := by_grind
      have ha₁ : a₁ = 0 :=
        by grind
      exact Or.inr ztugz
  · grind
  · rw [ite_eq_left hc] at h₁
    rw [ite_eq_right by_linarith, ite_eq_left by_linarith] at h₂
    zufzm

    · simp_all
    · have ha₂ : 0 < a₂ := by_grind
      have ha₁ : a₁ = 0 :=
        by grind
      exact Or.inr ztugz

/-- **Failing both sides.**  If the determinants fail the wedge sign logic on both sides `s` and
`-s`, then the point lies on one of the two lines through the apex (`L₂ = 0` or `L₁ = 0`), with
the stated sign of the other determinant relative to `D`. -/
theorem wedgeSign_cases {s D L₁ L₂ : ℝ} (hs : s = 1 ∨ s = -1) (h₁ : ¬ wedgeSign s D L₁ L₂)
    (h₂ : ¬ wedgeSign (-s) D L₁ L₂) :
    (L₂ = 0 ∧ 0 ≤ L₁ * D) ∨ (L₁ = 0 ∧ 0 ≤ L₂ * D) := by
  zukfw
  have hs0 : ztppw := by_grind
  unfold wedgeSign at h₁ h₂
  simp only [neg_mul] at h₂
  rcases wedgeSign_cases_aux ztohe (s * L₁) (s * L₂) h₁ h₂ with ⟨e, h⟩ | ⟨e, h⟩
  · refine Or.inl ztbbk
    rw [show s * L₁ * ztohe = ztohg * (L₁ * D) by ring, hss, one_mul] at h
    zubh
  · refine Or.inr ztbbk
    rw [show s * L₂ * ztohe = ztohg * (L₂ * D) by ring, hss, one_mul] at h
    zubh

/-- The wedge test only depends on the direction from the apex: for `ε > 0` the point
`lerp a b ε` passes iff `b` passes. -/
theorem wedgeTest_lerp (s : ℝ) (p a q b : Point) {ε : ℝ} (hε : 0 < ε) :
    wedgeTest s p a q ztlqu ↔ wedgeTest s p a q b := by
  have h1 : det p a ztlqu = ε * det p a b := by
    zuihk
  have h2 : det a q ztlqu = ε * det a q b := by
    rw [det_lerp, det_self_outer]; ring
  have k : ∀ u : ℝ, 0 < s * ztufd ↔ 0 < s * u := by
    zulnl
    rw [show s * ztufd = ε * zttzb by ring]
    simp_all
  unfold wedgeTest
  grind

/-- A point on the segment `p a` or `a q` fails the wedge test (on either side). -/
theorem not_wedgeTest_of_mem_edges {s : ℝ} {p a q x : Point}
    (hx : x ∈ Chazelle.segment p a ∨ x ∈ Chazelle.segment a q) : ¬ wedgeTest s p a q x := by
  have hc := det_cyclic p a q
  zuky
  · zueuv
    have e1 : det p a ztrti = 0 := by zuoha; simp
    have e2 : det a q ztrti = ztca * det p a q := by
      rw [det_lerp, det_self_outer, hc]; ring
    zueny

    · simp
    · zuknx
      · simp_all
      · nlinarith
    · intro h''
      have : s * det p a q = 0 := by_grind
      nlinarith
  · zueuv
    have e1 : det p a ztrth = t * det p a q := by
      zuihk
    have e2 : det a q ztrth = 0 := by zuoha; simp
    zueny

    · simp
    · zuknx
      · nlinarith
      simp_all
    simp

/-! ### The sector near a vertex -/
section Sector
variable {Q : Polygon} (hQ : Q.Simple) {k : ℕ} (hk : k < Q.n)
include hQ hk
variable {s : ℝ} {b : Point}
/-- **The sector at a vertex.**  For `s = ±1` there is a ball around `a = Q.vtx k` in which every
point passing the `s`-wedge test at the corner `vtx (k-1) → a → vtx (k+1)` is off the boundary,
and is filled exactly when `s = orient Q`. -/
theorem sector_spec (hs : s = 1 ∨ s = -1) :
    ∃ r > 0, ∀ x ∈ ball ztbda r,
      wedgeTest s ztcha ztbda ztwoh x →
        x ∉ Q.boundary ∧ (x ∈ Q.filled ↔ s = orient Q) := by
  zuerp
  obtain ⟨r, hr, hball⟩ := Chazelle.Existence.boundary_near_vtx hQ hk
  set p := Q.vtx ztkck with hp
  zuena

  zukfw
  zukaz
  set S : Set Point := ball a r ∩ {x | wedgeTest s p a q x} with hS
  -- the sector avoids the boundary
  have hSb : S ⊆ Q.boundaryᶜ := by
    rintro x ⟨hxb, hxw⟩ hxB
    exact not_wedgeTest_of_mem_edges by_simp_all hxw
  -- the sector is preconnected
  have hSc : ztulh := by
    zufqz
    · have e : S = ball a r ∩ ({x | 0 < s * det p a x} ∩ {x | 0 < s * det a q x}) := by
        ext x; simp only [hS, mem_inter_iff, Set.mem_ofPred_eq, wedgeTest, hc, ite_true]
      zui
      exact ((convex_ball a r).inter ((convex_det_pos p a s).inter
        ztlmg)).isPreconnected
    · by_cases hc' : s * det p a q < 0
      · have e : S = (ball a r ∩ {x | 0 < s * det p a x}) ∪ (ball a r ∩ {x | 0 < s * det a q x}) := by
          ext x; simp only [hS, mem_inter_iff, mem_union, Set.mem_ofPred_eq, wedgeTest, hc, hc',
            ite_true, ite_false]
          tauto
        zui
        -- a common point of the two half-disks
        have htq : Tendsto (fun ε : ℝ => a + ε • ((a - p) - (q - a))) (𝓝[>] 0) (𝓝 a) := by
          have hcont : Continuous fun ε : ℝ => a + ε • (zteoo - ztkcr) := by fun_prop
          have := hcont.tendsto 0
          zudlt
          zuhv
        obtain ⟨ε, hεb, hε0⟩ :=
          ((htq.eventually ztsd).and
            self_mem_nhdsWithin).exists
        zuizv
        obtain ⟨e1, e2⟩ := det_reflex_point p a q ε
        refine IsPreconnected.union _ zthnf zthnf
          ((convex_ball a r).inter (convex_det_pos p a s)).isPreconnected
          ((convex_ball a r).inter ztlmg).isPreconnected
        · show 0 < s * det p a _
          zvmxy; nlinarith
        · show 0 < s * det a q _
          zvnlz; nlinarith
      · have e : S = ball a r ∩ {x | 0 < s * det a q x} := by
          ext x; simp only [hS, mem_inter_iff, Set.mem_ofPred_eq, wedgeTest, hc, hc', ite_false]
        zui
        exact ((convex_ball a r).inter ztlmg).isPreconnected
  -- a point of the sector whose membership is known
  set U : Set Point := ball a r ∩ {x | 0 < s * det p a q → 0 < s * det p a x} with hU
  have hUo : ztule := by
    zufqz
    · have e : U = ball a r ∩ {x | 0 < s * det p a x} := by
        grind
      zvmwe; exact isOpen_ball.inter (isOpen_det_pos p a s)
    · have e : U = ball a r := by
        grind
      zvmwe; simp
  have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), lerp a q t ∈ U ∧ t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [(tendsto_lerp_zero a q).eventually ztsd,
      Ioo_mem_nhdsGT ztcjf] with t htb ht
    refine ⟨⟨htb, fun hc => ?_⟩, ht⟩
    show 0 < s * det p a _
    zukqn
    nlinarith [mul_pos ht.1 hc]
  obtain ⟨t, htU, ht01⟩ := ht_ev.exists
  obtain ⟨δ, hδU, hδor, hδ0⟩ := ((eventually_offset_mem s hUo htU).and
    ((eventually_offset_orient hQ hk ht01).and self_mem_nhdsWithin)).exists
  zuyx
  set y := offset a q t (s * δ) with hy
  have hyS : y ∈ S := by
    refine ⟨hδU.1, ?_⟩
    have hdet : 0 < s * det a q y := by
      rw [hy, det_offset, show s * (s * δ * sqLen a q) = ztohg * (δ * sqLen a q) by ring, hss,
        one_mul]
      exact mul_pos hδ0' (sqLen_pos haq)
    show wedgeTest s p a q y
    unfold wedgeTest
    split_ifs with hc hc'
    · zubfo
    · grind
    omega
  have hyb := hSb hyS
  have hyf : y ∈ Q.filled ↔ s = orient Q := by
    rcases sign_eq_or_eq_neg hs ztkbs with e | e
    · grind
    grind
  refine ⟨r, hr, fun x hxb hxw => ?_⟩
  have hxS : x ∈ S := ⟨hxb, hxw⟩
  have hxB := hSb hxS
  refine ⟨hxB, ?_⟩
  rw [mem_filled_iff hQ hxB, parity_eq_of_isPreconnected Q hSc hSb hxS hyS,
    ← mem_filled_iff hQ hyb]
  omega

/-- Along a direction passing the `s`-test, the points `lerp a b ε` near `a` are off the boundary
and filled exactly when `s = orient Q`. -/
theorem eventually_wedge (hs : s = 1 ∨ s = -1) {b : Point}
    (hw : wedgeTest s ztcha ztbda ztwoh b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), lerp ztbda b ε ∉ Q.boundary ∧
      (lerp ztbda b ε ∈ Q.filled ↔ s = orient Q) := by
  obtain ⟨r, hr, hsec⟩ := sector_spec hQ hk hs
  filter_upwards [(tendsto_lerp_zero ztbda b).eventually
    ztsd, self_mem_nhdsWithin] with ε hεb hε0
  exact hsec _ hεb ((wedgeTest_lerp _ _ _ _ _ hε0).2 hw)

/-- **Wedge ⇒ interior.**  If `b` passes the interior-side (`orient Q`) wedge test at vertex `k`,
then `lerp a b ε` is interior for all small `ε > 0`. -/
theorem eventually_interior_of_wedge
    (hw : wedgeTest ztgld ztcha ztbda ztwoh b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), lerp ztbda b ε ∈ Q.filled \ Q.boundary := by
  filter_upwards [eventually_wedge hQ hk ztkbs hw] with ε hε
  simp_all

/-- **Wedge ⇒ interior**, as an existence statement: some `lerp a b ε` with `ε ∈ (0, 1)` is
interior. -/
theorem exists_interior_of_wedge
    (hw : wedgeTest ztgld ztcha ztbda ztwoh b) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, lerp ztbda b ε ∈ Q.filled \ Q.boundary := by
  obtain ⟨ε, h1, h2⟩ := ((eventually_interior_of_wedge hQ hk hw).and
    ztxgc).exists
  grind

/-- **Interior ⇒ wedge.**  If `b ≠ a` and every point `lerp a b ε`, `ε ∈ (0, 1)`, of the open
segment from `a = Q.vtx k` to `b` is interior, then `b` passes the interior-side (`orient Q`)
wedge test at vertex `k`. -/
theorem wedge_of_interior (hba : b ≠ Q.vtx k)
    (hin : ∀ ε ∈ Ioo (0 : ℝ) 1, lerp ztbda b ε ∈ Q.filled \ Q.boundary) :
    wedgeTest ztgld ztcha ztbda ztwoh b := by
  zuerp
  set p := Q.vtx _ with hp
  zuena

  have hpa : p ≠ a := simple_vtx_ne hQ ztkcm hk ztrul
  zukaz
  have hbd : ∀ ε ∈ Ioo (0 : ℝ) 1, lerp a b ε ∉ Q.boundary := by_simp_all
  have seg_aq : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → lerp a q t ∈ Q.boundary := fun t h0 h1 =>
    ⟨k, hk, mem_segment_iff_lerp.2 by_grind⟩
  have seg_ap : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → lerp a p t ∈ Q.boundary := fun t h0 h1 =>
    ⟨prevIdx Q k, prevIdx_lt Q hk, by
      rw [edge_prevIdx Q hk, segment_comm]; exact mem_segment_iff_lerp.2 by_grind⟩
  -- a direction along an edge leaves the open segment on the boundary
  have ray : ∀ w : Point, (∀ t : ℝ, 0 ≤ t → t ≤ 1 → lerp a w t ∈ Q.boundary) →
      ∀ μ : ℝ, 0 < μ → b = lerp a w μ → False := by
    intro w hw μ hμ hb
    have e : lerp a b (1 / ztkhw) = lerp a w (μ / ztkhw) := by
      rw [hb]
      apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
        zufsp
    have h1 : 1 / ztkhw < 1 := by zuosn; linarith
    have h2 : μ / ztkhw ≤ 1 := by zunwx; linarith
    exact hbd _ ⟨by_positivity, h1⟩ (by zvmwe; exact by_grind)
  -- the case of a point on the line through `a` and `q`
  have line_case : det a q b = 0 → 0 ≤ det p a b * det p a q → False := by
    intro hL2 hL1
    obtain ⟨μ, hμ⟩ := exists_lerp_of_det_eq_zero haq hL2
    have eL1 : det p a b = μ * det p a q := by rw [hμ, det_lerp, det_self_right]; ring
    rw [eL1] at hL1
    rcases lt_trichotomy μ 0 with h | h | h
    · zuftl

      have hD' : det a q p = 0 := by rw [det_cyclic]; exact hD
      obtain ⟨ν, hν⟩ := exists_lerp_of_det_eq_zero haq hD'
      rcases lt_trichotomy ν 0 with hν0 | hν0 | hν0
      · have hν' := hν0.ne
        refine ray p seg_ap _ (div_pos_of_neg_of_neg h hν0) ?_
        rw [hμ, hν]
        apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
          zufsp
      · exact hpa (by rw [hν, hν0, lerp_zero])
      · -- the two edges at `a` would overlap
        set t := min ν 1 / 2 with ht
        have ht0 : ztfkp := by_positivity
        have htν : t < ν := by zvnup; linarith [min_le_left ν 1]
        have ht1 : t ≤ 1 := by zvnup; linarith [min_le_right ν 1]
        have hz1 : lerp a q t ∈ Q.edge k := mem_segment_iff_lerp.2 by_grind
        have hν' := hν0.ne'
        have hz2 : lerp a q t ∈ Q.edge ztkck := by
          rw [edge_prevIdx Q hk, segment_comm, ← hp, ← ha]
          refine mem_segment_iff_lerp.2 ⟨t / ν, by_positivity,
            by rw [div_le_one hν0]; grind, ?_⟩
          rw [hν]
          apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
            zufsp
        have hint := Chazelle.Jordan.simple_edge_inter hQ ztkcm hk
          by_grind
        have hz : lerp a q t ∈ Q.commonEndpoints ztkck k := by
          rw [← hint]; tauto
        have hz1' := hz.1
        rw [prevIdx_succ Q hk] at hz1'
        rcases hz1' with e | e
        · rw [← hp, hν] at e
          exact absurd (Chazelle.Geometry.lerp_injective haq e) htν.ne
        · have e' : lerp a q t = lerp a q 0 := by rw [lerp_zero]; exact e
          exact absurd (Chazelle.Geometry.lerp_injective haq e') ht0.ne'
    · simp_all
    tauto
  by_contra hw
  by_cases hw' : wedgeTest (-orient Q) p a q b
  · have hs' : -orient Q = 1 ∨ -orient Q = -1 := by
      rcases orient_eq Q with h | h <;> zvmwc <;> norm_num
    obtain ⟨ε, ⟨-, hf⟩, hε⟩ := ((eventually_wedge hQ hk hs' hw').and
      ztxgc).exists
    have e := hf.1 (hin ε hε).1
    grind
  · rcases wedgeSign_cases ztkbs hw hw' with ⟨hL2, hL1⟩ | ⟨hL1, hL2⟩
    · grind
    · obtain ⟨μ, hμ⟩ := exists_lerp_of_det_eq_zero hpa hL1
      have eL2 : det a q b = ztndo * det p a q := by
        rw [hμ, det_lerp, det_self_outer, det_cyclic]; ring
      rw [eL2] at hL2
      rcases lt_trichotomy μ 1 with h | h | h
      · refine ray p seg_ap ztndo by_linarith ?_
        zujkb
        apply point_ext <;> simp only [Chazelle.Geometry.lerp_fst, Chazelle.Geometry.lerp_snd] <;>
          ring
      · grind
      · zuftl

        grind

/-- **Exclusion.**  If the open segment from `a = Q.vtx k` to `b` lies in a set `U` disjoint from
the interior of `Q` (e.g. the interior of another piece of a subdivision), then `b` fails the
interior-side wedge test of `Q` at vertex `k`. -/
theorem not_wedge_of_disjoint {U : Set Point}
    (hU : ∀ ε ∈ Ioo (0 : ℝ) 1, lerp ztbda b ε ∈ U) (hdisj : Disjoint U ztrx) :
    ¬ wedgeTest ztgld ztcha ztbda ztwoh b := by
  intro hw
  obtain ⟨ε, hε, hin⟩ := exists_interior_of_wedge hQ hk hw
  grind
end Sector

/-! ### Diagonals of sub-polygons -/
section SubPoly
open Chazelle.Split (IsDiag innerSeg arcList splitFst splitSnd diagLen diagLen_spec splitPair_split
  getD_arcList length_arcList getD_idxOf)
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD)
variable {P : Polygon}
variable {l : List ℕ}
/-- The open segment of an interior diagonal of a simple sub-polygon is interior. -/
theorem isDiag_lerp_mem_interior (hQ : (subPoly P l).Simple) {d : ℕ × ℕ}
    (hd : IsDiag P l d) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    lerp ztjla ztjlb ε ∈ (subPoly P l).filled \ (subPoly P l).boundary := by
  have hmem : lerp _ _ ε ∈ innerSeg ztjla ztjlb := ⟨ε, hε, rfl⟩
  have hseg := Chazelle.Split.innerSeg_subset _ _ hmem
  obtain ⟨h1, h2⟩ := Chazelle.Split.ne_of_mem_innerSeg zttni hmem
  exact ⟨hd.2.2.2.2 hseg, hd.2.2.2.1 _ hseg h1 h2⟩

/-- **The diagonal passes the wedge test at its first endpoint.**  For a simple sub-polygon
`Q = subPoly P l`, an interior diagonal `d` of it and a position `i` of `d.1` in `l`, the point
`P.vtx d.2` passes the interior-side (`orient Q`) wedge test at the corner
`Q.vtx (i - 1) → Q.vtx i → Q.vtx (i + 1)`. -/
theorem wedge_of_isDiag (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d)
    {i : ℕ} (hi : i < l.length) (hx : l.getD i 0 = d.1) :
    wedgeTest (orient ztdi) ((subPoly P l).vtx (prevIdx ztdi i))
      ((subPoly P l).vtx i) ((subPoly P l).vtx (ztg % (subPoly P l).n)) ztjlb := by
  have hi' : i < (subPoly P l).n := by_simp_all
  have ha : (subPoly P l).vtx i = P.vtx d.1 := by rw [vtx_subPoly_getD P l hi, hx]
  refine wedge_of_interior hQ hi' (by rw [ha]; exact (hd.vtx_ne P hQ).symm) ?_
  zudik
  rw [ha]
  exact isDiag_lerp_mem_interior hQ hd hε

/-- **Orientation of an arc.**  If `subPoly P l` and the sub-polygon of an arc `arcList l s L`
(`1 ≤ L < l.length`) are simple and the arc's filled region lies in that of `subPoly P l`, they
have the same orientation (they share the directed edge `l[s] → l[s+1]`). -/
theorem orient_arcList (hQ : (subPoly P l).Simple) {s L : ℕ} (hs : s < l.length)
    (hL1 : 1 ≤ L) (hL : L < l.length) (hA : (subPoly P ztdll).Simple)
    (hsub : (subPoly P ztdll).filled ⊆ (subPoly P l).filled) :
    orient (subPoly P ztdll) = orient ztdi := by
  have hlen := length_arcList (s := s) hL
  have hn1 : (ztbgo % (subPoly P ztdll).n) = 1 := by
    rw [n_subPoly, hlen]; exact Nat.mod_eq_of_lt by_omega
  refine (orient_eq_of_filled_subset hA hQ (i := 0) (j := s) by_simp_all
    by_simp_all ?_ ?_ hsub).symm
  · rw [vtx_subPoly_getD P _ by_omega, vtx_subPoly_getD P _ hs,
      getD_arcList hL ztbg, Nat.add_zero, Nat.mod_eq_of_lt hs]
  · rw [hn1, vtx_subPoly_getD P _ by_omega, n_subPoly,
      vtx_subPoly_getD P _ ztcv, getD_arcList hL hL1]

/-- **The first piece of a split inherits the orientation.** -/
theorem orient_splitFst (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    orient ztzya = orient ztdi := by
  zucxr

  exact orient_arcList hQ ztuzo hL1 hLn hsp.simple₁
    hsp.filled_subset

/-- **The second piece of a split inherits the orientation.** -/
theorem orient_splitSnd (hQ : (subPoly P l).Simple) {d : ℕ × ℕ} (hd : IsDiag P l d) :
    orient ztzyb = orient ztdi := by
  zucxr

  exact orient_arcList hQ (List.idxOf_lt_length_of_mem hd.2.1) by_omega by_omega
    hsp.simple₂ hsp.symm.filled_subset
end SubPoly
end
end Chazelle.Final
namespace Chazelle.Jordan
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Geometry (lerp lerp_fst lerp_snd det_lerp det_lerp_self lerp_mem_segment point_ext
  point_ext_iff)

/-! ### Definitions -/

/-- The signed crossing of the upward vertical ray from `z` by the directed edge `u → v`:
`-1` if the edge crosses it from left to right, `1` from right to left, `0` if it does not
cross it (`crosses`, half-open rule). -/
noncomputable def windInd (z u v : Point) : ℤ :=
  if crosses z u v then (if u.1 < v.1 then -1 else 1) else 0

/-! ### Basic lemmas -/

/-! ### Local behaviour of one edge -/

/-! ### Local constancy -/

/-! ### Far away -/

/-! ### Jump across edges -/

/-! ### Subdividing an edge -/

/-! ### Open paths and closed walks -/

/-- The signed crossing sum of the open polygonal path through the vertex list `L`. -/
noncomputable def windPath (z : Point) : List Point → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: l => windInd z a b + windPath z (b :: l)

/-! ### Simple polygons: the winding number is the orientation inside, `0` outside -/
end
end Chazelle.Jordan
namespace Chazelle
namespace Programs
open Machine
@[expose] public section
def FirstHitRight (P : Polygon) (q : Point) (x : ℝ) : Prop :=
  (∃ i, i < P.n ∧ HitsRight q ztdn ztwir ∧
    x = hitX q ztdn ztwir) ∧
  (∀ i, i < P.n → HitsRight q ztdn ztwir →
    x ≤ hitX q ztdn ztwir)
variable {P : Polygon} {q : Point} {x y : ℝ}

/-- The first hit is strictly to the right of `q`. -/
theorem FirstHitRight.lt (h : FirstHitRight P q x) : q.1 < x := by
  obtain ⟨⟨i, hi, hhit, rfl⟩, -⟩ := h
  exact hhit.2

/-! ### The program computes the first hit -/
end
end Programs
end Chazelle
namespace Chazelle.Visibility
@[expose] public section
open Set Filter Topology
open Chazelle.Jordan

/-! ### The transpose polygon -/

/-- The polygon with the two coordinates of every vertex exchanged. -/
def transpose (P : Polygon) : Polygon := ⟨P.vertices.map Prod.swap⟩
variable (P : Polygon) (i : ℕ) (S : Set Point) (p : Point) (σ t : ℝ) (q : Point)
@[simp] theorem transpose_n : (transpose P).n = P.n := by
  simp [transpose, Polygon.n]
@[simp] theorem transpose_vtx : (transpose P).vtx i = (P.vtx i).swap := by
  simp only [transpose, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_map]
  grind

/-- Swapping the coordinates of both endpoints transports a segment. -/
theorem segment_swap (a b : Point) :
    Chazelle.segment a.swap b.swap = Prod.swap ⁻¹' Chazelle.segment a b := by
  zufj
  simp only [Chazelle.segment, mem_ofPred_eq, mem_preimage, Prod.swap, Geometry.point_ext_iff]
  grind
theorem transpose_edge :
    (transpose P).edge i = Prod.swap ⁻¹' P.edge i := by
  simp only [Polygon.edge, transpose_n, transpose_vtx, segment_swap]

/-- The boundary of the transpose is the transposed boundary. -/
theorem transpose_boundary : (transpose P).boundary = Prod.swap ⁻¹' P.boundary := by
  zufj
  simp only [Polygon.boundary, mem_ofPred_eq, mem_preimage, transpose_n, transpose_edge]
theorem transpose_commonEndpoints (i j : ℕ) :
    (transpose P).commonEndpoints i j = Prod.swap ⁻¹' P.commonEndpoints i j := by
  zufj
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, mem_preimage, transpose_n, transpose_vtx]
  grind

/-- The transpose of a simple polygon is simple. -/
theorem transpose_simple {P : Polygon} (hP : P.Simple) : (transpose P).Simple := by
  zucxq
  refine ⟨by simpa using h3, ?_, ?_⟩
  · intro i j hi hj h
    zujlt
    rw [transpose_vtx, transpose_vtx] at h
    grind
  · zuvb
    zujlt
    rw [transpose_edge, transpose_edge, transpose_commonEndpoints, ← preimage_inter,
      hedge i j hi hj hij]

/-- `Prod.swap` as a homeomorphism of the plane. -/
def swapHomeo : Point ≃ₜ Point := Homeomorph.prodComm ℝ ℝ
theorem swap_image_eq_preimage : Prod.swap '' S = Prod.swap ⁻¹' S := by
  grind

/-- Connected components in a transposed set are the transposed components. -/
theorem connectedComponentIn_swap (z : Point) :
    connectedComponentIn ztrkc z = Prod.swap ⁻¹' connectedComponentIn S z.swap := by
  by_cases hz : z ∈ Prod.swap ⁻¹' S
  · have := swapHomeo.image_connectedComponentIn hz
    have hcoe : ⇑swapHomeo = Prod.swap := rfl
    rw [hcoe, swap_image_eq_preimage, swap_image_eq_preimage, preimage_preimage] at this
    simp only [Prod.swap_swap, preimage_id'] at this
    grind
  · have hz' : z.swap ∉ S := hz
    rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty hz']
    simp

/-- Boundedness is invariant under transposition. -/
theorem isBoundedSet_swap_iff : IsBoundedSet ztrkc ↔ IsBoundedSet S := by
  constructor
  · zudtb
    refine ztexn
    grind
  · zudtb
    refine ztexn
    grind

/-- The filled region of the transpose is the transposed filled region. -/
theorem transpose_filled : (transpose P).filled = Prod.swap ⁻¹' P.filled := by
  zufj
  simp only [Polygon.filled, transpose_boundary, mem_union, mem_preimage, mem_ofPred_eq]
  rw [← preimage_compl, connectedComponentIn_swap, isBoundedSet_swap_iff]
theorem mem_transpose_filled_iff :
    p ∈ (transpose P).filled ↔ p.swap ∈ P.filled := by
  rw [transpose_filled]; rfl
theorem mem_transpose_boundary_iff :
    p ∈ (transpose P).boundary ↔ p.swap ∈ P.boundary := by
  rw [transpose_boundary]; rfl

/-! ### Horizontal parity -/

/-! ### Horizontal rays and their first boundary hit -/

/-- The point at parameter `t` on the horizontal ray from `p` in direction `σ`. -/
def rayPt (p : Point) (σ t : ℝ) : Point := (p.1 + σ * t, p.2)
@[simp] theorem rayPt_fst : (rayPt p σ t).1 = p.1 + σ * t := rfl
@[simp] theorem rayPt_snd : (rayPt p σ t).2 = p.2 := rfl
@[simp] theorem rayPt_zero (σ : ℝ) : rayPt p σ 0 = p := by
  zugyz
theorem continuous_rayPt (σ : ℝ) : Continuous ztogw := by
  zumuc
theorem rayPt_injective {σ : ℝ} (hσ : σ ≠ 0) : Function.Injective ztogw := by
  intro s t h
  have := congrArg Prod.fst h
  zudv
  simp_all

/-- The parameters `t > 0` at which the ray meets the boundary. -/
def hitSet (P : Polygon) (p : Point) (σ : ℝ) : Set ℝ :=
  {t : ℝ | 0 < t ∧ rayPt p σ t ∈ P.boundary}

/-- The parameter of the first boundary point of the open ray (`sInf` of `hitSet`; `0` when the
ray never meets the boundary). -/
noncomputable def hitParam (P : Polygon) (p : Point) (σ : ℝ) : ℝ := sInf ztlpr
theorem hitSet_bddBelow (σ : ℝ) : BddBelow ztlpr :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- A connected piece of a horizontal ray avoiding the boundary and containing an interior point
is interior. -/
theorem rayPt_mem_interior_of_isPreconnected {P : Polygon} (hP : P.Simple) {p : Point} {σ : ℝ}
    {I : Set ℝ} (hI : IsPreconnected I) (hIb : ∀ t ∈ I, rayPt p σ t ∉ P.boundary)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hint : rayPt p σ t₀ ∈ P.filled \ P.boundary) :
    ∀ t ∈ I, rayPt p σ t ∈ P.filled \ P.boundary := by
  zucj
  have himg : ztrfr := hI.image _ (continuous_rayPt p σ).continuousOn
  have hsub : rayPt p σ '' I ⊆ P.boundaryᶜ := by
    grind
  have hpar := parity_eq_of_isPreconnected P himg hsub (mem_image_of_mem _ ht₀) (mem_image_of_mem _ ht)
  zujfw
  rw [mem_filled_iff hP by_simp_all, ← hpar, ← mem_filled_iff hP hint.2]
  simp_all

/-- If the open ray never met the boundary it would be an unbounded connected subset of the
filled region: so the ray meets the boundary. -/
theorem hitSet_nonempty {P : Polygon} (hP : P.Simple) {p : Point} {σ : ℝ} (hσ : σ ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hint : rayPt p σ t₀ ∈ P.filled \ P.boundary) :
    (hitSet P p σ).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hIb : ∀ t ∈ Ioi (0 : ℝ), rayPt p σ t ∉ P.boundary := by
    zujbo
    have : ztrhd := ztoor
    simp_all
  have hall := rayPt_mem_interior_of_isPreconnected hP isPreconnected_Ioi hIb ht₀ hint
  obtain ⟨R, hR⟩ := filled_bounded P
  -- a far point of the ray, beyond `t₀`, leaves the square of radius `R`
  obtain ⟨s, hs0, hRs⟩ := exists_abs_add_mul_gt hσ (p.1 + σ * t₀) R
  have hs : t₀ + s ∈ Ioi (0 : ℝ) := by_grind
  have h3 := (hR _ (hall _ hs).1).1
  zvogc at h3
  grind

/-- **The first hit.**  If an initial open stretch `(0, t₀)` of the ray is interior, then the
first-hit parameter is at least `t₀`, the first-hit point is on the boundary, and every point of
the ray strictly before it is interior. -/
theorem hit_of_initial {P : Polygon} (hP : P.Simple) {p : Point} {σ : ℝ} (hσ : σ ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hint : ∀ t, 0 < t → t < t₀ → rayPt p σ t ∈ P.filled \ P.boundary) :
    t₀ ≤ hitParam P p σ ∧ rayPt p σ ztlpq ∈ P.boundary ∧
      ∀ t, 0 < t → t < hitParam P p σ → rayPt p σ t ∈ P.filled \ P.boundary := by
  have hmid : rayPt p σ (t₀ / 2) ∈ P.filled \ P.boundary := by_simp_all
  have hne := hitSet_nonempty hP hσ by_simp_all hmid
  -- every hit parameter is `≥ t₀`
  have hge : ∀ t ∈ hitSet P p σ, t₀ ≤ t := by
    zucj
    zumv
    exact (hint t ht.1 zteue).2 ht.2
  have h1 : t₀ ≤ hitParam P p σ := le_csInf hne hge
  -- the hit set is the closed set `{t | t₀ ≤ t ∧ rayPt ∈ boundary}`
  have hset : hitSet P p σ = {t : ℝ | t₀ ≤ t ∧ rayPt p σ t ∈ P.boundary} := by
    zufso
    constructor
    · zuhgs
    · zuhgr
  have hclosed : IsClosed ztlpr := by
    zucju
    exact (isClosed_Ici).inter ((isClosed_boundary P).preimage (continuous_rayPt p σ))
  have h2 :=
    (hclosed.csInf_mem hne ztlps).2
  zulot
  have hIb : ∀ t ∈ Ioo (0 : ℝ) ztlpq, rayPt p σ t ∉ P.boundary := by
    zujbo
    have : ztrhd := by_grind
    exact absurd (csInf_le ztlps this) (not_le.2 ht.2)
  have hmid' : t₀ / 2 ∈ Ioo (0 : ℝ) ztlpq := by_grind
  exact fun t ht1 ht2 =>
    rayPt_mem_interior_of_isPreconnected hP isPreconnected_Ioo hIb hmid' hmid t by_grind

/-- Every boundary point of the open ray is at or after the first hit. -/
theorem hitParam_le_of_mem_boundary (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt p σ t ∈ P.boundary) : hitParam P p σ ≤ t :=
  csInf_le ztlps ztoor

/-- **Uniqueness of the first hit.**  A boundary point of the open ray with no boundary point of
the ray strictly before it is the first hit. -/
theorem hitParam_eq_of_first (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt p σ t ∈ P.boundary) (hfirst : ∀ s, 0 < s → s < t → rayPt p σ s ∉ P.boundary) :
    hitParam P p σ = t := by
  refine le_antisymm (hitParam_le_of_mem_boundary P p σ ht hmem) ztlqs
  zugg
  zumv
  exact hfirst s hs.1 zteue hs.2

/-- An interior point has an interior initial stretch on every horizontal ray. -/
theorem exists_initial_interior {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) (σ : ℝ) :
    ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → rayPt q σ t ∈ P.filled \ P.boundary := by
  have hopen : ztsbs := isOpen_filled_sdiff_boundary hP
  have hcont : ContinuousAt (rayPt q σ) 0 := (continuous_rayPt q σ).continuousAt
  have hmem : P.filled \ P.boundary ∈ 𝓝 (rayPt q σ 0) := by
    zuohc; exact hopen.mem_nhds hq
  have := hcont.preimage_mem_nhds hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
  refine ⟨ε, hε, fun t ht1 ht2 => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht1]
  omega

/-! ### The interior-point specialisations -/

/-- The parameter of the first boundary point of the horizontal ray to the right of `q`. -/
noncomputable def rightHitParam (P : Polygon) (q : Point) : ℝ := hitParam P q 1

/-- The parameter of the first boundary point of the horizontal ray to the left of `q`. -/
noncomputable def leftHitParam (P : Polygon) (q : Point) : ℝ := hitParam P q (-1)
theorem rayPt_one (t : ℝ) : rayPt q 1 t = ztkcy := by
  zugyz
theorem rayPt_neg_one (t : ℝ) : rayPt q (-1) t = ztkda := by
  zubvf

/-- The full first-hit package for the right ray from an interior point. -/
theorem rightHit_spec {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    0 < rightHitParam P q ∧ zthjm ∈ P.boundary ∧
      ∀ t, 0 ≤ t → t < rightHitParam P q → ztkcy ∈ P.filled \ P.boundary := by
  obtain ⟨t₀, ht₀, hint⟩ := exists_initial_interior hP hq 1
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP one_ne_zero ht₀ hint
  rw [rayPt_one] at h2
  refine ztiwk
  zubbd
  · have := h3 t h ht1
    rwa [rayPt_one] at this
  grind

/-- The right ray from an interior point meets the boundary at a positive parameter. -/
theorem rightHitParam_pos {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : 0 < rightHitParam P q :=
  (rightHit_spec hP hq).1

/-- The first hit point of the right ray lies on the boundary. -/
theorem rightHit_mem_boundary {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : zthjm ∈ P.boundary :=
  (rightHit_spec hP hq).2.1

/-- The half-open ray segment from `q` to its first hit is interior. -/
theorem open_ray_subset_interior {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) :
    ∀ t, 0 ≤ t → t < rightHitParam P q → ztkcy ∈ P.filled \ P.boundary :=
  (rightHit_spec hP hq).2.2

/-- The full first-hit package for the left ray from an interior point. -/
theorem leftHit_spec {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    0 < leftHitParam P q ∧ zthjn ∈ P.boundary ∧
      ∀ t, 0 ≤ t → t < leftHitParam P q → ztkda ∈ P.filled \ P.boundary := by
  obtain ⟨t₀, ht₀, hint⟩ := exists_initial_interior hP hq (-1)
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP (neg_ne_zero.2 one_ne_zero) ht₀ hint
  rw [rayPt_neg_one] at h2
  refine ztiwk
  zubbd
  · have := h3 t h ht1
    rwa [rayPt_neg_one] at this
  grind
theorem leftHitParam_pos {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : 0 < leftHitParam P q :=
  (leftHit_spec hP hq).1
theorem leftHit_mem_boundary {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : zthjn ∈ P.boundary :=
  (leftHit_spec hP hq).2.1
theorem open_left_ray_subset_interior {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) :
    ∀ t, 0 ≤ t → t < leftHitParam P q → ztkda ∈ P.filled \ P.boundary :=
  (leftHit_spec hP hq).2.2

/-! ### Comparison with the half-open scan -/
open Metric
def DirInterior (P : Polygon) (i : ℕ) (σ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt ztdn σ t ∈ P.filled \ P.boundary
variable {P : Polygon}
/-- A locally interior direction is nonzero. -/
theorem DirInterior.ne_zero {i : ℕ} {σ : ℝ} (hi : i < P.n)
    (h : DirInterior P i σ) : σ ≠ 0 := by
  zunq
  obtain ⟨t, ht⟩ := h.exists
  apply ht.2
  simp only [rayPt, zero_mul, add_zero]
  exact zteyp

/-! ### The chord -/

/-- The parameter of the far endpoint of the chord of vertex `i` in direction `σ`. -/
noncomputable def chordParam (P : Polygon) (i : ℕ) (σ : ℝ) : ℝ := hitParam P ztdn σ

/-- The far endpoint of the chord of vertex `i` in direction `σ`. -/
noncomputable def chordEnd (P : Polygon) (i : ℕ) (σ : ℝ) : Point :=
  rayPt ztdn σ zthvq

/-- The closed chord of vertex `i` in direction `σ`. -/
noncomputable def chordSet (P : Polygon) (i : ℕ) (σ : ℝ) : Set Point :=
  Chazelle.segment ztdn (chordEnd P i σ)

/-- The open chord: the chord without its two endpoints. -/
noncomputable def openChordSet (P : Polygon) (i : ℕ) (σ : ℝ) : Set Point :=
  rayPt ztdn σ '' Ioo 0 zthvq
@[simp] theorem chordEnd_fst (P : Polygon) (i : ℕ) (σ : ℝ) :
    (chordEnd P i σ).1 = (P.vtx i).1 + σ * chordParam P i σ := rfl
@[simp] theorem chordEnd_snd (P : Polygon) (i : ℕ) (σ : ℝ) : (chordEnd P i σ).2 = (P.vtx i).2 :=
  rfl

/-- **The chord exists.**  When direction `σ` at vertex `i` is locally interior: the chord
parameter is positive, the far endpoint is on the boundary, and every point of the open chord
is interior. -/
theorem chord_spec (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) :
    0 < chordParam P i σ ∧ chordEnd P i σ ∈ P.boundary ∧
      ∀ t, 0 < t → t < chordParam P i σ → rayPt ztdn σ t ∈ P.filled \ P.boundary := by
  zuvg
  zuduw
  obtain ⟨h1, h2, h3⟩ := hit_of_initial hP (h.ne_zero hi) hu ztjwo
  exact ztooy
theorem chordParam_pos (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : 0 < chordParam P i σ :=
  (chord_spec hP hi h).1
theorem chordEnd_mem_boundary (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordEnd P i σ ∈ P.boundary :=
  (chord_spec hP hi h).2.1

/-- The open chord is interior. -/
theorem openChordSet_subset_interior (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : openChordSet P i σ ⊆ P.filled \ P.boundary := by
  zupc
  exact (chord_spec hP hi h).2.2 t ht.1 ht.2

/-- The far endpoint is not the vertex. -/
theorem chordEnd_ne_vtx (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordEnd P i σ ≠ P.vtx i := by
  zudii
  have := congrArg Prod.fst heq
  zujoh
  have hσ := h.ne_zero hi
  zuesa
  simp_all

/-- **Uniqueness of the chord.**  A boundary point of the open ray with no boundary point before
it is the far endpoint of the chord. -/
theorem chordParam_eq_of_first (P : Polygon) (i : ℕ) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt ztdn σ t ∈ P.boundary)
    (hfirst : ∀ s, 0 < s → s < t → rayPt ztdn σ s ∉ P.boundary) : chordParam P i σ = t :=
  hitParam_eq_of_first P ztdn σ ht hmem hfirst

/-- The chord as the image of the closed parameter interval. -/
theorem chordSet_eq_image (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) :
    chordSet P i σ = rayPt ztdn σ '' Icc 0 zthvq := by
  zuesa
  zufj
  zudlz

  · zuly
    refine ⟨t * chordParam P i σ, ztbjy, ?_⟩
    · nlinarith
    · zuekz
  · zufmh
    refine ⟨s / chordParam P i σ, div_nonneg hs0 hpos.le, (div_le_one hpos).2 hs1, ?_⟩
    zuewq

/-- The closed chord is the open chord with its two endpoints. -/
theorem chordSet_eq_openChordSet_union (hP : P.Simple) {i : ℕ} (hi : i < P.n)
    {σ : ℝ} (h : DirInterior P i σ) :
    chordSet P i σ = openChordSet P i σ ∪ {P.vtx i, chordEnd P i σ} := by
  zuexc
  zufj
  simp only [openChordSet, mem_union, mem_image, mem_Icc, mem_Ioo, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · zubcy
    zukmj
    · zukmm
      · grind
      tauto
    · zugaw
  · zueko
    · grind
    · exact ⟨0, ⟨le_rfl, (chordParam_pos hP hi h).le⟩, by_simp_all⟩
    · exact ⟨chordParam P i σ, ⟨(chordParam_pos hP hi h).le, le_rfl⟩, rfl⟩

/-- Points of the closed chord: the endpoints or interior points. -/
theorem mem_chordSet_cases (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) {p : Point} (hp : p ∈ chordSet P i σ) :
    p = P.vtx i ∨ p = chordEnd P i σ ∨ p ∈ P.filled \ P.boundary := by
  zuhks
  zudsh
  · exact Or.inr (Or.inr (openChordSet_subset_interior hP hi h hp))
  grind

/-- The chord meets the boundary exactly in its two endpoints. -/
theorem chordSet_inter_boundary (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) :
    chordSet P i σ ∩ P.boundary = {P.vtx i, chordEnd P i σ} := by
  zufj
  zuhpt
  constructor
  · rintro ⟨hp, hb⟩
    rcases mem_chordSet_cases hP hi h hp with h1 | h1 | h1
    · simp_all
    · simp_all
    simp_all
  · zucpg
    · exact ⟨Geometry.left_mem_segment _ _, i, hi, Geometry.left_mem_segment _ _⟩
    · exact ⟨Geometry.right_mem_segment _ _, chordEnd_mem_boundary hP hi h⟩

/-! ### The right chord and the half-open scan -/

/-! ### Abstract horizontal chords and their intersections -/

/-- The closed horizontal segment at height `y` between abscissae `a` and `b`. -/
def hseg (y a b : ℝ) : Set Point := {p | p.2 = y ∧ a ≤ p.1 ∧ p.1 ≤ b}

/-- A horizontal chord of `P`: a horizontal segment `[a, b] × {y}` with `a < b`, both
endpoints on the boundary, and the open part interior. -/
structure IsHChord (P : Polygon) (y a b : ℝ) : Prop where
  lt : a < b
  left_mem : (ztdv : Point) ∈ P.boundary
  right_mem : (ztdy : Point) ∈ P.boundary
  open_int : ∀ x, a < x → x < b → ((x, y) : Point) ∈ P.filled \ P.boundary

/-- **Two horizontal chords are equal or meet only in common endpoints.** -/
theorem hchord_inter {y a b y' a' b' : ℝ} (h : IsHChord P y a b)
    (h' : IsHChord P y' a' b') {p : Point} (hp : p ∈ hseg y a b) (hp' : p ∈ hseg y' a' b') :
    ztkhk ∨
      ztxdg := by
  zuzk

  -- is `p` an endpoint of the first chord?

  · -- then `p` is on the boundary, hence not in the open part of the second chord
    have hpb : p ∈ P.boundary := by
      zuklf
      · zuiuh
        zvmwk; exact h.left_mem
      · zuiui
        zvmwk; exact h.right_mem
    right
    zujx
    · grind
    · zuct
      zudrv

      have := h'.open_int p.1 ha' hb'
      grind
  · -- `p` is in the open part of the first chord, hence interior
    zuctf

    have hint := h.open_int p.1 ha hb
    zudkl
    -- so `p` is not an endpoint of the second chord either
    have ha' : ztpll := by
      zukly
      · zubvv
      · exfalso
        apply hint.2
        rw [show p = ztfoz from Prod.ext h1.symm hpy]
        exact h'.left_mem
    have hb' : ztppj := by
      zuklz
      · zubvv
      · exfalso
        apply hint.2
        rw [show p = ztfpb from Prod.ext h1 hpy]
        exact h'.right_mem
    left
    zuknv
    · -- `a'` is not in the open part of the first chord, and `a' < p.1 < b`, so `a' ≤ a`;
      -- symmetrically `a ≤ a'`
      zudmc
      · zube

        exact (h'.open_int a hlt ztmkz).2 h.left_mem
      · zube

        exact (h.open_int a' hlt ztmky).2 h'.left_mem
    · zudmc
      · zube

        exact (h.open_int b' ztmkz hlt).2 h'.right_mem
      · zube

        exact (h'.open_int b ztmky hlt).2 h.right_mem

/-- A horizontal segment `segment a b` (with `a.2 = b.2`) is an `hseg`. -/
theorem segment_horizontal_eq_hseg {a b : Point} (hab : a.2 = b.2) :
    Chazelle.segment a b = hseg a.2 ztttk ztttb := by
  zufj
  unfold hseg Chazelle.segment
  zuwb
  constructor
  · zuly
    zubi
    zujft
    · zuiek
      · zujkv
      · zujkx
    · zuiek
      · zujkm
      · zujkj
  · zuecm
    by_cases heq : a.1 = b.1
    · zumkq
      grind
    · refine ⟨(p.1 - a.1) / ztbco, ?_, ?_, ?_⟩
      · zujeh
        · rw [min_eq_left h.le] at h1
          positivity
        · rw [max_eq_left h.le] at h2
          zuitg
      · zujeh
        · rw [max_eq_right h.le] at h2
          zubid
        · rw [min_eq_right h.le] at h1
          zujhu
      grind

/-- The chord of a vertex, as a horizontal segment between its two abscissae. -/
theorem chordSet_eq_hseg (P : Polygon) (i : ℕ) (σ : ℝ) :
    chordSet P i σ = hseg (P.vtx i).2 ztciu
      ztcit :=
  segment_horizontal_eq_hseg by_simp_all

/-- **The chord of a vertex is a horizontal chord.** -/
theorem isHChord_chord (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : DirInterior P i σ) :
    IsHChord P (P.vtx i).2 ztciu
      ztcit := by
  obtain ⟨hpos, hend, hint⟩ := chord_spec hP hi h
  have hv : ((P.vtx i).1, (P.vtx i).2) = P.vtx i := rfl
  have he : ((chordEnd P i σ).1, (P.vtx i).2) = chordEnd P i σ := rfl
  have hvb : P.vtx i ∈ P.boundary := zteyp
  zur
  · have hlt : (P.vtx i).1 < (chordEnd P i 1).1 := by_simp_all
    zugwk

    have := hint (x - (P.vtx i).1) by_linarith ztisb
    zufps

  · have hlt : (chordEnd P i (-1)).1 < (P.vtx i).1 := by
      simp_all
    zugwl

    have := hint ((P.vtx i).1 - x) by_linarith
      ztisa
    zuenr

/-- The endpoints of `chordSet`, seen through `hseg`. -/
theorem hseg_endpoints_eq (P : Polygon) (i : ℕ) (σ : ℝ) :
    ({(ztciu, (P.vtx i).2),
        (ztcit, (P.vtx i).2)} : Set Point) =
      {P.vtx i, chordEnd P i σ} := by
  rcases le_total (P.vtx i).1 (chordEnd P i σ).1 with h | h
  · zunxx
    rfl
  · rw [min_eq_right h, max_eq_left h, Set.pair_comm]
    rfl

/-- **Chord intersection.**  Two vertex chords (in locally interior directions) are equal as
sets, or every common point is an endpoint of both. -/
theorem chordSet_inter (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) (hiσ : DirInterior P i σ)
    (hjτ : DirInterior P j τ) {p : Point} (hp : p ∈ chordSet P i σ ∩ chordSet P j τ) :
    chordSet P i σ = chordSet P j τ ∨
      (p ∈ ({P.vtx i, chordEnd P i σ} : Set Point) ∧
        p ∈ ({P.vtx j, chordEnd P j τ} : Set Point)) := by
  zuict
  rw [chordSet_eq_hseg] at hp1 hp2
  rcases hchord_inter (isHChord_chord hP hi hσ hiσ) (isHChord_chord hP hj hτ hjτ) hp1 hp2 with
    ⟨hy, ha, hb⟩ | ⟨h1, h2⟩
  · left
    rw [chordSet_eq_hseg, chordSet_eq_hseg, hy, ha, hb]
  · right
    rw [← hseg_endpoints_eq P i σ, ← hseg_endpoints_eq P j τ]
    grind

/-- **Chord disjointness.**  Two distinct vertex chords meet only in points that are endpoints
of both. -/
theorem chord_inter (hP : P.Simple) {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) (hiσ : DirInterior P i σ)
    (hjτ : DirInterior P j τ) (hne : chordSet P i σ ≠ chordSet P j τ) :
    chordSet P i σ ∩ chordSet P j τ ⊆
      ({P.vtx i, chordEnd P i σ} : Set Point) ∩ {P.vtx j, chordEnd P j τ} := by
  zuda
  rcases chordSet_inter hP hi hj hσ hτ hiσ hjτ hp with h | h
  · simp_all
  simp_all

/-! ### The set of all chords -/

/-- The set of all vertex chords of `P` (in locally interior directions). -/
def chords (P : Polygon) : Set ztf :=
  {S | ∃ i σ, i < P.n ∧ ztdd ∧ DirInterior P i σ ∧ S = chordSet P i σ}
theorem chords_subset_image (P : Polygon) :
    chords P ⊆ (fun x : ℕ × ℝ => chordSet P x.1 x.2) ''
      ztbxm := by
  rintro S ⟨i, σ, hi, hσ, -, rfl⟩
  refine ⟨(i, σ), ztbjy, rfl⟩
  simp_all
theorem chords_finite (P : Polygon) : (chords P).Finite :=
  ((Finset.range P.n).finite_toSet.prod by_simp_all).image _
    |>.subset (chords_subset_image P)

/-- **At most `2 n` chords.** -/
theorem chords_ncard_le (P : Polygon) : (chords P).ncard ≤ 2 * P.n := by
  have hfin : ((↑ztmba : Set ℕ) ×ˢ ({1, -1} : Set ℝ)).Finite :=
    (Finset.range P.n).finite_toSet.prod by_simp_all
  calc (chords P).ncard
      ≤ ((fun x : ℕ × ℝ => chordSet P x.1 x.2) ''
          ztbxm).ncard :=
        ncard_le_ncard (chords_subset_image P) ztjxu
    _ ≤ ((↑ztmba : Set ℕ) ×ˢ ({1, -1} : Set ℝ)).ncard := ncard_image_le hfin
    _ = 2 * P.n := by
        rw [ncard_prod, ncard_coe_finset, Finset.card_range, ncard_pair by_norm_num, mul_comm]

/-- Every chord is a closed segment with boundary endpoints and interior open part. -/
theorem chords_spec (hP : P.Simple) {S : Set Point} (hS : S ∈ chords P) :
    ∃ i σ, i < P.n ∧ ztdd ∧ DirInterior P i σ ∧ S = chordSet P i σ ∧
      IsHChord P (P.vtx i).2 ztciu
        ztcit := by
  obtain ⟨i, σ, hi, hσ, h, rfl⟩ := hS
  exact ⟨i, σ, hi, hσ, h, rfl, isHChord_chord hP hi hσ h⟩

/-- Every chord is closed. -/
theorem chords_isClosed {S : Set Point} (hS : S ∈ chords P) : IsClosed S := by
  obtain ⟨i, σ, -, -, -, rfl⟩ := hS
  exact Geometry.isClosed_segment _ _
def chordUnion (P : Polygon) : Set Point := ⋃₀ chords P

/-- The free interior: the interior region minus all chords. -/
def freeRegion (P : Polygon) : Set Point := zthbx \ chordUnion P

/-- The regions of the visibility map: the connected components of the free interior. -/
def regions (P : Polygon) : Set ztf :=
  {C | ∃ z ∈ freeRegion P, C = connectedComponentIn ztesb z}

/-- The union of the chords is closed (finitely many closed segments). -/
theorem isClosed_chordUnion (P : Polygon) : IsClosed (chordUnion P) :=
  (chords_finite P).isClosed_sUnion fun _ hS => chords_isClosed hS
variable {P : Polygon}
/-- Every chord lies in the filled region. -/
theorem chordSet_subset_filled (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordSet P i σ ⊆ P.filled := by
  zuda
  rcases mem_chordSet_cases hP hi h hp with rfl | rfl | hint
  · exact boundary_subset_filled P zteyp
  · exact boundary_subset_filled P ztlma
  simp_all

/-- The free interior is open. -/
theorem isOpen_freeRegion (hP : P.Simple) : IsOpen ztesb :=
  (isOpen_filled_sdiff_boundary hP).sdiff (isClosed_chordUnion P)

/-- Every region lies in the free interior. -/
theorem regions_subset {C : Set Point} (hC : C ∈ regions P) : C ⊆ freeRegion P := by
  zugqy
  zuitc

/-- Two regions are equal or disjoint. -/
theorem regions_eq_or_disjoint {C D : Set Point} (hC : C ∈ regions P)
    (hD : D ∈ regions P) : C = D ∨ Disjoint C D := by
  zugqy
  obtain ⟨w, -, rfl⟩ := hD
  by_cases h : Disjoint (connectedComponentIn ztesb z)
      (connectedComponentIn ztesb w)
  · simp_all
  · left
    obtain ⟨p, hpz, hpw⟩ := not_disjoint_iff.1 h
    rw [connectedComponentIn_eq hpz, connectedComponentIn_eq hpw]
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment continuous_lerp)

/-! ### Lines as graphs over the height -/

/-- The abscissa of the point at height `y` on the line through `u` and `w` (meaningful when
`u.2 ≠ w.2`). -/
noncomputable def xAt (u w : Point) (y : ℝ) : ℝ := u.1 + ztuem * (ztor / ztpj)
theorem xAt_left (u w : Point) : xAt u w u.2 = u.1 := by zuoew
variable {u w : Point} {P : Polygon} {i : ℕ} {q : Point}
theorem xAt_right (h : u.2 ≠ w.2) : xAt u w w.2 = w.1 := by
  zudhy
  zulve
  grind
theorem xAt_lerp (h : u.2 ≠ w.2) (t : ℝ) :
    xAt u w (lerp u w t).2 = (lerp u w t).1 := by
  zudhy
  zulve
  zujon
  grind

/-- `xAt u w` is affine. -/
theorem xAt_combo (u w : Point) {s t : ℝ} (hst : s + t = 1) (y y' : ℝ) :
    xAt u w ztohh = s * xAt u w y + t * xAt u w y' := by
  zulve
  grind
theorem continuous_xAt (u w : Point) : Continuous (xAt u w) := by
  unfold xAt; fun_prop

/-- Membership in a non-horizontal segment: the height is between the endpoint heights and the
abscissa is the one of the line. -/
theorem mem_segment_iff_xAt (h : u.2 ≠ w.2) {p : Point} :
    p ∈ Chazelle.segment u w ↔
      (min u.2 w.2 ≤ p.2 ∧ p.2 ≤ max u.2 w.2) ∧ p.1 = xAt u w p.2 := by
  zudhy
  constructor
  · zuly
    refine ztwub
    · zubvt
      zujk
      · simp_all
      · zujkz
    · zubvt
      zujk
      · zujko
      · zujkl
    · exact (xAt_lerp h t).symm
  · zugtl
    refine ⟨ztkcb / ztpj, ?_, ?_, ?_⟩
    · zujk
      · zujkw
        positivity
      · zujkk
        zuitg
    · zujk
      · zujkn
        zubid
      · zujky
        zujhu
    · zujle
      zubvt
      constructor
      · zuhmc
      simp_all

/-- Membership in the open part of a non-horizontal segment. -/
theorem openSegment_iff_xAt (h : u.2 ≠ w.2) {p : Point} :
    (∃ t ∈ Ioo (0 : ℝ) 1, p = lerp u w t) ↔
      (min u.2 w.2 < p.2 ∧ p.2 < max u.2 w.2) ∧ p.1 = xAt u w p.2 := by
  zudhy
  constructor
  · zubcy
    refine ⟨ztcp, (xAt_lerp h t).symm⟩
    · zubzv
      zujk
      · simp_all
      · zujkz
    · zubzv
      zujk
      · zujko
      · zujkl
  · zugtl
    refine ⟨ztkcb / ztpj, ztcp, ?_⟩
    · zujk
      · zujkw
        simp_all
      · zujkk
        exact div_pos_of_neg_of_neg by_linarith by_linarith
    · zujk
      · zujkn
        zubie
      · zujky
        zuosm; linarith
    · zujle
      zujon
      constructor
      · zuhmc
      simp_all

/-! ### Edges of a polygon as graphs -/

/-- The abscissa of edge `i` (extended to a line) at height `y`. -/
noncomputable def edgeX (P : Polygon) (i : ℕ) (y : ℝ) : ℝ := xAt ztdn ztwir y

/-- The lower height of edge `i`. -/
def edgeBot (P : Polygon) (i : ℕ) : ℝ := min (P.vtx i).2 (P.vtx ztwjy).2

/-- The upper height of edge `i`. -/
def edgeTop (P : Polygon) (i : ℕ) : ℝ := max (P.vtx i).2 (P.vtx ztwjy).2

/-- Edge `i` is not horizontal. -/
def NonHoriz (P : Polygon) (i : ℕ) : Prop := (P.vtx i).2 ≠ (P.vtx ztwjy).2

/-- `p` lies on the open part of edge `i`. -/
def OpenEdgePt (P : Polygon) (i : ℕ) (p : Point) : Prop :=
  ∃ t ∈ Ioo (0 : ℝ) 1, p = lerp ztdn ztwir t
theorem continuous_edgeX (P : Polygon) (i : ℕ) : Continuous (edgeX P i) := continuous_xAt _ _
theorem edgeX_combo (P : Polygon) (i : ℕ) {s t : ℝ} (hst : s + t = 1) (y y' : ℝ) :
    edgeX P i ztohh = s * edgeX P i y + t * edgeX P i y' :=
  xAt_combo _ _ hst y y'

/-- Membership in a non-horizontal edge. -/
theorem mem_edge_iff_edgeX (h : NonHoriz P i) {p : Point} :
    p ∈ P.edge i ↔ (edgeBot P i ≤ p.2 ∧ p.2 ≤ edgeTop P i) ∧ p.1 = edgeX P i p.2 :=
  mem_segment_iff_xAt h

/-- Membership in the open part of a non-horizontal edge. -/
theorem openEdgePt_iff_edgeX (h : NonHoriz P i) {p : Point} :
    OpenEdgePt P i p ↔ (edgeBot P i < p.2 ∧ p.2 < edgeTop P i) ∧ p.1 = edgeX P i p.2 :=
  openSegment_iff_xAt h
theorem OpenEdgePt.mem_edge {p : Point} (h : OpenEdgePt P i p) :
    p ∈ P.edge i := by
  zubpj
  exact lerp_mem_segment _ _ ht.1.le ht.2.le
theorem OpenEdgePt.mem_boundary (hi : i < P.n) {p : Point}
    (h : OpenEdgePt P i p) : p ∈ P.boundary :=
  ⟨i, hi, h.mem_edge⟩

/-- A point of the open part of edge `i` lies on no other edge. -/
theorem OpenEdgePt.not_mem_other (hP : P.Simple) {i : ℕ} (hi : i < P.n) {p : Point}
    (h : OpenEdgePt P i p) {k : ℕ} (hk : k < P.n) (hki : k ≠ i) : p ∉ P.edge k := by
  zubpj
  exact simple_openEdge_not_mem_other hP hi ht hk hki

/-- A point of the open part of an edge is not a vertex. -/
theorem OpenEdgePt.ne_vtx (hP : P.Simple) {i : ℕ} (hi : i < P.n) {p : Point}
    (h : OpenEdgePt P i p) {k : ℕ} (hk : k < P.n) : p ≠ P.vtx k := by
  zubpj
  exact simple_openEdge_ne_vtx hP hi ht hk

/-- The top endpoint of a non-horizontal edge is a vertex on the line of the edge. -/
theorem exists_vtx_edgeTop (hi : i < P.n) (h : NonHoriz P i) :
    ∃ k, k < P.n ∧ (P.vtx k).2 = edgeTop P i ∧ (P.vtx k).1 = edgeX P i (edgeTop P i) := by
  unfold edgeTop edgeX
  zujk
  · refine ztxzr
    · grind
    · rw [max_eq_right hlt.le, xAt_right h]
  · zumkr
    · grind
    · rw [max_eq_left hgt.le, xAt_left]

/-- The bottom endpoint of a non-horizontal edge is a vertex on the line of the edge. -/
theorem exists_vtx_edgeBot (hi : i < P.n) (h : NonHoriz P i) :
    ∃ k, k < P.n ∧ (P.vtx k).2 = edgeBot P i ∧ (P.vtx k).1 = edgeX P i (edgeBot P i) := by
  unfold edgeBot edgeX
  zujk
  · zumkr
    · grind
    · rw [min_eq_left hlt.le, xAt_left]
  · refine ztxzr
    · grind
    · rw [min_eq_right hgt.le, xAt_right h]

/-! ### The horizontal segment of a free point -/

/-- The first boundary point to the left of `q` on its horizontal line. -/
noncomputable def leftEnd (P : Polygon) (q : Point) : Point := zthjn

/-- The first boundary point to the right of `q` on its horizontal line. -/
noncomputable def rightEnd (P : Polygon) (q : Point) : Point := zthjm
@[simp] theorem leftEnd_fst (P : Polygon) (q : Point) : (leftEnd P q).1 = q.1 - leftHitParam P q :=
  rfl
@[simp] theorem leftEnd_snd (P : Polygon) (q : Point) : (leftEnd P q).2 = q.2 := rfl
@[simp] theorem rightEnd_fst (P : Polygon) (q : Point) :
    (rightEnd P q).1 = q.1 + rightHitParam P q := rfl
@[simp] theorem rightEnd_snd (P : Polygon) (q : Point) : (rightEnd P q).2 = q.2 := rfl
theorem leftEnd_fst_lt (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    (leftEnd P q).1 < q.1 := by
  rw [leftEnd_fst]; linarith [leftHitParam_pos hP hq]
theorem lt_rightEnd_fst (hP : P.Simple) {q : Point} (hq : q ∈ P.filled \ P.boundary) :
    q.1 < (rightEnd P q).1 := by
  rw [rightEnd_fst]; linarith [rightHitParam_pos hP hq]
theorem leftEnd_mem_boundary (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : leftEnd P q ∈ P.boundary :=
  leftHit_mem_boundary hP hq
theorem rightEnd_mem_boundary (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) : rightEnd P q ∈ P.boundary :=
  rightHit_mem_boundary hP hq

/-- A point of the horizontal line through `q` strictly between the two first hits is interior. -/
theorem mem_interior_of_between (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {p : Point} (hy : p.2 = q.2) (h1 : (leftEnd P q).1 < p.1)
    (h2 : p.1 < (rightEnd P q).1) : p ∈ P.filled \ P.boundary := by
  zufnx

  rcases le_or_gt q.1 p.1 with h | h
  · have := open_ray_subset_interior hP hq (p.1 - q.1) by_linarith by_linarith
    grind
  · have := open_left_ray_subset_interior hP hq zttxa by_linarith by_linarith
    grind

/-- The closed horizontal segment meets the boundary only in its two endpoints. -/
theorem closedHSeg_inter_boundary (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {p : Point} (hy : p.2 = q.2) (h1 : (leftEnd P q).1 ≤ p.1)
    (h2 : p.1 ≤ (rightEnd P q).1) (hp : p ∈ P.boundary) : p = leftEnd P q ∨ p = rightEnd P q := by
  zuff
  · zudt
    · exact absurd hp (mem_interior_of_between hP hq hy h1 h2).2
    · exact Or.inr (point_ext h2 hy)
  · exact Or.inl (point_ext h1.symm hy)

/-! ### Chords emitted towards interior points -/

/-- If the open horizontal stretch from vertex `i` in direction `σ` up to parameter `s` is
interior, the point at parameter `s` lies on the chord of `i` in direction `σ`. -/
theorem rayPt_mem_chordUnion (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hs : 0 < s)
    (hint : ∀ t, 0 < t → t < s → rayPt ztdn σ t ∈ P.filled \ P.boundary) :
    rayPt ztdn σ s ∈ chordUnion P := by
  have hdir : DirInterior P i σ := by
    zultr
    filter_upwards [Ioo_mem_nhdsGT hs] with t ht
    simp_all
  zubat
  have hle : s ≤ chordParam P i σ := (hit_of_initial hP hσ0 hs hint).1
  refine ⟨chordSet P i σ, zteyq, ?_⟩
  rw [chordSet_eq_image hP hi hdir]
  grind

/-- **The right endpoint of the horizontal segment of a free point is not a vertex.** -/
theorem rightEnd_ne_vtx (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) {k : ℕ}
    (hk : k < P.n) : rightEnd P q ≠ P.vtx k := by
  zudii
  zumep
  have hR := rightHitParam_pos hP hq'
  apply hq.2
  have e : ∀ t, rayPt ztjr (-1) t = (q.1 + (rightHitParam P q - t), q.2) := by
    zujbn
    zucqi
    zulzm
  have hmem := rayPt_mem_chordUnion hP hk ztbt hR (fun t ht1 ht2 => by
    zui
    exact open_ray_subset_interior hP hq' _ by_linarith by_linarith)
  simp_all

/-- **The left endpoint of the horizontal segment of a free point is not a vertex.** -/
theorem leftEnd_ne_vtx (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) {k : ℕ}
    (hk : k < P.n) : leftEnd P q ≠ P.vtx k := by
  zudii
  zumep
  have hL := leftHitParam_pos hP hq'
  apply hq.2
  have e : ∀ t, rayPt ztjr 1 t = (q.1 - (leftHitParam P q - t), q.2) := by
    zujbn
    zucqi
    zulzm
  have hmem := rayPt_mem_chordUnion hP hk ztp hL (fun t ht1 ht2 => by
    zui
    exact open_left_ray_subset_interior hP hq' _ by_linarith by_linarith)
  simp_all

/-- **No vertex on the closed horizontal segment of a free point.** -/
theorem not_vtx_mem_closedHSeg (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P)
    {k : ℕ} (hk : k < P.n) (hy : (P.vtx k).2 = q.2) (h1 : (leftEnd P q).1 ≤ (P.vtx k).1)
    (h2 : (P.vtx k).1 ≤ (rightEnd P q).1) : False := by
  have hb : P.vtx k ∈ P.boundary := ⟨k, hk, Geometry.left_mem_segment _ _⟩
  rcases closedHSeg_inter_boundary hP hq.1 hy h1 h2 hb with h | h
  · exact leftEnd_ne_vtx hP hq hk h.symm
  · exact rightEnd_ne_vtx hP hq hk h.symm

/-! ### The endpoints lie on open non-horizontal edges -/

/-- A horizontal edge at the height of an interior point `q` cannot contain, in its open part,
a first hit of the horizontal ray from `q`: it would contain `q` or an interior point. -/
theorem nonHoriz_of_openEdgePt_end (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {j : ℕ} (hj : j < P.n) {p : Point} (hp : OpenEdgePt P j p)
    (hpy : p.2 = q.2) (h1 : (leftEnd P q).1 ≤ p.1) (h2 : p.1 ≤ (rightEnd P q).1) :
    NonHoriz P j := by
  zujba
  zuenf

  obtain ⟨t, ht, hpt⟩ := hp
  have huw := simple_vtx_succ_ne hP hj
  have huw1 : u.1 ≠ w.1 := by_grind
  have hedge : P.edge j = hseg u.2 (min u.1 w.1) (max u.1 w.1) := segment_horizontal_eq_hseg hh
  have hpu : p.2 = u.2 := by_simp_all
  have hqu := hpy.symm.trans hpu
  -- the abscissa of `p` is strictly between the endpoint abscissae
  have hp1 : p.1 = u.1 + t * ztor := by_simp_all
  have hmin : min u.1 w.1 < p.1 := by
    zujen
    · simp_all
    · rw [min_eq_right h.le, hp1]; zunrd
  have hmax : p.1 < max u.1 w.1 := by
    zujen
    · rw [max_eq_right h.le, hp1]; zunrd
    · rw [max_eq_left h.le, hp1]; zunrd
  zufnx

  by_cases hmq : min u.1 w.1 ≤ q.1
  · by_cases hqM : q.1 ≤ max u.1 w.1
    · exact hq.2 ⟨j, hj, by zuowj; tauto⟩
    · -- `q` is to the right of the edge, so `max` lies strictly inside the left ray
      have hint := open_left_ray_subset_interior hP hq (q.1 - max u.1 w.1) by_linarith
        by_linarith
      zugjc

  · have hint := open_ray_subset_interior hP hq (min u.1 w.1 - q.1) by_linarith by_linarith
    zugjc

/-- **The right endpoint lies on the open part of a non-horizontal edge.** -/
theorem exists_rightEdge (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) :
    ∃ j, j < P.n ∧ OpenEdgePt P j ztfuj ∧ NonHoriz P j := by
  obtain ⟨j, hj, t, ht, heq⟩ := exists_openEdge_of_mem_boundary P (rightEnd_mem_boundary hP hq.1)
    (fun k hk => rightEnd_ne_vtx hP hq hk)
  have hop : OpenEdgePt P j _ := ztrer
  exact ⟨j, hj, hop, nonHoriz_of_openEdgePt_end hP hq.1 hj hop rfl
    ztfyb
    le_rfl⟩

/-- **The left endpoint lies on the open part of a non-horizontal edge.** -/
theorem exists_leftEdge (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) :
    ∃ i, i < P.n ∧ OpenEdgePt P i ztfta ∧ NonHoriz P i := by
  obtain ⟨i, hi, t, ht, heq⟩ := exists_openEdge_of_mem_boundary P (leftEnd_mem_boundary hP hq.1)
    (fun k hk => leftEnd_ne_vtx hP hq hk)
  have hop : OpenEdgePt P i _ := ztrer
  exact ⟨i, hi, hop, nonHoriz_of_openEdgePt_end hP hq.1 hi hop rfl le_rfl
    ztfyb⟩

/-- The abscissa of the right endpoint is the one of its edge at height `q.2`. -/
theorem rightEnd_fst_eq_edgeX {j : ℕ} (hj : NonHoriz P j)
    (h : OpenEdgePt P j ztfuj) : (rightEnd P q).1 = edgeX P j q.2 := by
  have := ((openEdgePt_iff_edgeX hj).1 h).2
  simp_all

/-- The abscissa of the left endpoint is the one of its edge at height `q.2`. -/
theorem leftEnd_fst_eq_edgeX {i : ℕ} (hi : NonHoriz P i)
    (h : OpenEdgePt P i ztfta) : (leftEnd P q).1 = edgeX P i q.2 := by
  have := ((openEdgePt_iff_edgeX hi).1 h).2
  simp_all

/-- The two edges carrying the endpoints are distinct. -/
theorem leftEdge_ne_rightEdge (hP : P.Simple) {q : Point}
    (hq : q ∈ P.filled \ P.boundary) {i j : ℕ} (hi : NonHoriz P i) (hj : NonHoriz P j)
    (hL : OpenEdgePt P i ztfta) (hR : OpenEdgePt P j ztfuj) : i ≠ j := by
  zunq
  have h1 := leftEnd_fst_eq_edgeX hi hL
  have h2 := rightEnd_fst_eq_edgeX hj hR
  have := leftEnd_fst_lt hP hq
  have := lt_rightEnd_fst hP hq
  linarith
end
end Chazelle.Visibility
section
set_option hygiene false
local macro "zquy" : tactic => `(tactic| (refine Set.Finite.union ?_ by_simp_all
                                          refine ((Finset.range P.n).finite_toSet.image (fun k => (P.vtx k).2)).subset ?_
                                          grind))
local macro "zquz" : tactic => `(tactic| have h1 : ztlxg := isOpen_lt continuous_const continuous_snd)
local macro "zqva" : tactic => `(tactic| have h2 : ztlxf := isOpen_lt continuous_snd continuous_const)
set_option hygiene true

/-!
# Every region of the horizontal visibility map is an open trapezoid

Let `q` be a free point of a simple polygon `P` (`q ∈ freeRegion P`, see `Map.lean`), and let
`i`, `j` be the (non-horizontal) edges carrying the two endpoints `leftEnd P q`, `rightEnd P q`
of its horizontal segment (`HSeg.lean`).  The lines of these edges are the graphs
`x = edgeX P i y` and `x = edgeX P j y`.  The *corridor* between them is obstructed above `q`
at the first height `y₂ > q.2` where an endpoint of `i` or `j`, or a vertex lying in the closed
corridor, occurs; similarly `y₁ < q.2` below.  The structure `IsTrap P q i j y₁ y₂` records this
choice, and

  `trapSet P i j y₁ y₂ = {p | y₁ < p.2 < y₂ ∧ edgeX P i p.2 < p.1 < edgeX P j p.2}`

is the open trapezoid.  Main results:

* `exists_isTrap`: every free point has such data;
* `IsTrap.trapSet_subset_freeRegion`: the trapezoid is free (no boundary point: an edge meeting
  it would reach the horizontal segment of `q` or leave through a side, `segment_exit`; no chord
  point: the emitting vertex is outside the corridor, so the chord would cross a side);
* `IsTrap.closure_inter_free`: a free point of the closure of the trapezoid is in the trapezoid
  (the open top and bottom sides contain no free point, `not_free_of_side`);
* `IsTrap.region_eq`: **the region of `q` is exactly the trapezoid**;
* `regions_eq_trapSet`, `regions_convex`: every region of the visibility map is an open
  trapezoid, in particular convex;
* `IsTrap.top_side`, `IsTrap.bot_side`: the open top and bottom sides consist of boundary points
  and chord points.
-/
namespace Chazelle.Visibility
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one point_ext point_ext_iff
  lerp_mem_segment continuous_lerp)

/-! ### The trapezoid -/

/-- The open trapezoid between heights `y₁` and `y₂`, bounded on the left by the line of edge
`i` and on the right by the line of edge `j`. -/
def trapSet (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) : Set Point :=
  {p | y₁ < p.2 ∧ p.2 < y₂ ∧ edgeX P i p.2 < p.1 ∧ p.1 < edgeX P j p.2}

/-- The closed trapezoid. -/
def closedTrap (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) : Set Point :=
  {p | y₁ ≤ p.2 ∧ p.2 ≤ y₂ ∧ edgeX P i p.2 ≤ p.1 ∧ p.1 ≤ edgeX P j p.2}
theorem isOpen_trapSet (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) : IsOpen ztbku := by
  zquz
  zqva
  have h3 :=
    isOpen_lt zteiw continuous_fst
  have h4 :=
    isOpen_lt continuous_fst zteix
  have : trapSet P i j y₁ y₂ = {p : Point | y₁ < p.2} ∩ ({p : Point | p.2 < y₂} ∩
      ({p : Point | edgeX P i p.2 < p.1} ∩ {p : Point | p.1 < edgeX P j p.2})) := by
    rfl
  zubk
  zuith
theorem isClosed_closedTrap (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) :
    IsClosed (closedTrap P i j y₁ y₂) := by
  zudnf

  have h3 :=
    isClosed_le zteiw continuous_fst
  have h4 :=
    isClosed_le continuous_fst zteix
  have : closedTrap P i j y₁ y₂ = {p : Point | y₁ ≤ p.2} ∩ ({p : Point | p.2 ≤ y₂} ∩
      ({p : Point | edgeX P i p.2 ≤ p.1} ∩ {p : Point | p.1 ≤ edgeX P j p.2})) := by
    rfl
  zubk
  zuith
theorem trapSet_subset_closedTrap (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) :
    trapSet P i j y₁ y₂ ⊆ closedTrap P i j y₁ y₂ :=
  fun _ hp => ztoom
theorem closure_trapSet_subset (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) :
    closure ztbku ⊆ closedTrap P i j y₁ y₂ :=
  closure_minimal (trapSet_subset_closedTrap P i j y₁ y₂) (isClosed_closedTrap P i j y₁ y₂)

/-- Strict inequalities are preserved by convex combinations. -/
theorem combo_lt_combo {a b a' b' s s' : ℝ} (h1 : a < a') (h2 : b < b') (hs : 0 ≤ s)
    (hs' : 0 ≤ s') (h : s + s' = 1) : s * a + s' * b < s * a' + s' * b' := by
  zuevh
  · simp_all
  · zugor

/-- The open trapezoid is convex. -/
theorem convex_trapSet (P : Polygon) (i j : ℕ) (y₁ y₂ : ℝ) : Convex ℝ ztbku := by
  zubaw

  · show y₁ < (a • x + b • y).2
    zutw
    exact combo_lt hx1 hy1 ha hb hab
  · show (a • x + b • y).2 < y₂
    zutw
    exact combo_gt hx2 hy2 ha hb hab
  · show edgeX P i (a • x + b • y).2 < (a • x + b • y).1
    zubip
    rw [edgeX_combo P i hab]
    zuita
  · show (a • x + b • y).1 < edgeX P j (a • x + b • y).2
    zubip
    rw [edgeX_combo P j hab]
    zuitb

/-- A preconnected set avoiding the boundary and containing an interior point is interior. -/
theorem subset_interior_of_isPreconnected {P : Polygon} (hP : P.Simple) {S : Set Point}
    (hS : IsPreconnected S) (hSb : ∀ p ∈ S, p ∉ P.boundary) {z : Point} (hz : z ∈ S)
    (hzi : z ∈ P.filled \ P.boundary) : S ⊆ P.filled \ P.boundary := by
  zuda
  zujfw
  rw [mem_filled_iff hP by_simp_all, parity_eq_of_isPreconnected P hS by_grind hp hz,
    ← mem_filled_iff hP hzi.2]
  simp_all

/-! ### The trapezoid data of a free point -/

/-- The data describing the region of a free point `q`: the two non-horizontal edges `i`
(left) and `j` (right) carrying the endpoints of its horizontal segment, and the heights
`y₁ < q.2 < y₂` of the bottom and top sides.  The heights stay within the ranges of both edges,
no vertex lies in the closed corridor strictly between the heights, and each height carries a
vertex of the closed corridor (or an endpoint of `i` or `j`). -/
structure IsTrap (P : Polygon) (q : Point) (i j : ℕ) (y₁ y₂ : ℝ) : Prop where
  hi : i < P.n
  hj : j < P.n
  nhL : NonHoriz P i
  nhR : NonHoriz P j
  left_mem : OpenEdgePt P i ztfta
  right_mem : OpenEdgePt P j ztfuj
  bot_lt : y₁ < q.2
  lt_top : q.2 < y₂
  botL : edgeBot P i ≤ y₁
  botR : edgeBot P j ≤ y₁
  topL : y₂ ≤ edgeTop P i
  topR : y₂ ≤ edgeTop P j
  no_vertex : ∀ k, k < P.n → y₁ < (P.vtx k).2 → (P.vtx k).2 < y₂ →
    edgeX P i (P.vtx k).2 ≤ (P.vtx k).1 → (P.vtx k).1 ≤ edgeX P j (P.vtx k).2 → False
  top_vertex : ∃ k, k < P.n ∧ (P.vtx k).2 = y₂ ∧
    ztdhg
  bot_vertex : ∃ k, k < P.n ∧ (P.vtx k).2 = y₁ ∧
    ztdhf
namespace IsTrap
variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}
theorem leftEnd_eq (h : IsTrap P q i j y₁ y₂) : (leftEnd P q).1 = edgeX P i q.2 :=
  leftEnd_fst_eq_edgeX h.nhL h.left_mem
theorem rightEnd_eq (h : IsTrap P q i j y₁ y₂) : (rightEnd P q).1 = edgeX P j q.2 :=
  rightEnd_fst_eq_edgeX h.nhR h.right_mem
theorem ne (hP : P.Simple) (hq : q ∈ P.filled \ P.boundary) (h : IsTrap P q i j y₁ y₂) : i ≠ j :=
  leftEdge_ne_rightEdge hP hq h.nhL h.nhR h.left_mem h.right_mem

/-- A point on the line of edge `i` at a height of the trapezoid's range lies on edge `i`. -/
theorem mem_edgeL (h : IsTrap P q i j y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2) (h2 : p.2 ≤ y₂)
    (hx : p.1 = edgeX P i p.2) : p ∈ P.edge i :=
  (mem_edge_iff_edgeX h.nhL).2 ⟨⟨h.botL.trans h1, h2.trans h.topL⟩, hx⟩

/-- A point on the line of edge `j` at a height of the trapezoid's range lies on edge `j`. -/
theorem mem_edgeR (h : IsTrap P q i j y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2) (h2 : p.2 ≤ y₂)
    (hx : p.1 = edgeX P j p.2) : p ∈ P.edge j :=
  (mem_edge_iff_edgeX h.nhR).2 ⟨⟨h.botR.trans h1, h2.trans h.topR⟩, hx⟩
theorem q_mem (hP : P.Simple) (hq : q ∈ P.filled \ P.boundary) (h : IsTrap P q i j y₁ y₂) :
    q ∈ trapSet P i j y₁ y₂ :=
  ⟨h.bot_lt, h.lt_top, by rw [← h.leftEnd_eq]; exact leftEnd_fst_lt hP hq,
    by rw [← h.rightEnd_eq]; exact lt_rightEnd_fst hP hq⟩
end IsTrap

/-! ### Existence of the trapezoid data -/

/-- The top height: the first obstruction of the corridor above `q`. -/
theorem exists_top_height {P : Polygon} {q : Point} {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (nhL : NonHoriz P i) (nhR : NonHoriz P j) (hL : OpenEdgePt P i ztfta)
    (hR : OpenEdgePt P j ztfuj) :
    ∃ y₂, q.2 < y₂ ∧ y₂ ≤ edgeTop P i ∧ y₂ ≤ edgeTop P j ∧
      (∀ k, k < P.n → q.2 < (P.vtx k).2 → (P.vtx k).2 < y₂ →
        edgeX P i (P.vtx k).2 ≤ (P.vtx k).1 → (P.vtx k).1 ≤ edgeX P j (P.vtx k).2 → False) ∧
      (∃ k, k < P.n ∧ (P.vtx k).2 = y₂ ∧
        ztdhg) := by
  set C : Set ℝ := {y | ∃ k, k < P.n ∧ (P.vtx k).2 = y ∧ q.2 < y ∧
    edgeX P i y ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y} ∪ {edgeTop P i, edgeTop P j} with hC
  have hfin : C.Finite := by
    zquy
  zuked
  obtain ⟨y₂, hy₂C, hmin⟩ := Set.exists_min_image C id hfin hne
  have hqi : q.2 < edgeTop P i := by
    have := ((openEdgePt_iff_edgeX nhL).1 hL).1.2
    tauto
  have hqj : q.2 < edgeTop P j := by
    have := ((openEdgePt_iff_edgeX nhR).1 hR).1.2
    tauto
  have hall : ∀ y ∈ C, q.2 < y := by
    grind
  refine ⟨y₂, by_grind, by_grind, by_grind, ?_, ?_⟩
  · grind
  · rcases hy₂C with ⟨k, hk, hky, -, h3, h4⟩ | h
    · grind
    · zugp

      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeTop hi nhL
        grind
      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeTop hj nhR
        grind

/-- The bottom height: the first obstruction of the corridor below `q`. -/
theorem exists_bot_height {P : Polygon} {q : Point} {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (nhL : NonHoriz P i) (nhR : NonHoriz P j) (hL : OpenEdgePt P i ztfta)
    (hR : OpenEdgePt P j ztfuj) :
    ∃ y₁, y₁ < q.2 ∧ edgeBot P i ≤ y₁ ∧ edgeBot P j ≤ y₁ ∧
      (∀ k, k < P.n → y₁ < (P.vtx k).2 → (P.vtx k).2 < q.2 →
        edgeX P i (P.vtx k).2 ≤ (P.vtx k).1 → (P.vtx k).1 ≤ edgeX P j (P.vtx k).2 → False) ∧
      (∃ k, k < P.n ∧ (P.vtx k).2 = y₁ ∧
        ztdhf) := by
  set C : Set ℝ := {y | ∃ k, k < P.n ∧ (P.vtx k).2 = y ∧ y < q.2 ∧
    edgeX P i y ≤ (P.vtx k).1 ∧ (P.vtx k).1 ≤ edgeX P j y} ∪ {edgeBot P i, edgeBot P j} with hC
  have hfin : C.Finite := by
    zquy
  zuked
  obtain ⟨y₁, hy₁C, hmax⟩ := Set.exists_max_image C id hfin hne
  have hqi : edgeBot P i < q.2 := by
    have := ((openEdgePt_iff_edgeX nhL).1 hL).1.1
    tauto
  have hqj : edgeBot P j < q.2 := by
    have := ((openEdgePt_iff_edgeX nhR).1 hR).1.1
    tauto
  have hall : ∀ y ∈ C, y < q.2 := by
    grind
  refine ⟨y₁, by_grind, by_grind, by_grind, ?_, ?_⟩
  · grind
  · rcases hy₁C with ⟨k, hk, hky, -, h3, h4⟩ | h
    · grind
    · zugp

      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeBot hi nhL
        grind
      · obtain ⟨k, hk, hky, hkx⟩ := exists_vtx_edgeBot hj nhR
        grind

/-- **Every free point has trapezoid data.** -/
theorem exists_isTrap {P : Polygon} (hP : P.Simple) {q : Point} (hq : q ∈ freeRegion P) :
    ∃ i j y₁ y₂, IsTrap P q i j y₁ y₂ := by
  obtain ⟨i, hi, hL, nhL⟩ := exists_leftEdge hP hq
  obtain ⟨j, hj, hR, nhR⟩ := exists_rightEdge hP hq
  obtain ⟨y₂, hq2, htopL, htopR, hnoT, htopV⟩ := exists_top_height hi hj nhL nhR hL hR
  obtain ⟨y₁, hq1, hbotL, hbotR, hnoB, hbotV⟩ := exists_bot_height hi hj nhL nhR hL hR
  refine ⟨i, j, y₁, y₂, ⟨hi, hj, nhL, nhR, hL, hR, hq1, hq2, hbotL, hbotR, htopL, htopR, ?_, htopV,
    hbotV⟩⟩
  intro k hk h1 h2 h3 h4
  rcases lt_trichotomy (P.vtx k).2 q.2 with hlt | heq | hgt
  · grind
  · rw [heq, ← leftEnd_fst_eq_edgeX nhL hL] at h3
    rw [heq, ← rightEnd_fst_eq_edgeX nhR hR] at h4
    exact not_vtx_mem_closedHSeg hP hq hk heq h3 h4
  grind

/-! ### Leaving an open convex set along a segment -/

/-- **Segment exit.**  A segment `lerp u w` through a point of an open convex set `T` meets `T`
in a parameter interval `(s₁, s₂)`; the points at `s₁`, `s₂` are in the closure of `T`, and each
is an endpoint of the segment or lies outside `T`. -/
theorem segment_exit {T : Set Point} (hT : IsOpen T) (hc : Convex ℝ T) (u w : Point) {s₀ : ℝ}
    (h0 : 0 ≤ s₀) (h1 : s₀ ≤ 1) (hs₀ : lerp u w s₀ ∈ T) :
    ∃ s₁ s₂, 0 ≤ s₁ ∧ s₁ ≤ s₀ ∧ s₀ ≤ s₂ ∧ s₂ ≤ 1 ∧
      (∀ s, s₁ < s → s < s₂ → lerp u w s ∈ T) ∧
      lerp u w s₁ ∈ closure T ∧ lerp u w s₂ ∈ closure T ∧
      (s₁ = 0 ∨ lerp u w s₁ ∉ T) ∧ (s₂ = 1 ∨ lerp u w s₂ ∉ T) := by
  set S : Set ℝ := {s | 0 ≤ s ∧ s ≤ 1 ∧ lerp u w s ∈ T} with hS
  have hs₀S : s₀ ∈ S := by_simp_all
  have hSne : S.Nonempty := ⟨s₀, hs₀S⟩
  have hbb : BddBelow S := ztoli
  have hba : BddAbove S := ⟨1, fun s hs => hs.2.1⟩
  have hSconv : Convex ℝ S := by
    intro s hs s' hs' a b ha hb hab
    have hb' : b = 1 - a := by_linarith
    subst hb'
    zusk
    · show 0 ≤ a * s + ztjed * s'
      nlinarith [mul_nonneg ha hs.1, mul_nonneg hb hs'.1]
    · show a * s + ztjed * s' ≤ 1
      nlinarith [mul_le_mul_of_nonneg_left hs.2.1 ha, mul_le_mul_of_nonneg_left hs'.2.1 hb]
    · show lerp u w _ ∈ T
      have e : lerp u w (a • s + ztjed • s') = a • lerp u w s + ztjed • lerp u w s' := by
        zujle
        simp only [smul_eq_mul, lerp_fst, lerp_snd, Geometry.add_fst, Geometry.add_snd,
          Geometry.smul_fst, Geometry.smul_snd]
        grind
      zui
      exact hc hs.2.2 hs'.2.2 ha hb hab
  have hord := hSconv.ordConnected
  have hcont : Continuous _ := continuous_lerp u w
  refine ⟨sInf S, sSup S, le_csInf hSne by_simp_all, csInf_le hbb hs₀S, le_csSup hba hs₀S,
    csSup_le hSne by_simp_all, ?_, ?_, ?_, ?_, ?_⟩
  · zumhk
    obtain ⟨a, haS, has⟩ := exists_lt_of_csInf_lt hSne hs1
    obtain ⟨b, hbS, hsb⟩ := exists_lt_of_lt_csSup hSne hs2
    exact (hord.out haS hbS by_grind).2.2
  · rcases (csInf_le hbb hs₀S).lt_or_eq with hlt | heq
    · refine mem_closure_of_tendsto (b := 𝓝[>] ztwdb)
        ztosu ?_
      filter_upwards [Ioo_mem_nhdsGT hlt] with s hs
      obtain ⟨a, haS, has⟩ := exists_lt_of_csInf_lt hSne hs.1
      exact (hord.out haS hs₀S by_grind).2.2
    · zvnbk; exact subset_closure hs₀
  · rcases (le_csSup hba hs₀S).lt_or_eq with hlt | heq
    · refine mem_closure_of_tendsto (b := 𝓝[<] (sSup S))
        ztosu ?_
      filter_upwards [Ioo_mem_nhdsLT hlt] with s hs
      obtain ⟨b, hbS, hsb⟩ := exists_lt_of_lt_csSup hSne hs.2
      exact (hord.out hs₀S hbS by_grind).2.2
    · zvnbo; exact subset_closure hs₀
  · zubqk
    zuilu
    obtain ⟨hne0, hmem⟩ := hcon
    have hpos := lt_of_le_of_ne (le_csInf hSne by_simp_all) (Ne.symm hne0)
    have hev : ∀ᶠ s in 𝓝 _, lerp u w s ∈ T :=
      hcont.continuousAt.preimage_mem_nhds ztvue
    obtain ⟨s, hsT, hs⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hpos)).exists
    have hsS : s ∈ S := ⟨hs.1.le, (hs.2.le.trans (csInf_le hbb hs₀S)).trans h1, hsT⟩
    exact absurd (csInf_le hbb hsS) (not_le.2 hs.2)
  · zubqk
    zuilu
    obtain ⟨hne1, hmem⟩ := hcon
    have hlt1 := lt_of_le_of_ne (csSup_le hSne by_simp_all) hne1
    have hev : ∀ᶠ s in 𝓝 _, lerp u w s ∈ T :=
      hcont.continuousAt.preimage_mem_nhds ztvue
    obtain ⟨s, hsT, hs⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hlt1)).exists
    have hsS : s ∈ S := ⟨h0.trans ((le_csSup hba hs₀S).trans hs.1.le), hs.2.le, hsT⟩
    exact absurd (le_csSup hba hsS) (not_le.2 hs.1)

/-! ### The trapezoid is free -/
namespace IsTrap
variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}

/-- No point of an edge other than `i`, `j` lies in the closed trapezoid at the height of `q`. -/
theorem no_edge_at_base (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂)
    {k : ℕ} (hk : k < P.n) (hki : k ≠ i) (hkj : k ≠ j) {z : Point} (hz : z ∈ P.edge k)
    (hzc : z ∈ closedTrap P i j y₁ y₂) (hzy : z.2 = q.2) : False := by
  obtain ⟨-, -, h3, h4⟩ := hzc
  rw [hzy, ← h.leftEnd_eq] at h3
  rw [hzy, ← h.rightEnd_eq] at h4
  rcases closedHSeg_inter_boundary hP hq.1 hzy h3 h4 ⟨k, hk, hz⟩ with e | e
  · zukre
    exact h.left_mem.not_mem_other hP h.hi hk hki hz
  · zukre
    exact h.right_mem.not_mem_other hP h.hj hk hkj hz

/-- No point of an edge other than `i`, `j` lies in the closed trapezoid strictly between the
two heights if it is a vertex or outside the open trapezoid. -/
theorem no_band_point (hP : P.Simple) (h : IsTrap P q i j y₁ y₂) {k : ℕ} (hk : k < P.n)
    (hki : k ≠ i) (hkj : k ≠ j) {x : Point} (hx : x ∈ P.edge k)
    (hxc : x ∈ closedTrap P i j y₁ y₂) (h1 : y₁ < x.2) (h2 : x.2 < y₂)
    (hv : x = P.vtx k ∨ x = P.vtx ztwtz ∨ x ∉ trapSet P i j y₁ y₂) : False := by
  obtain ⟨-, -, h3, h4⟩ := hxc
  have hvert : ∃ m, m < P.n ∧ x = P.vtx m := by
    rcases hv with hv | hv | hv
    · grind
    · exact ⟨zts % P.n, succIdx_lt P hk, hv⟩
    · have hor : x.1 = edgeX P i x.2 ∨ x.1 = edgeX P j x.2 := by
        zuct
        rw [not_or] at hne
        exact hv ⟨h1, h2, by_grind, by_grind⟩
      rcases hor with hor | hor
      · rcases simple_endpoint_of_mem_two hP hk h.hi hki hx (h.mem_edgeL h1.le h2.le hor) with e | e
        · grind
        · exact ztomi
      · rcases simple_endpoint_of_mem_two hP hk h.hj hkj hx (h.mem_edgeR h1.le h2.le hor) with e | e
        · grind
        · exact ztomi
  obtain ⟨m, hm, rfl⟩ := hvert
  exact h.no_vertex m hm h1 h2 h3 h4

/-- **The trapezoid contains no boundary point.** -/
theorem not_mem_boundary (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂)
    {p : Point} (hp : p ∈ trapSet P i j y₁ y₂) : p ∉ P.boundary := by
  rintro ⟨k, hk, hpk⟩
  zufjy
  have hki : k ≠ i := by
    zunq
    have := ((mem_edge_iff_edgeX h.nhL).1 hpk).2
    linarith
  have hkj : ztska := by
    zunq
    have := ((mem_edge_iff_edgeX h.nhR).1 hpk).2
    linarith
  obtain ⟨s₀, hs0, hs1, hps⟩ := hpk
  have hps' : p = lerp ztjr ztwiw s₀ := hps
  have hpT : lerp ztjr ztwiw s₀ ∈ trapSet P i j y₁ y₂ := by
    rw [← hps']; trivial
  obtain ⟨s₁, s₂, hs₁0, hs₁, hs₂, hs₂1, hT, hc₁, hc₂, hv₁, hv₂⟩ :=
    segment_exit ztpcl (convex_trapSet P i j y₁ y₂) ztjr
      ztwiw hs0 hs1 hpT
  have hsub := closure_trapSet_subset P i j y₁ y₂
  have hx₁e : lerp ztjr ztwiw s₁ ∈ P.edge k :=
    lerp_mem_segment _ _ hs₁0 by_grind
  have hx₂e : lerp ztjr ztwiw s₂ ∈ P.edge k :=
    lerp_mem_segment _ _ (hs₁0.trans ztqqu) hs₂1
  have hx₁c := hsub hc₁
  have hx₂c := hsub hc₂
  have hv₁' : lerp ztjr ztwiw s₁ = P.vtx k ∨
      lerp ztjr ztwiw s₁ = P.vtx ztwtz ∨
      lerp ztjr ztwiw s₁ ∉ trapSet P i j y₁ y₂ := by
    rcases hv₁ with e | hv
    · simp_all
    simp_all
  have hv₂' : lerp ztjr ztwiw s₂ = P.vtx k ∨
      lerp ztjr ztwiw s₂ = P.vtx ztwtz ∨
      lerp ztjr ztwiw s₂ ∉ trapSet P i j y₁ y₂ := by
    rcases hv₂ with e | hv
    · simp_all
    simp_all
  have hcont : ContinuousOn (fun s => (lerp ztjr ztwiw s).2) (Icc s₁ s₂) :=
    (continuous_lerp _ _).snd.continuousOn
  -- the height of `p` lies between the heights of the two exit points
  have hbetween : ((lerp ztjr ztwiw s₁).2 ≤ p.2 ∧
      p.2 ≤ (lerp ztjr ztwiw s₂).2) ∨
      ((lerp ztjr ztwiw s₂).2 ≤ p.2 ∧
      p.2 ≤ (lerp ztjr ztwiw s₁).2) := by
    rw [hps']
    zubzv
    rcases le_total (P.vtx k).2 (P.vtx ztwtz).2 with hd | hd
    · left
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right hs₁ ztwfp,
        mul_le_mul_of_nonneg_right hs₂ ztwfp]
    · right
      constructor <;> nlinarith [mul_le_mul_of_nonpos_right hs₁ ztwfs,
        mul_le_mul_of_nonpos_right hs₂ ztwfs]
  -- if the height of `q` is reached, the edge meets the closed trapezoid at that height
  have hIVT : ((lerp ztjr ztwiw s₁).2 ≤ q.2 ∧
      q.2 ≤ (lerp ztjr ztwiw s₂).2) ∨
      ((lerp ztjr ztwiw s₂).2 ≤ q.2 ∧
      q.2 ≤ (lerp ztjr ztwiw s₁).2) → False := by
    intro hA
    have hex : ∃ s ∈ Icc s₁ s₂, (lerp ztjr ztwiw s).2 = q.2 := by
      rcases hA with hA | hA
      · exact intermediate_value_Icc ztqqu hcont hA
      · exact intermediate_value_Icc' ztqqu hcont hA
    obtain ⟨s, ⟨hsa, hsb⟩, hsy⟩ := hex
    have hze : lerp _ _ s ∈ P.edge k :=
      lerp_mem_segment _ _ (hs₁0.trans hsa) (hsb.trans hs₂1)
    have hzc : lerp ztjr ztwiw s ∈ closedTrap P i j y₁ y₂ := by
      rcases hsa.lt_or_eq with hlt | heq
      · rcases hsb.lt_or_eq with hlt2 | heq2
        · exact trapSet_subset_closedTrap _ _ _ _ _ (hT s hlt hlt2)
        grind
      grind
    exact h.no_edge_at_base hP hq hk hki hkj hze hzc hsy
  by_cases hA : ((lerp ztjr ztwiw s₁).2 ≤ q.2 ∧
      q.2 ≤ (lerp ztjr ztwiw s₂).2) ∨
      ((lerp ztjr ztwiw s₂).2 ≤ q.2 ∧
      q.2 ≤ (lerp ztjr ztwiw s₁).2)
  · grind
  · rw [not_or] at hA
    obtain ⟨hA1, hA2⟩ := hA
    have key : ∀ x, x ∈ P.edge k → x ∈ closedTrap P i j y₁ y₂ →
        (x = P.vtx k ∨ x = P.vtx ztwtz ∨ x ∉ trapSet P i j y₁ y₂) →
        y₁ < x.2 → x.2 < y₂ → False :=
      fun x hx hxc hv h1 h2 => h.no_band_point hP hk hki hkj hx hxc h1 h2 hv
    have hb := h.bot_lt
    have ht := h.lt_top
    rcases hbetween with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · rcases le_or_gt (lerp ztjr ztwiw s₁).2 q.2 with hx | hx
      · have : (lerp ztjr ztwiw s₂).2 < q.2 := by
          grind
        zubfo
      · zubfo
    · rcases le_or_gt (lerp _ _ s₂).2 q.2 with hx | hx
      · have : (lerp ztjr ztwiw s₁).2 < q.2 := by
          grind
        exact key _ hx₁e hx₁c hv₁' by_linarith by_linarith
      · zubfo

/-- **The trapezoid is interior.** -/
theorem trapSet_subset_interior (hP : P.Simple) (hq : q ∈ freeRegion P)
    (h : IsTrap P q i j y₁ y₂) : trapSet P i j y₁ y₂ ⊆ P.filled \ P.boundary :=
  subset_interior_of_isPreconnected hP (convex_trapSet P i j y₁ y₂).isPreconnected
    (fun _ hp => h.not_mem_boundary hP hq hp) zttls hq.1

/-- **The trapezoid is free**: it contains no chord point either. -/
theorem trapSet_subset_freeRegion (hP : P.Simple) (hq : q ∈ freeRegion P)
    (h : IsTrap P q i j y₁ y₂) : trapSet P i j y₁ y₂ ⊆ freeRegion P := by
  zuda
  refine ⟨h.trapSet_subset_interior hP hq hp, ?_⟩
  rintro ⟨S, hS, hpS⟩
  obtain ⟨m, σ, hm, hσ, hdir, rfl, hch⟩ := chords_spec hP hS
  rw [chordSet_eq_hseg] at hpS
  obtain ⟨hy, ha, hb⟩ := hpS
  zufjy
  -- the emitting vertex is at the height of `p`, outside the closed corridor
  have hnot : ¬ (edgeX P i (P.vtx m).2 ≤ (P.vtx m).1 ∧ (P.vtx m).1 ≤ edgeX P j (P.vtx m).2) :=
    fun hh => h.no_vertex m hm by_grind by_grind hh.1 hh.2
  rw [← hy, not_and_or, not_le, not_le] at hnot
  have hbL : ((edgeX P i p.2, p.2) : Point) ∈ P.boundary :=
    ⟨i, h.hi, h.mem_edgeL hp1.le hp2.le rfl⟩
  have hbR : ((edgeX P j p.2, p.2) : Point) ∈ P.boundary :=
    ⟨j, h.hj, h.mem_edgeR hp1.le hp2.le rfl⟩
  have hminle := min_le_left (P.vtx m).1 (chordEnd P m σ).1
  have hlemax := le_max_left (P.vtx m).1 (chordEnd P m σ).1
  zuklt
  · -- the vertex is the left endpoint of the chord, and the left side of the corridor is inside
    have hmin : min (P.vtx m).1 (chordEnd P m σ).1 = (P.vtx m).1 := by
      grind
    have hint := hch.open_int (edgeX P i p.2) by_grind by_linarith
    grind
  · have hmax : max (P.vtx m).1 (chordEnd P m σ).1 = (P.vtx m).1 := by
      grind
    have hint := hch.open_int (edgeX P j p.2) by_linarith by_grind
    grind
end IsTrap

/-! ### The open top and bottom sides contain no free point -/

/-- A point `e` of an open non-horizontal edge such that all nearby points on one side (`ε`) of
the horizontal line through `e` lie in an interior set `U`: impossible, since the edge itself
has points on that side near `e`. -/
theorem side_edge_false {P : Polygon} {y₀ ε : ℝ} (hε : ε = 1 ∨ ε = -1) {U : Set Point}
    (hU : U ⊆ P.filled \ P.boundary) {e : Point} (hey : e.2 = y₀)
    (hnear : ∀ᶠ p' in 𝓝 e, 0 < ε * ztkbz → p' ∈ U) {j : ℕ} (hj : j < P.n)
    (hnh : NonHoriz P j) (he : OpenEdgePt P j e) : False := by
  obtain ⟨t, ht, rfl⟩ := he
  zuenf

  have hd0 := sub_ne_zero.2 (Ne.symm hnh)
  have hε2 : ε * ε = 1 := by_grind
  have hcont : Continuous fun η : ℝ => lerp u w ztxak :=
    (continuous_lerp u w).comp ztepq
  have htend : Tendsto (fun η : ℝ => lerp u w (t + ε * (w.2 - u.2) * η)) (𝓝[>] 0)
      (𝓝 (lerp u w t)) := by
    have := hcont.tendsto 0
    zubzw
    zuhv
  zulka
  have hev2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), t + ε * ztpj * η ∈ Ioo (0 : ℝ) 1 := by
    have hc : Continuous fun η : ℝ => t + ε * ztpj * η := by fun_prop
    have : Tendsto (fun η : ℝ => t + ε * (w.2 - u.2) * η) (𝓝[>] 0) (𝓝 t) := by
      have := hc.tendsto 0
      zubzw
      zuhv
    exact this.eventually ztvxj
  obtain ⟨η, hη1, hη2, hη0⟩ := (hev1.and ztqpz).exists
  have hη0' := hη0
  have hpos : 0 < ε * ((lerp u w ztxak).2 - y₀) := by
    rw [← hey]
    zubzv
    have : ε * ((u.2 + ztxak * ztpj) - (u.2 + t * ztpj)) =
        (ε * ε) * (ztpj * ztpj) * η := by_ring
    rw [this, hε2, one_mul]
    exact mul_pos ztvzh hη0'
  have hmem := hU (hη1 hpos)
  exact hmem.2 ⟨j, hj, lerp_mem_segment _ _ hη2.1.le hη2.2.le⟩

/-- **Side lemma.**  Let `(a, b) × {y₀}` be an open horizontal side of an interior set `U`, in
the sense that near every point of the side, all points on the side `ε` of the line are in `U`,
and let some vertex lie on the closed side.  Then no point of the open side is free. -/
theorem not_free_of_side {P : Polygon} (hP : P.Simple) {y₀ a b ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {U : Set Point} (hU : U ⊆ P.filled \ P.boundary)
    (hnear : ∀ x, a < x → x < b →
      ∀ᶠ p' in 𝓝 (ztcoo : Point), 0 < ε * ztkbz → p' ∈ U)
    {m : ℕ} (hm : m < P.n) (hmy : (P.vtx m).2 = y₀) (hma : a ≤ (P.vtx m).1)
    (hmb : (P.vtx m).1 ≤ b) {p : Point} (hp : p ∈ freeRegion P) (hpy : p.2 = y₀) (hpa : a < p.1)
    (hpb : p.1 < b) : False := by
  have hnot : ¬ ((leftEnd P p).1 ≤ (P.vtx m).1 ∧ (P.vtx m).1 ≤ (rightEnd P p).1) :=
    fun hh => not_vtx_mem_closedHSeg hP hp hm (hmy.trans hpy.symm) hh.1 hh.2
  rw [not_and_or, not_le, not_le] at hnot
  zuklt
  · obtain ⟨i, hi, hL, hnh⟩ := exists_leftEdge hP hp
    have hle := leftEnd_fst_lt hP hp.1
    have he : (((leftEnd P p).1, y₀) : Point) = leftEnd P p := point_ext rfl hpy.symm
    have := hnear (leftEnd P p).1 by_linarith by_linarith
    zugdu
    exact side_edge_false hε hU by_simp_all this hi hnh hL
  · obtain ⟨j, hj, hR, hnh⟩ := exists_rightEdge hP hp
    have hle := lt_rightEnd_fst hP hp.1
    have he : (((rightEnd P p).1, y₀) : Point) = rightEnd P p := point_ext rfl hpy.symm
    have := hnear (rightEnd P p).1 by_linarith by_linarith
    zugdu
    exact side_edge_false hε hU by_simp_all this hj hnh hR
namespace IsTrap
variable {P : Polygon} {q : Point} {i j : ℕ} {y₁ y₂ : ℝ}

/-- Near a point of the open top side, the points below the top height are in the trapezoid. -/
theorem near_top (h : IsTrap P q i j y₁ y₂) {x : ℝ} (hx1 : edgeX P i y₂ < x)
    (hx2 : x < edgeX P j y₂) :
    ∀ᶠ p' in 𝓝 (ztcxc : Point), 0 < (-1) * (p'.2 - y₂) → p' ∈ trapSet P i j y₁ y₂ := by
  have hopen : IsOpen {p' : Point | y₁ < p'.2 ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} := by
    zquz
    have h3 :=
      isOpen_lt zteiw continuous_fst
    have h4 :=
      isOpen_lt continuous_fst zteix
    exact h1.inter ztvsl
  have hmem : (ztcxc : Point) ∈
      {p' : Point | y₁ < p'.2 ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} :=
    ⟨h.bot_lt.trans h.lt_top, hx1, hx2⟩
  zuhdf
  exact ⟨hp'.1, by_linarith, hp'.2.1, hp'.2.2⟩

/-- Near a point of the open bottom side, the points above the bottom height are in the
trapezoid. -/
theorem near_bot (h : IsTrap P q i j y₁ y₂) {x : ℝ} (hx1 : edgeX P i y₁ < x)
    (hx2 : x < edgeX P j y₁) :
    ∀ᶠ p' in 𝓝 (ztfvi : Point), 0 < 1 * (p'.2 - y₁) → p' ∈ trapSet P i j y₁ y₂ := by
  have hopen : IsOpen {p' : Point | p'.2 < y₂ ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} := by
    zqva
    have h3 :=
      isOpen_lt zteiw continuous_fst
    have h4 :=
      isOpen_lt continuous_fst zteix
    exact h2.inter ztvsl
  have hmem : (ztfvi : Point) ∈
      {p' : Point | p'.2 < y₂ ∧ edgeX P i p'.2 < p'.1 ∧ p'.1 < edgeX P j p'.2} :=
    ⟨h.bot_lt.trans h.lt_top, hx1, hx2⟩
  zuhdf
  exact ⟨by_linarith, hp'.1, hp'.2.1, hp'.2.2⟩

/-- **A free point of the closure of the trapezoid lies in the trapezoid.** -/
theorem closure_inter_free (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂) :
    closure ztbku ∩ freeRegion P ⊆ trapSet P i j y₁ y₂ := by
  rintro p ⟨hpc, hpf⟩
  obtain ⟨h1, h2, h3, h4⟩ := closure_trapSet_subset P i j y₁ y₂ hpc
  have hnotL := fun e => hpf.1.2 ⟨i, h.hi, h.mem_edgeL h1 h2 e⟩
  have hnotR := fun e => hpf.1.2 ztmqq
  have h3' : edgeX P i p.2 < p.1 := by_grind
  have h4' : p.1 < edgeX P j p.2 := by_grind
  refine ⟨?_, ?_, h3', h4'⟩
  · rcases h1.lt_or_eq with hlt | heq
    · omega
    · exfalso
      zvnbo at h3' h4'
      obtain ⟨m, hm, hmy, hmx⟩ := h.bot_vertex
      zuhht
      exact not_free_of_side hP ztp zttlu
        ztmka hm hmy hma hmb hpf heq.symm h3' h4'
  · rcases h2.lt_or_eq with hlt | heq
    · omega
    · exfalso
      zvnbk at h3' h4'
      obtain ⟨m, hm, hmy, hmx⟩ := h.top_vertex
      zuhht
      exact not_free_of_side hP ztbt zttlu
        ztmkb hm hmy hma hmb hpf heq h3' h4'

/-- **The region of `q` is exactly the trapezoid.** -/
theorem region_eq (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂) :
    connectedComponentIn ztesb q = trapSet P i j y₁ y₂ := by
  zugjb
  · refine IsPreconnected.subset_left_of_subset_union ztpcl
      isClosed_closure.isOpen_compl ztvpd ?_
      ⟨q, mem_connectedComponentIn hq, h.q_mem hP hq.1⟩ isPreconnected_connectedComponentIn
    zuda
    by_cases hpc : p ∈ closure ztbku
    · exact Or.inl (h.closure_inter_free hP hq ⟨hpc, connectedComponentIn_subset _ _ hp⟩)
    simp_all
  · exact (convex_trapSet P i j y₁ y₂).isPreconnected.subset_connectedComponentIn
      zttls (h.trapSet_subset_freeRegion hP hq)

/-- The closure of the trapezoid lies in the filled region. -/
theorem closure_subset_filled (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂) :
    closure ztbku ⊆ P.filled :=
  closure_minimal (fun _ hp => (h.trapSet_subset_interior hP hq hp).1) (isClosed_filled P)

/-- A point of the open top side is in the closure of the trapezoid. -/
theorem top_mem_closure (h : IsTrap P q i j y₁ y₂) {x : ℝ} (hx1 : edgeX P i y₂ < x)
    (hx2 : x < edgeX P j y₂) : (ztcxc : Point) ∈ closure ztbku := by
  have hcont : Continuous fun η : ℝ => ((x, y₂ - η) : Point) := by fun_prop
  have htend : Tendsto (fun η : ℝ => ((x, y₂ - η) : Point)) (𝓝[>] 0) (𝓝 (x, y₂)) := by
    have := hcont.tendsto 0
    zujoz
    zuhv
  zucyz
  have hev := htend.eventually (h.near_top hx1 hx2)
  zufsq

/-- A point of the open bottom side is in the closure of the trapezoid. -/
theorem bot_mem_closure (h : IsTrap P q i j y₁ y₂) {x : ℝ} (hx1 : edgeX P i y₁ < x)
    (hx2 : x < edgeX P j y₁) : (ztfvi : Point) ∈ closure ztbku := by
  have hcont : Continuous fun η : ℝ => ((x, y₁ + η) : Point) := by fun_prop
  have htend : Tendsto (fun η : ℝ => ((x, y₁ + η) : Point)) (𝓝[>] 0) (𝓝 (x, y₁)) := by
    have := hcont.tendsto 0
    zufbg
    zuhv
  zucyz
  have hev := htend.eventually (h.near_bot hx1 hx2)
  zufsq

/-- **The open top side consists of boundary points and chord points.** -/
theorem top_side (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂) {x : ℝ}
    (hx1 : edgeX P i y₂ < x) (hx2 : x < edgeX P j y₂) :
    (ztcxc : Point) ∈ P.boundary ∪ chordUnion P := by
  zubqk
  zuilo
  have hc := h.top_mem_closure hx1 hx2
  have hfree : (ztcxc : Point) ∈ freeRegion P :=
    ⟨⟨h.closure_subset_filled hP hq hc, hcon.1⟩, hcon.2⟩
  have := h.closure_inter_free hP hq ztuhj
  exact lt_irrefl _ this.2.1

/-- **The open bottom side consists of boundary points and chord points.** -/
theorem bot_side (hP : P.Simple) (hq : q ∈ freeRegion P) (h : IsTrap P q i j y₁ y₂) {x : ℝ}
    (hx1 : edgeX P i y₁ < x) (hx2 : x < edgeX P j y₁) :
    (ztfvi : Point) ∈ P.boundary ∪ chordUnion P := by
  zubqk
  zuilo
  have hc := h.bot_mem_closure hx1 hx2
  have hfree : (ztfvi : Point) ∈ freeRegion P :=
    ⟨⟨h.closure_subset_filled hP hq hc, hcon.1⟩, hcon.2⟩
  have := h.closure_inter_free hP hq ztuhj
  exact lt_irrefl _ this.1
end IsTrap

/-! ### The main theorems -/

/-- **The region of a free point is an open trapezoid.** -/
theorem exists_isTrap_region_eq {P : Polygon} (hP : P.Simple) {q : Point}
    (hq : q ∈ freeRegion P) :
    ∃ i j y₁ y₂, IsTrap P q i j y₁ y₂ ∧
      connectedComponentIn ztesb q = trapSet P i j y₁ y₂ := by
  obtain ⟨i, j, y₁, y₂, h⟩ := exists_isTrap hP hq
  exact ⟨i, j, y₁, y₂, h, h.region_eq hP hq⟩

/-- **Every region of the horizontal visibility map is an open trapezoid**: for some free point
`q` with trapezoid data `i, j, y₁, y₂`, the region is
`{p | y₁ < p.2 < y₂ ∧ edgeX P i p.2 < p.1 < edgeX P j p.2}`. -/
theorem regions_eq_trapSet {P : Polygon} (hP : P.Simple) {C : Set Point} (hC : C ∈ regions P) :
    ∃ q i j y₁ y₂, q ∈ freeRegion P ∧ IsTrap P q i j y₁ y₂ ∧ C = trapSet P i j y₁ y₂ := by
  obtain ⟨q, hq, rfl⟩ := hC
  obtain ⟨i, j, y₁, y₂, h, he⟩ := exists_isTrap_region_eq hP hq
  grind
end
end Chazelle.Visibility
end
section
set_option hygiene false
local macro "zquc" : tactic => `(tactic| (set A := freeOf P S with hA; set A' := freeOf P (insert c S) with hA'; set R := connectedComponentIn A z₀ with hR; have hA'A : A' ⊆ A := freeOf_anti P by_simp_all; have hA'eq : ztmsu := freeOf_insert P c S; have hz₀A := chord_sdiff_subset_freeOf hP hS hc hcS hz₀))
local macro "zqud" : tactic => `(tactic| obtain ⟨z, -, rfl⟩ := hC)
local macro "zque" : tactic => `(tactic| (have hRopen : ztrfp := (isOpen_freeOf hP hS).connectedComponentIn; have hRA : R ⊆ A := connectedComponentIn_subset _ _))
local macro "zquf" : tactic => `(tactic| obtain ⟨i, σ, hi, -, h, rfl⟩ := hc)
local macro "zqug" : tactic => `(tactic| obtain ⟨i, σ, hi, hσ, h, rfl⟩ := hc)
set_option hygiene true

/-!
# Submaps of the horizontal visibility map: chord separation and exact splitting

A *submap* is a set `S ⊆ chords P` of vertex chords of a simple polygon `P`.  Its free set
`freeOf P S` is the interior `P.filled \ P.boundary` minus the chords of `S`, and its
*regions* `regionsOf P S` are the connected components of the free set (so
`regions P = regionsOf P (chords P)`).

* `chord_separates` (Chazelle's Lemma 2.1, interior version): for `c ∈ S` and an interior
  point `z` of `c`, the points `z ± (0, ε)` lie in the free set of `S` and in *different*
  regions.  The proof builds the closed walk `arcPoly` from the chord and one boundary arc of
  `P` between its endpoints; its boundary lies in `P.boundary ∪ c`, so the crossing parity of
  this walk is constant on every region, while it flips across the chord (`parity_flip`).
* `regionsOf_insert` (exact splitting): adding a chord `c ∉ S` to `S` replaces the unique
  region `R` containing the open chord by exactly two regions `R₁ ≠ R₂` with
  `R₁ ∪ R₂ = R \ c`, and leaves the other regions unchanged.
* `ncard_regionsOf`: a submap with `k` chords has exactly `k + 1` regions; in particular
  `regions_ncard : (regions P).ncard = (chords P).ncard + 1 ≤ 2 n + 1`.
-/
namespace Chazelle.Visibility
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan

/-! ### Regions of a submap -/

/-- The free set of the submap `S`: the interior of `P` minus the chords of `S`. -/
def freeOf (P : Polygon) (S : Set ztf) : Set Point :=
  zthbx \ ⋃₀ S

/-- The regions of the submap `S`: the connected components of its free set. -/
def regionsOf (P : Polygon) (S : Set ztf) : Set ztf :=
  {C | ∃ z ∈ freeOf P S, C = connectedComponentIn ztcvd z}
variable {P : Polygon} {S : Set (Set Point)} {C : Set Point} {c : Set Point} (w : Point) (r τ : ℝ)
/-- The union of a set of chords is closed. -/
theorem isClosed_sUnion_of_subset_chords
    (hS : S ⊆ chords P) : IsClosed ztufn :=
  ((chords_finite P).subset hS).isClosed_sUnion fun _ h => chords_isClosed ztqpn

/-- The free set of a submap is open. -/
theorem isOpen_freeOf (hP : P.Simple) {S : Set ztf} (hS : S ⊆ chords P) :
    IsOpen ztcvd :=
  (isOpen_filled_sdiff_boundary hP).sdiff (isClosed_sUnion_of_subset_chords hS)
theorem freeOf_anti (P : Polygon) {S T : Set ztf} (h : S ⊆ T) :
    freeOf P T ⊆ freeOf P S :=
  fun _ hp => ztool
theorem freeOf_insert (P : Polygon) (c : Set Point) (S : Set ztf) :
    freeOf P ztlf = freeOf P S \ c := by
  zufj
  simp only [freeOf, sUnion_insert, Set.mem_sdiff, mem_union]
  tauto
theorem mem_regionsOf {z : Point} (hz : z ∈ freeOf P S) :
    connectedComponentIn ztcvd z ∈ regionsOf P S := ztrfb

/-- Every region of a submap is open. -/
theorem regionsOf_open (hP : P.Simple) {S : Set ztf} (hS : S ⊆ chords P)
    {C : Set Point} (hC : C ∈ regionsOf P S) : IsOpen C := by
  zqud
  exact (isOpen_freeOf hP hS).connectedComponentIn

/-- Every region of a submap is nonempty. -/
theorem regionsOf_nonempty
    (hC : C ∈ regionsOf P S) : C.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := hC
  exact ztrza

/-- Every region of a submap is preconnected. -/
theorem regionsOf_isPreconnected
    (hC : C ∈ regionsOf P S) : IsPreconnected C := by
  zqud
  zulzc

/-- Every region of a submap lies in the free set. -/
theorem regionsOf_subset
    (hC : C ∈ regionsOf P S) : C ⊆ freeOf P S := by
  zqud
  zuitc

/-- A region is the component of each of its points. -/
theorem regionsOf_eq_component
    (hC : C ∈ regionsOf P S) {p : Point} (hp : p ∈ C) :
    C = connectedComponentIn ztcvd p := by
  zqud
  exact connectedComponentIn_eq hp

/-- Two regions of a submap are equal or disjoint. -/
theorem regionsOf_eq_or_disjoint {C D : Set Point}
    (hC : C ∈ regionsOf P S) (hD : D ∈ regionsOf P S) : C = D ∨ Disjoint C D := by
  by_cases h : Disjoint C D
  · simp_all
  · left
    obtain ⟨p, hpC, hpD⟩ := not_disjoint_iff.1 h
    rw [regionsOf_eq_component hC hpC, regionsOf_eq_component hD hpD]

/-- Two distinct regions of a submap are disjoint. -/
theorem regionsOf_disjoint_of_ne {C D : Set Point}
    (hC : C ∈ regionsOf P S) (hD : D ∈ regionsOf P S) (hne : C ≠ D) : Disjoint C D :=
  (regionsOf_eq_or_disjoint hC hD).resolve_left hne

/-- The empty submap has a single region, the whole interior. -/
theorem regionsOf_empty (hP : P.Simple) :
    regionsOf P ∅ = {P.filled \ P.boundary} := by
  have hfree : freeOf P ∅ = P.filled \ P.boundary := by
    simp [freeOf]
  ext C
  simp only [regionsOf, mem_ofPred_eq, mem_singleton_iff, hfree]
  constructor
  · zuecs
    exact (filled_sdiff_boundary_connected hP).connectedComponentIn hz
  · zunq
    obtain ⟨z, hz⟩ := filled_sdiff_boundary_nonempty hP
    exact ⟨z, hz, ((filled_sdiff_boundary_connected hP).connectedComponentIn hz).symm⟩

/-! ### Chords: elementary facts -/

/-- Every chord is horizontal: all its points share the ordinate of any of them. -/
theorem chords_snd_eq (hc : c ∈ chords P) {p q : Point}
    (hp : p ∈ c) (hq : q ∈ c) : p.2 = q.2 := by
  obtain ⟨i, σ, -, -, -, rfl⟩ := hc
  rw [chordSet_eq_hseg] at hp hq
  zukvl

/-- A chord lies in the filled region. -/
theorem chords_subset_filled (hP : P.Simple) {c : Set Point} (hc : c ∈ chords P) :
    c ⊆ P.filled := by
  zquf
  exact chordSet_subset_filled hP hi h

/-- Two distinct chords meet only in boundary points. -/
theorem chords_inter_subset_boundary (hP : P.Simple) {c d : Set Point}
    (hc : c ∈ chords P) (hd : d ∈ chords P) (hne : c ≠ d) : c ∩ d ⊆ P.boundary := by
  obtain ⟨i, σ, hi, hσ, hiσ, rfl⟩ := hc
  obtain ⟨j, τ, hj, hτ, hjτ, rfl⟩ := hd
  zuda
  rcases chordSet_inter hP hi hj hσ hτ hiσ hjτ hp with h | ⟨h, -⟩
  · simp_all
  · zugp

    · exact Existence.vtx_mem_boundary P hi
    · exact chordEnd_mem_boundary hP hi hiσ

/-- The interior part of a chord lies in the free set of every submap not containing it. -/
theorem chord_sdiff_subset_freeOf (hP : P.Simple) {S : Set ztf}
    (hS : S ⊆ chords P) {c : Set Point} (hc : c ∈ chords P) (hcS : c ∉ S) :
    c \ P.boundary ⊆ freeOf P S := by
  rintro p ⟨hp, hpb⟩
  refine ⟨⟨chords_subset_filled hP hc hp, hpb⟩, ?_⟩
  zudtd

  exact hpb (chords_inter_subset_boundary hP hc ztvtu hne by_simp_all)

/-- The interior part of a chord is the open chord. -/
theorem chordSet_sdiff_boundary (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordSet P i σ \ P.boundary = openChordSet P i σ := by
  zufj
  constructor
  · rintro ⟨hp, hpb⟩
    zuhks
    zudsh
    · zuitn
    · exfalso
      zugaa
      · exact hpb ztsxd
      · exact hpb ztlma
  · zulmw
    refine ⟨?_, (openChordSet_subset_interior hP hi h hp).2⟩
    zuihd

/-- The open chord is preconnected. -/
theorem isPreconnected_openChordSet (P : Polygon) (i : ℕ) (σ : ℝ) :
    IsPreconnected (openChordSet P i σ) :=
  isPreconnected_Ioo.image _ (continuous_rayPt _ σ).continuousOn

/-- The open chord is nonempty. -/
theorem openChordSet_nonempty (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : (openChordSet P i σ).Nonempty :=
  ⟨_, ⟨chordParam P i σ / 2, ⟨by zuohg,
    by zuohg⟩, rfl⟩⟩

/-- The interior part of a chord is nonempty and preconnected. -/
theorem chord_sdiff_nonempty_isPreconnected (hP : P.Simple) {c : Set Point}
    (hc : c ∈ chords P) : (c \ P.boundary).Nonempty ∧ IsPreconnected (c \ P.boundary) := by
  zquf
  rw [chordSet_sdiff_boundary hP hi h]
  exact ⟨openChordSet_nonempty hP hi h, isPreconnected_openChordSet P i σ⟩

/-! ### The closed walk made of a chord and a boundary arc -/

/-- The closed walk with vertices `P.vtx i, P.vtx (i+1), …, P.vtx (i+m-1)` (indices mod `n`)
followed by the point `e`. -/
def arcPoly (P : Polygon) (i m : ℕ) (e : Point) : Polygon :=
  ⟨(List.range m).map (fun k => P.vtx ztgwb) ++ [e]⟩
@[simp] theorem arcPoly_n (P : Polygon) (i m : ℕ) (e : Point) : (arcPoly P i m e).n = m + 1 := by
  simp [arcPoly, Polygon.n]
theorem arcPoly_vtx_of_lt (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) {k : ℕ} (hk : k < m) :
    (arcPoly P i m e).vtx k = P.vtx ztgwb := by
  simp only [arcPoly, Polygon.vtx, List.getD_eq_getElem?_getD]
  grind
theorem arcPoly_vtx_last (P : Polygon) (i m : ℕ) (e : Point) : (arcPoly P i m e).vtx m = e := by
  simp [arcPoly, Polygon.vtx, List.getD_eq_getElem?_getD]
theorem arcPoly_edge_of_lt (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) {k : ℕ} (hk : k + 1 < m) :
    (arcPoly P i m e).edge k = P.edge ztgwb := by
  zucrd
  rw [arcPoly_n, Nat.mod_eq_of_lt by_grind, arcPoly_vtx_of_lt P i e by_omega,
    arcPoly_vtx_of_lt P i e hk, Existence.mod_add_one_mod]
theorem arcPoly_edge_pen (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) (hm : 0 < m) :
    (arcPoly P i m e).edge ztfte = Chazelle.segment ztcck e := by
  zucrd
  rw [arcPoly_n, show m - 1 + 1 = m by omega, Nat.mod_eq_of_lt by_simp_all,
    arcPoly_vtx_of_lt P i e by_omega, arcPoly_vtx_last]
theorem arcPoly_edge_last (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) (hm : 0 < m) :
    (arcPoly P i m e).edge m = Chazelle.segment e ztoxm := by
  zucrd
  rw [arcPoly_n, Nat.mod_self, arcPoly_vtx_of_lt P i e hm, arcPoly_vtx_last, Nat.add_zero]

/-- Every edge of the walk other than the last lies in the boundary of `P`, provided the
penultimate edge does. -/
theorem arcPoly_edge_subset_boundary (P : Polygon) (hn : 0 < P.n) (i : ℕ) {m : ℕ} (e : Point)
    (hm : 0 < m) (hpen : Chazelle.segment ztcck e ⊆ P.boundary) {k : ℕ}
    (hk : k < m) : (arcPoly P i m e).edge k ⊆ P.boundary := by
  zuidv
  · rw [arcPoly_edge_of_lt P i e h]
    exact Existence.edge_subset_boundary P zthp
  · have : k = m - 1 := by_omega
    zumo
    rw [arcPoly_edge_pen P i e hm]
    omega

/-- The boundary of the walk lies in the boundary of `P` together with the closing segment. -/
theorem arcPoly_boundary_subset (P : Polygon) (hn : 0 < P.n) (i : ℕ) {m : ℕ} (e : Point)
    (hm : 0 < m) (hpen : Chazelle.segment ztcck e ⊆ P.boundary) :
    (arcPoly P i m e).boundary ⊆ P.boundary ∪ Chazelle.segment e ztoxm := by
  zuhjt
  zukqe
  rcases Nat.lt_or_ge k m with h | h
  · exact Or.inl (arcPoly_edge_subset_boundary P hn i e hm hpen h hp)
  · have : k = m := by_omega
    zumo
    rw [arcPoly_edge_last P i e hm] at hp
    simp_all

/-! ### Chord separation -/

/-- **The parity flip across a chord.**  For an interior point `z` of the chord of vertex `i`
in direction `σ`, there is a closed walk `Γ` whose boundary lies in `P.boundary ∪ chord`, such
that the points `z ± (0, ε)` (small `ε > 0`) are off the boundary of `Γ` and have different
crossing parities with respect to `Γ`. -/
theorem exists_walk_parity_flip (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) {z : Point} (hz : z ∈ chordSet P i σ)
    (hzb : z ∉ P.boundary) :
    ∃ Γ : Polygon, Γ.boundary ⊆ P.boundary ∪ chordSet P i σ ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        ztgd ∉ Γ.boundary ∧ ztfr ∉ Γ.boundary ∧
          parity Γ ztgd ≠ parity Γ ztfr := by
  zuiz
  obtain ⟨j, hj, hej⟩ := chordEnd_mem_boundary hP hi h
  set e := chordEnd P i σ with he
  set m := ztqry % P.n + 1 with hm
  have hm0 : ztphu := by_omega
  have hidx : (i + ztfte) % P.n = j := by
    rw [hm, Nat.add_sub_cancel, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      show i + ztqry = j + P.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have hpen : Chazelle.segment ztcck e ⊆ P.boundary := by
    zujiz
    refine Subset.trans ?_ (Existence.edge_subset_boundary P hj)
    exact Geometry.segment_subset_of_convex ztemu
      ztdte hej
  have hii := Nat.mod_eq_of_lt hi
  refine ⟨arcPoly P i m e, ?_, ?_⟩
  · refine (arcPoly_boundary_subset P hn i e hm0 hpen).trans ?_
    rw [hii, Geometry.segment_comm]
    rfl
  · have hzΓ : z ∈ (arcPoly P i m e).edge m := by
      rw [arcPoly_edge_last P i e hm0, hii, Geometry.segment_comm]
      exact hz
    have hmn : m < (arcPoly P i m e).n := by_simp
    have hsucc : ztbl % (arcPoly P i m e).n = 0 := by_simp
    have hv0 : (arcPoly P i m e).vtx 0 = P.vtx i := by
      rw [arcPoly_vtx_of_lt P i e hm0, Nat.add_zero, hii]
    have hne : ((arcPoly P i m e).vtx m).1 ≠ ((arcPoly P i m e).vtx ztybh).1 := by
      rw [hsucc, hv0, arcPoly_vtx_last, he, chordEnd_fst]
      zudii
      have hσ0 := h.ne_zero hi
      zuesa
      grind
    have hzu : z ≠ (arcPoly P i m e).vtx m := by
      rw [arcPoly_vtx_last]
      zunq
      exact hzb ztlma
    have hzv : z ≠ (arcPoly P i m e).vtx ztybh := by
      rw [hsucc, hv0]
      zunq
      exact hzb ztsxd
    have hother : ∀ k, k < (arcPoly P i m e).n → k ≠ m → z ∉ (arcPoly P i m e).edge k := by
      zulnd
      zukqe
      exact hzb (arcPoly_edge_subset_boundary P hn i e hm0 hpen by_omega hzk)
    exact parity_flip _ hmn hzΓ hne hzu hzv hother

/-- **Chord separation** (Lemma 2.1, interior case).  Let `S ⊆ chords P`, `c ∈ S`, and let `z`
be an interior point of `c`.  Then for all small `ε > 0` the points `z ± (0, ε)` lie in the
free set of `S` and in different regions of `S`. -/
theorem chord_separates (hP : P.Simple) {S : Set ztf} (hS : S ⊆ chords P)
    {c : Set Point} (hc : c ∈ S) {z : Point} (hz : z ∈ c) (hzb : z ∉ P.boundary) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      ztgd ∈ freeOf P S ∧ ztfr ∈ freeOf P S ∧
        connectedComponentIn ztcvd ztgd ≠
          connectedComponentIn ztcvd ztfr := by
  obtain ⟨i, σ, hi, hσ, h, rfl⟩ := hS hc
  obtain ⟨Γ, hΓ, ε₁, hε₁, hflip⟩ := exists_walk_parity_flip hP hi h hz hzb
  -- the two points are eventually in the free set
  have hup : Tendsto (fun ε : ℝ => ((z.1, z.2 + ε) : Point)) (𝓝[>] 0) _ :=
    ((by fun_prop : Continuous fun ε : ℝ => (ztgd : Point)).tendsto' 0 z
      by_simp).mono_left nhdsWithin_le_nhds
  have hdn : Tendsto (fun ε : ℝ => ((z.1, z.2 - ε) : Point)) (𝓝[>] 0) _ :=
    ((by fun_prop : Continuous fun ε : ℝ => (ztfr : Point)).tendsto' 0 z
      by_simp).mono_left nhdsWithin_le_nhds
  have hzint : ztsnl := ⟨chordSet_subset_filled hP hi h hz, hzb⟩
  have hint := (isOpen_filled_sdiff_boundary hP).mem_nhds hzint
  -- the other chords: a closed set not containing `z`
  have hK : IsClosed (⋃₀ ztger) :=
    isClosed_sUnion_of_subset_chords (fun _ hd => hS hd.1)
  have hzK : z ∉ ⋃₀ ztger := by
    rintro ⟨d, ⟨hdS, hdc⟩, hzd⟩
    zukxp
    exact hzb (chords_inter_subset_boundary hP ztbkp ztqpo ztvav by_simp_all)
  zulif
  have hfree : ∀ ε : ℝ, 0 < ε → ∀ p : Point, p.1 = z.1 → p.2 ≠ z.2 →
      p ∈ P.filled \ P.boundary → p ∉ ⋃₀ ztger → p ∈ freeOf P S := by
    intro ε hε p hp1 hp2 hpint hpK
    refine ⟨hpint, ?_⟩
    rintro ⟨d, hdS, hpd⟩
    by_cases hdc : d = chordSet P i σ
    · subst hdc
      exact hp2 (chords_snd_eq ztbkp hpd hz)
    grind
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ztgd ∈ freeOf P S ∧ ztfr ∈ freeOf P S ∧
        connectedComponentIn ztcvd ztgd ≠
          connectedComponentIn ztcvd ztfr := by
    filter_upwards [hup.eventually hint, hdn.eventually hint, hup.eventually hKn,
      hdn.eventually hKn, self_mem_nhdsWithin, Ioo_mem_nhdsGT hε₁] with ε h1 h2 h3 h4 h5 h6
    zumfe
    have hp : ztgd ∈ freeOf P S :=
      hfree ε hε _ rfl by_grind h1 h3
    have hq : ztfr ∈ freeOf P S :=
      hfree ε hε _ rfl by_grind h2 h4
    zudjn

    have hsub : freeOf P S ⊆ Γ.boundaryᶜ := by
      zufxo

      · exact hp.1.2 hb
      · exact hp.2 by_grind
    exact parity_eq_of_isPreconnected Γ isPreconnected_connectedComponentIn
      ztdeh ztvyt
      ztrrs
  zucom
  exact ztiwo

/-! ### Half-disks -/

/-- The open half-disk (for the sup metric: half-square) of radius `r` around `w`, on the side
`τ` (`1` = above, `-1` = below). -/
def halfDisk (w : Point) (r τ : ℝ) : Set Point := ball w r ∩ {p | 0 < τ * ztkcc}
theorem mem_halfDisk_iff {w p : Point} {r τ : ℝ} :
    p ∈ halfDisk w r τ ↔ (|p.1 - w.1| < r ∧ |p.2 - w.2| < r) ∧ 0 < τ * ztkcc := by
  zughr
theorem halfDisk_subset_ball : halfDisk w r τ ⊆ ball w r :=
  inter_subset_left
theorem convex_halfDisk : Convex ℝ ztefh := by
  zubsb

  zutw
  have : ztcrk := by
    grind
  zubk
  zucoq
  · positivity
  · zudba
theorem isPreconnected_halfDisk : IsPreconnected ztefh :=
  (convex_halfDisk w r τ).isPreconnected

/-- The point at signed vertical distance `s` from `w` lies in the half-disk. -/
theorem vert_mem_halfDisk {w : Point} {r τ s : ℝ} (hτ : τ = 1 ∨ τ = -1) (hs0 : 0 < s)
    (hsr : s < r) : (zthkz : Point) ∈ halfDisk w r τ := by
  zueyz
  zudlq
  zujj
  · grind
  grind

/-- A half-disk around a point at the same height, inside the ball, is inside the half-disk. -/
theorem halfDisk_mono {w w' : Point} {r r' τ : ℝ} (hh : w'.2 = w.2) (hb : ball w' r' ⊆ ball w r) :
    halfDisk w' r' τ ⊆ halfDisk w r τ := by
  zuczg
  refine ztryv
  simp_all

/-- Two half-disks on the same side, centred at the same height and at horizontal distance
less than the first radius, meet. -/
theorem halfDisk_inter_nonempty {w w' : Point} {r r' τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hh : w'.2 = w.2) (hx : |w'.1 - w.1| < r) (hr' : 0 < r') :
    (halfDisk w r τ ∩ halfDisk w' r' τ).Nonempty := by
  zuyc

  · zueyz
    zufbf
    have habs : ztpqt := by
      grind
    zuifd

  · zugxt

/-! ### Exact splitting -/

/-- A half-disk at a chord point, inside the free set of `S`, avoids the chord and so lies in
the free set of `insert c S`. -/
theorem halfDisk_subset_freeOf_insert
    (hc : c ∈ chords P) {w : Point} (hw : w ∈ c) {r τ : ℝ} (hball : ball w r ⊆ freeOf P S) :
    halfDisk w r τ ⊆ freeOf P ztlf := by
  zuczg
  rw [freeOf_insert]
  zuhjb

  rw [chords_snd_eq hc hpc hw, sub_self, mul_zero] at hp2
  simp_all

/-- A preconnected subset of the free set meeting a region lies in it. -/
theorem subset_regionsOf_of_inter {U : Set Point}
    (hU : U ∈ regionsOf P S) {T : Set Point} (hT : IsPreconnected T) (hTS : T ⊆ freeOf P S)
    (hne : (T ∩ U).Nonempty) : T ⊆ U := by
  zugqm
  rw [regionsOf_eq_component hU hqU]
  zulyt

/-- Around every interior point of a chord `c` inside an open set `R` there is a ball inside
`R` whose points at the height of the chord lie on `c`. -/
theorem exists_ball_chord (hP : P.Simple) {c : Set Point} (hc : c ∈ chords P)
    {R : Set Point} (hR : IsOpen R) (hcR : c \ P.boundary ⊆ R) {w : Point}
    (hw : w ∈ c \ P.boundary) :
    ∃ r > (0 : ℝ), ball w r ⊆ R ∧ ∀ p ∈ ball w r, p.2 = w.2 → p ∈ c := by
  zqug
  zueus
  rw [chordSet_sdiff_boundary hP hi h] at hw
  obtain ⟨t, ⟨ht0, htL⟩, rfl⟩ := hw
  refine ⟨min r₁ (min t (chordParam P i σ - t)), by_simp_all,
    (ball_subset_ball by_simp_all).trans hball, fun p hp hp2 => ?_⟩
  zukxo
  simp only [rayPt_fst, rayPt_snd] at hp hp2
  have h1 : |p.1 - ztfls| < t :=
    by simp_all
  have h2 : |p.1 - ztfls| < chordParam P i σ - t :=
    by simp_all
  zujhj
  zubgl
  have hmem : p ∈ openChordSet P i σ := by
    refine ⟨t + σ * (p.1 - ztfls), ztcp, ?_⟩
    · zubbe
    · zubbe
    · zudtm
      zuipr

  zuihd

/-- **Half-disks on one side of a chord all lie in the same region.**  Let `R` be an open set
containing the interior part of the chord `c` and contained in the free set of `S`, and let
`U` be a region of `insert c S`.  If some half-disk (on side `τ`, inside `R`) at an interior
point of `c` lies in `U`, then every such half-disk does. -/
theorem halfDisk_all (hP : P.Simple) {S : Set ztf} {c : Set Point}
    (hc : c ∈ chords P) {R : Set Point} (hR : IsOpen R) (hcR : c \ P.boundary ⊆ R)
    (hRS : R ⊆ freeOf P S) {U : Set Point} (hU : U ∈ regionsOf P ztlf) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1)
    (hex : ∃ w ∈ c \ P.boundary, ∃ r > (0 : ℝ), ball w r ⊆ R ∧ halfDisk w r τ ⊆ U) :
    ∀ w ∈ c \ P.boundary, ∀ r > (0 : ℝ), ball w r ⊆ R → halfDisk w r τ ⊆ U := by
  -- a half-disk inside `R` meeting `U` lies in `U`
  have key : ∀ w ∈ c, ∀ r : ℝ, ball w r ⊆ R → (halfDisk w r τ ∩ U).Nonempty →
      halfDisk w r τ ⊆ U := fun w hw r hb hne =>
    subset_regionsOf_of_inter hU ztrsn
      (halfDisk_subset_freeOf_insert hc hw ztvuq) hne
  zqug
  have hσ1 : ztguu := by_grind
  have hopen := chordSet_sdiff_boundary hP hi h
  zuikh
  set v := P.vtx i
  set L := chordParam P i σ
  set T : Set ℝ := {t | ∃ r > (0 : ℝ), ball zthzo r ⊆ R ∧ halfDisk zthzo r τ ⊆ U}
    with hT
  -- `T` is open
  have hTopen : IsOpen T := by
    zujgz
    rintro t ⟨r, hr, hb, hU'⟩
    refine ⟨r / 2, half_pos hr, fun t' ht' => ?_⟩
    rw [mem_ball, Real.dist_eq] at ht'
    have hb' : ball ztrvc ztzr ⊆ ball zthzo r := by
      zuda
      zujks
      simp only [rayPt_fst, rayPt_snd] at hp ⊢
      refine zthma
      have : p.1 - (v.1 + σ * t) = ztzxm + σ * ztkft := by_ring
      zubk
      calc |ztzxm + σ * ztkft|
          ≤ |p.1 - ztkgp| + |σ * ztkft| := abs_add_le _ _
        _ < r / 2 + r / 2 := by
            grind
        _ = r := by_ring
    exact ⟨r / 2, half_pos hr, hb'.trans hb,
      (halfDisk_mono (w := rayPt v σ t) (w' := rayPt v σ t') rfl hb').trans hU'⟩
  -- `T` is relatively closed in the parameter interval
  have hTclosed : closure T ∩ Ioo 0 L ⊆ T := by
    rintro t ⟨htc, ht⟩
    set w := rayPt v σ t with hw
    have hwR := hcR ztbik
    zueuo
    obtain ⟨t', ht'T, htt'⟩ := Metric.mem_closure_iff.1 htc ztzr zteta
    obtain ⟨r', hr', -, hU'⟩ := ht'T
    rw [Real.dist_eq] at htt'
    have hwc : w ∈ chordSet P i σ := by
      zuexc
      grind
    refine ztiwl
    · have hx : |(rayPt v σ t').1 - w.1| < r := by
        zujjy
        zudlo
        grind
      obtain ⟨p, hp1, hp2⟩ := halfDisk_inter_nonempty hτ by_rfl hx hr'
      exact ztfka
  -- `T` meets the parameter interval
  have hTne : (Ioo 0 L ∩ T).Nonempty := by
    obtain ⟨w, ⟨t, ht, rfl⟩, r, hr, hb, hU'⟩ := hex
    exact ⟨t, ht, r, hr, hb, hU'⟩
  have hall :=
    isPreconnected_Ioo.subset_of_closure_inter_subset hTopen hTne hTclosed
  -- conclusion
  rintro w ⟨t, ht, rfl⟩ r hr hb
  obtain ⟨r₁, hr₁, -, hU'⟩ := hall ht
  have hwc : rayPt v σ t ∈ chordSet P i σ := by
    zuexc
    grind
  zujfb
  · zudrp

/-- **Every region of `insert c S` inside the region `R` of `c` contains a half-disk at an
interior point of `c`.** -/
theorem exists_halfDisk_subset (hP : P.Simple) {S : Set ztf}
    (hS : S ⊆ chords P) {c : Set Point} (hc : c ∈ chords P) (hcS : c ∉ S) {z₀ : Point}
    (hz₀ : z₀ ∈ c \ P.boundary) {U : Set Point} (hU : U ∈ regionsOf P ztlf) {u : Point}
    (huU : u ∈ U) (huR : u ∈ connectedComponentIn ztcvd z₀) :
    ∃ w ∈ c \ P.boundary, ∃ r > (0 : ℝ), ∃ τ : ℝ, ztoi ∧
      ball w r ⊆ connectedComponentIn ztcvd z₀ ∧ halfDisk w r τ ⊆ U := by
  zukah
  zquc
  have hcR :=
    (chord_sdiff_nonempty_isPreconnected hP hc).2.subset_connectedComponentIn hz₀
      ztqjt
  zque
  have hUopen := regionsOf_open hP hS' hU
  have hUA' := regionsOf_subset hU
  have hUeq := regionsOf_eq_component hU huU
  -- limit points of `U` in `A'` lie in `U`
  have hclos : ztrgh := by
    have hpre : ztrfr :=
      (regionsOf_isPreconnected hU).subset_closure ztubi
        inter_subset_left
    have := hpre.subset_connectedComponentIn ztreo inter_subset_right
    simp_all
  -- a chord point in the closure of `U`
  have hex : ∃ w ∈ c \ P.boundary, w ∈ closure U := by
    zubaj

    have hcl : ztrgi := by
      zudsy

      exact hno p ⟨hpcc, (hRA hpR).1.2⟩ hpc
    have hRU :=
      isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUopen ztrev hcl
    grind
  zugqv
  obtain ⟨r, hr, hb, hline⟩ := exists_ball_chord hP hc hRopen hcR hw
  zubrs

  have hqc : q ∉ c := by
    grind
  zugna

  · zujpm
  · have hτ : ztile = 1 ∨ ztile = -1 := by
      zujpm
    refine subset_regionsOf_of_inter hU ztlqi
      (halfDisk_subset_freeOf_insert hc hw.1 ztvup) ztlwl
    zuwb
    zujem
    · zujki
    simp_all

/-- **Exact splitting.**  Adding a chord `c ∉ S` to a submap `S ⊆ chords P` replaces the region
`R` of `S` containing the interior of `c` by exactly two regions `R₁ ≠ R₂` with
`R₁ ∪ R₂ = R \ c`, and leaves every other region unchanged. -/
theorem regionsOf_insert (hP : P.Simple) {S : Set ztf} (hS : S ⊆ chords P)
    {c : Set Point} (hc : c ∈ chords P) (hcS : c ∉ S) :
    ∃ R ∈ regionsOf P S, c \ P.boundary ⊆ R ∧ ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ R₁ ∪ R₂ = R \ c ∧
      R₁ ∈ regionsOf P ztlf ∧ R₂ ∈ regionsOf P ztlf ∧
      regionsOf P ztlf = ztogy ∪ {R₁, R₂} := by
  zukah
  obtain ⟨z₀, hz₀⟩ := (chord_sdiff_nonempty_isPreconnected hP hc).1
  zquc
  have hRmem := mem_regionsOf hz₀A
  have hcR :=
    (chord_sdiff_nonempty_isPreconnected hP hc).2.subset_connectedComponentIn hz₀
      ztqjt
  zque
  zucbn
  -- the two candidate regions

  have hpt : ztyae := fun τ hτ =>
    vert_mem_halfDisk hτ ztvum by_linarith
  have hhalf : ztmxs := fun τ =>
    halfDisk_subset_freeOf_insert hc hz₀.1 ztvus
  zukew
  have hRτ : ∀ τ, ztoi → connectedComponentIn A' ztwby ∈ regionsOf P _ :=
    fun τ hτ => mem_regionsOf by_grind
  have hhalfR : ztxtr :=
    fun τ hτ => (isPreconnected_halfDisk _ _ _).subset_connectedComponentIn zttoe ztvvh
  -- components of `A'` inside `R`
  have hsubR : ztipa := by
    zueaa

  have hRτR := fun τ hτ =>
    hsubR _ by_grind ztisy
  -- every region of `insert c S` meeting `R` is one of the two
  have hcases : ∀ U ∈ regionsOf P ztlf, (U ∩ R).Nonempty →
      U = connectedComponentIn A' zthzf ∨ U = connectedComponentIn A' ztdpc := by
    zugob
    obtain ⟨w, hw, r, hr, τ, hτ, hb, hsub⟩ :=
      exists_halfDisk_subset hP hS hc hcS hz₀ hU huU huR
    have hall := halfDisk_all hP hc hRopen hcR hRA hU hτ by_grind z₀ hz₀ r₀ hr₀ hb₀
    zukex
    have hUeq : ztscs := regionsOf_eq_component hU hptU
    zujj
    · grind
    grind
  -- the two regions differ
  have hne : ztyyn := by
    obtain ⟨ε₀, hε₀, hsep⟩ :=
      chord_separates hP hS' zthip hz₀.1 hz₀.2
    zuha

    have h1 : ztyla := by
      zulvq
      have := vert_mem_halfDisk ztp hε0 hε2 (w := z₀)
      grind
    have h2 : ztylb := by
      zulvr
      have := vert_mem_halfDisk ztbt hε0 hε2 (w := z₀)
      grind
    calc connectedComponentIn _ ztewu
        = connectedComponentIn A' _ := (connectedComponentIn_eq h1).symm
      _ = connectedComponentIn A' _ := heq
      _ = connectedComponentIn _ ztewv :=
          connectedComponentIn_eq h2
  -- other regions are unchanged
  have hother : ∀ U ∈ regionsOf P S, U ≠ R → U ∈ regionsOf P ztlf := by
    zudzx

    have hdisj := regionsOf_disjoint_of_ne hU hRmem hUR
    have hUA' : ztsfo := by
      zuda
      zuksb

      have hpR := hcR ⟨hpc, (connectedComponentIn_subset _ _ hp).1.2⟩
      zulyu
    zuizm

    zugjb
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        ztmml hUA'
    · zulyf
  refine ⟨R, hRmem, hcR, connectedComponentIn A' _, connectedComponentIn A' _, hne,
    ?_, hRτ 1 ztp, hRτ _ ztbt, ?_⟩
  · zugjb
    · zuewh
      · exact ztxme
      · exact ⟨hRτR _ ztbt hp,
          (ztfhr : p ∈ A \ c).2⟩
    · zueci

      rcases hcases _ (mem_regionsOf hpA') ⟨p, mem_connectedComponentIn hpA', hpR⟩ with h | h
      · exact Or.inl zthxp
      · exact Or.inr zthxp
  · zuefr

    · zulmt
      zubpm
      zufwq

      · exact Or.inr (hcases _ (mem_regionsOf hu) ztpgb)
      · left
        have hUmem := mem_regionsOf huA
        have hUR : ztsfn := by
          zufxl
        zubpl

    · zuflz
      · grind
      · tauto
      grind

/-! ### Counting regions -/

/-- The region `R` split by `regionsOf_insert` is not one of the two new regions, and the two
new regions are not old regions other than `R`: bookkeeping for the count. -/
theorem ncard_regionsOf_insert (hP : P.Simple) {S : Set ztf}
    (hS : S ⊆ chords P) {c : Set Point} (hc : c ∈ chords P) (hcS : c ∉ S)
    (hfin : (regionsOf P S).Finite) :
    (regionsOf P ztlf).Finite ∧
      (regionsOf P ztlf).ncard = (regionsOf P S).ncard + 1 := by
  obtain ⟨R, hR, -, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := regionsOf_insert hP hS hc hcS
  have hnew : ∀ U, U ∈ regionsOf P ztlf → U ⊆ R → U ∉ regionsOf P S \ {R} := by
    zuecd

    obtain ⟨p, hp⟩ := regionsOf_nonempty hU
    exact (regionsOf_disjoint_of_ne hUS hR hUne).notMem_of_mem_left hp ztvuh
  have hR₁R : ztiyp := fun p hp => by
    zubtb
    grind
  have hR₂R : ztiyq := fun p hp => by
    zuclo
    grind
  have hdisj : Disjoint ztogy {R₁, R₂} := by
    grind
  zudab
  refine ztzog
  rw [ncard_union_eq hdisj hfin.sdiff ztcwq, ncard_pair hne,
    ← ncard_sdiff_singleton_add_one hR hfin]

/-- **Region count.**  A submap with `k` chords has exactly `k + 1` regions (and finitely
many). -/
theorem regionsOf_finite_ncard (hP : P.Simple) {S : Set ztf}
    (hS : S ⊆ chords P) :
    (regionsOf P S).Finite ∧ (regionsOf P S).ncard = S.ncard + 1 := by
  have hfin := (chords_finite P).subset hS
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    rw [regionsOf_empty hP]
    simp
  | @insert c S hcS hSfin ih =>
    have hS' : S ⊆ chords P := by_grind
    have hc : c ∈ chords P := by_grind
    zuhhr
    obtain ⟨hfin'', hcard''⟩ := ncard_regionsOf_insert hP hS' hc hcS hfin'
    zufly

/-- A submap with `k` chords has exactly `k + 1` regions. -/
theorem ncard_regionsOf (hP : P.Simple) {S : Set ztf}
    (hS : S ⊆ chords P) : (regionsOf P S).ncard = S.ncard + 1 :=
  (regionsOf_finite_ncard hP hS).2

/-- The regions of a submap form a finite set. -/
theorem regionsOf_finite (hP : P.Simple) {S : Set ztf}
    (hS : S ⊆ chords P) : (regionsOf P S).Finite :=
  (regionsOf_finite_ncard hP hS).1

/-- **The visibility map of a simple polygon has exactly one more region than it has chords.** -/
theorem regions_ncard (hP : P.Simple) :
    (regions P).ncard = (chords P).ncard + 1 :=
  ncard_regionsOf hP ztibe

/-- The visibility map has at most `2 n + 1` regions. -/
theorem regions_ncard_le (hP : P.Simple) : (regions P).ncard ≤ 2 * P.n + 1 := by
  rw [regions_ncard hP]
  exact Nat.add_le_add_right (chords_ncard_le P) 1

/-- The regions of the visibility map form a finite set. -/
theorem regions_finite (hP : P.Simple) : (regions P).Finite :=
  regionsOf_finite hP ztibe
end
end Chazelle.Visibility
end
section
set_option hygiene false
local macro "zqbij" : tactic => `(tactic| (rw [mem_dom_iff]
                                           refine ⟨hp, fun h => ?_, fun h => ?_⟩))
local macro "zqbik" : tactic => `(tactic| have h1 := (C.mem_slit_iff.1 h).1)
local macro "zqbil" : tactic => `(tactic| (have h1 := C.midR_lt_radius
                                           have h2 := C.coordBound_lt_midR))
local macro "zqbim" : tactic => `(tactic| (rintro p ⟨⟨hp, hy⟩, hx⟩
                                           simp only [mem_ofPred_eq] at hx hy))
set_option hygiene true

/-!
# Subchains of a simple polygon and their box domain

This file sets up the *subchain visibility model* of Chazelle §2 (see
`docs/design-subchain-model.md`).

## The chain

A `Chain` is a simple polygon `P` together with a start index `s` and a number of edges `m`
with `1 ≤ m ≤ n - 1`: the chain consists of the edges `s, s+1, …, s+m-1` of `P` (indices mod
`n`), i.e. of the vertices `s, …, s+m`.  Its point set is `Chain.set`; it is closed, bounded,
contained in `P.boundary`, and misses at least one edge of `P` (`missingIdx`).

* `compl_connected`: **the complement of a simple open chain is connected**.  Proof: the
  complement contains the interior and the exterior of `P`, both connected (Jordan), and
  the midpoint `q` of a missing edge lies in the closure of both; so `Int ∪ {q} ∪ Ext` is
  connected, and `C.setᶜ` lies between it and its closure (every boundary point of `P` is a
  limit of interior points).
* `compl_unbounded`: the complement is unbounded.

## The box domain with a slit

The model works inside the open square `box C.radius` of half-side `radius = coordBound P + 1`,
which contains the chain.  To make the domain simply connected we remove, besides the chain,
a vertical *slit* from a topmost vertex `top` of the chain up to the top side of the box.  No
horizontal chord ever crosses the slit (all chain points are at height `≤ top.2`, and the only
slit point at that height is `top ∈ C`), so the slit is invisible to the visibility map; it
only turns the annulus `box \ C` into a disk `dom = box \ (C ∪ slit)`, so that *every* chord
separates (`Chazelle.Chain.Separation`).

* `box_sdiff_set_connected`: `box r \ C.set` is connected for `r > coordBound P` (clamp the
  connected set `C.setᶜ` into the box).
* `dom_connected`: `dom` is connected (the four corridors of the box around the chain lie in one
  piece of any separation of `dom`, and the slit is a limit of the corridor above the chain).
-/
namespace Chazelle
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp)

/-- A subchain of a polygon `P`: the `m` consecutive edges `s, s+1, …, s+m-1` (indices modulo
`P.n`), with `1 ≤ m ≤ P.n - 1` so that at least one edge of `P` is missing. -/
structure Chain where
  /-- The ambient polygon. -/
  P : Polygon
  /-- The index of the first edge of the chain. -/
  s : ℕ
  /-- The number of edges of the chain. -/
  m : ℕ
  /-- At least one edge. -/
  one_le : 1 ≤ m
  /-- At least one edge of `P` is missing. -/
  add_one_le : m + 1 ≤ P.n
namespace Chain
variable (C : Chain)
theorem n_pos : 0 < C.P.n := by have := C.add_one_le; omega
theorem m_lt : C.m < C.P.n := by have := C.add_one_le; omega

/-- The index in `P` of the `k`-th edge of the chain. -/
def edgeIdx (k : ℕ) : ℕ := zttw % C.P.n
theorem edgeIdx_lt (k : ℕ) : C.edgeIdx k < C.P.n := Nat.mod_lt _ C.n_pos
theorem edgeIdx_succ (k : ℕ) : ztlec % C.P.n = C.edgeIdx zts :=
  Existence.mod_add_one_mod _ _ _

/-- The `k`-th vertex of the chain (`k = 0, …, m`). -/
def vertex (k : ℕ) : Point := C.P.vtx zthqt

/-- The `k`-th edge of the chain (`k = 0, …, m - 1`), as a set. -/
def chainEdge (k : ℕ) : Set Point := C.P.edge zthqt
theorem chainEdge_eq (k : ℕ) :
    C.chainEdge k = Chazelle.segment ztib ztwkj := by
  unfold chainEdge Polygon.edge vertex
  zummh

/-- The point set of the chain: the union of its edges. -/
def set : Set Point := {p | ∃ k, k < C.m ∧ p ∈ C.chainEdge k}

/-- The vertices of the chain. -/
def vertices : Set Point := {p | ∃ k, k ≤ C.m ∧ p = C.vertex k}
theorem chainEdge_subset_boundary (k : ℕ) : C.chainEdge k ⊆ C.P.boundary :=
  Existence.edge_subset_boundary C.P ztcsx

/-- The chain lies on the boundary of `P`. -/
theorem set_subset_boundary : C.set ⊆ C.P.boundary := by
  rintro p ⟨k, -, hp⟩
  exact C.chainEdge_subset_boundary k hp
theorem set_eq_biUnion : C.set = ⋃ k ∈ Finset.range C.m, C.chainEdge k := by
  zufj
  simp [set, Finset.mem_range]

/-- The chain is a closed set. -/
theorem isClosed_set : IsClosed C.set := by
  rw [set_eq_biUnion]
  exact isClosed_biUnion_finset fun k _ => isClosed_edge C.P _

/-- The complement of the chain is open. -/
theorem isOpen_compl : IsOpen C.setᶜ := C.isClosed_set.isOpen_compl
theorem vertex_mem_chainEdge (k : ℕ) : C.vertex k ∈ C.chainEdge k := by
  rw [chainEdge_eq]; exact Geometry.left_mem_segment _ _
theorem vertex_succ_mem_chainEdge (k : ℕ) : C.vertex zts ∈ C.chainEdge k := by
  rw [chainEdge_eq]; exact Geometry.right_mem_segment _ _
variable {k : ℕ} {p : Point} {j : ℕ} {r : ℝ}
/-- Every vertex of the chain lies on the chain. -/
theorem vertex_mem_set (hk : k ≤ C.m) : C.vertex k ∈ C.set := by
  rcases Nat.lt_or_ge k C.m with h | h
  · exact ⟨k, h, C.vertex_mem_chainEdge k⟩
  · have hkm : k = C.m := by_omega
    subst hkm
    refine ⟨C.m - 1, by have := C.one_le; omega, ?_⟩
    have := C.vertex_succ_mem_chainEdge ztdfi
    rwa [Nat.sub_add_cancel C.one_le] at this

/-- Coordinates of chain points are bounded by `coordBound P`. -/
theorem abs_le_coordBound_of_mem_set (hp : p ∈ C.set) :
    |p.1| ≤ coordBound C.P ∧ |p.2| ≤ coordBound C.P :=
  abs_le_coordBound_of_mem_boundary C.P (C.set_subset_boundary hp)
theorem coordBound_nonneg : 0 ≤ coordBound C.P :=
  Finset.sum_nonneg by_grind

/-! ### The missing edge -/

/-- The index of the edge of `P` following the chain; it is not an edge of the chain. -/
def missingIdx : ℕ := C.edgeIdx C.m
theorem missingIdx_lt : C.missingIdx < C.P.n := C.edgeIdx_lt _

/-- No chain edge is the missing edge. -/
theorem edgeIdx_ne_missingIdx (hk : k < C.m) : C.edgeIdx k ≠ C.missingIdx := by
  zuq
  unfold missingIdx edgeIdx at h
  zumaz
  zuftc
  have := Nat.ModEq.eq_of_lt_of_lt h2 (by have := C.m_lt; omega) C.m_lt
  omega

/-- The relative interior of the missing edge is off the chain. -/
theorem missing_open_not_mem_set (hP : C.P.Simple) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    lerp ztuwz ztkpx t ∉ C.set := by
  rintro ⟨k, hk, hmem⟩
  exact simple_openEdge_not_mem_other hP C.missingIdx_lt ht ztcsx
    (C.edgeIdx_ne_missingIdx hk) hmem

/-- The midpoint of the missing edge. -/
noncomputable def missingMid : Point :=
  lerp ztuwz ztkpx ztcn
theorem missingMid_mem_boundary : C.missingMid ∈ C.P.boundary :=
  ⟨C.missingIdx, C.missingIdx_lt, Geometry.lerp_mem_segment _ _ by_norm_num by_norm_num⟩
theorem missingMid_not_mem_set (hP : C.P.Simple) : C.missingMid ∉ C.set :=
  C.missing_open_not_mem_set hP by_grind

/-! ### Connectedness of the complement -/

/-- **The complement of a simple open chain is connected.** -/
theorem compl_connected (hP : C.P.Simple) : IsPreconnected C.setᶜ := by
  set q := C.missingMid with hq
  have hqb := C.missingMid_mem_boundary
  have hqC := C.missingMid_not_mem_set hP
  set I := C.P.filled \ C.P.boundary with hI
  set E := C.P.filledᶜ with hE
  have hIq :=
    (filled_sdiff_boundary_connected hP).subset_closure subset_union_left
      (union_subset subset_closure
        (singleton_subset_iff.2 (boundary_subset_closure_interior hP hqb)))
  have hEq :=
    (filled_compl_connected hP).subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.2 (boundary_subset_closure_compl hP hqb)))
  have hU : IsPreconnected (I ∪ {q} ∪ (E ∪ {q})) :=
    hIq.union q by_simp by_simp hEq
  refine hU.subset_closure ?_ ?_
  · rintro p ((hp | hp) | (hp | hp))
    · exact fun h => hp.2 ztuxg
    · simp_all
    · exact fun h => hp (boundary_subset_filled _ ztuxg)
    simp_all
  · zuda
    by_cases hb : p ∈ C.P.boundary
    · exact closure_mono (subset_union_left.trans subset_union_left)
        (boundary_subset_closure_interior hP hb)
    · by_cases hf : p ∈ C.P.filled
      · exact subset_closure by_simp_all
      · exact subset_closure by_simp_all

/-! ### The topmost vertex -/
theorem exists_top : ∃ k, k ≤ C.m ∧ ∀ j, j ≤ C.m → (C.vertex j).2 ≤ (C.vertex k).2 := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image ztbaea
    ztmjt ztufo
  refine ⟨k, by_simp_all, fun j hj => hmax j ?_⟩
  simp_all

/-- The index of a topmost vertex of the chain: the **least** such index (`Nat.find`), so that it
is determined by the vertex sequence and computable by a left-to-right scan (review finding F7,
`Core.TopIdxSpec`). -/
noncomputable def topIdx : ℕ := by
  classical
  exact Nat.find C.exists_top
theorem topIdx_spec : C.topIdx ≤ C.m ∧ ∀ j, j ≤ C.m → (C.vertex j).2 ≤ (C.vertex C.topIdx).2 := by
  classical
  unfold topIdx
  convert Nat.find_spec C.exists_top
theorem topIdx_le : C.topIdx ≤ C.m := C.topIdx_spec.1

/-- `topIdx` is the least index of a topmost vertex. -/
theorem topIdx_min (hj : j ≤ C.m) (htop : ∀ i, i ≤ C.m → (C.vertex i).2 ≤ (C.vertex j).2) :
    C.topIdx ≤ j := by
  classical
  unfold topIdx
  convert Nat.find_min' C.exists_top ⟨hj, htop⟩

/-- A topmost vertex of the chain. -/
noncomputable def top : Point := C.vertex C.topIdx
theorem vertex_snd_le_top (hj : j ≤ C.m) : (C.vertex j).2 ≤ C.top.2 :=
  C.topIdx_spec.2 j hj
theorem top_mem_set : C.top ∈ C.set := C.vertex_mem_set C.topIdx_le

/-- Every point of the chain is at height at most `top.2`. -/
theorem snd_le_top_of_mem_set (hp : p ∈ C.set) : p.2 ≤ C.top.2 := by
  obtain ⟨k, hk, hp⟩ := hp
  rw [chainEdge_eq] at hp
  zufkr
  have h1 := C.vertex_snd_le_top (j := k) by_omega
  have h2 := C.vertex_snd_le_top (j := k + 1) by_omega
  show (C.vertex k).2 + s * ztjcb ≤ C.top.2
  nlinarith

/-! ### The box -/

/-- The open square of half-side `r` centred at the origin. -/
def box (r : ℝ) : Set Point := {p | |p.1| < r ∧ |p.2| < r}
theorem mem_box_iff {p : Point} : p ∈ box r ↔ |p.1| < r ∧ |p.2| < r := Iff.rfl
theorem isOpen_box (r : ℝ) : IsOpen ztvfr := by
  have : box r = (fun p : Point => p.1) ⁻¹' Ioo (-r) r ∩ (fun p : Point => p.2) ⁻¹' Ioo (-r) r := by
    zuhcz
  zubk
  exact (isOpen_Ioo.preimage continuous_fst).inter (isOpen_Ioo.preimage continuous_snd)
theorem convex_box (r : ℝ) : Convex ℝ ztvfr := by
  have : box r = ({x : Point | -r < x.1} ∩ {x | x.1 < r}) ∩ ({x | -r < x.2} ∩ {x | x.2 < r}) := by
    zuhcz
  zubk
  exact ((convex_fst_gt _).inter ztqjy).inter ((convex_snd_gt _).inter ztvlp)

/-- Clamp a real number into `[-r, r]`. -/
def clampR (r a : ℝ) : ℝ := max (-r) (min r a)
theorem continuous_clampR (r : ℝ) : Continuous (clampR r) :=
  continuous_const.max (continuous_const.min continuous_id)
theorem abs_clampR_le (hr : 0 ≤ r) (a : ℝ) : |clampR r a| ≤ r := by
  zulug
theorem clampR_eq_self {r a : ℝ} (h : |a| ≤ r) : clampR r a = a := by
  zulug
theorem abs_clampR_eq {r a : ℝ} (hr : 0 ≤ r) (h : r < |a|) : |clampR r a| = r := by
  zulug

/-- Clamp a point into the closed square of half-side `r`. -/
def clampPt (r : ℝ) (p : Point) : Point := (clampR r p.1, clampR r p.2)
theorem continuous_clampPt (r : ℝ) : Continuous (clampPt r) :=
  ((continuous_clampR r).comp continuous_fst).prodMk ((continuous_clampR r).comp continuous_snd)
theorem clampPt_eq_self {p : Point} (h1 : |p.1| ≤ r) (h2 : |p.2| ≤ r) :
    clampPt r p = p := by
  unfold clampPt
  rw [clampR_eq_self h1, clampR_eq_self h2]

/-- **The box minus the chain is connected**, for any box strictly larger than the coordinate
bound: clamping maps the connected set `C.setᶜ` into `box r \ C.set`. -/
theorem box_sdiff_set_connected (hP : C.P.Simple) {r : ℝ} (hr : coordBound C.P < r) :
    IsPreconnected (box r \ C.set) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  set B := coordBound C.P with hB
  set r' := (max (max |x.1| |x.2|) ztkwt + r) / 2 with hr'
  have hx1 := hx.1.1
  have hx2 := hx.1.2
  have hy1 := hy.1.1
  have hy2 := hy.1.2
  have hmax : max (max |x.1| |x.2|) ztkwt < r :=
    by simp_all
  have hr'r : r' < r := by_grind
  have hBr' : B < r' := by
    grind
  have hx1' : |x.1| ≤ r' := by
    grind
  have hx2' : |x.2| ≤ r' := by
    grind
  have hy1' : |y.1| ≤ r' := by
    grind
  have hy2' : |y.2| ≤ r' := by
    grind
  have hr'0 := (C.coordBound_nonneg.trans hBr'.le)
  refine ⟨clampPt r' '' C.setᶜ, ?_, ?_, ?_,
    (C.compl_connected hP).image _ (continuous_clampPt r').continuousOn⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨lt_of_le_of_lt zttew hr'r,
      lt_of_le_of_lt zttew hr'r⟩, ?_⟩
    zuhgp
    by_cases hin : |p.1| ≤ r' ∧ |p.2| ≤ r'
    · rw [clampPt_eq_self hin.1 hin.2] at hmem
      grind
    · have hcoord := C.abs_le_coordBound_of_mem_set hmem
      simp only [clampPt] at hcoord
      rcases not_and_or.1 hin with h | h
      · zuhko

      · zuhko

  · exact ⟨x, hx.2, clampPt_eq_self hx1' hx2'⟩
  · exact ⟨y, hy.2, clampPt_eq_self hy1' hy2'⟩

/-! ### The radius, the slit and the domain -/

/-- The half-side of the box: one more than the coordinate bound of `P`. -/
noncomputable def radius : ℝ := coordBound C.P + 1
theorem coordBound_lt_radius : coordBound C.P < C.radius := by
  unfold radius; linarith
theorem radius_pos : 0 < C.radius := lt_of_le_of_lt C.coordBound_nonneg C.coordBound_lt_radius

/-- The chain lies inside the box. -/
theorem set_subset_box : C.set ⊆ box C.radius := fun _ hp =>
  ⟨lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).1 C.coordBound_lt_radius,
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).2 C.coordBound_lt_radius⟩
theorem top_mem_box : C.top ∈ box C.radius := C.set_subset_box C.top_mem_set

/-- The top end of the slit, on the top side of the box. -/
noncomputable def slitTop : Point := ztnka

/-- The slit: the vertical segment from the topmost vertex to the top side of the box. -/
noncomputable def slit : Set Point := Chazelle.segment C.top C.slitTop
theorem top_snd_lt_radius : C.top.2 < C.radius :=
  lt_of_le_of_lt (abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).2).2
    C.coordBound_lt_radius
theorem mem_slit_iff :
    p ∈ C.slit ↔ p.1 = C.top.1 ∧ C.top.2 ≤ p.2 ∧ p.2 ≤ C.radius := by
  have hlt := C.top_snd_lt_radius
  constructor
  · zulmw
    refine ⟨fst_eq_of_mem_segment_vertical (v := C.slitTop) rfl hp, ?_⟩
    zufkv
    show C.top.2 ≤ C.top.2 + t * ztswc ∧
      C.top.2 + t * ztswc ≤ C.radius
    simp only [slitTop]
    zueop
  · zuei
    exact mem_segment_of_vertical rfl h1 h2 h3

/-- The obstacle: the chain together with the slit. -/
noncomputable def obstacle : Set Point := C.set ∪ C.slit

/-- The domain of the model: the open box minus the chain and the slit. -/
noncomputable def dom : Set Point := box C.radius \ C.obstacle
theorem isClosed_obstacle : IsClosed C.obstacle :=
  C.isClosed_set.union (Geometry.isClosed_segment _ _)
theorem isOpen_dom : IsOpen C.dom := (isOpen_box _).sdiff C.isClosed_obstacle
theorem isClosed_dom_compl : IsClosed C.domᶜ := C.isOpen_dom.isClosed_compl
theorem dom_subset_box : C.dom ⊆ box C.radius := fun _ h => h.1
theorem mem_dom_iff : p ∈ C.dom ↔ p ∈ box C.radius ∧ p ∉ C.set ∧ p ∉ C.slit := by
  simp only [dom, obstacle, Set.mem_sdiff, mem_union, not_or]
theorem not_mem_set_of_mem_dom (hp : p ∈ C.dom) : p ∉ C.set :=
  (C.mem_dom_iff.1 hp).2.1
theorem not_mem_slit_of_mem_dom (hp : p ∈ C.dom) : p ∉ C.slit :=
  (C.mem_dom_iff.1 hp).2.2
theorem set_subset_dom_compl : C.set ⊆ C.domᶜ := fun _ hp hd => C.not_mem_set_of_mem_dom hd hp
theorem slit_subset_dom_compl : C.slit ⊆ C.domᶜ := fun _ hp hd => C.not_mem_slit_of_mem_dom hd hp

/-- Points of the box above the coordinate bound are in the domain. -/
theorem mem_dom_of_high (hp : p ∈ box C.radius) (hy : coordBound C.P < p.2)
    (hx : p.1 ≠ C.top.1) : p ∈ C.dom := by
  rw [mem_dom_iff]
  refine ⟨hp, fun h => ?_, fun h => hx (C.mem_slit_iff.1 h).1⟩
  have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).2).2
  linarith

/-- The domain is nonempty. -/
theorem dom_nonempty : C.dom.Nonempty := by
  refine ⟨(ztlmi / 2, ztlmi / 2), ?_⟩
  have hB := C.coordBound_nonneg
  have hBr := C.coordBound_lt_radius
  have htop := (abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).1).2
  refine C.mem_dom_of_high ztcp by_grind by_grind
  · grind
  grind

/-! ### Corridors of the box around the chain -/

/-- The part of the box strictly above the chain. -/
noncomputable def upper : Set Point := box C.radius ∩ {p | C.top.2 < p.2}
theorem isOpen_upper : IsOpen C.upper :=
  (isOpen_box _).inter ztetr

/-- The left corridor: the part of the box to the left of every chain point. -/
noncomputable def corrL : Set Point := box C.radius ∩ {p | p.1 < -coordBound C.P}

/-- The right corridor. -/
noncomputable def corrR : Set Point := box C.radius ∩ {p | coordBound C.P < p.1}

/-- The bottom corridor. -/
noncomputable def corrB : Set Point := box C.radius ∩ {p | p.2 < -coordBound C.P}

/-- The upper corridor, left of the slit. -/
noncomputable def upperL : Set Point := C.upper ∩ {p | p.1 < C.top.1}

/-- The upper corridor, right of the slit. -/
noncomputable def upperR : Set Point := C.upper ∩ {p | C.top.1 < p.1}
theorem convex_upper : Convex ℝ C.upper := (convex_box _).inter (convex_snd_gt _)
theorem convex_corrL : Convex ℝ C.corrL := (convex_box _).inter ztqjy
theorem convex_corrR : Convex ℝ C.corrR := (convex_box _).inter ztvlo
theorem convex_corrB : Convex ℝ C.corrB := (convex_box _).inter ztvlp
theorem convex_upperL : Convex ℝ C.upperL := C.convex_upper.inter ztqjy
theorem convex_upperR : Convex ℝ C.upperR := C.convex_upper.inter ztvlo
theorem abs_top_fst_le : |C.top.1| ≤ coordBound C.P :=
  (C.abs_le_coordBound_of_mem_set C.top_mem_set).1
theorem abs_top_snd_le : |C.top.2| ≤ coordBound C.P :=
  (C.abs_le_coordBound_of_mem_set C.top_mem_set).2
theorem corrL_subset_dom : C.corrL ⊆ C.dom := by
  rintro p ⟨hp, hx⟩
  simp only [mem_ofPred_eq] at hx
  zqbij
  · have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).1).1
    linarith
  · zqbik
    have := (abs_le.1 C.abs_top_fst_le).1
    linarith
theorem corrR_subset_dom : C.corrR ⊆ C.dom := by
  rintro p ⟨hp, hx⟩
  simp only [mem_ofPred_eq] at hx
  zqbij
  · have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).1).2
    linarith
  · zqbik
    have := (abs_le.1 C.abs_top_fst_le).2
    linarith
theorem corrB_subset_dom : C.corrB ⊆ C.dom := by
  rintro p ⟨hp, hy⟩
  simp only [mem_ofPred_eq] at hy
  zqbij
  · have := (abs_le.1 (C.abs_le_coordBound_of_mem_set h).2).1
    linarith
  · have h1 := (C.mem_slit_iff.1 h).2.1
    have := (abs_le.1 C.abs_top_snd_le).1
    linarith
theorem upperL_subset_dom : C.upperL ⊆ C.dom := by
  zqbim
  zqbij
  · have := C.snd_le_top_of_mem_set h
    linarith
  · zqbik
    linarith
theorem upperR_subset_dom : C.upperR ⊆ C.dom := by
  zqbim
  zqbij
  · have := C.snd_le_top_of_mem_set h
    linarith
  · zqbik
    linarith

/-- The midpoint radius `(B + R)/2`, used to name points of the corridors. -/
noncomputable def midR : ℝ := ztlmi / 2
theorem coordBound_lt_midR : coordBound C.P < C.midR := by
  zujqp
theorem midR_lt_radius : C.midR < C.radius := by
  zujqp
theorem midR_pos : 0 < C.midR := lt_of_le_of_lt C.coordBound_nonneg C.coordBound_lt_midR
theorem abs_midR : |C.midR| = C.midR := abs_of_pos C.midR_pos
theorem abs_neg_midR : |-C.midR| = C.midR := by rw [abs_neg, abs_midR]
theorem upperL_inter_corrL : (C.upperL ∩ C.corrL).Nonempty := by
  zqbil
  have h3 := (abs_le.1 C.abs_top_fst_le).1
  zuhwd
  refine ⟨(-C.midR, C.midR), ztbarz, ztwub⟩ <;>
    zught
theorem corrL_inter_corrB : (C.corrL ∩ C.corrB).Nonempty := by
  zqbil
  refine ⟨(-C.midR, -C.midR), ztwub, ztwub⟩ <;>
    simp only [mem_ofPred_eq, abs_neg_midR] <;> linarith
theorem corrB_inter_corrR : (C.corrB ∩ C.corrR).Nonempty := by
  zqbil
  refine ⟨(C.midR, -C.midR), ztwub, ztwub⟩ <;>
    zught
theorem corrR_inter_upperR : (C.corrR ∩ C.upperR).Nonempty := by
  zqbil
  have h3 := (abs_le.1 C.abs_top_fst_le).2
  zuhwd
  refine ⟨(C.midR, C.midR), ztwub, ztbarz⟩ <;>
    simp only [mem_ofPred_eq, abs_midR] <;> linarith

/-- A point of the open slit is a limit of points of the upper-left corridor. -/
theorem slit_mem_closure_upperL (hp : p ∈ box C.radius) (hp1 : p.1 = C.top.1)
    (hp2 : C.top.2 < p.2) : p ∈ closure C.upperL := by
  have hcont : Continuous fun δ : ℝ => ((p.1 - δ, p.2) : Point) := by fun_prop
  have htend : Tendsto (fun δ : ℝ => ((p.1 - δ, p.2) : Point)) (𝓝[>] 0) (𝓝 p) := by
    have := hcont.tendsto 0
    zujoz
    zuhv
  zucyz
  have hε : 0 < C.radius - |p.1| := by linarith [hp.1]
  filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
  refine ⟨⟨⟨?_, hp.2⟩, ?_⟩, ?_⟩
  · grind
  · simp_all
  simp_all

/-- A convex subset of a set with no separation crossing lies on one side. -/
theorem convex_side {u v D K : Set Point} (hu : IsOpen u) (hv : IsOpen v) (hK : Convex ℝ K)
    (hKD : K ⊆ D) (hcov : D ⊆ u ∪ v) (hempty : D ∩ ztdwk = ∅) : K ⊆ u ∨ K ⊆ v := by
  by_cases hKu : (K ∩ u).Nonempty
  · by_cases hKv : (K ∩ v).Nonempty
    · exfalso
      obtain ⟨p, hpK, hpuv⟩ := hK.isPreconnected u v hu hv (hKD.trans hcov) hKu hKv
      zujvz

    · left
      zuda
      zujdr
      · zubh
      · exact absurd ztrdw hKv
  · right
    zuda
    zujdr
    · exact absurd ztrdw hKu
    omega

/-- Two convex pieces of `D` that meet lie on the same side of a separation. -/
theorem convex_same_side {u v D K K' : Set Point} (hu : IsOpen u) (hv : IsOpen v)
    (hK' : Convex ℝ K') (hK'D : K' ⊆ D) (hcov : D ⊆ u ∪ v) (hempty : D ∩ ztdwk = ∅)
    (hmeet : (K ∩ K').Nonempty) (hKu : K ⊆ u) (hKD : K ⊆ D) : K' ⊆ u := by
  rcases convex_side hu hv hK' hK'D hcov hempty with h | h
  · zubh
  · exfalso
    obtain ⟨p, hpK, hpK'⟩ := hmeet
    zujvz

/-- The core of the connectedness argument: if both halves of the upper corridor lie in `u`,
then `u, v` cannot separate the domain. -/
theorem dom_connected_aux (hP : C.P.Simple) {u v : Set Point} (hu : IsOpen u) (hv : IsOpen v)
    (hcov : C.dom ⊆ u ∪ v) (hne : (C.dom ∩ v).Nonempty) (hempty : C.dom ∩ ztdwk = ∅)
    (hL : C.upperL ⊆ u) (hR : C.upperR ⊆ u) : False := by
  have hD0 := C.box_sdiff_set_connected hP C.coordBound_lt_radius
  have hdom0 : C.dom ⊆ box C.radius \ C.set := fun p hp => ⟨hp.1, C.not_mem_set_of_mem_dom hp⟩
  have hcov0 : box C.radius \ C.set ⊆ ztoja ∪ v := by
    zuco
    zujts
    · left; right
      obtain ⟨hq1, hq2, -⟩ := C.mem_slit_iff.1 hqs
      refine ⟨hq.1, ?_⟩
      zuwb
      rcases hq2.lt_or_eq with h | h
      · zubh
      · exfalso
        apply hq.2
        have : q = C.top := by_grind
        zudaq
    · rcases hcov (C.mem_dom_iff.2 ⟨hq.1, hq.2, hqs⟩) with h | h
      · simp_all
      simp_all
  have hne0 : (ztrkx ∩ ztoja).Nonempty := by
    obtain ⟨q, hq⟩ := C.upperL_inter_corrL
    exact ⟨q, hdom0 (C.upperL_subset_dom hq.1), by_grind⟩
  have hne1 : (ztrkx ∩ v).Nonempty := by
    obtain ⟨q, hq1, hq2⟩ := hne
    exact ⟨q, hdom0 hq1, hq2⟩
  obtain ⟨p, hp0, hpu, hpv⟩ := hD0 ztoja v (hu.union C.isOpen_upper) hv hcov0 hne0 hne1
  by_cases hpD : p ∈ C.dom
  · rcases hpu with hpu | hpu
    · zujvy

    · -- `p` is in the upper corridor and off the slit: in one of the two halves
      have hslit := C.not_mem_slit_of_mem_dom hpD
      have hy := hpu.2
      have hx : p.1 ≠ C.top.1 := by
        zuetb
        exact hslit (C.mem_slit_iff.2 ⟨hx, hy.le, (abs_le.1 hpu.1.2.le).2⟩)
      have hpu' : p ∈ u := by
        rcases lt_or_gt_of_ne hx with h | h
        · tauto
        tauto
      zujvy

  · -- `p` is on the open slit: a nearby point of the upper-left corridor is in `v`
    have hpslit : p ∈ C.slit := by
      zumv
      exact hpD ztuxe
    obtain ⟨hp1, hp2, -⟩ := C.mem_slit_iff.1 hpslit
    have hp2' : C.top.2 < p.2 := by
      rcases hp2.lt_or_eq with h | h
      · zubh
      · exfalso
        apply hp0.2
        zuhdk
        zudaq
    have hcl := C.slit_mem_closure_upperL hp0.1 hp1 hp2'
    obtain ⟨q, hqv, hqU⟩ := mem_closure_iff.1 hcl v hv hpv
    have : q ∈ C.dom ∩ ztdwk := ⟨C.upperL_subset_dom hqU, hL hqU, hqv⟩
    simp_all

/-- **The domain is connected.** -/
theorem dom_connected (hP : C.P.Simple) : IsPreconnected C.dom := by
  intro u v hu hv hcov hneu hnev
  by_contra hempty'
  have hempty := not_nonempty_iff_eq_empty.1 hempty'
  -- the chain of corridors lies on one side
  have hchain : ∀ w w' : Set Point, IsOpen w → IsOpen w' → C.dom ⊆ w ∪ w' →
      C.dom ∩ (w ∩ w') = ∅ → C.upperL ⊆ w → C.upperR ⊆ w := by
    intro w w' hw hw' hcov' hempty' hL
    have h1 := convex_same_side hw hw' C.convex_corrL C.corrL_subset_dom hcov'
      hempty' C.upperL_inter_corrL hL C.upperL_subset_dom
    have h2 := convex_same_side hw hw' C.convex_corrB C.corrB_subset_dom hcov'
      hempty' C.corrL_inter_corrB h1 C.corrL_subset_dom
    have h3 := convex_same_side hw hw' C.convex_corrR C.corrR_subset_dom hcov'
      hempty' C.corrB_inter_corrR h2 C.corrB_subset_dom
    exact convex_same_side hw hw' C.convex_upperR C.upperR_subset_dom hcov' hempty'
      C.corrR_inter_upperR h3 C.corrR_subset_dom
  have hempty_symm : C.dom ∩ (v ∩ u) = ∅ := by_grind
  have hcov_symm : C.dom ⊆ v ∪ u := by_grind
  rcases convex_side hu hv C.convex_upperL C.upperL_subset_dom hcov hempty with hL | hL
  · exact C.dom_connected_aux hP hu hv hcov hnev hempty hL by_grind
  · exact C.dom_connected_aux hP hv hu hcov_symm hneu hempty_symm hL
      by_grind
