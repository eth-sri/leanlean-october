/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.HorizontalStrip
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Topology.DiscreteSubset
import DOZZ.ShiftEquations.Quotient.Walk
import DOZZ.Complex.Basic
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# Whole-plane factorization from two incommensurable shift laws

This is the final quotient argument of [KRV, §11], for abstract total functions. Let `C` be
meromorphic on the strip `S_h` and `D` meromorphic there and nonzero off a codiscrete set, and
suppose that both obey the two shift laws `F(z + b) = K₁(z) F(z - b)` and
`F(z + b') = K₂(z) F(z - b')` with the same multipliers, off a codiscrete subset of the whole plane,
with `b / b'` irrational. Then `C = c D` off a codiscrete subset of the plane, inside the strip.

Inside the strip `C / D` has the incommensurable periods `2b, 2b'`, hence is a constant germ `c`
(the dense-period theorem). The discrepancy set `E = {z ∈ S_h : C z ≠ c D z}` therefore has no
accumulation point in `S_h`. It has none on the boundary lines either: near a boundary point every
horizontal line close to the boundary avoids the exceptional set of the shift laws over a long
segment, and on such a line a discrepancy is transported along bounded walks with steps
`±2b, ±2b'` to the dense set of translates by the period group, which would make `E` infinite on a
compact segment of `S_h`.
-/

public section

open Filter Set Topology Metric

namespace DOZZ.Proofs

/-- One shift law transports the discrepancy `C - c D` across a step. -/
theorem shift_discrepancy_eq {C D : ℂ → ℂ} {K c u B : ℂ}
    (hC : C (u + B) = K * C (u - B)) (hD : D (u + B) = K * D (u - B)) :
    C (u + B) - c * D (u + B) = K * (C (u - B) - c * D (u - B)) := by
  grind
section
variable {C D K₁ K₂ : ℂ → ℂ}

/-- **Propagation along a bounded walk.** If both shift laws hold with nonzero multipliers at every
point of a horizontal segment through `x₀`, a nonzero discrepancy at `x₀` stays nonzero along a
walk with steps `±2b, ±2b'` whose midpoints stay in the segment. -/
theorem discrepancy_ne_zero_along_walk {b b' ρ : ℝ} {c x₀ : ℂ}
    (hb : 0 < b) (hb' : 0 < b')
    (hgood : ∀ m : ℂ, m.im = x₀.im → |m.re - x₀.re| ≤ ρ →
      (C (m + b) = K₁ m * C (m - b) ∧ D (m + b) = K₁ m * D (m - b) ∧ K₁ m ≠ 0) ∧
      (C (m + b') = K₂ m * C (m - b') ∧ D (m + b') = K₂ m * D (m - b') ∧ K₂ m ≠ 0))
    (l : List ℝ) (hl : ∀ e ∈ l, e = 2 * b ∨ e = -(2 * b) ∨ e = 2 * b' ∨ e = -(2 * b'))
    (hbound : ∀ k ≤ l.length, |(l.take k).sum| + max b b' ≤ ρ)
    (h0 : C x₀ - c * D x₀ ≠ 0) :
    C (x₀ + (l.sum : ℂ)) - c * D (x₀ + (l.sum : ℂ)) ≠ 0 := by
  -- discrepancy at the `k`-th position
  have hstep : ∀ k, k ≤ l.length →
      C (x₀ + ((l.take k).sum : ℂ)) - c * D (x₀ + ((l.take k).sum : ℂ)) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      have hkl : k < l.length := hk
      have ih' := ih hkl.le
      set s := (l.take k).sum with hs
      set u := x₀ + (s : ℂ) with hu
      have hsum : (l.take (k + 1)).sum = s + l[k] := by simp_all
      have hmem : l[k] ∈ l := List.getElem_mem hkl
      have hbk := hbound k hkl.le
      have hbmax : b ≤ max b b' := le_max_left b b'
      have hbmax' : b' ≤ max b b' := le_max_right b b'
      have him : ∀ t : ℝ, (u + (t : ℂ)).im = x₀.im := fun t => by simp_all
      have hre : ∀ t : ℝ, (u + (t : ℂ)).re - x₀.re = s + t := fun t => by simp [hu]; ring
      rw [hsum, Complex.ofReal_add, ← add_assoc, ← hu]
      rcases hl _ hmem with he | he | he | he
      · -- step `+2b`, midpoint `u + b`
        have hm := (hgood _ (him b) (by
          rw [hre]; calc |s + b| ≤ |s| + |b| := abs_add_le _ _
            _ = |s| + b := by rw [abs_of_pos hb]
            _ ≤ ρ := by linarith)).1
        rw [he, show ((2 * b : ℝ) : ℂ) = (b : ℂ) + b by push_cast; ring, ← add_assoc, (shift_discrepancy_eq (c := c) hm.1 hm.2.1),
          add_sub_cancel_right]
        simp_all
      · -- step `-2b`, midpoint `u - b`
        have hm := (hgood (u + ((-b : ℝ) : ℂ)) (him (-b)) (by
          rw [hre]; calc |s + -b| ≤ |s| + |-b| := abs_add_le _ _
            _ = |s| + b := by rw [abs_neg, abs_of_pos hb]
            _ ≤ ρ := by linarith)).1
        have e := shift_discrepancy_eq (c := c) hm.1 hm.2.1
        rw [show u + ((-b : ℝ) : ℂ) + (b : ℂ) = u by simp] at e
        rw [he, show u + ((-(2 * b) : ℝ) : ℂ) = u + ((-b : ℝ) : ℂ) - b by push_cast; ring]
        intro hz
        rw [hz, mul_zero] at e
        exact ih' e
      · -- step `+2b'`, midpoint `u + b'`
        have hm := (hgood _ (him b') (by
          rw [hre]; calc |s + b'| ≤ |s| + |b'| := abs_add_le _ _
            _ = |s| + b' := by rw [abs_of_pos hb']
            _ ≤ ρ := by linarith)).2
        rw [he, show ((2 * b' : ℝ) : ℂ) = (b' : ℂ) + b' by push_cast; ring, ← add_assoc, (shift_discrepancy_eq (c := c) hm.1 hm.2.1),
          add_sub_cancel_right]
        exact mul_ne_zero hm.2.2 ih'
      · -- step `-2b'`, midpoint `u - b'`
        have hm := (hgood (u + ((-b' : ℝ) : ℂ)) (him (-b')) (by
          rw [hre]; calc |s + -b'| ≤ |s| + |-b'| := abs_add_le _ _
            _ = |s| + b' := by rw [abs_neg, abs_of_pos hb']
            _ ≤ ρ := by linarith)).2
        have e := shift_discrepancy_eq (c := c) hm.1 hm.2.1
        rw [show u + ((-b' : ℝ) : ℂ) + (b' : ℂ) = u by push_cast; ring] at e
        rw [he, show u + ((-(2 * b') : ℝ) : ℂ) = u + ((-b' : ℝ) : ℂ) - b' by push_cast; ring]
        intro hz
        rw [hz, mul_zero] at e
        exact ih' e
  have := hstep l.length le_rfl
  simp_all

/-- **No accumulation at the boundary.** If the discrepancy `C - c D` vanishes on a punctured
neighborhood of every point of the strip, it vanishes on a full neighborhood of each boundary point,
intersected with the strip. -/
theorem eventually_nhds_boundary_discrepancy {h b b' : ℝ} {c : ℂ}
    (hb : 0 < b) (hb' : 0 < b') (hirr : Irrational (b / b'))
    (hgood : ∀ᶠ z in codiscrete ℂ,
      (C (z + b) = K₁ z * C (z - b) ∧ D (z + b) = K₁ z * D (z - b) ∧ K₁ z ≠ 0) ∧
      (C (z + b') = K₂ z * C (z - b') ∧ D (z + b') = K₂ z * D (z - b') ∧ K₂ z ≠ 0))
    (hin : ∀ z ∈ horizontalStrip h, ∀ᶠ w in 𝓝[≠] z, C w = c * D w)
    (w₀ : ℂ) (hw₀ : |w₀.im| = h) :
    ∀ᶠ x in 𝓝 w₀, x ∈ horizontalStrip h → C x = c * D x := by
  set S := {z | ¬ ((C (z + b) = K₁ z * C (z - b) ∧ D (z + b) = K₁ z * D (z - b) ∧
      K₁ z ≠ 0) ∧ (C (z + b') = K₂ z * C (z - b') ∧ D (z + b') = K₂ z * D (z - b') ∧
      K₂ z ≠ 0))} with hSdef
  have hS : IsClosed S ∧ IsDiscrete S := by
    refine compl_mem_codiscrete_iff.1 ?_
    filter_upwards [hgood] with z hz
    simp_all
  set L : ℝ := 3 * (b + b') + 1 with hL
  set R := L + 2 with hR
  have hF :=
    ((isCompact_closedBall w₀ R).inter_left hS.1).finite (hS.2.mono inter_subset_left)
  -- the imaginary parts of the finitely many exceptional points near `w₀`
  set I := (fun z => z.im) '' (S ∩ closedBall w₀ R) with hIdef
  have hI : ∀ᶠ y in 𝓝 w₀.im, y = w₀.im ∨ y ∉ I := by
    have hcl : IsClosed (I \ {w₀.im}) := ((hF.image _).sdiff).isClosed
    have hnot : w₀.im ∉ I \ {w₀.im} := by simp
    filter_upwards [hcl.isOpen_compl.mem_nhds hnot] with y hy
    by_cases hyt : y = w₀.im <;> tauto
  obtain ⟨ε, hε, hεI⟩ := Metric.eventually_nhds_iff.1 hI
  refine Metric.eventually_nhds_iff.2 ⟨min ε 1, lt_min hε one_pos, fun x hx hxS => ?_⟩
  by_contra hne
  have hdist := hx
  have hxim :=
    lt_of_le_of_lt (by simpa [Complex.dist_eq, ← Complex.sub_im] using
      Complex.abs_im_le_norm _) hdist
  have hxre : |x.re - w₀.re| < min ε 1 :=
    lt_of_le_of_lt (by simpa [Complex.dist_eq, ← Complex.sub_re] using
      Complex.abs_re_le_norm _) hdist
  have hxS' : |x.im| < h := hxS
  have hyne : x.im ≠ w₀.im := by
    intro he
    rw [he, hw₀] at hxS'
    exact lt_irrefl _ hxS'
  have hy_not : x.im ∉ I := (hεI (show dist x.im w₀.im < ε by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hxim (min_le_left ..))).resolve_left hyne
  -- the horizontal segment through `x` is free of exceptional points
  have hline : ∀ m : ℂ, m.im = x.im → |m.re - x.re| ≤ L →
      (C (m + b) = K₁ m * C (m - b) ∧ D (m + b) = K₁ m * D (m - b) ∧ K₁ m ≠ 0) ∧
      (C (m + b') = K₂ m * C (m - b') ∧ D (m + b') = K₂ m * D (m - b') ∧ K₂ m ≠ 0) := by
    intro m hmim hmre
    by_contra hm
    apply hy_not
    refine ⟨m, ⟨hm, ?_⟩, hmim⟩
    rw [mem_closedBall, Complex.dist_eq]
    have h1 : |(m - w₀).re| ≤ L + 1 := by
      rw [Complex.sub_re]
      calc |m.re - w₀.re| = |(m.re - x.re) + (x.re - w₀.re)| := by ring_nf
        _ ≤ |m.re - x.re| + |x.re - w₀.re| := abs_add_le ..
        _ ≤ L + 1 := by grind
    have h2 : |(m - w₀).im| ≤ 1 := by
      rw [Complex.sub_im, hmim]
      exact hxim.le.trans (min_le_right ε 1)
    calc ‖m - w₀‖ ≤ |(m - w₀).re| + |(m - w₀).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ R := by linarith
  -- the discrepancy has finitely many zeros... finitely many nonzeros on a compact segment
  set ℓ : Set ℂ := {z | z.im = x.im ∧ |z.re - x.re| ≤ 1} with hℓdef
  have hℓc : IsCompact ℓ := by
    have hsub : ℓ ⊆ closedBall x 1 := by
      intro z ⟨hzi, hzr⟩
      rw [mem_closedBall, Complex.dist_eq]
      calc ‖z - x‖ ≤ |(z - x).re| + |(z - x).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - x.re| := by simp [hzi]
        _ ≤ 1 := hzr
    refine (isCompact_closedBall x 1).of_isClosed_subset ?_ hsub
    exact (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le ((Complex.continuous_re.sub continuous_const).abs) continuous_const)
  have hℓS : ℓ ⊆ horizontalStrip h := fun z hz => by
    change |z.im| < h
    rwa [hz.1]
  have hEfin : {z | z ∈ ℓ ∧ C z - c * D z ≠ 0}.Finite := by
    by_contra hinf
    obtain ⟨p, hpℓ, hp⟩ :=
      Set.Infinite.exists_accPt_of_subset_isCompact hinf hℓc (fun z hz => hz.1)
    have hp0 :=
      eventually_nhdsWithin_iff.1 (hin p (hℓS hpℓ))
    rw [accPt_iff_frequently] at hp
    obtain ⟨w, ⟨hwp, -, hw⟩, hw'⟩ := (hp.and_eventually hp0).exists
    exact hw (sub_eq_zero.mpr (hw' hwp))
  -- every small element of the period group translates `x` into that finite set
  have hirr2 : Irrational ((2 * b) / (2 * b')) := by
    rwa [mul_div_mul_left _ _ two_ne_zero]
  have hT := infinite_closure_pair_pos_lt hirr2
    (show 0 < min (min (2 * b) (2 * b')) 1 by positivity)
  apply hT
  refine Set.Finite.subset (hEfin.preimage (f := fun g : ℝ => x + (g : ℂ))
    (fun g₁ _ g₂ _ he => by simpa using he)) ?_
  intro g ⟨hgG, hg0, hgε⟩
  have hga : |g| < min (2 * b) (2 * b') := by
    rw [abs_of_pos hg0]; exact lt_of_lt_of_le hgε (min_le_left ..)
  obtain ⟨l, hl, hlsum, hlb⟩ :=
    exists_bounded_walk (by positivity) (by positivity) hgG hg0.ne' hga
  have hwalk := discrepancy_ne_zero_along_walk hb hb'
    (fun m hmim hmre => hline m hmim hmre) l hl
    (fun k hk => by
      have := hlb k hk
      have hmax : max b b' ≤ b + b' := max_le (by linarith) (by linarith)
      linarith) (sub_ne_zero.mpr hne)
  rw [hlsum] at hwalk
  refine ⟨⟨by simp, ?_⟩, hwalk⟩
  simp
  rw [abs_of_pos hg0]
  exact (lt_of_lt_of_le hgε (min_le_right ..)).le

end

/-- A common shift law with nonzero multiplier makes the quotient `C / D` periodic with period
`2T`, off a codiscrete set. -/
theorem eventually_div_add_two_mul_eq {C D K : ℂ → ℂ} {T : ℝ}
    (hlaw : ∀ᶠ z in codiscrete ℂ,
      C (z + T) = K z * C (z - T) ∧ D (z + T) = K z * D (z - T) ∧ K z ≠ 0)
    (hD0 : ∀ᶠ z in codiscrete ℂ, D z ≠ 0) :
    ∀ᶠ w in codiscrete ℂ, C (w + ((2 * T : ℝ) : ℂ)) / D (w + ((2 * T : ℝ) : ℂ)) = C w / D w := by
  filter_upwards [eventually_codiscrete_comp_add hlaw T, hD0] with w hw hDw
  obtain ⟨h1, h2, hK⟩ := hw
  have e : w + ((2 * T : ℝ) : ℂ) = w + T + T := by push_cast; ring
  grind

/-- **Whole-plane factorization.** Two total functions meromorphic on a strip that obey the same two
shift laws with incommensurable half-steps `b, b'` off a codiscrete subset of the plane are
proportional on the strip, off a codiscrete subset of the plane. -/
theorem exists_eventually_eq_const_mul_of_shifts {C D K₁ K₂ : ℂ → ℂ} {h b b' : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hb' : 0 < b') (hirr : Irrational (b / b'))
    (hC : MeromorphicOn C (horizontalStrip h)) (hD : MeromorphicOn D (horizontalStrip h))
    (hD0 : ∀ᶠ z in codiscrete ℂ, D z ≠ 0)
    (hgood : ∀ᶠ z in codiscrete ℂ,
      (C (z + b) = K₁ z * C (z - b) ∧ D (z + b) = K₁ z * D (z - b) ∧ K₁ z ≠ 0) ∧
      (C (z + b') = K₂ z * C (z - b') ∧ D (z + b') = K₂ z * D (z - b') ∧ K₂ z ≠ 0)) :
    ∃ c : ℂ, ∀ᶠ z in codiscrete ℂ, z ∈ horizontalStrip h → C z = c * D z := by
  -- Step 1: the quotient is a constant germ on the strip
  have hp₁ := eventually_div_add_two_mul_eq (hgood.mono fun _ h => h.1) hD0
  have hp₂ := eventually_div_add_two_mul_eq (hgood.mono fun _ h => h.2) hD0
  have hirr2 : ∀ q : ℚ, (2 * b) / (2 * b') ≠ (q : ℝ) := by
    rw [mul_div_mul_left _ _ two_ne_zero]
    tauto
  obtain ⟨c, hc, -⟩ := meromorphicOn_strip_constant_of_dense_periods h hh (fun z => C z / D z)
    (hC.div hD) _ _ (by positivity) (by positivity) hirr2
    (fun z _ => eventually_nhdsNE_of_eventually_codiscrete hp₁ z)
    (fun z _ => eventually_nhdsNE_of_eventually_codiscrete hp₂ z)
  have hin : ∀ z ∈ horizontalStrip h, ∀ᶠ w in 𝓝[≠] z, C w = c * D w := by
    intro z hz
    filter_upwards [hc z hz, eventually_nhdsNE_of_eventually_codiscrete hD0 z] with w hw hDw
    aesop
  -- Steps 2–3: the discrepancy set does not accumulate anywhere in the plane
  refine ⟨c, eventually_codiscrete_iff_forall_eventually_nhdsNE.2 fun x => ?_⟩
  rcases lt_trichotomy |x.im| h with hx | hx | hx
  · filter_upwards [hin x hx] with w hw _ using hw
  · exact nhdsWithin_le_nhds
      (eventually_nhds_boundary_discrepancy hb hb' hirr hgood hin x hx)
  · have hopen : IsOpen {z : ℂ | h < |z.im|} :=
      isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hx)] with w hw hwS
    exact absurd hwS (not_lt.mpr hw.le)

end DOZZ.Proofs

end
