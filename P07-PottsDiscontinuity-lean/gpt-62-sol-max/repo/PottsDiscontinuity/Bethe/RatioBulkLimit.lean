module

public import PottsDiscontinuity.Bethe.CountingQuadrature
public import PottsDiscontinuity.Bethe.RatioLogDifference
public import PottsDiscontinuity.Bethe.RatioPredecessor
public import PottsDiscontinuity.Bethe.RatioScaledIncrement

/-! The Bethe counting derivative gives every interior root gap mass `1/N`.
Integrate the scaled logarithmic difference as a constant on each such gap. -/

@[expose] public section
open Set Filter MeasureTheory Finset
open scoped Topology

namespace PottsDiscontinuity.Bethe

private def gapNext {n : ℕ} (j : Fin n) : Fin n :=
  if h : j.val + 1 < n then ⟨j.val + 1, h⟩ else j

private theorem le_gapNext {n : ℕ} (j : Fin n) : j ≤ gapNext j := by
  unfold gapNext
  grind

private noncomputable def gapTest {n : ℕ} (q v : Fin n → ℝ) (D : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ j, (Ico (q j) (q (gapNext j))).indicator (fun y => v j * D y) x

private theorem gapTest_eq {n : ℕ} (hn : 0 < n) {q : Fin n → ℝ} (hq : StrictMono q)
    (v : Fin n → ℝ) (D : ℝ → ℝ) (x : ℝ) :
    gapTest q v D x = if q ⟨0, hn⟩ ≤ x ∧ x < q ⟨n - 1, by omega⟩ then
      v (ratioRootIndex hn q x) * D x else 0 := by
  classical
  have hindex {j : Fin n} (hj : x ∈ Ico (q j) (q (gapNext j))) : ratioRootIndex hn q x = j := by
    by_cases hv : j.val + 1 < n
    · exact ratio_rootIndex_on_cell hn q hq j hv (by simpa [gapNext, hv] using hj)
    · simp [gapNext, hv] at hj
  unfold gapTest
  split
  · rename_i h
    obtain ⟨hj, hx⟩ := ratio_rootIndex_cell hn q hq h.1 h.2
    rw [sum_eq_single (ratioRootIndex hn q x)]
    · exact indicator_of_mem (by simpa [gapNext, hj] using hx) _
    · exact fun j _ hj => indicator_of_notMem (fun h => hj (hindex h).symm) _
    · simp
  · rename_i h
    refine sum_eq_zero fun j _ => indicator_of_notMem (fun hj => h ?_) _
    exact ⟨(hq.monotone (by exact Nat.zero_le _)).trans hj.1,
      hj.2.trans_le (hq.monotone (by change (gapNext j).val ≤ n - 1; omega))⟩

private theorem gap_integrable {n : ℕ} (q v : Fin n → ℝ) {D : ℝ → ℝ} (hD : Continuous D) (j : Fin n) :
    Integrable ((Ico (q j) (q (gapNext j))).indicator (fun y => v j * D y)) :=
  (integrable_indicator_iff measurableSet_Ico).mpr
    ((hD.const_mul (v j)).integrableOn_Icc.mono_set Ico_subset_Icc_self)

private theorem integral_gapTest {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {q : Fin n → ℝ} (hq : StrictMono q) (hBE : DiscreteBetheEquation Δ N n q) (v : Fin n → ℝ) :
    (∫ x, gapTest q (fun j => (N : ℝ) * v j) (betheCountingDerivative Δ N n q) x) =
      (∑ j, v j) - v ⟨n - 1, by omega⟩ := by
  classical
  let D := betheCountingDerivative Δ N n q
  have hD := continuous_betheCountingDerivative hΔ N n q
  let last : Fin n := ⟨n - 1, by omega⟩
  unfold gapTest
  rw [integral_finsetSum _ (fun j _ => gap_integrable q (fun j => (N : ℝ) * v j) hD j)]
  trans ∑ j, (v j - if j = last then v last else 0)
  · refine sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · have hj : j ≠ last := by intro hh; rw [hh] at h; dsimp [last] at h; omega
      rw [ite_eq_right hj, sub_zero, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (hq.monotone (le_gapNext j)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_betheCountingFunction hΔ N n q x)
          (hD.intervalIntegrable _ _), betheCountingFunction_root_value hN q hBE,
        betheCountingFunction_root_value hN q hBE]
      have hNc : (N : ℝ) ≠ 0 := by positivity
      simp only [gapNext, dite_eq_left h, discreteBetheIndex, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    · have hj : j = last := Fin.ext (by dsimp [last]; omega)
      rw [gapNext, dite_eq_right h, Set.Ico_self, indicator_empty, integral_zero, ite_eq_left hj, hj, sub_self]
  · simp [last]

/-- The logarithmic sum converges by dominated convergence in the equal-mass cells. -/
theorem ratio_logsum_tendsto_of_geometry {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {Δ c C M : ℝ} (hΔ : Δ < -1) (hc : 2 < c) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (N n : ι → ℕ) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < n i)
    (q a : ∀ i, Fin (n i) → ℝ) (hq : ∀ i, q i ∈ S_n (n i))
    (ha : ∀ i j, a i j ∈ Ioo (-Real.pi) Real.pi)
    (hBE : ∀ i, DiscreteBetheEquation Δ (N i) (n i) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (hshift : ∀ᶠ i in l, ∀ j, |(N i : ℝ) * (q i j - a i j)| ≤ C * |q i j|)
    (hupper : ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi, |betheCountingDerivative Δ (N i) (n i) (q i) x| ≤ M)
    (w E : ℝ → ℝ)
    (hD : ∀ x ∈ Ioo (-Real.pi) Real.pi,
      Tendsto (fun i => betheCountingDerivative Δ (N i) (n i) (q i) x) l (𝓝 (w x)))
    (hspan : ∀ x ∈ Ioo (-Real.pi) Real.pi,
      ∀ᶠ i in l, q i ⟨0, hn i⟩ ≤ x ∧ x < q i ⟨n i - 1, by have := hn i; omega⟩)
    (hpred : ∀ x ∈ Ioo (-Real.pi) Real.pi,
      Tendsto (fun i => q i (ratioRootIndex (hn i) (q i) x)) l (𝓝 x))
    (he : ∀ x ∈ Ioo (-Real.pi) Real.pi, x ≠ 0 →
      Tendsto (fun i => (N i : ℝ) *
        (q i (ratioRootIndex (hn i) (q i) x) - a i (ratioRootIndex (hn i) (q i) x))) l (𝓝 (E x))) :
    Tendsto (fun i => ∑ j, (ratioEll c (q i j) - ratioEll c (a i j))) l
      (𝓝 (∫ x in Icc (-Real.pi) Real.pi, ratioEllPrime c x * E x * w x)) := by
  let B := 2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) * C
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) (ratio_profile_bound_nonneg hc)) hC
  let v (i) (j : Fin (n i)) := ratioEll c (q i j) - ratioEll c (a i j)
  let D (i) := betheCountingDerivative Δ (N i) (n i) (q i)
  let F (i) := gapTest (q i) (fun j => (N i : ℝ) * v i j) (D i)
  let J := Icc (-Real.pi) Real.pi
  let μ := volume.restrict J
  let g (x : ℝ) := ratioEllPrime c x * E x * w x
  let bound (_ : ℝ) := B * M
  have hv : ∀ᶠ i in l, ∀ j, |(N i : ℝ) * v i j| ≤ B := by
    filter_upwards [hshift, hNlim.eventually (eventually_ge_atTop (2 * C))] with i hi hl j
    exact ratio_scaled_root_log_bound hc (hN i) hC hl ((hq i).1 j) (ha i j) (hi j)
  have hmeas (i : ι) : AEStronglyMeasurable (F i) μ := by
    apply Integrable.aestronglyMeasurable
    exact (integrable_finsetSum _ fun j _ => gap_integrable (q i) (fun j => (N i : ℝ) * v i j)
      (continuous_betheCountingDerivative hΔ _ _ _) j).restrict
  have hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ bound x := by
    filter_upwards [hv, hupper] with i hi hu
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc : MeasurableSet J)] with x hx
    rw [Real.norm_eq_abs, show F i x = _ from gapTest_eq (hn i) (hq i).2.1 _ _ _]
    split
    · rw [abs_mul]
      exact mul_le_mul (hi _) (hu x hx) (abs_nonneg _) hB
    · simpa [bound] using mul_nonneg hB hM
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (g x)) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc : MeasurableSet J),
      Measure.ae_ne μ (0 : ℝ), Measure.ae_ne μ Real.pi, Measure.ae_ne μ (-Real.pi)] with x hx hx0 hxp hxm
    have hx' : x ∈ Ioo (-Real.pi) Real.pi := ⟨lt_of_le_of_ne hx.1 hxm.symm, lt_of_le_of_ne hx.2 hxp⟩
    let u i := q i (ratioRootIndex (hn i) (q i) x)
    let z i := a i (ratioRootIndex (hn i) (q i) x)
    have hz : Tendsto z l (𝓝 x) := by
      have ht := (hpred x hx').sub ((he x hx' hx0).div_atTop hNlim)
      rw [sub_zero] at ht
      refine ht.congr fun i => ?_
      have hNi : (N i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hN i)).ne'
      rw [mul_div_cancel_left₀ _ hNi, sub_sub_cancel]
    have ht := (ratio_scaled_ell_tendsto hc hx' hx0 u z _ (hpred x hx') hz (he x hx' hx0)).mul (hD x hx')
    apply ht.congr'
    filter_upwards [hspan x hx'] with i hi
    simp only [F, gapTest_eq (hn i) (hq i).2.1, ite_eq_left hi]
    rfl
  have hb : Integrable bound μ := integrableOn_const (by simp [J])
  have hInt := tendsto_integral_filter_of_dominated_convergence bound (.of_forall hmeas) hbound hb hpoint
  have hfull (i : ι) : (∫ x, F i x ∂μ) = ∫ x, F i x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    dsimp only [F]
    rw [gapTest_eq (hn i) (hq i).2.1, ite_eq_right]
    intro h
    exact hx ⟨((hq i).1 _).1.le.trans h.1, h.2.le.trans ((hq i).1 _).2.le⟩
  let jlast (i) : Fin (n i) := ⟨n i - 1, by have := hn i; omega⟩
  have hlast : Tendsto (fun i => v i (jlast i)) l (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_nhds.div_atTop hNlim : Tendsto (fun i => B / (N i : ℝ)) l (𝓝 0))
    filter_upwards [hv] with i hi
    have hh := hi (jlast i)
    have hNi : (0 : ℝ) < N i := Nat.cast_pos.mpr (hN i)
    rw [abs_mul, abs_of_pos hNi] at hh
    exact (le_div_iff₀' hNi).mpr (Real.norm_eq_abs _ ▸ hh)
  have ht := hInt.add hlast
  rw [add_zero] at ht
  refine ht.congr fun i => ?_
  rw [hfull, integral_gapTest hΔ (hN i) (hn i) (hq i).2.1 (hBE i), sub_add_cancel]

end PottsDiscontinuity.Bethe
