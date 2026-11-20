module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.ObservationHS
public import RequestProject.PhysicalHardyWeights
public import RequestProject.PlanarNotation

/-!
# Double Fourier coefficients of kernels with Lipschitz rows (toward Lemma 6.6)

Let `k(θ, t)` be a bounded kernel, measurable in `t`, which is `2π`-periodic and uniformly
`K`-Lipschitz in `θ` (for `t ∈ [0, 2π)`). Its rows `θ ↦ k(θ, ·)` are then a periodic Lipschitz
map into `L²(𝕋)`, and the estimate of `FourierLipschitz.lean`, applied to the Fourier basis of
`L²(𝕋)`, gives for the double Fourier coefficients
`k_{n m} = (θ ↦ (t ↦ k(θ, t))^(n))^(m)`

  `∑_{n, m} m² |k_{n m}|² < ∞`     (`summable_sq_mul_kernelCoeff`).

This is the form in which the regularity of the corrected Volterra kernel `r_E` of Lemma 6.6
enters the compactness of the normalized remainder in Lemma 6.7.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- `L²(𝕋)` with the normalized Haar measure on `ℝ / 2πℤ`. -/
abbrev L2Circ := Lp ℂ 2 (@AddCircle.haarAddCircle anglePeriod _)

section

variable (x : ParamCircle) (f : ℝ → ℂ)

include x in
/-- The representative in `[0, 2π)` of a point of the circle. -/
def circRep : ℝ := (AddCircle.measurableEquivIco anglePeriod 0 x : ℝ)

lemma circRep_mem : circRep x ∈ angleIco := by
  have := (AddCircle.measurableEquivIco anglePeriod 0 x).2
  simpa [circRep] using this

lemma liftIco_eq_comp : AddCircle.liftIco anglePeriod 0 f = fun x => f (circRep x) := rfl

lemma measurable_liftIco_two_pi {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (AddCircle.liftIco anglePeriod 0 f) := by
  exact hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIco anglePeriod 0).measurable)

lemma memLp_liftIco_two_pi {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M) :
    MemLp (AddCircle.liftIco anglePeriod 0 f) 2 AddCircle.haarAddCircle :=
  MemLp.of_bound (measurable_liftIco_two_pi hf).aestronglyMeasurable M
    (ae_of_all _ fun x => hM _)

/-- Fourier coefficients of the lift of a function on `[0, 2π)` to the circle. -/
lemma fourierCoeff_liftIco_two_pi (n : ℤ) :
    fourierCoeff (AddCircle.liftIco anglePeriod 0 f) n = angleCoeff f n := by
  rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp

end

section Kernel

variable {k : ℝ → ℝ → ℂ} {M : ℝ} {K : NNReal}
  (hmeas : ∀ θ, Measurable (k θ)) (hbd : ∀ θ t, ‖k θ t‖ ≤ M)

/-- The row `θ ↦ k(θ, ·)` as an element of `L²(𝕋)`. -/
def kernelRow (θ : ℝ) : L2Circ :=
  (memLp_liftIco_two_pi (hmeas θ) (hbd θ)).toLp _

include hmeas hbd in
lemma inner_kernelRow_fourierBasis (θ : ℝ) (n : ℤ) :
    ⟪kernelRow hmeas hbd θ, fourierBasis n⟫_ℂ = conj (angleCoeff (k θ) n) := by
  rw [← inner_conj_symm, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]
  rw [kernelRow, fourierCoeff_congr_ae (MemLp.coeFn_toLp (memLp_liftIco_two_pi (hmeas θ) (hbd θ))),
    fourierCoeff_liftIco_two_pi]

include hmeas hbd in
lemma norm_kernelRow_sub_le
    (hlip : ∀ θ θ' t, t ∈ angleIco → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|) (θ θ' : ℝ) :
    ‖kernelRow hmeas hbd θ - kernelRow hmeas hbd θ'‖ ≤ K * |θ - θ'| := by
  unfold kernelRow
  rw [← MemLp.toLp_sub]
  have h := Lp.norm_le_of_ae_bound  (p := 2)
    (f := MemLp.toLp _ ((memLp_liftIco_two_pi (hmeas θ) (hbd θ)).sub
      (memLp_liftIco_two_pi (hmeas θ') (hbd θ')))) (C := K * |θ - θ'|) (by positivity) ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle anglePeriod _) = 1 := by
      simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp ((memLp_liftIco_two_pi (hmeas θ) (hbd θ)).sub
      (memLp_liftIco_two_pi (hmeas θ') (hbd θ')))] with x hx
    rw [hx, Pi.sub_apply, liftIco_eq_comp, liftIco_eq_comp]
    exact hlip θ θ' _ (circRep_mem x)

include hmeas hbd in
lemma kernelRow_periodic (hper : ∀ θ t, t ∈ angleIco → k (θ + anglePeriod) t = k θ t) :
    Function.Periodic (kernelRow hmeas hbd) anglePeriod := by
  intro θ
  
  refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
  exact hper θ _ (circRep_mem x)

end Kernel

end PolyaNeumann
