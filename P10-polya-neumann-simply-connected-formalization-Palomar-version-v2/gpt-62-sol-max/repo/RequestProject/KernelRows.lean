module

public import RequestProject.CircleFourier
public import RequestProject.ObservationHS

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
abbrev L2Circ := Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _)

/-- The normalized Haar `L²` norm is bounded by any uniform bound on a representative. -/
lemma norm_toLp_circle_le {f : AddCircle (2 * π) → ℂ}
    (hf : MemLp f 2 AddCircle.haarAddCircle) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  have h' := Lp.norm_le_of_ae_bound (f := hf.toLp f) hC
    (hf.coeFn_toLp.mono fun x hx => hx ▸ h x)
  simp_all [measureUnivNNReal]

/-- The representative in `[0, 2π)` of a point of the circle. -/
def circRep (x : AddCircle (2 * π)) : ℝ := (AddCircle.measurableEquivIco (2 * π) 0 x : ℝ)

lemma circRep_mem (x : AddCircle (2 * π)) : circRep x ∈ Set.Ico 0 (2 * π) := by grind [circRep]

lemma liftIco_eq_comp (f : ℝ → ℂ) : AddCircle.liftIco (2 * π) 0 f = fun x => f (circRep x) := rfl

lemma measurable_liftIco_two_pi {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (AddCircle.liftIco (2 * π) 0 f) := hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (2 * π) 0).measurable)

lemma memLp_liftIco_two_pi {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M) :
    MemLp (AddCircle.liftIco (2 * π) 0 f) 2 AddCircle.haarAddCircle :=
  MemLp.of_bound (measurable_liftIco_two_pi hf).aestronglyMeasurable M
    (ae_of_all _ fun x => hM _)

/-- Fourier coefficients of the lift of a function on `[0, 2π)` to the circle. -/
lemma fourierCoeff_liftIco_two_pi (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIco (2 * π) 0 f) n = fourierCoeffOn two_pi_pos f n := by
  rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp

section Kernel

variable {k : ℝ → ℝ → ℂ} {M : ℝ} {K : NNReal}
  (hmeas : ∀ θ, Measurable (k θ)) (hbd : ∀ θ t, ‖k θ t‖ ≤ M)

/-- The row `θ ↦ k(θ, ·)` as an element of `L²(𝕋)`. -/
def kernelRow (θ : ℝ) : L2Circ :=
  (memLp_liftIco_two_pi (hmeas θ) (hbd θ)).toLp _

include hmeas hbd in
lemma inner_kernelRow_fourierBasis (θ : ℝ) (n : ℤ) :
    ⟪kernelRow hmeas hbd θ, fourierBasis n⟫_ℂ = conj (fourierCoeffOn two_pi_pos (k θ) n) := by
  rw [← inner_conj_symm, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]
  congr 1
  rw [kernelRow, fourierCoeff_congr_ae (MemLp.coeFn_toLp (memLp_liftIco_two_pi (hmeas θ) (hbd θ))),
    fourierCoeff_liftIco_two_pi]

include hmeas hbd in
lemma norm_kernelRow_sub_le
    (hlip : ∀ θ θ' t, t ∈ Set.Ico 0 (2 * π) → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|) (θ θ' : ℝ) :
    ‖kernelRow hmeas hbd θ - kernelRow hmeas hbd θ'‖ ≤ K * |θ - θ'| := by
  unfold kernelRow
  rw [← MemLp.toLp_sub]
  apply norm_toLp_circle_le _ (by positivity)
  intro x
  exact hlip θ θ' (circRep x) (circRep_mem x)

include hmeas hbd in
lemma kernelRow_periodic (hper : ∀ θ t, t ∈ Set.Ico 0 (2 * π) → k (θ + 2 * π) t = k θ t) :
    Function.Periodic (kernelRow hmeas hbd) (2 * π) := by
  intro θ
  unfold kernelRow
  refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
  rw [liftIco_eq_comp]
  exact hper θ _ (circRep_mem x)

lemma norm_kernelRow_le (θ : ℝ) : ‖kernelRow hmeas hbd θ‖ ≤ M := by
  exact norm_toLp_circle_le _ ((norm_nonneg _).trans (hbd 0 0))
    (fun x => by tauto)

end Kernel

end PolyaNeumann
