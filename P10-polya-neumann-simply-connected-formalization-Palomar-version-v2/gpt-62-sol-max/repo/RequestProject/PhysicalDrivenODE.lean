module

public import RequestProject.CircleFourier
public import RequestProject.IntervalRegularity
public import RequestProject.IntervalFTC
public import RequestProject.CorrectedKernelSmooth
public import RequestProject.Unitarity

/-! Absolute continuity and the equation for the driven transport. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

local notation "L" => (2 * Real.pi)
local notation "J" => Icc (0 : ℝ) L
local notation "κ" => -(Complex.I / (Real.sqrt 2 : ℂ))

theorem continuous_transportCoeff_of_contDiff {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (E : ℝ) :
    Continuous (transportCoeff γ E) := by
  have := hγ.continuous_deriv_one
  fun_prop [transportCoeff]

theorem hasDerivAt_transport_of_contDiff {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {t : ℝ} (ht : t ∈ Ioo 0 L) : HasDerivAt W (transportCoeff γ E t * W t) t :=
  (hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW
    (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Variation of constants with an integrable forcing vector. -/
def transportResponse (W : ℝ → Ell2 →L[ℂ] Ell2) (x : Ell2) (c : ℂ) (f : ℝ → Ell2) (t : ℝ) : Ell2 :=
  W t (x + c • ∫ s in (0 : ℝ)..t, (ContinuousLinearMap.adjoint (W s)) (f s))

theorem transportResponse_continuousOn {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W J)
    (x : Ell2) (c : ℂ) {f : ℝ → Ell2} (hf : IntervalIntegrable f volume 0 L) :
    ContinuousOn (transportResponse W x c f) J := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).mp
    (intervalIntegrable_adjoint_apply hW hf)
  rw [← uIcc_of_le Real.two_pi_pos.le] at hi
  have h := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le Real.two_pi_pos.le] at h
  exact hW.clm_apply (continuousOn_const.add (h.const_smul c))

theorem transportResponse_absolutelyContinuous {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (x : Ell2) (c : ℂ) {f : ℝ → Ell2} (hf : IntervalIntegrable f volume 0 L) :
    AbsolutelyContinuousOnInterval (transportResponse W x c f) 0 L := by
  obtain ⟨M, hM⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  have h₁ := (uIcc_of_le Real.two_pi_pos.le ▸ hM : LipschitzOnWith M W (uIcc 0 L)).absolutelyContinuousOnInterval
  have h₂ := absolutelyContinuousOnInterval_intervalIntegral_banach (intervalIntegrable_adjoint_apply hW.1 hf)
    (by simp : (0 : ℝ) ∈ uIcc 0 L)
  exact absolutelyContinuousOnInterval_clm_apply h₁
    (((LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval).add (h₂.const_smul c))

theorem transportResponse_ae_hasDerivAt {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hγ : ContDiff ℝ 1 γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (x : Ell2) (c : ℂ) {f : ℝ → Ell2} (hf : IntervalIntegrable f volume 0 L) :
    ∀ᵐ t, t ∈ Ioo 0 L → HasDerivAt (transportResponse W x c f)
      (transportCoeff γ E t (transportResponse W x c f t) + c • f t) t := by
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le (intervalIntegrable_adjoint_apply hW.1 hf)]
    with t hd ht
  refine (hasDerivAt_clm_apply_real (hasDerivAt_transport_of_contDiff hγ hW ht)
    ((hd ht).const_smul c |>.const_add x)).congr_deriv ?_
  have hc : W t ((ContinuousLinearMap.adjoint (W t)) (f t)) = f t := by
    rw [← ContinuousLinearMap.mul_apply, transport_mul_adjoint hK hW (Ioo_subset_Icc_self ht),
      ContinuousLinearMap.one_apply]
  simp [transportResponse, hc]

/-- The actual wave-number scalar in the transport coefficient. -/
def physicalDrivenQ (E : ℝ) : ℂ := -(Complex.I * (Real.sqrt E : ℂ)) / 2

section

variable {E : ℝ} (hE : 0 < E)
include E hE

theorem physicalDrivenQ_ne_zero  : physicalDrivenQ E ≠ 0 := by
  unfold physicalDrivenQ
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hE).ne'))) (by norm_num)

theorem physicalDrivenQ_sq_ne_zero  : physicalDrivenQ E ^ 2 ≠ 0 :=
  pow_ne_zero _ (physicalDrivenQ_ne_zero hE)

end

section

variable (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ)
include W g

/-- The actual driven vector with zero initial value, given by variation
of constants.  No terminal value is built into this definition. -/
def physicalDrivenVector  (θ : ℝ) : Ell2 :=
  (-(Complex.I / (Real.sqrt 2 : ℂ))) •
    W θ (∫ s in (0 : ℝ)..θ, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))

@[simp] theorem physicalDrivenVector_zero  :
    physicalDrivenVector W g 0 = 0 := by
  simp [physicalDrivenVector]

/-- The terminal zero is a consequence of the actual adjoint observation
kernel, rather than an imposed periodic endpoint condition. -/
theorem physicalDrivenVector_endpoint 
    (hO : observationAdj W g = 0) : physicalDrivenVector W g (2 * Real.pi) = 0 := by
  change (-(Complex.I / (Real.sqrt 2 : ℂ))) • W (2 * Real.pi) (observationAdj W g) = 0
  simp_all

end



def physicalDrivenCentered (γ : ℝ → ℂ) (θ : ℝ) : ℂ := γ θ - γ 0

theorem physicalDrivenQ_sq {E : ℝ} (hE : 0 ≤ E) :
    physicalDrivenQ E ^ 2 = -(E : ℂ) / 4 := by
  have hs : (Real.sqrt E : ℂ) ^ 2 = (E : ℂ) := by
    exact_mod_cast Real.sq_sqrt hE
  simp only [physicalDrivenQ, div_pow, neg_sq, mul_pow, Complex.I_sq, hs]
  ring


private theorem physicalDrivenVector_eq_response (W : ℝ → Ell2 →L[ℂ] Ell2) (g : ℝ → ℂ) :
    physicalDrivenVector W g = transportResponse W 0 κ (fun t => g t • basisVec 0) := by
  ext t j
  simp [physicalDrivenVector, transportResponse]

private theorem intervalIntegrable_smul_basisVec {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume 0 L) :
    IntervalIntegrable (fun t => g t • basisVec 0) volume 0 L :=
  ⟨hg.1.smul_const _, hg.2.smul_const _⟩

/-- The driven vector is continuous for integrable loads. -/
theorem physicalDrivenVector_continuousOn_of_intervalIntegrable
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W J) (g : ℝ → ℂ)
    (hg : IntervalIntegrable g volume 0 L) : ContinuousOn (physicalDrivenVector W g) J := by
  rw [physicalDrivenVector_eq_response]
  exact transportResponse_continuousOn hW _ _ (intervalIntegrable_smul_basisVec hg)

theorem physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 L) :
    AbsolutelyContinuousOnInterval (physicalDrivenVector W g) 0 L := by
  rw [physicalDrivenVector_eq_response]
  exact transportResponse_absolutelyContinuous hK hW _ _ (intervalIntegrable_smul_basisVec hg)

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))
include γ K hK hγ E W hW g hg

/-- The actual driven differential equation holds a.e. for integrable
forcing, derived from the genuine primitive and actual transport. -/
theorem physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable
     :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenVector W g)
        (transportCoeff γ E θ (physicalDrivenVector W g θ) +
          (-(Complex.I / (Real.sqrt 2 : ℂ)) * g θ) • basisVec 0) θ := by
  simp only [physicalDrivenVector_eq_response, ← smul_smul]
  exact transportResponse_ae_hasDerivAt hK hγ hW _ _ (intervalIntegrable_smul_basisVec hg)

end


end PolyaNeumann
end
