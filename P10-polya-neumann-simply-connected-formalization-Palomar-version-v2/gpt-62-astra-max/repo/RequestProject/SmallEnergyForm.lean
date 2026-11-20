module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.SmallKernel
public import RequestProject.PlanarNotation

/-!
# Lemma 8.6 (negative index at small energy): the reduction to a Schur complement

For a bounded operator `U` on `ℓ²` put

  `F(w) = -4 Im ⟨w, U w⟩`,   `B(x, w) = 2i ⟨x, (U - U^*) w⟩`,

so that `B` is a Hermitian form with `B(w, w) = F(w)`; on Herglotz data `F` is the Herglotz form
(`herglotzForm_eq_im`). If `F(x) < 0`, the Schur complement

  `C(w) = F(w) - |B(x, w)|² / F(x)`

is invariant under `w ↦ w + t x` (`imSchur_add_smul`), and `C ≥ 0` on a dense set forces
`F ≥ 0` on the closed hyperplane `{B(x, ·) = 0}` (`nonneg_of_imSchur_nonneg`): this is the
index count `ind₋ 𝒜_E ≤ 1` of Lemma 8.6.

The analytic input (Lemmas 8.2–8.5, proved in `SmallEnergyCore.lean`) is `small_energy_schur_core`: for small `E > 0`,
`F(e₀) < 0`, and every finitely supported `w` can be shifted along `e₀` to a vector on which
`C ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

section

variable (U : ShiftOp) (x v w : Ell2) (t : ℂ)
include U

include w in
/-- The form `F(w) = -4 Im ⟨w, U w⟩`. -/
def imForm : ℝ := -4 * (⟪w, U w⟫_ℂ).im

include w x in
/-- The Hermitian form `B(x, w) = 2i ⟨x, (U - U^*) w⟩`. -/
def imPair : ℂ :=
  2 * Complex.I * ⟪x, (U - ContinuousLinearMap.adjoint U) w⟫_ℂ

include w x in
/-- The Schur complement `C(w) = F(w) - |B(x, w)|² / F(x)`. -/
def imSchur : ℝ :=
  imForm U w - ‖imPair U x w‖ ^ 2 / imForm U x

lemma imPair_self : imPair U w w = imForm U w := by
  unfold imPair imForm
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  have hz : ⟪U w, w⟫_ℂ = conj ⟪w, U w⟫_ℂ := (inner_conj_symm _ _).symm
  rw [hz]
  generalize ⟪w, U w⟫_ℂ = z
  apply Complex.ext <;> simp
  ring

lemma imPair_conj : imPair U w x = conj (imPair U x w) := by
  unfold imPair
  have h : ⟪w, (U - ContinuousLinearMap.adjoint U) x⟫_ℂ =
      -conj ⟪x, (U - ContinuousLinearMap.adjoint U) w⟫_ℂ := by
    simp [inner_conj_symm, inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  rw [h, map_mul, map_mul, Complex.conj_I, map_ofNat]
  ring

lemma imPair_add_right :
    imPair U x (v + w) = imPair U x v + imPair U x w := by
  unfold imPair; rw [map_add, inner_add_right]; ring

lemma imPair_smul_right :
    imPair U x (t • w) = t * imPair U x w := by
  unfold imPair; rw [map_smul, inner_smul_right]; ring

lemma imPair_add_left :
    imPair U (v + w) x = imPair U v x + imPair U w x := by
  unfold imPair; rw [inner_add_left]; ring

lemma imPair_smul_left :
    imPair U (t • w) x = conj t * imPair U w x := by
  unfold imPair; rw [inner_smul_left]; ring

/-- The Schur complement is invariant under `w ↦ w + t x`. -/
lemma imSchur_add_smul {x : Ell2} (hx : imForm U x ≠ 0) (w : Ell2)
    (t : ℂ) : imSchur U x (w + t • x) = imSchur U x w := by
  set a := imForm U x with ha
  set b := imPair U x w with hb
  have hxx  := imPair_self U x
  have hF : ((imForm U (w + t • x) : ℝ) : ℂ) =
      (imForm U w : ℂ) + conj t * b + t * conj b + t * conj t * a := by
    rw [← imPair_self, ← imPair_self, imPair_add_left, imPair_add_right, imPair_add_right,
      imPair_smul_left, imPair_smul_right, imPair_smul_left, imPair_smul_right, hxx,
      imPair_conj U x w]
    ring
  have hB : imPair U x (w + t • x) = b + t * a := by
    rw [imPair_add_right, imPair_smul_right, hxx]
  unfold imSchur
  rw [← ha, hB]
  have hFr : imForm U (w + t • x) =
      imForm U w + 2 * (conj t * b).re + Complex.normSq t * a := by
    have := congrArg Complex.re hF
    simp only [Complex.ofReal_re, Complex.add_re] at this
    rw [this]
    have e1 : (t * conj b).re = (conj t * b).re := by
      simp [map_mul, mul_comm]
    have e2 : (t * conj t * (a : ℂ)).re = Complex.normSq t * a := by
      simp [Complex.mul_conj]
    linarith
  have hN : ‖b + t * a‖ ^ 2 = ‖b‖ ^ 2 + 2 * a * (conj t * b).re + Complex.normSq t * a ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp only [Complex.normSq_ofReal, map_mul, Complex.conj_ofReal]
    have : (b * (conj t * a)).re = a * (conj t * b).re := by
      simp; ring
    linarith
  rw [hFr, hN]
  field_simp
  ring

/-- Continuity of `F` and of `B(x, ·)`. -/
lemma continuous_imForm : Continuous (imForm U) := by
  
  exact continuous_const.mul (Complex.continuous_im.comp
    (continuous_id.inner (U.continuous)))

lemma continuous_imPair : Continuous (imPair U x) := by
  
  exact continuous_const.mul (continuous_const.inner
    (U - ContinuousLinearMap.adjoint U).continuous)

/-- **Index count.** If the Schur complement is nonnegative on a dense set, then `F ≥ 0` on the closed hyperplane `{B(x, ·) = 0}`. -/
theorem nonneg_of_imSchur_nonneg {x : Ell2}
    {S : Set Ell2} (hS : Dense S) (hC : ∀ w ∈ S, 0 ≤ imSchur U x w) (w : Ell2)
    (hw : imPair U x w = 0) : 0 ≤ imForm U w := by
  have hcont : Continuous (imSchur U x) := by
    exact (continuous_imForm U).sub (((continuous_imPair U x).norm.pow 2).div_const _)
  have hall : ∀ v, 0 ≤ imSchur U x v := by
    intro v
    
    exact (isClosed_le continuous_const hcont).closure_subset_iff.mpr hC (hS v)
  have := hall w
  unfold imSchur at this
  rwa [hw, norm_zero, zero_pow two_ne_zero, zero_div, sub_zero] at this

end

/-- Finitely supported vectors are dense in `ℓ²`. -/
lemma dense_finSupp : Dense {v : Ell2 | ∃ N : ℕ, ∀ n, N ≤ n → (v : ℕ → ℂ) n = 0} := by
  intro v
  
  refine mem_closure_of_tendsto (lp.hasSum_single (p := 2) (by norm_num) v).tendsto_sum_nat ?_
  refine Eventually.of_forall fun N => ⟨N, fun n hn => ?_⟩
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have : n ≠ i := by
    have := Finset.mem_range.mp hi; omega
  simp [this]

/-! ### Linear dependence of the Herglotz vector on the density -/

lemma herglotzVec_congr {a b : ℝ → ℂ} (hab : a = b) (ha : IsDirDensity a) (hb : IsDirDensity b)
    (k : ℝ) (z : ℂ) : herglotzVec ha k z = herglotzVec hb k z := by
  subst hab; rfl

lemma herglotzVec_add {a b : ℝ → ℂ} (ha : IsDirDensity a) (hb : IsDirDensity b) (k : ℝ)
    (z : ℂ) : herglotzVec (ha.add hb) k z = herglotzVec ha k z + herglotzVec hb k z := by
  have hf : (∑ i, (![1, 1] : Fin 2 → ℂ) i • (![a, b] : Fin 2 → ℝ → ℂ) i) = a + b := by
    simp
  have hs : IsDirDensity (∑ i, (![1, 1] : Fin 2 → ℂ) i • (![a, b] : Fin 2 → ℝ → ℂ) i) := by
    rw [hf]; exact ha.add hb
  
  rw [← herglotzVec_congr hf hs (ha.add hb), herglotzVec_sum _ _ (by
    simp [*]) hs, Fin.sum_univ_two]
  simp

lemma herglotzVec_smul {a : ℝ → ℂ} (ha : IsDirDensity a) (c : ℂ) (k : ℝ) (z : ℂ) :
    herglotzVec (ha.const_smul c) k z = c • herglotzVec ha k z := by
  have hf : (∑ i, (![c] : Fin 1 → ℂ) i • (![a] : Fin 1 → ℝ → ℂ) i) = c • a := by
    simp
  have hs : IsDirDensity (∑ i, (![c] : Fin 1 → ℂ) i • (![a] : Fin 1 → ℝ → ℂ) i) := by
    rw [hf]; exact ha.const_smul c
  
  rw [← herglotzVec_congr hf hs (ha.const_smul c), herglotzVec_sum _ _ (by
    simp [*]) hs]
  simp

/-- The `L²` direction densities, as a submodule of all functions. -/
def dirDensities : Submodule ℂ (ℝ → ℂ) where
  carrier := {a | IsDirDensity a}
  add_mem' ha hb := MemLp.add ha hb
  zero_mem' := MemLp.zero
  smul_mem' c _ ha := MemLp.const_smul ha c

/-- `a ↦ y_a(z)` as a linear map on direction densities. -/
def herglotzVecLin (k : ℝ) (z : ℂ) : dirDensities →ₗ[ℂ] Ell2 where
  toFun a := herglotzVec (a.2 : IsDirDensity a.1) k z
  map_add' a b := herglotzVec_add a.2 b.2 k z
  map_smul' c a := herglotzVec_smul a.2 c k z

/-- For a closed Lipschitz curve, the signed area integral does not depend on the base point:
`∫ Im(conj(γ - γ(0)) γ') = ∫ Im(conj γ · γ')`. -/
lemma integral_areaDensity_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ anglePeriod = γ 0) :
    ∫ₚ θ, areaDensity γ θ = ∫ₚ θ, signedAreaDensity γ θ := by
  have hloc  := locallyIntegrable_of_bounded
      (by fun_prop) (norm_deriv_le_of_lipschitzWith hK)
  
  have hint1 : IntervalIntegrable (fun θ => conj (γ 0) * deriv γ θ) volume 0 anglePeriod :=
    ((hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).const_mul _
  
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn 
     (hK.continuous.sub continuous_const).continuousOn
  have hA : IntervalIntegrable (areaDensity γ) volume 0 anglePeriod := by
    refine (intervalIntegrable_const (c := R * K)).mono_fun'
      (areaDensity_aestronglyMeasurable hK.continuous).restrict ?_
    rw [Set.uIoc_of_le (by positivity)]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun θ hθ => ?_)
    exact abs_areaDensity_le hK hR ⟨hθ.1.le, hθ.2⟩
  have h1 : (signedAreaDensity γ) =
      fun θ => areaDensity γ θ + Complex.imCLM (conj (γ 0) * deriv γ θ) := by
    funext θ; simp only [areaDensity, signedAreaDensity, map_sub, sub_mul, Complex.sub_im,
      Complex.imCLM_apply]; ring
  have h0 : ∫ₚ θ, Complex.imCLM (conj (γ 0) * deriv γ θ) = 0 := by
    rw [Complex.imCLM.intervalIntegral_comp_comm hint1, intervalIntegral.integral_const_mul,
      integral_deriv_of_lipschitz hK, hclosed, sub_self, mul_zero, map_zero]
  rw [h1, intervalIntegral.integral_add hA (⟨Complex.imCLM.integrable_comp hint1.1, Complex.imCLM.integrable_comp hint1.2⟩), h0, add_zero]

/-- `F(e₀) = 2 a_E`. -/
lemma imForm_monodromy_basisVec (W : TransportPath) :
    imForm (monodromy W) (basisVec 0) = 2 * smallA W := by
  unfold imForm smallA monodromy
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_basisVec,
    Complex.conj_im]
  ring

/-- **Lemma 8.2 (sign of `a_E`).** For small `E > 0`, `F(e₀) = 2 a_E < 0`. -/
theorem small_energy_imForm_basisVec_neg {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : TransportPath, IsTransport γ E W →
      imForm (monodromy W) (basisVec 0) < 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed := hγ.periodic.eq
  obtain ⟨C, hC0, hC⟩ := smallA_approx hK
  set v := (volume Ω).toReal with hv
  have hvpos : 0 < v := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  have harea : ∫ₚ θ, areaDensity γ θ = 2 * v := by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area
  refine ⟨min 1 ((v / (C + 1)) ^ 2), (by positivity),
    fun E hE hEδ W hW => ?_⟩
  
  have hE2  := hEδ.trans_le (min_le_right _ _)
  have hs : Real.sqrt E < v / (C + 1) := by
    rw [show v / (C + 1) = Real.sqrt ((v / (C + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt hE.le hE2
  have hs' : (C + 1) * Real.sqrt E < v := by
    rw [lt_div_iff₀ (by positivity)] at hs; linarith
  have h := hC E hE.le ((hEδ.trans_le (min_le_left _ _)).le) W hW
  rw [harea] at h
  have h2 := (abs_le.mp h).2
  have hsq := Real.sqrt_nonneg E
  rw [imForm_monodromy_basisVec]
  nlinarith [mul_lt_mul_of_pos_left hs' hE]

end PolyaNeumann

end
