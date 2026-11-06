module

public import RequestProject.AreaTrace
public import RequestProject.SpectralExpansion
public import RequestProject.CutFourier

/-!
# Lemma 9.3: the trace of the cut logarithm of the monodromy

For a closed Lipschitz curve, let `0 < ε < 2π` and let `[E₁, E₂] ⊂ (0, ∞)` be an interval on
which `e^{iε}` avoids the spectrum of `U_E`. We prove that the cut phase sum
`∑_{z ≠ 1} mult(z) argCut ε z` of `U_E` increases on `[E₁, E₂]` at the constant rate
`tr L_E = (1/4) ∫₀^{2π} b`.

The argument replaces the holomorphic functional calculus of the paper by an absolutely convergent
Fourier series: on the part of the circle away from the cut, `argCut ε = ∑ₙ 2 Re(cₙ (zⁿ - 1))`
(`CutFourier.lean`), so the cut phase sum is `∑ₙ 2 Re(cₙ tr(U_E^n - I))`
(`SpectralExpansion.lean`). Each `tr(U_E^n - I)` is differentiated through the curvature formula
`∂_E U_E = i Q_E U_E`, its derivative being `i n tr(Q_E U_E^n)`, and the resulting series
`∑ₙ 2 Re(i n cₙ tr(Q_E U_E^n))` is `tr Q_E` because `∑ₙ 2 Re(i n cₙ zⁿ) = 1` on the spectrum.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Real Topology ComplexConjugate

noncomputable section

namespace PolyaNeumann

variable {W : ℝ → Ell2 →L[ℂ] Ell2} {b : ℝ → ℝ} {γ : ℝ → ℂ} {K : NNReal}

/-- `⟨x, D_N y⟩ = 2 ⟨e₀, y⟩ ⟨x, e₀⟩ - ⟨e₁, y⟩ ⟨x, e₁⟩`. -/
lemma inner_diagN (x y : Ell2) :
    inner ℂ x (diagN y) = 2 * (inner ℂ (basisVec 0) y * inner ℂ x (basisVec 0)) -
      inner ℂ (basisVec 1) y * inner ℂ x (basisVec 1) := by
  simp [diagN, inner_sub_right, inner_smul_right, basisVec]

/-- Parseval in a Hilbert basis: `∑ᵢ |⟨bᵢ, v⟩|² = ‖v‖²`. -/
lemma hasSum_norm_inner_sq {ι : Type*} (b : HilbertBasis ι ℂ Ell2) (v : Ell2) :
    HasSum (fun i => ‖inner ℂ (b i) v‖ ^ 2) (‖v‖ ^ 2) := by
  convert Complex.hasSum_re (b.hasSum_inner_mul_inner v v) using 1
  · funext i
    rw [← inner_conj_symm (b i) v, RCLike.norm_conj, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simp [← Complex.ofReal_pow]

/-- The trace form `∫₀^{2π} b (2 ⟨u₀, X u₀⟩ - ⟨u₁, X u₁⟩)`, `u_j = W(θ)^* e_j`: the trace of
`(∫ b W^* D_N W) X`. -/
def traceForm (W : ℝ → Ell2 →L[ℂ] Ell2) (b : ℝ → ℝ) (X : Ell2 →L[ℂ] Ell2) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
    (2 * inner ℂ (star (W θ) (basisVec 0)) (X (star (W θ) (basisVec 0))) -
      inner ℂ (star (W θ) (basisVec 1)) (X (star (W θ) (basisVec 1))))

lemma norm_inner_mul_inner_le (u v w : Ell2) :
    ‖inner ℂ v w * inner ℂ w u‖ ≤ (‖inner ℂ w v‖ ^ 2 + ‖inner ℂ w u‖ ^ 2) / 2 := by
  rw [norm_mul, norm_inner_symm v w]
  nlinarith [sq_nonneg (‖inner ℂ w v‖ - ‖inner ℂ w u‖)]

lemma intervalIntegrable_ofReal_mul (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 (2 * π))) :
    IntervalIntegrable (fun θ => b θ * f θ) volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine Integrable.of_bound ((Complex.continuous_ofReal.comp_aestronglyMeasurable hb).restrict.mul
    (hf.aestronglyMeasurable measurableSet_Icc)) (B * M)
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun θ hθ => ?_))
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul (hbB θ hθ) (hM θ hθ) (norm_nonneg _) ((abs_nonneg _).trans (hbB θ hθ))

lemma intervalIntegrable_abs_mul (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 (2 * π))) :
    IntervalIntegrable (fun θ => |b θ| * f θ) volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine Integrable.of_bound (hb.norm.restrict.mul (hf.aestronglyMeasurable measurableSet_Icc))
    (B * M) ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun θ hθ => ?_))
  rw [norm_mul, Real.norm_eq_abs, abs_abs]
  exact mul_le_mul (hbB θ hθ) (hM θ hθ) (norm_nonneg _) ((abs_nonneg _).trans (hbB θ hθ))

/-- Parseval under an integral: `∑ₙ ∫ b ⟨v, eₙ⟩ ⟨eₙ, w⟩ = ∫ b ⟨v, w⟩`. -/
lemma hasSum_integral_inner_mul_inner {v w : ℝ → Ell2} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hw : ContinuousOn w (Icc 0 (2 * π))) {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun n => ∫ θ in 0..(2 * π), b θ * (inner ℂ (v θ) (e n) * inner ℂ (e n) (w θ)))
      (∫ θ in 0..(2 * π), b θ * inner ℂ (v θ) (w θ)) := by
  have hπ : 0 ≤ 2 * π := by positivity
  have hsub : uIoc 0 (2 * π) ⊆ Icc 0 (2 * π) := by
    grind
  have hgs : ∀ θ, HasSum (fun n => |b θ| * ((‖inner ℂ (e n) (v θ)‖ ^ 2 +
      ‖inner ℂ (e n) (w θ)‖ ^ 2) / 2)) (|b θ| * ((‖v θ‖ ^ 2 + ‖w θ‖ ^ 2) / 2)) := fun θ =>
    (((hasSum_norm_inner_sq e _).add (hasSum_norm_inner_sq e _)).div_const 2).mul_left _
  have hvm : AEStronglyMeasurable v (volume.restrict (uIoc 0 (2 * π))) :=
    (hv.aestronglyMeasurable measurableSet_Icc).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hwm : AEStronglyMeasurable w (volume.restrict (uIoc 0 (2 * π))) :=
    (hw.aestronglyMeasurable measurableSet_Icc).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n θ => |b θ| * ((‖inner ℂ (e n) (v θ)‖ ^ 2 + ‖inner ℂ (e n) (w θ)‖ ^ 2) / 2))
    (fun n => ?_) (fun n => Eventually.of_forall fun θ _ => ?_)
    (Eventually.of_forall fun θ _ => (hgs θ).summable) ?_
    (Eventually.of_forall fun θ _ => (e.hasSum_inner_mul_inner (v θ) (w θ)).mul_left _)
  · fun_prop
  · rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_inner_mul_inner_le _ _ _) (abs_nonneg _)
  · exact (intervalIntegrable_abs_mul hb hbB (((hv.norm.pow 2).add (hw.norm.pow 2)).div_const 2)).congr (fun θ _ => (hgs θ).tsum_eq.symm)

/-- **Trace of `(∫ b W^* D_N W) X`.** For a continuous unitary family `W` on `[0, 2π]`, a bounded
measurable weight `b` and any bounded operator `X`, the diagonal sum of
`(∫₀^{2π} b W^* D_N W) X` in any Hilbert basis is the trace form `traceForm W b X`. -/
theorem hasSum_trace_integral_conj_diagN_mul {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : ContinuousOn W (Icc 0 (2 * π)))
    (hunit : ∀ θ ∈ Icc 0 (2 * π), W θ ∈ unitary (Ell2 →L[ℂ] Ell2))
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) (X : Ell2 →L[ℂ] Ell2) {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun n => inner ℂ (e n)
        (((∫ θ in 0..(2 * π), b θ • (star (W θ) * diagN * W θ)) * X) (e n)))
      (traceForm W b X) := by
  have huc : ∀ j, ContinuousOn (fun θ => star (W θ) (basisVec j)) (Icc 0 (2 * π)) := fun j =>
    hW.star.clm_apply continuousOn_const
  have hXc  := fun j => (ContinuousLinearMap.adjoint X).continuous.comp_continuousOn
    (huc j)
  have hS : ∀ j, HasSum (fun n => ∫ θ in 0..(2 * π), b θ *
      (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec j))) (e n) *
        inner ℂ (e n) (star (W θ) (basisVec j))))
      (∫ θ in 0..(2 * π), b θ *
        inner ℂ (star (W θ) (basisVec j)) (X (star (W θ) (basisVec j)))) := by
    intro j
    have := hasSum_integral_inner_mul_inner (hXc j) (huc j) hb hbB e
    simp_all [ContinuousLinearMap.adjoint_inner_left]
  have hpt : ∀ n θ, inner ℂ (e n) ((b θ • (star (W θ) * diagN * W θ)) (X (e n))) =
      2 * (b θ * (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec 0))) (e n) *
        inner ℂ (e n) (star (W θ) (basisVec 0)))) -
      b θ * (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec 1))) (e n) *
        inner ℂ (e n) (star (W θ) (basisVec 1))) := by
    intro n θ
    have k1 : ∀ j, inner ℂ (basisVec j) (W θ (X (e n))) = inner ℂ
        (ContinuousLinearMap.adjoint X (ContinuousLinearMap.adjoint (W θ) (basisVec j))) (e n) := by
      simp [ContinuousLinearMap.adjoint_inner_left]
    have k2 : ∀ j, inner ℂ (W θ (e n)) (basisVec j) =
        inner ℂ (e n) (ContinuousLinearMap.adjoint (W θ) (basisVec j)) := by
      simp [ContinuousLinearMap.adjoint_inner_right]
    rw [ContinuousLinearMap.smul_apply, real_smul_eq_coe_smul_ell2, inner_smul_right,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, inner_diagN,
      k1 0, k1 1, k2 0, k2 1]
    ring
  have hI : ∀ j n, IntervalIntegrable (fun θ => b θ *
      (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec j))) (e n) *
        inner ℂ (e n) (star (W θ) (basisVec j)))) volume 0 (2 * π) := fun j n =>
    intervalIntegrable_ofReal_mul hb hbB (((hXc j).inner continuousOn_const).mul
      (continuousOn_const.inner (huc j)))
  have h1 : ∀ n, inner ℂ (e n)
      (((∫ θ in 0..(2 * π), b θ • (star (W θ) * diagN * W θ)) * X) (e n)) =
      2 * (∫ θ in 0..(2 * π), b θ *
        (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec 0))) (e n) *
          inner ℂ (e n) (star (W θ) (basisVec 0)))) -
      ∫ θ in 0..(2 * π), b θ *
        (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec 1))) (e n) *
          inner ℂ (e n) (star (W θ) (basisVec 1))) := by
    intro n
    set L : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
      (innerSL ℂ (e n)).comp (ContinuousLinearMap.apply ℂ Ell2 (X (e n)))
    have hL : ∀ Y, L Y = inner ℂ (e n) (Y (X (e n))) := fun Y => rfl
    rw [ContinuousLinearMap.mul_apply, ← hL, ← L.intervalIntegral_comp_comm (intervalIntegrable_conj_diagN hW hunit hb hbB)]
    simp_all
  simp_rw [h1]
  have hT : traceForm W b X = 2 * (∫ θ in 0..(2 * π), b θ *
        inner ℂ (star (W θ) (basisVec 0)) (X (star (W θ) (basisVec 0)))) -
      ∫ θ in 0..(2 * π), b θ *
        inner ℂ (star (W θ) (basisVec 1)) (X (star (W θ) (basisVec 1))) := by
    have hJ : ∀ j, IntervalIntegrable (fun θ => b θ *
        inner ℂ (star (W θ) (basisVec j)) (X (star (W θ) (basisVec j)))) volume 0 (2 * π) :=
      fun j => intervalIntegrable_ofReal_mul hb hbB ((huc j).inner
        (X.continuous.comp_continuousOn (huc j)))
    rw [traceForm, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hJ 0).const_mul 2) (hJ 1)]
    ring
  rw [hT]
  exact ((hS 0).mul_left 2).sub (hS 1)

lemma monodromy_mem_unitary' (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)

/-- Conjugating the trace form by a unitary commuting with `X` does not change it. -/
lemma traceForm_mul_star {V X : Ell2 →L[ℂ] Ell2}
    (hV : V ∈ unitary (Ell2 →L[ℂ] Ell2)) (hVX : V * X = X * V) :
    traceForm (fun θ => W θ * star V) b X = traceForm W b X := by
  unfold traceForm
  simp [← ContinuousLinearMap.mul_apply X V, ← hVX, ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_apply (star V) V, Unitary.star_mul_self_of_mem hV]

/-- **Trace of `U^j Q U^{n-j}`.** For the monodromy `U` of a transport `W` and `j ≤ n`, the
diagonal sum of `U^j Q U^{n-j}` in any Hilbert basis is `(1/4) traceForm W b (U^n)`. -/
theorem hasSum_trace_pow_mul_curvatureOp_mul_pow (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {j n : ℕ} (hjn : j ≤ n)
    {ι : Type*} [Countable ι] (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun m => inner ℂ (e m) ((monodromy W ^ j * curvatureOp γ W * monodromy W ^ (n - j))
        (e m)))
      (1 / 4 * traceForm W (areaDensity γ) (monodromy W ^ n)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn 
     (hK.continuous.sub continuous_const).continuousOn
  set U := monodromy W with hUdef
  set V := U ^ j with hVdef
  have hV  := pow_mem (monodromy_mem_unitary' hK hW) j
  have hpow : U ^ (n - j) = star V * U ^ n := by
    rw [← Nat.add_sub_cancel' hjn, pow_add, ← mul_assoc, Unitary.star_mul_self_of_mem hV, one_mul, Nat.add_sub_cancel' hjn]
  set W' : ℝ → Ell2 →L[ℂ] Ell2 := fun θ => W θ * star V with hW'
  have hW'c : ContinuousOn W' (Icc 0 (2 * π)) := hW.1.mul continuousOn_const
  set L : (Ell2 →L[ℂ] Ell2) →L[ℝ] (Ell2 →L[ℂ] Ell2) :=
    (ContinuousLinearMap.mul ℝ (Ell2 →L[ℂ] Ell2) V).comp
      ((ContinuousLinearMap.mul ℝ (Ell2 →L[ℂ] Ell2)).flip (star V))
  have hL : ∀ Y, L Y = V * (Y * star V) := fun Y => rfl
  have hconj : V * curvatureOp γ W * U ^ (n - j) = (1 / 4 : ℝ) •
      ((∫ θ in 0..(2 * π), areaDensity γ θ • (star (W' θ) * diagN * W' θ)) * U ^ n) := by
    rw [hpow, curvatureOp, mul_smul_comm, smul_mul_assoc, ← mul_assoc]
    rw [mul_assoc V, ← hL, ← L.intervalIntegral_comp_comm (intervalIntegrable_conj_diagN hW.1 (fun θ hθ => transport_mem_unitary hK hW hθ)
    (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ))]
    continuity
  have h := (hasSum_trace_integral_conj_diagN_mul hW'c (fun θ hθ =>
    Submonoid.mul_mem _ (transport_mem_unitary hK hW hθ) (Unitary.star_mem hV))
    (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ)
    (U ^ n) e).mul_left (1 / 4)
  rw [traceForm_mul_star hV (by simp_all [← pow_add, add_comm])] at h
  simp_all [real_smul_eq_coe_smul_ell2, inner_smul_right]

/-- The energy derivative of `U_E^n`: `∂_E U^n = i ∑_{j < n} U^j Q U^{n-j}`. -/
theorem hasDerivAt_monodromy_pow (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) (n : ℕ) :
    HasDerivAt (fun E => monodromy (Ws E) ^ n)
      (Complex.I • ∑ j ∈ Finset.range n,
        monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j)) E := by
  induction n with
  | zero => simpa using hasDerivAt_const E 1
  | succ n ih =>
    refine (ih.mul (hasDerivAt_monodromy_energy hK hclosed hWs hE)).congr_deriv (Eq.symm ?_)
    rw [Finset.sum_range_succ, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Nat.sub_add_comm (Finset.mem_range.mp hj).le]
      rfl
    continuity

/-- Trace-norm bound for `∑_{j < n} U^j Q U^{n-j}`. -/
lemma traceBound_sum_pow_mul_mul_pow {T U : Ell2 →L[ℂ] Ell2} {C : ℝ} (hT : TraceBound T C)
    (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) (n : ℕ) :
    TraceBound (Complex.I • ∑ j ∈ Finset.range n, U ^ j * T * U ^ (n - j)) (n * C) := by
  have hs : ∀ m : ℕ, m ≤ n →
      TraceBound (∑ j ∈ Finset.range m, U ^ j * T * U ^ (n - j)) (m * C) := by
    intro m
    induction m with
    | zero => simpa using TraceBound.zero
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul]
      exact (ih (by omega)).add ((hT.unitary_mul (pow_mem hU m)).mul_unitary (pow_mem hU _))
  have := (hs n le_rfl).smul Complex.I
  simp_all

/-- The trace `i n tr(Q_E U_E^n) = i n (1/4) traceForm W_E b (U_E^n)` of `∂_E U_E^n`. -/
def tauE (γ : ℝ → ℂ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (n : ℕ) (E : ℝ) : ℂ :=
  Complex.I * n * ((1 / 4 : ℂ) * traceForm (Ws E) (areaDensity γ) (monodromy (Ws E) ^ n))

/-- The diagonal sum of `∂_E U_E^n` is `tauE`. -/
theorem hasSum_trace_deriv_monodromy_pow {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ) (n : ℕ)
    {ι : Type*} [Countable ι] (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun m => inner ℂ (e m) ((Complex.I • ∑ j ∈ Finset.range n,
        monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j)) (e m)))
      (tauE γ Ws n E) := by
  have h := (hasSum_sum (s := Finset.range n) (fun j hj =>
    hasSum_trace_pow_mul_curvatureOp_mul_pow hK (hWs E) (Finset.mem_range.mp hj).le e)).mul_left
      Complex.I
  rw [Finset.sum_const, Finset.card_range] at h
  convert h using 1
  · simp [inner_smul_right, inner_sum]
  · rw [tauE]; ring

/-- **Integrated trace identity.** For `0 < E₁ ≤ E₂`, if the diagonal sums of `U_{E_i}^n - I` in a
Hilbert basis are `T_i`, then `T₂ - T₁ = ∫_{E₁}^{E₂} tauE`. -/
theorem trace_monodromy_pow_sub (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E₁ E₂ : ℝ} (h1 : 0 < E₁) (h12 : E₁ ≤ E₂) (n : ℕ)
    (e : HilbertBasis ℕ ℂ Ell2) {T₁ T₂ : ℂ}
    (hT₁ : HasSum (fun m => inner ℂ (e m) ((monodromy (Ws E₁) ^ n - 1) (e m))) T₁)
    (hT₂ : HasSum (fun m => inner ℂ (e m) ((monodromy (Ws E₂) ^ n - 1) (e m))) T₂) :
    IntervalIntegrable (tauE γ Ws n) volume E₁ E₂ ∧
      T₂ - T₁ = ∫ E in E₁..E₂, tauE γ Ws n E := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn 
     (hK.continuous.sub continuous_const).continuousOn
  set C0 : ℝ := 1 / 4 * ((R * K * 3) * (2 * π))
  set D : ℝ → Ell2 →L[ℂ] Ell2 := fun E => Complex.I • ∑ j ∈ Finset.range n,
    monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j) with hD
  have hTB : ∀ E, TraceBound (D E) (n * C0) := fun E =>
    traceBound_sum_pow_mul_mul_pow (traceBound_curvatureOp hK hR (hWs E))
      (monodromy_mem_unitary' hK (hWs E)) n
  have hposc : ∀ E ∈ uIcc E₁ E₂, 0 < E := fun E hE => by
    rw [uIcc_of_le h12] at hE; grind
  set g : ℕ → ℝ → ℂ := fun m E => inner ℂ (e m) ((monodromy (Ws E) ^ n) (e m)) with hg
  set d : ℕ → ℝ → ℂ := fun m E => inner ℂ (e m) (D E (e m)) with hd
  have hgd : ∀ m E, 0 < E → HasDerivAt (g m) (d m E) E := by
    intro m E hE
    set L : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
      (innerSL ℂ (e m)).comp (ContinuousLinearMap.apply ℂ Ell2 (e m))
    exact (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt E
      (hasDerivAt_monodromy_pow hK hclosed hWs hE n)
  have hpart : ∀ (M : ℕ) E, ‖∑ m ∈ Finset.range M, d m E‖ ≤ n * C0 := by
    intro M E
    have := hTB E (Fin M) (fun i => e i) (fun i => e i)
      (e.orthonormal.comp _ (fun i j h => Fin.val_injective h))
      (e.orthonormal.comp _ (fun i j h => Fin.val_injective h))
    rwa [Fin.sum_univ_eq_sum_range (fun m => inner ℂ (e m) (D E (e m)))] at this
  have hone : ∀ m E, ‖d m E‖ ≤ n * C0 := by
    intro m E
    have := hTB E Unit (fun _ => e m) (fun _ => e m)
      (e.orthonormal.comp _ (fun i j _ => Subsingleton.elim i j))
      (e.orthonormal.comp _ (fun i j _ => Subsingleton.elim i j))
    simp_all
  have hdm : ∀ m, AEStronglyMeasurable (d m) (volume.restrict (uIoc E₁ E₂)) := by
    intro m
    refine (stronglyMeasurable_deriv (g m)).aestronglyMeasurable.congr ?_
    exact (ae_restrict_iff' measurableSet_uIoc).mpr
      (Eventually.of_forall fun E hE => (hgd m E (fun E hE => by
    grind E hE)).deriv)
  have hdi  := fun m =>
    IntervalIntegrable.mono_fun' (intervalIntegrable_const ) (hdm m)
      (Eventually.of_forall fun E => hone m E)
  have hftc  := fun m =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun E hE => hgd m E (hposc E hE)) (hdi m)
  -- partial sums
  have hS : ∀ M : ℕ, ∫ E in E₁..E₂, (∑ m ∈ Finset.range M, d m E) =
      ∑ m ∈ Finset.range M, (g m E₂ - g m E₁) := by
    intro M
    rw [intervalIntegral.integral_finset_sum (fun m _ => hdi m)]
    simp_all
  have hlimS : ∀ E ∈ uIoc E₁ E₂, Tendsto (fun M => ∑ m ∈ Finset.range M, d m E) atTop
      (𝓝 (tauE γ Ws n E)) := fun E _ =>
    (hasSum_trace_deriv_monodromy_pow hK hWs E n e).tendsto_sum_nat
  refine ⟨?_, tendsto_nhds_unique (by
    have := (hT₂.sub hT₁).tendsto_sum_nat
    simp_all [inner_sub_right]) (intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => n * C0)
    (Eventually.of_forall fun M => Finset.aestronglyMeasurable_fun_sum _ (fun m _ => hdm m))
    (Eventually.of_forall fun M => Eventually.of_forall fun E _ => hpart M E)
    intervalIntegrable_const
    (Eventually.of_forall fun E hE => hlimS E hE))⟩
  refine IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := n * C0)) ?_ ?_
  · exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun M => Finset.aestronglyMeasurable_fun_sum _ (fun m _ => hdm m))
      ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall hlimS))
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun E hE => ?_)
    exact le_of_tendsto' ((hlimS E hE).norm) (fun M => hpart M E)

lemma norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
    rw [h, Nat.cast_succ, add_mul, one_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    simp_all

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {U : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- The cut phase sum as a sum over the eigenvalue listing. -/
lemma cutPhaseSum_eq_tsum_eigIdx {U : H →L[ℂ] H} {ε : ℝ}
    (hs : Summable (fun p : EigIdx U => argCut ε p.1)) :
    cutPhaseSum ε U = ∑' p : EigIdx U, argCut ε p.1 := by
  rw [hs.tsum_sigma' (fun z => (hasSum_fintype _).summable), cutPhaseSum]
  continuity 

omit [CompleteSpace H] in
/-- Exchange of the eigenvalue sum and the Fourier sum. -/
lemma hasSum_fourier_eigen (c : ℕ → ℂ) (hc : Summable (fun n  => n * ‖c n‖))
    (hs : Summable (fun p : EigIdx U => ‖(p.1 : ℂ) - 1‖))
    (hz : ∀ p : EigIdx U, ‖(p.1 : ℂ)‖ = 1) (f : EigIdx U → ℝ)
    (hf : ∀ p : EigIdx U, HasSum (fun n  => 2 * (c n * (p.1 ^ n - 1)).re) (f p)) :
    Summable f ∧ HasSum (fun n  => 2 * (c n * ∑' p : EigIdx U, ((p.1 : ℂ) ^ n - 1)).re)
      (∑' p, f p) := by
  set F : EigIdx U × ℕ → ℝ := fun q => 2 * (c q.2 * (q.1.1 ^ q.2 - 1)).re with hF
  have hFb : ∀ q, ‖F q‖ ≤ 2 * ‖(q.1.1 : ℂ) - 1‖ * (q.2 * ‖c q.2‖) := by
    intro q
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    have h1 := Complex.abs_re_le_norm (c q.2 * (q.1.1 ^ q.2 - 1))
    rw [norm_mul] at h1
    have h3 : ‖c q.2‖ * ‖(q.1.1 : ℂ) ^ q.2 - 1‖ ≤ ‖c q.2‖ * (q.2 * ‖(q.1.1 : ℂ) - 1‖) :=
      mul_le_mul_of_nonneg_left (norm_pow_sub_one_le (hz q.1) q.2) (norm_nonneg _)
    nlinarith
  have hFs : Summable F := by
    refine Summable.of_norm_bounded ?_ hFb
    have := (hs.mul_of_nonneg hc (fun _ => norm_nonneg _) (fun n => by positivity)).mul_left 2
    grind
  have hA := hFs.hasSum
  have h1 := hA.prod_fiberwise hf
  have hpow : ∀ n : ℕ, HasSum (fun p : EigIdx U => (p.1 : ℂ) ^ n - 1)
      (∑' p : EigIdx U, (p.1 ^ n - 1)) := by
    intro n
    refine (Summable.of_norm_bounded (hs.mul_left (n : ℝ)) (fun p => ?_)).hasSum
    exact norm_pow_sub_one_le (hz p) n
  have h2 := ((Equiv.prodComm ℕ (EigIdx U)).hasSum_iff.mpr hA).prod_fiberwise (by
    intro n
    have := (Complex.hasSum_re ((hpow n).mul_left (c n))).mul_left 2
    assumption)
  refine ⟨h1.summable, ?_⟩
  simp_all [h1.tsum_eq]

/-- **Scalar functional calculus.** If `∑ₙ 2 Re(aₙ zⁿ) = 1` at every eigenvalue `z` of `U` and at
`z = 1`, then `∑ₙ 2 Re(aₙ ⟨u, Uⁿ u⟩) = ‖u‖²` for every `u`. -/
lemma hasSum_re_inner_pow (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h1 : HasSum (fun n  => 2 * (a n).re) 1)
    (hz : ∀ p : EigIdx U, HasSum (fun n  => 2 * (a n * p.1 ^ n).re) 1) (u : H) :
    HasSum (fun n  => 2 * (a n * inner ℂ u ((U ^ n) u)).re) (‖u‖ ^ 2) := by
  have he := orthonormal_eigVec hU
  set w : EigIdx U → ℝ := fun p => ‖inner ℂ (eigVec U p) u‖ ^ 2 with hw
  have hprod : ∀ p : EigIdx U, inner ℂ (eigVec U p) u * inner ℂ u (eigVec U p) = w p := by
    intro p
    rw [← inner_conj_symm u (eigVec U p), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set F : ℕ × EigIdx U → ℝ := fun q => 2 * (a q.1 * (q.2.1 ^ q.1 - 1)).re * w q.2 with hF
  have hzn  := norm_eigVal hU
  have hFb : ∀ q, ‖F q‖ ≤ 4 * (‖a q.1‖ * w q.2) := by
    intro q
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_nonneg (by positivity : 0 ≤ w q.2)]
    have h1 := Complex.abs_re_le_norm (a q.1 * (q.2.1 ^ q.1 - 1))
    rw [norm_mul] at h1
    have h3 : ‖a q.1‖ * ‖(q.2.1 : ℂ) ^ q.1 - 1‖ ≤ ‖a q.1‖ * 2 :=
      mul_le_mul_of_nonneg_left (by
      refine (norm_sub_le _ _).trans ?_
      norm_num [hzn]) (norm_nonneg _)
    have hw0 : 0 ≤ w q.2 := by positivity
    nlinarith
  have hFs : Summable F := by
    refine Summable.of_norm_bounded ?_ hFb
    exact ((ha.mul_of_nonneg (he.inner_products_summable u) (fun _ => norm_nonneg _) (fun _ => by positivity)).mul_left 4)
  have hfibp : ∀ p : EigIdx U, HasSum (fun n => F (n, p)) 0 := by
    intro p
    have := ((hz p).sub h1).mul_right (w p)
    simp_all [mul_sub]
  have hA := hFs.hasSum
  have hz0 : ∑' q, F q = 0 := by
    have := (((Equiv.prodComm (EigIdx U) ℕ).hasSum_iff.mpr hA).prod_fiberwise
      (hfibp))
    exact (hasSum_zero.unique this).symm
  have h2 := hA.prod_fiberwise (by
    intro n
    have h := hasSum_inner_pow_sub_one hU hC n u u
    have h' : inner ℂ u ((U ^ n - 1) u) = inner ℂ u ((U ^ n) u) - (‖u‖ ^ 2 : ℝ) := by
      simp [inner_sub_right]
    rw [h'] at h
    have := (Complex.hasSum_re (h.mul_left (a n))).mul_left 2
    convert this using 2 with p
    rw [mul_assoc ((p.1 : ℂ) ^ n - 1), hprod p, ← mul_assoc, Complex.re_mul_ofReal]
    ring)
  rw [hz0] at h2
  have h3 := (h1.mul_right (‖u‖ ^ 2)).add h2
  rw [one_mul, add_zero] at h3
  convert h3 using 2 with n
  rw [mul_sub, Complex.sub_re, Complex.re_mul_ofReal]
  ring

end General

variable {γ : ℝ → ℂ} {K : NNReal}

/-- **The series `∑ₙ 2 Re(cₙ tauE n E)` is `tr Q_E`.** If `∑ₙ 2 Re(i n cₙ zⁿ) = 1` at `z = 1` and at
every eigenvalue of `U_E`, then `∑ₙ 2 Re(cₙ · i n tr(Q_E U_E^n)) = (1/4) ∫₀^{2π} b`. -/
theorem hasSum_re_tauE (hK : LipschitzWith K γ)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ)
    (hC : IsCompactOperator ⇑(monodromy (Ws E) - 1)) (c : ℕ → ℂ)
    (hc : Summable (fun n  => n * ‖c n‖))
    (h1 : HasSum (fun n  => 2 * (Complex.I * n * c n).re) 1)
    (hz : ∀ p : EigIdx (monodromy (Ws E)),
      HasSum (fun n  => 2 * (Complex.I * n * c n * p.1 ^ n).re) 1) :
    HasSum (fun n  => 2 * (c n * tauE γ Ws n E).re)
      ((1 / 4) * ∫ θ in 0..(2 * π), areaDensity γ θ) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn 
     (hK.continuous.sub continuous_const).continuousOn
  have hπ : 0 ≤ 2 * π := by positivity
  have hsub : uIoc 0 (2 * π) ⊆ Icc 0 (2 * π) := by
    grind
  set W := Ws E with hWdef
  set U := monodromy W with hUdef
  set b := areaDensity γ with hbdef
  have hU  := monodromy_mem_unitary' hK (hWs E)
  have hb  := areaDensity_aestronglyMeasurable hK.continuous
  have hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ R * K := fun θ hθ => abs_areaDensity_le hK hR hθ
  set a : ℕ → ℂ := fun n => Complex.I * n * c n with ha
  have has : Summable (fun n => ‖a n‖) := by
    simp_all
  set u : ℕ → ℝ → Ell2 := fun j θ => star (W θ) (basisVec j) with hu
  have huc : ∀ j, ContinuousOn (u j) (Icc 0 (2 * π)) := fun j =>
    (hWs E).1.star.clm_apply continuousOn_const
  have hun : ∀ j, ∀ θ ∈ Icc 0 (2 * π), ‖u j θ‖ = 1 := by
    intro j θ hθ
    exact norm_adjoint_unitary_basisVec (transport_mem_unitary hK (hWs E) hθ) j
  set f : ℕ → ℝ → ℂ := fun n θ => b θ *
    (2 * inner ℂ (u 0 θ) ((U ^ n) (u 0 θ)) - inner ℂ (u 1 θ) ((U ^ n) (u 1 θ))) with hf
  have hfi : ∀ n, IntervalIntegrable (f n) volume 0 (2 * π) := fun n =>
    intervalIntegrable_ofReal_mul hb hbB
      ((continuousOn_const.mul ((huc 0).inner ((U ^ n).continuous.comp_continuousOn (huc 0)))).sub
        ((huc 1).inner ((U ^ n).continuous.comp_continuousOn (huc 1))))
  set G : ℕ → ℝ → ℝ := fun n θ => 2 * (a n * f n θ).re with hG
  have hGi : ∀ n, ∫ θ in 0..(2 * π), G n θ = 2 * (a n * traceForm W b (U ^ n)).re := by
    intro n
    have e1 : traceForm W b (U ^ n) = ∫ θ in 0..(2 * π), f n θ := rfl
    rw [e1, ← intervalIntegral.integral_const_mul, ← Complex.reCLM_apply,
      ← Complex.reCLM.intervalIntegral_comp_comm ((hfi n).const_mul (a n)),
      ← intervalIntegral.integral_const_mul]
    rfl
  have hterm : ∀ n, 2 * (c n * tauE γ Ws n E).re =
      (1 / 4) * ∫ θ in 0..(2 * π), G n θ := by
    intro n
    rw [hGi, tauE]
    have : c n * (Complex.I * n * (1 / 4 * traceForm (Ws E) (areaDensity γ)
        (monodromy (Ws E) ^ n))) = (1 / 4 : ℝ) * (a n * traceForm W b (U ^ n)) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]
    ring
  simp_rw [hterm]
  refine HasSum.mul_left _ ?_
  -- dominated convergence in `θ`
  have hpt : ∀ θ ∈ Icc 0 (2 * π), HasSum (fun n => G n θ) (b θ) := by
    intro θ hθ
    have h0 := hasSum_re_inner_pow hU hC a has h1 hz (u 0 θ)
    have h1' := hasSum_re_inner_pow hU hC a has h1 hz (u 1 θ)
    rw [hun 0 θ hθ] at h0
    rw [hun 1 θ hθ] at h1'
    have := ((h0.mul_left 2).sub h1').mul_left (b θ)
    convert this using 1
    · funext n
      simp only [hG]
      rw [show a n * (b θ * (2 * inner ℂ (u 0 θ) ((U ^ n) (u 0 θ)) -
          inner ℂ (u 1 θ) ((U ^ n) (u 1 θ)))) = b θ *
          (2 * (a n * inner ℂ (u 0 θ) ((U ^ n) (u 0 θ))) -
            a n * inner ℂ (u 1 θ) ((U ^ n) (u 1 θ))) by ring]
      simp 
      ring
    ring
  have hGb : ∀ n, ∀ θ ∈ Icc 0 (2 * π), ‖G n θ‖ ≤ |b θ| * (6 * ‖a n‖) := by
    intro n θ hθ
    have hk : ∀ j, ‖inner ℂ (u j θ) ((U ^ n) (u j θ))‖ ≤ 1 := by
      intro j
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hun j θ hθ, one_mul]
      calc ‖(U ^ n) (u j θ)‖ ≤ ‖U ^ n‖ * ‖u j θ‖ := (U ^ n).le_opNorm _
        _ ≤ 1 * 1 := by
          rw [hun j θ hθ]
          exact mul_le_mul_of_nonneg_right (norm_le_one_of_mem_unitary (pow_mem hU n))
            zero_le_one
        _ = 1 := by ring
    have hf3 : ‖f n θ‖ ≤ |b θ| * 3 := by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_ofNat]
      grind) (abs_nonneg _)
    calc ‖G n θ‖ = 2 * |(a n * f n θ).re| := by
          simp_all
      _ ≤ 2 * (‖a n‖ * ‖f n θ‖) := by
          gcongr; exact (Complex.abs_re_le_norm _).trans (norm_mul_le _ _)
      _ ≤ 2 * (‖a n‖ * (|b θ| * 3)) := by gcongr
      _ = |b θ| * (6 * ‖a n‖) := by ring
  have hsumb : ∀ θ, HasSum (fun n => |b θ| * (6 * ‖a n‖)) (|b θ| * (6 * ∑' n, ‖a n‖)) :=
    fun θ => (has.hasSum.mul_left 6).mul_left _
  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n θ => |b θ| * (6 * ‖a n‖)) (fun n =>
    ((Complex.continuous_re.comp_aestronglyMeasurable
      ((intervalIntegrable_iff.mp ((hfi n).const_mul (a n))).aestronglyMeasurable)).const_mul 2))
    (fun n => Eventually.of_forall fun θ hθ => hGb n θ (hsub hθ))
    (Eventually.of_forall fun θ _ => (hsumb θ).summable)
    ((intervalIntegrable_abs_mul hb hbB continuousOn_const).congr (fun θ _ => (hsumb θ).tsum_eq.symm))
    (Eventually.of_forall fun θ hθ => hpt θ (hsub hθ))
  assumption

/-- `‖tauE‖ ≤ n · (trace-norm bound of `Q_E`)`. -/
lemma norm_tauE_le (hK : LipschitzWith K γ)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) (E : ℝ) (n : ℕ) :
    ‖tauE γ Ws n E‖ ≤ n * (1 / 4 * ((R * K * 3) * (2 * π))) := by
  set e : HilbertBasis ℕ ℂ Ell2 := default
  refine le_of_tendsto' (hasSum_trace_deriv_monodromy_pow hK hWs E n e).tendsto_sum_nat.norm
    (fun M => ?_)
  have := traceBound_sum_pow_mul_mul_pow (traceBound_curvatureOp hK hR (hWs E))
    (monodromy_mem_unitary' hK (hWs E)) n (Fin M) (fun i => e i) (fun i => e i)
    (e.orthonormal.comp _ (fun i j h => Fin.val_injective h))
    (e.orthonormal.comp _ (fun i j h => Fin.val_injective h))
  rwa [Fin.sum_univ_eq_sum_range (fun m => inner ℂ (e m) ((Complex.I • ∑ j ∈ Finset.range n,
    monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j)) (e m)))] at this

/-- A uniform cut neighbourhood: if `e^{iε}` avoids the spectrum of `U_E` for `E ∈ [E₁, E₂]`,
then all eigenvalues of these `U_E` stay at distance `≥ r` from `e^{iε}`, for some `r > 0` with
also `r ≤ |1 - e^{iε}|`. -/
lemma exists_cut_radius (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) {E₁ E₂ : ℝ}
    (h1 : 0 < E₁)
    (hcut : ∀ E ∈ Icc E₁ E₂, Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    ∃ r, 0 < r ∧ r ≤ ‖1 - Complex.exp (ε * Complex.I)‖ ∧
      ∀ E ∈ Icc E₁ E₂, ∀ (z : ℂ) (v : Ell2), v ≠ 0 → monodromyAt γ E v = z • v →
        r ≤ ‖z - Complex.exp (ε * Complex.I)‖ := by
  set w := Complex.exp (ε * Complex.I) with hw
  set G : ℝ × ℂ → Ell2 →L[ℂ] Ell2 := fun q => algebraMap ℂ _ q.2 - monodromyAt γ q.1 with hG
  have hGc : ContinuousOn G (Ioi 0 ×ˢ univ) := by
    intro q hq
    refine ContinuousAt.continuousWithinAt ?_
    exact ((continuous_algebraMap ℂ (Ell2 →L[ℂ] Ell2)).continuousAt.comp continuousAt_snd).sub
      ((continuousAt_monodromyAt hK hclosed hq.1).comp continuousAt_fst)
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_Icc.prod isCompact_singleton).exists_thickening_subset_open (hGc.isOpen_inter_preimage (isOpen_Ioi.prod isOpen_univ) Units.isOpen) (by
    rintro ⟨E, z⟩ ⟨hE, hz⟩
    subst hz
    refine ⟨⟨h1.trans_le hE.1, mem_univ _⟩, ?_⟩
    exact spectrum.notMem_iff.mp (hcut E hE))
  refine ⟨min δ ‖1 - w‖, lt_min hδ (by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    rw [eq_comm, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h2 : ε = n * (2 * π) := by
      have := congrArg Complex.im hn
      simpa using this
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
      nlinarith 
    · simp_all
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      nlinarith), min_le_right _ _, fun E hE z v hv hUv => ?_⟩
  by_contra hlt
  have hmem : (E, z) ∈ Metric.thickening δ (Icc E₁ E₂ ×ˢ {w}) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(E, w), ⟨hE, mem_singleton _⟩, ?_⟩
    simp_all [dist_eq_norm]
  obtain ⟨u, hu⟩ := (hδO hmem).2
  apply hv
  calc v = ((↑u⁻¹ : Ell2 →L[ℂ] Ell2) * ↑u) v := by norm_num
    _ = 0 := by simp_all

/-- The eigenvalues `z ≠ 1` of the monodromy, listed with multiplicity, satisfy
`∑ |z_p - 1| < ∞`. -/
lemma summable_norm_eigIdx_sub_one (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) :
    Summable (fun p : EigIdx (monodromy W) => ‖(p.1 : ℂ) - 1‖) := by
  rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  refine (summable_eigenMult_monodromy hK hclosed hE hW).congr (fun z => ?_)
  simp 

/-- **Per-energy Fourier expansion of the cut phase sum.** If the eigenvalues of `U_E` avoid the
`r`-neighbourhood of `e^{iε}` on which the Fourier series of `argCut ε` converges, then the cut phase
sum is `∑ₙ 2 Re(cₙ tr(U_E^n - I))`, with `tr(U_E^n - I) = ∑_p (z_p^n - 1)` the diagonal sum of
`U_E^n - I` in any Hilbert basis. -/
lemma cutPhaseSum_fourier (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) {ε : ℝ} (c : ℕ → ℂ) (hc : Summable (fun n  => n * ‖c n‖))
    (hf : ∀ p : EigIdx (monodromy W),
      HasSum (fun n  => 2 * (c n * (p.1 ^ n - 1)).re) (argCut ε p.1))
    (e : HilbertBasis ℕ ℂ Ell2) :
    (∀ n : ℕ, HasSum (fun m => inner ℂ (e m) ((monodromy W ^ n - 1) (e m)))
      (∑' p : EigIdx (monodromy W), (p.1 ^ n - 1))) ∧
    HasSum (fun n  => 2 * (c n * ∑' p : EigIdx (monodromy W), ((p.1 : ℂ) ^ n - 1)).re)
      (cutPhaseSum ε (monodromy W)) := by
  have hU := monodromy_mem_unitary' hK hW
  have hs := summable_norm_eigIdx_sub_one hK hclosed hE hW
  have hz := norm_eigVal hU
  refine ⟨fun n => hasSum_trace_pow_sub_one hU (isCompactOperator_monodromy_sub_one hK hclosed hE hW) e n ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => norm_pow_sub_one_le (hz p) n) (hs.mul_left (n : ℝ))
  · obtain ⟨hfs, hsum⟩ := hasSum_fourier_eigen c hc hs hz _ hf
    rwa [cutPhaseSum_eq_tsum_eigIdx hfs]

/-- **Lemma 9.3, analytic core.** For a closed Lipschitz curve, `0 < ε < 2π`, and an interval
`[E₁, E₂] ⊂ (0, ∞)` on which `e^{iε}` avoids the spectrum of `U_E`, the cut phase sum increases at
the constant rate `(1/4) ∫₀^{2π} b`. -/
theorem cutPhaseSum_monodromyAt_sub' (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    cutPhaseSum ε (monodromyAt γ E₂) - cutPhaseSum ε (monodromyAt γ E₁) =
      (E₂ - E₁) * ((1 / 4) * ∫ θ in 0..(2 * π), areaDensity γ θ) := by
  obtain ⟨r, hr, hr1, hrE⟩ := exists_cut_radius hK hclosed hε0 hε h1 hcut
  obtain ⟨c, hc, hcF⟩ := exists_cutFourier hε0 hε hr
  choose Ws hWs using transport_exists_of_lipschitz γ hK
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn 
     (hK.continuous.sub continuous_const).continuousOn
  set C0 : ℝ := 1 / 4 * ((R * K * 3) * (2 * π))
  set τ₀ : ℝ := (1 / 4) * ∫ θ in 0..(2 * π), areaDensity γ θ
  set e : HilbertBasis ℕ ℂ Ell2 := default
  set T : ℕ → ℝ → ℂ := fun n E => ∑' p : EigIdx (monodromy (Ws E)), (p.1 ^ n - 1) with hT
  -- eigenvalues of `U_E` for `E ∈ [E₁, E₂]` stay away from the cut
  have hfar : ∀ E ∈ Icc E₁ E₂, ∀ p : EigIdx (monodromy (Ws E)),
      ‖(p.1 : ℂ)‖ = 1 ∧ r ≤ ‖p.1 - Complex.exp (ε * Complex.I)‖ := by
    intro E hE p
    have hU := monodromy_mem_unitary' hK (hWs E)
    refine ⟨norm_eigVal hU p, hrE E hE _ (eigVec _ p) ((orthonormal_eigVec hU).ne_zero p) ?_⟩
    rw [monodromyAt_eq hK (hWs E)]
    exact eigVec_eigen _ p
  have hE0 : ∀ E ∈ Icc E₁ E₂, 0 ≤ E := fun E hE => (h1.trans_le hE.1).le
  have hper : ∀ E ∈ Icc E₁ E₂, (∀ n : ℕ, HasSum (fun m => inner ℂ (e m)
      ((monodromy (Ws E) ^ n - 1) (e m))) (T n E)) ∧
      HasSum (fun n  => 2 * (c n * T n E).re) (cutPhaseSum ε (monodromyAt γ E)) := by
    intro E hE
    rw [monodromyAt_eq hK (hWs E)]
    exact cutPhaseSum_fourier hK hclosed (hE0 E hE) (hWs E) c hc
      (fun p => (hcF _ (hfar E hE p).1 (hfar E hE p).2).1) e
  have hE₁ : E₁ ∈ Icc E₁ E₂ := ⟨le_rfl, h12⟩
  have hE₂ : E₂ ∈ Icc E₁ E₂ := ⟨h12, le_rfl⟩
  have hint := fun n => trace_monodromy_pow_sub hK hclosed hWs h1 h12 n e
    ((hper E₁ hE₁).1 n) ((hper E₂ hE₂).1 n)
  -- left side: difference of the two Fourier expansions
  have hL : HasSum (fun n  => ∫ E in E₁..E₂, 2 * (c n * tauE γ Ws n E).re)
      (cutPhaseSum ε (monodromyAt γ E₂) - cutPhaseSum ε (monodromyAt γ E₁)) := by
    convert (hper E₂ hE₂).2.sub (hper E₁ hE₁).2 using 1
    funext n
    rw [intervalIntegral.integral_const_mul]
    have h := Complex.reCLM.intervalIntegral_comp_comm ((hint n).1.const_mul (c n))
    simp only [Complex.reCLM_apply] at h
    rw [h, intervalIntegral.integral_const_mul, ← (hint n).2]
    simp [mul_sub]
  -- right side: dominated convergence
  have huIoc : ∀ E ∈ uIoc E₁ E₂, E ∈ Icc E₁ E₂ := fun E hE => by
    grind
  have hR' : HasSum (fun n  => ∫ E in E₁..E₂, 2 * (c n * tauE γ Ws n E).re)
      (∫ _ in E₁..E₂, τ₀) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => 2 * (n * ‖c n‖) * C0) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · have := ((intervalIntegrable_iff.mp ((hint n).1.const_mul (c n))).aestronglyMeasurable)
      fun_prop
    · refine Eventually.of_forall fun E _ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_two]
      have h1 := Complex.abs_re_le_norm (c n * tauE γ Ws n E)
      rw [norm_mul] at h1
      have h3 : ‖c n‖ * ‖tauE γ Ws n E‖ ≤ ‖c n‖ * (n * C0) :=
        mul_le_mul_of_nonneg_left (norm_tauE_le hK hWs hR E n) (norm_nonneg _)
      nlinarith
    · exact Eventually.of_forall fun E _ => (hc.mul_left 2).mul_right C0
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun E hE => ?_
      have hEI := huIoc E hE
      refine hasSum_re_tauE hK hWs E
        (isCompactOperator_monodromy_sub_one hK hclosed (hE0 E hEI) (hWs E)) c hc ?_
        (fun p => (hcF _ (hfar E hEI p).1 (hfar E hEI p).2).2)
      simpa using (hcF 1 (by simp) hr1).2
  rw [hL.unique hR', intervalIntegral.integral_const, smul_eq_mul]

end PolyaNeumann

end
