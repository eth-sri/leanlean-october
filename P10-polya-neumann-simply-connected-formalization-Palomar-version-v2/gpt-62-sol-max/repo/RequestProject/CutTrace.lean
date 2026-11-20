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

/-- `⟨x, D_N y⟩ = 2 ⟨e₀, y⟩ ⟨x, e₀⟩ - ⟨e₁, y⟩ ⟨x, e₁⟩`. -/
lemma inner_diagN (x y : Ell2) :
    inner ℂ x (diagN y) = 2 * (inner ℂ (basisVec 0) y * inner ℂ x (basisVec 0)) -
      inner ℂ (basisVec 1) y * inner ℂ x (basisVec 1) := by
  simp  [diagN, ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, inner_sub_right, inner_smul_right, basisVec]

section TraceFunctional
set_option maxSynthPendingDepth 4

variable {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B)

def diagPair (W : ℝ → Ell2 →L[ℂ] Ell2) (θ : ℝ) : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
  let u (j : ℕ) := star (W θ) (basisVec j)
  2 • (innerSL ℂ (u 0)).comp (ContinuousLinearMap.apply ℂ Ell2 (u 0)) -
    (innerSL ℂ (u 1)).comp (ContinuousLinearMap.apply ℂ Ell2 (u 1))

private lemma diagPair_apply (θ : ℝ) (X : Ell2 →L[ℂ] Ell2) :
    diagPair W θ X = 2 * inner ℂ (star (W θ) (basisVec 0)) (X (star (W θ) (basisVec 0))) -
      inner ℂ (star (W θ) (basisVec 1)) (X (star (W θ) (basisVec 1))) := by
  simp [diagPair, two_mul]

/-- The trace functional of the integrated conjugates of `diagN`. -/
def traceForm (W : ℝ → Ell2 →L[ℂ] Ell2) (b : ℝ → ℝ) : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), b θ • diagPair W θ

include hW in
private lemma continuousOn_diagPair : ContinuousOn (diagPair W) (Icc 0 (2 * π)) := by
  have h (j : ℕ) : ContinuousOn (fun θ => star (W θ) (basisVec j)) (Icc 0 (2 * π)) :=
    hW.star.clm_apply continuousOn_const
  have hq (j : ℕ) :=
    ((innerSL ℂ).continuous.comp_continuousOn (h j)).clm_comp
      ((ContinuousLinearMap.apply ℂ Ell2).continuous.comp_continuousOn (h j))
  exact ((hq 0).const_smul _).sub (hq 1)

include hW hb hbB in
private lemma traceForm_apply (X : Ell2 →L[ℂ] Ell2) : traceForm W b X =
    ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) * diagPair W θ X := by
  let ev := ContinuousLinearMap.apply ℂ ℂ X
  change ev (∫ θ in (0 : ℝ)..(2 * π), b θ • diagPair W θ) = _
  rw [← ev.intervalIntegral_comp_comm ((intervalIntegrable_of_abs_le hb hbB).smul_continuousOn
    (by simpa only [uIcc_of_le Real.two_pi_pos.le] using continuousOn_diagPair hW))]
  simp  [ContinuousLinearMap.apply_apply, Complex.real_smul, ev]

end TraceFunctional

lemma norm_inner_mul_inner_le (u v w : Ell2) :
    ‖inner ℂ v w * inner ℂ w u‖ ≤ (‖inner ℂ w v‖ ^ 2 + ‖inner ℂ w u‖ ^ 2) / 2 := by
  rw [norm_mul, norm_inner_symm v w]
  nlinarith [sq_nonneg (‖inner ℂ w v‖ - ‖inner ℂ w u‖)]

section

variable {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ} (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B)
include b hb B hbB

lemma intervalIntegrable_ofReal_mul {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 (2 * π))) :
    IntervalIntegrable (fun θ => (b θ : ℂ) * f θ) volume 0 (2 * π) := by
  simp  [← Complex.real_smul]
  exact (intervalIntegrable_of_abs_le hb hbB).smul_continuousOn (by rwa [uIcc_of_le Real.two_pi_pos.le])

lemma intervalIntegrable_abs_mul {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 (2 * π))) :
    IntervalIntegrable (fun θ => |b θ| * f θ) volume 0 (2 * π) :=
  (intervalIntegrable_of_abs_le hb hbB).abs.mul_continuousOn (by rwa [uIcc_of_le Real.two_pi_pos.le])

end

/-- Parseval under an integral: `∑ₙ ∫ b ⟨v, eₙ⟩ ⟨eₙ, w⟩ = ∫ b ⟨v, w⟩`. -/
lemma hasSum_integral_inner_mul_inner {v w : ℝ → Ell2} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hw : ContinuousOn w (Icc 0 (2 * π))) {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun n => ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) * (inner ℂ (v θ) (e n) * inner ℂ (e n) (w θ)))
      (∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) * inner ℂ (v θ) (w θ)) := by
  have hgs : ∀ θ, HasSum (fun n => |b θ| * ((‖inner ℂ (e n) (v θ)‖ ^ 2 +
      ‖inner ℂ (e n) (w θ)‖ ^ 2) / 2)) (|b θ| * ((‖v θ‖ ^ 2 + ‖w θ‖ ^ 2) / 2)) := fun θ =>
    (((hasSum_norm_inner_sq e _).add (hasSum_norm_inner_sq e _)).div_const 2).mul_left _
  have hGi :=
    intervalIntegrable_abs_mul hb hbB (((hv.norm.pow 2).add (hw.norm.pow 2)).div_const 2)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n θ => |b θ| * ((‖inner ℂ (e n) (v θ)‖ ^ 2 + ‖inner ℂ (e n) (w θ)‖ ^ 2) / 2))
    (fun n => ?_) (fun n => Eventually.of_forall fun θ _ => ?_)
    (Eventually.of_forall fun θ _ => (hgs θ).summable) ?_
    (Eventually.of_forall fun θ _ => (e.hasSum_inner_mul_inner (v θ) (w θ)).mul_left _)
  · rw [uIoc_of_le Real.two_pi_pos.le]
    exact (intervalIntegrable_ofReal_mul hb hbB
      ((hv.inner (continuousOn_const (c := e n))).mul
        ((continuousOn_const (c := e n)).inner hw))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_inner_mul_inner_le _ _ _) (abs_nonneg _)
  · exact hGi.congr (fun θ _ => (hgs θ).tsum_eq.symm)

/-- Trace of a weighted integral of conjugates of `diagN`, with bounded operators
on either side. The answer uses their cyclic product. -/
theorem hasSum_trace_integral_conj_diagN {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : ContinuousOn W (Icc 0 (2 * π)))
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) (X Y : Ell2 →L[ℂ] Ell2)
    {ι : Type*} [Countable ι] (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun n => inner ℂ (e n)
        ((X * (∫ θ in (0 : ℝ)..(2 * π), b θ • (star (W θ) * diagN * W θ)) * Y) (e n)))
      (traceForm W b (Y * X)) := by
  let u (j : ℕ) (θ : ℝ) := star (W θ) (basisVec j)
  let v (j : ℕ) (θ : ℝ) := ContinuousLinearMap.adjoint Y (u j θ)
  let w (j : ℕ) (θ : ℝ) := X (u j θ)
  have hu (j : ℕ) : ContinuousOn (u j) (Icc 0 (2 * π)) :=
    hW.star.clm_apply continuousOn_const
  have hv (j : ℕ) :=
    (ContinuousLinearMap.adjoint Y).continuous.comp_continuousOn (hu j)
  have hw (j : ℕ) :=
    X.continuous.comp_continuousOn (hu j)
  let F (j : ℕ) (θ : ℝ) := (b θ : ℂ) * inner ℂ (v j θ) (w j θ)
  let G (j : ℕ) (n : ι) (θ : ℝ) := (b θ : ℂ) * (inner ℂ (v j θ) (e n) * inner ℂ (e n) (w j θ))
  have hF j : IntervalIntegrable (F j) volume 0 (2 * π) :=
    intervalIntegrable_ofReal_mul hb hbB ((hv j).inner (hw j))
  have hG j n : IntervalIntegrable (G j n) volume 0 (2 * π) :=
    intervalIntegrable_ofReal_mul hb hbB
      (((hv j).inner continuousOn_const).mul (continuousOn_const.inner (hw j)))
  have hS (j : ℕ) : HasSum (fun n => ∫ θ in (0 : ℝ)..(2 * π), G j n θ)
      (∫ θ in (0 : ℝ)..(2 * π), F j θ) :=
    hasSum_integral_inner_mul_inner (hv j) (hw j) hb hbB e
  have eq₁ (n : ι) :
      2 * (∫ θ in (0 : ℝ)..(2 * π), G 0 n θ) - (∫ θ in (0 : ℝ)..(2 * π), G 1 n θ) =
      inner ℂ (e n) ((X * (∫ θ in (0 : ℝ)..(2 * π), b θ • (star (W θ) * diagN * W θ)) * Y) (e n)) := by
    let L := (innerSL ℂ (e n)).comp (X.comp (ContinuousLinearMap.apply ℂ Ell2 (Y (e n))))
    change _ = L (∫ θ in (0 : ℝ)..(2 * π), b θ • (star (W θ) * diagN * W θ))
    rw [← L.intervalIntegral_comp_comm (intervalIntegrable_conj_diagN hW hb hbB),
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub ((hG 0 n).const_mul 2) (hG 1 n)]
    congr 1
    funext θ
    simp only [G, v, w, u, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, real_smul_eq_coe_smul_ell2, map_smul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    have hleft (z : Ell2) : inner ℂ (e n) (X (ContinuousLinearMap.adjoint (W θ) z)) =
        inner ℂ (W θ (ContinuousLinearMap.adjoint X (e n))) z := by
      rw [← ContinuousLinearMap.adjoint_inner_left X, ContinuousLinearMap.adjoint_inner_right (W θ)]
    simp  [hleft, inner_diagN, smul_eq_mul]
    ring
  have eq₂ :
      2 * (∫ θ in (0 : ℝ)..(2 * π), F 0 θ) - (∫ θ in (0 : ℝ)..(2 * π), F 1 θ) =
      traceForm W b (Y * X) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub ((hF 0).const_mul 2) (hF 1)]
    simp only [traceForm_apply hW hb hbB, F, v, w, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.mul_apply, diagPair_apply]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  simpa only [eq₁, eq₂] using ((hS 0).mul_left 2).sub (hS 1)

/-- All terms of the power derivative have the same diagonal sum. -/
theorem hasSum_trace_pow_mul_curvatureOp_mul_pow {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {j n : ℕ} (hjn : j ≤ n)
    {ι : Type*} [Countable ι] (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun m => inner ℂ (e m) ((monodromy W ^ j * curvatureOp γ W * monodromy W ^ (n - j))
        (e m)))
      ((1 / 4 : ℂ) * traceForm W (areaDensity γ) (monodromy W ^ n)) := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  have h := (hasSum_trace_integral_conj_diagN hW.1
    (areaDensity_aestronglyMeasurable hK.continuous) (fun _ => abs_areaDensity_le hK hR)
    (monodromy W ^ j) (monodromy W ^ (n - j)) e).mul_left (1 / 4 : ℂ)
  rw [← pow_add, Nat.sub_add_cancel hjn] at h
  convert h using 2 with m
  simp [curvatureOp, real_smul_eq_coe_smul_ell2, inner_smul_right]

/-- Curvature contribution to the derivative of a monodromy power. -/
private def powerCurvature (U Q : Ell2 →L[ℂ] Ell2) (n : ℕ) : Ell2 →L[ℂ] Ell2 :=
  Complex.I • ∑ j ∈ Finset.range n, U ^ j * Q * U ^ (n - j)

/-- The energy derivative of `U_E^n`: `∂_E U^n = i ∑_{j < n} U^j Q U^{n-j}`. -/
private theorem hasDerivAt_monodromy_pow {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) (n : ℕ) :
    HasDerivAt (fun E => monodromy (Ws E) ^ n)
      (powerCurvature (monodromy (Ws E)) (curvatureOp γ (Ws E)) n) E := by
  let U := monodromy (Ws E)
  let Q := curvatureOp γ (Ws E)
  let f (j : ℕ) := U ^ j * Q * U ^ (n - j)
  refine ((hasDerivAt_monodromy_energy hK hclosed hWs hE).fun_pow' n).congr_deriv ?_
  symm
  change Complex.I • (∑ j ∈ Finset.range n, f j) =
    ∑ j ∈ Finset.range n, U ^ (n.pred - j) * (Complex.I • (Q * U)) * U ^ j
  rw [← Finset.sum_range_reflect f, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [f, Nat.pred_eq_sub_one, mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [← pow_succ']
  rw [show n - (n - 1 - j) = j + 1 by have := Finset.mem_range.mp hj; omega]

/-- Trace-norm bound for `∑_{j < n} U^j Q U^{n-j}`. -/
private lemma traceBound_powerCurvature {T U : Ell2 →L[ℂ] Ell2} {C : ℝ} (hT : TraceBound T C)
    (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) (n : ℕ) :
    TraceBound (powerCurvature U T n) (n * C) := by
  have hs (m : ℕ) : TraceBound (∑ j ∈ Finset.range m, U ^ j * T * U ^ (n - j)) (m * C) := by
    induction m with
    | zero => simpa using TraceBound.zero
    | succ m ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul]
      exact ih.add ((hT.unitary_mul (pow_mem hU m)).mul_unitary (pow_mem hU _))
  simpa [powerCurvature, Complex.norm_I] using (hs n).smul Complex.I

/-- The trace `i n tr(Q_E U_E^n) = i n (1/4) traceForm W_E b (U_E^n)` of `∂_E U_E^n`. -/
def tauE (γ : ℝ → ℂ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (n : ℕ) (E : ℝ) : ℂ :=
  Complex.I * n * ((1 / 4 : ℂ) * traceForm (Ws E) (areaDensity γ) (monodromy (Ws E) ^ n))

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
include γ K hK

/-- The diagonal sum of `∂_E U_E^n` is `tauE`. -/
private theorem hasSum_trace_deriv_monodromy_pow 
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ) (n : ℕ)
    {ι : Type*} [Countable ι] (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun m => inner ℂ (e m) (powerCurvature (monodromy (Ws E)) (curvatureOp γ (Ws E)) n (e m)))
      (tauE γ Ws n E) := by
  have h := (hasSum_sum (s := Finset.range n) (fun j hj =>
    hasSum_trace_pow_mul_curvatureOp_mul_pow hK (hWs E) (Finset.mem_range.mp hj).le e)).mul_left
      Complex.I
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  convert h using 1
  · funext m
    simp only [powerCurvature, ContinuousLinearMap.smul_apply, inner_smul_right,
      ContinuousLinearMap.sum_apply, inner_sum, Pi.smul_apply, smul_eq_mul]
  · rw [tauE]; ring

omit γ K hK in
private lemma norm_sum_trace_range {D : Ell2 →L[ℂ] Ell2} {C : ℝ} (hD : TraceBound D C)
    (e : HilbertBasis ℕ ℂ Ell2) (M : ℕ) : ‖∑ m ∈ Finset.range M, inner ℂ (e m) (D (e m))‖ ≤ C := by
  have ho := e.orthonormal.comp (fun i : Fin M => (i : ℕ)) Fin.val_injective
  simpa only [Function.comp_apply, Fin.sum_univ_eq_sum_range (fun m => inner ℂ (e m) (D (e m)))] using hD (Fin M) _ _ ho ho

/-- **Integrated trace identity.** Apply the fundamental theorem to each finite compression,
then use the trace-norm bound to pass to the limit. -/
theorem trace_monodromy_pow_sub
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E₁ E₂ : ℝ} (h1 : 0 < E₁) (h12 : E₁ ≤ E₂) (n : ℕ)
    (e : HilbertBasis ℕ ℂ Ell2) {T₁ T₂ : ℂ}
    (hT₁ : HasSum (fun m => inner ℂ (e m) ((monodromy (Ws E₁) ^ n - 1) (e m))) T₁)
    (hT₂ : HasSum (fun m => inner ℂ (e m) ((monodromy (Ws E₂) ^ n - 1) (e m))) T₂) :
    IntervalIntegrable (tauE γ Ws n) volume E₁ E₂ ∧
      T₂ - T₁ = ∫ E in E₁..E₂, tauE γ Ws n E := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  let C := n * (1 / 4 * ((R * K * 3) * (2 * π)))
  let D (E : ℝ) := powerCurvature (monodromy (Ws E)) (curvatureOp γ (Ws E)) n
  let L (M : ℕ) := diagFunctional (fun i : Fin M => e i) (fun i => e i)
  let g (M : ℕ) (E : ℝ) := L M (monodromy (Ws E) ^ n - 1)
  let d (M : ℕ) (E : ℝ) := L M (D E)
  have hgd (M) E (hE : E ∈ uIcc E₁ E₂) : HasDerivAt (g M) (d M E) E := by
    rw [uIcc_of_le h12] at hE
    exact ((L M).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt E
      ((hasDerivAt_monodromy_pow hK hclosed hWs (h1.trans_le hE.1) n).sub_const _)
  have hdiag (M) (X : Ell2 →L[ℂ] Ell2) : L M X = ∑ m ∈ Finset.range M, inner ℂ (e m) (X (e m)) := by
    rw [diagFunctional_apply, Fin.sum_univ_eq_sum_range (fun m => inner ℂ (e m) (X (e m)))]
  have hb M E : ‖d M E‖ ≤ C := by
    change ‖L M (D E)‖ ≤ C
    rw [hdiag]
    exact norm_sum_trace_range (traceBound_powerCurvature
      (traceBound_curvatureOp hK hR (hWs E)) (monodromy_mem_unitary' hK (hWs E)) n) e M
  haveI : SecondCountableTopologyEither ℝ ℂ := secondCountableTopologyEither_of_left _ _
  have hm M : AEStronglyMeasurable (d M) (volume.restrict (uIoc E₁ E₂)) :=
    (stronglyMeasurable_deriv (g M)).aestronglyMeasurable.congr <|
      (ae_restrict_iff' measurableSet_uIoc).2 <| .of_forall fun E hE =>
        (hgd M E (uIoc_subset_uIcc hE)).deriv
  have hi M :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (hgd M)
      (IntervalIntegrable.mono_fun' intervalIntegrable_const (hm M) (.of_forall fun E => hb M E))
  have hl E : Tendsto (fun M => d M E) atTop (𝓝 (tauE γ Ws n E)) := by
    simpa only [d, hdiag] using (hasSum_trace_deriv_monodromy_pow hK hWs E n e).tendsto_sum_nat
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (.of_forall hm) (.of_forall fun M => .of_forall fun E _ => hb M E) intervalIntegrable_const
    (.of_forall fun E _ => hl E)
  refine ⟨IntervalIntegrable.mono_fun' intervalIntegrable_const
    (aestronglyMeasurable_of_tendsto_ae atTop hm (.of_forall hl))
    (.of_forall fun E => le_of_tendsto' (hl E).norm (fun M => hb M E)), ?_⟩
  simp_rw [hi] at hlim
  exact tendsto_nhds_unique (by simpa only [g, hdiag] using
    (hT₂.tendsto_sum_nat.sub hT₁.tendsto_sum_nat)) hlim

end

lemma norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
    rw [h, Nat.cast_succ, add_mul, one_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_mul, hz, one_mul]; exact ih

private lemma summable_pow_sub_one {α : Type*} {z : α → ℂ}
    (hz : ∀ p, ‖z p‖ = 1) (hs : Summable fun p => ‖z p - 1‖) (n : ℕ) :
    Summable fun p => z p ^ n - 1 :=
  (hs.mul_left (n : ℝ)).of_norm_bounded fun p => norm_pow_sub_one_le (hz p) n

private lemma norm_two_re_mul_le (c z : ℂ) : ‖2 * (c * z).re‖ ≤ 2 * ‖c‖ * ‖z‖ := by
  simpa [Real.norm_eq_abs, abs_mul, norm_mul, mul_assoc] using
    (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (c * z)) (by norm_num : (0 : ℝ) ≤ 2))

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The cut phase sum as a sum over the eigenvalue listing. -/
lemma cutPhaseSum_eq_tsum_eigIdx {U : H →L[ℂ] H} {ε : ℝ}
    (hs : Summable (fun p : EigIdx U => argCut ε p.1)) :
    cutPhaseSum ε U = ∑' p : EigIdx U, argCut ε p.1 := by
  rw [hs.tsum_sigma' (fun z => (hasSum_fintype _).summable), cutPhaseSum]
  congr 1
  funext z
  rw [tsum_fintype, cutPhaseTerm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [CompleteSpace H] in
/-- Exchange of the eigenvalue sum and the Fourier sum. -/
lemma hasSum_fourier_eigen {U : H →L[ℂ] H} (c : ℕ → ℂ) (hc : Summable (fun n : ℕ => n * ‖c n‖))
    (hs : Summable (fun p : EigIdx U => ‖(p.1 : ℂ) - 1‖))
    (hz : ∀ p : EigIdx U, ‖(p.1 : ℂ)‖ = 1) (f : EigIdx U → ℝ)
    (hf : ∀ p : EigIdx U, HasSum (fun n : ℕ => 2 * (c n * ((p.1 : ℂ) ^ n - 1)).re) (f p)) :
    Summable f ∧ HasSum (fun n : ℕ => 2 * (c n * ∑' p : EigIdx U, ((p.1 : ℂ) ^ n - 1)).re)
      (∑' p, f p) := by
  set F : EigIdx U × ℕ → ℝ := fun q => 2 * (c q.2 * ((q.1.1 : ℂ) ^ q.2 - 1)).re with hF
  have hFb (q) : ‖F q‖ ≤ 2 * ‖(q.1.1 : ℂ) - 1‖ * (q.2 * ‖c q.2‖) := calc
    _ ≤ 2 * ‖c q.2‖ * (q.2 * ‖(q.1.1 : ℂ) - 1‖) :=
      (norm_two_re_mul_le _ _).trans (by gcongr; exact norm_pow_sub_one_le (hz q.1) q.2)
    _ = _ := by ring
  have hFs : Summable F := by
    refine Summable.of_norm_bounded ?_ hFb
    have := (hs.mul_of_nonneg hc (fun _ => norm_nonneg _) (fun n => by positivity)).mul_left 2
    simpa only [mul_assoc] using this
  have hA := hFs.hasSum
  have h1 := hA.prod_fiberwise hf
  have hn (n : ℕ) := (Complex.hasSum_re
    ((summable_pow_sub_one hz hs n).hasSum.mul_left (c n))).mul_left 2
  have hA' :=
    (Equiv.prodComm ℕ (EigIdx U)).hasSum_iff.mpr hA
  exact ⟨h1.summable, h1.tsum_eq ▸ hA'.prod_fiberwise hn⟩


end General

/-- Summing the absolutely convergent self-adjoint Fourier series in operator norm
reduces to evaluating it at the eigenvalues and the fixed space. -/
private lemma hasSum_hermitian_pow {U : Ell2 →L[ℂ] Ell2}
    (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) (hC : IsCompactOperator ⇑(U - 1))
    (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h1 : HasSum (fun n : ℕ => 2 * (a n).re) 1)
    (hz : ∀ p : EigIdx U, HasSum (fun n : ℕ => 2 * (a n * (p.1 : ℂ) ^ n).re) 1) :
    HasSum (fun n => a n • U ^ n + star (a n • U ^ n)) 1 := by
  let V (n : ℕ) := a n • U ^ n + star (a n • U ^ n)
  have hs : Summable V := (ha.mul_left 2).of_norm_bounded fun n => by
    refine (norm_add_le _ _).trans ?_
    simp only [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map, norm_smul, two_mul]
    exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_unitary (pow_mem hU n)))
      (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_unitary (pow_mem hU n)))
  let L := ∑' n, V n
  suffices L = 1 by simpa only [← this] using hs.hasSum
  have eval {z : ℂ} {x : Ell2} (h : U x = z • x) (hn : ‖z‖ = 1)
      (hz : HasSum (fun n : ℕ => 2 * (a n * z ^ n).re) 1) : L x = x := by
    have heq n : V n x = ((2 * (a n * z ^ n).re : ℝ) : ℂ) • x := by
      change (a n • U ^ n + star (a n • U ^ n)) x = _
      rw [star_smul, star_pow, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        clm_pow_apply_of_eigen h, clm_pow_apply_of_eigen (star_apply_of_eigen hU hn h), smul_smul, smul_smul, ← add_smul]
      congr 1
      change a n * z ^ n + conj (a n) * conj z ^ n = _
      rw [← map_pow, ← map_mul, Complex.add_conj]
    have ht := (hz.mapL Complex.ofRealCLM).mapL (ContinuousLinearMap.toSpanSingleton ℂ x)
    have hsx := hs.hasSum.mapL (ContinuousLinearMap.apply ℂ Ell2 x)
    exact (by simpa [heq] using hsx : HasSum _ (L x)).unique (by simpa using ht : HasSum _ x)
  apply eq_of_eigVec_and_fixed hU hC
  · exact fun p => eval (eigVec_eigen U p) (norm_eigVal hU p) (hz p)
  · intro x hx
    exact eval (z := 1) (by simpa using hx) norm_one (by simpa using h1)


section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E))
include γ K hK Ws hWs

set_option maxSynthPendingDepth 4 in
/-- The derivative series is the trace pairing with the identity, since the
self-adjoint Fourier series of the slope is the identity on the spectrum. -/
theorem hasSum_re_tauE (E : ℝ)
    (hC : IsCompactOperator ⇑(monodromy (Ws E) - 1)) (c : ℕ → ℂ)
    (hc : Summable (fun n : ℕ => n * ‖c n‖))
    (h1 : HasSum (fun n : ℕ => 2 * (Complex.I * n * c n).re) 1)
    (hz : ∀ p : EigIdx (monodromy (Ws E)),
      HasSum (fun n : ℕ => 2 * (Complex.I * n * c n * (p.1 : ℂ) ^ n).re) 1) :
    HasSum (fun n : ℕ => 2 * (c n * tauE γ Ws n E).re)
      ((1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ) := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  let W := Ws E
  let U := monodromy W
  let b := areaDensity γ
  let a (n : ℕ) := Complex.I * n * c n
  have ha : Summable fun n => ‖a n‖ := by
    simpa only [a, norm_mul, Complex.norm_I, Complex.norm_natCast, one_mul] using hc
  have hu θ := transport_mem_unitary hK (hWs E) (θ := θ)
  have hb := areaDensity_aestronglyMeasurable hK.continuous
  have hB θ := abs_areaDensity_le hK hR (θ := θ)
  let L := traceForm W b
  let T := Complex.reCLM.comp (L.restrictScalars ℝ)
  have htrace (X : Ell2 →L[ℂ] Ell2) : T X = ∫ θ in (0 : ℝ)..(2 * π),
      ((b θ : ℂ) * diagPair W θ X).re := by
    change (L X).re = _
    rw [traceForm_apply (hWs E).1 hb hB]
    exact (Complex.reCLM.intervalIntegral_comp_comm
      (intervalIntegrable_ofReal_mul hb hB ((continuousOn_diagPair (hWs E).1).clm_apply continuousOn_const))).symm
  have hstar (X : Ell2 →L[ℂ] Ell2) : T (star X) = T X := by
    rw [htrace, htrace]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hquad (v : Ell2) : (inner ℂ v (star X v)).re = (inner ℂ v (X v)).re := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right X]
      exact inner_re_symm (𝕜 := ℂ) (X v) v
    simp  [diagPair_apply, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, hquad]
  have hid : T 1 = ∫ θ in (0 : ℝ)..(2 * π), b θ := by
    rw [htrace]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    have hvec (j : ℕ) : ‖star (W θ) (basisVec j)‖ = 1 := norm_adjoint_unitary_basisVec (hu θ hθ) j
    norm_num [diagPair_apply, inner_self_eq_norm_sq_to_K, hvec, Complex.mul_re]
  have h := ((hasSum_hermitian_pow (monodromy_mem_unitary' hK (hWs E)) hC a ha h1 hz).mapL T).mul_left (1/4)
  rw [hid] at h
  convert h using 1
  funext n
  rw [map_add T, hstar]
  change 2 * (c n * tauE γ Ws n E).re = (1/4) * ((L (a n • U ^ n)).re + (L (a n • U ^ n)).re)
  rw [map_smul, smul_eq_mul]
  unfold tauE
  rw [show c n * (Complex.I * n * ((1 / 4 : ℂ) * traceForm (Ws E) (areaDensity γ)
      (monodromy (Ws E) ^ n))) = ((1 / 4 : ℝ) : ℂ) * (a n * traceForm W b (U ^ n)) by
    simp only [a, U, b]; push_cast; ring, Complex.re_ofReal_mul]
  ring

/-- The norm of the trace of the power derivative grows at most linearly. -/
lemma norm_tauE_le {R : ℝ} (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) (E : ℝ) (n : ℕ) :
    ‖tauE γ Ws n E‖ ≤ n * (1 / 4 * ((R * K * 3) * (2 * π))) :=
  le_of_tendsto' (hasSum_trace_deriv_monodromy_pow hK hWs E n (default : HilbertBasis ℕ ℂ Ell2)).tendsto_sum_nat.norm
    (norm_sum_trace_range (traceBound_powerCurvature (traceBound_curvatureOp hK hR (hWs E))
      (monodromy_mem_unitary' hK (hWs E)) n) _)


end

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
include γ K hK hclosed

/-- A uniform cut neighbourhood: if `e^{iε}` avoids the spectrum of `U_E` for `E ∈ [E₁, E₂]`,
then all eigenvalues of these `U_E` stay at distance `≥ r` from `e^{iε}`, for some `r > 0` with
also `r ≤ |1 - e^{iε}|`. -/
lemma exists_cut_radius  {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) {E₁ E₂ : ℝ}
    (h1 : 0 < E₁)
    (hcut : ∀ E ∈ Icc E₁ E₂, Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    ∃ r, 0 < r ∧ r ≤ ‖1 - Complex.exp (ε * Complex.I)‖ ∧
      ∀ E ∈ Icc E₁ E₂, ∀ z ∈ spectrum ℂ (monodromyAt γ E),
        r ≤ ‖z - Complex.exp (ε * Complex.I)‖ := by
  set w := Complex.exp (ε * Complex.I) with hw
  set G : ℝ × ℂ → Ell2 →L[ℂ] Ell2 := fun q => algebraMap ℂ _ q.2 - monodromyAt γ q.1 with hG
  have hGc : ContinuousOn G (Ioi 0 ×ˢ univ) := by
    intro q hq
    have hq1 := hq.1
    refine ContinuousAt.continuousWithinAt ?_
    exact ((continuous_algebraMap ℂ (Ell2 →L[ℂ] Ell2)).continuousAt.comp continuousAt_snd).sub
      ((continuousAt_monodromyAt hK hclosed hq1).comp continuousAt_fst)
  have hO := hGc.isOpen_inter_preimage (isOpen_Ioi.prod isOpen_univ) Units.isOpen
  have hKc : IsCompact (Icc E₁ E₂ ×ˢ ({w} : Set ℂ)) := isCompact_Icc.prod isCompact_singleton
  have hKO : Icc E₁ E₂ ×ˢ ({w} : Set ℂ) ⊆ (Ioi 0 ×ˢ univ) ∩ G ⁻¹' {x | IsUnit x} := by
    rintro ⟨E, z⟩ ⟨hE, hz⟩
    rw [mem_singleton_iff] at hz
    subst hz
    refine ⟨⟨h1.trans_le hE.1, mem_univ _⟩, ?_⟩
    exact spectrum.notMem_iff.mp (hcut E hE)
  obtain ⟨δ, hδ, hδO⟩ := hKc.exists_thickening_subset_open hO hKO
  have hw1 := norm_sub_pos_iff.mpr (exp_mul_I_ne_one hε0 hε).symm
  refine ⟨min δ ‖1 - w‖, lt_min hδ hw1, min_le_right _ _, fun E hE z hz => ?_⟩
  refine (min_le_left _ _).trans ?_
  by_contra hlt
  push_neg at hlt
  have hmem : (E, z) ∈ Metric.thickening δ (Icc E₁ E₂ ×ˢ ({w} : Set ℂ)) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(E, w), ⟨hE, mem_singleton _⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, dist_eq_norm]
    simpa using hlt
  exact (spectrum.notMem_iff.mpr (hδO hmem).2) hz

/-- The eigenvalues `z ≠ 1` of the monodromy, listed with multiplicity, satisfy
`∑ |z_p - 1| < ∞`. -/
lemma summable_norm_eigIdx_sub_one  {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) :
    Summable (fun p : EigIdx (monodromy W) => ‖(p.1 : ℂ) - 1‖) := by
  exact summable_norm_eigIdx (summable_eigenMult_monodromy hK hclosed hE hW)

/-- **Per-energy Fourier expansion of the cut phase sum.** If the eigenvalues of `U_E` avoid the
`r`-neighbourhood of `e^{iε}` on which the Fourier series of `argCut ε` converges, then the cut phase
sum is `∑ₙ 2 Re(cₙ tr(U_E^n - I))`, with `tr(U_E^n - I) = ∑_p (z_p^n - 1)` the diagonal sum of
`U_E^n - I` in any Hilbert basis. -/
lemma cutPhaseSum_fourier  {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) {ε : ℝ} (c : ℕ → ℂ) (hc : Summable (fun n : ℕ => n * ‖c n‖))
    (hf : ∀ p : EigIdx (monodromy W),
      HasSum (fun n : ℕ => 2 * (c n * ((p.1 : ℂ) ^ n - 1)).re) (argCut ε p.1))
    (e : HilbertBasis ℕ ℂ Ell2) :
    (∀ n : ℕ, HasSum (fun m => inner ℂ (e m) ((monodromy W ^ n - 1) (e m)))
      (∑' p : EigIdx (monodromy W), ((p.1 : ℂ) ^ n - 1))) ∧
    HasSum (fun n : ℕ => 2 * (c n * ∑' p : EigIdx (monodromy W), ((p.1 : ℂ) ^ n - 1)).re)
      (cutPhaseSum ε (monodromy W)) := by
  have hU := monodromy_mem_unitary' hK hW
  have hC := isCompactOperator_monodromy_sub_one hK hclosed hE hW
  have hs := summable_norm_eigIdx_sub_one hK hclosed hE hW
  have hz := norm_eigVal hU
  refine ⟨fun n => hasSum_trace_pow_sub_one hU hC e n ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => norm_pow_sub_one_le (hz p) n) (hs.mul_left (n : ℝ))
  · obtain ⟨hfs, hsum⟩ := hasSum_fourier_eigen c hc hs hz _ hf
    rwa [cutPhaseSum_eq_tsum_eigIdx hfs]

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit γ K hK hclosed in
/-- A cut outside the spectrum gives an absolutely summable cut phase. -/
lemma summable_cutPhaseTerm {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hs : Summable (fun p : EigIdx U => ‖(p.1 : ℂ) - 1‖)) {ε : ℝ}
    (hε : 0 < ε) (h2ε : ε < 2 * π) (hcut : Complex.exp (ε * Complex.I) ∉ spectrum ℂ U) :
    Summable (cutPhaseTerm ε U) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (spectrum.isClosed (𝕜 := ℂ) U).isOpen_compl _ hcut
  obtain ⟨c, hc, hf⟩ := exists_cutFourier hε h2ε hr
  have h := (hasSum_fourier_eigen c hc hs (norm_eigVal hU) (fun p => argCut ε p.1) fun p =>
    (hf _ (norm_eigVal hU p) (le_of_not_gt fun hlt => hball (Metric.mem_ball.2
      (by rwa [dist_eq_norm])) (eigVal_mem_spectrum hU p))).1).1
  convert h.sigma using 1
  funext z
  rw [tsum_fintype, cutPhaseTerm]
  simp  [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end

/-- **Lemma 9.3, analytic core.** For a closed Lipschitz curve, `0 < ε < 2π`, and an interval
`[E₁, E₂] ⊂ (0, ∞)` on which `e^{iε}` avoids the spectrum of `U_E`, the cut phase sum increases at
the constant rate `(1/4) ∫₀^{2π} b`. -/
theorem cutPhaseSum_monodromyAt_sub  {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    cutPhaseSum ε (monodromyAt γ E₂) - cutPhaseSum ε (monodromyAt γ E₁) =
      (E₂ - E₁) * ((1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ) := by
  obtain ⟨r, hr, hr1, hrE⟩ := exists_cut_radius hK hclosed hε0 hε h1 hcut
  obtain ⟨c, hc, hcF⟩ := exists_cutFourier hε0 hε hr
  choose Ws hWs using fun E => transport_exists_of_lipschitz γ hK E
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  set C0 : ℝ := 1 / 4 * ((R * K * 3) * (2 * π))
  set τ₀ : ℝ := (1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ
  set e : HilbertBasis ℕ ℂ Ell2 := default
  set T : ℕ → ℝ → ℂ := fun n E => ∑' p : EigIdx (monodromy (Ws E)), ((p.1 : ℂ) ^ n - 1) with hT
  -- eigenvalues of `U_E` for `E ∈ [E₁, E₂]` stay away from the cut
  have hfar (E) (hE : E ∈ Icc E₁ E₂) (p : EigIdx (monodromy (Ws E))) :
      ‖(p.1 : ℂ)‖ = 1 ∧ r ≤ ‖(p.1 : ℂ) - Complex.exp (ε * Complex.I)‖ := by
    have hU := monodromy_mem_unitary' hK (hWs E)
    refine ⟨norm_eigVal hU p, hrE E hE _ ?_⟩
    rw [monodromyAt_eq hK (hWs E)]
    exact eigVal_mem_spectrum hU p
  have hE0 : ∀ E ∈ Icc E₁ E₂, 0 ≤ E := fun E hE => (h1.trans_le hE.1).le
  have hper : ∀ E ∈ Icc E₁ E₂, (∀ n : ℕ, HasSum (fun m => inner ℂ (e m)
      ((monodromy (Ws E) ^ n - 1) (e m))) (T n E)) ∧
      HasSum (fun n : ℕ => 2 * (c n * T n E).re) (cutPhaseSum ε (monodromyAt γ E)) := by
    intro E hE
    rw [monodromyAt_eq hK (hWs E)]
    exact cutPhaseSum_fourier hK hclosed (hE0 E hE) (hWs E) c hc
      (fun p => (hcF _ (hfar E hE p).1 (hfar E hE p).2).1) e
  have hE₁ : E₁ ∈ Icc E₁ E₂ := ⟨le_rfl, h12⟩
  have hE₂ : E₂ ∈ Icc E₁ E₂ := ⟨h12, le_rfl⟩
  have hint := fun n => trace_monodromy_pow_sub hK hclosed hWs h1 h12 n e
    ((hper E₁ hE₁).1 n) ((hper E₂ hE₂).1 n)
  -- left side: difference of the two Fourier expansions
  have hL : HasSum (fun n : ℕ => ∫ E in E₁..E₂, 2 * (c n * tauE γ Ws n E).re)
      (cutPhaseSum ε (monodromyAt γ E₂) - cutPhaseSum ε (monodromyAt γ E₁)) := by
    convert (hper E₂ hE₂).2.sub (hper E₁ hE₁).2 using 1
    funext n
    rw [intervalIntegral.integral_const_mul]
    have h := Complex.reCLM.intervalIntegral_comp_comm ((hint n).1.const_mul (c n))
    simp only [Complex.reCLM_apply] at h
    rw [h, intervalIntegral.integral_const_mul, ← (hint n).2]
    rw [mul_sub, Complex.sub_re]
    ring
  -- right side: dominated convergence
  have huIoc : ∀ E ∈ uIoc E₁ E₂, E ∈ Icc E₁ E₂ := fun E hE => by
    rw [uIoc_of_le h12] at hE; exact Ioc_subset_Icc_self hE
  have hR' : HasSum (fun n : ℕ => ∫ E in E₁..E₂, 2 * (c n * tauE γ Ws n E).re)
      (∫ _ in E₁..E₂, τ₀) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => 2 * (n * ‖c n‖) * C0) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · have := ((intervalIntegrable_iff.mp ((hint n).1.const_mul (c n))).aestronglyMeasurable)
      exact (continuous_const.mul Complex.continuous_re).comp_aestronglyMeasurable this
    · refine .of_forall fun E _ => (norm_two_re_mul_le _ _).trans ?_
      calc 2 * ‖c n‖ * ‖tauE γ Ws n E‖ ≤ 2 * ‖c n‖ * (n * C0) := by
             gcongr
             exact norm_tauE_le hK hWs hR E n
        _ = _ := by ring
    · exact Eventually.of_forall fun E _ => (hc.mul_left 2).mul_right C0
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun E hE => ?_
      have hEI := huIoc E hE
      refine hasSum_re_tauE hK hWs E
        (isCompactOperator_monodromy_sub_one hK hclosed (hE0 E hEI) (hWs E)) c hc ?_
        (fun p => (hcF _ (hfar E hEI p).1 (hfar E hEI p).2).2)
      have h := (hcF 1 (by simp) hr1).2
      simpa using h
  rw [hL.unique hR', intervalIntegral.integral_const, smul_eq_mul]

end

end PolyaNeumann

end
