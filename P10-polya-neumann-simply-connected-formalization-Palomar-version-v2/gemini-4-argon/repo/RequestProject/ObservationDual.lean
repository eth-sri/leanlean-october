module

public import RequestProject.ObservationHSEnergy
public import RequestProject.HilbertSchmidt

/-!
# Lemma 6.3: the dual of the projected observation on `X = H^{-1/2}(𝕋)`

Lemma 6.3 of the paper asserts that the adjoint of the periodic projected observation
`O_E Π^c_E : ℓ² → H¹(𝕋)` extends `T_E^♯ = Π^c_E O_E^*` to a compact operator `X → ℓ²`,
`X = H^{-1/2}(𝕋)`, depending continuously on `E` in norm. In Fourier coordinates,
`X ≅ ℓ²(ℤ)` through the normalization `g ↦ (λₙ^{-1/2} ĝ(n))ₙ` with `λₙ = 1 + |n|`, so the
extension is the operator `T_E^♯ Λ^{1/2} : ℓ²(ℤ) → ℓ²` (this is also the operator `𝒮_E` of
Lemma 7.4 before composition with the fixed chart `R`).

We construct it (`projObsDual`) as the synthesis operator `f ↦ ∑ₙ fₙ ρₙ` of the vectors
`ρₙ = λₙ^{1/2} r̂(-n)`, where `r̂(k)` are the vector Fourier coefficients on `[0, L]` of the row
`r_E(θ) = Π^c_E W_E(θ)^* e₀`. Since `⟨r̂(-n), v⟩ = (O_E Π^c_E v)^(n)`, Parseval and the
Hilbert–Schmidt bounds of `ObservationHS.lean` give `∑ₙ ‖ρₙ‖² < ∞`. Hence:

* `projObsDual` is compact (`isCompactOperator_projObsDual`);
* if `c_{E₀} ≠ 0`, it is continuous in `E` at `E₀` in operator norm
  (`tendsto_projObsDual_energy`), by the continuity results of `ObservationHSEnergy.lean`;
* it extends `T_E^♯`: for every continuous `2π`-periodic `g`,
  `projObsDual (2π λ^{-1/2} ĝ) = Π^c_E O_E^* g` (`projObsDual_normalizedCoeff`);
* consequently, for any fixed bounded `R`, the reduced observation `𝒮_E = T_E^♯ Λ^{1/2} R` of
  Lemma 7.4 is compact and norm-continuous in `E` (`reducedObservation_compact_continuous`).

The generic part (`rowSynth`) is the synthesis operator of a square-summable family of vectors.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

/-! ### Synthesis operators of square-summable families -/

section RowOp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (ρ : ℤ → H) (hρ : Summable fun n => ‖ρ n‖ ^ 2)
include hρ

def rowAnalysisLin : H →ₗ[ℂ] L2Z where
  toFun v := ⟨fun n => ⟪ρ n, v⟫_ℂ, (show Memℓp (fun n => ⟪ρ n, v⟫_ℂ) 2 by
    refine memℓp_two_iff_summable.mpr ?_
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hρ.mul_right (‖v‖ ^ 2))
    rw [← mul_pow]
    gcongr
    exact norm_inner_le_norm _ _)⟩
  map_add' v w := by
    ext n
    exact inner_add_right (ρ n) v w
  map_smul' c v := by
    ext n
    exact inner_smul_right (ρ n) v c

lemma rowAnalysisLin_apply v n :
    (rowAnalysisLin ρ hρ v : ℤ → ℂ) n = ⟪ρ n, v⟫_ℂ := rfl

lemma norm_rowAnalysisLin_le v :
    ‖rowAnalysisLin ρ hρ v‖ ≤ Real.sqrt (∑' n, ‖ρ n‖ ^ 2) * ‖v‖ := by
  have hS : 0 ≤ ∑' n, ‖ρ n‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have := Real.sqrt_le_sqrt (show ‖rowAnalysisLin ρ hρ v‖ ^ 2 ≤ (∑' n, ‖ρ n‖ ^ 2) * ‖v‖ ^ 2 by
    rw [norm_sq_L2Z, ← tsum_mul_right]
    refine (summable_norm_sq_L2Z _).tsum_le_tsum (fun n => ?_) (hρ.mul_right _)
    rw [rowAnalysisLin_apply, ← mul_pow]
    gcongr
    exact norm_inner_le_norm _ _)
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg _)] at this

/-- The analysis operator `v ↦ (⟨ρₙ, v⟩)ₙ : H → ℓ²(ℤ)`. -/
def rowAnalysis : H →L[ℂ] L2Z :=
  (rowAnalysisLin ρ hρ).mkContinuous _ (norm_rowAnalysisLin_le ρ hρ)

lemma rowAnalysis_apply v n :
    (rowAnalysis ρ hρ v : ℤ → ℂ) n = ⟪ρ n, v⟫_ℂ := rfl

variable [CompleteSpace H]

/-- The synthesis operator `f ↦ ∑ₙ fₙ ρₙ : ℓ²(ℤ) → H`, the adjoint of the analysis operator. -/
def rowSynth : L2Z →L[ℂ] H := ContinuousLinearMap.adjoint (rowAnalysis ρ hρ)

/-- `⟨v, ∑ₙ fₙ ρₙ⟩ = ∑ₙ ⟨v, ρₙ⟩ fₙ`. -/
lemma inner_rowSynth v f :
    ⟪v, rowSynth ρ hρ f⟫_ℂ = ∑' n, ⟪v, ρ n⟫_ℂ * f n := by
  rw [rowSynth, ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [rowAnalysis_apply, ← inner_conj_symm v (ρ n)]
  simp [mul_comm]

/-- The synthesis operator sends the `n`-th standard basis vector to `ρₙ`. -/
lemma rowSynth_stdBasisZ n : rowSynth ρ hρ (stdBasisZ n) = ρ n := by
  refine ext_inner_left ℂ fun v => ?_
  rw [inner_rowSynth, stdBasisZ_apply, tsum_eq_single n]
  · simp
  · intro k hk
    simp [hk]

/-- `‖∑ₙ fₙ ρₙ - ∑ₙ fₙ σₙ‖ ≤ (∑ₙ ‖ρₙ - σₙ‖²)^{1/2} ‖f‖`. -/
theorem norm_rowSynth_sub_le σ hσ :
    ‖rowSynth ρ hρ - rowSynth σ hσ‖ ≤ Real.sqrt (∑' n, ‖ρ n - σ n‖ ^ 2) := by
  have hcol : ∀ n, (rowSynth ρ hρ - rowSynth σ hσ) (stdBasisZ n) = ρ n - σ n := by
    intro n
    rw [ContinuousLinearMap.sub_apply, rowSynth_stdBasisZ, rowSynth_stdBasisZ]
  simpa [hcol] using (norm_le_sqrt_tsum_norm_sq stdBasisZ (rowSynth ρ hρ - rowSynth σ hσ) (by simpa [hcol] using (show Summable fun n => ‖ρ n - σ n‖ ^ 2 by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hρ.add hσ).mul_left 2)
    have h1 := norm_sub_le (ρ n) (σ n)
    have h2 : 0 ≤ ‖ρ n - σ n‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖ρ n‖ - ‖σ n‖)])))

end RowOp

/-! ### Weighted Parseval bounds -/

section WeightedParseval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} (b : HilbertBasis ι ℂ H) (R : ℤ → H)

/-- If the coefficients `cⱼ(n) = ⟨Rₙ, bⱼ⟩` satisfy `∑ⱼ ∑ₙ (n² + 1) |cⱼ(n)|² < ∞`, then
`∑ₙ (1 + |n|) ‖Rₙ‖² ≤ ∑ⱼ ∑ₙ n² |cⱼ(n)|² + 2 ∑ⱼ ∑ₙ |cⱼ(n)|²`. -/
theorem summable_weight_norm_sq_of_basis
    (h1 : Summable fun p : ι × ℤ => ((p.2 : ℝ)) ^ 2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2)
    (h2 : Summable fun p : ι × ℤ => ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖R n‖ ^ 2) ∧
      ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖R n‖ ^ 2 ≤
        ∑' p : ι × ℤ, ((p.2 : ℝ)) ^ 2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 +
          2 * ∑' p : ι × ℤ, ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 := by
  set g : ι × ℤ → ℝ := fun p => (1 + |(p.2 : ℝ)|) * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 with hg
  have hle : ∀ p : ι × ℤ, g p ≤ (p.2 : ℝ) ^ 2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 +
      2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 := by
    intro p
    have := mul_le_mul_of_nonneg_right (show 1 + |(p.2 : ℝ)| ≤ (p.2 : ℝ) ^ 2 + 2 by
      nlinarith [sq_abs (p.2 : ℝ), sq_nonneg (|(p.2 : ℝ)| - 1)]) (sq_nonneg ‖⟪R p.2, b p.1⟫_ℂ‖)
    simp only [hg]
    linarith
  have hf := h1.add (h2.mul_left 2)
  have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; positivity
  have hgs := Summable.of_nonneg_of_le hg0 hle hf
  have hgs' : Summable fun q : ℤ × ι => g q.swap :=
    (Equiv.prodComm ℤ ι).summable_iff.mpr hgs
  have hrow : ∀ n : ℤ, HasSum (fun j => g (n, j).swap) ((1 + |(n : ℝ)|) * ‖R n‖ ^ 2) := by
    intro n
    refine ((show HasSum (fun i => ‖⟪b i, (R n)⟫_ℂ‖ ^ 2) (‖(R n)‖ ^ 2) by
      have h := Complex.hasSum_re (b.hasSum_inner_mul_inner (R n) (R n))
      rw [inner_self_eq_norm_sq_to_K] at h
      convert h using 1
      · funext i
        rw [← inner_conj_symm (b i) (R n), RCLike.norm_conj, Complex.mul_conj, Complex.ofReal_re,
          Complex.normSq_eq_norm_sq]
      · simp [← Complex.ofReal_pow]).mul_left (1 + |(n : ℝ)|)).congr_fun fun j => ?_
    simp only [hg, Prod.swap_prod_mk]
    rw [norm_inner_symm]
  refine ⟨(hgs'.prod.congr fun n => (hrow n).tsum_eq), ?_⟩
  rw [show ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖R n‖ ^ 2 = ∑' p, g p by
    rw [← (Equiv.prodComm ℤ ι).tsum_eq g]
    change _ = ∑' q : ℤ × ι, g q.swap
    rw [hgs'.tsum_prod]
    exact tsum_congr fun n => ((hrow n).tsum_eq).symm, ← tsum_mul_left, ← h1.tsum_add (h2.mul_left 2)]
  exact hgs.tsum_le_tsum hle hf

end WeightedParseval

/-! ### The projected observation in Fourier coordinates -/

/-- Fourier coefficients on `[0, 2π]` only depend on the values on `[0, 2π]`. -/
lemma fourierCoeffOn_congr_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : ℝ → F} (h : EqOn f g (Icc 0 (2 * π))) n :
    fourierCoeffOn two_pi_pos f n = fourierCoeffOn two_pi_pos g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le two_pi_pos.le] at hθ
  simp [h hθ]

/-- Fourier coefficients on `[0, 2π]` are additive for functions continuous on `[0, 2π]`. -/
lemma fourierCoeffOn_sub_of_continuousOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f g : ℝ → F} (hf : ContinuousOn f (Icc 0 (2 * π)))
    (hg : ContinuousOn g (Icc 0 (2 * π))) n :
    fourierCoeffOn two_pi_pos (fun θ => f θ - g θ) n =
      fourierCoeffOn two_pi_pos f n - fourierCoeffOn two_pi_pos g n := by
  have hc : ContinuousOn (fun x : ℝ => fourier (-n) (x : AddCircle (2 * π - 0)))
      (uIcc 0 (2 * π)) :=
    ((map_continuous (fourier (-n))).comp continuous_quotient_mk').continuousOn
  rw [uIcc_of_le two_pi_pos.le] at hc
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    ← smul_sub, ← intervalIntegral.integral_sub]
  · simp_rw [smul_sub]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le two_pi_pos.le]
    exact hc.smul hf
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le two_pi_pos.le]
    exact hc.smul hg

/-- Pairing a vector Fourier coefficient with a vector: `⟨r̂(-n), v⟩ = (⟨r(·), v⟩)^(n)`. -/
lemma inner_fourierCoeffOn_neg {r : ℝ → Ell2} (hr : ContinuousOn r (Icc 0 (2 * π))) v
    n :
    ⟪fourierCoeffOn two_pi_pos r (-n), v⟫_ℂ =
      fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v⟫_ℂ) n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, neg_neg,
    RCLike.real_smul_eq_coe_smul (K := ℂ), ← Complex.coe_smul, inner_smul_left]
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ v) (show IntervalIntegrable (fun x => fourier n (x : AddCircle (2 * π - 0)) • r x) volume 0 (2 * π) by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le two_pi_pos.le]
    exact ((map_continuous (fourier n)).comp continuous_quotient_mk').continuousOn.smul hr)
  simp only [innerSL_apply_apply] at h
  rw [← inner_conj_symm]
  erw [← h]
  rw [intervalIntegral.integral_of_le two_pi_pos.le,
    intervalIntegral.integral_of_le two_pi_pos.le, ← integral_conj]
  simp only [inner_smul_right, map_mul, inner_conj_symm, ← fourier_neg]
  simp [smul_eq_mul]
  exact Or.inl (map_ofNat (starRingEnd ℂ) 2)

section Concrete

variable {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- The standard Hilbert basis of `ℓ²(ℕ₀)`. -/
def stdBasisN : HilbertBasis ℕ ℂ Ell2 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Ell2)

local notation "Φ0" => IsTransport γ E W

lemma periodize_projObsRow_eqOn (hW : Φ0) :
    EqOn (periodize (projObsRow W)) (projObsRow W) (Icc 0 (2 * π)) :=
  fun _ hθ => periodize_eqOn_Icc (projObsRow_endpoint hW) hθ

local notation "Φ1" => LipschitzWith K γ

lemma lipschitzWith_periodize_projObsRow (hK : Φ1) (hW : Φ0) :
    LipschitzWith ⟨Real.sqrt E * shiftConst * K, by have := shiftConst_nonneg; positivity⟩
      (periodize (projObsRow W)) :=
  lipschitzWith_periodize (fun _ hx _ hy => norm_projObsRow_sub_le hK hW hx hy)
    (projObsRow_endpoint hW)

lemma continuousOn_projObsRow (hK : Φ1) (hW : Φ0) :
    ContinuousOn (projObsRow W) (Icc 0 (2 * π)) :=
  (lipschitzWith_periodize_projObsRow hK hW).continuous.continuousOn.congr
    (periodize_projObsRow_eqOn hW).symm

lemma norm_projObsRow_le (hK : Φ1) (hW : Φ0) 
    (hθ : θ ∈ Icc 0 (2 * π)) : ‖projObsRow W θ‖ ≤ 1 := by
  unfold projObsRow
  refine (norm_cutProj_apply_le _ _).trans ?_
  refine ((ContinuousLinearMap.adjoint (W θ)).le_opNorm _).trans ?_
  rw [LinearIsometryEquiv.norm_map, show ‖basisVec 0‖ = 1 by simp [basisVec], mul_one]
  exact norm_transport_le_one hK hW hθ

/-- The vector Fourier coefficient `r̂_E(-n)` of the projected observation row
`r_E(θ) = Π^c_E W_E(θ)^* e₀`; it represents the `n`-th Fourier coefficient of `O_E Π^c_E`. -/
def projObsCoeffVec (W : ℝ → Ell2 →L[ℂ] Ell2) (n : ℤ) : Ell2 :=
  fourierCoeffOn two_pi_pos (projObsRow W) (-n)

/-- `⟨r̂_E(-n), v⟩ = (O_E Π^c_E v)^(n)`. -/
lemma inner_projObsCoeffVec (hK : Φ1) (hW : Φ0) (v : Ell2)
    (n : ℤ) :
    ⟪projObsCoeffVec W n, v⟫_ℂ = fourierCoeffOn two_pi_pos
      (fun θ => observation W (cutProj (cutC (W (2 * π)) (basisVec 0)) v) θ) n := by
  rw [projObsCoeffVec, inner_fourierCoeffOn_neg (continuousOn_projObsRow hK hW)]
  simp [observation_cutProj_eq]

lemma inner_projObsCoeffVec_periodize (hK : Φ1) (hW : Φ0)
    (v : Ell2) n :
    ⟪projObsCoeffVec W n, v⟫_ℂ =
      fourierCoeffOn two_pi_pos (fun θ => ⟪periodize (projObsRow W) θ, v⟫_ℂ) n := by
  rw [projObsCoeffVec, inner_fourierCoeffOn_neg (continuousOn_projObsRow hK hW)]
  exact fourierCoeffOn_congr_Icc (fun θ hθ => by
    simp [periodize_projObsRow_eqOn hW hθ]) n

/-- The normalized rows `ρₙ = λₙ^{1/2} r̂_E(-n)`, `λₙ = 1 + |n|`. -/
def normProjObsRow (W : ℝ → Ell2 →L[ℂ] Ell2) (n : ℤ) : Ell2 :=
  (Real.sqrt (1 + |(n : ℝ)|) : ℂ) • projObsCoeffVec W n

lemma norm_normProjObsRow_sq W n :
    ‖normProjObsRow W n‖ ^ 2 = (1 + |(n : ℝ)|) * ‖projObsCoeffVec W n‖ ^ 2 := by
  rw [normProjObsRow, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

/-- The coefficients `⟨r̂_E(-n), eⱼ⟩` satisfy the `H¹` and `L²` Hilbert–Schmidt bounds. -/
lemma summable_inner_projObsCoeffVec (hK : Φ1) (hW : Φ0) :
    (Summable fun p : ℕ × ℤ =>
      ((p.2 : ℝ)) ^ 2 * ‖⟪projObsCoeffVec W p.2, stdBasisN p.1⟫_ℂ‖ ^ 2) ∧
    (Summable fun p : ℕ × ℤ => ‖⟪projObsCoeffVec W p.2, stdBasisN p.1⟫_ℂ‖ ^ 2) := by
  constructor
  · simp_rw [inner_projObsCoeffVec hK hW]
    exact projected_observation_hilbertSchmidt hK hW stdBasisN.orthonormal
  · simp_rw [inner_projObsCoeffVec_periodize hK hW]
    refine (tsum_sq_fourierCoeff_rows_le stdBasisN.orthonormal
      (lipschitzWith_periodize_projObsRow hK hW).continuous (B := 1) fun θ hθ => ?_).1
    rw [periodize_projObsRow_eqOn hW hθ]
    exact norm_projObsRow_le hK hW hθ

/-- The normalized rows are square summable: `O_E Π^c_E : ℓ² → H^{1/2}(𝕋)` is Hilbert–Schmidt. -/
theorem summable_normProjObsRow (hK : Φ1) (hW : Φ0) :
    Summable fun n => ‖normProjObsRow W n‖ ^ 2 := by
  simp_rw [norm_normProjObsRow_sq]
  exact (summable_weight_norm_sq_of_basis stdBasisN (projObsCoeffVec W)
    (summable_inner_projObsCoeffVec hK hW).1 (summable_inner_projObsCoeffVec hK hW).2).1

open Classical in
/-- **The dual of the projected observation** `T_E^♯ Λ^{1/2} : ℓ²(ℤ) → ℓ²(ℕ₀)`, i.e. the
extension of `T_E^♯ = Π^c_E O_E^*` to `X = H^{-1/2}(𝕋)` read in normalized Fourier coordinates:
`f ↦ ∑ₙ fₙ λₙ^{1/2} r̂_E(-n)`. (It is set to `0` if the rows are not square summable, which
does not happen for transports of Lipschitz curves.) -/
def projObsDual (W : ℝ → Ell2 →L[ℂ] Ell2) : L2Z →L[ℂ] Ell2 :=
  if h : Summable fun n => ‖normProjObsRow W n‖ ^ 2 then rowSynth (normProjObsRow W) h else 0

lemma projObsDual_eq (hK : Φ1) (hW : Φ0) :
    projObsDual W = rowSynth (normProjObsRow W) (summable_normProjObsRow hK hW) := by
  rw [projObsDual, dif_pos (summable_normProjObsRow hK hW)]

end Concrete

/-! ### Continuity in the energy -/

/-- Weighted square summability is preserved by differences. -/
lemma summable_mul_norm_sub_sq {α : Type*} {w : α → ℝ} (hw : ∀ p, 0 ≤ w p) {a b : α → ℂ}
    (ha : Summable fun p => w p * ‖a p‖ ^ 2) (hb : Summable fun p => w p * ‖b p‖ ^ 2) :
    Summable fun p => w p * ‖a p - b p‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hw p) (sq_nonneg _)) (fun p => ?_)
    ((ha.add hb).mul_left 2)
  have h1 := norm_sub_le (a p) (b p)
  have h2 : ‖a p - b p‖ ^ 2 ≤ 2 * ‖a p‖ ^ 2 + 2 * ‖b p‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a p‖ - ‖b p‖), norm_nonneg (a p - b p)]
  nlinarith [hw p]

section Energy

variable {γ : ℝ → ℂ} {K : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

theorem tendsto_projObsDual_energy (hK : LipschitzWith K γ)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    Tendsto (fun E => projObsDual (Ws E)) (𝓝 E₀) (𝓝 (projObsDual (Ws E₀))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := ((tendsto_projected_observation_H1_energy hK hWs E₀ hc stdBasisN.orthonormal).add ((tendsto_projected_observation_L2_energy hK hWs E₀ hc stdBasisN.orthonormal).const_mul 2)).sqrt
  rw [mul_zero, add_zero, Real.sqrt_zero] at hlim
  refine squeeze_zero (fun E => norm_nonneg _) (fun E => ?_) hlim
  rw [projObsDual_eq hK (hWs E), projObsDual_eq hK (hWs E₀)]
  refine (norm_rowSynth_sub_le _ _ _ _).trans (Real.sqrt_le_sqrt ?_)
  simp_rw [show ∀ n : ℤ, ‖normProjObsRow (Ws E) n - normProjObsRow (Ws E₀) n‖ ^ 2 = (1 + |(n : ℝ)|) * ‖projObsCoeffVec (Ws E) n - projObsCoeffVec (Ws E₀) n‖ ^ 2 by
    intro n
    rw [normProjObsRow, normProjObsRow, ← smul_sub, norm_smul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]]
  have h1 := summable_mul_norm_sub_sq (fun p : ℕ × ℤ => sq_nonneg (p.2 : ℝ))
    (summable_inner_projObsCoeffVec hK (hWs E)).1 (summable_inner_projObsCoeffVec hK (hWs E₀)).1
  have h2 := summable_mul_norm_sub_sq (w := fun _ : ℕ × ℤ => 1) (fun _ => zero_le_one)
    (by simpa using (summable_inner_projObsCoeffVec hK (hWs E)).2)
    (by simpa using (summable_inner_projObsCoeffVec hK (hWs E₀)).2)
  simp [← inner_sub_left] at h1 h2
  have key := (summable_weight_norm_sq_of_basis stdBasisN
    (fun n => projObsCoeffVec (Ws E) n - projObsCoeffVec (Ws E₀) n) h1 h2).2
  have h_inl E₀ E v n : ⟪projObsCoeffVec (Ws E) n - projObsCoeffVec (Ws E₀) n, v⟫_ℂ = fourierCoeffOn two_pi_pos (fun θ => observation (Ws E) (cutProj (cutC (Ws E (2 * π)) (basisVec 0)) v) θ - observation (Ws E₀) (cutProj (cutC (Ws E₀ (2 * π)) (basisVec 0)) v) θ) n := by
    have hcont : ∀ E', ContinuousOn
        (fun θ => observation (Ws E') (cutProj (cutC (Ws E' (2 * π)) (basisVec 0)) v) θ)
        (Icc 0 (2 * π)) := by
      intro E'
      simp [observation_cutProj_eq]
      exact (continuousOn_projObsRow hK (hWs E')).inner continuousOn_const
    rw [inner_sub_left, inner_projObsCoeffVec hK (hWs E), inner_projObsCoeffVec hK (hWs E₀),
      fourierCoeffOn_sub_of_continuousOn (hcont E) (hcont E₀)]
  simp [h_inl] at key
  exact key

end Energy

/-! ### Parseval's identity in inner-product form -/


/-! ### The reduced observation of Lemma 7.4 -/


end PolyaNeumann
