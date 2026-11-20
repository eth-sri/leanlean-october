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

/-- Parseval in a Hilbert basis: `∑ᵢ |⟨bᵢ, v⟩|² = ‖v‖²`. -/
lemma hasSum_norm_inner_sq_hilbertBasis {ι : Type*} (b : HilbertBasis ι ℂ H) (v : H) :
    HasSum (fun i => ‖⟪b i, v⟫_ℂ‖ ^ 2) (‖v‖ ^ 2) := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner v v)
  rw [inner_self_eq_norm_sq_to_K] at h
  convert h using 1
  · funext i
    rw [← inner_conj_symm (b i) v, RCLike.norm_conj, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  norm_cast

variable (ρ : ℤ → H) (hρ : Summable fun n => ‖ρ n‖ ^ 2)
include hρ

lemma memℓp_rowAnalysis (v : H) : Memℓp (fun n => ⟪ρ n, v⟫_ℂ) 2 := by
  refine memℓp_two_iff_summable.mpr ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hρ.mul_right (‖v‖ ^ 2))
  rw [← mul_pow]
  gcongr
  exact norm_inner_le_norm _ _

/-- The analysis map `v ↦ (⟨ρₙ, v⟩)ₙ` as a linear map. -/
def rowAnalysisLin : H →ₗ[ℂ] L2Z where
  toFun v := ⟨fun n => ⟪ρ n, v⟫_ℂ, memℓp_rowAnalysis ρ hρ v⟩
  map_add' v w := by
    ext n
    exact inner_add_right (ρ n) v w
  map_smul' c v := by
    ext n
    exact inner_smul_right (ρ n) v c


lemma norm_rowAnalysisLin_le (v : H) :
    ‖rowAnalysisLin ρ hρ v‖ ≤ Real.sqrt (∑' n, ‖ρ n‖ ^ 2) * ‖v‖ := by
  have hS : 0 ≤ ∑' n, ‖ρ n‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have h2 : ‖rowAnalysisLin ρ hρ v‖ ^ 2 ≤ (∑' n, ‖ρ n‖ ^ 2) * ‖v‖ ^ 2 := by
    rw [norm_sq_L2Z, ← tsum_mul_right]
    refine (summable_norm_sq_L2Z _).tsum_le_tsum (fun n => ?_) (hρ.mul_right _)
    rw [← mul_pow]
    gcongr
    exact norm_inner_le_norm _ _
  have := Real.sqrt_le_sqrt h2
  simp_all

/-- The analysis operator `v ↦ (⟨ρₙ, v⟩)ₙ : H → ℓ²(ℤ)`. -/
def rowAnalysis : H →L[ℂ] L2Z :=
  (rowAnalysisLin ρ hρ).mkContinuous _ (norm_rowAnalysisLin_le ρ hρ)

lemma rowAnalysis_apply (v : H) (n : ℤ) :
    (rowAnalysis ρ hρ v : ℤ → ℂ) n = ⟪ρ n, v⟫_ℂ := rfl

variable [CompleteSpace H]

/-- The synthesis operator `f ↦ ∑ₙ fₙ ρₙ : ℓ²(ℤ) → H`, the adjoint of the analysis operator. -/
def rowSynth : L2Z →L[ℂ] H := ContinuousLinearMap.adjoint (rowAnalysis ρ hρ)

/-- `⟨v, ∑ₙ fₙ ρₙ⟩ = ∑ₙ ⟨v, ρₙ⟩ fₙ`. -/
lemma inner_rowSynth (v : H) (f : L2Z) :
    ⟪v, rowSynth ρ hρ f⟫_ℂ = ∑' n, ⟪v, ρ n⟫_ℂ * f n := by
  rw [rowSynth, ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [rowAnalysis_apply, ← inner_conj_symm v (ρ n)]
  simp [mul_comm]

/-- The synthesis operator sends the `n`-th standard basis vector to `ρₙ`. -/
lemma rowSynth_stdBasisZ (n : ℤ) : rowSynth ρ hρ (stdBasisZ n) = ρ n := by
  refine ext_inner_left ℂ fun v => ?_
  rw [inner_rowSynth, stdBasisZ_apply, tsum_eq_single n]
  all_goals simp_all

/-- `‖∑ₙ fₙ ρₙ - ∑ₙ fₙ σₙ‖ ≤ (∑ₙ ‖ρₙ - σₙ‖²)^{1/2} ‖f‖`. -/
theorem norm_rowSynth_sub_le (σ : ℤ → H) (hσ : Summable fun n => ‖σ n‖ ^ 2) :
    ‖rowSynth ρ hρ - rowSynth σ hσ‖ ≤ Real.sqrt (∑' n, ‖ρ n - σ n‖ ^ 2) := by
  have hcol : ∀ n, (rowSynth ρ hρ - rowSynth σ hσ) (stdBasisZ n) = ρ n - σ n := by
    simp [rowSynth_stdBasisZ]
  have hs : Summable fun n => ‖ρ n - σ n‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hρ.add hσ).mul_left 2)
    have h1 := norm_sub_le (ρ n) (σ n)
    have h2 : 0 ≤ ‖ρ n - σ n‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖ρ n‖ - ‖σ n‖)]
  have := norm_le_sqrt_tsum_norm_sq stdBasisZ (rowSynth ρ hρ - rowSynth σ hσ)
    (by simpa [hcol] using hs)
  simp_all

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
  have hle : ∀ p : ι × ℤ, g p ≤ ((p.2 : ℝ)) ^ 2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 +
      2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 := by
    intro p
    have hw : 1 + |(p.2 : ℝ)| ≤ (p.2 : ℝ) ^ 2 + 2 := by
      nlinarith [sq_abs (p.2 : ℝ), sq_nonneg (|(p.2 : ℝ)| - 1)]
    have := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖⟪R p.2, b p.1⟫_ℂ‖)
    simp  [hg]
    linarith
  have hf : Summable fun p : ι × ℤ => ((p.2 : ℝ)) ^ 2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 +
      2 * ‖⟪R p.2, b p.1⟫_ℂ‖ ^ 2 := h1.add (h2.mul_left 2)
  have hg0 : ∀ p, 0 ≤ g p := fun p => by positivity
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hle hf
  have hgs' : Summable fun q : ℤ × ι => g q.swap :=
    (Equiv.prodComm ℤ ι).summable_iff.mpr hgs
  have hrow : ∀ n : ℤ, HasSum (fun j => g (n, j).swap) ((1 + |(n : ℝ)|) * ‖R n‖ ^ 2) := by
    intro n
    have hp := (hasSum_norm_inner_sq_hilbertBasis b (R n)).mul_left (1 + |(n : ℝ)|)
    refine hp.congr_fun fun j => ?_
    simp only [hg, Prod.swap_prod_mk]
    rw [norm_inner_symm]
  have hsum : Summable fun n : ℤ => (1 + |(n : ℝ)|) * ‖R n‖ ^ 2 :=
    hgs'.prod.congr fun n => (hrow n).tsum_eq
  refine ⟨hsum, ?_⟩
  have htp : ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖R n‖ ^ 2 = ∑' p, g p := by
    rw [← (Equiv.prodComm ℤ ι).tsum_eq g]
    change _ = ∑' q : ℤ × ι, g q.swap
    rw [hgs'.tsum_prod]
    exact tsum_congr fun n => ((hrow n).tsum_eq).symm
  rw [htp, ← tsum_mul_left, ← h1.tsum_add (h2.mul_left 2)]
  exact hgs.tsum_le_tsum hle hf

end WeightedParseval

/-! ### The projected observation in Fourier coordinates -/

/-- Fourier coefficients on `[0, 2π]` only depend on the values on `[0, 2π]`. -/
lemma fourierCoeffOn_congr_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : ℝ → F} (h : EqOn f g (Icc 0 (2 * π))) (n : ℤ) :
    fourierCoeffOn two_pi_pos f n = fourierCoeffOn two_pi_pos g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le two_pi_pos.le] at hθ
  tauto

/-- Pairing a vector Fourier coefficient with a vector: `⟨r̂(-n), v⟩ = (⟨r(·), v⟩)^(n)`. -/
lemma inner_fourierCoeffOn_neg {r : ℝ → Ell2} (hr : ContinuousOn r (Icc 0 (2 * π))) (v : Ell2)
    (n : ℤ) :
    ⟪fourierCoeffOn two_pi_pos r (-n), v⟫_ℂ =
      fourierCoeffOn two_pi_pos (fun θ => ⟪r θ, v⟫_ℂ) n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, neg_neg]
  rw [← Complex.coe_smul, inner_smul_left]
  have hint : IntervalIntegrable
      (fun x : ℝ => fourier n (x : AddCircle (2 * π - 0)) • r x) volume 0 (2 * π) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le two_pi_pos.le]
    fun_prop
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ v) hint
  simp only [innerSL_apply_apply] at h
  rw [← inner_conj_symm]
  erw [← h]
  rw [intervalIntegral.integral_of_le two_pi_pos.le,
    intervalIntegral.integral_of_le two_pi_pos.le, ← integral_conj]
  simp only [inner_smul_right, map_mul, inner_conj_symm, ← fourier_neg]
  simp 
  exact Or.inl (map_ofNat (starRingEnd ℂ) 2)

section Concrete

variable {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- The standard Hilbert basis of `ℓ²(ℕ₀)`. -/
def stdBasisN : HilbertBasis ℕ ℂ Ell2 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Ell2)

lemma periodize_projObsRow_eqOn (hW : IsTransport γ E W) :
    EqOn (periodize (projObsRow W)) (projObsRow W) (Icc 0 (2 * π)) :=
  fun _ hθ => periodize_eqOn_Icc (projObsRow_endpoint hW) hθ

lemma lipschitzWith_periodize_projObsRow (hK : LipschitzWith K γ) (hW : IsTransport γ E W) :
    LipschitzWith ⟨Real.sqrt E * shiftConst * K, by have := shiftConst_nonneg; positivity⟩
      (periodize (projObsRow W)) :=
  lipschitzWith_periodize (fun _ hx _ hy => norm_projObsRow_sub_le hK hW hx hy)
    (projObsRow_endpoint hW)

lemma continuousOn_projObsRow (hK : LipschitzWith K γ) (hW : IsTransport γ E W) :
    ContinuousOn (projObsRow W) (Icc 0 (2 * π)) :=
  (lipschitzWith_periodize_projObsRow hK hW).continuous.continuousOn.congr
    (periodize_projObsRow_eqOn hW).symm

lemma norm_projObsRow_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) {θ : ℝ}
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
lemma inner_projObsCoeffVec (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (v : Ell2)
    (n : ℤ) :
    ⟪projObsCoeffVec W n, v⟫_ℂ = fourierCoeffOn two_pi_pos
      (fun θ => observation W (cutProj (cutC (W (2 * π)) (basisVec 0)) v) θ) n := by
  rw [projObsCoeffVec, inner_fourierCoeffOn_neg (continuousOn_projObsRow hK hW)]
  simp  [observation_cutProj_eq]

/-- The normalized rows `ρₙ = λₙ^{1/2} r̂_E(-n)`, `λₙ = 1 + |n|`. -/
def normProjObsRow (W : ℝ → Ell2 →L[ℂ] Ell2) (n : ℤ) : Ell2 :=
  (Real.sqrt (1 + |(n : ℝ)|) : ℂ) • projObsCoeffVec W n

lemma norm_normProjObsRow_sq (W : ℝ → Ell2 →L[ℂ] Ell2) (n : ℤ) :
    ‖normProjObsRow W n‖ ^ 2 = (1 + |(n : ℝ)|) * ‖projObsCoeffVec W n‖ ^ 2 := by
  rw [normProjObsRow, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

private theorem weighted_fourier_row_bound {r : ℝ → Ell2} {K : NNReal}
    (hr : LipschitzWith K r) (hper : Function.Periodic r (2 * π)) {B : ℝ}
    (hB : ∀ θ ∈ Icc 0 (2 * π), ‖r θ‖ ≤ B) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖fourierCoeffOn two_pi_pos r (-n)‖ ^ 2) ∧
    ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖fourierCoeffOn two_pi_pos r (-n)‖ ^ 2 ≤ π ^ 2 * K ^ 2 / 4 + 2 * B ^ 2 := by
  have h := tsum_sq_fourierCoeff_rows_le stdBasisN.orthonormal hr.continuous hB
  have h₁ := summable_sq_mul_fourierCoeff stdBasisN.orthonormal hr hper
  have h₂ := tsum_sq_mul_fourierCoeff_le stdBasisN.orthonormal hr hper
  obtain ⟨hs, hle⟩ := summable_weight_norm_sq_of_basis stdBasisN
    (fun n => fourierCoeffOn two_pi_pos r (-n))
    (by simpa only [inner_fourierCoeffOn_neg hr.continuous.continuousOn] using h₁)
    (by simpa only [inner_fourierCoeffOn_neg hr.continuous.continuousOn] using h.1)
  simp only [inner_fourierCoeffOn_neg hr.continuous.continuousOn] at hle
  exact ⟨hs, hle.trans (add_le_add h₂ (by gcongr; exact h.2))⟩

/-- The normalized rows are square summable. -/
theorem summable_normProjObsRow (hK : LipschitzWith K γ) (hW : IsTransport γ E W) :
    Summable fun n => ‖normProjObsRow W n‖ ^ 2 := by
  have he (n : ℤ) : projObsCoeffVec W n = fourierCoeffOn two_pi_pos (periodize (projObsRow W)) (-n) :=
    (fourierCoeffOn_congr_Icc (periodize_projObsRow_eqOn hW) _).symm
  simp_rw [norm_normProjObsRow_sq, he]
  exact (weighted_fourier_row_bound (lipschitzWith_periodize_projObsRow hK hW)
    (periodic_periodize _) (B := 1) fun θ hθ => by
      rw [periodize_projObsRow_eqOn hW hθ]; exact norm_projObsRow_le hK hW hθ).1

open Classical in
/-- **The dual of the projected observation** `T_E^♯ Λ^{1/2} : ℓ²(ℤ) → ℓ²(ℕ₀)`, i.e. the
extension of `T_E^♯ = Π^c_E O_E^*` to `X = H^{-1/2}(𝕋)` read in normalized Fourier coordinates:
`f ↦ ∑ₙ fₙ λₙ^{1/2} r̂_E(-n)`. (It is set to `0` if the rows are not square summable, which
does not happen for transports of Lipschitz curves.) -/
def projObsDual (W : ℝ → Ell2 →L[ℂ] Ell2) : L2Z →L[ℂ] Ell2 :=
  if h : Summable fun n => ‖normProjObsRow W n‖ ^ 2 then rowSynth (normProjObsRow W) h else 0

lemma projObsDual_eq (hK : LipschitzWith K γ) (hW : IsTransport γ E W) :
    projObsDual W = rowSynth (normProjObsRow W) (summable_normProjObsRow hK hW) := by
  rw [projObsDual, dif_pos (summable_normProjObsRow hK hW)]

end Concrete

/-! ### Continuity in the energy -/

section Energy

variable {γ : ℝ → ℂ} {K : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

/-- **Lemma 6.3 (continuity of the extended adjoint).** If `c_{E₀} ≠ 0`, then
`E ↦ T_E^♯ Λ^{1/2}` is continuous at `E₀` in operator norm. -/
theorem tendsto_projObsDual_energy (hK : LipschitzWith K γ)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    Tendsto (fun E => projObsDual (Ws E)) (𝓝 E₀) (𝓝 (projObsDual (Ws E₀))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨Lf, Bf, hL, hB, hdat⟩ := projObsRowDiff_data hK hWs E₀ hc
  have hLf : Tendsto (fun E => ((Lf E).toNNReal : ℝ)) (𝓝 E₀) (𝓝 0) := by
    have := (NNReal.continuous_coe.tendsto _).comp ((continuous_real_toNNReal.tendsto 0).comp hL)
    simpa [Function.comp_def] using this
  have hlim := (((hLf.pow 2).const_mul (π ^ 2)).div_const 4).add ((hB.pow 2).const_mul 2) |>.sqrt
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div, add_zero, Real.sqrt_zero] at hlim
  refine squeeze_zero (fun E => norm_nonneg _) (fun E => ?_) hlim
  rw [projObsDual_eq hK (hWs E), projObsDual_eq hK (hWs E₀)]
  refine (norm_rowSynth_sub_le _ _ _ _).trans (Real.sqrt_le_sqrt ?_)
  have he (n : ℤ) : projObsCoeffVec (Ws E) n - projObsCoeffVec (Ws E₀) n =
      fourierCoeffOn two_pi_pos (periodize (projObsRowDiff Ws E₀ E)) (-n) := by
    rw [projObsCoeffVec, projObsCoeffVec, ← fourierCoeffOn_sub_of_continuousOn
      (continuousOn_projObsRow hK (hWs E)) (continuousOn_projObsRow hK (hWs E₀))]
    exact (fourierCoeffOn_congr_Icc (fun θ hθ =>
      periodize_eqOn_Icc (projObsRowDiff_endpoint hWs E₀ E) hθ) _).symm
  have hn (n : ℤ) : ‖normProjObsRow (Ws E) n - normProjObsRow (Ws E₀) n‖ ^ 2 =
      (1 + |(n : ℝ)|) * ‖fourierCoeffOn two_pi_pos (periodize (projObsRowDiff Ws E₀ E)) (-n)‖ ^ 2 := by
    rw [normProjObsRow, normProjObsRow, ← smul_sub, he, norm_smul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  simp_rw [hn]
  exact (weighted_fourier_row_bound (hdat E).1 (periodic_periodize _) fun θ hθ => by
    rw [periodize_eqOn_Icc (projObsRowDiff_endpoint hWs E₀ E) hθ]
    exact (hdat E).2 θ hθ).2

end Energy

/-! ### Parseval's identity in inner-product form -/


/-! ### The reduced observation of Lemma 7.4 -/


end PolyaNeumann
