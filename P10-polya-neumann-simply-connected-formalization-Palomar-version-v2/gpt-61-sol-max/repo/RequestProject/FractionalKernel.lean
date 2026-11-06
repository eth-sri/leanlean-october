module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.FractionalRows
public import RequestProject.KernelRows

/-!
# `H^{1+δ}` regularity of kernels in the first variable (Lemma 6.6, fractional part)

Let `k(θ, t)` be a bounded kernel, measurable in `t`, `2π`-periodic and uniformly Lipschitz in
`θ`. Suppose that its second differences in `θ` satisfy, uniformly in `t ∈ [0, 2π)`,

  `|k(θ+2h, t) - 2k(θ+h, t) + k(θ, t)| ≤ A h²`  for `θ ∈ [0, 2π - 2h]`,

(this holds when `θ ↦ k(θ, t)` has an `A`-Lipschitz derivative on `[0, 2π]`, the derivative being
allowed to jump at the cut). Then the double Fourier coefficients
`k_{n m} = (θ ↦ (t ↦ k(θ, t))^(n))^(m)` satisfy

  `∑_{n, m} |m|^{2+2δ} |k_{n m}|² < ∞`  for every `0 ≤ δ < 1/2`
  (`summable_kernelCoeff_three_halves`).

This is the fractional analogue of `summable_sq_mul_kernelCoeff`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory Topology



/-- `min a b ≤ a^τ b^{1-τ}` for `a, b ≥ 0` and `0 ≤ τ ≤ 1`. -/
lemma min_le_rpow_mul_rpow {a b τ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    min a b ≤ a ^ τ * b ^ (1 - τ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    calc a = a ^ τ * a ^ (1 - τ) := by
          rw [← Real.rpow_add' ha (by norm_num), add_sub_cancel, Real.rpow_one]
      _ ≤ a ^ τ * b ^ (1 - τ) := by
          gcongr
  · rw [min_eq_right h]
    calc b = b ^ τ * b ^ (1 - τ) := by
          rw [← Real.rpow_add' hb (by norm_num), add_sub_cancel, Real.rpow_one]
      _ ≤ a ^ τ * b ^ (1 - τ) := by gcongr

section Rows

variable {H : Type*} [NormedAddCommGroup H] {r : ℝ → H} (hr : Continuous r)
include hr

/-- **Interpolated second-difference bound.** If `‖Δ²_h r(θ)‖ ≤ A h²` for `θ ∈ [0, 2π - 2h]`,
`‖Δ²_h r(θ)‖ ≤ B h` for all `θ` and `‖r‖ ≤ M`, then for `0 ≤ τ ≤ 1` and `0 < h ≤ π/2`,
`∫₀^{2π} ‖Δ²_h r‖² ≤ (π² A² + 2B²)^τ (32 π M²)^{1-τ} h^{3τ}`. -/
theorem secondDiff_integral_le_interp {A B M τ h : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hh : 0 < h) (hh' : h ≤ π / 2)
    (hgood : ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h), ‖secondDiff r h θ‖ ≤ A * h ^ 2)
    (hbad : ∀ θ, ‖secondDiff r h θ‖ ≤ B * h) (hM : ∀ θ, ‖r θ‖ ≤ M) :
    ∫ θ in (0 : ℝ)..circlePeriod, ‖secondDiff r h θ‖ ^ 2 ≤
      ((π ^ 2 * A ^ 2 + 2 * B ^ 2) ^ τ * (32 * π * M ^ 2) ^ (1 - τ)) * h ^ (3 * τ) := by
  have hFc := (continuous_secondDiff hr h).norm.pow 2
  have h1 := secondDiff_integral_le hr hh hh' hgood hbad
  have h4 : ∀ θ, ‖secondDiff r h θ‖ ≤ 4 * M := by
    intro θ
    unfold secondDiff
    have := hM (θ + 2 * h); have := hM (θ + h); have := hM θ
    have e1 := norm_sub_le (r (θ + 2 * h) - r (θ + h)) (r (θ + h) - r θ)
    have e2 := norm_sub_le (r (θ + 2 * h)) (r (θ + h))
    have e3 := norm_sub_le (r (θ + h)) (r θ)
    linarith
  have h2 : ∫ θ in (0 : ℝ)..circlePeriod, ‖secondDiff r h θ‖ ^ 2 ≤ 32 * π * M ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
      (hFc.intervalIntegrable _ _) intervalIntegrable_const
      fun θ _ => pow_le_pow_left₀ (norm_nonneg _) (h4 θ) 2
    simp   at this
    linarith
  have hX : 0 ≤ π ^ 2 * A ^ 2 + 2 * B ^ 2 := by positivity
  have hm := min_le_rpow_mul_rpow (mul_nonneg hX (by positivity : (0 : ℝ) ≤ h ^ (3 : ℝ)))
    (by positivity : (0 : ℝ) ≤ 32 * π * M ^ 2) hτ0 hτ1
  have e : ((π ^ 2 * A ^ 2 + 2 * B ^ 2) * h ^ (3 : ℝ)) ^ τ * (32 * π * M ^ 2) ^ (1 - τ) =
      ((π ^ 2 * A ^ 2 + 2 * B ^ 2) ^ τ * (32 * π * M ^ 2) ^ (1 - τ)) * h ^ (3 * τ) := by
    rw [Real.mul_rpow hX (by positivity), ← Real.rpow_mul hh.le]
    ring
  grind

end Rows

/-- The exponent `τ = (5 + 2δ)/6` used for the interpolation: `2 + 2δ < 3τ ≤ 3` for
`0 ≤ δ < 1/2`. -/
def interpExp (δ : ℝ)  := (5 + 2 * δ) / 6

/-- The explicit `H^{1+δ}` bound of a kernel with second-difference constant `A`, Lipschitz
constant `K` and sup bound `M`. -/
def interpBound A K M δ  :=
  |circlePeriod⁻¹ * ((π ^ 2 * A ^ 2 + 2 * (2 * K) ^ 2) ^ interpExp δ *
      (32 * π * M ^ 2) ^ (1 - interpExp δ)) * (π / 2) ^ (3 * interpExp δ)| *
    2 ^ (2 * (1 + δ)) * (1 - (2 : ℝ) ^ (2 * (1 + δ) - 3 * interpExp δ))⁻¹

/-- `interpBound A K M δ → 0` as `M → 0`, for `δ < 1/2`. -/
theorem tendsto_interpBound A K  (hδ' : δ < 1 / 2) :
    Tendsto (fun M => interpBound A K M δ) (𝓝 0) (𝓝 0) := by
  have hτ : 0 < 1 - interpExp δ := by unfold interpExp; linarith
  have hc : Continuous fun M : ℝ => (32 * π * M ^ 2) ^ (1 - interpExp δ) :=
    (continuous_const.mul (continuous_pow 2)).rpow_const fun _ => Or.inr hτ.le
  have hcont : Continuous fun M => interpBound A K M δ := by
    unfold interpBound
    fun_prop
  have := hcont.tendsto 0
  convert this using 2
  unfold interpBound
  rw [show (32 * π * 0 ^ 2) = 0 by ring, Real.zero_rpow hτ.ne']
  simp

section Kernel

variable {k : ℝ → ComplexCurve} {M } (hmeas : ∀ θ, Measurable (k θ)) (hbd : ∀ θ t, ‖k θ t‖ ≤ M)

include hmeas hbd in
/-- A pointwise bound on second differences of the kernel bounds the second difference of the
rows in `L²(𝕋)`. -/
lemma norm_secondDiff_kernelRow_le  (hD : 0 ≤ D)
    (hpt : ∀ t ∈ Set.Ico 0 circlePeriod, ‖secondDiff (fun θ => k θ t) h θ‖ ≤ D) :
    ‖secondDiff (kernelRow hmeas hbd) h θ‖ ≤ D := by
  unfold secondDiff kernelRow
  rw [← MemLp.toLp_sub, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
  set hm := fun θ => memLp_liftIco_two_pi (hmeas θ) (hbd θ)
  have h := Lp.norm_le_of_ae_bound (μ := (@AddCircle.haarAddCircle circlePeriod _)) (p := 2)
    (f := MemLp.toLp _ (((hm (θ + 2 * h)).sub (hm (θ + h))).sub ((hm (θ + h)).sub (hm θ))))
    (C := D) hD ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle circlePeriod _) = 1 := by
      simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp
      (((hm (θ + 2 * h)).sub (hm (θ + h))).sub ((hm (θ + h)).sub (hm θ)))] with x hx
    rw [hx]
    exact hpt _ (circRep_mem x)

include hmeas hbd in
lemma norm_kernelRow_le θ : ‖kernelRow hmeas hbd θ‖ ≤ M := by
  have hM0  := (norm_nonneg _).trans (hbd 0 0)
  unfold kernelRow
  have h := Lp.norm_le_of_ae_bound (μ := (@AddCircle.haarAddCircle circlePeriod _)) (p := 2)
    (f := MemLp.toLp _ (memLp_liftIco_two_pi (hmeas θ) (hbd θ))) (C := M) hM0 ?_
  · have h1 : measureUnivNNReal (@AddCircle.haarAddCircle circlePeriod _) = 1 := by
      simp [measureUnivNNReal]
    simpa [h1] using h
  · filter_upwards [MemLp.coeFn_toLp (memLp_liftIco_two_pi (hmeas θ) (hbd θ))] with x hx
    measurability

include hmeas hbd in
/-- **Quantitative `H^{1+δ}` bound for kernels.** Let `k(θ, t)` be bounded by `M`, measurable in
`t`, `2π`-periodic and uniformly `K`-Lipschitz in `θ`, with second differences in `θ` at most
`A h²` on `[0, 2π - 2h]`. Then for `0 ≤ δ < 1/2` the double Fourier coefficients satisfy
`∑_{n,m} |m|^{2+2δ} |k_{n m}|² < ∞` and this sum is at most `interpBound A K M δ`. -/
theorem kernelCoeff_interp {K : NNReal}  (hA : 0 ≤ A)
    (hlip : ∀ θ θ' t, t ∈ Set.Ico 0 circlePeriod → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hper : ∀ θ t, t ∈ Set.Ico 0 circlePeriod → k (θ + 2 * π) t = k θ t)
    (hsecond : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h),
      ∀ t ∈ Set.Ico 0 circlePeriod, ‖secondDiff (fun θ => k θ t) h θ‖ ≤ A * h ^ 2)
     (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    Summable (fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2) ∧
    ∑' p : ℤ × ℤ, |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2 ≤
      interpBound A K M δ := by
  have hL : LipschitzWith K (kernelRow hmeas hbd) := by
    refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_kernelRow_sub_le hmeas hbd hlip θ θ'
  have hbad : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ,
      ‖secondDiff (kernelRow hmeas hbd) h θ‖ ≤ (2 * K) * h := by
    intro h hh _ θ
    have e1 := norm_kernelRow_sub_le hmeas hbd hlip (θ + 2 * h) (θ + h)
    have e2 := norm_kernelRow_sub_le hmeas hbd hlip (θ + h) θ
    rw [show θ + 2 * h - (θ + h) = h by ring, abs_of_pos hh] at e1
    rw [show θ + h - θ = h by ring, abs_of_pos hh] at e2
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hgood  := fun h h0 h1 θ hθ =>
    norm_secondDiff_kernelRow_le hmeas hbd (by positivity) (hsecond h h0 h1 θ hθ)
  have hτ0 : 0 ≤ interpExp δ := by unfold interpExp; linarith
  have hτ1 : interpExp δ ≤ 1 := by unfold interpExp; linarith
  have hfin := sum_rpow_mul_fourierCoeff_rows_le (fourierBasis (T := 2 * π)).orthonormal
    hL.continuous (kernelRow_periodic hmeas hbd hper) (s := 1 + δ) (β := 3 * interpExp δ)
    (by linarith) (by unfold interpExp; linarith) fun h h0 h1 =>
      secondDiff_integral_le_interp hL.continuous hτ0 hτ1 h0 h1 (hgood h h0 h1) (hbad h h0 h1)
        (norm_kernelRow_le hmeas hbd)
  simp_rw [inner_kernelRow_fourierBasis, fourierCoeffOn_conj, Complex.norm_conj] at hfin
  set f : ℤ × ℤ → ℝ := fun p => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2 with hf
  set σ : ℤ × ℤ ≃ ℤ × ℤ := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hfσ : ∀ u : Finset (ℤ × ℤ), ∑ p ∈ u, f (σ p) ≤ interpBound A K M δ := by
    intro u
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) (hfin u)
    simp [hf, σ, show 2 * (1 + δ) = 2 + 2 * δ by ring]
  have hs  := summable_of_sum_le (fun p => by simp only [ hf]; positivity) hfσ
  have hs' : Summable f := (Equiv.summable_iff σ).mp hs
  refine ⟨hs', ?_⟩
  rw [← Equiv.tsum_eq σ]
  exact hs.tsum_le_of_sum_le hfσ

include hmeas hbd in
/-- **`H^{1+δ}` regularity of a kernel in the first variable.** Let `k(θ, t)` be bounded,
measurable in `t`, `2π`-periodic and uniformly `K`-Lipschitz in `θ` (for `t ∈ [0, 2π)`), and
suppose that for `0 < h ≤ π/2`, `θ ∈ [0, 2π - 2h]` and `t ∈ [0, 2π)`,
`|k(θ+2h, t) - 2k(θ+h, t) + k(θ, t)| ≤ A h²`. Then the double Fourier coefficients satisfy
`∑_{n,m} |m|^{2+2δ} |k_{n m}|² < ∞` for every `0 ≤ δ < 1/2`. -/
theorem summable_kernelCoeff_three_halves {K : NNReal}  (hA : 0 ≤ A)
    (hlip : ∀ θ θ' t, t ∈ Set.Ico 0 circlePeriod → ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hper : ∀ θ t, t ∈ Set.Ico 0 circlePeriod → k (θ + 2 * π) t = k θ t)
    (hsecond : ∀ h : ℝ, 0 < h → h ≤ π / 2 → ∀ θ ∈ Set.Icc 0 (2 * π - 2 * h),
      ∀ t ∈ Set.Ico 0 circlePeriod, ‖secondDiff (fun θ => k θ t) h θ‖ ≤ A * h ^ 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    Summable fun p : ℤ × ℤ => |(p.2 : ℝ)| ^ (2 + 2 * δ) *
      ‖fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2‖ ^ 2 :=
  (kernelCoeff_interp hmeas hbd hA hlip hper hsecond hδ hδ').1

end Kernel

end PolyaNeumann
