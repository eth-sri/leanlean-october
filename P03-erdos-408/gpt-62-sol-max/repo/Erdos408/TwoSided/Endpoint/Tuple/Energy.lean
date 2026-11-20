module

public import Erdos408.OneSided.Major.Energy.Average
public import Erdos408.TwoSided.Endpoint.Tuple.Exceptional
public import Erdos821.Classical.FourierSeparation
public import Erdos821.P5Mellin.MellinCutoff

/-!
# Separation of the cutoff piece (tuple part)

S13 of `blueprint/two_sided_correlation.md` §6.3 (E6, separation; PD (6.32)).

* `exists_mellin_piece`: a piece `ψ₁` supported in `[1, 2]` with derivative bounds `M₁` has a
  Mellin density `a` with `∫ |a| ≤ L^{K₁}` and tail `∫_{|ξ| > L^{C_sep}} |a| ≤ K_A L^{-A_t}`,
  from the vendored `Erdos821.P5Mellin.mellinCutoffTask_proof` at `C = 1`, `lo = 1`, `hi = 2`,
  `bounds j = max (M₁ j) 0`; the density is transported from `Fin 1 → ℝ` to `ℝ` as in
  `exists_mellinCutoff` (`Erdos408/TwoSided/Graph/Insertion.lean`).
* `integral_sq_le_of_le_integral_split`: the energy of an average
  `F(τ) ≤ c ∫ w(ξ) h(ξ, τ) dξ`, with the inner energies bounded by `E₁` for `|ξ| ≤ R` and by
  `E₂` everywhere: `∫ F² ≤ c² (∫ w) (E₁ ∫ w + E₂ ∫_{|ξ| > R} w)`. This is
  `OneSided.integral_sq_le_of_le_integral` (`Erdos408/OneSided/Major/Energy/Average.lean`)
  with the tail kept apart.
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open Filter MeasureTheory

/-- **Mellin density of a piece.** For the class of pieces `ψ₁` supported in `[1, 2]` with
`|ψ₁^{(j)}| ≤ M₁ j` there are `C_sep > 0` and `K₁ > 0` such that, for every tail saving
`A_t > 0`, there is `K_A` with: eventually, every piece has a density `a` with
`∫ |a| ≤ L^{K₁}`, `ψ₁(y) = ∫ a(ξ) y^{2πiξ} dξ` for `y > 0` and
`∫_{|ξ| > L^{C_sep}} |a| ≤ K_A L^{-A_t}`. -/
theorem exists_mellin_piece (M₁ : ℕ → ℝ) :
    ∃ Cf K : ℝ, 0 < Cf ∧ 0 < K ∧ ∀ At : ℝ, 0 < At → ∃ KA : ℝ, 0 < KA ∧ ∀ᶠ x : ℝ in atTop,
      ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
        (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) →
        (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
        ∃ a : ℝ → ℂ, Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ Real.log x ^ K ∧
          (∀ y : ℝ, 0 < y →
            ψ₁ y = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) ∧
          (∫ ξ in {ξ : ℝ | Real.log x ^ Cf < |ξ|}, ‖a ξ‖) ≤ KA * Real.log x ^ (-At) := by
  obtain ⟨Cf, K, hCf, hK, hmel⟩ := Erdos821.P5Mellin.mellinCutoffTask_proof
    Erdos821.Classical.lem_fourier_separation 1 1 2 (fun j => max (M₁ j) 0)
    one_pos one_pos one_lt_two (fun j => le_max_right _ _)
  refine ⟨Cf, K, hCf, hK, fun At hAt => ?_⟩
  obtain ⟨KA, hKA, hx⟩ := hmel At hAt
  refine ⟨KA, hKA, ?_⟩
  filter_upwards [hx, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  intro ψ₁ hψ hψs hψd
  obtain ⟨a, hai, ha₁, harep, hat⟩ := hx ψ₁ ⟨hψ,
    fun y hy => hψs y (Function.mem_support.1 hy),
    fun j y => (hψd j y).trans (le_trans (le_max_left _ _) (le_mul_of_one_le_right
      (le_max_right _ _) (Real.one_le_rpow hL (by positivity))))⟩
  -- transport along `t ↦ (fun _ => t)`
  set e := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm with he
  have hmp : MeasurePreserving e volume volume := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have he₀ : ∀ t, e t 0 = t := fun t => rfl
  refine ⟨fun t => a (e t), (hmp.integrable_comp_emb e.measurableEmbedding).2 hai, ?_, ?_, ?_⟩
  · rw [hmp.integral_comp' (fun ξ => ‖a ξ‖)]
    exact ha₁
  · intro y hy
    rw [harep y hy, ← hmp.integral_comp' (fun ξ => a ξ * Erdos821.Blueprint.Analytic.mellin y
      (2 * Real.pi * ξ 0))]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [he₀, mellin_eq_cpow hy]
  · have hpre : e ⁻¹' {ξ : Fin 1 → ℝ | Erdos821.Blueprint.Analytic.L x ^ Cf < ‖ξ‖} =
        {ξ : ℝ | Real.log x ^ Cf < |ξ|} := by
      ext t
      have : ‖e t‖ = |t| := by
        change ‖fun _ : Fin 1 => t‖ = |t|
        rw [pi_norm_const, Real.norm_eq_abs]
      change Real.log x ^ Cf < ‖e t‖ ↔ Real.log x ^ Cf < |t|
      rw [this]
    rw [← hpre, hmp.setIntegral_preimage_emb e.measurableEmbedding (fun ξ => ‖a ξ‖)]
    exact hat

/-- The energy of an average, with the tail kept apart: if `0 ≤ F(τ) ≤ c ∫ w(ξ) h(ξ, τ) dξ`
with `w ≥ 0` integrable and `0 ≤ h ≤ M` continuous, `∫_a^b h(ξ, ·)² ≤ E₁` for `|ξ| ≤ R` and
`∫_a^b h(ξ, ·)² ≤ E₂` for every `ξ`, then
`∫_a^b F² ≤ c² (∫ w) (E₁ ∫ w + E₂ ∫_{|ξ| > R} w)`. -/
theorem integral_sq_le_of_le_integral_split {a b c M E₁ E₂ R : ℝ} (hab : a ≤ b)
    {w : ℝ → ℝ} (hw : Integrable w) (hw0 : ∀ ξ, 0 ≤ w ξ) {h : ℝ → ℝ → ℝ}
    (hh : Continuous (Function.uncurry h)) (hh0 : ∀ ξ τ, 0 ≤ h ξ τ)
    (hhM : ∀ ξ τ, h ξ τ ≤ M) (hE₁0 : 0 ≤ E₁) (hE₁ : ∀ ξ, |ξ| ≤ R → ∫ τ in a..b, h ξ τ ^ 2 ≤ E₁)
    (hE₂ : ∀ ξ, ∫ τ in a..b, h ξ τ ^ 2 ≤ E₂) {F : ℝ → ℝ}
    (hF0 : ∀ τ, 0 ≤ F τ) (hF : ∀ τ, F τ ≤ c * ∫ ξ, w ξ * h ξ τ) :
    ∫ τ in a..b, F τ ^ 2 ≤
      c ^ 2 * (∫ ξ, w ξ) * (E₁ * (∫ ξ, w ξ) + E₂ * ∫ ξ in {ξ : ℝ | R < |ξ|}, w ξ) := by
  let S : Set ℝ := {ξ | R < |ξ|}
  have hs : MeasurableSet S := measurableSet_lt measurable_const continuous_abs.measurable
  have hg := (hw.const_mul E₁).add ((hw.indicator hs).const_mul E₂)
  have hmajor (ξ : ℝ) : w ξ * (∫ τ in a..b, h ξ τ ^ 2) ≤ E₁ * w ξ + E₂ * S.indicator w ξ := by
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      nlinarith [mul_le_mul_of_nonneg_left (hE₂ ξ) (hw0 ξ), mul_nonneg hE₁0 (hw0 ξ)]
    · rw [Set.indicator_of_notMem hξ, mul_zero, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left (hE₁ ξ (not_lt.1 hξ)) (hw0 ξ)]
  have hb := OneSided.integral_sq_le_of_le_integral_majorant hab hw hw0 hh hh0 hhM hg hmajor hF0 hF
  simp only [Pi.add_apply] at hb
  rw [integral_add (hw.const_mul E₁) ((hw.indicator hs).const_mul E₂), integral_const_mul,
    integral_const_mul, integral_indicator hs] at hb
  exact hb

end Erdos408.TwoSided.TupleHigh
