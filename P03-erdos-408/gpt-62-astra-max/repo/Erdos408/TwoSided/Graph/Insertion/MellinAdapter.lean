module

public import Erdos408.Scales

public import Erdos408.TwoSided.Defs
public import Erdos821.Classical.FourierSeparation
public import Erdos821.P5Mellin.MellinCutoff

/-!
# The Mellin cutoff adapter

The adapter for X6 of `blueprint/two_sided_correlation.md` §4.2 (WD §5.2): upstream's
`mellinCutoffTask_proof` (for `MellinCutoffTask`) takes complex cutoffs with `CutoffBound`
derivative bounds and gives densities on `Fin 1 → ℝ`. Here the cutoff class `CutoffAdmissible`
satisfies `CutoffBound` at `C = 1`, `lo = κ⁻¹`, `hi = κ`, `bounds j = max (M j) 0` eventually;
`exists_mellinCutoff` (`Graph/Insertion.lean`) transports the densities to `ℝ` along
`t ↦ (fun _ => t)`.
-/

@[expose] public section

namespace Erdos408.TwoSided.InsertionMellin

open Filter

/-- Eventually the derivative bounds of the cutoff class are below `max (M k) 0 L^{k+1}`:
`T^{C_Ψ k} ≤ L^{k+1}` once `T ≥ 1` and `max(C_Ψ, 0) log T ≤ T`, with `T = log L`. -/
theorem eventually_iteratedDeriv_bound (CΨ : ℝ) (M : ℕ → ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (Ψ : ℝ → ℝ) (k : ℕ) (y : ℝ),
      |iteratedDeriv k Ψ y| ≤ M k * logLog x ^ (CΨ * k) →
        |iteratedDeriv k Ψ y| ≤ max (M k) 0 * Real.log x ^ ((1 : ℝ) * ((k : ℝ) + 1)) := by
  set c : ℝ := max CΨ 0
  have hc0 : 0 ≤ c := by positivity
  have hT : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlog := (Real.isLittleO_log_id_atTop.bound (by positivity : (0 : ℝ) < 1 / (c + 1)))
  filter_upwards [hT.eventually hlog, hT.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hlx hT1 hL0
  intro Ψ k y hk
  set T := Real.log (Real.log x)
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT1
  rw [Real.norm_of_nonneg hlT, id, Real.norm_of_nonneg (by linarith)] at hlx
  -- `c log T ≤ T`
  have hcT : c * Real.log T ≤ T := by
    have h := mul_le_mul_of_nonneg_left hlx hc0
    calc _ ≤ c * (1 / (c + 1) * T) := h
      _ = c / (c + 1) * T := by ring
      _ ≤ 1 * T := by
          gcongr
          bound
      _ = T := one_mul T
  have hpow : T ^ (CΨ * k) ≤ Real.log x ^ ((1 : ℝ) * ((k : ℝ) + 1)) := by
    calc _ ≤ T ^ (c * k) :=
          by bound
      _ = Real.exp (Real.log T * (c * k)) := Real.rpow_def_of_pos (by linarith) _
      _ ≤ Real.exp (T * ((1 : ℝ) * ((k : ℝ) + 1))) := Real.exp_le_exp.2 (by nlinarith)
      _ = _ := (Real.rpow_def_of_pos hL0 _).symm
  calc _ ≤ M k * T ^ (CΨ * k) := hk
    _ ≤ max (M k) 0 * T ^ (CΨ * k) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ _ :=
        by gcongr

/-- The iterated derivatives of a smooth real function, cast to `ℂ`, have the same norms. -/
theorem norm_iteratedDeriv_ofReal {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (k : ℕ) (y : ℝ) :
    ‖iteratedDeriv k (fun y => (Ψ y : ℂ)) y‖ = |iteratedDeriv k Ψ y| := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hΨ.contDiffAt
    (by exact_mod_cast le_top)

end Erdos408.TwoSided.InsertionMellin
