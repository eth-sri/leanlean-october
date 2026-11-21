module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.UniformInverseMellinBounds

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.EulerDerivativesAndDecay

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve

theorem fieldTransform_uniform_euler_two_ended_bound
    (D : ℝ) (r : ℕ) (b : ℝ) (j n : ℕ) (δ : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        Vendor.PositiveSideSupport b h →
        (∀ x : ℝ, 0 < x → x ≤ 1 →
          ‖Vendor.EulerIter j (fieldTransform D r h) x‖ ≤
            C * Vendor.S b N h * Real.rpow x (-δ)) ∧
        (∀ x : ℝ, 1 ≤ x →
          ‖Vendor.EulerIter j (fieldTransform D r h) x‖ ≤
            C * Vendor.S b N h * Real.rpow x (-(n : ℝ))) := by
  set a : ℝ := min δ ((n : ℝ) + 1) with ha_def
  set v : ℝ := max δ ((n : ℝ) + 1) with hv_def
  have ha : 0 < a := by rw [ha_def]; exact lt_min hδ (by positivity)
  have hav : a ≤ v := by rw [ha_def, hv_def]; exact min_le_max
  obtain ⟨N, C0, hC0, hrap⟩ :=
    B_uniform_rapid_bound D r b a v (j + 2) hD hr hb ha hav
  refine ⟨N, C0 * (v + 1) ^ j, by positivity, ?_⟩
  intro h hh hhc hsupp
  have hS : 0 ≤ Vendor.S b N h := Vendor.S_nonneg b hb N h hh
  have hδmem : δ ∈ Set.Icc a v :=
    ⟨by rw [ha_def]; exact min_le_left _ _, by rw [hv_def]; exact le_max_left _ _⟩
  have hmem : ((n : ℝ) + 1) ∈ Set.Icc a v :=
    ⟨by rw [ha_def]; exact min_le_right _ _, by rw [hv_def]; exact le_max_right _ _⟩
  have step : ∀ c ∈ Set.Icc a v, ∀ x : ℝ, 0 < x →
      ‖Vendor.EulerIter j (fieldTransform D r h) x‖
        ≤ C0 * (v + 1) ^ j * Vendor.S b N h * x ^ (-c) := by
    intro c hc x hx
    have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
    rw [EulerIter_fieldTransform_eq_mellinInv D r h hD hr hh hhc j c x hcpos hx]
    have hmain := InverseMellinBounds.euler_bound (B D r h) hx
      (mul_nonneg hC0.le hS) hcpos.le hc.2 (le_rfl) (hrap h hh hhc hsupp c hc)
    convert hmain using 1 <;> ring
  refine ⟨?_, ?_⟩
  · intro x hx0 hx1
    simpa using step δ hδmem x hx0
  · intro x hx1
    have hlt : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    calc ‖Vendor.EulerIter j (fieldTransform D r h) x‖
        ≤ C0 * (v + 1) ^ j * Vendor.S b N h * x ^ (-(((n : ℝ) + 1))) :=
          step ((n : ℝ) + 1) hmem x hlt
      _ ≤ C0 * (v + 1) ^ j * Vendor.S b N h * x ^ (-(n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

end DedekindZetaZeroFree.LargeSieve

end
