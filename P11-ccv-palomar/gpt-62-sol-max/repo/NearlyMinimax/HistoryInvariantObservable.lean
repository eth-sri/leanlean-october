module

public import NearlyMinimax.HighObservableRegularity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue


@[expose] public section

/-!
# Invariant observable laws derived from genuine conditional local annihilation
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

section
variable {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : ∀ j h, ∫ e, F (historyMarkedAppend dependent P.symm j (h, e)) * a e ∂π = 0)
include hF hM hFbound hkill

section
variable {t : ℝ} (ht : t ∈ Icc 0 T)
include ht

/-- Conditional signed annihilation kills the positive prior's append generator by Fubini. -/
private theorem prior_generator_eq_zero :
    historyMarkedPriorGenerator dependent P.symm Δ t π a F = 0 := by
  let _ := P.probability ht
  unfold historyMarkedPriorGenerator
  apply Finset.sum_eq_zero
  intro j _
  let G := fun p : HistoryMarked dependent E × E => F (historyMarkedAppend dependent P.symm j p) * a p.2
  have hG : Measurable G :=
    (hF.comp (historyMarkedAppend_measurable dependent P.symm j)).mul (P.measurable.comp measurable_snd)
  have hi : Integrable G ((historyMarkedPrior dependent Δ t π a).prod π) :=
    Integrable.of_bound hG.aestronglyMeasurable (M * B) (.of_forall fun p => by
      simpa only [G, Real.norm_eq_abs, abs_mul] using
        mul_le_mul (hFbound _) (P.bound p.2) (abs_nonneg _) hM)
  change (∫ p, G p ∂_) = 0
  rw [integral_prod G hi]
  simp [G, hkill j]

/-- An annihilated bounded observable is constant along the source path. -/
theorem historyMarkedPrior_invariant_observable :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) = ∫ h, F h ∂historyMarkedReference dependent Δ π := by
  have hT := ht.1.trans ht.2
  let f := fun u => ∫ h, F h ∂historyMarkedPrior dependent Δ u π a
  have h0 : f 0 = ∫ h, F h ∂historyMarkedReference dependent Δ π := by
    change (∫ h, F h ∂historyMarkedPrior dependent Δ 0 π a) = _
    rw [P.integral_eq_density ⟨le_rfl, hT⟩ F]
    simp [historyMarkedDensity_zero]
  change f t = _
  rw [← h0]
  rcases ht.1.eq_or_lt with he | hp
  · simp [← he]
  have hF₀ := BoundedPath.const (s := Icc 0 T) hF hM hFbound
  have hc : ContinuousOn f (Icc 0 T) :=
    (historyMarkedPrior_variable_observable_lipschitz P hF₀
      (fun h => (LipschitzWith.const (F h)).lipschitzOnWith)).continuousOn
  have hd (u : ℝ) (hu : u ∈ Ioo 0 T) : HasDerivAt f 0 u := by
    have he := historyMarkedPrior_observable_product_rule P hu
      (hF₀.mono Ioo_subset_Icc_self) (BoundedPath.const (f := fun _ : HistoryMarked dependent E => 0)
        measurable_const le_rfl (by simp)) (fun _ v _ => hasDerivAt_const v _)
    simpa only [f, prior_generator_eq_zero P F hF M hM hFbound hkill (Ioo_subset_Icc_self hu),
      integral_zero, add_zero] using he
  obtain ⟨u, hu, he⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hp (hc.mono (Icc_subset_Icc_right ht.2))
    (fun u hu => hd u (Ioo_subset_Ioo_right ht.2 hu))
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp he.symm).resolve_right (by simpa using hp.ne'))

end

end
end NearlyMinimax
