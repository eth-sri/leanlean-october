module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffOperator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Tactic

/-! # Measurability and finite localized source norm for the near-full cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open MeasureTheory Set Parabolic
open scoped ENNReal

/-- The full Borel coefficient and smooth jets give a measurable cutoff operator. -/
theorem measurable_scaledUnitCutoff_backwardOperator {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {A : FullKineticCoefficient d}
    (hA : Measurable (fullKineticCoefficientAt A))
    (P₀ : KineticPoint d) (R ell : ℝ) :
    Measurable (backwardOperator A (scaledUnitCutoff f P₀ R ell)) := by
  have hT := ((continuous_unitCutoffTransport hf).comp
    (continuous_kineticAffineInverse P₀ R)).measurable
  have hH := ((continuous_unitCutoffVelocityHessian hf).comp
    (continuous_kineticAffineInverse P₀ R)).measurable
  have hC : Measurable (fun P => matrixContraction (fullKineticCoefficientAt A P)
      (sliceHessian (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
        (kineticAffineInverse P₀ R P).velocity)) := by
    unfold matrixContraction
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    fun_prop
  convert ((measurable_const (a := ell * (R ^ 2)⁻¹)).mul (hT.sub hC)) using 1
  funext P
  apply scaledUnitCutoff_backwardOperator <;> assumption

/-- Smooth tests with a measurable operator have measurable localized sources on open sets. -/
theorem localizedSource_aestronglyMeasurable {d : ℕ} (A : FullKineticCoefficient d)
    {psi u : KineticPoint d → ℝ} {Q : Set (KineticPoint d)} (hQ : IsOpen Q)
    (hpsi : ContinuousOn psi Q) (hu : ContinuousOn u Q)
    (hop : Measurable (backwardOperator A psi)) :
    AEStronglyMeasurable (localizedSource A psi u) (volume.restrict Q) := by
  have hE : MeasurableSet (Q ∩ {P | u P < psi P}) := by
    simpa [Set.preimage] using
      ((hpsi.sub hu).isOpen_inter_preimage hQ (isOpen_Ioi (a := 0))).measurableSet
  have hm : AEStronglyMeasurable
      ((Q ∩ {P | u P < psi P}).indicator
        (fun P => max (backwardOperator A psi P) 0)) volume :=
    ((hop.max measurable_const).aestronglyMeasurable).indicator hE
  apply hm.restrict.congr
  filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
  simp [localizedSource, indicator, mem_inter_iff, mem_ofPred_eq, hP]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
