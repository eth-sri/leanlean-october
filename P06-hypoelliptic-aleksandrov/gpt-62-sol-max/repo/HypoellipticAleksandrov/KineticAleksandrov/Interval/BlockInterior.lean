module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlock

/-! # The source unit-frequency block at interior points of case I -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Interior cancellation is uniform over interval location and length. -/
theorem interval_interior_block
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ a c : ℝ,
      InteriorBlockContraction lam Lam m Lb (PDE.oneDimensionalAxisBox a c) δ := by
  obtain ⟨δ, hδ, hδ1, h⟩ := interior_frequency_block exists_terminalEvolution_of_classical
    1 (by norm_num) lam Lam m Lb hlam hlamLam hm hmLb
  exact ⟨δ, hδ, hδ1, fun a c => h _⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval
