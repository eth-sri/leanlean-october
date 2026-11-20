module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Family
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Existence
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Alpha
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamily

/-! # The unconditional Appendix C counterexample -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Filter MeasureTheory Counterexample
open scoped MatrixOrder

/-- Autonomous counterexamples for every finite exponent below `4d`, with fixed shared
ellipticity bounds and cylinder, constructed internally in both coefficient classes. -/
theorem kinetic_aleksandrov_autonomous_counterexample_aux
    (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ lam Lam : ℝ, ∃ P₀ : KineticPoint d, ∃ R : ℝ,
      0 < lam ∧ lam ≤ Lam ∧ 0 < R ∧
      MeasurableFamilyStatement d p lam Lam P₀ R ∧ SmoothFamilyStatement d p lam Lam P₀ R := by
  obtain ⟨α,ha,ha1,he⟩ := exists_subcritical_alpha d hd p hp hpd
  obtain ⟨m⟩ := classicalProfile_exists hd ha ha1
  obtain ⟨S,hS,h⟩ := m.measurable_family hd (zero_lt_one.trans_le hp) ha he
  exact ⟨m.lam,m.Lam,⟨0,0,0⟩,S,m.hlam,m.ordered,hS,h,smoothFamily_of_measurable hp hS h⟩

end HypoellipticAleksandrov.KineticAleksandrov
