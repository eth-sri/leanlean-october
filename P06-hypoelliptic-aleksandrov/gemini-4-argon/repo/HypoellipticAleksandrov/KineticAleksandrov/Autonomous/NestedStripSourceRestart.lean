module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSourceIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation

/-! # Compact-source nested identity with the actual internal-exit restriction -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/- Internal exits for a pair of single intervals in physical coordinates. -/
def nestedIntervalInternalExit (H1 H2 : Interval) (sMinus T : ℝ) : Set Point :=
  {p | sMinus < p.time ∧ p.time < T ∧
    (p.velocity 0 = H1.lo ∨ p.velocity 0 = H1.hi) ∧ p.velocity 0 ∈ H2.carrier}

/- The actual interval internal-exit set is Borel. -/
theorem measurableSet_nestedIntervalInternalExit (H1 H2 : Interval) (sMinus T : ℝ) :
    MeasurableSet (nestedIntervalInternalExit H1 H2 sMinus T) := by
  have hv : Measurable (fun p : Point => p.velocity 0) :=
    ((continuous_apply 0).comp continuous_velocity).measurable
  exact (measurableSet_lt measurable_const continuous_time.measurable).inter
    ((measurableSet_lt continuous_time.measurable measurable_const).inter
      (((measurableSet_eq_fun hv measurable_const).union
        (measurableSet_eq_fun hv measurable_const)).inter
        (isOpen_Ioo.measurableSet.preimage hv)))

/- Outside the internal restart boundary the larger source potential is zero at smaller exits. -/
theorem nestedSourcePotential_zero_outer
    (hH : HormanderHypoellipticityStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (E : StripEvolution H2)
    (hE : IsStripEvolution A H2 E) (sMinus T : ℝ) (f : exitProbeSubmodule)
    (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆ {p | p.time < T ∧ p.velocity 0 ∈ H2.carrier})
    (p ) (hp : p ∈ reconstructionExit H1 sMinus T)
    (hn : p ∉ nestedIntervalInternalExit H1 H2 sMinus T) :
    nestedSourcePotential H2 E T f p = 0 := by
  have hz := nestedSourcePotential_continuous_zero_exit hH hlam hLam A H2 E hE T f hfn hs
  rcases hp with hp | hp
  · exact hz.2.1 p hp.1
  · have hv : p.velocity 0 ∉ H2.carrier := fun hv => hn ⟨hp.1, hp.2.1, hp.2.2, hv⟩
    have hc := (nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T
      (Or.inr (Or.inr hp))).2
    apply hz.2.2 p
    change ¬ (H2.lo < p.velocity 0 ∧ p.velocity 0 < H2.hi) at hv
    by_cases hl : p.velocity 0 = H2.lo
    · exact Or.inl hl
    · exact Or.inr (le_antisymm hc.2 (by
        by_contra hn
        exact hv ⟨lt_of_le_of_ne hc.1 (Ne.symm hl), lt_of_not_ge hn⟩))

/- The larger Green source integral is the smaller integral plus its true internal restart.
The restart measure is the smaller exit measure restricted to the literal internal boundary. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
