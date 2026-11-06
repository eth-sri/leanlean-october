module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJointSource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceBound
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifiedJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionOperator

/-! # Spacetime recovery and shell domination of the actual limiting source -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set HypoellipticAleksandrov.Parabolic
open scoped Topology
open scoped Convolution

/- The spacetime indicator uses exactly the fixed-time profile domain. -/
theorem constructionIndicatorSource_apply {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (q : XV d) :
    constructionIndicatorSource h r mu R (t, q) =
      {y | profileFunction h y < 1}.indicator
        (fun y => timeCutoffSourceRepresentative h r mu R ⟨t, y.1, y.2⟩) q := by
  by_cases hp : profileFunction h q < 1 <;> simp [constructionIndicatorSource, hp]

/- The actual mollified operator converges almost everywhere in native spacetime
volume to a jointly measurable version of the selected zero-extended source. -/
theorem construction_fixed_time_le_ae_spacetime {d } (f g : ℝ × XV d → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ t : ℝ, ∀ᵐ q ∂volume, f (t, q) ≤ g (t, q)) :
    ∀ᵐ P : KineticPoint d ∂volume,
      f (KineticPoint.equivProd d P) ≤ g (KineticPoint.equivProd d P) := by
  have hs := measurableSet_le hf hg
  have hp : ∀ᵐ z : ℝ × XV d ∂volume, f z ≤ g z :=
    (Measure.ae_prod_iff_ae_ae hs).mpr (Eventually.of_forall hfg)
  exact (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae hp

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
