module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionNested

/-! # The literal nested finite-union Green and exit decomposition for finite sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The genuine nested-strip identities for a finite measure supported in the smaller open strip.
The source's strict lower-time support, omitted by the planned signature, is restored here. -/
theorem strip_nested
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ) (_hT : sMinus < T)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ e ∂nu, sMinus < e.1.time) :
    let nu2 := nu.map (finiteUnionNestedPoleInclusion H1 H2 hsub T)
    let tau := finiteUnionRestartPoleMeasure A H1 H2 sMinus T nu
    finiteUnionGreenMixture A H2 T nu2 =
      finiteUnionGreenMixture A H1 T nu +
        finiteUnionGreenMixture A H2 T tau ∧
    finiteUnionExitMixture A H2 T nu2 =
      (finiteUnionExitMixture A H1 T nu).restrict
        (finiteUnionExitSet H2 sMinus T) +
        finiteUnionExitMixture A H2 T tau := enlarged_strip_nested A H1 H2 hsub sMinus T _hT nu (hnu.mono fun _ he => he.le)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
