module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsBorel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsNesting

/-! # Actual Green and exit mixtures with the restored strict source support condition -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion)
include lam Lam A

/-- The componentwise union Green mixture is the actual measurable measure integral. -/
def finiteUnionGreenMixture (T : WithTop ℝ)
    (nu : Measure (FiniteUnionPole H T)) : Measure Point :=
  nu.bind (finiteUnionGreen A H T)

section
variable (T : ℝ) (nu : Measure (FiniteUnionPole H (T : WithTop ℝ)))
include T nu

/-- The componentwise union exit mixture is the same measurable integral of actual exits. -/
def finiteUnionExitMixture : Measure Point :=
  nu.bind (finiteUnionExit A H T)

/-- Union exit mixtures preserve the total mass of their finite source measure. -/
theorem finiteUnionExitMixture_mass :
    finiteUnionExitMixture A H T nu univ = nu univ := by
  unfold finiteUnionExitMixture
  rw [Measure.bind_apply MeasurableSet.univ
    (finiteUnionExit_measurable A H T).aemeasurable]
  simp only [measure_univ, lintegral_const, one_mul]

end

end

/-- A finite source gives a finite actual union exit mixture. -/
instance finiteUnionExitMixture_isFiniteMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (nu : Measure (FiniteUnionPole H (T : WithTop ℝ))) [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionExitMixture A H T nu) :=
  ⟨by rw [finiteUnionExitMixture_mass]; exact measure_lt_top _ _⟩

/-- With the source support restored, the whole exit mixture sits on the prescribed exit. -/
theorem finiteUnionExitMixture_compl_exit
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H (T : WithTop ℝ)))
    (hnu : ∀ᵐ e ∂nu, sMinus < e.1.time) :
    finiteUnionExitMixture A H T nu (finiteUnionExitSet H sMinus T)ᶜ = 0 := by
  unfold finiteUnionExitMixture
  rw [Measure.bind_apply
    (measurableSet_finiteUnionExitSet H sMinus T).compl
    (finiteUnionExit_measurable A H T).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hnu] with e he
  exact finiteUnionExit_compl_exit A H sMinus T e he.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
