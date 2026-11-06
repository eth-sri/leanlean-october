module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsBorel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsNesting

/-! # Actual Green and exit mixtures with the restored strict source support condition -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory


variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion)

/-- The componentwise union Green mixture is the actual measurable measure integral. -/
def finiteUnionGreenMixture
     (T : WithTop ℝ)
    (nu : Measure (FiniteUnionPole H T)) : Measure Point :=
  nu.bind (finiteUnionGreen hH hLE hlam hLam A H T)

variable (T : ℝ) (nu : Measure (FiniteUnionPole H (T : WithTop ℝ)))

/-- The componentwise union exit mixture is the same measurable integral of actual exits. -/
def finiteUnionExitMixture
      : Measure Point :=
  nu.bind (finiteUnionExit hH hLE hlam hLam A H T)





/-- With the source support restored, the whole exit mixture sits on the prescribed exit. -/
theorem finiteUnionExitMixture_compl_exit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H (T : WithTop ℝ)))
    (hnu : ∀ᵐ e ∂nu, sMinus < e.1.time) :
    finiteUnionExitMixture hH hLE hlam hLam A H T nu (finiteUnionExitSet H sMinus T)ᶜ = 0 := by
  unfold finiteUnionExitMixture
  rw [Measure.bind_apply
    (measurableSet_finiteUnionExitSet H sMinus T).compl
    (finiteUnionExit_measurable hH hLE hlam hLam A H T).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hnu] with e he
  exact finiteUnionExit_compl_exit hH hLE hlam hLam A H sMinus T e he.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
