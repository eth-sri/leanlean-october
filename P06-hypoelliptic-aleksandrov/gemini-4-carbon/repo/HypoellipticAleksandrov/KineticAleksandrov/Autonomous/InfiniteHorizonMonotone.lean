module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen

/-! # Actual domain monotonicity at finite and infinite horizons -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov


/-- Domain monotonicity survives the genuine increasing-limit construction of infinite Green. -/
theorem stripGreen_domain_mono_infinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (e : StripPole H1 ⊤) :
    stripGreen hH hLE hlam hLam A H1 ⊤ e ≤
      stripGreen hH hLE hlam hLam A H2 ⊤ (nestedPoleInclusion H1 H2 hsub ⊤ e)  := by
  have stripGreen_domain_mono_finite (T : ℝ) (e : StripPole H1 (T : WithTop ℝ)) :
      stripGreen hH hLE hlam hLam A H1 T e ≤
      stripGreen hH hLE hlam hLam A H2 T (nestedPoleInclusion H1 H2 hsub T e) := by
    have h := nestedIntervalGreen_identity hH hLE hlam hLam A H1 H2 hsub
      (e.1.time - 1) T e (by linarith)
    apply Measure.le_iff.mpr
    intro B _
    exact (congrArg (fun μ : Measure Point => μ B) h).symm ▸ le_add_right le_rfl
  rw [stripGreen_infinite_eq_iSup hH hLE hlam hLam A H1 e]
  apply iSup_le
  intro T
  apply iSup_le
  intro ht
  have hfinite : nestedPoleInclusion H1 H2 hsub T (stripPoleFinite H1 e T ht) =
      stripPoleFinite H2 (nestedPoleInclusion H1 H2 hsub ⊤ e) T ht := by
    apply Subtype.ext
    rfl
  exact (stripGreen_domain_mono_finite T (stripPoleFinite H1 e T ht)).trans ((congrArg (stripGreen hH hLE hlam hLam A H2 T) hfinite) ▸ (stripGreen_finite_restrict_infinite hH hLE hlam hLam A H2 (nestedPoleInclusion H1 H2 hsub ⊤ e) T ht).symm ▸ Measure.restrict_le_self)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
