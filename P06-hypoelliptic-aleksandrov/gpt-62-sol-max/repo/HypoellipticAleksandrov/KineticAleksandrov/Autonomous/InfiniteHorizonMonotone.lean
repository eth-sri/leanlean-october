module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen

/-! # Actual domain monotonicity at finite and infinite horizons -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
  (hsub : H1.carrier ⊆ H2.carrier)

/-- The actual finite Green measure increases when the velocity interval is enlarged. -/
theorem stripGreen_domain_mono_finite (T : ℝ) (e : StripPole H1 (T : WithTop ℝ)) :
    stripGreen A H1 T e ≤
      stripGreen A H2 T (nestedPoleInclusion H1 H2 hsub T e) := by
  have h := nestedIntervalGreen_identity A H1 H2 hsub
    (e.1.time - 1) T e (by linarith)
  apply Measure.le_iff.mpr
  intro B _
  have hh := congrArg (fun μ : Measure Point => μ B) h
  exact hh.symm ▸ le_add_right le_rfl

/-- Domain monotonicity survives the genuine increasing-limit construction of infinite Green. -/
theorem stripGreen_domain_mono_infinite (e : StripPole H1 ⊤) :
    stripGreen A H1 ⊤ e ≤
      stripGreen A H2 ⊤ (nestedPoleInclusion H1 H2 hsub ⊤ e) := by
  rw [stripGreen_infinite_eq_iSup A H1 e]
  apply iSup_le
  intro T
  apply iSup_le
  intro ht
  have h := stripGreen_domain_mono_finite A H1 H2 hsub T
    (stripPoleFinite H1 e T ht)
  have hfinite : nestedPoleInclusion H1 H2 hsub T (stripPoleFinite H1 e T ht) =
      stripPoleFinite H2 (nestedPoleInclusion H1 H2 hsub ⊤ e) T ht := by
    apply Subtype.ext
    rfl
  have hinc := stripGreen_finite_restrict_infinite A H2
    (nestedPoleInclusion H1 H2 hsub ⊤ e) T ht
  exact h.trans ((congrArg (stripGreen A H2 T) hfinite) ▸ hinc.symm ▸ Measure.restrict_le_self)

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
