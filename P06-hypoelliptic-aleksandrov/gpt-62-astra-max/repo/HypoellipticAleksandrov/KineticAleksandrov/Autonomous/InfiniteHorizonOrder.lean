module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonMonotone

/-! # Joint domain and horizon monotonicity for the actual Green family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H1 H2 : Interval) (hsub : H1.carrier ⊆ H2.carrier) (T1 T2 : WithTop ℝ) (hT : T1 ≤ T2)
    (e : StripPole H1 T1)

include hsub hT e in
/-- Enlarge the velocity carrier and terminal horizon without changing the physical pole. -/
def stripEnlargePole : StripPole H2 T2 :=
  ⟨e.1, e.2.1.trans_le hT, hsub e.2.2⟩

/-- The actual Green measure increases jointly with its domain and terminal horizon. -/
theorem stripGreen_mono :
    stripGreen hlam hLam A H1 T1 e ≤
      stripGreen hlam hLam A H2 T2 (stripEnlargePole H1 H2 hsub T1 T2 hT e) := by
  let ei : StripPole H1 ⊤ := ⟨e.1, WithTop.coe_lt_top _, e.2.2⟩
  have hd := stripGreen_domain_mono_infinite hlam hLam A H1 H2 hsub ei
  cases T1 with
  | top =>
    have he := top_le_iff.mp hT
    subst T2
    exact hd
  | coe t1 =>
    have ht1 := WithTop.coe_lt_coe.mp e.2.1
    have h1' := (congrArg (stripGreen hlam hLam A H1 t1) (Subtype.ext rfl)).symm.trans (stripGreen_finite_restrict_infinite hlam hLam A H1 ei t1 ht1)
    apply h1' ▸ le_trans (Measure.restrict_mono_measure hd _)
    cases T2 with
    | top => exact Measure.restrict_le_self
    | coe t2 =>
      have ht12 := WithTop.coe_le_coe.mp hT
      have ht2 := ht1.trans_le ht12
      have h2' :=
        (congrArg (stripGreen hlam hLam A H2 t2) (Subtype.ext rfl)).symm.trans (stripGreen_finite_restrict_infinite hlam hLam A H2 (nestedPoleInclusion H1 H2 hsub ⊤ ei) t2 ht2)
      exact h2'.symm ▸ Measure.restrict_mono_set _ (fun p hp => hp.trans_le ht12)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
