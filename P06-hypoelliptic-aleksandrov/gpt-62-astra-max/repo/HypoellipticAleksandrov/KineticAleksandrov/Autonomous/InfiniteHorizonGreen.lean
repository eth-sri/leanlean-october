module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeOneSign

/-! # The exact infinite-horizon Green supremum and inherited quadratic bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (e : StripPole H ⊤) (T : ℝ) (hT : e.1.time < T)

include hT in
/-- Every infinite pole determines the same physical pole at any later finite terminal time. -/
def stripPoleFinite :
    StripPole H (T : WithTop ℝ) := ⟨e.1, WithTop.coe_lt_coe.mpr hT, e.2.2⟩

/-- Every finite terminal Green measure is the physical-time restriction of the infinite one. -/
theorem stripGreen_finite_restrict_infinite :
    stripGreen hlam hLam A H T (stripPoleFinite H e T hT) =
      (stripGreen hlam hLam A H ⊤ e).restrict {p | p.time < T} :=
  stripGreenOfKernel_horizonRestriction H _ T (stripPoleFinite H e T hT)

/-- The actual infinite Green measure is the supremum over all later finite terminal times. -/
theorem stripGreen_infinite_eq_iSup :
    stripGreen hlam hLam A H ⊤ e =
      ⨆ (T : ℝ) (hT : e.1.time < T),
        stripGreen hlam hLam A H T (stripPoleFinite H e T hT) := by
  apply le_antisymm
  · apply Measure.le_iff.mpr
    intro B hB
    let t (n : ℕ) : ℝ := e.1.time + n + 1
    let U (n : ℕ) : Set Point := {p | p.time < t n}
    have ht (n : ℕ) : e.1.time < t n := by
      grind
    have hm : Monotone (fun n => B ∩ U n) := by
      intro n m hnm p hp
      refine ⟨hp.1, ?_⟩
      have hn : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
      grind
    have hun : (⋃ n, B ∩ U n) = B := by
      ext p
      constructor
      · aesop
      · intro hp
        obtain ⟨n, hn⟩ := exists_nat_gt (p.time - e.1.time)
        apply mem_iUnion.mpr
        refine ⟨n, hp, ?_⟩
        grind
    conv_lhs => rw [← hun, hm.measure_iUnion]
    apply iSup_le
    intro n
    have heq := congrArg (fun μ : Measure Point => μ B) (stripGreen_finite_restrict_infinite hlam hLam A H e (t n) (ht n))
    rw [Measure.restrict_apply hB] at heq
    rw [← heq]
    have hle : stripGreen hlam hLam A H (t n)
        (stripPoleFinite H e (t n) (ht n)) ≤
          ⨆ (T : ℝ) (hT : e.1.time < T),
            stripGreen hlam hLam A H T (stripPoleFinite H e T hT) :=
      le_iSup_of_le (t n) (le_iSup_of_le (ht n) le_rfl)
    exact Measure.le_iff.mp hle B hB
  · apply iSup_le
    intro T
    apply iSup_le
    intro hT
    rw [stripGreen_finite_restrict_infinite hlam hLam A H e T hT]
    exact Measure.restrict_le_self

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
