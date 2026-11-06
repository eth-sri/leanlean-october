module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonMonotone
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeOneSign
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen

/-! # Joint domain and horizon monotonicity for the actual Green family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- Enlarge the velocity carrier and terminal horizon without changing the physical pole. -/
def stripEnlargePole (H1 H2 : Interval) (hsub : H1.carrier ⊆ H2.carrier)
    (T1 T2 ) (hT : T1 ≤ T2) (e : StripPole H1 T1) : StripPole H2 T2 :=
  ⟨e.1, e.2.1.trans_le hT, hsub e.2.2⟩

/- The actual Green measure increases jointly with its domain and terminal horizon. -/
theorem stripGreen_mono
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (T1 T2 : WithTop ℝ) (hT : T1 ≤ T2)
    (e : StripPole H1 T1) :
    stripGreen hH hLE hlam hLam A H1 T1 e ≤
      stripGreen hH hLE hlam hLam A H2 T2 (stripEnlargePole H1 H2 hsub T1 T2 hT e) := by
  let ei : StripPole H1 ⊤ := ⟨e.1, WithTop.coe_lt_top _, e.2.2⟩
  have hd : stripGreen hH hLE hlam hLam A H1 ⊤ ei ≤
      stripGreen hH hLE hlam hLam A H2 ⊤ (nestedPoleInclusion H1 H2 hsub ⊤ ei) := by
    have _h_xinl_0 : stripGreen hH hLE hlam hLam A H1 ⊤ ei =
        ⨆ (T : ℝ) (hT : ei.1.time < T),
          stripGreen hH hLE hlam hLam A H1 T (stripPoleFinite H1 ei T hT) := by
      apply le_antisymm
      · apply Measure.le_iff.mpr
        intro B hB
        let t (n : ℕ) : ℝ := ei.1.time + (n : ℝ) + 1
        let U (n : ℕ) : Set Point := {p | p.time < t n}
        have ht (n : ℕ) : ei.1.time < t n := by
          dsimp only [t]
          linarith [Nat.cast_nonneg (α := ℝ) n]
        have hm : Monotone (fun n => B ∩ U n) := by
          intro n m hnm p hp
          refine ⟨hp.1, ?_⟩
          have hn : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
          have hp' : p.time < ei.1.time + (n : ℝ) + 1 := hp.2
          change p.time < ei.1.time + (m : ℝ) + 1
          linarith
        have hun : (⋃ n, B ∩ U n) = B := by
          ext p
          constructor
          · intro hp
            obtain ⟨n, hn⟩ := mem_iUnion.mp hp
            exact hn.1
          · intro hp
            obtain ⟨n, hn⟩ := exists_nat_gt (p.time - ei.1.time)
            apply mem_iUnion.mpr
            refine ⟨n, hp, ?_⟩
            change p.time < ei.1.time + (n : ℝ) + 1
            linarith
        conv_lhs => rw [← hun, hm.measure_iUnion]
        apply iSup_le
        intro n
        have hr := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H1 ei (t n) (ht n)
        have heq := congrArg (fun μ : Measure Point => μ B) hr
        rw [Measure.restrict_apply hB] at heq
        rw [← heq]
        have hle : stripGreen hH hLE hlam hLam A H1 (t n)
            (stripPoleFinite H1 ei (t n) (ht n)) ≤
              ⨆ (T : ℝ) (hT : ei.1.time < T),
                stripGreen hH hLE hlam hLam A H1 T (stripPoleFinite H1 ei T hT) :=
          le_iSup_of_le (t n) (le_iSup_of_le (ht n) le_rfl)
        exact Measure.le_iff.mp hle B hB
      · apply iSup_le
        intro T
        apply iSup_le
        intro hT
        rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A H1 ei T hT]
        exact Measure.restrict_le_self
    rw [_h_xinl_0]
    apply iSup_le
    intro T
    apply iSup_le
    intro ht
    have h : stripGreen hH hLE hlam hLam A H1 T (stripPoleFinite H1 ei T ht) ≤
      stripGreen hH hLE hlam hLam A H2 T (nestedPoleInclusion H1 H2 hsub T (stripPoleFinite H1 ei T ht)) := by
      let e := (stripPoleFinite H1 ei T ht)
      have h := nestedIntervalGreen_identity hH hLE hlam hLam A H1 H2 hsub
        (e.1.time - 1) T e (by linarith)
      apply Measure.le_iff.mpr
      intro B _
      have hh := congrArg (fun μ : Measure Point => μ B) h
      exact hh.symm ▸ le_add_right le_rfl
    have hfinite : nestedPoleInclusion H1 H2 hsub T (stripPoleFinite H1 ei T ht) =
        stripPoleFinite H2 (nestedPoleInclusion H1 H2 hsub ⊤ ei) T ht := by
      apply Subtype.ext
      rfl
    have hinc := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H2
      (nestedPoleInclusion H1 H2 hsub ⊤ ei) T ht
    have heq := congrArg (stripGreen hH hLE hlam hLam A H2 T) hfinite
    exact h.trans (heq ▸ hinc.symm ▸ Measure.restrict_le_self)
  cases T1 with
  | top =>
    have he : T2 = ⊤ := top_le_iff.mp hT
    subst T2
    exact hd
  | coe t1 =>
    have ht1 : e.1.time < t1 := WithTop.coe_lt_coe.mp e.2.1
    have h1 := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H1 ei t1 ht1
    have hp1 : stripPoleFinite H1 ei t1 ht1 = e := Subtype.ext rfl
    apply ((congrArg (stripGreen hH hLE hlam hLam A H1 t1) hp1).symm.trans h1) ▸ le_trans (Measure.restrict_mono_measure hd _)
    cases T2 with
    | top => exact Measure.restrict_le_self
    | coe t2 =>
      have ht12 : t1 ≤ t2 := WithTop.coe_le_coe.mp hT
      have ht2 := ht1.trans_le ht12
      have h2 := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H2
        (nestedPoleInclusion H1 H2 hsub ⊤ ei) t2 ht2
      have hp2 : stripPoleFinite H2 (nestedPoleInclusion H1 H2 hsub ⊤ ei) t2 ht2 =
          stripEnlargePole H1 H2 hsub t1 t2 hT e := Subtype.ext rfl
      exact ((congrArg (stripGreen hH hLE hlam hLam A H2 t2) hp2).symm.trans h2).symm ▸ Measure.restrict_mono_set _ (fun p hp => hp.trans_le ht12)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
