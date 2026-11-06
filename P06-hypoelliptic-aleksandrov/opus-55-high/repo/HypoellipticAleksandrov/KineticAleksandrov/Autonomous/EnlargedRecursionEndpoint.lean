module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionPoint

/-! # Nested union identities retaining a pole at the lower observation time -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

variable (H1 H2 : FiniteIntervalUnion) (s T : ℝ) (mu : Measure Point)

/-- On the prescribed exit, lowering its time origin does not change an internal face. -/
theorem enlarged_internal_restrict_eq  (hmu : ∀ᵐ p ∂mu, p ∈ finiteUnionExitSet H1 s T) :
    mu.restrict (finiteUnionInternalExit H1 H2 (s - 1) T) =
      mu.restrict (finiteUnionInternalExit H1 H2 s T) := by
  apply Measure.restrict_congr_set
  filter_upwards [hmu] with p hp
  apply propext
  change (s - 1 < p.time ∧ p.time < T ∧
      p.velocity 0 ∈ frontier H1.carrier ∩ H2.carrier) ↔
    (s < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier H1.carrier ∩ H2.carrier)
  rcases hp with hp | hp
  · simp_all
  grind

/-- On a smaller prescribed exit, lowering time does not change the larger outer face. -/
theorem enlarged_outer_restrict_eq  (hmu : ∀ᵐ p ∂mu, p ∈ finiteUnionExitSet H1 s T) :
    mu.restrict (finiteUnionExitSet H2 (s - 1) T) =
      mu.restrict (finiteUnionExitSet H2 s T) := by
  apply Measure.restrict_congr_set
  filter_upwards [hmu] with p hp
  apply propext
  change (p.time = T ∧ p.velocity 0 ∈ closure H2.carrier ∨
      s - 1 < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier H2.carrier) ↔
    (p.time = T ∧ p.velocity 0 ∈ closure H2.carrier ∨
      s < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier H2.carrier)
  rcases hp with hp | hp
  · simp_all
  grind

/-- The literal nested union decomposition is valid also at the lower time endpoint. -/
theorem enlarged_nested_union_point
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) (he : s ≤ e.1.time) :
    finiteUnionGreen hH hLE hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      finiteUnionGreen hH hLE hlam hLam A H1 T e +
        (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T e).bind
          (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
    finiteUnionExit hH hLE hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict (finiteUnionExitSet H2 s T) +
        (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T e).bind
          (finiteUnionExit hH hLE hlam hLam A H2 T) := by
  have hs : s - 1 < e.1.time := by linarith
  have hm : ∀ᵐ p ∂finiteUnionExit hH hLE hlam hLam A H1 T e,
      p ∈ finiteUnionExitSet H1 s T := finiteUnionExit_compl_exit hH hLE hlam hLam A H1 s T e he
  have h := strip_nested_union_point hH hLE hlam hLam A H1 H2 hsub _ T e hs
  have hi : finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 (s - 1) T e =
      finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T e := by
    unfold finiteUnionPointRestartPoles
    rw [enlarged_internal_restrict_eq H1 H2 s T _ hm]
  rw [hi, enlarged_outer_restrict_eq H1 H2 s T _ hm] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
