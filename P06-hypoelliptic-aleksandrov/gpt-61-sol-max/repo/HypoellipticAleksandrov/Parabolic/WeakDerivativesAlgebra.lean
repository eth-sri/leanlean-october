module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.SolveByElim
import all HypoellipticAleksandrov.Parabolic.CrossVelocityWeakDerivativeCommutation
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
section
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
private alias _semanticProof_77a760a65596 := HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset
end


/-!
# Raw algebra for parabolic weak derivatives

This module records coefficient-free algebraic closure properties of the raw
time and velocity weak-derivative predicates.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

private theorem integrable_restrict_mul_of_locallyIntegrableOn
     {U : HypoellipticAleksandrov.Parabolic.Region d} {f g : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : LocallyIntegrableOn f U ) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSub : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) (timeVelocityVolumeOn U) := (Integrable.restrict
  ((integrableOn_iff_integrable_of_support_subset fun ⦃z⦄ hz => tsupport_mul_subset_right (subset_closure hz)).mp
    (IntegrableOn.smul_continuousOn
      (LocallyIntegrableOn.integrableOn_compact_subset hf hgSub (HasCompactSupport.isCompact hgCompact))
      (Continuous.continuousOn hg) (HasCompactSupport.isCompact hgCompact))))

variable {f : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem timeDerivative_continuous
    (hf : ContDiff ℝ PDE.smoothOrder f) : Continuous (timeDerivative f) := by
  unfold timeDerivative
  simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem timeDerivative_compact
    (hf : HasCompactSupport f) : HasCompactSupport (timeDerivative f) := (id (HasCompactSupport.fderiv_apply ℝ hf (1, 0)))

private theorem timeDerivative_tsupport  (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  change closure (Function.support (fun z => fderiv ℝ f z (1, 0))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

variable {f : HypoellipticAleksandrov.Parabolic.ScalarField d} {i : Fin d}

private theorem velocityGradient_continuous
    (hf : ContDiff ℝ PDE.smoothOrder f) : Continuous (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const



private theorem velocityGradient_tsupport  {i : Fin d} (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := _semanticProof_77a760a65596

namespace HasWeakTimeDerivOn

/-- Zero has zero weak time derivative. -/
theorem zero {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} :
    HasWeakTimeDerivOn U (0 ) 0 := by
  intro φ hφ hφCompact hφSub
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]

variable {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}

/-- Weak time differentiation commutes with constant scalar multiplication. -/
theorem smul
    {u du : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakTimeDerivOn U u du) (c : ℝ) :
    HasWeakTimeDerivOn U (c • u) (c • du) := by
  intro φ hφ hφCompact hφSub
  calc
    (∫ z in U, (c • u) z * timeDerivative φ z) =
        c * ∫ z in U, u z * timeDerivative φ z := by
      rw [show (fun z => (c • u) z * timeDerivative φ z) =
          fun z => c * (u z * timeDerivative φ z) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
    _ = c * (-(∫ z in U, du z * φ z)) := by
      rw [hu φ hφ hφCompact hφSub]
    _ = -∫ z in U, (c • du) z * φ z := by
      rw [show (fun z => (c • du) z * φ z) = fun z => c * (du z * φ z) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
      ring

/-- Raw weak time derivatives are additive when all representatives are
locally integrable. -/
theorem add
    {u du v dv : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U v dv)
    (huLoc : LocallyIntegrableOn u U )
    (hduLoc : LocallyIntegrableOn du U )
    (hvLoc : LocallyIntegrableOn v U )
    (hdvLoc : LocallyIntegrableOn dv U ) :
    HasWeakTimeDerivOn U (fun z => u z + v z) (fun z => du z + dv z) := by
  intro φ hφ hφCompact hφSub
  let μU  := timeVelocityVolumeOn U
  let dφ  := timeDerivative φ
  have hφCont  := hφ.continuous
  have hdφCont  := timeDerivative_continuous hφ
  have hdφCompact  := timeDerivative_compact hφCompact
  have hdφSub  := timeDerivative_tsupport φ |>.trans hφSub




  change (∫ z, (u z + v z) * dφ z ∂μU) =
    -∫ z, (du z + dv z) * φ z ∂μU
  calc
    (∫ z, (u z + v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) + ∫ z, v z * dφ z ∂μU := by
      rw [← integral_add (integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub) (integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU + -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        exact hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        exact hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU + ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z + dv z) * φ z ∂μU := by
      rw [← integral_add (integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub) (integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub)]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

/-- Weak time differentiation commutes with finite sums when every value and
derivative representative is locally integrable. -/
theorem fin_sum
    {d n : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {u du : Fin n → HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : ∀ j, HasWeakTimeDerivOn U (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U )
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U ) :
    HasWeakTimeDerivOn U
      (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  let sharedTerm_9015f2e621 := ((locallyIntegrableOn_zero (X := TimeVelocity d) (s := U) (μ := volume) (ε'' := ℝ)))
  classical
  have huSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, u j z) U  := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        sharedTerm_9015f2e621
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (huLoc j).add ih
  have hduSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, du j z) U  := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        sharedTerm_9015f2e621
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (hduLoc j).add ih

  exact (show ∀ s : Finset (Fin n),
      HasWeakTimeDerivOn U
        (fun z => ∑ j ∈ s, u j z) (fun z => ∑ j ∈ s, du j z) by
      intro s
      induction s using Finset.induction_on with
      | empty => solve_by_elim (maxDepth := 4) [@_root_.HypoellipticAleksandrov.Parabolic.HasWeakTimeDerivOn.zero]
      | @insert j s hj ih =>
          simp_all [HasWeakTimeDerivOn.add]) Finset.univ

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Zero has zero weak velocity derivative. -/
theorem zero {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d} :
    HasWeakVelocityPartialDerivOn U i (0 ) 0 := by
  intro φ hφ hφCompact hφSub
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]

variable {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}

/-- Weak velocity differentiation commutes with constant scalar multiplication. -/
theorem smul
    {u dui : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) (c : ℝ) :
    HasWeakVelocityPartialDerivOn U i (c • u) (c • dui) := by
  intro φ hφ hφCompact hφSub
  calc
    (∫ z in U, (c • u) z * velocityGradient φ z i) =
        c * ∫ z in U, u z * velocityGradient φ z i := by
      rw [show (fun z => (c • u) z * velocityGradient φ z i) =
          fun z => c * (u z * velocityGradient φ z i) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
    _ = c * (-(∫ z in U, dui z * φ z)) := by
      rw [hu φ hφ hφCompact hφSub]
    _ = -∫ z in U, (c • dui) z * φ z := by
      rw [show (fun z => (c • dui) z * φ z) = fun z => c * (dui z * φ z) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
      ring

section
variable {u du v dv : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : HasWeakVelocityPartialDerivOn U i u du) (hv : HasWeakVelocityPartialDerivOn U i v dv) (huLoc : LocallyIntegrableOn u U volume) (hduLoc : LocallyIntegrableOn du U volume) (hvLoc : LocallyIntegrableOn v U volume) (hdvLoc : LocallyIntegrableOn dv U volume)

include hu hv huLoc hduLoc hvLoc hdvLoc
/-- Raw weak velocity derivatives are additive when all representatives are
locally integrable. -/
theorem add
     :
    HasWeakVelocityPartialDerivOn U i (fun z => u z + v z) (fun z => du z + dv z) := by
  intro φ hφ hφCompact hφSub
  let μU  := timeVelocityVolumeOn U
  let dφ  := fun z => velocityGradient φ z i
  have hφCont  := hφ.continuous
  have hdφCont : Continuous dφ := velocityGradient_continuous hφ
  have hdφCompact : HasCompactSupport dφ := _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hφCompact
  have hdφSub : tsupport dφ ⊆ U := velocityGradient_tsupport φ |>.trans hφSub




  change (∫ z, (u z + v z) * dφ z ∂μU) =
    -∫ z, (du z + dv z) * φ z ∂μU
  calc
    (∫ z, (u z + v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) + ∫ z, v z * dφ z ∂μU := by
      rw [← integral_add (integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub) (integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU + -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        exact hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        exact hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU + ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z + dv z) * φ z ∂μU := by
      rw [← integral_add (integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub) (integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub)]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

/-- Raw weak velocity derivatives commute with subtraction when all
representatives are locally integrable. -/
theorem sub
     :
    HasWeakVelocityPartialDerivOn U i
      (fun z => u z - v z) (fun z => du z - dv z) := by
  intro φ hφ hφCompact hφSub
  let μU  := timeVelocityVolumeOn U
  let dφ  := fun z => velocityGradient φ z i
  have hφCont  := hφ.continuous
  have hdφCont : Continuous dφ := velocityGradient_continuous hφ
  have hdφCompact : HasCompactSupport dφ := _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hφCompact
  have hdφSub : tsupport dφ ⊆ U := velocityGradient_tsupport φ |>.trans hφSub




  change (∫ z, (u z - v z) * dφ z ∂μU) =
    -∫ z, (du z - dv z) * φ z ∂μU
  calc
    (∫ z, (u z - v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) - ∫ z, v z * dφ z ∂μU := by
      rw [← integral_sub (integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub) (integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU - -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        exact hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        exact hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU - ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z - dv z) * φ z ∂μU := by
      rw [← integral_sub (integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub) (integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub)]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
end


/-- Weak velocity differentiation commutes with finite sums when every value
and derivative representative is locally integrable. -/
theorem fin_sum
    {d n : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {i : Fin d}
    {u du : Fin n → HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hu : ∀ j, HasWeakVelocityPartialDerivOn U i (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U )
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U ) :
    HasWeakVelocityPartialDerivOn U i
      (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  let sharedTerm_2e9b192fe7 := ((locallyIntegrableOn_zero (X := TimeVelocity d) (s := U) (μ := volume) (ε'' := ℝ)))
  classical
  have huSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, u j z) U  := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        sharedTerm_2e9b192fe7
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (huLoc j).add ih
  have hduSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, du j z) U  := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        sharedTerm_2e9b192fe7
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (hduLoc j).add ih

  exact (show ∀ s : Finset (Fin n),
      HasWeakVelocityPartialDerivOn U i
        (fun z => ∑ j ∈ s, u j z) (fun z => ∑ j ∈ s, du j z) by
      intro s
      induction s using Finset.induction_on with
      | empty => solve_by_elim (maxDepth := 4) [@_root_.HypoellipticAleksandrov.Parabolic.HasWeakVelocityPartialDerivOn.zero]
      | @insert j s hj ih =>
          simp_all [HasWeakVelocityPartialDerivOn.add]) Finset.univ

end HasWeakVelocityPartialDerivOn

end HypoellipticAleksandrov.Parabolic
