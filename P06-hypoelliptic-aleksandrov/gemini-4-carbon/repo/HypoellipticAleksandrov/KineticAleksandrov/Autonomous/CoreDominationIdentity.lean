module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationRemainder
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationGreenRemainder

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter HypoellipticAleksandrov ProbabilityTheory
open scoped Topology

/-- Finite positive decompositions become an exact measure sum when remainder mass vanishes. -/
theorem measure_eq_sum_of_remainder_mass_tendsto_zero (mu : Measure Point)
    (piece remainder : ℕ → Measure Point)
    (hsplit : ∀ N, mu = ∑ n ∈ Finset.range N, piece n + remainder N)
    (hr : Tendsto (fun N => remainder N univ) atTop (𝓝 0)) :
    mu = Measure.sum piece := by
  ext B hB
  have hsum := (ENNReal.tendsto_nat_tsum (fun n => piece n B)).add (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr (fun _ => zero_le) (fun _ => measure_mono (subset_univ B)))
  have he (N : ℕ) : mu B = (∑ n ∈ Finset.range N, piece n B) + remainder N B := by
    rw [hsplit N, Measure.add_apply, Measure.finsetSum_apply]
  rw [Measure.sum_apply _ hB]
  simpa using tendsto_nhds_unique tendsto_const_nhds (hsum.congr (fun N => (he N).symm))


/-- Restriction distributes over every finite measure sum. -/
theorem visit_restrict_finset_sum (mu : ℕ → Measure Point) (N : ℕ) (B : Set Point) :
    (∑ n ∈ Finset.range N, mu n).restrict B = ∑ n ∈ Finset.range N, (mu n).restrict B :=
  map_sum (Measure.restrictₗ B) mu (Finset.range N)


/-- The actual outer core occupation is exactly the sum of its active visit occupations. -/
theorem visitOuterGreen_core_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    (visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P).restrict
      {q | q.velocity 0 ∈ c.core} =
    Measure.sum (fun n => (visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J)
      s T ∘ₘ visitEntrancePiece hH hLE hlam hLam A c J s T P n).restrict
        {q | q.velocity 0 ∈ c.core})  := by
  have visitOuterGreen_remainder_tendsto_zero :
      Tendsto (fun n => (visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ
      visitEntrancePiece hH hLE hlam hLam A c J s T P n) univ) atTop (𝓝 0) := by
    let := visitCount_isFiniteMeasure hH hLE hlam hLam A c J s T hT P hP
    exact visit_green_mixture_remainder_tendsto_zero hH hLE hlam hLam A J.toFiniteUnion s T _
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  let GW := visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
  let GO := visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T
  let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P
  let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P
  have hi : (visitInitialGreen P (visitEntranceInterval c) GW).restrict C = 0 := by
    classical
    unfold visitInitialGreen
    split
    · exact Measure.restrict_zero C
    · exact Measure.restrict_eq_zero.mpr
        (visitWaitingGreenKernel_core_zero hH hLE hlam hLam A c J s T P)
  have hw (n : ℕ) : (GW ∘ₘ beta n).restrict C = 0 :=
    Measure.restrict_eq_zero.mpr
      (visitWaitingGreenMixture_core_zero hH hLE hlam hLam A c J s T (beta n))
  apply measure_eq_sum_of_remainder_mass_tendsto_zero _ _
    (fun n => (GO ∘ₘ gamma n).restrict C)
  · intro N
    have h := congrArg (fun m => m.restrict C)
      (visitAlternating_green hH hLE hlam hLam A c J s T hT P hP N)
    change (GO P).restrict C =
      (visitInitialGreen P (visitEntranceInterval c) GW +
        ∑ n ∈ Finset.range N, ((visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T) ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N).restrict C at h
    simpa [Measure.restrict_add, visit_restrict_finset_sum, hi, hw] using h
  · have hz := visitOuterGreen_remainder_tendsto_zero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun _ => zero_le) (fun n => Measure.restrict_le_self univ)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

