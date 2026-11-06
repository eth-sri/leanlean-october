module

public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Sobolev.W1p.RepresentativeGraph

/-!
# Closure of representative weak gradients under `L^p` convergence

This file exposes the closed-graph limit principle behind Sobolev
composition and truncation arguments.  If values and every native gradient
coordinate converge in `L^p`, then a limit of weak-gradient pairs is again a
weak-gradient pair.

The proof passes through the quotient `L^p` closed graph.  The native gradient
is lifted internally to `HilbertVec`; the public assumptions and conclusion
remain on `Vec d`, and coordinatewise convergence is converted to the exact
Euclidean-gradient norm without a dimension-dependent loss.
-/

 public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- Weak gradients are closed under value and coordinatewise gradient
convergence in `L^p`, for every exponent `p ≥ 1`. -/
theorem HasWeakGradientOn.of_tendsto_eLpNorm
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {uSeq : ℕ → Vec d → ℝ}
    {DuSeq : ℕ → Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (huSeq : ∀ n, MemLpOn U p (uSeq n))
    (hDuSeq : ∀ n, GradMemLpOn U p (DuSeq n))
    (hweak :
      ∀ n, HasWeakGradientOn U (uSeq n) (DuSeq n))
    (hValue :
      Tendsto
        (fun n =>
          eLpNorm (uSeq n - u) p (volumeOn U))
        atTop (𝓝 0))
    (hGradient :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => DuSeq n x i - Du x i)
              p (volumeOn U))
          atTop (𝓝 0)) :
    HasWeakGradientOn U u Du := (hasWeakGradientOn_of_weakGradientLpPairOfRepresentatives_mem hu hDu
  (IsClosed.mem_of_tendsto (ClosedSubmodule.isClosed (weakGradientGraph U p))
    (id
      (Tendsto.prodMk_nhds ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' uSeq huSeq u hu).mpr hValue)
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => toHilbertVecField (DuSeq n))
              (fun n => gradMemLpOn_iff_memLp_toHilbertVecField.mp (hDuSeq n)) (toHilbertVecField Du)
              (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu)).mpr
          (Eq.mpr
            (id
              (congrFun'
                (congrFun'
                  (congrArg Tendsto
                    (funext fun n =>
                      Eq.trans
                        (congrFun'
                          (congrFun'
                            (congrArg
                              (@eLpNorm (Vec d) (HilbertVec d) SeminormedAddGroup.toContinuousENorm.toENorm
                                (PiLp.topologicalSpace 2 fun x => ℝ) MeasureSpace.pi.toMeasurableSpace)
                              (toHilbertVecField_sub (DuSeq n) Du))
                            p)
                          (volumeOn U))
                        ((fun n =>
                            eLpNorm_toHilbertVecField_eq (volumeOn U) p (fun x => DuSeq n x - Du x)
                              (AEMeasurable.aestronglyMeasurable
                                (aemeasurable_pi_iff.mpr fun i =>
                                  AEStronglyMeasurable.aemeasurable
                                    (AEStronglyMeasurable.sub (MemLp.aestronglyMeasurable (hDuSeq n i))
                                      (MemLp.aestronglyMeasurable (hDu i))))))
                          n)))
                  atTop)
                (𝓝 0)))
            (tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate Fact.out
              (fun n i =>
                AEStronglyMeasurable.sub (MemLp.aestronglyMeasurable (hDuSeq n i)) (MemLp.aestronglyMeasurable (hDu i)))
              hGradient)))))
    (Eventually.of_forall fun n =>
      weakGradientLpPairOfRepresentatives_mem_weakGradientGraph (huSeq n) (hDuSeq n) (hweak n))))

end PDE
