module

public import QPBT.Combining.Lines
public import QPBT.Combining.OrderedPoints
public import QPBT.Combining.OverlapGap
public import QPBT.Combining.Points.Placement

/-!
# Marginal deficits of the evaluated pair-line measurement

Closeness to the ordered product of the two expanded point measurements controls
its overlap with the first basis. The distance bound needs only that the joint
point marginal is uniform, and applies to both restricted and extended line laws.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Completed point pairs -/

/-- A sum over completed outcome pairs of a function vanishing on both `none`
classes is the sum over the uncompleted pairs. -/
theorem sum_option_prod_eq_of_none {β γ : Type*} [Fintype β] [Fintype γ]
    (F : Option β × Option γ → ℝ) (h1 : ∀ o2, F (none, o2) = 0)
    (h2 : ∀ o1, F (o1, none) = 0) :
    (∑ o, F o) = ∑ bc : β × γ, F (some bc.1, some bc.2) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_option, h1, h2, Finset.sum_const_zero, zero_add]

section

variable {β γ d : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] [Fintype d] [DecidableEq d]
    (Q : Measurement (β × γ) d)
include β γ d Q

/-- The completed joint measurement has the joint effect on a pair of
evaluations. -/
theorem completedPair_effect_some (bc : β × γ) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect (some bc.1, some bc.2) =
      Q.effect bc :=
  SandwichProduct.postprocess_effect_of_injective Q _ (by intro a b h; simpa [Prod.ext_iff] using h) bc

/-- The completed joint measurement vanishes on outcomes outside the image of
the completion. -/
theorem completedPair_effect_eq_zero (o : Option β × Option γ)
    (ho : ∀ bc : β × γ, (some bc.1, some bc.2) ≠ o) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect o = 0 :=
  SandwichProduct.postprocess_effect_eq_zero_of_notMem Q _ (fun ⟨bc, hbc⟩ => ho bc hbc)

/-- The completion of a projective joint measurement is projective. -/
theorem completedPair_isProjective (hQ : Measurement.IsProjective Q) :
    Measurement.IsProjective (Q.postprocess fun ab => (some ab.1, some ab.2)) :=
  SandwichProduct.postprocess_isProjective Q hQ _

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

section

variable (S : ProjectiveSetting P ε)
include S

/-- A placed projection is a projection. -/
theorem place_isProj (p : Placement)
    {E : Op (S.ExpandedLocalSpace p.side)} (hE : IsProj E) :
    IsProj (S.place p E) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p E * S.place p E = S.place p E
    rw [← place_mul, hE.isIdempotentElem.eq]
  · rw [Matrix.star_eq_conjTranspose, ← place_conjTranspose,
      hE.isSelfAdjoint.isHermitian.eq]

/-- Every effect of the completed expanded point measurement is a projection,
the `none` effect being zero. -/
theorem pointMeasExpOption_isProj
    (side : PlayerSide) (W : PauliKind) (u : PauliPoint P)
    (o : Option (PauliScalar P)) :
    IsProj ((S.pointMeasExpOption side W u).effect o) :=
  SandwichProduct.postprocess_isProjective _ (S.pointMeasExp_isProjective side W u) some o

/-- The completed joint point measurement and a completed point product differ
only on outcome pairs with two evaluations, so their placed state-dependent
squared distance is the one of the joint point measurement and the point
product.  Blueprint `ch15_qpbt_combining.tex:2651-2698`. -/
theorem sum_norm_place_completedPair_sub_sq
    (p : Placement)
    (Q : Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p.side))
    (Gc : Option (PauliScalar P) × Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace p.side))
    (G : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace p.side))
    (hsome : ∀ ab : PauliScalar P × PauliScalar P, Gc (some ab.1, some ab.2) = G ab)
    (hnone1 : ∀ o2, Gc (none, o2) = 0) (hnone2 : ∀ o1, Gc (o1, none) = 0) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        ‖applyOperatorToState
          (S.place p ((Q.postprocess fun ab => (some ab.1, some ab.2)).effect o) -
            S.place p (Gc o)) S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState (S.place p (Q.effect ab) - S.place p (G ab))
          S.psiHat‖ ^ 2 := by
  refine Eq.trans (sum_option_prod_eq_of_none _ ?_ ?_) (Finset.sum_congr rfl fun ab _ => ?_)
  · intro o
    rw [completedPair_effect_eq_zero Q (none, o) (fun _ => by simp), hnone1, place_zero, sub_self]
    simp [applyOperatorToState]
  · intro o
    rw [completedPair_effect_eq_zero Q (o, none) (fun _ => by simp), hnone2, place_zero, sub_self]
    simp [applyOperatorToState]
  · rw [completedPair_effect_some, hsome]

/-- Read the component of a completed point pair in the chosen basis. -/
abbrev completedPointPairEffect (side : PlayerSide) (W : PauliKind)
    (xz : PointPair P)
    (o : Option (PauliScalar P) × Option (PauliScalar P)) :=
  (S.pointMeasExpOption side W (W.component xz)).effect (W.component o)

end

end ProjectiveSetting

/-! ## The abstract one-point deficit -/

/-- Agreement with `Q` and proximity to `T = R T` force agreement with `R`.
The three overlap comparisons insert `Q`, replace `Q` by `T`, and remove `R`
from `R T`. This is the common argument of `lem:claim-17-2` and `lem:claim-17-3`. -/
theorem one_sub_overlap_le_of_consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A Q : X → Measurement α ι) (R T : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hQ : ∀ x, Measurement.IsProjective (Q x)) (hR : ∀ x a, IsProj (R x a))
    (hAQ : ∀ x a, Commute ((A x).effect a) ((Q x).effect a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hRT : ∀ x a, R x a * T x a = T x a)
    (η ζ : ℝ)
    (hcons : measurementDefect μ A
      Q ψ ≤ η)
    (hdist : opFamilyDistSq μ (fun x a => (Q x).effect a)
      T ψ ≤ ζ) :
    1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a)) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  let Qe := fun x a => (Q x).effect a
  let L := fun B : X → α → Op ι => avgOver μ (fun x =>
    ∑ a, stateQForm ψ ((A x).effect a * B x a))
  have hsub (B C : X → α → Op ι) : L B - L C = L (fun x a => B x a - C x a) := by
    simp only [L, mul_sub, stateQForm_sub, Finset.sum_sub_distrib, avgOver_sub]
  have h1 : 1 - L Qe ≤ η := by
    rw [show 1 - L Qe = measurementDefect μ A Q ψ from
      (consistencyDefect_eq_one_sub_overlap μ A Q ψ hμ hψ).symm]
    exact hcons
  have h1' : 1 - L Qe ≤ Real.sqrt η := by
    have hn : 0 ≤ L Qe := avgOver_nonneg μ _ fun x => Finset.sum_nonneg fun a _ => by
      rw [← stateQForm_applyOperatorToState_eq_of_isProj ψ (hQ x a) (hAQ x a)]
      exact stateQForm_nonneg _ ((A x).pos a)
    have hu : L Qe ≤ 1 := avgOver_sum_stateQForm_mul_le_one μ A Qe ψ hμ hψ
      (fun x a => hQ x a) hAQ
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 : |L Qe - L T| ≤ Real.sqrt ζ :=
    abs_overlap_gap_le_sqrt_of_opFamilyDistSq μ A Qe T ψ hμ hψ ζ hdist
  have h4 : |L (fun x a => R x a * Qe x a) - L T| ≤ Real.sqrt ζ := by
    rw [hsub, show (fun x a => R x a * Qe x a - T x a) =
        (fun x a => R x a * (Qe x a - T x a)) by ext x a; rw [mul_sub, hRT]]
    exact (abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj μ A R
      (fun x a => Qe x a - T x a) ψ hμ hψ hR hAR).trans (Real.sqrt_le_sqrt hdist)
  have h5 : |L (fun x a => R x a * Qe x a) - L R| ≤ Real.sqrt η :=
    (abs_overlap_gap_le_sqrt_one_sub_of_isProj μ A Qe R ψ hμ hψ
      (fun x a => hQ x a) hR hAQ hAR).trans (Real.sqrt_le_sqrt h1)
  change 1 - L R ≤ _
  linarith [(abs_le.mp h2).2, (abs_le.mp h4).1, (abs_le.mp h5).2]

/-! ## The two placed deficits -/

section Placed

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- On opposite placements, closeness to an ordered product controls the
marginal overlap with its first (projective) factor. -/
theorem one_sub_placed_overlap_le_of_product_distance {Y α : Type*}
    [Fintype Y] [DecidableEq Y] [Fintype α] [DecidableEq α]
    (first second : Placement) (hopp : first.IsOpposite second)
    (ν : Distribution Y) (hν : ν.IsProbability) (η ζ : ℝ)
    (A : Y → Measurement α (S.ExpandedLocalSpace first.side))
    (Q : Y → Measurement α (S.ExpandedLocalSpace second.side))
    (R T : Y → α → Op (S.ExpandedLocalSpace second.side))
    (hQ : ∀ x, Measurement.IsProjective (Q x))
    (hR : ∀ x a, IsProj (R x a))
    (hcons : S.placedDefect first second ν (fun x => A x) (fun x => Q x) ≤ η)
    (hdist : opFamilyDistSq ν (fun x a => S.place second ((Q x).effect a))
      (fun x a => S.place second (R x a * T x a)) S.psiHat ≤ ζ) :
    1 - avgOver ν (fun x => ∑ a,
      S.placedCorrelation first second ((A x).effect a) (R x a)) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  refine one_sub_overlap_le_of_consistencyDefect ν
    (fun x => S.placedMeasurement first (A x)) (fun x => S.placedMeasurement second (Q x))
    (fun x a => S.place second (R x a)) (fun x a => S.place second (R x a * T x a))
    S.psiHat hν S.psiHat_norm (fun x => S.placedMeasurement_isProjective _ _ (hQ x))
    (fun x a => S.place_isProj _ (hR x a))
    (fun _ _ => S.place_comm first second hopp _ _)
    (fun _ _ => S.place_comm first second hopp _ _)
    ?_ η ζ hcons hdist
  intro x a
  rw [← S.place_mul, ← mul_assoc, (hR x a).isIdempotentElem.eq]

/-- A law with uniform joint point marginal has small distance from the
completed joint measurement to the ordered product, in either order. -/
theorem CombinedPointsWitness.completedProduct_dist_le {Y : Type*}
    (points : CombinedPointsWitness S δQ) (p : Placement) (W : PauliKind)
    (ν : Distribution Y)
    (point : Y → PointPair P)
    (hpoint : ∀ f, avgOver ν (f ∘ point) = avgOver (uniformDistribution _) f) :
    opFamilyDistSq ν
      (fun y o => S.place p ((points.completedPair p.side (point y).1 (point y).2).effect o))
      (fun y o => S.place p (S.completedPointPairEffect p.side W (point y) o *
        S.completedPointPairEffect p.side W.other (point y) o)) S.psiHat ≤ 4 * δQ := by
  let integrand (xz : PointPair P) :=
    ∑ o, ‖applyOperatorToState (S.place p ((points.completedPair p.side xz.1 xz.2).effect o) -
      S.place p (S.completedPointPairEffect p.side W xz o *
        S.completedPointPairEffect p.side W.other xz o)) S.psiHat‖ ^ 2
  change avgOver ν (integrand ∘ point) ≤ _
  rw [hpoint]
  refine le_of_eq_of_le (avgOver_congr _ _ _ fun xz => ?_) (points.ordered_point_dist_le p W)
  refine S.sum_norm_place_completedPair_sub_sq p (points.Q p.side xz.1 xz.2) _ _ ?_ ?_ ?_
  · intro ab
    cases W <;> simp only [ProjectiveSetting.orderedPointProduct, ProjectiveSetting.pointPairEffect,
      ProjectiveSetting.completedPointPairEffect,
      PauliKind.other, PauliKind.component, S.pointMeasExpOption_effect_some]
  · intro o
    cases W <;> simp only [ProjectiveSetting.completedPointPairEffect, PauliKind.other, PauliKind.component,
      S.pointMeasExpOption_effect_none, zero_mul, mul_zero]
  · intro o
    cases W <;> simp only [ProjectiveSetting.completedPointPairEffect, PauliKind.other, PauliKind.component,
      S.pointMeasExpOption_effect_none, zero_mul, mul_zero]

end Placed

/-! ## The two deficits over a product of restricted line-point laws -/

/-- Every restricted line-point law has total mass one. -/
theorem restrictedLinePointDist_isProbability (P : AdmissibleParams)
    (kind : LineKind) (i : Fin P.m) :
    (restrictedLinePointDist P kind i).IsProbability :=
  restrictedLineDist_isProbability P.toLdParams kind i

/-- The point marginal of a restricted line-point law is uniform. -/
theorem restrictedLinePointDist_map_snd (P : AdmissibleParams) (kind : LineKind)
    (i : Fin P.m) :
    (restrictedLinePointDist P kind i).map Prod.snd =
      uniformDistribution (PauliPoint P) := by
  rw [restrictedLinePointDist_eq_map_prod, Distribution.map_map]
  exact Distribution.prod_map_fst _ _ (Distribution.prod_isProbability _ _
    (subLineSeedDist_isProbability P i) (uniformDistribution_isProbability _))

/-- The pair of points of a product of two restricted line-point laws is a
uniform pair. -/
theorem prod_restrictedLinePointDist_map_points (P : AdmissibleParams)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)).map (fun s => (s.1.2, s.2.2)) =
      uniformDistribution
        (PointPair P) := by
  have h : Distribution.prod ((restrictedLinePointDist P kindX i).map Prod.snd)
      ((restrictedLinePointDist P kindZ j).map Prod.snd) =
      uniformDistribution
        (PointPair P) := by
    rw [restrictedLinePointDist_map_snd, restrictedLinePointDist_map_snd,
      uniformDistribution_prod]
  rw [← h, Distribution.prod_map_left, Distribution.prod_map_right,
    Distribution.map_map]

section Restricted

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

section

variable (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second)
include lines first second hopposite

/-- Restricting both line directions costs at most the product of the two
line-distribution density bounds. -/
theorem CombinedLinesWitness.consistent_restricted
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    S.placedDefect first second (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)) (lines.evalPair first.side) (fun s => points.completedPair second.side s.1.2 s.2.2) ≤ 4 * (P.m : ℝ) ^ 2 * δP :=
  (avgOver_prod_restrictedLinePointDist_le _ (fun s =>
    consistencyDefect_integrand_nonneg S first second hopposite
      (lines.evalPair first.side s) (points.completedPair second.side s.1.2 s.2.2))
    kindX kindZ i j).trans
    (mul_le_mul_of_nonneg_left (lines.consistent first second hopposite) (by positivity))

set_option maxHeartbeats 500000 in
/-- The marginal deficit in basis `W` for restricted line-point laws.
Restriction inflates the line error by `4 m ^ 2`; the point marginal remains uniform. -/
theorem CombinedLinesWitness.one_sub_overlap_restricted_le (W : PauliKind)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    1 - avgOver
      (Distribution.prod (restrictedLinePointDist P kindX i) (restrictedLinePointDist P kindZ j))
      (fun s => ∑ o, S.placedCorrelation first second
        ((lines.evalPair first.side s).effect o) (S.completedPointPairEffect second.side W (s.1.2, s.2.2) o)) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  refine one_sub_placed_overlap_le_of_product_distance first second hopposite _
    (Distribution.prod_isProbability _ _
      (restrictedLinePointDist_isProbability P kindX i) (restrictedLinePointDist_isProbability P kindZ j))
    _ _ (lines.evalPair first.side) (fun s => points.completedPair second.side s.1.2 s.2.2)
    (fun s => S.completedPointPairEffect second.side W (s.1.2, s.2.2))
    (fun s => S.completedPointPairEffect second.side W.other (s.1.2, s.2.2))
    (fun _ => completedPair_isProjective _ (points.projective _ _ _))
    (fun _ _ => S.pointMeasExpOption_isProj _ _ _ _)
    (lines.consistent_restricted first second hopposite kindX kindZ i j)
    ?_
  apply points.completedProduct_dist_le second W
    (Distribution.prod (restrictedLinePointDist P kindX i) (restrictedLinePointDist P kindZ j))
    (fun s => (s.1.2, s.2.2))
  intro f
  simp only [Function.comp_def]
  rw [← Distribution.avgOver_map _ (fun s : SourceLinePointPair P => (s.1.2, s.2.2)) f,
    prod_restrictedLinePointDist_map_points]

end

end Restricted

end

end MIPStarRE.QPBT
