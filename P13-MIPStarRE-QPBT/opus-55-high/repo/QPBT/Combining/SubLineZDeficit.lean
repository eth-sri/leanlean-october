module

public import QPBT.Combining.ZEvalDeficit
public import QPBT.Combining.UniformLinePoint

/-!
# Sub-line averages of the Z-point overlap

The Z-point overlap of the paired-line measurement depends on the two source
lines and the Z block of the sampled extended point. The separate projected-point
mixture properties of the directly indexed sub-line law identify each one-point
marginal as a mixture of restricted product laws. Both marginal averaging
identities are recorded here. Regrouping line answers by their evaluations
then transfers the Z-overlap deficit from
`MIPStarRE.QPBT.Combining.ZEvalDeficit` to this law.

The Z-overlap estimates hold for arbitrary opposite placements, with separate
first-player specializations. The concrete X-overlap deficit instead uses the
exact X marginal of the X-Z-X sandwich and is proved in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z estimates support blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The separate marginal identities encode the analogue of Property 2 of
`lem:qld-sublines` for the directly indexed law; source-distribution transport
remains separate.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Regrouping the line answers by their evaluations -/

/-- Summing a paired-line answer against a family of point effects that
depends on the answer only through its two evaluations is summing the
evaluation classes of the paired-line measurement against that family.  This
is the fiber regrouping of the proofs of `lem:claim-17-1`, `lem:claim-17-2`,
and `lem:claim-17-3`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:2651-2830`. -/
theorem regroup_line_answer_sum_at {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (lineX lineZ : LineDesc P.toLdParams) (x z : Fin P.m → PauliScalar P)
    (G : Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace second.side)) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          ((S.placedMeasurement first
            ((lines.T first.side lineX lineZ).postprocess (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2)))).effect o *
            S.place second (G o.1 o.2))) =
      ∑ fX, ∑ fZ, stateQForm S.psiHat
        (S.place first ((lines.T first.side lineX lineZ).effect (fX, fZ)) *
          S.place second (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) := by
  have hsum : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (M : DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d) →
        Op (S.ExpandedLocalSpace first.side))
      (N : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)),
      stateQForm S.psiHat (S.place first (∑ fs ∈ s, M fs) * N) =
        ∑ fs ∈ s, stateQForm S.psiHat (S.place first (M fs) * N) := by
    intro s M N
    rw [S.place_finsetSum]
    simp [stateQForm, applyOperatorToState, Finset.sum_mul]
  calc
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          stateQForm S.psiHat
            ((S.placedMeasurement first
              ((lines.T first.side lineX lineZ).postprocess (fun fs =>
                (evalOpt lineX x fs.1, evalOpt lineZ z fs.2)))).effect o *
              S.place second (G o.1 o.2))) =
        ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2) = o),
            stateQForm S.psiHat
              (S.place first ((lines.T first.side lineX lineZ).effect fs) *
                S.place second (G o.1 o.2)) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [ProjectiveSetting.placedMeasurement_effect,
        MIPStarRE.Quantum.Measurement.postprocess_effect]
      exact hsum _ _ _
    _ = ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2) = o),
            stateQForm S.psiHat
              (S.place first ((lines.T first.side lineX lineZ).effect fs) *
                S.place second
                  (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))) := by
      refine Finset.sum_congr rfl fun o _ =>
        Finset.sum_congr rfl fun fs hfs => ?_
      rw [← (Finset.mem_filter.mp hfs).2]
    _ = ∑ fs : DegPoly P.toLdParams (P.m * P.d) ×
          DegPoly P.toLdParams (P.m * P.d),
          stateQForm S.psiHat
            (S.place first ((lines.T first.side lineX lineZ).effect fs) *
              S.place second
                (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))) :=
      Finset.sum_fiberwise_of_maps_to (fun fs _ => Finset.mem_univ _) _
    _ = ∑ fX, ∑ fZ, stateQForm S.psiHat
          (S.place first ((lines.T first.side lineX lineZ).effect (fX, fZ)) *
            S.place second (G (evalOpt lineX x fX) (evalOpt lineZ z fZ))) :=
      Fintype.sum_prod_type (f := fun fs => stateQForm S.psiHat
        (S.place first ((lines.T first.side lineX lineZ).effect fs) *
          S.place second (G (evalOpt lineX x fs.1) (evalOpt lineZ z fs.2))))

variable (P : AdmissibleParams) (sublines : SubLineWitness P) (F : (LineDesc P.toLdParams × LineDesc P.toLdParams) × (Fin P.m → PauliScalar P) → ℝ)

/-- The sub-line average of a function of the two source lines and the
`X`-point of the sampled extended point is a mixture of averages over products
of two restricted line-point laws, the `X`-point being the point of the first
factor. This is the use of Property~2 of `lem:qld-sublines` in the proof of
`lem:claim-17-2`, blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`. -/
theorem SubLineWitness.exists_avgOver_X_eq_mixture :
    ∃ components : Distribution (SubLineComponent P), components.IsProbability ∧
      avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => F (sample.2, projX (directPointToPauli P
              (sample.1.base + t • sample.1.direction))))) =
        avgOver components (fun c =>
          avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
              (restrictedLinePointDist P c.1 c.2.2))
            (fun w => F ((w.1.1, w.2.1), w.1.2))) := by
  obtain ⟨components, hcomp, hX, -⟩ := sublines.source_mixture
  refine ⟨components, hcomp, ?_⟩
  have h1 : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => F (sample.2, projX (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) =
      avgOver ((subLinePointDist P sublines.D).map subLineXProjection) F := by
    rw [Distribution.avgOver_map, subLinePointDist, Distribution.avgOver_map,
      SandwichProduct.avgOver_distribution_prod]
    rfl
  rw [h1, hX, avgOver_bind]
  refine avgOver_congr _ _ _ fun c => ?_
  rw [subLineXComponentDist, Distribution.avgOver_map, Distribution.prod_map_right,
    Distribution.avgOver_map]

/-- The sub-line average of a function of the two source lines and the
`Z`-point of the sampled extended point is a mixture of averages over products
of two restricted line-point laws, the `Z`-point being the point of the second
factor.  This is the use of Property~2 of `lem:qld-sublines` in the proof of
`lem:claim-17-3`, blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`. -/
theorem SubLineWitness.exists_avgOver_Z_eq_mixture :
    ∃ components : Distribution (SubLineComponent P), components.IsProbability ∧
      avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => F (sample.2, projZ (directPointToPauli P
              (sample.1.base + t • sample.1.direction))))) =
        avgOver components (fun c =>
          avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
              (restrictedLinePointDist P c.1 c.2.2))
            (fun w => F ((w.1.1, w.2.1), w.2.2))) := by
  obtain ⟨components, hcomp, -, hZ⟩ := sublines.source_mixture
  refine ⟨components, hcomp, ?_⟩
  have h1 : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => F (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) =
      avgOver ((subLinePointDist P sublines.D).map subLineZProjection) F := by
    rw [Distribution.avgOver_map, subLinePointDist, Distribution.avgOver_map,
      SandwichProduct.avgOver_distribution_prod]
    rfl
  rw [h1, hZ, avgOver_bind]
  refine avgOver_congr _ _ _ fun c => ?_
  rw [subLineZComponentDist, Distribution.avgOver_map, Distribution.prod_map_left,
    Distribution.avgOver_map]

/-! ## The two one-point overlaps -/

section Overlaps

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- The overlap of the paired-line measurement at two source lines with the
expanded `Z`-point effect at a point, summed over the line answers.  This is
the integrand of the left-hand side of `lem:claim-17-3`, as a function of the
two source lines and the `Z`-point alone. -/
def zPointOverlapAt (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) : ℝ :=
  ∑ fX, ∑ fZ, stateQForm S.psiHat
    (S.place first ((lines.T first.side w.1.1 w.1.2).effect (fX, fZ)) *
      S.place second ((S.pointMeasExpOption second.side .Z w.2).effect (evalOpt w.1.2 w.2 fZ)))

variable (lines : CombinedLinesWitness S points δP) (first second : Placement)

/-- At a pair of line-point pairs, the `Z`-point overlap is the overlap of the
evaluated pair-line measurement with the completed `Z`-point measurement; the
`X`-point of the first pair only labels the evaluation classes. -/
theorem zPointOverlap_eq_at (w : LinePointPairSample P) :
    zPointOverlapAt lines first second ((w.1.1, w.2.1), w.2.2) =
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place first
            (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
              (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2)) :=
  (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
    (fun _ o2 => (S.pointMeasExpOption second.side .Z w.2.2).effect o2)).symm

/-- The `Z`-point overlap is nonnegative. -/
theorem zPointOverlap_nonneg_at (hopposite : first.IsOpposite second)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) :
    0 ≤ zPointOverlapAt lines first second w :=
  Finset.sum_nonneg fun fX _ => Finset.sum_nonneg fun fZ _ =>
    stateQForm_nonneg _ (S.place_mul_place_nonneg first second hopposite
      ((lines.T first.side w.1.1 w.1.2).pos (fX, fZ))
      ((S.pointMeasExpOption second.side .Z w.2).pos (evalOpt w.1.2 w.2 fZ)))

/-- The sub-line average of the `Z`-point overlap is at most one. -/
theorem SubLineWitness.avgOver_zPointOverlap_le_one_at (sublines : SubLineWitness P)
    (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤ 1 := by
  obtain ⟨components, hcomp, hmix⟩ :=
    SubLineWitness.exists_avgOver_Z_eq_mixture P sublines (zPointOverlapAt lines first second)
  rw [hmix]
  refine hcomp.avgOver_le_of_forall_le_on_support _ _ fun c _ => ?_
  have h := avgOver_sum_stateQForm_mul_le_one
    (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
      (restrictedLinePointDist P c.1 c.2.2))
    (fun w : LinePointPairSample P => S.placedMeasurement first
      ((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
        (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)))
    (fun (w : LinePointPairSample P)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place second ((S.pointMeasExpOption second.side .Z w.2.2).effect o.2))
    S.psiHat
    (Distribution.prod_isProbability _ _
      (restrictedLinePointDist_isProbability P c.1 c.2.1)
      (restrictedLinePointDist_isProbability P c.1 c.2.2))
    S.psiHat_norm
    (fun w o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun w o => S.place_comm first second hopposite _ _)
  simp at h
  rw [avgOver_congr _ _ _ fun w => zPointOverlap_eq_at lines first second w]
  exact h

/-- The deficit of the sub-line average of the `Z`-point overlap is bounded by
the inflated line and point consistency errors.  This is the bound on the
deficit in the proof of `lem:claim-17-3`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`. -/
theorem SubLineWitness.one_sub_avgOver_zPointOverlap_le_at
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    1 - avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  obtain ⟨components, hcomp, hmix⟩ :=
    SubLineWitness.exists_avgOver_Z_eq_mixture P sublines (zPointOverlapAt lines first second)
  rw [hmix, ← avgOver_const_of_isProbability components hcomp 1, ← avgOver_sub]
  refine hcomp.avgOver_le_of_forall_le_on_support _ _ fun c _ => ?_
  rw [avgOver_congr _ _ _ fun w => zPointOverlap_eq_at lines first second w]
  refine lines.one_sub_overlap_restricted_le_at first second hopposite c.1 c.1 c.2.1 c.2.2
    (fun xz o => (S.pointMeasExpOption second.side .Z xz.2).effect o.2)
    (fun xz o => (S.pointMeasExpOption second.side .X xz.1).effect o.1)
    (fun _ _ => S.pointMeasExpOption_isProj _ _ _ _) (fun _ _ => S.pointMeasExpOption_isProj _ _ _ _) ?_
  exact le_of_eq_of_le (avgOver_congr _ _ _ fun xz => S.completedPair_norm_sq_sum_ZX points second xz.1 xz.2)
    (points.orderedZX_dist_le second)

end Overlaps

end

end MIPStarRE.QPBT
