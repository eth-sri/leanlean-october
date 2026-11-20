module

public import QPBT.Combining.Points.Consistency

/-!
# Orthonormalization of the sandwich POVM

For each fixed point pair `(x, z)`, the sandwich POVM `R^{x,z}` on one
register placement is consistent with the sandwich POVM on the opposite
placement, with the consistency defect bounded by
`ProjectiveSetting.sandwichDefectBound`.  The orthonormalization lemma
`lem:ortho`, in its explicit-constant form
`projective_rounding_with_explicit_constant`, therefore produces a projective
measurement `Q^{x,z}` on the original local space, within `220 · c^{1/4}` of
`R^{x,z}` on the expanded state, where `c` is that bound.  Choosing such a
measurement for every pair and averaging, the concavity of `t ↦ t^{1/4}`
turns the average of the fiberwise errors into the same function of the
average defect.

The orthonormalization lemma is stated for a bipartite state whose first
tensor factor carries the POVM to be rounded.  The two bipartitions used are
`AA' | BA''(B'B'')`, for Alice's measurements, and `BA'' | AA'(B'B'')`, for
Bob's; the second is introduced here.

## Main results

* `baAaBipartition` with its two placement lemmas.
* `avgOver_rpow_quarter_le`: Jensen's inequality for the fourth root.
* `ProjectiveSetting.exists_projective_close_sandwich`: the fiberwise
  orthonormalization, for any bipartition exhibiting the two placements as
  the two tensor factors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:786-790`
(the application of the orthonormalization lemma), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:870-878` (`lem:qld-4-10`), and
`blueprint/src/chapter/ch14_qpbt_observables.tex:395-464` (`lem:ortho`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Jensen's inequality for the fourth root -/

/-- The fourth root of a nonnegative real is the iterated square root. -/
theorem rpow_quarter_eq_sqrt_sqrt {t : ℝ} (ht : 0 ≤ t) :
    Real.rpow t (1 / 4 : ℝ) = Real.sqrt (Real.sqrt t) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
  norm_num

/-- Jensen's inequality for the concave function `t ↦ t^{1/4}` on a
sub-probability average, obtained by applying the square-root inequality
twice. -/
theorem avgOver_rpow_quarter_le {X : Type*} (𝒟 : Distribution X)
    (h𝒟 : ∑ x ∈ 𝒟.support, 𝒟.weight x ≤ 1) (b : X → ℝ) (hb : ∀ x, 0 ≤ b x) :
    avgOver 𝒟 (fun x => Real.rpow (b x) (1 / 4 : ℝ)) ≤
      Real.rpow (avgOver 𝒟 b) (1 / 4 : ℝ) := by
  have h1 : |avgOver 𝒟 (fun x => Real.sqrt (Real.sqrt (b x)))| ≤
      Real.sqrt (avgOver 𝒟 (fun x => Real.sqrt (b x))) :=
    MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun x => by simp [abs_of_nonneg])
      (fun x => Real.sqrt_nonneg _) h𝒟
  have h2 :=
    MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun x => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) hb h𝒟
  rw [rpow_quarter_eq_sqrt_sqrt (avgOver_nonneg 𝒟 b hb)]
  refine Eq.trans_le (avgOver_congr _ _ _ fun x => rpow_quarter_eq_sqrt_sqrt (hb x)) ?_
  refine le_trans (le_abs_self _) ?_
  refine le_trans h1 ?_
  exact Real.sqrt_le_sqrt (le_trans (le_abs_self _) h2)

/-! ## The bipartition with Bob's registers first -/

/-- Regroup `AA'A''BB'B''` as `BA'' | AA'(B'B'')`.  This is the bipartition
in which Bob's expanded local space is the first tensor factor, used to
orthonormalize the sandwich POVM on Bob's side. -/
def baAaBipartition (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃
      (ιB × PauliRegister P) ×
        ((ιA × PauliRegister P) × (PauliRegister P × PauliRegister P)) where
  toFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((b, a''), ((a, a'), (b', b'')))
  invFun := fun ⟨⟨b, a''⟩, ⟨a, a'⟩, b', b''⟩ => ((a, (a', a'')), (b, (b', b'')))
  left_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl
  right_inv := by rintro ⟨⟨b, a''⟩, ⟨a, a'⟩, b', b''⟩; rfl

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- Under the `BA'' | AA'(B'B'')` bipartition, a `BA''` placement is the
ordinary left tensor placement. -/
theorem reindexOp_baAaBipartition_left (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    reindexOp (baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O
          (1 : Op ((S.toStrategy.ιA × PauliRegister P) ×
            (PauliRegister P × PauliRegister P)))) =
      S.place .BA'' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, baAaBipartition, Equiv.coe_fn_mk, heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-- Under the `BA'' | AA'(B'B'')` bipartition, an `AA'` placement is the
ordinary right tensor placement, with identity on the unused EPR pair. -/
theorem reindexOp_baAaBipartition_right (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.AA'.side)) :
    reindexOp (baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιB × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
      S.place .AA' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, baAaBipartition, Equiv.coe_fn_mk, heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-! ## Transport along a bipartition -/

section Bipartition

variable (S : ProjectiveSetting P ε) (p₁ p₂ : Placement)

section

variable {α : Type*} [Fintype α]

set_option synthInstance.maxSize 400 in
/-- The consistency defect of two placed POVMs, read in the bipartite picture
of the reindexed expanded state, is their off-diagonal mass in the expanded
state. -/
theorem consistencyDefect_reindex_eq [DecidableEq α]
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      S.ExpandedLocalSpace p₁.side ×
        (S.ExpandedLocalSpace p₂.side × (PauliRegister P × PauliRegister P)))
    (he₁ : ∀ O : Op (S.ExpandedLocalSpace p₁.side),
      reindexOp e (heteroKron O
        (1 : Op (S.ExpandedLocalSpace p₂.side ×
          (PauliRegister P × PauliRegister P)))) = S.place p₁ O)
    (he₂ : ∀ O : Op (S.ExpandedLocalSpace p₂.side),
      reindexOp e (heteroKron (1 : Op (S.ExpandedLocalSpace p₁.side))
        (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
          S.place p₂ O)
    (Q : Measurement α (S.ExpandedLocalSpace p₁.side))
    (R : Measurement α (S.ExpandedLocalSpace p₂.side)) :
    bipartiteDefect (uniformDistribution Unit)
        (fun _ => Q)
        (fun _ => leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P) R)
        (reindexState e S.psiHat) =
      ∑ a : α, ∑ b : α, if a = b then 0 else
        stateQForm S.psiHat (S.place p₁ (Q.effect a) * S.place p₂ (R.effect b)) := by
  classical
  simp only [bipartiteDefect, consistencyDefect]
  rw [avgOver_uniform_const]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · rw [if_neg hab, if_neg hab, consistency_term_eq_stateQForm,
      WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul, he₁]
    change stateQForm S.psiHat (_ *
      reindexOp e (heteroKron 1 (heteroKron (R.effect b) 1))) = _
    rw [he₂]

set_option synthInstance.maxSize 400 in
/-- The state-dependent distance of two families placed on the first factor,
read in the bipartite picture, is their placed distance in the expanded
state. -/
theorem opFamilyDistSq_reindex_left_eq
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      S.ExpandedLocalSpace p₁.side ×
        (S.ExpandedLocalSpace p₂.side × (PauliRegister P × PauliRegister P)))
    (he₁ : ∀ O : Op (S.ExpandedLocalSpace p₁.side),
      reindexOp e (heteroKron O
        (1 : Op (S.ExpandedLocalSpace p₂.side ×
          (PauliRegister P × PauliRegister P)))) = S.place p₁ O)
    (A B : α → Op (S.ExpandedLocalSpace p₁.side)) :
    opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron (A a) 1) (fun _ a => heteroKron (B a) 1)
        (reindexState e S.psiHat) =
      ∑ a : α, ‖applyOperatorToState (S.place p₁ (A a) - S.place p₁ (B a))
        S.psiHat‖ ^ 2 := by
  classical
  unfold opFamilyDistSq
  rw [avgOver_uniform_const]
  simp [WinImplications.norm_applyOperatorToState_reindexState, WinImplications.reindexOp_sub, he₁]

end

set_option synthInstance.maxSize 400 in
/-- Fiberwise orthonormalization of the sandwich POVM: for the placement pair
exhibited by the bipartition `e`, there is, for every point pair, a projective
measurement on the local space of the first placement whose placed distance to
the placed sandwich is at most `220` times the fourth root of the consistency
bound; on average over the point pair the distance is at most `220` times the
fourth root of the averaged bound.  Both distances are squared distances.
This is the application of `lem:ortho` in the proof of `lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:786-790`,
carried out for each point pair and averaged by Jensen's inequality. -/
theorem exists_projective_close_sandwich (hopp : p₁.IsOpposite p₂)
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      S.ExpandedLocalSpace p₁.side ×
        (S.ExpandedLocalSpace p₂.side × (PauliRegister P × PauliRegister P)))
    (he₁ : ∀ O : Op (S.ExpandedLocalSpace p₁.side),
      reindexOp e (heteroKron O
        (1 : Op (S.ExpandedLocalSpace p₂.side ×
          (PauliRegister P × PauliRegister P)))) = S.place p₁ O)
    (he₂ : ∀ O : Op (S.ExpandedLocalSpace p₂.side),
      reindexOp e (heteroKron (1 : Op (S.ExpandedLocalSpace p₁.side))
        (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
          S.place p₂ O)
    :
    ∃ Q : PointPair P →
        Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p₁.side),
      (∀ xz, MIPStarRE.QPBT.Measurement.IsProjective (Q xz)) ∧
        opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz (ab : PauliScalar P × PauliScalar P) =>
            S.place p₁ ((Q xz).effect ab))
          (fun xz ab => S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab))
          S.psiHat ≤
          220 * Real.rpow (avgOver (uniformDistribution (PointPair P))
            (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) := by
  classical
  have hxz : ∀ xz : PointPair P,
      ∃ Pm : Measurement (PauliScalar P × PauliScalar P)
        (S.ExpandedLocalSpace p₁.side),
        MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
          ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
            (S.place p₁ (Pm.effect ab) -
              S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab))
            S.psiHat‖ ^ 2 ≤
            220 * Real.rpow (S.sandwichDefectBound p₁ p₂ xz) (1 / 4) := by
    intro xz
    obtain ⟨Pm, hPm, hdist⟩ := projective_rounding_with_explicit_constant
      (reindexState e S.psiHat) (by rw [reindexState_norm_eq, psiHat_norm]) (S.sandwichPoint p₁.side xz.1 xz.2)
      _
      _ (S.sandwichDefectBound_nonneg p₁ p₂ xz) (by
        rw [consistencyDefect_reindex_eq S p₁ p₂ e he₁ he₂]
        exact S.sandwich_offDiagonal_le_sandwichDefectBound p₁ p₂ hopp xz)
    refine ⟨Pm, hPm, ?_⟩
    rw [opFamilyDistSq_reindex_left_eq S p₁ p₂ e he₁] at hdist
    exact hdist
  choose Q hQ using hxz
  refine ⟨Q, fun xz => (hQ xz).1, ?_⟩
  refine le_trans (avgOver_mono _ _ _ fun xz => (hQ xz).2) ?_
  refine Eq.trans_le (avgOver_const_mul _ _ _) ?_
  gcongr
  exact avgOver_rpow_quarter_le _ (uniformDistribution_weight_sum_le_one _) _
    (S.sandwichDefectBound_nonneg p₁ p₂)

end Bipartition

end ProjectiveSetting

end

end MIPStarRE.QPBT
