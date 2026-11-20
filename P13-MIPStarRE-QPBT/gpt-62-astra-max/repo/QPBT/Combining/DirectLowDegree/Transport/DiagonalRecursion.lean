module

public import QPBT.Combining.DirectLowDegree.Transport.BranchComparison

/-!
# Diagonal branches of the coordinate strategies of the direct low-degree game

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question of `Transport.Questions` carries the leading index of that direction.
On the generic event that the direction is nonzero at `i`, the leading index
is `i` and the question is the canonical direct question of the direct sample
`(p, i, v)`, where the LDT defect is bounded by the direct rejection.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses to that index with the factor `q⁻¹`, the
probability that the sampled coordinate vanishes; at the last index the zero
direction has the last coordinate as its leading index by convention and no
recursion occurs.  Summing the recursion shows that each LDT diagonal branch
is at most `q / (q - 1) ≤ 2` times the corresponding branch rejection of the
direct game.  The factor is genuine: a strategy that answers the canonical
question of a direction badly and the non-canonical questions of the same
geometric line well has LDT diagonal failure exceeding the direct branch
rejection.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:49-65,130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-! ## Direction coordinates and the one-coordinate recursion

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question carries the leading index of that direction.  On the generic event
that the direction is nonzero at `i`, the leading index is `i` and the
question is the canonical direct question of the direct sample `(p, i, v)`.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses with the factor `q⁻¹`, the probability that
the sampled coordinate vanishes.  At the last index the zero direction has the
last coordinate as its leading index by convention, and no recursion occurs. -/

section DirectionCoordinates

variable (D : DirectLdParams)

/-- Restricting at an index where the direction vanishes is restricting at the
next index. -/
private theorem directPrefixProjection_succ_of_zero
    (i i' : Fin D.m) (hi : i'.val = i.val + 1)
    (v : DirectPoint D) (hv : v i = 0) :
    directPrefixProjection i v = directPrefixProjection i' v := by
  funext j
  unfold directPrefixProjection
  by_cases hj : j.val < i.val
  · rw [if_pos hj, if_pos (by omega)]
  · by_cases hj' : j.val < i'.val
    · have hji : j = i := Fin.ext (by omega)
      simp_all
    · rw [if_neg hj, if_neg hj']

/-- Restriction beyond a coordinate ignores translation along that
coordinate. -/
private theorem directPrefixProjection_add_single
    (i i' : Fin D.m) (hi : i.val < i'.val)
    (v : DirectPoint D) (c : DirectScalarQ D) :
    directPrefixProjection i' (v + c • Pi.single i (1 : DirectScalarQ D)) =
      directPrefixProjection i' v := by
  funext j
  unfold directPrefixProjection
  by_cases hj : j.val < i'.val
  · simp_all
  · have hji : j ≠ i := by
      grind
    simp_all

/-- At the last coordinate the restricted direction has that coordinate as
its leading index: either the direction is nonzero there, or the restricted
direction is zero and the leading index of the zero direction is the last
coordinate by convention. -/
private theorem directDiagonalIndexOf_prefixProjection_last
    (i : Fin D.m) (hi : i.val + 1 = D.m) (v : DirectPoint D) :
    directDiagonalIndexOf (directPrefixProjection i v) = i := by
  by_cases hv : v i = 0
  · have hzero : directPrefixProjection i v = 0 := by
      funext j
      unfold directPrefixProjection
      by_cases hj : j.val < i.val
      · bound
      · rw [if_neg hj]
        have hji : j = i := Fin.ext (by omega)
        simp_all
    rw [hzero]
    have hsupp : ¬ (directionSupport D (0 : DirectPoint D)).Nonempty := by
      rintro ⟨j, hj⟩
      exact (mem_directionSupport D 0 j).mp hj rfl
    unfold directDiagonalIndexOf
    rw [dif_neg hsupp]
    apply Fin.ext
    simp
    simp only [DirectLdParams.firstIndex]
    omega
  · solve_by_elim [directDiagonalIndexOf_prefixProjection]

/-- Restricting to the vanishing of a coordinate below the restriction index
scales the uniform average by the inverse field size: translation along that
coordinate permutes the directions and preserves the restriction. -/
private theorem avgOver_uniform_coord_zero (i i' : Fin D.m) (hi : i.val < i'.val)
    (G : (DirectPoint D) → ℝ) :
    avgOver (uniformDistribution (DirectPoint D))
        (fun v => if v i = 0 then G (directPrefixProjection i' v) else 0) =
      (Fintype.card (DirectScalarQ D) : ℝ)⁻¹ *
        avgOver (uniformDistribution (DirectPoint D))
          (fun v => G (directPrefixProjection i' v)) := by
  classical
  have hshift : ∀ c : DirectScalarQ D,
      (∑ v : DirectPoint D,
        if v i = c then G (directPrefixProjection i' v) else 0) =
      ∑ v : DirectPoint D,
        if v i = 0 then G (directPrefixProjection i' v) else 0 := by
    intro c
    refine Fintype.sum_equiv
      (Equiv.addRight ((-c) • Pi.single i 1)) _ _ ?_
    intro v
    rw [Equiv.coe_addRight, directPrefixProjection_add_single D i i' hi]
    simp [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, add_neg_eq_zero]
  have hsum : (∑ v : DirectPoint D, G (directPrefixProjection i' v)) =
      (Fintype.card (DirectScalarQ D)) *
        ∑ v : DirectPoint D,
          if v i = 0 then G (directPrefixProjection i' v) else 0 := by
    calc
      _ =
          ∑ v : DirectPoint D, ∑ c : DirectScalarQ D,
            if v i = c then G (directPrefixProjection i' v) else 0 := by
        simp
      _ = ∑ c : DirectScalarQ D, ∑ v : DirectPoint D,
            if v i = c then G (directPrefixProjection i' v) else 0 :=
        Finset.sum_comm
      _ = ∑ c : DirectScalarQ D, ∑ v : DirectPoint D,
            if v i = 0 then G (directPrefixProjection i' v) else 0 :=
        Finset.sum_congr rfl fun c _ => hshift c
      _ = _ := by
        simp
  rw [avgOver_uniform_eq_inv_card_mul_sum, avgOver_uniform_eq_inv_card_mul_sum, hsum,
    mul_left_comm, ← mul_assoc ((Fintype.card (DirectScalarQ D) : ℝ)⁻¹)
      (Fintype.card (DirectScalarQ D) : ℝ), inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

variable (j : Fin D.m)

/-- Split a direct direction into the LDT free coordinates of the
`j`-restricted diagonal test, read in reversed coordinate order, and the
coordinates below the reversed index. -/
private def restrictedDirectionEquiv :
    (DirectPoint D) ≃
      (Fin (j.val + 1) → Fq D.toLDTParameters) ×
        (Fin (Fin.rev j).val → DirectScalarQ D) where
  toFun v :=
    (fun c => directScalarEquiv D (v ⟨D.m - 1 - c.val, by have := D.hm; omega⟩),
      fun c => v ⟨c.val, by
        omega⟩)
  invFun x := fun c =>
    if h : c.val < (Fin.rev j).val then x.2 ⟨c.val, h⟩
    else (directScalarEquiv D).symm
      (x.1 ⟨D.m - 1 - c.val, by
        have h3 := Fin.val_rev j
        omega⟩)
  left_inv v := by
    funext c
    by_cases h : c.val < (Fin.rev j).val
    · simp only [dif_pos h, Fin.eta]
    · simp only [dif_neg h, Equiv.symm_apply_apply]
      refine congrArg v (Fin.ext ?_)
      change D.m - 1 - (D.m - 1 - c.val) = c.val
      omega
  right_inv x := by
    refine Prod.ext ?_ ?_
    · funext c
      have h3 := Fin.val_rev j
      have hc : ¬ (D.m - 1 - c.val < (Fin.rev j).val) := by omega
      simp only [dif_neg hc, Equiv.apply_symm_apply]
      refine congrArg x.1 (Fin.ext ?_)
      change D.m - 1 - (D.m - 1 - c.val) = c.val
      omega
    · funext c
      simp only [dif_pos c.isLt, Fin.eta]

/-- The decoded `j`-restricted LDT direction of the free coordinates is the
restriction of the direction at the reversed index. -/
private theorem ldtPointToDirect_extend_restrictedDirectionEquiv
    (v : DirectPoint D) :
    letI := D.toLDTFieldModel
    ldtPointToDirect D
        (extendRestrictedDirection j (restrictedDirectionEquiv D j v).1) =
      directPrefixProjection (Fin.rev j) v := by
  letI := D.toLDTFieldModel
  funext c
  by_cases hc : c.val < (Fin.rev j).val
  · simp_all [directPrefixProjection, ldtPointToDirect_extendRestrictedDirection_prefix_zero D j _ c hc, if_pos hc]
  · have hrevj := Fin.val_rev j
    have hrevc := Fin.val_rev c
    have hle : (Fin.rev c).val ≤ j.val := by omega
    unfold directPrefixProjection
    rw [if_neg hc]
    simp only [ldtPointToDirect, directPointEquiv_symm_apply, extendRestrictedDirection,
      dif_pos hle, restrictedDirectionEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
    congr
    change D.m - 1 - (Fin.rev c).val = c.val
    omega

/-- Averaging over the LDT `j`-restricted diagonal sample is averaging over
a direct point and a direct direction restricted at the reversed index. -/
private theorem avgOver_restrictedDiagonalSample_eq
    (H : (DirectPoint D) → (DirectPoint D) → ℝ) :
    letI := D.toLDTFieldModel
    avgOver (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
        (fun s => H (ldtPointToDirect D s.1)
          (ldtPointToDirect D (extendRestrictedDirection j s.2))) =
      avgOver (uniformDistribution
          ((DirectPoint D) × (DirectPoint D)))
        (fun pv => H pv.1 (directPrefixProjection (Fin.rev j) pv.2)) := by
  letI := D.toLDTFieldModel
  rw [avgOver_uniform_prod (fun u free => H (ldtPointToDirect D u)
      (ldtPointToDirect D (extendRestrictedDirection j free))),
    avgOver_uniform_prod (fun p v => H p (directPrefixProjection (Fin.rev j) v)),
    avgOver_uniform_equiv (directPointEquiv D)]
  apply avgOver_congr
  intro u
  rw [← avgOver_uniform_equiv_fst (restrictedDirectionEquiv D j)
    (fun free => H (ldtPointToDirect D u)
      (ldtPointToDirect D (extendRestrictedDirection j free)))]
  apply avgOver_congr
  grind [ldtPointToDirect_extend_restrictedDirectionEquiv]

end DirectionCoordinates

/-- Geometric-series bookkeeping for the one-coordinate recursion.  If every
term is at most its rejection term plus `q⁻¹` times the term at the next
index, and the term at the last index is at most its rejection term, then the
sum is at most twice the sum of the rejection terms once `q ≥ 2`. -/
private theorem sum_le_two_mul_sum_of_recursion {m : ℕ} (t r : Fin m → ℝ) (q : ℝ)
    (hq : 2 ≤ q) (ht : ∀ i, 0 ≤ t i)
    (hstep : ∀ i i' : Fin m, i'.val = i.val + 1 → t i ≤ r i + q⁻¹ * t i')
    (hlast : ∀ i : Fin m, i.val + 1 = m → t i ≤ r i) :
    ∑ i, t i ≤ 2 * ∑ i, r i := by
  classical
  have hq0 : 0 < q := by linarith
  have hqinv0 := inv_nonneg.mpr hq0.le
  let succSum : Fin m → ℝ := fun i =>
    ∑ i' : Fin m, if i'.val = i.val + 1 then t i' else 0
  have hbound : ∀ i, t i ≤ r i + q⁻¹ * succSum i := by
    intro i
    by_cases h : i.val + 1 < m
    · have hsucc : succSum i = t ⟨i.val + 1, h⟩ := by
        simp only [succSum]
        rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
        · simp
        · grind
        · simp
      grind
    · have hsucc : succSum i = 0 := by
        refine Finset.sum_eq_zero fun i' _ => ?_
        grind
      simp [hsucc]
      apply hlast
      have := i.isLt
      omega
  have hsuccSum : ∑ i, succSum i ≤ ∑ i, t i := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i' _ => ?_
    simp [← Finset.sum_filter]
    calc _
        ≤ _ := mul_le_mul_of_nonneg_right (by
          have h1 : (Finset.univ.filter fun i : Fin m => i'.val = i.val + 1).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro a ha b hb
            simp [Finset.mem_filter] at ha hb
            omega
          exact_mod_cast h1) (ht i')
      _ = t i' := one_mul _
  have htotal : ∑ i, t i ≤ ∑ i, r i + q⁻¹ * ∑ i, t i := by
    calc _ ≤ _ := Finset.sum_le_sum fun i _ => hbound i
      _ = ∑ i, r i + q⁻¹ * ∑ i, succSum i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by
        gcongr
  have hT : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht i
  have hhalf :=
    mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num) hq) hT
  linarith

section DiagonalRecursion

variable (D : DirectLdParams)

variable (dd : (DirectPoint D) → ℝ) (rj : Fin D.m → (DirectPoint D) → ℝ)

/-- One step of the recursion at a fixed point.  On the generic event the
leading index is the sampled index and the LDT defect is bounded by the
direct rejection there; on the vanishing event the restriction agrees with the
restriction at the next index. -/
private theorem diagonal_recursion_step
    (hrj : ∀ i v, 0 ≤ rj i v)
    (hdd : ∀ v, dd v ≤ rj (directDiagonalIndexOf v) v)
    (i i' : Fin D.m) (hi : i'.val = i.val + 1) :
    avgOver (uniformDistribution (DirectPoint D))
        (fun v => dd (directPrefixProjection i v)) ≤
      avgOver (uniformDistribution (DirectPoint D))
          (fun v => rj i (directPrefixProjection i v)) +
        (Fintype.card (DirectScalarQ D) : ℝ)⁻¹ *
          avgOver (uniformDistribution (DirectPoint D))
            (fun v => dd (directPrefixProjection i' v)) := by
  classical
  have hsplit : ∀ v : DirectPoint D,
      dd (directPrefixProjection i v) =
        (if v i = 0 then 0 else dd (directPrefixProjection i v)) +
          (if v i = 0 then dd (directPrefixProjection i' v) else 0) := by
    intro v
    by_cases hv : v i = 0
    · simp [zero_add, if_pos hv, directPrefixProjection_succ_of_zero D i i' hi v hv]
    · simp_all
  rw [avgOver_congr _ _ _ hsplit, avgOver_add,
    avgOver_uniform_coord_zero D i i' (by omega) dd]
  gcongr
  refine avgOver_mono _ _ _ fun v => ?_
  by_cases hv : v i = 0
  · simp_all
  · rw [if_neg hv]
    refine LE.le.trans_eq (hdd _) ?_
    rw [directDiagonalIndexOf_prefixProjection D i v hv]

/-- Summed over the restriction index, the LDT diagonal quantities at a
fixed point are at most twice the direct rejections. -/
private theorem diagonal_sum_le
    (hdd0 : ∀ v, 0 ≤ dd v) (hrj : ∀ i v, 0 ≤ rj i v)
    (hdd : ∀ v, dd v ≤ rj (directDiagonalIndexOf v) v) :
    ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
        (fun v => dd (directPrefixProjection i v)) ≤
      2 * ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
        (fun v => rj i (directPrefixProjection i v)) := by
  refine sum_le_two_mul_sum_of_recursion _ _ (Fintype.card (DirectScalarQ D))
    (by exact_mod_cast Fintype.one_lt_card) ?_ ?_ ?_
  · solve_by_elim [avgOver_nonneg]
  · solve_by_elim [diagonal_recursion_step]
  · intro i hi
    refine avgOver_mono _ _ _ fun v => ?_
    calc _ ≤
        rj (directDiagonalIndexOf (directPrefixProjection i v))
          (directPrefixProjection i v) := hdd _
      _ = _ := by
        rw [directDiagonalIndexOf_prefixProjection_last D i hi v]

end DiagonalRecursion

/-! ## The diagonal-line branches -/

section DiagonalBranches

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

section

variable (p : DirectPoint D) (i : Fin D.m) (v : DirectPoint D)

/-- The rejected direct mass at the diagonal question of a direct sample with
the line on the left. -/
private def diagonalLinePointRejection : ℝ :=
  directRejectedMass D S (.dline, ⟨lineRepMap v p, i, v⟩) (directLdPointQuestionOf D p)

/-- The rejected direct mass at the diagonal question of a direct sample with
the point on the left. -/
private def diagonalPointLineRejection : ℝ :=
  directRejectedMass D S (directLdPointQuestionOf D p) (.dline, ⟨lineRepMap v p, i, v⟩)

end

section

variable (p v : DirectPoint D)

/-- The LDT diagonal defect with the line on the left, as a function of the
decoded base point and decoded direction of the LDT line. -/
private def diagonalLinePointDefect : ℝ :=
  letI := D.toLDTFieldModel
  qBipartiteConsDefect (directCoordinateProjStrat S hS r).state
    (postprocess ((directCoordinateProjStrat S hS r).diagonalMeasurementA
      (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩)).toSubMeas (fun g => g zeroCoord))
    ((directCoordinateProjStrat S hS r).pointMeasurementB
      (directPointEquiv D p)).toSubMeas

/-- The LDT diagonal defect with the point on the left, as a function of the
decoded base point and decoded direction of the LDT line. -/
private def diagonalPointLineDefect : ℝ :=
  letI := D.toLDTFieldModel
  qBipartiteConsDefect (directCoordinateProjStrat S hS r).state
    ((directCoordinateProjStrat S hS r).pointMeasurementA
      (directPointEquiv D p)).toSubMeas
    (postprocess ((directCoordinateProjStrat S hS r).diagonalMeasurementB
      (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩)).toSubMeas (fun g => g zeroCoord))

/-- The canonical direct question of the LDT line of a direct sample. -/
private theorem directDiagonalQuestionOf_ldtDiagonalLineOf_eq :
    directDiagonalQuestionOf (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩) =
      (.dline, ⟨lineRepMap v p, directDiagonalIndexOf v, v⟩) := by
  simp [directDiagonalQuestionOf, ldtDiagonalLineOf]

end

private theorem directPointQuestionOf_directPointEquiv (p : DirectPoint D) :
    directPointQuestionOf (directPointEquiv D p) = directLdPointQuestionOf D p := by
  simp [directPointQuestionOf]

section

variable (p v : DirectPoint D)

/-- The LDT diagonal defect is at most the direct rejection at the
canonical question carrying the leading index. -/
private theorem diagonalLinePointDefect_le :
    diagonalLinePointDefect D S hS r p v ≤
      diagonalLinePointRejection D S p (directDiagonalIndexOf v) v := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    _
    (directPointQuestionOf (directPointEquiv D p))
    _
    _
    (fun a b hab => directDiagonalAnswerReadout_zeroCoord_eq_of_win D r
      (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩) a b hab)
  unfold diagonalLinePointDefect diagonalLinePointRejection
  change qBipartiteConsDefect (strategyQuantumState S)
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.A (directDiagonalQuestionOf (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩)))
            (hS.1 _))
          (directDiagonalAnswerReadout D r
            (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩))).toSubMeas
        (fun g => g zeroCoord))
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.B (directPointQuestionOf (directPointEquiv D p))) (hS.2 _))
        (directPointAnswerReadout r)).toSubMeas ≤ _
  simp_all [directDiagonalQuestionOf_ldtDiagonalLineOf_eq, directPointQuestionOf_directPointEquiv]

/-- The LDT diagonal defect with the point on the left is at most the
direct rejection at the canonical question carrying the leading index. -/
private theorem diagonalPointLineDefect_le :
    diagonalPointLineDefect D S hS r p v ≤
      diagonalPointLineRejection D S p (directDiagonalIndexOf v) v := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directPointQuestionOf (directPointEquiv D p))
    _
    _
    _
    (fun a b hab => directPointAnswerReadout_eq_diagonal_zeroCoord_of_win D r
      (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩) a b hab)
  unfold diagonalPointLineDefect diagonalPointLineRejection
  change qBipartiteConsDefect (strategyQuantumState S)
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          (S.A (directPointQuestionOf (directPointEquiv D p))) (hS.1 _))
        (directPointAnswerReadout r)).toSubMeas
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            (S.B (directDiagonalQuestionOf (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩)))
            (hS.2 _))
          (directDiagonalAnswerReadout D r
            (ldtDiagonalLineOf ⟨p, D.firstIndex, v⟩))).toSubMeas
        (fun g => g zeroCoord)) ≤ _
  simp_all [directDiagonalQuestionOf_ldtDiagonalLineOf_eq, directPointQuestionOf_directPointEquiv]

end

/-- Formalization-only decomposition of a fixed ordered branch rejection into
the stored index and the remaining point-direction pair of a direct sample.
This supports the direct-to-LDT comparison corresponding to
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`. -/
theorem directLdBranchRejectionProbability_eq_index_avg (types : LdType × LdType) :
    directLdBranchRejectionProbability S types =
      avgOver (uniformDistribution (Fin D.m)) fun i =>
        avgOver (uniformDistribution
            ((DirectPoint D) × (DirectPoint D))) fun pv =>
          directRejectedMass D S
            (types.1, directLdMap types.1 (⟨pv.1, i, pv.2⟩ : DirectLdSpace D))
            (types.2, directLdMap types.2 (⟨pv.1, i, pv.2⟩ : DirectLdSpace D)) := by
  rw [directLdBranchRejectionProbability_eq_avgOver,
    avgOver_uniform_equiv_prod (directLdSpaceIndexEquiv D)]
  rfl

/-- The LDT line of the decoded data of an LDT line is that line. -/
private theorem ldtDiagonalLineOf_decode (u w : Point D.toLDTParameters) :
    ldtDiagonalLineOf
        ⟨ldtPointToDirect D u, D.firstIndex, ldtPointToDirect D w⟩ =
      { base := u, direction := w } := by
  simp [ldtDiagonalLineOf]

/-- The LDT `j`-restricted diagonal branch with the line on the left, as
an average of the decoded defect over the point-direction pair. -/
private theorem diagonal_line_point_term_eq (j : Fin D.m) :
    letI := D.toLDTFieldModel
    bipartiteConsError (directCoordinateProjStrat S hS r).state
        (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
        ((directCoordinateProjStrat S hS r).diagonalLineAnswerFamilyA j)
        ((directCoordinateProjStrat S hS r).diagonalPointAnswerFamilyB j) =
      avgOver (uniformDistribution
          ((DirectPoint D) × (DirectPoint D))) fun pv =>
        diagonalLinePointDefect D S hS r pv.1 (directPrefixProjection (Fin.rev j) pv.2) := by
  letI := D.toLDTFieldModel
  rw [← avgOver_restrictedDiagonalSample_eq]
  apply avgOver_congr
  intro s
  unfold diagonalLinePointDefect
  simp [ldtDiagonalLineOf_decode]
  rfl

/-- The LDT `j`-restricted diagonal branch with the point on the left, as
an average of the decoded defect over the point-direction pair. -/
private theorem diagonal_point_line_term_eq (j : Fin D.m) :
    letI := D.toLDTFieldModel
    bipartiteConsError (directCoordinateProjStrat S hS r).state
        (uniformDistribution (RestrictedDiagonalSample D.toLDTParameters j))
        ((directCoordinateProjStrat S hS r).diagonalPointAnswerFamilyA j)
        ((directCoordinateProjStrat S hS r).diagonalLineAnswerFamilyB j) =
      avgOver (uniformDistribution
          ((DirectPoint D) × (DirectPoint D))) fun pv =>
        diagonalPointLineDefect D S hS r pv.1 (directPrefixProjection (Fin.rev j) pv.2) := by
  letI := D.toLDTFieldModel
  rw [← avgOver_restrictedDiagonalSample_eq]
  apply avgOver_congr
  intro s
  unfold diagonalPointLineDefect
  simp [ldtDiagonalLineOf_decode]
  rfl

/-- Summing a decoded diagonal quantity over the reversed index is summing it
over the direct index, and the point average may be taken outside. -/
private theorem sum_rev_avgOver_eq
    (F : (DirectPoint D) → Fin D.m → (DirectPoint D) → ℝ) :
    ∑ j : Fin D.m, avgOver (uniformDistribution
        ((DirectPoint D) × (DirectPoint D)))
        (fun pv => F pv.1 (Fin.rev j) (directPrefixProjection (Fin.rev j) pv.2)) =
      avgOver (uniformDistribution (DirectPoint D)) fun p =>
        ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
          (fun v => F p i (directPrefixProjection i v)) := by
  rw [avgOver_sum]
  have hrev := Equiv.sum_comp Fin.revPerm (fun i =>
    avgOver (uniformDistribution (DirectPoint D)) fun p =>
      avgOver (uniformDistribution (DirectPoint D))
        (fun v => F p i (directPrefixProjection i v)))
  rw [← hrev]
  congr 1 with j
  exact avgOver_uniform_prod fun p v => F p j.rev (directPrefixProjection j.rev v)

/-- The direct index average of a diagonal quantity, with the point average
taken outside. -/
private theorem avgOver_index_eq
    (F : Fin D.m →
      ((DirectPoint D) × (DirectPoint D)) → ℝ) :
    avgOver (uniformDistribution (Fin D.m)) (fun i =>
        avgOver (uniformDistribution
          ((DirectPoint D) × (DirectPoint D)))
          (F i)) =
      (D.m : ℝ)⁻¹ * avgOver (uniformDistribution (DirectPoint D)) fun p =>
        ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
          (fun v => F i (p, v)) := by
  rw [avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin, avgOver_sum]
  congr 1
  congr 1 with i
  exact avgOver_uniform_prod fun p v => F i (p, v)

/-- The diagonal-line failure with the line on the left is at most twice the
diagonal-line/point branch rejection of the direct game. -/
theorem directCoordinate_diagonal_line_point_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat S hS r).diagonalLineLeftPointRightFailureProbability ≤
      2 * directLdBranchRejectionProbability S (.dline, .point) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.diagonalLineLeftPointRightFailureProbability
  simp [directLdBranchRejectionProbability_eq_index_avg, avgOver_index_eq, Finset.sum_congr rfl (fun j _ => diagonal_line_point_term_eq D S hS r j), sum_rev_avgOver_eq D (fun p _ v => diagonalLinePointDefect D S hS r p v)]
  have hmain :
      avgOver (uniformDistribution (DirectPoint D)) (fun p =>
          ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
            (fun v => diagonalLinePointDefect D S hS r p (directPrefixProjection i v))) ≤
        avgOver (uniformDistribution (DirectPoint D)) (fun p =>
          2 * ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
            (fun v => diagonalLinePointRejection D S p i (directPrefixProjection i v))) := by
    refine avgOver_mono _ _ _ fun p => ?_
    exact diagonal_sum_le D _
      _
      (fun v => qBipartiteConsDefect_nonneg _ _ _)
      (fun i v => directRejectedMass_nonneg D S _ _)
      (diagonalLinePointDefect_le D S hS r p)
  rw [avgOver_const_mul] at hmain
  calc _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by
      simp [diagonalLinePointRejection, directLdMap, directLdPointQuestionOf]
      ring

/-- The diagonal-line failure with the point on the left is at most twice the
point/diagonal-line branch rejection of the direct game. -/
theorem directCoordinate_diagonal_point_line_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat S hS r).diagonalPointLeftLineRightFailureProbability ≤
      2 * directLdBranchRejectionProbability S (.point, .dline) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.diagonalPointLeftLineRightFailureProbability
  simp [directLdBranchRejectionProbability_eq_index_avg, avgOver_index_eq, Finset.sum_congr rfl (fun j _ => diagonal_point_line_term_eq D S hS r j), sum_rev_avgOver_eq D (fun p _ v => diagonalPointLineDefect D S hS r p v)]
  have hmain :
      avgOver (uniformDistribution (DirectPoint D)) (fun p =>
          ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
            (fun v => diagonalPointLineDefect D S hS r p (directPrefixProjection i v))) ≤
        avgOver (uniformDistribution (DirectPoint D)) (fun p =>
          2 * ∑ i : Fin D.m, avgOver (uniformDistribution (DirectPoint D))
            (fun v => diagonalPointLineRejection D S p i (directPrefixProjection i v))) := by
    refine avgOver_mono _ _ _ fun p => ?_
    exact diagonal_sum_le D _
      _
      (fun v => qBipartiteConsDefect_nonneg _ _ _)
      (fun i v => directRejectedMass_nonneg D S _ _)
      (diagonalPointLineDefect_le D S hS r p)
  rw [avgOver_const_mul] at hmain
  calc _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by
      simp [diagonalPointLineRejection, directLdMap, directLdPointQuestionOf]
      ring

end DiagonalBranches

end

end MIPStarRE.QPBT
