module

public import QPBT.Combining.Lines.RestrictedMixture
public import QPBT.Combining.Witnesses

/-!
# Error inflation of restricted line-point averages

This module records how a nonnegative average over the line-point distribution
transfers to one restricted component.  The line-point law places weight
`1 / 2` on each of its two kinds and, inside each kind, weight `1 / m` on each
coordinate index, so every restricted component carries mixture weight
`1 / (2 m)` and a nonnegative average inflates by at most `2 m`.

## References

The estimates are items 1 and 2 of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled estimates at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement

noncomputable section

/-! ## Inflation of a restricted line-point average -/

/-- Restricting a nonnegative line-point average to one kind and one coordinate
index inflates it by at most `2 m`.  This is the pointwise form of item 1 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`. -/
theorem avgOver_restrictedLinePointDist_le {P : AdmissibleParams}
    (f : (LinePointSample P.toLdParams) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kind : LineKind) (i : Fin P.m) :
    avgOver (restrictedLinePointDist P kind i) f ≤
      2 * (P.m : ℝ) * avgOver (linePointDist P.toLdParams) f := by
  classical
  haveI := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one P.one_le_m)
  have hm : (0 : ℝ) < (P.m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one P.one_le_m
  have hkind : avgOver (lineKindPointDist P.toLdParams kind) f ≤
      2 * avgOver (linePointDist P.toLdParams) f := by
    rw [linePointDist, avgOver_mix]
    have hA := avgOver_nonneg (aLinePointDist P.toLdParams) f hf
    have hD := avgOver_nonneg (dLinePointDist P.toLdParams) f hf
    cases kind <;> linarith
  have hcomp := avgOver_bind_uniform_component_le (restrictedLineDist P.toLdParams kind) f hf i
  rw [Fintype.card_fin, one_div_mul_eq_div, div_le_iff₀ hm, ← lineKindPointDist_eq_bind_restricted] at hcomp
  simpa only [restrictedLinePointDist, mul_comm, mul_left_comm, mul_assoc] using
    hcomp.trans (mul_le_mul_of_nonneg_right hkind hm.le)

/-- Restricting a nonnegative average over two independent line-point samples
to one kind and coordinate index in each factor inflates it by at most
`4 m ^ 2`.  This is the pointwise form of item 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1056-1058`. -/
theorem avgOver_prod_restrictedLinePointDist_le {P : AdmissibleParams}
    (f : ((LinePointSample P.toLdParams) ×
      (LinePointSample P.toLdParams)) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kindX kindZ : LineKind) (i j : Fin P.m) :
    avgOver (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * avgOver (Distribution.prod
        (linePointDist P.toLdParams) (linePointDist P.toLdParams)) f := by
  classical
  have hfactor : (0 : ℝ) ≤ 2 * (P.m : ℝ) := by positivity
  rw [SandwichProduct.avgOver_distribution_prod, SandwichProduct.avgOver_distribution_prod]
  have hinner :=
    fun s1 => avgOver_restrictedLinePointDist_le
      (fun s2 => f (s1, s2)) (fun s2 => hf (s1, s2)) kindZ j
  calc _
      ≤ avgOver (restrictedLinePointDist P kindX i)
          (fun s1 => 2 * (P.m : ℝ) *
            avgOver (linePointDist P.toLdParams) (fun s2 => f (s1, s2))) :=
        avgOver_mono _ _ _ hinner
    _ = 2 * (P.m : ℝ) * avgOver (restrictedLinePointDist P kindX i)
          (fun s1 => avgOver (linePointDist P.toLdParams)
            (fun s2 => f (s1, s2))) := avgOver_const_mul _ _ _
    _ ≤ 2 * (P.m : ℝ) * (2 * (P.m : ℝ) *
          avgOver (linePointDist P.toLdParams)
            (fun s1 => avgOver (linePointDist P.toLdParams)
              (fun s2 => f (s1, s2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactor
        exact avgOver_restrictedLinePointDist_le
          (fun s1 => avgOver (linePointDist P.toLdParams)
            (fun s2 => f (s1, s2)))
          (fun s1 => avgOver_nonneg _ _ fun s2 => hf (s1, s2)) kindX i
    _ = _ := by ring

end

end MIPStarRE.QPBT
