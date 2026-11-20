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
    {f : (LineDesc P.toLdParams × (PauliPoint P)) → ℝ}
    (hf : ∀ sample, 0 ≤ f sample) (kind : LineKind) (i : Fin P.m) :
    avgOver (restrictedLinePointDist kind i) f ≤
      2 * (P.m : ℝ) * avgOver (linePointDist P.toLdParams) f := by
  classical
  haveI :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one P.one_le_m)
  have hm : 0 < (P.m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one P.one_le_m
  have hAnonneg : 0 ≤ avgOver (aLinePointDist P.toLdParams) f :=
    avgOver_nonneg _ _ hf
  have hDnonneg : 0 ≤ avgOver (dLinePointDist P.toLdParams) f :=
    avgOver_nonneg _ _ hf
  have hmixture : avgOver (linePointDist P.toLdParams) f =
      1 / 2 * avgOver (aLinePointDist P.toLdParams) f +
        _ * avgOver (dLinePointDist P.toLdParams) f :=
    avgOver_mix _ _ _ _ _ f
  -- Each kind is bounded by twice the full line-point average.
  have hsum : 2 * avgOver (linePointDist P.toLdParams) f =
      avgOver (aLinePointDist P.toLdParams) f +
        avgOver (dLinePointDist P.toLdParams) f := by
    rw [hmixture]
    ring
  have hcomponent : ∀ (ν : Fin P.m → Distribution (LineDesc P.toLdParams ×
      (PauliPoint P))) (μ : Distribution (LineDesc P.toLdParams ×
      (PauliPoint P))),
      μ = Distribution.bind (uniformDistribution (Fin P.m)) ν →
      avgOver μ f ≤ 2 * avgOver (linePointDist P.toLdParams) f →
      avgOver (ν i) f ≤ 2 * P.m * avgOver (linePointDist P.toLdParams) f := by
    intro ν μ hbind hle
    have hcomp := avgOver_bind_uniform_component_le ν f hf i
    rw [Fintype.card_fin, ← hbind] at hcomp
    have hstep : avgOver (ν i) f ≤ P.m * avgOver μ f := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm] at hcomp
      rw [mul_comm]
      exact hcomp
    refine le_trans hstep ?_
    refine LE.le.trans_eq (mul_le_mul_of_nonneg_left hle (le_of_lt hm)) ?_
    ring
  cases kind with
  | axis =>
      exact hcomponent _ (aLinePointDist P.toLdParams)
        ((by
           classical
           haveI :=
             Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one P.toLdParams.hm)
           have hmix := Distribution.bind_uniform_restrict_eq
             (clDistribution (ldALineCL P.toLdParams) (ldPointCL P.toLdParams))
             (restrictedLineSeedEvent P.toLdParams) (restrictedALineSeedEvent_positive P.toLdParams)
             (fun i => by
               simp [clDistribution_seedEvent_mass P.toLdParams i (ldALineCL P.toLdParams) fun _ => rfl])
             (fun sample => ⟨chiIndex P.toLdParams (LdSpace.seed sample.1), rfl, fun i hi => hi.symm⟩)
           rw [aLinePointDist, ← hmix, Distribution.bind_map]
           rfl)) (by
          rw [hsum]
          exact le_add_of_nonneg_right hDnonneg)
  | diagonal =>
      exact hcomponent _ (dLinePointDist P.toLdParams)
        ((by
           classical
           haveI :=
             Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one P.toLdParams.hm)
           have hmix := Distribution.bind_uniform_restrict_eq
             (clDistribution (ldDLineCL P.toLdParams) (ldPointCL P.toLdParams))
             (restrictedLineSeedEvent P.toLdParams) (restrictedDLineSeedEvent_positive P.toLdParams)
             (fun i => by
               simp [clDistribution_seedEvent_mass P.toLdParams i (ldDLineCL P.toLdParams) fun _ => rfl])
             (fun sample => ⟨chiIndex P.toLdParams (LdSpace.seed sample.1), rfl, fun i hi => hi.symm⟩)
           rw [dLinePointDist, ← hmix, Distribution.bind_map]
           rfl)) (by
          rw [hsum]
          exact le_add_of_nonneg_left hAnonneg)

/-- Restricting a nonnegative average over two independent line-point samples
to one kind and coordinate index in each factor inflates it by at most
`4 m ^ 2`.  This is the pointwise form of item 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1056-1058`. -/
theorem avgOver_prod_restrictedLinePointDist_le {P : AdmissibleParams}
    (f : ((LineDesc P.toLdParams × (PauliPoint P)) ×
      (LineDesc P.toLdParams × (PauliPoint P))) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kindX kindZ : LineKind) (i j : Fin P.m) :
    avgOver (Distribution.prod (restrictedLinePointDist kindX i)
        (restrictedLinePointDist kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * avgOver (Distribution.prod
        (linePointDist P.toLdParams) (linePointDist P.toLdParams)) f := by
  classical
  simp [avgOver_prod]
  calc _
      ≤ _ :=
        avgOver_mono _ _ _ (fun s1 => avgOver_restrictedLinePointDist_le (fun s2 => hf (s1, s2)) kindZ j)
    _ = _ := avgOver_const_mul _ _ _
    _ ≤ 2 * P.m * (2 * P.m *
          avgOver (linePointDist P.toLdParams)
            (fun s1 => avgOver (linePointDist P.toLdParams)
              (fun s2 => f (s1, s2)))) := by
        gcongr
        exact avgOver_restrictedLinePointDist_le
          (fun s1 => avgOver_nonneg _ _ fun s2 => hf (s1, s2)) kindX i
    _ = _ := by ring

end

end MIPStarRE.QPBT
