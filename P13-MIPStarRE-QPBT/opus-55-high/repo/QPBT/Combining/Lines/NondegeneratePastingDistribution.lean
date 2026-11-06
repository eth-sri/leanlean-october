module

public import QPBT.Combining.Lines.NondegeneratePastingMass

/-!
# Nondegenerate-line pasting distribution

This module constructs the proof-only normalized product line-point law whose
first sampled line has nonzero direction.

## References

The conditioning supports the pasting argument in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`, using
the normalized question laws from
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

variable (L : LdParams)

/-- The first-line nondegeneracy event has positive mass under the product
line-point law. -/
theorem prod_linePointDist_nondegenerate_mass_pos :
    0 < ∑ samples ∈
        (Distribution.prod (linePointDist L) (linePointDist L)).support.filter
          (fun samples => samples.1.1.direction ≠ 0),
      (Distribution.prod (linePointDist L) (linePointDist L)).weight samples := by
  change 0 < nondegenerateLinePastingMass L
  grind [nondegenerateLinePastingMass_bounds]

/-- Proof-only question law obtained by conditioning the product line-point law
on nonzero first-line direction and relabeling the two samples for pasting. -/
def nondegenerateLinePastingDist :
    Distribution (((LineDesc L × LineDesc L) ×
      (LineDesc L × (Fin L.m → ScalarQ L))) ×
        (LineDesc L × (Fin L.m → ScalarQ L))) :=
  (Distribution.restrict (Distribution.prod (linePointDist L) (linePointDist L))
    (fun samples => samples.1.1.direction ≠ 0)
    (prod_linePointDist_nondegenerate_mass_pos L)).map
      (fun samples => (((samples.1.1, samples.2.1), samples.2), samples.1))

/-- The proof-only nondegenerate pasting question law is normalized. -/
theorem nondegenerateLinePastingDist_isProbability :
    (nondegenerateLinePastingDist L).IsProbability :=
  (Distribution.restrict_isProbability _ _
    (prod_linePointDist_nondegenerate_mass_pos L)).map _

end

end MIPStarRE.QPBT
