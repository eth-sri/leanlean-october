module

public import QPBT.Combining.Defs

/-! Canonical representatives and their invariance under the conditioning maps. -/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Canonical representatives are unchanged by the conditioning maps -/

/-- Two axis-line descriptions with the same seed and the same base agree:
the stored proof of `def:line-representative` invariance is a proposition and
carries no further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_axis_congr {L : LdParams}
    {b b' : LdPoint L} {s : ScalarQ L} (h : b = b')
    (hb : lineRepMap (coordinateDirection (chiIndex L s)) b = b)
    (hb' : lineRepMap (coordinateDirection (chiIndex L s)) b' = b') :
    LineDesc.axis b s hb = LineDesc.axis b' s hb' := by simp_all

/-- Two diagonal-line descriptions with the same seed, the same base and the
same direction agree: the stored proofs of `def:line-representative`
invariance and of the prefix-zero condition are propositions and carry no
further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_diagonal_congr {L : LdParams}
    {b b' d d' : LdPoint L} {s : ScalarQ L}
    (hb : b = b') (hd : d = d')
    (h1 : lineRepMap d b = b)
    (h2 : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d j = 0)
    (h1' : lineRepMap d' b' = b')
    (h2' : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d' j = 0) :
    LineDesc.diagonal b s d h1 h2 = LineDesc.diagonal b' s d' h1' h2' := by simp_all

end

end MIPStarRE.QPBT
