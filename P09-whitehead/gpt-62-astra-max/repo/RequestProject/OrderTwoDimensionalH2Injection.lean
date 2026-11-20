module

public import RequestProject.OrderRealizationCockcroft
public import RequestProject.StrictOrderNormalizationMaps

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

variable [(nerve P).HasDimensionLE 2]

/-- The stated nerve dimension bound excludes actual strictly increasing tetrahedra. -/
theorem strictOrdTet_isEmpty_of_dimension_two :
    IsEmpty (StrictOrdTet P) := by
  refine ⟨fun t => ?_⟩
  let s := ordTetNerveEquiv P ⟨t.1, t.2.1.le, t.2.2.1.le, t.2.2.2.le⟩
  have hs : s ∈ (nerve P).nonDegenerate 3 := by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mpr
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · apply t.2.1
    · apply t.2.2.1
    · apply t.2.2.2
  have hdim := (nerve P).dim_le_of_nonDegenerate ⟨s, hs⟩ 2
  omega

theorem normalizeOrdBoundary3_eq_zero_of_dimension_two
    (b : OrdTet P →₀ ℤ) : normalizeOrdChain2 (ordBoundary3 b) = 0 := by
  letI := strictOrdTet_isEmpty_of_dimension_two (P := P)
  erw [normalizeOrdChain2_ordBoundary3]
  have hz : normalizeOrdChain3 b = 0 := Subsingleton.elim _ _
  simp_all

end FiniteChains.Comb
