module

public import OAI.NumberTheory.DirichletL.Descent.Dyadic

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
noncomputable section

section FiniteGrid
variable {M H C A : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq C] [AddCommMonoid A]

def gridCommonSupport (T : Finset ((M × H) × C)) (m : M) : Finset C :=
  (T.filter fun u => u.1.1 = m).image Prod.snd

theorem finite_triple_support_reindex (T : Finset ((M × H) × C))
    (f : (M × H) × C → A) :
    (∑ u ∈ T, f u) = ∑ p ∈ T.image Prod.fst,
      ∑ c ∈ gridCommonSupport T p.1, if (p, c) ∈ T then f (p, c) else 0 := by
  have hp := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image Prod.fst) (g := Prod.fst)
    (by grind) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr (by grind)
    grind
  · grind
  · simp
  grind

end FiniteGrid

def HybridColumnData.gridIndex (d : HybridColumnData) :
    (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) × Ideal ActualEisensteinCubic.O := ((d.residualN, d.residualB), d.common)

theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal ActualEisensteinCubic.O) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  have hm : d.residualN = e.residualN := congrArg (fun u => u.1.1) hg
  have hh : d.residualB = e.residualB := congrArg (fun u => u.1.2) hg
  have hc : d.common = e.common := congrArg Prod.snd hg
  have ht := hd.trans he.symm
  cases d
  cases e
  simp_all

def hybridGridSupport (D : Finset HybridColumnData) :
    Finset ((Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) × Ideal ActualEisensteinCubic.O) := D.image HybridColumnData.gridIndex

end
end SevenEighths.InverseMoment

end OAI
