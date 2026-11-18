module
public import OAI.NumberTheory.DirichletL.Descent.Dyadic

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

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
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huT, congrArg Prod.fst hup⟩, rfl⟩
    · simpa only [← hup, Prod.eta] using huT
  · intro u hu v hv he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    · exact he
  · intro c hc
    exact ⟨(p, c), Finset.mem_filter.mpr ⟨((Finset.mem_filter.mp hc).2), rfl⟩, rfl⟩
  · intro u hu
    simp only [← ((Finset.mem_filter.mp hu).2), Prod.eta]

end FiniteGrid

def HybridColumnData.gridIndex (d : HybridColumnData) :
    (Ideal Eis × Ideal Eis) × Ideal Eis := ((d.residualN, d.residualB), d.common)

theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal Eis) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  cases d
  cases e
  cases (congrArg Prod.snd hg)
  cases (congrArg (fun u => u.1.1) hg)
  cases (congrArg (fun u => u.1.2) hg)
  cases (hd.trans he.symm)
  rfl

def hybridGridSupport (D : Finset HybridColumnData) :
    Finset ((Ideal Eis × Ideal Eis) × Ideal Eis) := D.image HybridColumnData.gridIndex

end
end SevenEighths.InverseMoment

end OAI
