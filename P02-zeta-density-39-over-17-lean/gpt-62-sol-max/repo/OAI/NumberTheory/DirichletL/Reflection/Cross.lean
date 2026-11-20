module
public import OAI.NumberTheory.DirichletL.Reflection.Frozen

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_frozen_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F)
    (hu : (R ∪ P) ∪ F = Finset.univ) :
    (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      (∏ i ∈ R, (∏ k ∈ R.erase i, x i k^a)*(l i*∏ k ∈ F, x i k^a)) *
      (∏ i ∈ P, (∏ k ∈ P.erase i, x i k^b)*(l i*∏ k ∈ F, x i k^b)) *
      (∏ i ∈ R, ∏ k ∈ P, x i k^a*x k i^b) := by
  let ll := fun i => l i*∏ k ∈ F, x i k ^ (if i ∈ R then a else b)
  have hx : (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      ∏ i ∈ R ∪ P, (∏ k ∈ (R ∪ P).erase i,
        x i k ^ (if i ∈ R then a else b))*ll i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ F := fun hf => Finset.disjoint_left.mp hF hi hf
    have he : Finset.univ.erase i = (R ∪ P).erase i ∪ F := by
      rw [← hu, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn]
    rw [he,Finset.prod_union (hF.mono_left (Finset.erase_subset _ _))]
    dsimp [ll]
    ring
  rw [hx,MixedCrossSeparation.ordered_cross_partition_on x ll a b R P (R ∪ P) hRP rfl]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [ll,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [ll,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI
