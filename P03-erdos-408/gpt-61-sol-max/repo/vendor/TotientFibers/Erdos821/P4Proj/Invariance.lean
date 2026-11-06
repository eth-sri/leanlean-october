module
public import Mathlib.Tactic

public import Erdos821.P4Probe.RowBridge
public import Erdos821.P4Probe.Anova
public import Erdos821.P4Probe.CountingTasks
public import Erdos821.P4Probe.InvarianceTasks
public import Erdos821.P4Count.ProbeCounting

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Proj
open Erdos821.P4Probe

noncomputable section

variable {s M : ℕ} {α : Fin s → Type} [∀ g, Fintype (α g)]

local instance rowSiteDecidableEq' (s M : ℕ) : DecidableEq (RowSite s M) :=
  Classical.decEq _

/-- Pushforward action of a row permutation on flat samples. -/
def rowPush (π : Fin s → Equiv.Perm (Fin M))
    (y : ProductSample (FlatAlphabet α M)) : ProductSample (FlatAlphabet α M) :=
  fun z => y ((rowPermutation s M π).symm z)

/-- The pushforward action is bijective. -/
def rowSampleEquiv (π : Fin s → Equiv.Perm (Fin M)) :
    ProductSample (FlatAlphabet α M) ≃ ProductSample (FlatAlphabet α M) where
  toFun y := rowPush (s := s) (M := M) (α := α) π y
  invFun y := fun z => y ((rowPermutation s M π) z)
  left_inv y := by
    funext ⟨g, i⟩
    show y (g, (π g).symm ((π g) i)) = y (g, i)
    rw [Equiv.symm_apply_apply]
  right_inv y := by
    funext ⟨g, i⟩
    show y (g, (π g) ((π g).symm i)) = y (g, i)
    rw [Equiv.apply_symm_apply]

omit [(g : Fin s) → Fintype (α g)] in
/-- Flat weights are constant along row permutations. -/
lemma flatWeight_pushforward  w 
     π   y  :
    productWeight (flatWeight w) (rowPush (s := s) (M := M) (α := α) π y) =
      productWeight (flatWeight w) y := Equiv.prod_comp (rowPermutation s M π).symm
    (fun j => (flatWeight w) j (y j))

omit [(g : Fin s) → Fintype (α g)] in
/-- A symmetric source stays invariant under row-permutation pushforward. -/
lemma symmetric_pushforward_invariant
    (f : ProbeSample α M → ℂ)
    (hsym : ∀ (π : Fin s → Equiv.Perm (Fin M)) x,
      f (fun g i => x g (π g i)) = f x)
    (π : Fin s → Equiv.Perm (Fin M)) (y : ProductSample (FlatAlphabet α M)) :
    (fun y => f (flattenRows.symm y)) (rowPush (s := s) (M := M) (α := α) π y) =
      (fun y => f (flattenRows.symm y)) y := by
  show f (flattenRows.symm (rowPush (s := s) (M := M) (α := α) π y)) =
    f (flattenRows.symm y)
  have hx : flattenRows.symm (rowPush (s := s) (M := M) (α := α) π y) =
      fun g i => (flattenRows.symm y) g ((π g).symm i) := by
    funext g i
    rfl
  rw [hx]
  exact hsym (fun g => (π g).symm) _

/-- Membership in a row-permuted Finset unfolds through the inverse. -/
lemma mem_map_rowPerm (π : Fin s → Equiv.Perm (Fin M))
    (S : Finset (RowSite s M))  z  :
    z ∈ S.map (rowPermutation s M π).toEmbedding ↔
      (rowPermutation s M π).symm z ∈ S := by
  simp_all

omit [(g : Fin s) → Fintype (α g)] in
/-- Mixing commutes with row-permutation pushforward over mapped sets. -/
lemma mix_pushforward  π 
     S 
     x y  :
    mixCoords (S.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y) =
      rowPush (s := s) (M := M) (α := α) π (mixCoords S x y) := by
  funext ⟨g, i⟩
  have hiff : ((g, i) ∈ S.map (rowPermutation s M π).toEmbedding) ↔
      ((rowPermutation s M π).symm (g, i) ∈ S) :=
    mem_map_rowPerm π S (g, i)
  by_cases hz : (g, i) ∈ S.map (rowPermutation s M π).toEmbedding
  · have hS : (rowPermutation s M π).symm (g, i) ∈ S := hiff.mp hz
    have h1 : mixCoords (S.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y) (g, i) =
        (rowPush (s := s) (M := M) (α := α) π y) (g, i) := by
      simp only [mixCoords]
      exact ite_eq_left hz
    have h2 : (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) =
        y ((rowPermutation s M π).symm (g, i)) := by
      simp only [mixCoords]
      exact ite_eq_left hS
    have h3 : (rowPush (s := s) (M := M) (α := α) π (mixCoords S x y)) (g, i) =
        (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) := rfl
    aesop
  · have hS : (rowPermutation s M π).symm (g, i) ∉ S :=
      fun h => hz (hiff.mpr h)
    have h1 : mixCoords (S.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y) (g, i) =
        (rowPush (s := s) (M := M) (α := α) π x) (g, i) := by
      simp only [mixCoords]
      exact ite_eq_right hz
    have h2 : (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) =
        x ((rowPermutation s M π).symm (g, i)) := by
      simp only [mixCoords]
      exact ite_eq_right hS
    have h3 : (rowPush (s := s) (M := M) (α := α) π (mixCoords S x y)) (g, i) =
        (mixCoords S x y) ((rowPermutation s M π).symm (g, i)) := rfl
    aesop

/-- Averaging over a mapped set pulls back through row permutations. -/
lemma avg_pullback  w 
     π 
     U   G 
     x  :
    productAverage (flatWeight w) (U.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π x) =
      productAverage (flatWeight w) U
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) x := by
  unfold productAverage
  symm
  apply Fintype.sum_equiv (rowSampleEquiv (s := s) (M := M) (α := α) π)
  intro y'
  show (productWeight (flatWeight w) y' : ℂ) *
      (fun z => G (rowPush (s := s) (M := M) (α := α) π z))
        (mixCoords U x y') =
    (productWeight (flatWeight w)
        (rowPush (s := s) (M := M) (α := α) π y') : ℂ) *
      G (mixCoords (U.map (rowPermutation s M π).toEmbedding)
        (rowPush (s := s) (M := M) (α := α) π x)
        (rowPush (s := s) (M := M) (α := α) π y'))
  rw [flatWeight_pushforward, mix_pushforward]

section
variable (π : Fin s → Equiv.Perm (Fin M)) (S : Finset (RowSite s M))
include π S

/-- Mapping by `σ.symm` then `σ` is the identity on finsets. -/
lemma map_symm_map  
      :
    (S.map (rowPermutation s M π).symm.toEmbedding).map
      (rowPermutation s M π).toEmbedding = S := by
  aesop

/-- Mapping by `σ` then `σ.symm` is the identity on finsets. -/
lemma map_map_symm  
      :
    (S.map (rowPermutation s M π).toEmbedding).map
      (rowPermutation s M π).symm.toEmbedding = S := by
  aesop

end

/-- Full projection pulls back through row permutations. -/
lemma full_pullback  w 
     π 
     I   G 
     x  :
    productFull (flatWeight w) (I.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π x) =
      productFull (flatWeight w) I
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) x := by
  unfold productFull
  symm
  refine Finset.sum_bij (fun V _ => V.map (rowPermutation s M π).toEmbedding)
    ?_ ?_ ?_ ?_
  · simp_all
  · simp_all
  · intro U hU
    simp only [Finset.mem_powerset] at hU
    refine ⟨U.map (rowPermutation s M π).symm.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_powerset]
      have hsub : U.map (rowPermutation s M π).symm.toEmbedding ⊆
          (I.map (rowPermutation s M π).toEmbedding).map
            (rowPermutation s M π).symm.toEmbedding :=
        Finset.map_subset_map.mpr hU
      rwa [map_map_symm] at hsub
    · exact map_symm_map π U
  grind [rowPermutation, avg_pullback]

/-- Complement of a mapped set is the mapped complement (relative to `univ`). -/
lemma univ_sdiff_map  π 
     S  :
    (Finset.univ \ S.map (rowPermutation s M π).toEmbedding) =
      (Finset.univ \ S).map (rowPermutation s M π).toEmbedding := by
  grind [Finset.univ, rowPermutation, mem_map_rowPerm]

section
variable (w : ∀ g, α g → ℝ)
include w

/-- ANOVA components pull back through row permutations. -/
lemma anova_pullback  
     π 
     S   G 
     x  :
    productAnova (flatWeight w) Finset.univ
        (S.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π x) =
      productAnova (flatWeight w) Finset.univ S
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) x := by
  unfold productAnova
  have hcompl : (Finset.univ \ S.map (rowPermutation s M π).toEmbedding) =
      (Finset.univ \ S).map (rowPermutation s M π).toEmbedding :=
    univ_sdiff_map π S
  rw [hcompl]
  have hcomp : (fun z => productAverage (flatWeight w)
      ((Finset.univ \ S).map (rowPermutation s M π).toEmbedding) G
      (rowPush (s := s) (M := M) (α := α) π z)) =
      productAverage (flatWeight w) (Finset.univ \ S)
        (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) := by
    simp_all [avg_pullback, Finset.univ]
  grind [productFull, flatWeight, rowPermutation, productAverage, Finset.univ, rowPush, full_pullback]

/-- Symmetric ANOVA energies are invariant under row permutations. -/
lemma anova_energy_invariant  
    (f : ProbeSample α M → ℂ)
    (hsym : ∀ (π : Fin s → Equiv.Perm (Fin M)) x,
      f (fun g i => x g (π g i)) = f x)
     π   S  :
    productSqNorm (flatWeight w)
        (productAnova (flatWeight w) Finset.univ
          (S.map (rowPermutation s M π).toEmbedding)
          (fun y => f (flattenRows.symm y))) =
      productSqNorm (flatWeight w)
        (productAnova (flatWeight w) Finset.univ S
          (fun y => f (flattenRows.symm y))) := by
  let G : ProductSample (FlatAlphabet α M) → ℂ :=
    fun y => f (flattenRows.symm y)
  have hG : (fun z => G (rowPush (s := s) (M := M) (α := α) π z)) = G := by
    funext y
    exact symmetric_pushforward_invariant f hsym π y
  have hpoint : ∀ y, productAnova (flatWeight w) Finset.univ
      (S.map (rowPermutation s M π).toEmbedding) G
      (rowPush (s := s) (M := M) (α := α) π y) =
      productAnova (flatWeight w) Finset.univ S G y := by
    grind [anova_pullback]
  unfold productSqNorm
  symm
  apply Fintype.sum_equiv (rowSampleEquiv (s := s) (M := M) (α := α) π)
  intro y
  show productWeight (flatWeight w) y *
      ‖productAnova (flatWeight w) Finset.univ S G y‖ ^ 2 =
    productWeight (flatWeight w) (rowPush (s := s) (M := M) (α := α) π y) *
      ‖productAnova (flatWeight w) Finset.univ
        (S.map (rowPermutation s M π).toEmbedding) G
        (rowPush (s := s) (M := M) (α := α) π y)‖ ^ 2
  rw [flatWeight_pushforward, hpoint]

end

end
end Erdos821.P4Proj

/-- The exclusive row-symmetry fact: ANOVA energies are invariant. -/
theorem Erdos821.P4Probe.RowAnovaInvariantTask_proof :
    Erdos821.P4Probe.RowAnovaInvariantTask := by
  solve_by_elim [Erdos821.P4Proj.anova_energy_invariant]
