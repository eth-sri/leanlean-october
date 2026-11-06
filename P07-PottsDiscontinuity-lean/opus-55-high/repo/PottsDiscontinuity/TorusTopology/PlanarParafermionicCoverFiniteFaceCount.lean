/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable (n : ℕ)
def faceBaseRange  : Finset ℤ := Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)
def faceSheetRange  : Finset ℤ :=
  Finset.Icc (-((n ^ 5 : ℕ) : ℤ)) ((n ^ 5 : ℕ) : ℤ)
def faceFullCarrier  : Finset ParafermionicCoverVertex :=
  ((faceBaseRange n ×ˢ faceBaseRange n) ×ˢ faceSheetRange n)
def faceBranchFiber  : Finset ParafermionicCoverVertex :=
  ({(0,-1)} : Finset (ℤ × ℤ)) ×ˢ faceSheetRange n
def faceSeamTopFiber  : Finset ParafermionicCoverVertex :=
  (({0} : Finset ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (-2)) ×ˢ
    ({((n ^ 5 : ℕ) : ℤ)} : Finset ℤ)

theorem faceBaseRange_card  :
    (faceBaseRange n).card = 2*n := by
  have h : ((faceBaseRange n).card : ℤ) = 2*(n : ℤ) := by
    calc
      _ = ((n : ℤ)-1) + 1 - (-(n : ℤ)) :=
        Int.card_Icc_of_le (-(n : ℤ)) ((n : ℤ)-1) (by omega)
      _ = 2*(n : ℤ) := by ring
  omega

theorem faceSheetRange_card  :
    (faceSheetRange n).card = 2*n^5+1 := by
  have h : ((faceSheetRange n).card : ℤ) =
      2*((n^5 : ℕ) : ℤ)+1 := by
    calc
      _ = ((n^5:ℕ):ℤ) + 1 - (-((n^5:ℕ):ℤ)) :=
        Int.card_Icc_of_le (-((n^5:ℕ):ℤ)) ((n^5:ℕ):ℤ) (by omega)
      _ = 2*((n^5:ℕ):ℤ)+1 := by ring
  omega

theorem faceFullCarrier_card  :
    (faceFullCarrier n).card = (2*n)^2 * (2*n^5+1) := by
  simp [faceFullCarrier, faceBaseRange_card, faceSheetRange_card, Finset.card_product]
  ring

theorem faceBranchFiber_card  :
    (faceBranchFiber n).card = 2*n^5+1 := by
  simp [faceBranchFiber, faceSheetRange_card]

theorem faceSeamTopFiber_card (hn : 1 ≤ n) :
  (faceSeamTopFiber n).card = n-1 := by
  have hcard : ((Finset.Icc (-(n : ℤ)) (-2)).card : ℤ) = n-1 := by
    aesop
  simp_all [faceSeamTopFiber]

theorem faceBranchFiber_subset_full (hn : 1 ≤ n) :
    faceBranchFiber n ⊆ faceFullCarrier n := by
  intro v hv
  rcases Finset.mem_product.mp hv with ⟨hbase,hk⟩
  change v ∈ ((faceBaseRange n ×ˢ faceBaseRange n) ×ˢ faceSheetRange n)
  grind [faceBaseRange]

theorem faceSeamTopFiber_subset_full (hn : 1 ≤ n) :
    faceSeamTopFiber n ⊆ faceFullCarrier n := by
  intro v hv
  rcases Finset.mem_product.mp hv with ⟨hbase,hk⟩
  change v ∈ ((faceBaseRange n ×ˢ faceBaseRange n) ×ˢ faceSheetRange n)
  grind [faceBaseRange, faceSheetRange]

theorem faceBranchFiber_disjoint_seamTopFiber  :
    Disjoint (faceBranchFiber n) (faceSeamTopFiber n) := by
  apply Finset.disjoint_left.mpr
  intro v hv1 hv2
  rcases Finset.mem_product.mp hv1 with ⟨hbase,hk⟩
  rcases Finset.mem_product.mp hv2 with ⟨hbase2,hk2⟩
  simp_all

theorem faceFiniteFaces_eq_sdiff  :
    parafermionicCoverFiniteOrdinaryFaces n =
      faceFullCarrier n \ (faceBranchFiber n ∪ faceSeamTopFiber n) := by
  apply Finset.ext
  intro v
  rw [Finset.mem_sdiff, Finset.mem_union,
    parafermionicCoverFiniteOrdinaryFaces_mem_iff]
  simp only [faceFullCarrier, faceBaseRange, faceSheetRange,
    faceBranchFiber, faceSeamTopFiber, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_singleton]
  constructor <;> grind

theorem parafermionicCoverFiniteOrdinaryFaces_card (hn : 1 ≤ n) :
    (parafermionicCoverFiniteOrdinaryFaces n).card + (2*n^5+1) + (n-1) =
      (2*n)^2 * (2*n^5+1) := by
  have hsub :=
    Finset.union_subset (faceBranchFiber_subset_full n hn)
      (faceSeamTopFiber_subset_full n hn)
  rw [faceFiniteFaces_eq_sdiff n,
    Finset.card_sdiff_of_subset hsub,
    Finset.card_union_of_disjoint (faceBranchFiber_disjoint_seamTopFiber n),
    faceFullCarrier_card, faceBranchFiber_card, faceSeamTopFiber_card n hn]
  have hn5 : n ≤ n^5 := by nlinarith [Nat.one_le_pow 4 n hn]
  have htotal : 2*(2*n^5+1) ≤ (2*n)^2*(2*n^5+1) := by
    have hn2 : 4 ≤ (2*n)^2 := by nlinarith
    nlinarith
  omega
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
