/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def faceBaseRange (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)
def faceSheetRange (n : ℕ) : Finset ℤ :=
  Finset.Icc (-((n ^ 5 : ℕ) : ℤ)) ((n ^ 5 : ℕ) : ℤ)
def faceFullCarrier (n : ℕ) : Finset ParafermionicCoverVertex :=
   (faceBaseRange n ×ˢ faceBaseRange n) ×ˢ faceSheetRange n 
def faceBranchFiber (n : ℕ) : Finset ParafermionicCoverVertex :=
  ({(0,-1)} : Finset (ℤ × ℤ)) ×ˢ faceSheetRange n
def faceSeamTopFiber (n : ℕ) : Finset ParafermionicCoverVertex :=
  (({0} : Finset ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (-2)) ×ˢ
    ({((n ^ 5 : ℕ) : ℤ)} : Finset ℤ)

section

variable (n : ℕ)
include n

private theorem faceBaseRange_card  :
    (faceBaseRange n).card = 2*n := by
  have h :  (faceBaseRange n).card  = 2*(n : ℤ) := by
    
    calc
      _ =   n -1  + 1 -  -(n : ℤ)  :=
        Int.card_Icc_of_le (- n ) ( n -1) (by omega)
      _ = 2* n  := by ring
  exact_mod_cast h

private theorem faceSheetRange_card  :
    (faceSheetRange n).card = 2*n^5+1 := by
  have h :  (faceSheetRange n).card  =
      2*( n^5  : ℤ)+1 := by
    
    calc
      _ =  (n^5:ℕ)  + 1 -  -((n^5:ℕ):ℤ)  :=
        Int.card_Icc_of_le (- (n^5:ℕ) )  (n^5:ℕ)  (by omega)
      _ = 2* (n^5:ℕ) +1 := by ring
  exact_mod_cast h

private theorem faceFullCarrier_card  :
    (faceFullCarrier n).card = (2*n)^2 * (2*n^5+1) := by
  simp [faceFullCarrier, faceBaseRange_card, faceSheetRange_card]
  ring

private theorem faceBranchFiber_card  :
    (faceBranchFiber n).card = 2*n^5+1 := by
  simp [faceBranchFiber, faceSheetRange_card]

section

variable (hn : 1 ≤ n)
include hn

private theorem faceSeamTopFiber_card   :
  (faceSeamTopFiber n).card = n-1 := by
  have hcard : ((Finset.Icc (-(n : ℤ)) (-2)).card : ℤ) = n-1 := by
    aesop
  have hnat : (Finset.Icc (-(n : ℤ)) (-2)).card = n-1 := by
    exact_mod_cast hcard
  simp [faceSeamTopFiber, hnat]

private theorem faceBranchFiber_subset_full   :
    faceBranchFiber n ⊆ faceFullCarrier n := by
  grind +locals

private theorem faceSeamTopFiber_subset_full   :
    faceSeamTopFiber n ⊆ faceFullCarrier n := by
  grind +locals

end

private theorem faceBranchFiber_disjoint_seamTopFiber  :
    Disjoint (faceBranchFiber n) (faceSeamTopFiber n) := by
  apply Finset.disjoint_left.mpr
  intro v hv1 hv2
  rcases Finset.mem_product.mp hv1 with ⟨hbase,hk⟩
  rcases Finset.mem_product.mp hv2 with ⟨hbase2,hk2⟩
  simp_all

private theorem faceFiniteFaces_eq_sdiff  :
    parafermionicCoverFiniteOrdinaryFaces n =
      faceFullCarrier n \ (faceBranchFiber n ∪ faceSeamTopFiber n) := by
  
  apply Finset.ext
  intro v
  rw [parafermionicCoverFiniteOrdinaryFaces_mem_iff]
  simp only [faceFullCarrier, faceBaseRange, faceSheetRange, faceBranchFiber, faceSeamTopFiber]
  grind

theorem parafermionicCoverFiniteOrdinaryFaces_card  (hn : 1 ≤ n) :
    (parafermionicCoverFiniteOrdinaryFaces n).card + (2*n^5+1) + (n-1) =
      (2*n)^2 * (2*n^5+1) := by
  
  
  rw [faceFiniteFaces_eq_sdiff n,
    Finset.card_sdiff_of_subset (Finset.union_subset (faceBranchFiber_subset_full n hn)
                                     (faceSeamTopFiber_subset_full n hn)),
    Finset.card_union_of_disjoint (faceBranchFiber_disjoint_seamTopFiber n),
    faceFullCarrier_card, faceBranchFiber_card, faceSeamTopFiber_card n hn]
  have hn5 : n ≤ n^5 := by nlinarith [Nat.one_le_pow 4 n hn]
  
  have htotal : 2*(2*n^5+1) ≤ (2*n)^2*(2*n^5+1) := by
    simp_all <;> nlinarith
  omega

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
