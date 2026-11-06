module

public import Mathlib

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains

open MonoidAlgebra

attribute [local instance 0] Classical.propDecidable

variable {G : Type*} [Group G] (H : Subgroup G)

def subRingHom : MonoidAlgebra ℤ H →+* MonoidAlgebra ℤ G :=
  MonoidAlgebra.mapDomainRingHom ℤ H.subtype

def restrictH : MonoidAlgebra ℤ G →+ MonoidAlgebra ℤ H :=
  (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := H)).symm.toAddMonoidHom.comp
    ((Finsupp.comapDomain.addMonoidHom (M := ℤ) (f := (Subtype.val : H → G))
      Subtype.coe_injective).comp (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := G)).toAddMonoidHom)

def slice (g : G) : MonoidAlgebra ℤ G →+ MonoidAlgebra ℤ H :=
  (restrictH H).comp (AddMonoidHom.mulLeft (single g⁻¹ (1 : ℤ)))

theorem slice_mul (g : G) (x : MonoidAlgebra ℤ G) (y : MonoidAlgebra ℤ H) :
    slice H g (x * subRingHom H y) = slice H g x * y := by
  have hsingle (p : G) (c : ℤ) :
      slice H g (single p c) = if hp : g⁻¹ * p ∈ H then single ⟨g⁻¹ * p, hp⟩ c else 0 := by
    show restrictH H (single g⁻¹ (1 : ℤ) * single p c) = _
    rw [MonoidAlgebra.single_mul_single, one_mul]
    ext h
    change (single (g⁻¹ * p) c).coeff (h : G) = _
    by_cases hp : g⁻¹ * p ∈ H
    · rw [dif_pos hp]; simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Subtype.ext_iff]
    · rw [dif_neg hp]; simp [show g⁻¹ * p ≠ h from fun hc => hp (hc ▸ h.2)]
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single a m =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add _ _ h₁ h₂ => simp [mul_add, h₁, h₂]
      | single b n =>
          rw [show subRingHom H (single b n) = single (b : G) n from MonoidAlgebra.mapDomain_single,
            MonoidAlgebra.single_mul_single, hsingle, hsingle]
          by_cases hp : g⁻¹ * a ∈ H
          · have hp' : g⁻¹ * (a * (b : G)) ∈ H := by
              rw [show g⁻¹ * (a * (b : G)) = (g⁻¹ * a) * (b : G) by group]; exact H.mul_mem hp b.2
            rw [dif_pos hp, dif_pos hp', MonoidAlgebra.single_mul_single]
            exact congrArg (single · _) (Subtype.ext (by simp [mul_assoc]))
          · have hp' : ¬ g⁻¹ * (a * (b : G)) ∈ H := fun hc => hp <| by
              rw [show g⁻¹ * a = (g⁻¹ * (a * (b : G))) * (b : G)⁻¹ by group]
              exact H.mul_mem hc (H.inv_mem b.2)
            rw [dif_neg hp, dif_neg hp', zero_mul]

theorem cosetPiece_apply (g : G) (x : MonoidAlgebra ℤ G) (p : G) :
    (single g (1 : ℤ) * subRingHom H (slice H g x)).coeff p
      = if (QuotientGroup.mk p : G ⧸ H) = QuotientGroup.mk g then x.coeff p else 0 := by
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]
  by_cases hp : g⁻¹ * p ∈ H
  · rw [if_pos ((QuotientGroup.eq (s := H)).2 (by simpa using H.inv_mem hp)),
      show (subRingHom H (slice H g x)).coeff (g⁻¹ * p) = (slice H g x).coeff ⟨g⁻¹ * p, hp⟩ from
        Finsupp.mapDomain_apply_of_injective Subtype.coe_injective (slice H g x).coeff ⟨g⁻¹ * p, hp⟩]
    show (single g⁻¹ (1 : ℤ) * x).coeff (g⁻¹ * p) = x.coeff p
    rw [MonoidAlgebra.coeff_single_mul_apply]; simp
  · rw [if_neg fun hc => hp (by simpa using H.inv_mem ((QuotientGroup.eq (s := H)).1 hc))]
    exact Finsupp.mapDomain_notin_range _ _ fun ⟨h, hh⟩ => hp (hh ▸ h.2)

theorem sum_cosetPieces_of_subset (x : MonoidAlgebra ℤ G) (S : Finset (G ⧸ H))
    (hS : x.coeff.support.image (fun p => (QuotientGroup.mk p : G ⧸ H)) ⊆ S) :
    ∑ C ∈ S, single (Quotient.out C) (1 : ℤ) * subRingHom H (slice H (Quotient.out C) x) = x := by
  classical
  ext p
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl fun C _ => by
    rw [cosetPiece_apply, show (QuotientGroup.mk (Quotient.out C) : G ⧸ H) = C from Quotient.out_eq C],
    Finset.sum_ite_eq (b := fun _ => x.coeff p)]
  by_cases hp : p ∈ x.coeff.support
  · exact if_pos (hS (Finset.mem_image_of_mem _ hp))
  · simp [Finsupp.notMem_support_iff.1 hp]

variable {J : Type*} [Fintype J] {ι : Type*}

def subgroupCycles (A : ι → J → MonoidAlgebra ℤ H) : Set (J → MonoidAlgebra ℤ G) :=
  {w | ∃ y : J → MonoidAlgebra ℤ H, (∀ i, ∑ j, y j * A i j = 0) ∧
        w = fun j => subRingHom H (y j)}

theorem cycle_mem_span_subgroup_cycles (A : ι → J → MonoidAlgebra ℤ H)
    (v : J → MonoidAlgebra ℤ G) (hv : ∀ i, ∑ j, v j * subRingHom H (A i j) = 0) :
    v ∈ Submodule.span (MonoidAlgebra ℤ G) (subgroupCycles H A) := by
  classical
  let S : Finset (G ⧸ H) := (Finset.univ : Finset J).biUnion fun j =>
    (v j).coeff.support.image fun p => (QuotientGroup.mk p : G ⧸ H)
  rw [show v = ∑ C ∈ S, fun j =>
      single (Quotient.out C) (1 : ℤ) * subRingHom H (slice H (Quotient.out C) (v j)) by
    funext j; simp only [Finset.sum_apply]
    exact (sum_cosetPieces_of_subset H (v j) S
      (Finset.subset_biUnion_of_mem (fun j => (v j).coeff.support.image fun p => (QuotientGroup.mk p : G ⧸ H))
        (Finset.mem_univ j))).symm]
  refine Submodule.sum_mem _ fun C _ => ?_
  have hmem : (fun j => subRingHom H (slice H (Quotient.out C) (v j))) ∈ subgroupCycles H A :=
    ⟨fun j => slice H (Quotient.out C) (v j), fun i => by
      have h := congrArg (slice H (Quotient.out C)) (hv i)
      rw [map_sum, map_zero] at h
      exact (Finset.sum_congr rfl fun j _ => (slice_mul H _ (v j) (A i j)).symm).trans h, rfl⟩
  simpa [Pi.smul_def, smul_eq_mul] using
    Submodule.smul_mem (Submodule.span (MonoidAlgebra ℤ G) (subgroupCycles H A))
      (single (Quotient.out C) (1 : ℤ)) (Submodule.subset_span hmem)
