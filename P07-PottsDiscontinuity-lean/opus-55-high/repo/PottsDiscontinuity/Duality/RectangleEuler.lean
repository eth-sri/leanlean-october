/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import PottsDiscontinuity.Duality.RectangleDualPotential
public import PottsDiscontinuity.Duality.RectangleOpenFlow

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

section
variable (a : LatticeVertex) (w h : ℕ)
def rectangleConfigurationOfCarrier (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleGraph a w h) := by
  change Finset (rectangleGraph a w h).edgeSet
  exact A

def rectangleCarrierOfConfiguration (A : Configuration (rectangleGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier a w h) := by
  change Finset (rectangleGraph a w h).edgeSet
  exact A

abbrev rectangleOpenDivSpace (A : Finset (rectanglePrimalEdgeCarrier a w h)) :=
  @Min.min (Submodule ℝ (RectanglePrimalFlow a w h)) inferInstance
    (rectangleOpenFlowSubmodule a w h (rectangleConfigurationOfCarrier a w h A))
    (rectangleDivergenceFreeFlowSubmodule a w h)

def rectanglePrimalBondSubtype (e : rectanglePrimalEdgeCarrier a w h) : RectanglePrimalBond a w h :=
  ⟨rectanglePrimalEdgeBond a w h e,
    rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩
end

 section
variable (a : LatticeVertex) (w h : ℕ) (A : Finset (rectanglePrimalEdgeCarrier a w h))
theorem rectangleDualCurlKernel_openSupport
    (φ : rectangleDualPotentialCurlKernel a w h A)
    (b : RectanglePrimalBond a w h)
    (hb : rectanglePrimalBondToEdge a w h b ∉ A) :
    rectanglePotentialCurlMap a w h φ.1 b = 0 := by
  let e := rectanglePrimalBondToEdge a w h b
  have heq : rectanglePrimalEdgeBondEquiv a w h e = b := by
    grind [rectanglePrimalEdgeBondEquiv]
  have hzero := φ.2 e (by omega)
  change rectanglePotentialCurlMap a w h φ.1
    (rectanglePrimalBondSubtype a w h e) = 0 at hzero
  have hbond : rectanglePrimalBondSubtype a w h e =
      rectanglePrimalEdgeBondEquiv a w h e := by
    rfl
  simp_all

 theorem rectangleOpenFlow_mem_curlKernel
    (F : rectangleOpenDivSpace a w h A) :
    (rectanglePotentialCurlLinearEquiv a w h).symm
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩ ∈
      rectangleDualPotentialCurlKernel a w h A := by
  intro e he
  have hclosed : rectanglePrimalBondToEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e) ∉ A := by
    grind [rectanglePrimalBondToEdge, rectanglePrimalEdgeBondEquiv]
  have hzero := (Submodule.mem_inf.mp F.2).1
    ((rectanglePrimalEdgeBondEquiv a w h) e) hclosed
  have hF : rectanglePotentialCurlMap a w h
      ((rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩) = F.1 := by
    have hh := congrArg Subtype.val
      ((rectanglePotentialCurlLinearEquiv a w h).apply_symm_apply
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
    tauto
  aesop

def rectangleDualCurlKernelToOpenIntersection
     :
    rectangleDualPotentialCurlKernel a w h A →ₗ[ℝ]
      rectangleOpenDivSpace a w h A where
  toFun φ := by
    refine ⟨(rectanglePotentialCurlLinearEquiv a w h φ.1).1, ?_⟩
    apply Submodule.mem_inf.mpr
    constructor
    · intro b hb
      exact rectangleDualCurlKernel_openSupport a w h A φ b hb
    simp
  map_add' φ ψ := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h (φ.1 + ψ.1)).1 =
      (rectanglePotentialCurlLinearEquiv a w h φ.1).1 +
        (rectanglePotentialCurlLinearEquiv a w h ψ.1).1
    exact congrArg Subtype.val
      (map_add (rectanglePotentialCurlLinearEquiv a w h).toLinearMap φ.1 ψ.1)
  map_smul' c φ := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h (c • φ.1)).1 =
      c • (rectanglePotentialCurlLinearEquiv a w h φ.1).1
    exact congrArg Subtype.val
      (map_smul (rectanglePotentialCurlLinearEquiv a w h).toLinearMap c φ.1)

def rectangleOpenIntersectionToDualCurlKernel
     :
    (rectangleOpenDivSpace a w h A) →ₗ[ℝ]
      rectangleDualPotentialCurlKernel a w h A where
  toFun F := by
    let d : rectangleDivergenceFreeFlowSubmodule a w h :=
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩
    refine ⟨(rectanglePotentialCurlLinearEquiv a w h).symm d, ?_⟩
    grind [rectangleOpenFlow_mem_curlKernel]
  map_add' F G := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1 + G.1, ?_⟩ =
      (rectanglePotentialCurlLinearEquiv a w h).symm
          ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩ +
        (rectanglePotentialCurlLinearEquiv a w h).symm
          ⟨G.1, (Submodule.mem_inf.mp G.2).2⟩
    · exact map_add ((rectanglePotentialCurlLinearEquiv a w h).symm).toLinearMap
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩
        ⟨G.1, (Submodule.mem_inf.mp G.2).2⟩
  map_smul' c F := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨c • F.1, ?_⟩ =
      c • (rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩
    · exact map_smul ((rectanglePotentialCurlLinearEquiv a w h).symm).toLinearMap c
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩

 theorem rectangleDualCurlKernelOpenEquiv_bijective
     :
    Function.Bijective (rectangleDualCurlKernelToOpenIntersection a w h A) := by
  constructor
  · intro φ ψ hxy
    have hflow := congrArg Subtype.val hxy
    apply Subtype.ext
    apply (rectanglePotentialCurlLinearEquiv a w h).injective
    apply Subtype.ext
    tauto
  · intro F
    refine ⟨rectangleOpenIntersectionToDualCurlKernel a w h A F, ?_⟩
    apply Subtype.ext
    have hval := congrArg Subtype.val
      ((rectanglePotentialCurlLinearEquiv a w h).apply_symm_apply
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
    tauto

noncomputable def rectangleDualCurlKernelOpenLinearEquiv
     :
    rectangleDualPotentialCurlKernel a w h A ≃ₗ[ℝ]
      rectangleOpenDivSpace a w h A :=
  LinearEquiv.ofBijective (rectangleDualCurlKernelToOpenIntersection a w h A)
    (rectangleDualCurlKernelOpenEquiv_bijective a w h A)

noncomputable def rectangleDualPotentialCurlKernelSignedKernelEquiv
     :
    rectangleDualPotentialCurlKernel a w h A ≃ₗ[ℝ]
      LinearMap.ker (signedDivergence (rectangleGraph a w h)
        (rectangleConfigurationOfCarrier a w h A)
        (rectangleOpenEdgeOrientation a w h (rectangleConfigurationOfCarrier a w h A))) :=
  (rectangleDualCurlKernelOpenLinearEquiv a w h A).trans
    (rectangleOpenFlowDivergenceKernelEquiv a w h (rectangleConfigurationOfCarrier a w h A)).symm

theorem rectangleDualComponentCount_eq_potentialFinrank_add_one
     :
    componentCount (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h A) =
      Module.finrank ℝ (rectangleDualPotentialCurlKernel a w h A) + 1 :=
  (rectangleDualPotentialCurlKernel_finrank_add_one a w h A).symm

 theorem rectangleEuler_additive  :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h)))
          (rectangleConfigurationOfCarrier a w h A) + 1 := by
  have heq := (rectangleDualPotentialCurlKernelSignedKernelEquiv a w h A).finrank_eq
  have hpot := rectangleDualComponentCount_eq_potentialFinrank_add_one a w h A
  calc
    componentCount (rectangleDualGraph a w h) (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A) + Fintype.card (RectangleVertex a w h) =
        (Module.finrank ℝ (rectangleDualPotentialCurlKernel a w h A) + 1) +
          Fintype.card (RectangleVertex a w h) := by omega
    _ = Module.finrank ℝ (LinearMap.ker
        (signedDivergence (rectangleGraph a w h)
          (rectangleConfigurationOfCarrier a w h A)
          (rectangleOpenEdgeOrientation a w h (rectangleConfigurationOfCarrier a w h A)))) +
          Fintype.card (RectangleVertex a w h) + 1 := by omega
    _ = A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h)))
          (rectangleConfigurationOfCarrier a w h A) + 1 := by
      rw [(rectangleSignedFlowDimension a w h (rectangleConfigurationOfCarrier a w h A))]
      rfl
end

section
variable (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
theorem rectangleEuler_additive_config  :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (rectangleCarrierOfConfiguration a w h A)) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := by
  have hEuler := rectangleEuler_additive a w h (rectangleCarrierOfConfiguration a w h A)
  tauto

 theorem rectangleEuler_additive_card_config  :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (rectangleCarrierOfConfiguration a w h A)) +
        (w + 1) * (h + 1) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := by
  rw [← card_rectangleVertex a w h]
  grind [rectangleEuler_additive_config]
end

end
end PottsDiscontinuity.FK
