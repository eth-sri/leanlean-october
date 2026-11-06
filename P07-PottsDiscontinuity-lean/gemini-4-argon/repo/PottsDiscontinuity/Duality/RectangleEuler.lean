module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import PottsDiscontinuity.Duality.RectangleDualPotential
public import PottsDiscontinuity.Duality.RectangleOpenFlow

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

def rectangleConfigurationOfCarrier (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleGraph a w h) := A

def rectangleCarrierOfConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier a w h) := A

abbrev rectangleOpenDivSpace (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :=
  @Min.min (Submodule ℝ (RectanglePrimalFlow a w h)) inferInstance
    (rectangleOpenFlowSubmodule a w h (rectangleConfigurationOfCarrier a w h A))
    (rectangleDivergenceFreeFlowSubmodule a w h)

theorem rectangleDualCurlKernel_openSupport
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (φ : rectangleDualPotentialCurlKernel a w h A)
    (b : RectanglePrimalBond a w h)
    (hb : rectanglePrimalBondToEdge a w h b ∉ A) :
    rectanglePotentialCurlMap a w h φ.1 b = 0 := by
  let e := rectanglePrimalBondToEdge a w h b
  have hzero := φ.2 e hb
  have heq : rectanglePrimalEdgeBond_mem a w h e = b :=
    (rectanglePrimalEdgeBondEquiv a w h).right_inv b
  rwa [heq] at hzero

theorem rectangleOpenFlow_mem_curlKernel
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (F : rectangleOpenDivSpace a w h A) :
    (rectanglePotentialCurlLinearEquiv a w h).symm
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩ ∈
      rectangleDualPotentialCurlKernel a w h A := by
  intro e he
  have hclosed : rectanglePrimalBondToEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e) ∉ A := by
    have hedge : rectanglePrimalBondToEdge a w h ((rectanglePrimalEdgeBondEquiv a w h) e) = e :=
      (rectanglePrimalEdgeBondEquiv a w h).left_inv e
    rwa [hedge]
  have hzero := (Submodule.mem_inf.mp F.2).1
    ((rectanglePrimalEdgeBondEquiv a w h) e) hclosed
  have hF : rectanglePotentialCurlMap a w h
      ((rectanglePotentialCurlLinearEquiv a w h).symm
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩) = F.1 :=
    congrArg Subtype.val ((rectanglePotentialCurlLinearEquiv a w h).apply_symm_apply
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
  change rectanglePotentialCurlMap a w h
    ((rectanglePotentialCurlLinearEquiv a w h).symm
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
    (rectanglePrimalEdgeBondEquiv a w h e) = 0
  rwa [hF]

noncomputable def rectangleDualCurlKernelOpenLinearEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel a w h A ≃ₗ[ℝ]
      rectangleOpenDivSpace a w h A where
  toFun φ := ⟨(rectanglePotentialCurlLinearEquiv a w h φ.1).1,
    Submodule.mem_inf.mpr ⟨fun b hb => rectangleDualCurlKernel_openSupport a w h A φ b hb,
      (rectanglePotentialCurlLinearEquiv a w h φ.1).2⟩⟩
  invFun F := ⟨(rectanglePotentialCurlLinearEquiv a w h).symm ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩,
    rectangleOpenFlow_mem_curlKernel a w h A F⟩
  left_inv φ := by
    apply Subtype.ext
    exact (rectanglePotentialCurlLinearEquiv a w h).left_inv φ.1
  right_inv F := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h
      ((rectanglePotentialCurlLinearEquiv a w h).symm ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)).1 = F.1
    exact congrArg Subtype.val
      ((rectanglePotentialCurlLinearEquiv a w h).apply_symm_apply ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
  map_add' φ ψ := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h (φ.1 + ψ.1)).1 =
      (rectanglePotentialCurlLinearEquiv a w h φ.1).1 + (rectanglePotentialCurlLinearEquiv a w h ψ.1).1
    exact congrArg Subtype.val (map_add (rectanglePotentialCurlLinearEquiv a w h).toLinearMap φ.1 ψ.1)
  map_smul' c φ := by
    apply Subtype.ext
    change (rectanglePotentialCurlLinearEquiv a w h (c • φ.1)).1 =
      c • (rectanglePotentialCurlLinearEquiv a w h φ.1).1
    exact congrArg Subtype.val (map_smul (rectanglePotentialCurlLinearEquiv a w h).toLinearMap c φ.1)

theorem rectangleEuler_additive_card_config (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h (rectangleCarrierOfConfiguration a w h A)) +
        (w + 1) * (h + 1) =
      A.card + componentCount (rectangleGraph a w h)
        (BoundaryCondition.free (∅ : Set (RectangleVertex a w h))) A + 1 := by
  let A' := rectangleCarrierOfConfiguration a w h A
  have hdim := rectangleSignedFlowDimension a w h A
  have heq := ((rectangleDualCurlKernelOpenLinearEquiv a w h A').trans
    (rectangleOpenFlowDivergenceKernelEquiv a w h A).symm).finrank_eq
  have hpot := (rectangleDualPotentialCurlKernel_finrank_add_one a w h A').symm
  rw [← card_rectangleVertex a w h, hpot, heq]
  omega

end
end PottsDiscontinuity.FK
