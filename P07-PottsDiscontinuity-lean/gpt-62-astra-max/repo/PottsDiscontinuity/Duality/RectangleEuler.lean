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

def rectangleConfigurationOfCarrier {a : LatticeVertex} {w h : ℕ}
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleGraph a w h) := A

def rectangleCarrierOfConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Finset (rectanglePrimalEdgeCarrier a w h) := A

abbrev rectangleOpenDivSpace {a : LatticeVertex} {w h : ℕ}
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :=
  @Min.min (Submodule ℝ (RectanglePrimalFlow a w h)) inferInstance
    (rectangleOpenFlowSubmodule a w h (rectangleConfigurationOfCarrier A))
    (rectangleDivergenceFreeFlowSubmodule a w h)

def rectanglePrimalBondSubtype {a : LatticeVertex} {w h : ℕ}
    (e : rectanglePrimalEdgeCarrier a w h) : RectanglePrimalBond a w h :=
  ⟨rectanglePrimalEdgeBond e,
    rectanglePrimalEdgeBond_endpoints_mem_public e⟩

 theorem rectangleDualCurlKernel_openSupport
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (φ : rectangleDualPotentialCurlKernel A)
    (b : RectanglePrimalBond a w h)
    (hb : rectanglePrimalBondToEdge b ∉ A) :
    rectanglePotentialCurlMap a w h φ.1 b = 0 := by
  let e := rectanglePrimalBondToEdge b
  have heq : rectanglePrimalEdgeBondEquiv a w h e = b := (rectanglePrimalEdgeBondEquiv a w h).right_inv b
  have hzero := φ.2 e (by assumption)
  change rectanglePotentialCurlMap a w h φ.1
    (rectanglePrimalBondSubtype e) = 0 at hzero
  have hbond : rectanglePrimalBondSubtype e =
      rectanglePrimalEdgeBondEquiv a w h e := by
    apply Subtype.ext
    rfl
  grind

 theorem rectangleOpenFlow_mem_curlKernel
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (F : rectangleOpenDivSpace A) :
    (rectanglePotentialCurlLinearEquiv a w h).symm
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩ ∈
      rectangleDualPotentialCurlKernel A := by
  intro e he
  let equiv := rectanglePrimalEdgeBondEquiv a w h
  have hclosed : rectanglePrimalBondToEdge
      (equiv e) ∉ A := by
    have hedge : rectanglePrimalBondToEdge
      (equiv e) = e :=
      equiv.left_inv e
    grind
  have hzero := (Submodule.mem_inf.mp F.2).1
    (equiv e) hclosed
  let map := rectanglePotentialCurlMap a w h ((rectanglePotentialCurlLinearEquiv a w h).symm ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
  have hF : map = F.1 := congrArg Subtype.val (LinearEquiv.apply_symm_apply (rectanglePotentialCurlLinearEquiv a w h) ⟨↑F, (Submodule.mem_inf.mp F.property).right⟩)
  have hFedge := congrFun hF (equiv e)
  have hbond : rectanglePrimalBondSubtype e =
      equiv e := by
    apply Subtype.ext
    rfl
  change map
    (rectanglePrimalBondSubtype e) = 0
  grind

def rectangleDualCurlKernelToOpenIntersection
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel A →ₗ[ℝ]
      rectangleOpenDivSpace A where
  toFun φ := by
    refine ⟨(rectanglePotentialCurlLinearEquiv a w h φ.1).1, ?_⟩
    apply Submodule.mem_inf.mpr
    constructor
    · intro b hb
      exact rectangleDualCurlKernel_openSupport a w h A φ b hb
    · exact (rectanglePotentialCurlLinearEquiv a w h φ.1).2
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
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    (rectangleOpenDivSpace A) →ₗ[ℝ]
      rectangleDualPotentialCurlKernel A where
  toFun F := by
    let d : rectangleDivergenceFreeFlowSubmodule a w h :=
      ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩
    refine ⟨(rectanglePotentialCurlLinearEquiv a w h).symm d, ?_⟩
    exact rectangleOpenFlow_mem_curlKernel a w h A F
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
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Function.Bijective (rectangleDualCurlKernelToOpenIntersection a w h A) := by
  constructor
  · intro φ ψ hxy
    have hflow := congrArg Subtype.val hxy
    apply Subtype.ext
    apply (rectanglePotentialCurlLinearEquiv a w h).injective
    exact Subtype.ext hflow
  · intro F
    refine ⟨rectangleOpenIntersectionToDualCurlKernel a w h A F, ?_⟩
    apply Subtype.ext
    have hval := congrArg Subtype.val
      ((rectanglePotentialCurlLinearEquiv a w h).apply_symm_apply
        ⟨F.1, (Submodule.mem_inf.mp F.2).2⟩)
    exact hval

noncomputable def rectangleDualCurlKernelOpenLinearEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel A ≃ₗ[ℝ]
      rectangleOpenDivSpace A :=
  LinearEquiv.ofBijective _
    (rectangleDualCurlKernelOpenEquiv_bijective a w h A)

noncomputable def rectangleDualPotentialCurlKernelSignedKernelEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel A ≃ₗ[ℝ]
      LinearMap.ker (signedDivergence (rectangleGraph a w h)
        (rectangleConfigurationOfCarrier A)
        (rectangleOpenEdgeOrientation (rectangleConfigurationOfCarrier A))) :=
  (rectangleDualCurlKernelOpenLinearEquiv a w h A).trans
    (rectangleOpenFlowDivergenceKernelEquiv a w h _).symm

private theorem rectangleDualComponentCount_eq_potentialFinrank_add_one
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    componentCount
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration A) =
      Module.finrank ℝ (rectangleDualPotentialCurlKernel A) + 1 := (rectangleDualPotentialCurlKernel_finrank_add_one a w h A).symm

 theorem rectangleEuler_additive (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    componentCount
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration A) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount
        (BoundaryCondition.free (∅))
          (rectangleConfigurationOfCarrier A) + 1 := by
  have heq := (rectangleDualPotentialCurlKernelSignedKernelEquiv a w h A).finrank_eq
  have hpot := rectangleDualComponentCount_eq_potentialFinrank_add_one a w h A
  calc
    _ =
        (Module.finrank ℝ (rectangleDualPotentialCurlKernel A) + 1) +
          Fintype.card (RectangleVertex a w h) := by grind
    _ = Module.finrank ℝ (LinearMap.ker
        (signedDivergence _
          _
          (rectangleOpenEdgeOrientation (rectangleConfigurationOfCarrier A)))) +
          Fintype.card (RectangleVertex a w h) + 1 := by grind
    _ = _ := by
      rw [(rectangleSignedFlowDimension a w h _)]
      rfl

theorem rectangleEuler_additive_config (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    componentCount
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration (rectangleCarrierOfConfiguration a w h A)) +
        Fintype.card (RectangleVertex a w h) =
      A.card + componentCount
        (BoundaryCondition.free (∅)) A + 1 := rectangleEuler_additive a w h _

 theorem rectangleEuler_additive_card_config (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    componentCount
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration (rectangleCarrierOfConfiguration a w h A)) +
        (w + 1) * (h + 1) =
      A.card + componentCount
        (BoundaryCondition.free (∅)) A + 1 := by
  rw [← card_rectangleVertex a w h]
  exact rectangleEuler_additive_config a w h A

end
end PottsDiscontinuity.FK
