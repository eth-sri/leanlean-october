/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleFlowIntegration
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

/-- Zero-exterior dual potentials as an actual linear subspace of all
expanded-face functions. -/
def rectangleExteriorPotentialSubmodule (a : LatticeVertex) (w h : ℕ) :
    Submodule ℝ (RectangleDualVertex a w h → ℝ) where
  carrier := {φ | ∀ z, z.1 ∈ rectangleDualBoundary a w h → φ z = 0}
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ z hz
    simp [hφ z hz, hψ z hz]
  smul_mem' := by
    intro c φ hφ z hz
    simp [hφ z hz]

def rectanglePotentialAsExterior (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) : RectangleExteriorPotential a w h :=
  ⟨φ.1, φ.2⟩

private lemma divergence_add {a : LatticeVertex} {w h : ℕ} (F G : RectanglePrimalFlow a w h) (z : LatticeVertex) :
    rectanglePrimalFlowDivergence (F+G) z = rectanglePrimalFlowDivergence F z + rectanglePrimalFlowDivergence G z := by
  simp only [rectanglePrimalFlowDivergence,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl
  intro b _; split_ifs <;> (try simp) <;> ring
private lemma divergence_smul {a : LatticeVertex} {w h : ℕ} (c : ℝ) (F : RectanglePrimalFlow a w h) (z : LatticeVertex) :
    rectanglePrimalFlowDivergence (c • F) z = c * rectanglePrimalFlowDivergence F z := by
  simp only [rectanglePrimalFlowDivergence,Finset.mul_sum]; apply Finset.sum_congr rfl
  intro b _; split_ifs <;> (try simp) <;> ring

/-- Actual rectangle flows whose incidence divergence vanishes at every
primal rectangle vertex. -/
def rectangleDivergenceFreeFlowSubmodule (a : LatticeVertex) (w h : ℕ) :
    Submodule ℝ (RectanglePrimalBond a w h → ℝ) where
  carrier := {F | ∀ v, v ∈ latticeRectangle a w h →
    rectanglePrimalFlowDivergence F v = 0}
  zero_mem' := by
    intro v hv
    simp [rectanglePrimalFlowDivergence]
  add_mem' := by
    intro F G hF hG v hv
    rw [divergence_add, hF v hv, hG v hv]
    ring
  smul_mem' := by
    intro c F hF v hv
    rw [divergence_smul, hF v hv]
    ring

/-- Curl of a potential on the wired dual, extended by zero. -/
def rectanglePotentialCurlMap (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ] RectanglePrimalFlow a w h where
  toFun φ b := rectangleCurlFlow (rectanglePotentialAsExterior a w h φ) b.val
  map_add' φ ψ := by
    funext b; cases ha : b.val.axis <;> simp [rectangleCurlFlow, ha,rectangleExtendedPotential,rectanglePotentialAsExterior] <;> split_ifs <;> (try simp) <;> ring
  map_smul' c φ := by
    funext b; cases ha : b.val.axis <;> simp [rectangleCurlFlow, ha,rectangleExtendedPotential,rectanglePotentialAsExterior] <;> split_ifs <;> (try simp) <;> ring

 theorem rectanglePotentialCurlMap_mem_divergenceFree
    (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) :
    rectanglePotentialCurlMap a w h φ ∈ rectangleDivergenceFreeFlowSubmodule a w h := by
  rintro ⟨x,y⟩ _
  let ψ := rectanglePotentialAsExterior a w h φ
  change rectanglePrimalFlowDivergence (fun b => rectangleCurlFlow ψ b.val) (x,y) = 0
  rw [divergence_stencil]
  simp only [hor,vert,extended_curl]
  simp only [rectangleCurlFlow,LatticeBond.faceBase]
  ring

/-- The actual curl map with its mathematically proved divergence-free range. -/
def rectanglePotentialCurlIntoDivergenceFree (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ]
      rectangleDivergenceFreeFlowSubmodule a w h where
  toFun φ := ⟨rectanglePotentialCurlMap a w h φ,
    rectanglePotentialCurlMap_mem_divergenceFree a w h φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    exact map_add (rectanglePotentialCurlMap a w h) φ ψ
  map_smul' c φ := by
    apply Subtype.ext
    exact map_smul (rectanglePotentialCurlMap a w h) c φ

theorem rectanglePotentialCurlInto_injective (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectanglePotentialCurlIntoDivergenceFree a w h) := by
  intro φ ψ hφψ
  let P := rectangleExtendedPotential (rectanglePotentialAsExterior a w h φ)
  let Q := rectangleExtendedPotential (rectanglePotentialAsExterior a w h ψ)
  have he := congrArg Subtype.val hφψ
  have hd (x y : ℤ) : P (x-1,y)-P (x,y) = Q (x-1,y)-Q (x,y) := by
    have hz := congrArg (fun F : RectanglePrimalFlow a w h => vert F x y) he
    change vert (fun b => rectangleCurlFlow (rectanglePotentialAsExterior a w h φ) b.val) x y =
      vert (fun b => rectangleCurlFlow (rectanglePotentialAsExterior a w h ψ) b.val) x y at hz
    simp only [vert,extended_curl] at hz
    simpa [P,Q,rectangleCurlFlow,LatticeBond.faceBase] using hz
  apply Subtype.ext; funext z
  let g i := P (i,z.val.2) - Q (i,z.val.2)
  have hh := period_one_const (f := g) (fun i => by dsimp [g]; linarith [hd i z.val.2]) z.val.1 (a.1-2)
  have hout : (a.1-2,z.val.2) ∉ rectangleDualExpanded a w h := by
    simp [rectangleDualExpanded,mem_latticeRectangle]; omega
  simpa [g,P,Q,rectangleExtendedPotential,z.property,hout,rectanglePotentialAsExterior,sub_eq_zero] using hh

theorem rectanglePotentialCurlInto_surjective (a : LatticeVertex) (w h : ℕ) :
    Function.Surjective (rectanglePotentialCurlIntoDivergenceFree a w h) := by
  intro F
  let φ := flowPotential F.val F.property
  refine ⟨⟨φ.val,φ.property⟩,Subtype.ext (funext (curl_flowPotential F.val F.property))⟩

/-- The finite discrete-curl map is a genuine linear equivalence between
zero-exterior dual potentials and divergence-free flows on actual rectangle
edges. -/
noncomputable def rectanglePotentialCurlLinearEquiv (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h ≃ₗ[ℝ]
      rectangleDivergenceFreeFlowSubmodule a w h :=
  LinearEquiv.ofBijective _
    ⟨rectanglePotentialCurlInto_injective a w h,
      rectanglePotentialCurlInto_surjective a w h⟩

end PottsDiscontinuity.FK
