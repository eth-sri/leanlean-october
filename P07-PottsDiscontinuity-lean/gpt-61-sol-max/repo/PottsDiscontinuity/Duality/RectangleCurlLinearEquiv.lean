/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

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
    simp_all
  smul_mem' := by
    simp_all

private def rectanglePotentialAsExterior (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) : RectangleExteriorPotential a w h :=
  ⟨φ.1, φ.2⟩

private theorem rectanglePrimalFlowDivergence_add
    (a : LatticeVertex) (w h : ℕ) (F G : RectanglePrimalBond a w h → ℝ)
    (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h (F + G) v =
      rectanglePrimalFlowDivergence a w h F v + rectanglePrimalFlowDivergence a w h G v := by
  
  unfold rectanglePrimalFlowDivergence
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  grind

private theorem rectanglePrimalFlowDivergence_smul
    (a : LatticeVertex) (w h : ℕ) (c : ℝ) (F : RectanglePrimalBond a w h → ℝ)
    (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h (c • F) v =
      c * rectanglePrimalFlowDivergence a w h F v := by
  
  
  
  calc
    (∑ b : rectangleActualIncidentBonds a w h v,
      if b.1.1.source = v then c * F b.1 else -(c * F b.1)) =
        ∑ b : rectangleActualIncidentBonds a w h v,
          c *  if b.1.1.source = v then F b.1 else -F b.1  := by
            simp_all
    _ = c * ∑ b : rectangleActualIncidentBonds a w h v,
           if b.1.1.source = v then F b.1 else -F b.1  := by
            rw [Finset.mul_sum]

/-- Actual rectangle flows whose incidence divergence vanishes at every
primal rectangle vertex. -/
def rectangleDivergenceFreeFlowSubmodule (a : LatticeVertex) (w h : ℕ) :
    Submodule ℝ (RectanglePrimalBond a w h → ℝ) where
  carrier := {F | ∀ v, v ∈ latticeRectangle a w h →
    rectanglePrimalFlowDivergence a w h F v = 0}
  zero_mem' := by
    intro v hv
    simp [rectanglePrimalFlowDivergence]
  add_mem' := by
    simp_all [rectanglePrimalFlowDivergence_add]
  smul_mem' := by
    simp_all [rectanglePrimalFlowDivergence_smul]

def rectanglePotentialExtendedLinear (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex)  :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

private theorem rectanglePotentialExtendedLinear_add (a : LatticeVertex) (w h : ℕ)
    (φ ψ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) :
    rectanglePotentialExtendedLinear a w h (φ + ψ) z =
      rectanglePotentialExtendedLinear a w h φ z +
        rectanglePotentialExtendedLinear a w h ψ z := by
  by_cases hz : z ∈ rectangleDualExpanded a w h <;>
    simp [rectanglePotentialExtendedLinear, hz]

private theorem rectanglePotentialExtendedLinear_smul (a : LatticeVertex) (w h : ℕ)
    (c : ℝ) (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) :
    rectanglePotentialExtendedLinear a w h (c • φ) z =
      c * rectanglePotentialExtendedLinear a w h φ z := by
  by_cases hz : z ∈ rectangleDualExpanded a w h <;>
    simp [rectanglePotentialExtendedLinear]

def rectanglePotentialCurlValue (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) (b : LatticeBond) : ℝ :=
  match b.axis with
  | .horizontal => rectanglePotentialExtendedLinear a w h φ (b.faceBase true) -
      rectanglePotentialExtendedLinear a w h φ (b.faceBase false)
  | .vertical => rectanglePotentialExtendedLinear a w h φ (b.faceBase false) -
      rectanglePotentialExtendedLinear a w h φ (b.faceBase true)

private theorem rectanglePotentialCurlValue_eq_flow (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) (b : LatticeBond) :
    rectanglePotentialCurlValue a w h φ b =
      rectangleCurlFlow a w h (rectanglePotentialAsExterior a w h φ) b := by
  cases b.axis <;> rfl

/-- Curl as a linear map from zero-exterior potentials into all actual
rectangle-edge flows. -/
def rectanglePotentialCurlMap (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ]
       RectanglePrimalBond a w h → ℝ  where
  toFun φ b := rectanglePotentialCurlValue a w h φ b.1
  map_add' φ ψ := by
    funext b
    cases hax : b.1.axis
    · simp only [rectanglePotentialCurlValue, hax, Pi.add_apply]
      rw [rectanglePotentialExtendedLinear_add, rectanglePotentialExtendedLinear_add]
      abel
    · simp only [rectanglePotentialCurlValue, hax, Pi.add_apply]
      rw [rectanglePotentialExtendedLinear_add, rectanglePotentialExtendedLinear_add]
      abel
  map_smul' c φ := by
    funext b
    cases hax : b.1.axis
    · simp only [rectanglePotentialCurlValue, hax, Pi.smul_apply]
      rw [rectanglePotentialExtendedLinear_smul, rectanglePotentialExtendedLinear_smul]
      simp only [RingHom.id_apply]
      ring
    · simp only [rectanglePotentialCurlValue, hax, Pi.smul_apply]
      rw [rectanglePotentialExtendedLinear_smul, rectanglePotentialExtendedLinear_smul]
      simp only [RingHom.id_apply]
      ring

 theorem rectanglePotentialCurlMap_mem_divergenceFree
    (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) :
    rectanglePotentialCurlMap a w h φ ∈ rectangleDivergenceFreeFlowSubmodule a w h := by
                                                                                        solve_by_elim [_root_.congrArg, _root_.funext, _root_.PottsDiscontinuity.FK.rectanglePotentialCurlValue_eq_flow, _root_.PottsDiscontinuity.FK.rectanglePrimalCurlDivergence_eq_zero]

/-- The actual curl map with its mathematically proved divergence-free range. -/
def rectanglePotentialCurlIntoDivergenceFree (a : LatticeVertex) (w h : ℕ) :
    rectangleExteriorPotentialSubmodule a w h →ₗ[ℝ]
      rectangleDivergenceFreeFlowSubmodule a w h where
  toFun φ := ⟨rectanglePotentialCurlMap a w h φ,
    rectanglePotentialCurlMap_mem_divergenceFree a w h φ⟩
  map_add' φ ψ := by
    simp_all
  map_smul' c φ := by
    simp_all

section

variable (a : LatticeVertex)
include a

private theorem rectanglePotential_bottomFace_boundary
     (w h n : ℕ) (hn : n < w) :
    rectangleFlowVertex a (n : ℤ) (-1) ∈ rectangleDualBoundary a w h := by
  grind [rectangleDualBoundary, rectangleDualInterior, rectangleDualExpanded, latticeRectangle, rectangleFlowVertex,
    rectangleFlowX, rectangleFlowY]

section

variable (w h : ℕ)
include w h

private theorem rectangleExtendedPotential_zero_of_boundary
      (φ : RectangleExteriorPotential a w h)
    (z : LatticeVertex) (hz : z ∈ rectangleDualBoundary a w h) :
    rectangleExtendedPotential a w h φ z = 0 := by
  rw [rectangleExtendedPotential_of_mem a w h φ z (Finset.mem_filter.mp hz).1]
  aesop

section

variable (φ ψ : RectangleExteriorPotential a w h) (hcurl : ∀ b : RectanglePrimalBond a w h,
      rectangleCurlFlow a w h φ b.1 = rectangleCurlFlow a w h ψ b.1)
include hcurl

private theorem rectangleExteriorPotential_ext_atInterior
     
    
    (n m : ℕ) (hn : n < w) (hm : m < h) :
    rectangleExtendedPotential a w h φ (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      rectangleExtendedPotential a w h ψ (rectangleFlowVertex a (n : ℤ) (m : ℤ)) := by
  
  have hrow (j : ℕ) (hj : j < h) :
      rectangleExtendedPotential a w h φ (rectangleFlowVertex a n j) =
        rectangleExtendedPotential a w h ψ (rectangleFlowVertex a n j) := by
    induction j with
    | zero =>
        have hc := hcurl ⟨⟨rectangleFlowVertex a n 0, .horizontal⟩,
           fun j hj => by
             constructor <;> rw [mem_latticeRectangle] <;>
               simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY,
                 LatticeBond.source, LatticeBond.target] <;> omega  0 hj⟩
        simp [rectangleCurlFlow, LatticeBond.faceBase, rectangleFlowVertex,
          rectangleFlowX, rectangleFlowY] at hc
        
        have hbd := rectanglePotential_bottomFace_boundary a w h n hn
        have hbd' : (a.1 +  n , a.2 - 1) ∈ rectangleDualBoundary a w h := by
          
          exact hbd
        have hφbot := rectangleExtendedPotential_zero_of_boundary a w h φ _ hbd'
        have hψbot := rectangleExtendedPotential_zero_of_boundary a w h ψ _ hbd'
        rw [hφbot, hψbot] at hc
        simpa [rectangleFlowVertex, rectangleFlowX, rectangleFlowY] using hc
    | succ j ih =>
        have hc := hcurl ⟨⟨rectangleFlowVertex a n j.succ, .horizontal⟩,
           fun j hj => by
             constructor <;> rw [mem_latticeRectangle] <;>
               simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY,
                 LatticeBond.source, LatticeBond.target] <;> omega  j.succ hj⟩
        simp [rectangleCurlFlow, LatticeBond.faceBase, rectangleFlowX, rectangleFlowY] at hc
        have htop : (a.1 +  n , a.2 + ( j  + 1)) =
            rectangleFlowVertex a n j.succ := by
          rfl
        have hbottom : (a.1 +  n , a.2 + ( j  + 1) - 1) =
            rectangleFlowVertex a n j := by
          grind [rectangleFlowVertex, rectangleFlowY]
        grind
  exact hrow m hm

private theorem rectangleExteriorPotential_ext_of_curl_eq
     
     :
    φ = ψ := by
  apply Subtype.ext
  funext z
  by_cases hI : z.1 ∈ rectangleDualInterior a w h
  · have hprop := (Finset.mem_filter.mp hI).2
    let n  := (z.1.1 - a.1).toNat
    let m  := (z.1.2 - a.2).toNat
    
    
    
    
    
    
    have hcoords : z.1 = rectangleFlowVertex a n m := by
      grind [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    have hp := rectangleExteriorPotential_ext_atInterior a w h φ ψ hcurl n m (by omega) (by omega)
    
    have hexV : rectangleFlowVertex a n m ∈ rectangleDualExpanded a w h := by
      grind
    have hsub : z = ⟨rectangleFlowVertex a n m, hexV⟩ := Subtype.ext hcoords
    rw [rectangleExtendedPotential_of_mem a w h φ _ hexV,
      rectangleExtendedPotential_of_mem a w h ψ _ hexV] at hp
    rw [hsub]
    exact hp
  · grind [rectangleDualBoundary]

end

/-- Curl determines a zero-exterior potential uniquely by row-wise recurrence
from the lower wired boundary. -/
theorem rectanglePotentialCurlMap_injective   :
    Function.Injective (rectanglePotentialCurlMap a w h) := by
  intro φ ψ hφψ
  
  apply Subtype.ext
  exact congrArg Subtype.val (rectangleExteriorPotential_ext_of_curl_eq a w h
                                (rectanglePotentialAsExterior a w h φ) (rectanglePotentialAsExterior a w h ψ) (by
                                  intro b
                                  have hb := congrFun hφψ b
                                  change rectanglePotentialCurlValue a w h φ b.1 =
                                    rectanglePotentialCurlValue a w h ψ b.1 at hb
                                  aesop))

 theorem rectanglePotentialCurlInto_injective
      :
    Function.Injective (rectanglePotentialCurlIntoDivergenceFree a w h) := by
  intro φ ψ hφψ
  apply rectanglePotentialCurlMap_injective a w h
  exact congrArg Subtype.val hφψ

 theorem rectanglePotentialCurlInto_surjective
      :
    Function.Surjective (rectanglePotentialCurlIntoDivergenceFree a w h) := by
  solve_by_elim [_root_.PottsDiscontinuity.FK.rectangleFlowExteriorPotential_curl_eq_flow, _root_.Exists.intro,
    _root_.Subtype.ext, _root_.funext]

end

end

/-- The finite discrete-curl map is a genuine linear equivalence between
zero-exterior dual potentials and divergence-free flows on actual rectangle
edges. -/
noncomputable def rectanglePotentialCurlLinearEquiv (a : LatticeVertex) (w h : ℕ)  :=
  LinearEquiv.ofBijective (rectanglePotentialCurlIntoDivergenceFree a w h)
    ⟨rectanglePotentialCurlInto_injective a w h,
      rectanglePotentialCurlInto_surjective a w h⟩

end PottsDiscontinuity.FK
