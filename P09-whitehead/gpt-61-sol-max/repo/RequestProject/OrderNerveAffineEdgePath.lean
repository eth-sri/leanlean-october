import Mathlib.Tactic

import RequestProject.OrderNerveRealizationContraction
import RequestProject.OrderNerveFiniteCoordinates
import RequestProject.OrderNerveRealizationMapCoordinates
import RequestProject.SimpleLoopBoundaryHomeomorph

/-! Explicit affine paths along actual realization edges, with exact
barycentric coordinates and injectivity. Unlike an arbitrary chosen path
inside a simplex, these paths parametrize each edge exactly once.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial

variable {P : Type} [PartialOrder P]

def affineEdgeSimplex {a b : P} (h : a ≤ b)  := ComposableArrows.mk₁ (homOfLE h)

def affineEdgeEndpoint {a b : P} (h : a ≤ b) (i : Fin 2)  :=
  Classical.choose (orderNerveRealizationVertex_mem_simplex (affineEdgeSimplex h) i)

theorem affineEdgeEndpoint_spec {a b : P} (h : a ≤ b) (i : Fin 2) :
    orderNerveRealizationSimplex P (affineEdgeSimplex h) (affineEdgeEndpoint h i) =
      orderNerveRealizationVertex ((affineEdgeSimplex h).obj i) :=
  Classical.choose_spec (orderNerveRealizationVertex_mem_simplex (affineEdgeSimplex h) i)

def orderNerveAffineEdgePath {a b : P} (h : a ≤ b) :
    Path (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) where
  toFun t := orderNerveRealizationSimplex P (affineEdgeSimplex h)
    (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))
  continuous_toFun := (orderNerveRealizationSimplex P (affineEdgeSimplex h)).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp (continuous_id.prodMk
      (continuous_const.prodMk continuous_const)))
  source' := by
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
    simp
    rfl
  target' := by
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
    simp
    rfl

theorem orderNerveAffineEdgePath_coordinates {a b : P} (h : a ≤ b) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveAffineEdgePath h t) p =
      (1 - (t : ℝ)) * (if a = p then 1 else 0) + (t : ℝ) * (if b = p then 1 else 0) := by
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (affineEdgeSimplex h)
      (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))) p = _
  rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
  simp [orderNerveRealizationCoordinates_vertex]
  rfl

def orderNerveComparablePath {a b : P} (h : a ≤ b ∨ b ≤ a)  :=
  if hab : a ≤ b then orderNerveAffineEdgePath hab
  else (orderNerveAffineEdgePath (h.resolve_left hab)).symm

theorem orderNerveComparablePath_coordinates {a b : P} (h : a ≤ b ∨ b ≤ a) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveComparablePath h t) p =
      (1 - (t : ℝ)) * (if a = p then 1 else 0) + (t : ℝ) * (if b = p then 1 else 0) := by
  classical aesop (add simp [orderNerveComparablePath, Path.symm_apply, orderNerveAffineEdgePath_coordinates, unitInterval.coe_symm_eq])

variable (v : P → ℝ)
theorem orderNerveAffineRealization_vertex  (p : P) :
    orderNerveAffineRealization v (orderNerveRealizationVertex p) = v p := by
  have h := congrArg (fun k => k (default : SimplexCategory.toTop.{0}.obj ⦋0⦌))
    (orderNerveAffineRealization_simplex v (n := ⦋0⦌) (ComposableArrows.mk₀ p))
  aesop (add simp [orderNerveAffineSimplex])

theorem orderNerveAffineEdgePath_affine  {a b : P}
    (h : a ≤ b) (t : I) :
    orderNerveAffineRealization v (orderNerveAffineEdgePath h t) =
      (1 - (t : ℝ)) * v a + (t : ℝ) * v b := by
  have hs (z : SimplexCategory.toTop.obj ⦋1⦌) := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex v (affineEdgeSimplex h))
  change ∀ z, orderNerveAffineRealization v
    (orderNerveRealizationSimplex P (affineEdgeSimplex h) z) =
      orderNerveAffineSimplex v (affineEdgeSimplex h) z at hs
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P (affineEdgeSimplex h)
    (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))) = _
  rw [hs, orderNerveAffineSimplex_blend, ← hs, ← hs,
    affineEdgeEndpoint_spec, affineEdgeEndpoint_spec,
    orderNerveAffineRealization_vertex, orderNerveAffineRealization_vertex]
  rfl

theorem orderNerveComparablePath_affine  {a b : P}
    (h : a ≤ b ∨ b ≤ a) (t : I) :
    orderNerveAffineRealization v (orderNerveComparablePath h t) =
      (1 - (t : ℝ)) * v a + (t : ℝ) * v b := by
  classical grind [orderNerveComparablePath, orderNerveAffineEdgePath_affine]

/-- Collapsing vertices is allowed: the affine path formula is natural for
every monotone map, including the actual letter-reading map. -/
theorem orderNerveComparablePath_natural {Q : Type} [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) {a b : P} (h : a ≤ b ∨ b ≤ a)
    (h' : f a ≤ f b ∨ f b ≤ f a) (t : I) :
    orderNerveRealizationMap f hf (orderNerveComparablePath h t) =
      orderNerveComparablePath h' t := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  change orderNerveAffineRealization (fun z => if z = q then 1 else 0)
    (orderNerveRealizationMap f hf (orderNerveComparablePath h t)) = _
  rw [orderNerveAffineRealization_natural, orderNerveComparablePath_affine,
    orderNerveComparablePath_coordinates]
  rfl

theorem orderNerveComparablePath_injective {a b : P} (h : a ≤ b ∨ b ≤ a) (hne : a ≠ b) :
    Function.Injective (orderNerveComparablePath h) := by
  intro s t hst
  have hcoord := congrArg (fun x => orderNerveRealizationCoordinates P x b) hst
  simp [orderNerveComparablePath_coordinates, if_neg hne] at hcoord
  exact Subtype.ext hcoord

theorem orderNerveComparablePath_of_support [Fintype P] {a b : P}
    (h : a ≤ b ∨ b ≤ a) (hne : a ≠ b) (x : orderNerveRealization P)
    (hx : ∀ p, p ≠ a → p ≠ b → orderNerveRealizationCoordinates P x p = 0) :
    ∃ t : I, orderNerveComparablePath h t = x := by
  let c := orderNerveRealizationCoordinates P x
  have hsum : c a + c b = 1 := by
    calc
      c a + c b = ∑ p ∈ ({a, b} : Finset P), c p := by simp [hne]
      _ = ∑ p : P, c p := by
        apply Finset.sum_subset (Finset.subset_univ _)
        aesop
      _ = 1 := orderNerveRealizationCoordinates_sum x
  have ha := orderNerveRealizationCoordinates_nonneg x a
  have hb := orderNerveRealizationCoordinates_nonneg x b
  let t : I := ⟨c b, hb, by dsimp [c] at hsum ⊢; linarith⟩
  refine ⟨t, ?_⟩
  apply orderNerveRealizationCoordinates_injective P
  funext p
  rw [orderNerveComparablePath_coordinates]
  grind

end FiniteChains.Comb
