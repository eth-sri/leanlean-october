module

public import RequestProject.QCubeThreeFaceIndex
public import RequestProject.GenusCollapseIteration
public import RequestProject.GenusUniversalPolygonTransport
public import RequestProject.CylinderPi1Surjective
public import RequestProject.OrderNerveCommonSimplex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import RequestProject.GenusQuotientRelativeSupport
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import RequestProject.PresPosetReading
public import RequestProject.OrderNerveOneDecoding
public import Mathlib
public import Mathlib.Topology.UnitInterval
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import RequestProject.CombPi1
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.CategoryTheory.Whiskering
public import RequestProject.Statement
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.LinearMapPiProd
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.QuasiIso
public import RequestProject.GenusLoops
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section
noncomputable section
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeFaceSquare_zero_small (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s, t) := by
  ext
  rw [qSquareSmallFacet_ordered _ hvw
    (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s)]
  rfl

theorem qThreeFaceSquare_zero_large (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s, t) := by
  ext
  rw [qSquareLargeFacet_ordered _ hvw
    (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s)]
  rfl

theorem qThreeFaceSquare_one_small (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s, t) := by
  ext
  have h21 : 2 ≠ 1 := by decide
  have hspx := threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs (1, s)).1 =
      qCubeFacet c v s := by
    simp [qThreeFaceSquare, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection]
  rw [qSquareSmallFacet_ordered _ (hvw.trans huv) (hval.symm ▸ hspx), hval]
  rfl

theorem qThreeFaceSquare_one_large (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, t, s) := by
  ext
  have h21 : 2 ≠ 1 := by decide
  have hspx := threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs (1, s)).1 =
      qCubeFacet c v s := by
    simp [qThreeFaceSquare, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection]
  rw [qSquareLargeFacet_ordered _ (hvw.trans huv) (hval.symm ▸ hspx), hval]
  simpa [qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, h21] using qCubeFacet_comm c huv.ne s t

theorem qThreeFaceSquare_two_small (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, t, s) := by
  ext
  have h21 : 2 ≠ 1 := by decide
  have hspx := threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs (2, s)).1 =
      qCubeFacet c w s := by
    simp [qThreeFaceSquare, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection, h21]
  rw [qSquareSmallFacet_ordered _ (huv) (hval.symm ▸ hspx), hval]
  simpa [qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, h21] using qCubeFacet_comm c hvw.ne s t

theorem qThreeFaceSquare_two_large (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, t, s) := by
  ext
  have h21 : 2 ≠ 1 := by decide
  have hspx := threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs (2, s)).1 =
      qCubeFacet c w s := by
    simp [qThreeFaceSquare, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection, h21]
  rw [qSquareLargeFacet_ordered _ (huv) (hval.symm ▸ hspx), hval]
  simpa [qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, h21] using qCubeFacet_comm c (hvw.trans huv).ne s t

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}


/-- Boundary naturality for every finite chain of actual indexed square facets. -/
theorem qThreeFace_boundary_naturality (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (r : (Fin 3 × ZMod 2) →₀ ℤ) :
    qSquareCubicalBoundary
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) r) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryMatrix r) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r z hr hz => grind
  | single i n =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        qSquareCubicalBoundary, Finsupp.linearCombination_single,
        threeFacetBoundaryMatrix, Finsupp.linearCombination_single, map_smul,
        (show qSquareCubicalFaceBoundary
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs i) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn i) by
          obtain ⟨e, s⟩ := i
          fin_cases e
          · change qSquareCubicalFaceBoundary
              (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
                (Ne.symm hvw.ne) hs (0, s)) =
              Finsupp.lmapDomain ℤ ℤ
                (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
                  (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn (0, s))
            simp only [threeFacetBoundaryColumn, Fin.isValue, reduceIte]
            simp only [map_add, map_sub, map_neg, Finsupp.lmapDomain_apply,
              Finsupp.mapDomain_single, qSquareCubicalFaceBoundary]
            rw [qThreeFaceSquare_zero_small c u v w huv hvw hs s 0,
              qThreeFaceSquare_zero_small c u v w huv hvw hs s 1,
              qThreeFaceSquare_zero_large c u v w huv hvw hs s 0,
              qThreeFaceSquare_zero_large c u v w huv hvw hs s 1]
            abel
          · change qSquareCubicalFaceBoundary
              (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
                (Ne.symm hvw.ne) hs (1, s)) =
              Finsupp.lmapDomain ℤ ℤ
                (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
                  (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn (1, s))
            simp only [threeFacetBoundaryColumn, Fin.isValue,
              show (1 : Fin 3) ≠ 0 by decide, reduceIte]
            simp only [map_add, map_sub, map_neg, Finsupp.lmapDomain_apply,
              Finsupp.mapDomain_single, qSquareCubicalFaceBoundary]
            rw [qThreeFaceSquare_one_small c u v w huv hvw hs s 0,
              qThreeFaceSquare_one_small c u v w huv hvw hs s 1,
              qThreeFaceSquare_one_large c u v w huv hvw hs s 0,
              qThreeFaceSquare_one_large c u v w huv hvw hs s 1]
            abel
          · change qSquareCubicalFaceBoundary
              (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
                (Ne.symm hvw.ne) hs (2, s)) =
              Finsupp.lmapDomain ℤ ℤ
                (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
                  (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn (2, s))
            simp only [threeFacetBoundaryColumn, Fin.isValue,
              show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, reduceIte]
            simp only [map_add, map_sub, map_neg, Finsupp.lmapDomain_apply,
              Finsupp.mapDomain_single, qSquareCubicalFaceBoundary]
            rw [qThreeFaceSquare_two_small c u v w huv hvw hs s 0,
              qThreeFaceSquare_two_small c u v w huv hvw hs s 1,
              qThreeFaceSquare_two_large c u v w huv hvw hs s 0,
              qThreeFaceSquare_two_large c u v w huv hvw hs s 1]
            abel)]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeFace_cycle_coefficients (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (r : (Fin 3 × ZMod 2) →₀ ℤ)
    (hr : qSquareCubicalBoundary
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) r) = 0) :
    ∀ i, r i = r (0, 0) * threeFacetOrientation i := by
  apply threeFacetBoundaryMatrix_kernel
  apply Finsupp.mapDomain_injective
    (qThreeEdge_injective c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
      (Ne.symm hvw.ne) hs)
  rw [Finsupp.mapDomain_zero]
  exact (qThreeFace_boundary_naturality c u v w huv hvw hs r).symm.trans hr

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qThreeOrderedCoordinates (c : QCube A) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    (QSquare A →₀ ℤ) →ₗ[ℤ] ((Fin 3 × ZMod 2) →₀ ℤ) :=
  Finsupp.lcomapDomain (qThreeFaceSquare c u v w huv huw hvw hs) (qThreeFaceSquare_injective c u v w huv huw hvw hs)

/-- The six actual facet coefficients reconstruct every chain supported below the three-cube. -/
theorem qThreeOrderedCoordinates_reconstruct (c : QCube A) (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c) :
    Finsupp.mapDomain (qThreeFaceSquare c u v w huv huw hvw hs) (qThreeOrderedCoordinates c u v w huv huw hvw hs r) = r := by
  apply Finsupp.mapDomain_comapDomain _ (qThreeFaceSquare_injective c u v w huv huw hvw hs)
  intro s hmem
  exact qThreeFaceSquare_exhaustive c u v w huv huw hvw hs s (hr s hmem)

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeOrientedFaces_subdivision (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    qSquareChainSubdivision
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) threeOrientedFaces) =
      cubeThreeSquareBoundary c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs := by
  let f := qThreeFaceSquare c u v w (Ne.symm huv.ne)
    (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs
  have h0 s : qSquareChainSubdivision (Finsupp.single (f (0, s)) 1) =
      cubeSquareSubdivision (qCubeFacet c u s) v w (Ne.symm hvw.ne)
        (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 hvw
      (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s)]
    simp
    rfl
  have h1 s : qSquareChainSubdivision (Finsupp.single (f (1, s)) 1) =
      cubeSquareSubdivision (qCubeFacet c v s) u w (Ne.symm (hvw.trans huv).ne)
        (threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 (hvw.trans huv)
      (threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s)]
    simp
    rfl
  have h2 s : qSquareChainSubdivision (Finsupp.single (f (2, s)) 1) =
      cubeSquareSubdivision (qCubeFacet c w s) u v (Ne.symm huv.ne)
        (threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 huv
      (threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs s)]
    simp
    rfl
  simp only [threeOrientedFaces, map_sub, map_add,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [h0, h0, h1, h1, h2, h2]
  unfold cubeThreeSquareBoundary
  abel

/-- Every actual square cycle supported on a three-cube's facets subdivides to a scalar
multiple of its actual oriented cubical boundary. -/
theorem qThreeFacetCycle_subdivision (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c)
    (hcycle : qSquareCubicalBoundary r = 0) :
    ∃ k : ℤ, qSquareChainSubdivision r = k •
      cubeThreeSquareBoundary c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs := by
  let f := qThreeFaceSquare c u v w (Ne.symm huv.ne)
    (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs
  let z := qThreeOrderedCoordinates c u v w (Ne.symm huv.ne)
    (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs r
  have hrecon : Finsupp.lmapDomain ℤ ℤ f z = r :=
    qThreeOrderedCoordinates_reconstruct c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs r hr
  have hz : qSquareCubicalBoundary (Finsupp.lmapDomain ℤ ℤ f z) = 0 := by
    rwa [hrecon]
  have hcoeff := qThreeFace_cycle_coefficients c u v w huv hvw hs z hz
  have he : z = z (0, 0) • threeOrientedFaces := by
    ext i
    rw [Finsupp.smul_apply, threeOrientedFaces_apply, hcoeff i]
    rfl
  refine ⟨z (0, 0), ?_⟩
  conv_lhs => rw [← hrecon, he, map_smul, map_smul]
  exact congrArg (fun x => z (0, 0) • x) (qThreeOrientedFaces_subdivision c u v w huv hvw hs)

end FiniteChains.Davis

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_component_boundary_scalar (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ k : ℤ, strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)) =
      k • cubeThreeSquareBoundary c u v w (Ne.symm huv.ne)
        (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs := by
  obtain ⟨r, hcycle, hsupport, he⟩ := qCube_three_component_facet_boundary c
    (qCube_three_card c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
      (Ne.symm hvw.ne) hs) y hy hb
  have hr : ∀ s ∈ r.support, s.1 < c := by
    intro s hmem
    obtain ⟨a, ha, h0 | h1⟩ := hsupport s hmem
    · rw [h0]
      exact qCubeFacet_lt c a 0 ha
    · rw [h1]
      exact qCubeFacet_lt c a 1 ha
  obtain ⟨k, hk⟩ := qThreeFacetCycle_subdivision c u v w huv hvw hs r hr
    ((qSquareCubicalBoundary_zero_iff r).mpr hcycle)
  refine ⟨-k, ?_⟩
  simp_all

end FiniteChains.Davis
end

section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem strictThreeChain_top_partition (y : StrictOrdTet (QCube A) →₀ ℤ) :
    y = ∑ c ∈ y.support.image (fun t => t.1.2.2.2),
      y.filter (fun t => t.1.2.2.2 = c) := by
  ext t
  simp
  by_cases ht : y t = 0
  · simp [Finsupp.filter_apply, ht]
  · rw [Finset.sum_eq_single t.1.2.2.2]
    · simp
    · intro c _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_image.mpr
        ⟨t, Finsupp.mem_support_iff.mpr ht, rfl⟩))

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_ordered_frame (c : QCube A) (hc : c.spx.card = 3) :
    ∃ u v w : V, v < u ∧ w < v ∧ c.spx = {u, v, w} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Finset.card_eq_three.mp hc
  have perm (a b d) (hp : ∀ t : V, t = x ∨ t = y ∨ t = z ↔
      t = a ∨ t = b ∨ t = d) : c.spx = {a, b, d} := by
    ext t
    simp only [hs, Finset.mem_insert, Finset.mem_singleton]
    exact hp t
  rcases lt_or_gt_of_ne hxy with hxy | hxy <;>
    rcases lt_or_gt_of_ne hxz with hxz | hxz <;>
    rcases lt_or_gt_of_ne hyz with hyz | hyz
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

abbrev QThreeCube (A : CommRel V) := {c : QCube A // c.spx.card = 3}

def qThreeFrame (c : QThreeCube A) :
    {p : V × V × V // p.2.1 < p.1 ∧ p.2.2 < p.2.1 ∧ c.1.spx = {p.1, p.2.1, p.2.2}} := by
  apply Classical.choice
  obtain ⟨u, v, w, huv, hvw, hs⟩ := qCube_three_ordered_frame c.1 c.2
  exact ⟨⟨(u, v, w), huv, hvw, hs⟩⟩

def qThreeUpper (c : QThreeCube A) : V := (qThreeFrame c).1.1
def qThreeMiddle (c : QThreeCube A) : V := (qThreeFrame c).1.2.1
def qThreeLower (c : QThreeCube A) : V := (qThreeFrame c).1.2.2

theorem qThree_middle_lt_upper (c : QThreeCube A) : qThreeMiddle c < qThreeUpper c :=
  (qThreeFrame c).2.1

theorem qThree_lower_lt_middle (c : QThreeCube A) : qThreeLower c < qThreeMiddle c :=
  (qThreeFrame c).2.2.1

theorem qThree_free_directions (c : QThreeCube A) :
    c.1.spx = {qThreeUpper c, qThreeMiddle c, qThreeLower c} := (qThreeFrame c).2.2.2

def qThreeCubeBoundary (c : QThreeCube A) :
    (strictOrderCx (QCube A)).F →₀ ℤ :=
  cubeThreeSquareBoundary c.1 (qThreeUpper c) (qThreeMiddle c) (qThreeLower c)
    (Ne.symm (qThree_middle_lt_upper c).ne)
    (Ne.symm ((qThree_lower_lt_middle c).trans (qThree_middle_lt_upper c)).ne)
    (Ne.symm (qThree_lower_lt_middle c).ne) (qThree_free_directions c)

def qThreeChainBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ qThreeCubeBoundary

theorem qThreeCube_component_boundary (c : QThreeCube A)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ k : ℤ, strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c.1)) =
      k • qThreeCubeBoundary c :=
  qCube_three_component_boundary_scalar c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) (qThree_free_directions c) y hy hb

end FiniteChains.Davis

section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ, qThreeChainBoundary r = strictOrdBoundary3 y := by
  let S := y.support.image (fun t => t.1.2.2.2)
  have hc c (hmem : c ∈ S) : c.spx.card = 3 := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hmem
    exact (qCube_tetrahedron_dimensions t (hy t ht)).2.2.2
  let C : {c : QCube A // c ∈ S} → QThreeCube A := fun c => ⟨c.1, hc c.1 c.2⟩
  have hex a : ∃ k : ℤ,
      strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = a.1)) =
        k • qThreeCubeBoundary (C a) := qThreeCube_component_boundary (C a) y hy hb
  choose k hk using hex
  refine ⟨∑ a ∈ S.attach, Finsupp.single (C a) (k a), ?_⟩
  rw [map_sum]
  simp only [qThreeChainBoundary, Finsupp.linearCombination_single]
  have hp : strictOrdBoundary3 y = ∑ c ∈ S,
      strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)) := by
    conv_lhs => rw [strictThreeChain_top_partition y]
    rw [map_sum]
  rw [hp, ← Finset.sum_attach S (fun c =>
    strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)))]
  apply Finset.sum_congr rfl
  intro a _
  exact (hk a).symm

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

def qThreeCubicalFaceBoundary (c : QThreeCube A) : QSquare A →₀ ℤ :=
  Finsupp.lmapDomain ℤ ℤ
    (qThreeFaceSquare c.1 (qThreeUpper c) (qThreeMiddle c) (qThreeLower c)
      (Ne.symm (qThree_middle_lt_upper c).ne)
      (Ne.symm ((qThree_lower_lt_middle c).trans (qThree_middle_lt_upper c)).ne)
      (Ne.symm (qThree_lower_lt_middle c).ne) (qThree_free_directions c)) threeOrientedFaces

def qThreeCubicalBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    (QSquare A →₀ ℤ) := Finsupp.linearCombination ℤ qThreeCubicalFaceBoundary

theorem qThreeCubicalFaceBoundary_subdivision (c : QThreeCube A) :
    qSquareChainSubdivision (qThreeCubicalFaceBoundary c) = qThreeCubeBoundary c :=
  qThreeOrientedFaces_subdivision c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) (qThree_free_directions c)

theorem qThreeCubicalBoundary_subdivision (r : QThreeCube A →₀ ℤ) :
    qSquareChainSubdivision (qThreeCubicalBoundary r) = qThreeChainBoundary r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp_all
  | single c n =>
      rw [qThreeCubicalBoundary, Finsupp.linearCombination_single, map_smul,
        qThreeCubicalFaceBoundary_subdivision, qThreeChainBoundary,
        Finsupp.linearCombination_single]

/-- Every strict three-boundary with the stated actual dimension bounds is the subdivision
of an actual finite cubical three-boundary, and coefficient recovery gives that boundary. -/
theorem qCube_three_cubical_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ,
      qSquareChainSubdivision (qThreeCubicalBoundary r) = strictOrdBoundary3 y ∧
      qSquareCycleCoefficients (strictOrdBoundary3 y) = qThreeCubicalBoundary r := by
  obtain ⟨r, hr⟩ := qCube_three_boundary_reconstruction y hy hb
  have he := (qThreeCubicalBoundary_subdivision r).trans hr
  refine ⟨r, he, ?_⟩
  rw [← he, qSquare_coefficients_subdivision]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}


/-- Every coefficient of the actual indexed oriented face chain is the collapse's
ordinary boundary coefficient. -/
theorem qThreeOrientedFaces_coordinate_apply (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (g : Cube V) :
    Finsupp.mapDomain (fun i => qCubeToCoordinate
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs i).1) threeOrientedFaces g =
      cubeBdry (qCubeToCoordinate c) (Sum.inl g) := by
  let f := fun i => qCubeToCoordinate
    (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
      (Ne.symm hvw.ne) hs i).1
  have hinj : Function.Injective f := by
    intro i j h
    apply qThreeFaceSquare_injective c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs
    exact Subtype.ext (qCubeToCoordinate_injective h)
  by_cases hg : g ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hg
    rw [Finsupp.mapDomain_apply_of_injective hinj, threeOrientedFaces_apply]
    exact (show cubeBdry (qCubeToCoordinate c)
      (Sum.inl (qCubeToCoordinate
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs i).1)) = threeFacetOrientation i by
      change cubeBdry (qCubeToCoordinate c)
        (Sum.inl (qCubeToCoordinate (qCubeFacet c (qThreeDirection u v w i.1) i.2))) = _
      rw [cubeBdry_actual_facet c _ (qThreeDirection_mem c u v w hs i.1) i.2]
      obtain ⟨hw0, hv0, hu0⟩ := threeFacet_incidence_zero c huv hvw hs
      obtain ⟨hw1, hv1, hu1⟩ := threeFacet_incidence_one c huv hvw hs
      obtain ⟨e, s⟩ := i
      fin_cases e <;> fin_cases s <;>
        norm_num [qThreeDirection, threeFacetOrientation, fixedCoordinateSign, Fin.ext_iff] at * <;> assumption).symm
  · have hzero : cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
      apply cubeBdry_zero_off_actual_facets
      intro a ha s he
      rw [hs, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha
      · subst a
        exact hg ⟨(0, s), he.symm⟩
      · subst a
        exact hg ⟨(1, s), he.symm⟩
      · subst a
        exact hg ⟨(2, s), he.symm⟩
    rw [Finsupp.mapDomain_notin_range _ _ hg, hzero]

/-- Coordinate transport of the actual six-facet boundary is the finite ordinary
coordinate boundary used by the collapse. -/
theorem qThreeCubicalFaceBoundary_coordinate (c : QThreeCube A) :
    Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
      (qThreeCubicalFaceBoundary c) = qCubeCoordinateFacetChain c.1 := by
  change Finsupp.mapDomain (fun s : QSquare A => qCubeToCoordinate s.1)
    (Finsupp.mapDomain _ threeOrientedFaces) = _
  rw [← Finsupp.mapDomain_comp]
  ext g
  rw [qCubeCoordinateFacetChain_apply]
  exact qThreeOrientedFaces_coordinate_apply c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) (qThree_free_directions c) g

/-- Coordinate boundary naturality for all genuine finite cubical three-chains. -/
theorem qThreeCubicalBoundary_coordinate (r : QThreeCube A →₀ ℤ) :
    Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
      (qThreeCubicalBoundary r) =
      Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => grind
  | single c n =>
      rw [qThreeCubicalBoundary, Finsupp.linearCombination_single, map_smul,
        qThreeCubicalFaceBoundary_coordinate, Finsupp.linearCombination_single]

/-- Ordinary coordinate transport of every dimension-bounded strict three-boundary is
an actual finite combination of the cube boundaries used by the collapse. -/
theorem qCube_three_coordinate_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ,
      Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
        (qSquareCycleCoefficients (strictOrdBoundary3 y)) =
      Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r := by
  obtain ⟨r, _, hr⟩ := qCube_three_cubical_boundary_reconstruction y hy hb
  refine ⟨r, ?_⟩
  rw [hr, qThreeCubicalBoundary_coordinate]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

theorem qCube_coordinate_pos_iff (c : QCube A) (σ : Finset V) :
    posCube σ = qCubeToCoordinate c ↔ σ = c.spx ∧ c.sgn = 0 := by
  constructor
  · intro he
    have hs : σ = c.spx := by
      have h := congrArg freeSet he
      simpa using h
    refine ⟨hs, ?_⟩
    funext v
    have h := qCubeToCoordinate_parity c v
    rw [← he] at h
    by_cases hv : v ∈ σ <;> simpa [posCube, hv] using h.symm
  · rintro ⟨rfl, hsgn⟩
    exact (qCubeToCoordinate_sgn_zero c hsgn).symm

variable [LinearOrder V]

def qCubeTruncatedCoordinateBoundary (c : QCube A) :
    (Cube V ⊕ Finset V) →₀ ℤ :=
  Finsupp.lmapDomain ℤ ℤ Sum.inl (qCubeCoordinateFacetChain c) +
    if c.sgn = 0 then Finsupp.single (Sum.inr c.spx) (cutSign c.spx) else 0

/-- Every ordinary and cut-face coefficient of the genuine finite truncated boundary
is exactly the boundary used by the collapse. -/
theorem qCubeTruncatedCoordinateBoundary_apply (c : QCube A) (f : Cube V ⊕ Finset V) :
    qCubeTruncatedCoordinateBoundary c f = cubeBdry (qCubeToCoordinate c) f := by
  cases f with
  | inl g =>
      have hmap : Finsupp.mapDomain (Sum.inl : Cube V → Cube V ⊕ Finset V) (qCubeCoordinateFacetChain c) (Sum.inl g) =
          qCubeCoordinateFacetChain c g := Finsupp.mapDomain_apply_of_injective Sum.inl_injective _ g
      by_cases hsgn : c.sgn = 0 <;>
        simp [qCubeTruncatedCoordinateBoundary, Finsupp.lmapDomain_apply, hmap,
          qCubeCoordinateFacetChain_apply, hsgn]
  | inr σ =>
      have hmap : Finsupp.mapDomain Sum.inl (qCubeCoordinateFacetChain c) (Sum.inr σ) = 0 :=
        Finsupp.mapDomain_notin_range _ _ (by rintro ⟨g, h⟩; cases h)
      simp only [qCubeTruncatedCoordinateBoundary, Finsupp.add_apply,
        Finsupp.lmapDomain_apply, hmap, zero_add, cubeBdry_inr, qCube_coordinate_pos_iff]
      by_cases hsgn : c.sgn = 0
      · grind
      · simp_all

/-- For a three-cube the extra cut face has coefficient minus one precisely at the
positive corner, and is absent for every other sign pattern. -/

def qThreeTruncatedCoordinateBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    ((Cube V ⊕ Finset V) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeTruncatedCoordinateBoundary c.1)

def qThreeCutFaceChain : (QThreeCube A →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun c : QThreeCube A =>
    if c.1.sgn = 0 then Finsupp.single c.1.spx 1 else 0)

/-- The finite truncated three-boundary is its proved ordinary coordinate boundary
minus the finite chain of positive-corner cut faces. -/
theorem qThreeTruncatedCoordinateBoundary_split (r : QThreeCube A →₀ ℤ) :
    qThreeTruncatedCoordinateBoundary r =
      Finsupp.lmapDomain ℤ ℤ Sum.inl
        (Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r) -
      Finsupp.lmapDomain ℤ ℤ Sum.inr (qThreeCutFaceChain r) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs =>
      simp only [map_add, hr, hs]
      abel
  | single c n =>
      rw [qThreeTruncatedCoordinateBoundary, Finsupp.linearCombination_single,
        (show qCubeTruncatedCoordinateBoundary c.1 =
      Finsupp.lmapDomain ℤ ℤ Sum.inl (qCubeCoordinateFacetChain c.1) -
        if c.1.sgn = 0 then Finsupp.single (Sum.inr c.1.spx) 1 else 0 by
          simp only [qCubeTruncatedCoordinateBoundary, cutSign, c.2]
          by_cases hsgn : c.1.sgn = 0 <;> simp [hsgn, sub_eq_add_neg]), smul_sub,
        Finsupp.linearCombination_single, map_smul,
        qThreeCutFaceChain, Finsupp.linearCombination_single, map_smul]
      by_cases hsgn : c.1.sgn = 0 <;>
        simp [hsgn, Finsupp.lmapDomain_apply]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}


/-- A geometric chain collapse kills every genuine finite truncated boundary whose
three-cubes occur in the actual collapse sequence. -/
theorem qThreeTruncatedBoundary_collapse_zero
    (lp : List (Cube V × (Cube V ⊕ Finset V)))
    (hlp : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp)
    (r : QThreeCube A →₀ ℤ)
    (hr : ∀ c ∈ r.support, ∃ f, (qCubeToCoordinate c.1, f) ∈ lp) :
    CollapseChain.cmap (cubeBdry (V := V)) lp
      (qThreeTruncatedCoordinateBoundary r) = 0 := by
  let L : ((Cube V ⊕ Finset V) → ℤ) →+ ((Cube V ⊕ Finset V) → ℤ) :=
    { toFun := CollapseChain.cmap (cubeBdry) lp
      map_zero' := CollapseChain.cmap_zero lp
      map_add' := CollapseChain.cmap_add lp }
  have he : (qThreeTruncatedCoordinateBoundary r) =
      ∑ c ∈ r.support, (fun f => r c * cubeBdry (qCubeToCoordinate c.1) f) := by
    funext f
    simp only [Finset.sum_apply, (show qThreeTruncatedCoordinateBoundary r f =
      ∑ c ∈ r.support, r c * cubeBdry (qCubeToCoordinate c.1) f by
      simp only [qThreeTruncatedCoordinateBoundary, Finsupp.linearCombination_apply,
        Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply,
        qCubeTruncatedCoordinateBoundary_apply, smul_eq_mul])]
  change L (qThreeTruncatedCoordinateBoundary r) = 0
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro c hc
  obtain ⟨f, hf⟩ := hr c hc
  change CollapseChain.cmap (cubeBdry) lp
    (fun g => r c * cubeBdry (qCubeToCoordinate c.1) g) = 0
  rw [CollapseChain.cmap_leftMul,
    CollapseChain.cmap_bdry_eq_zero hlp (qCubeToCoordinate c.1, f) hf]
  funext g
  simp

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb ASC
variable (q : ℕ) [NeZero q]


theorem genus_truncated_three_boundary_collapse_zero
    (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (qThreeTruncatedCoordinateBoundary r) = 0 := by
  apply qThreeTruncatedBoundary_collapse_zero _ (genusChainCollapse_isChainCollapse q)
  intro c _
  exact (by
    apply (genusChainCollapse_isPairCollapse q).covers
    apply mem_topCubes.mpr
    rw [freeSet_qCubeToCoordinate]
    exact ⟨genus_simplex_mem_faces q c.1.isSimplex, c.2⟩)

/-- Every cut cell surviving the actual genus collapse has at most two vertices. -/
theorem genusSpine_cut_card_le_two (σ : CutCell (cmpRel (GenusVertex q)))
    (hσ : (Sum.inr σ : GenusTruncatedCell q) ∈ genusSpineCellSet q) : σ.1.card ≤ 2 := by
  have hmax := genus_chain_card_le_three q (genus_simplex_mem_faces q σ.2.2)
  by_contra hnot
  have hthree : σ.1.card = 3 := by omega
  have hremoved := genusChainCollapse_removes_cut_triangle q σ.1
    ⟨genus_simplex_mem_faces q σ.2.2, hthree⟩
  exact hσ.2 hremoved

/-- The actual surviving-spine comparison lands entirely in quotient cube dimension
at most two, including its retained cut cells. -/
theorem genusSpineCellToOld_dimension_le_two (c : GenusSpineCell q) :
    (genusSpineCellToOld q c).1.spx.card ≤ 2 := by
  cases hc : c.1 with
  | inl d =>
      have hd := c.2.1
      rw [hc] at hd
      simpa [genusSpineCellToOld, truncatedCellRetraction, hc, truncatedCellDimension] using hd
  | inr σ =>
      have hσ := c.2
      rw [hc] at hσ
      have hcard := genusSpine_cut_card_le_two q σ hσ
      simpa [genusSpineCellToOld, truncatedCellRetraction, hc, posQCube] using hcard

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


/-- Every actual finite old-spine face chain maps into full-cube triangles whose top
cube has dimension at most two. -/
theorem markedSpineToFullCube_chain_dimension (d : (markedSpineCx q).F →₀ ℤ)
    (t : (orderCx (QCube (cmpRel (GenusVertex q)))).F)
    (ht : t ∈ (chain2 (markedSpineToFullCube q) d).support) :
    t.1.2.2.spx.card ≤ 2 := by
  classical
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  exact (genusSpineCellToOld_dimension_le_two q f.1.1.2.2)

/-- Normalization preserves the actual maximum cube dimension of the marked-spine image. -/
theorem markedSpineToFullCube_normalized_dimension (d : (markedSpineCx q).F →₀ ℤ)
    (t : StrictOrdTri (QCube (cmpRel (GenusVertex q))))
    (ht : t ∈ (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)).support) :
    t.1.2.2.spx.card ≤ 2 := by
  by_contra hdim
  have hzero : normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) t = 0 := by
    erw [normalizeOrdChain2, Finsupp.linearCombination_apply, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have hn : normalizeOrdTriangle a t = 0 := by
      unfold normalizeOrdTriangle
      split_ifs with h
      · by_cases he : ⟨a.1, h⟩ = t
        · have hd := markedSpineToFullCube_chain_dimension q d a ha
          have htop := congrArg (fun x : StrictOrdTri (QCube (cmpRel (GenusVertex q))) =>
            x.1.2.2) he
          erw [htop] at hd
          exact False.elim (hdim hd)
        · simp_all
      · simp
    change (((chain2 (markedSpineToFullCube q) d) a) • normalizeOrdTriangle a) t = 0
    rw (config := { transparency := .default }) [Finsupp.smul_apply, hn, smul_zero]
  simp_all

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical
/-- Viewing a subset inside a containing carrier preserves its actual subspace topology. -/
def orderNerveNestedCarrierHomeomorph {X : Type} [TopologicalSpace X]
    (S C : Set X) (h : S ⊆ C) : S ≃ₜ {x : C // x.val ∈ S} where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- The actual supported closed-star carriers are homeomorphic under a poset cover. -/
def vertexStarCarrierHomeomorph (hf : IsPosetCover f) (v : P) :
    (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P)) ≃ₜ
    (orderNerveRealizationSubcomplex Q (orderNerveVertexStar Q (f v)) :
      Set (orderNerveRealization Q)) :=
  (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm.trans
    ((hf.vertexStarRealizationHomeomorph v).trans
      (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar Q (f v))))

/-- The closed-star carrier homeomorphism agrees with the actual realized projection. -/
theorem vertexStarCarrierHomeomorph_coe (hf : IsPosetCover f) (v : P)
    (x : (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P))) :
    (hf.vertexStarCarrierHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    (orderNerveVertexStar P v)).surjective x
  change (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar Q (f v))
    (hf.vertexStarRealizationHomeomorph v
      ((orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm
        (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v) y)))).val = _
  erw [Homeomorph.symm_apply_apply, orderNerveRealizationSubtypeHomeomorph_coe,
    orderNerveRealizationSubtypeHomeomorph_coe]
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

/-- On a lifted closed star, the center coordinate is preserved by the projection. -/
theorem vertexStarCarrier_coordinate (hf : IsPosetCover f) (v : P)
    (x : (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P))) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf.mono x.val) (f v) =
      orderNerveRealizationCoordinates P x.val v := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    (orderNerveVertexStar P v)).surjective x
  erw [orderNerveRealizationSubtypeHomeomorph_coe]
  change orderNerveAffineRealization (fun q => if q = f v then 1 else 0)
    (orderNerveRealizationMap f hf.mono
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h) y)) =
    orderNerveAffineRealization (fun p => if p = v then 1 else 0)
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h) y)
  erw [orderNerveAffineRealization_natural, orderNerveAffineRealization_natural,
    orderNerveAffineRealization_natural]
  have hv : (((fun q => if q = f v then 1 else 0) ∘ f) ∘
      (Subtype.val : orderNerveVertexStar P v → P)) =
      ((fun p => if p = v then (1 : ℝ) else 0) ∘ Subtype.val) := by
    funext p
    have he : f p.val = f v ↔ p.val = v := by
      constructor
      · intro h
        rcases p.property with hp | hp
        · exact hf.down_inj hp (le_refl v) h
        · exact hf.up_inj hp (le_refl v) h
      · simp_all
    simp only [Function.comp_apply, he]
  rw (config := { transparency := .default }) [hv]

/-- Each lifted open star is genuinely homeomorphic to its target open star. -/
def vertexOpenStarHomeomorph (hf : IsPosetCover f) (v : P) :
    orderNerveRealizationOpenStar P v ≃ₜ orderNerveRealizationOpenStar Q (f v) :=
  (orderNerveNestedCarrierHomeomorph _ _
    (orderNerveRealizationOpenStar_subset_subcomplex v)).trans
    (((hf.vertexStarCarrierHomeomorph v).subtype (p := fun x =>
      x.val ∈ orderNerveRealizationOpenStar P v) (q := fun x =>
      x.val ∈ orderNerveRealizationOpenStar Q (f v)) (by
        intro x
        change (0 < orderNerveRealizationCoordinates P x.val v) ↔
          (0 < orderNerveRealizationCoordinates Q
            (hf.vertexStarCarrierHomeomorph v x).val (f v))
        rw (config := { transparency := .default }) [hf.vertexStarCarrierHomeomorph_coe, hf.vertexStarCarrier_coordinate])).trans
      (orderNerveNestedCarrierHomeomorph _ _
        (orderNerveRealizationOpenStar_subset_subcomplex (f v))).symm)

/-- The open-sheet homeomorphism is the actual realized projection. -/
theorem vertexOpenStarHomeomorph_coe (hf : IsPosetCover f) (v : P)
    (x : orderNerveRealizationOpenStar P v) :
    (hf.vertexOpenStarHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := by
  exact hf.vertexStarCarrierHomeomorph_coe v
    ⟨x.val, orderNerveRealizationOpenStar_subset_subcomplex v x.property⟩

end IsPosetCover
end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory

/-- Closed vertex-star carriers are contractible in the actual CW topology. -/
theorem orderNerveRealization_closedStar_contractible {P : Type} [PartialOrder P] (v : P) :
    ContractibleSpace (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P)) := by
  let a : orderNerveVertexStar P v := ⟨v, Or.inl le_rfl⟩
  letI := orderNerveRealization_contractible_of_comparable a (fun p => p.property)
  exact (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm.contractibleSpace

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Paths lying in a simply connected subspace are homotopic in the ambient
space, with their endpoints fixed. -/
theorem paths_homotopic_of_range_subset {X : Type} [TopologicalSpace X]
    {A : Set X} (hA : IsSimplyConnected A) {a b : X} (p q : Path a b)
    (hp : Set.range p ⊆ A) (hq : Set.range q ⊆ A) : p.Homotopic q := by
  letI : SimplyConnectedSpace A := hA
  have ha  := hp p.source_mem_range
  have hb  := hp p.target_mem_range
  let p' : Path (⟨a, ha⟩ : A) ⟨b, hb⟩ :=
    { toFun := fun t => ⟨p t, hp ⟨t, rfl⟩⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path (⟨a, ha⟩ : A) ⟨b, hb⟩ :=
    { toFun := fun t => ⟨q t, hq ⟨t, rfl⟩⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  exact (SimplyConnectedSpace.paths_homotopic p' q').map
    ⟨Subtype.val, continuous_subtype_val⟩

/-- Two vertices of a canonical simplex can be joined inside that simplex. -/
theorem orderNerveRealizationSimplex_exists_path {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (i j : Fin (n.len + 1)) :
    ∃ p : Path (orderNerveRealizationVertex (s.obj i))
        (orderNerveRealizationVertex (s.obj j)),
      Set.range p ⊆ Set.range (orderNerveRealizationSimplex P s) := by
  obtain ⟨z, hz⟩ := orderNerveRealizationVertex_mem_simplex s i
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex s j
  let p := (PathConnectedSpace.joined z w).somePath.map
    (orderNerveRealizationSimplex P s).hom.continuous
  refine ⟨p.cast hz.symm hw.symm, ?_⟩
  rintro x ⟨t, rfl⟩
  exact ⟨(PathConnectedSpace.joined z w).somePath t, rfl⟩

/-- A realized comparable edge, chosen inside its canonical one-simplex. -/
def orderNerveRealizationEdgePath {P : Type} [PartialOrder P]
    {a b : P} (h : a ≤ b) : Path (orderNerveRealizationVertex a)
      (orderNerveRealizationVertex b) :=
  (orderNerveRealizationSimplex_exists_path (n := ⦋1⦌) (ComposableArrows.mk₁ (homOfLE h))
    (0 : Fin 2) (1 : Fin 2)).choose


/-- A comparable edge stays in any closed vertex star containing its endpoints. -/
theorem orderNerveRealizationEdgePath_supported {P : Type} [PartialOrder P]
    {a b : P} (h : a ≤ b) (v : P) (ha : a ≤ v ∨ v ≤ a) (hb : b ≤ v ∨ v ≤ b) :
    Set.range (orderNerveRealizationEdgePath h) ⊆
      (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
        Set (orderNerveRealization P)) := by
  apply ((orderNerveRealizationSimplex_exists_path (ComposableArrows.mk₁ (homOfLE h))
    0 1).choose_spec).trans
  apply orderNerveRealizationSimplex_supported (orderNerveVertexStar P v)
  intro i
  fin_cases i
  · exact ha
  · exact hb

theorem orderNerveRealizationVertex_mem_closedStar {P : Type} [PartialOrder P]
    {p v : P} (hp : p ≤ v ∨ v ≤ p) :
    orderNerveRealizationVertex p ∈
      (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
        Set (orderNerveRealization P)) := by
  intro q hq
  by_cases he : p = q
  · subst q
    exact (hq hp).elim
  · simp only [orderNerveRealizationCoordinates_vertex, if_neg he]

/-- The degenerate edge represents the identity path class. -/
theorem orderNerveRealizationEdgePath_refl {P : Type} [PartialOrder P] (a : P) :
    (orderNerveRealizationEdgePath (le_refl a)).Homotopic
      (Path.refl (orderNerveRealizationVertex a)) := by
  letI := orderNerveRealization_closedStar_contractible a
  apply paths_homotopic_of_range_subset
    (A := (orderNerveRealizationSubcomplex P (orderNerveVertexStar P a))) (by
        change SimplyConnectedSpace _
        infer_instance)
  · exact orderNerveRealizationEdgePath_supported le_rfl a (Or.inl le_rfl) (Or.inl le_rfl)
  · rintro x ⟨t, rfl⟩
    exact orderNerveRealizationVertex_mem_closedStar (Or.inl le_rfl)

/-- A chain of three vertices gives the actual topological triangle relation. -/
theorem orderNerveRealizationEdgePath_trans {P : Type} [PartialOrder P]
    {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    (orderNerveRealizationEdgePath (hab.trans hbc)).Homotopic
      ((orderNerveRealizationEdgePath hab).trans (orderNerveRealizationEdgePath hbc)) := by
  letI := orderNerveRealization_closedStar_contractible b
  apply paths_homotopic_of_range_subset
    (A := (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b))) (by
        change SimplyConnectedSpace _
        infer_instance)
  · exact orderNerveRealizationEdgePath_supported _ b (Or.inl hab) (Or.inr hbc)
  · rw [Path.trans_range]
    exact Set.union_subset
      (orderNerveRealizationEdgePath_supported hab b (Or.inl hab) (Or.inl le_rfl))
      (orderNerveRealizationEdgePath_supported hbc b (Or.inl le_rfl) (Or.inr hbc))

/-- Comparable vertices and their canonical edge paths form a functor to the
actual topological fundamental groupoid of the realization. -/
def orderNerveRealizationFundamentalFunctor (P : Type) [PartialOrder P] :
    P ⥤ FundamentalGroupoid (orderNerveRealization P) where
  obj p := FundamentalGroupoid.mk (orderNerveRealizationVertex p)
  map h := Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath (leOfHom h))
  map_id a := Quotient.sound (orderNerveRealizationEdgePath_refl a)
  map_comp f g := Quotient.sound (orderNerveRealizationEdgePath_trans (leOfHom f) (leOfHom g))

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable (P : Type u) [PartialOrder P]

/-- The actual order-nerve three-boundary with codomain its genuine two-cycle module. -/
def ordBoundary3Cycles : (OrdTet P →₀ ℤ) →ₗ[ℤ]
    LinearMap.ker (bdry2 (orderCx P)) :=
  (ordBoundary3 (P := P)).codRestrict (LinearMap.ker (bdry2 (orderCx P)))
    (fun y => bdry2_ordBoundary3 y)

/-- Second integral homology of the genuine order nerve, defined by its actual boundaries. -/
abbrev OrderNerveH2 :=
  (LinearMap.ker (bdry2 (orderCx P))) ⧸ LinearMap.range (ordBoundary3Cycles P)

/-- The actual homology class of an actual finite order-nerve two-cycle. -/
def orderNerveH2Class (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) : OrderNerveH2 P :=
  Submodule.Quotient.mk ⟨c, hc⟩

/-- An actual order-nerve cycle class vanishes exactly when the cycle has an actual finite three-filling. -/
theorem orderNerveH2Class_eq_zero_iff (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    orderNerveH2Class P c hc = 0 ↔ ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c := by
  rw [orderNerveH2Class, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
variable (P : Type) [PartialOrder P]

/-- The actual Mathlib differential detects precisely the actual cellular two-cycles. -/
theorem mathlibOrderNerve_cycle_iff (c : OrdTri P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) c) = 0 ↔ FiniteChains.Comb.bdry2 (orderCx P) c = 0 := by
  rw [mathlibOrderNerve_d2]
  constructor
  · intro h
    apply Finsupp.mapDomain_injective (ordEdgeNerveEquiv P).injective
    simpa using h
  · simp_all

/-- The actual Mathlib alternating-face two-cycle kernel has genuine order-cell coordinates. -/
def mathlibOrderNerveCycleEquiv :
    LinearMap.ker (FiniteChains.Comb.bdry2 (orderCx P)) ≃ₗ[ℤ]
      LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 1).hom) where
  toFun c := ⟨Finsupp.domLCongr (R := ℤ) (M := ℤ) (ordTriNerveEquiv P) c.val,
    by simpa only [LinearMap.mem_ker, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain] using
        (mathlibOrderNerve_cycle_iff P c.val).mpr c.property⟩
  invFun c := ⟨(Finsupp.domLCongr (R := ℤ) (M := ℤ) (ordTriNerveEquiv P)).symm c.val, by
    apply (mathlibOrderNerve_cycle_iff P _).mp
    have he := (Finsupp.domLCongr (R := ℤ) (M := ℤ)
      (ordTriNerveEquiv P)).apply_symm_apply c.val
    simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain] at he
    rw [he]
    exact c.property⟩
  left_inv c := Subtype.ext (LinearEquiv.symm_apply_apply _ c.val)
  right_inv c := Subtype.ext (LinearEquiv.apply_symm_apply _ c.val)
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' n c := Subtype.ext (map_smul _ _ _)

/-- The actual Mathlib three-differential lands in its actual two-cycle kernel. -/
theorem mathlibOrderNerve_d2_d3 (c : CategoryTheory.ComposableArrows P 3 →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 2).hom c) = 0 := by
  obtain ⟨d, rfl⟩ := Finsupp.mapDomain_surjective (ordTetNerveEquiv P).surjective c
  rw [mathlibOrderNerve_d3, mathlibOrderNerve_d2, bdry2_ordBoundary3,
    Finsupp.mapDomain_zero]

/-- The actual Mathlib third differential with its genuine cycle-kernel codomain. -/
def mathlibOrderNerveBoundary3Cycles :
    (CategoryTheory.ComposableArrows P 3 →₀ ℤ) →ₗ[ℤ]
      LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 1).hom) :=
  ((AlgebraicTopology.AlternatingFaceMapComplex.objD
    (mathlibOrderNerveModule P) 2).hom).codRestrict _ (mathlibOrderNerve_d2_d3 P)

/-- The actual cycle comparison maps precisely onto Mathlib's actual three-boundary range. -/
theorem mathlibOrderNerveCycleEquiv_boundary_range :
    (LinearMap.range (ordBoundary3Cycles P)).map
      (mathlibOrderNerveCycleEquiv P).toLinearMap =
        LinearMap.range (mathlibOrderNerveBoundary3Cycles P) := by
  ext c
  constructor
  · rintro ⟨d, ⟨y, rfl⟩, rfl⟩
    refine ⟨Finsupp.mapDomain (ordTetNerveEquiv P) y, ?_⟩
    ext
    change _ = (Finsupp.domLCongr
      (ordTriNerveEquiv P)) (ordBoundary3 y)
    rw [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain]
    exact mathlibOrderNerve_d3 P y
  · rintro ⟨y, rfl⟩
    obtain ⟨d, rfl⟩ := Finsupp.mapDomain_surjective (ordTetNerveEquiv P).surjective y
    refine ⟨ordBoundary3Cycles P d, ⟨d, rfl⟩, ?_⟩
    ext
    change (Finsupp.domLCongr
      (ordTriNerveEquiv P)) (ordBoundary3 d) = _
    rw [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain]
    exact (mathlibOrderNerve_d3 P d).symm

/-- Actual order-cell second homology agrees with the quotient formed from
Mathlib's genuine alternating-face differentials. -/
def mathlibOrderNerveH2Equiv : OrderNerveH2 P ≃ₗ[ℤ]
    (LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom)) ⧸
        LinearMap.range (mathlibOrderNerveBoundary3Cycles P) :=
  Submodule.Quotient.equiv _ _ (mathlibOrderNerveCycleEquiv P)
    (mathlibOrderNerveCycleEquiv_boundary_range P)

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- The actual degree-three to degree-one segment of Mathlib's alternating-face complex. -/
def mathlibOrderNerveShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2)
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1)
    (by
      apply ModuleCat.hom_ext
      ext c
      exact mathlibOrderNerve_d2_d3 P c)

/-- The genuine order-cell quotient is linearly equivalent to Mathlib's
categorical homology of its actual alternating-face differential segment. -/
def mathlibOrderNerveCategoricalH2Equiv :
    OrderNerveH2 P ≃ₗ[ℤ] (mathlibOrderNerveShortComplex P).homology :=
  (mathlibOrderNerveH2Equiv P).trans
    ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.symm.toLinearEquiv)

/-- The explicit differential segment is the actual degree-two short complex. -/
def mathlibOrderNerveShortComplexIso :
    mathlibOrderNerveShortComplex P ≅
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).sc 2 :=
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (mathlibOrderNerveModule P)).d 3 2 =
          AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2 ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ 2)
    (by
      change 𝟙 _ ≫ (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (mathlibOrderNerveModule P)).d 2 1 =
          AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1 ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ 1) :
      mathlibOrderNerveShortComplex P ≅
        (AlgebraicTopology.AlternatingFaceMapComplex.obj
          (mathlibOrderNerveModule P)).sc' 3 2 1) ≪≫
    ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (mathlibOrderNerveModule P)).isoSc' 3 2 1
        ((ComplexShape.down ℕ).prev_eq' (by decide : (ComplexShape.down ℕ).Rel 3 2))
        ((ComplexShape.down ℕ).next_eq' (by decide : (ComplexShape.down ℕ).Rel 2 1))).symm

/-- The order-cell quotient is the actual degree-two categorical homology of
Mathlib's alternating-face chain complex. -/
def mathlibOrderNerveComplexH2Equiv :
    OrderNerveH2 P ≃ₗ[ℤ]
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 :=
  (mathlibOrderNerveCategoricalH2Equiv P).trans
    (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
      (mathlibOrderNerveShortComplexIso P)).toLinearEquiv)

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}


/-- Actual positive-square coefficients vanish for every dimension-two cycle whose
coefficients at flags through the removed positive origin vanish. -/
theorem qSquareCycleCoefficients_positive_zero
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0)
    (horigin : ∀ t : (strictOrderCx (QCube A)).F,
      t.1.1.spx = ∅ ∧ t.1.1.sgn = 0 → z t = 0)
    (c : QSquare A) (hsgn : c.1.sgn = 0) : qSquareCycleCoefficients z c = 0 := by
  let t := squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
    (qSquare_free_directions c) (false, 0, true)
  have ht := horigin t (show (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, true)).1.1.spx = ∅ ∧
    (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, true)).1.1.sgn = 0 by
    constructor
    · rfl
    · funext x
      simp [squareFlag, squareEndpointFlag, squarePositiveFlag, cubePositiveVertex,
        qCubeFacet, hsgn])
  have he := congrArg (fun r => r t)
    (cubeTwoCycle_square_component c.1 (qSquareLeft c) (qSquareRight c)
      (qSquare_directions_ne c) (qSquare_free_directions c) z hz hcycle)
  simp only [t, Finsupp.filter_apply, squareFlag_top, Finsupp.smul_apply,
    squareSubdivision_flag_coefficient] at he
  rw [ht] at he
  norm_num [squareFlagSign, smul_eq_mul] at he
  exact he

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Restoring the corner does not turn an old face's first vertex into that corner. -/
theorem oldToFullCube_face_ne_corner
    (f : (orderCx (QOld (cmpRel (GenusVertex q)))).F) :
    ((oldToFullCube q).onF f).1.1 ≠ positiveCorner (cmpRel (GenusVertex q)) := by
  intro h
  apply f.1.1.2
  exact ⟨congrArg QCube.spx h, congrArg QCube.sgn h⟩

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (p : P)

def cornerTriangleEdge (t : OrdTri P) :
    (orderCx (Set.Ioi p)).E →₀ ℤ := by
  classical
  exact if h : t.1.1 = p ∧ p < t.1.2.1 then
    Finsupp.single ⟨(⟨t.1.2.1, h.2⟩, ⟨t.1.2.2, h.2.trans_le t.2.2⟩), t.2.2⟩ 1 else 0

def cornerChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    ((orderCx (Set.Ioi p)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (cornerTriangleEdge p)

def cornerTetrahedronTriangle (t : OrdTet P) :
    (orderCx (Set.Ioi p)).F →₀ ℤ := by
  classical
  exact if h : t.1.1 = p ∧ p < t.1.2.1 then
    Finsupp.single ⟨(⟨t.1.2.1, h.2⟩,
      ⟨t.1.2.2.1, h.2.trans_le t.2.2.1⟩,
      ⟨t.1.2.2.2, (h.2.trans_le t.2.2.1).trans_le t.2.2.2⟩), t.2.2⟩ 1 else 0

def cornerChain3 : (OrdTet P →₀ ℤ) →ₗ[ℤ]
    ((orderCx (Set.Ioi p)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (cornerTetrahedronTriangle p)

/-- Extracting a minimal corner from a three-boundary gives the negative boundary
of its actual upper-interval triangle chain. -/

theorem cornerChain2_ordBoundary3 (hp : ∀ v : P, v ≤ p → v = p)
    (c : OrdTet P →₀ ℤ) :
    cornerChain2 p (ordBoundary3 c) = -bdry2 (orderCx (Set.Ioi p)) (cornerChain3 p c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add, neg_add]
  | single t n =>
      rw [ordBoundary3, Finsupp.linearCombination_single, map_smul,
        (show cornerChain2 p (ordTetBoundary t) =
      -bdry2 (orderCx (Set.Ioi p)) (cornerTetrahedronTriangle p t) by
          obtain ⟨⟨a, b, c, d⟩, hab, hbc, hcd⟩ := t
          by_cases ha : a = p
          · subst a
            by_cases hb : b = p
            · subst b
              simp [ordTetBoundary, cornerChain2, cornerTriangleEdge,
                cornerTetrahedronTriangle]
            · have hpb  := lt_of_le_of_ne hab (Ne.symm hb)
              have hpc := hpb.trans_le hbc
              simp only [ordTetBoundary, cornerChain2, map_add, map_sub, Finsupp.linearCombination_single]
              simp [ordTetBoundary, cornerChain2, cornerTriangleEdge,
                cornerTetrahedronTriangle, hpb, hpc, hb,
                map_add, map_sub, map_smul, Finsupp.linearCombination_single,
                bdry2, orderCx, pathChain]
              abel
          · have hb : b ≠ p := by
              intro h
              exact ha (hp a (h ▸ hab))
            simp [ordTetBoundary, cornerChain2, cornerTriangleEdge,
              cornerTetrahedronTriangle, ha, hb]), cornerChain3,
        Finsupp.linearCombination_single, map_smul, smul_neg]

end FiniteChains.Comb
end

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)


theorem le_positiveCorner_iff (c : QCube A) :
    c ≤ positiveCorner A ↔ c = positiveCorner A := by
  constructor
  · intro h
    apply QCube.ext'
    · exact Finset.Subset.antisymm h.1 (Finset.empty_subset _)
    · exact h.2
  · simp_all

theorem positiveCorner_lt_iff (c : QCube A) :
    positiveCorner A < c ↔ c.spx.Nonempty ∧ c.sgn = 0 := by
  rw [lt_iff_le_and_ne, (show positiveCorner A ≤ c ↔ c.sgn = 0 by
    constructor
    · intro h
      funext v
      by_cases hv : v ∈ c.spx
      · exact c.sgn_eq_zero v hv
      · exact (h.2 v hv).symm
    · intro h
      exact ⟨Finset.empty_subset _, fun v _ => by rw [h]; rfl⟩)]
  constructor
  · rintro ⟨hs, hn⟩
    refine ⟨Finset.nonempty_iff_ne_empty.mpr ?_, hs⟩
    intro he
    apply hn
    symm
    apply QCube.ext' he
    intro v _
    exact congrFun hs v
  · rintro ⟨hne, hs⟩
    refine ⟨hs, ?_⟩
    intro he
    have hz := congrArg QCube.spx he
    exact (Finset.nonempty_iff_ne_empty.mp hne) hz.symm

/-- The strict upper interval of the actual restored corner is precisely the surface
simplex poset, with its actual face order. -/
def positiveCornerLinkEquiv : Set.Ioi (positiveCorner A) ≃o NeSpx A where
  toFun c := ⟨c.1.spx, (positiveCorner_lt_iff A c.1).mp c.2 |>.1, c.1.isSimplex⟩
  invFun σ := ⟨surfaceFullCube A σ, (positiveCorner_lt_iff A _).mpr ⟨σ.2.1, rfl⟩⟩
  left_inv c := by
    apply Subtype.ext
    change surfaceFullCube A ⟨c.1.spx, ((positiveCorner_lt_iff A c.1).mp c.2).1, c.1.isSimplex⟩ = c.1
    apply QCube.ext' (by rfl)
    intro v _
    exact (congrFun ((positiveCorner_lt_iff A c.1).mp c.2).2 v).symm
  right_inv σ := rfl
  map_rel_iff' := by
    intro c d
    change c.1.spx ⊆ d.1.spx ↔ c.1 ≤ d.1
    constructor
    · intro h
      refine ⟨h, ?_⟩
      intro v _
      rw [((positiveCorner_lt_iff A c.1).mp c.2).2,
        ((positiveCorner_lt_iff A d.1).mp d.2).2]
    · exact fun h => h.1

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

def cornerSurfaceMap : Hom (orderCx (Set.Ioi (positiveCorner A)))
    (orderCx (NeSpx A)) :=
  orderCxMap (positiveCornerLinkEquiv A) (positiveCornerLinkEquiv A).monotone

def cornerSurfaceChain2 :
    ((orderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ] ((orderCx (NeSpx A)).E →₀ ℤ) :=
  (chain1 (cornerSurfaceMap A)).comp (cornerChain2 (positiveCorner A))

def cornerSurfaceChain3 :
    (OrdTet (QCube A) →₀ ℤ) →ₗ[ℤ] ((orderCx (NeSpx A)).F →₀ ℤ) :=
  (chain2 (cornerSurfaceMap A)).comp (cornerChain3 (positiveCorner A))

/-- The extracted corner of a full-cube three-boundary is an actual surface boundary. -/
theorem cornerSurfaceChain2_ordBoundary3 (c : OrdTet (QCube A) →₀ ℤ) :
    cornerSurfaceChain2 A (ordBoundary3 c) =
      -Comb.bdry2 (orderCx (NeSpx A)) (cornerSurfaceChain3 A c) := by
  change chain1 (cornerSurfaceMap A) (cornerChain2 (positiveCorner A) (ordBoundary3 c)) = _
  rw [cornerChain2_ordBoundary3 _ (fun v hv => (le_positiveCorner_iff A v).mp hv), map_neg]
  rw [cornerSurfaceChain3, LinearMap.comp_apply, bdry2_chain2]

/-- Extracting the explicit cone fan recovers exactly its input surface edge chain. -/
theorem cornerSurfaceChain2_surfaceCornerFan (c : (orderCx (NeSpx A)).E →₀ ℤ) :
    cornerSurfaceChain2 A (surfaceCornerFan A c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
      have hlt : positiveCorner A < surfaceFullCube A e.1.1 :=
        (positiveCorner_lt_iff A _).mpr ⟨e.1.1.2.1, rfl⟩
      rw [surfaceCornerFan, coneEdgeChain, Finsupp.linearCombination_single, map_smul]
      change n • chain1 (cornerSurfaceMap A)
        (cornerChain2 (positiveCorner A)
          (Finsupp.single (coneEdgeTriangle (surfaceFullCube A)
            (surfaceFullCube_monotone A) (positiveCorner A)
            (positiveCorner_le_surface A) e) 1)) = _
      rw [cornerChain2, Finsupp.linearCombination_single, one_smul]
      have h : positiveCorner A = positiveCorner A ∧
          positiveCorner A < surfaceFullCube A e.1.1 := ⟨rfl, hlt⟩
      simp only [coneEdgeTriangle, cornerTriangleEdge, dif_pos h]
      simp [chain1, cornerSurfaceMap, orderCxMap, positiveCornerLinkEquiv,
        surfaceFullCube, posQCube]

end FiniteChains.Davis
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem cornerSurfaceChain2_oldToFullCube
    (c : (orderCx (QOld (cmpRel (GenusVertex q)))).F →₀ ℤ) :
    cornerSurfaceChain2 (cmpRel (GenusVertex q)) (chain2 (oldToFullCube q) c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => grind
  | single f n =>
      have hn := oldToFullCube_face_ne_corner q f
      change chain1 (cornerSurfaceMap _) (cornerChain2 (positiveCorner _)
        (Finsupp.mapDomain (oldToFullCube q).onF (Finsupp.single f n))) = 0
      erw [Finsupp.mapDomain_single, cornerChain2, Finsupp.linearCombination_single]
      simp [cornerTriangleEdge, hn]


def capSurfaceFace : (cappedSpineCx q).F →
    (orderCx (NeSpx (cmpRel (GenusVertex q)))).E →₀ ℤ
  | .inl _ => 0
  | .inr x => pathChain (gSig q (x.1.val, x.2))

def capSurfaceChain2 : ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    ((orderCx (NeSpx (cmpRel (GenusVertex q)))).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (capSurfaceFace q)

theorem cornerSurfaceChain2_controlledAugmentedChain2 (c : (cappedSpineCx q).F →₀ ℤ) :
    cornerSurfaceChain2 (cmpRel (GenusVertex q)) (controlledAugmentedChain2 q c) =
      capSurfaceChain2 q c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single f n =>
      erw [controlledAugmentedChain2, Finsupp.linearCombination_single, map_smul,
        capSurfaceChain2, Finsupp.linearCombination_single]
      apply congrArg (n • ·)
      obtain f | x := f
      · change cornerSurfaceChain2 _ (Finsupp.single ((markedSpineToFullCube q).onF f) 1) = 0
        have h := cornerSurfaceChain2_oldToFullCube q
          (Finsupp.single (((genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))).onF f) 1)
        change cornerSurfaceChain2 _ (Finsupp.mapDomain (oldToFullCube q).onF
          (Finsupp.single (((genusSpineToOld q).comp
            (componentIncl (genusSpineCx q) (spineBase q))).onF f) 1)) = 0 at h
        erw [Finsupp.mapDomain_single] at h
        exact h
      · exact (show cornerSurfaceChain2 (cmpRel (GenusVertex q))
      (hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x)) =
        pathChain (gSig q (x.1.val, x.2)) by
        erw [controlledCoverCap_hurewicz, map_add, cornerSurfaceChain2_oldToFullCube,
          cornerSurfaceChain2_surfaceCornerFan, zero_add])

/-- The actual augmented capping loops of every capped-cover cycle form a surface boundary. -/
theorem capSurfaceCycle_boundary (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (orderCx (NeSpx (cmpRel (GenusVertex q)))).F →₀ ℤ,
      Comb.bdry2 _ d = capSurfaceChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨y, hy⟩ := controlledAugmentedCycle_boundary3 q c hc
  refine ⟨-cornerSurfaceChain3 _ y, ?_⟩
  erw [map_neg, ← cornerSurfaceChain2_ordBoundary3, hy,
    cornerSurfaceChain2_controlledAugmentedChain2]

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable (q : ℕ) [NeZero q]

def characterRel : Empty ⊕ PUnit → FreeGroup (ℕ × Bool) := fun _ => 1
def characterA (h : ℕ) : ℕ × Bool := (h, false)
def characterB (h : ℕ) : ℕ × Bool := (h, true)
def characterGen (x : ℕ × Bool) : Multiplicative ((ℕ × Bool) →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.single x 1)

omit [NeZero q] in
theorem characterRel_read (j : Empty ⊕ PUnit) :
    wordVal characterGen (genusW characterRel characterA characterB q j) = 1 := by
  obtain j | j := j
  · grind
  · erw [genusW_inr, wordVal, mk_surfWord, map_commWord]
    simp [commWord, mul_comm]

def surfaceCharacterCocycle :
    OrdCocycle (NeSpx (cmpRel (GenusVertex q))) (Multiplicative ((ℕ × Bool) →₀ ℤ)) :=
  (presCoc (genusW characterRel characterA characterB q) characterGen
    (characterRel_read q)).pullback
      (genusAtt characterRel characterA characterB q)
      (genusAtt characterRel characterA characterB q).monotone

/-- This explicit surface cocycle evaluates each actual marking to its distinct basis vector. -/
theorem surfaceCharacterCocycle_gSig (x : Fin q × Bool) :
    (surfaceCharacterCocycle q).readPath (gSig q (x.1.val, x.2)) =
      Multiplicative.ofAdd (Finsupp.single (x.1.val, x.2) (1 : ℤ)) := by
  erw [surfaceCharacterCocycle, OrdCocycle.pullback_readPath]
  have h := (presCoc (genusW characterRel characterA characterB q) characterGen
    (characterRel_read q)).readPath_htpy
      (genus_hread characterRel characterA characterB q PUnit.unit.{1} (x.1.val, x.2))
  simp at h
  erw [h]
  have hl : genusLw characterA characterB q PUnit.unit.{1} (x.1.val, x.2) =
      [((x.1.val, x.2), true)] := by
    obtain ⟨i, b⟩ := x
    cases b <;>
      simp [genusLw, sLet, Nat.mod_eq_of_lt i.isLt, characterA, characterB,
        show (4 * i.val + 1) / 4 = i.val from by omega]
  erw [hl]
  exact reading_genClass _ _ _ _

/-- Evaluating this character extracts precisely the coefficient of each actual cap face. -/
theorem surfaceCharacter_capSurfaceChain2 (c : (cappedSpineCx q).F →₀ ℤ)
    (x : Fin q × Bool) :
    (surfaceCharacterCocycle q).chain1 (capSurfaceChain2 q c) (x.1.val, x.2) =
      c (.inr x) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single f n =>
      erw [capSurfaceChain2, Finsupp.linearCombination_single, LinearMap.map_smul]
      obtain f | z := f
      · simp [capSurfaceFace]
      · change (n • (surfaceCharacterCocycle q).chain1
          (pathChain (gSig q (z.1.val, z.2)))) (x.1.val, x.2) = _
        erw [OrdCocycle.chain1_pathChain, surfaceCharacterCocycle_gSig]
        change (n • Finsupp.single (z.1.val, z.2) 1) (x.1.val, x.2) =
          (Finsupp.single (Sum.inr z) n) (Sum.inr x)
        simp [Finsupp.single_apply, Prod.ext_iff, Fin.ext_iff]

/-- Every actual capped-cover cycle has zero augmented coefficient on every cap face. -/
theorem cappedCoverCycle_cap_augmentation_zero (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) (x : Fin q × Bool) :
    Finsupp.mapDomain Prod.snd c (.inr x) = 0 := by
  obtain ⟨d, hd⟩ := capSurfaceCycle_boundary q c hc
  have h := (surfaceCharacterCocycle q).chain1_bdry2 d
  erw [hd] at h
  have he := congrArg (fun z : (ℕ × Bool) →₀ ℤ => z (x.1.val, x.2)) h
  simpa only [surfaceCharacter_capSurfaceChain2, Finsupp.zero_apply] using he

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


theorem controlledAugmentedChain2_old (d : (markedSpineCx q).F →₀ ℤ) :
    controlledAugmentedChain2 q (Finsupp.mapDomain Sum.inl d) =
      chain2 (markedSpineToFullCube q) d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => erw [Finsupp.mapDomain_add, map_add, hc, hd, map_add]
  | single f n =>
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single, controlledAugmentedChain2,
        Finsupp.linearCombination_single]
      change n • Finsupp.single ((markedSpineToFullCube q).onF f) 1 =
        Finsupp.mapDomain (markedSpineToFullCube q).onF (Finsupp.single f n)
      simp

/-- Every actual capped-cover cycle augments entirely into old spine faces, whose
full-cube image is an actual ordinary three-boundary. -/

theorem cappedCoverCycle_old_augmentation_cycle (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d := by
  obtain ⟨d, hd, y, hy⟩ := (show ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d by
    obtain ⟨d, hd⟩ := (show ∃ d : (markedSpineCx q).F →₀ ℤ, Finsupp.mapDomain Sum.inl d = (Finsupp.mapDomain Prod.snd c) by
      refine ⟨(Finsupp.mapDomain Prod.snd c).comapDomain Sum.inl Sum.inl_injective.injOn, ?_⟩
      apply Finsupp.mapDomain_comapDomain _ Sum.inl_injective
      intro f hf
      obtain f | x := f
      · simp
      · exact False.elim ((Finsupp.mem_support_iff.mp hf) ((cappedCoverCycle_cap_augmentation_zero q c hc) x)))
    obtain ⟨y, hy⟩ := controlledAugmentedCycle_boundary3 q c hc
    refine ⟨d, hd, y, ?_⟩
    erw [← hd, controlledAugmentedChain2_old] at hy
    exact hy)
  have hp : Comb.bdry2 (cappedSpineCx q) (Finsupp.mapDomain Prod.snd c) = 0 := by
    let f : Hom (cappedTreeCover q) (cappedSpineCx q) :=
      SpanningTree.treeCoverProj (cappedSpineTree q) (relSub (cappedSpinePresentation q)) _
    change Comb.bdry2 (cappedSpineCx q) (chain2 f c) = 0
    erw [bdry2_chain2, hc, map_zero]
  rw (config := { transparency := .default }) [← hd] at hp
  change Comb.bdry2 (cappedSpineCx q) (chain2 (cappedSpineIncl q) d) = 0 at hp
  rw (config := { transparency := .default }) [bdry2_chain2] at hp
  have hzero : Comb.bdry2 (markedSpineCx q) d = 0 := by
    convert hp using 1 <;>
      simp only [chain1, cappedSpineIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_id]
  exact ⟨d, hd, hzero, y, hy⟩

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- The actual old spine image of every capped-cover cycle, after ordinary normalization
and square coefficient recovery, is a genuine finite coordinate three-boundary. -/
theorem cappedCoverCycle_old_coordinate_boundary (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ (d : (markedSpineCx q).F →₀ ℤ)
      (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ),
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      Finsupp.lmapDomain ℤ ℤ (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
        (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))) =
      Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r := by
  obtain ⟨d, hd, hcycle, y, hy⟩ := cappedCoverCycle_old_augmentation_cycle q c hc
  obtain ⟨z, hz⟩ := normalized_boundary3 _ ⟨y, hy⟩
  have hdim : ∀ t ∈ z.support, t.1.2.2.2.spx.card ≤ 3 := by
    intro t _
    exact genus_chain_card_le_three q (genus_simplex_mem_faces q t.1.2.2.2.isSimplex)
  have hb : ∀ s ∈ (strictOrdBoundary3 z).support, s.1.2.2.spx.card ≤ 2 := by
    intro s hs
    rw [hz] at hs
    exact markedSpineToFullCube_normalized_dimension q d s hs
  obtain ⟨r, hr⟩ := qCube_three_coordinate_boundary_reconstruction z hdim hb
  refine ⟨d, r, hd, hcycle, ?_⟩
  rwa [hz] at hr

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]



/-- Normalization creates no coefficient at a flag through the removed positive vertex. -/
theorem markedSpineToFullCube_normalized_zero_at_origin (d : (markedSpineCx q).F →₀ ℤ)
    (t : StrictOrdTri (QCube (cmpRel (GenusVertex q))))
    (ht : t.1.1.spx = ∅ ∧ t.1.1.sgn = 0) :
    normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) t = 0 := by
  erw [normalizeOrdChain2, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have hn : normalizeOrdTriangle a t = 0 := by
    unfold normalizeOrdTriangle
    split_ifs with h
    · by_cases he : ⟨a.1, h⟩ = t
      · have hfirst := congrArg (fun x : StrictOrdTri (QCube (cmpRel (GenusVertex q))) =>
          x.1.1) he
        have hnot := (show ¬ (a.1.1.spx = ∅ ∧ a.1.1.sgn = 0) by
          classical
          obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
          exact ((genusSpineCellToOld q f.1.1.1).2))
        erw [hfirst] at hnot
        exact False.elim (hnot ht)
      · simp_all
    · simp
  change (((chain2 (markedSpineToFullCube q) d) a) • normalizeOrdTriangle a) t = 0
  rw (config := { transparency := .default }) [Finsupp.smul_apply, hn, smul_zero]

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineCycle_positive_square_zero (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (s : QSquare (cmpRel (GenusVertex q))) (hs : s.1.sgn = 0) :
    qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)) s = 0 := by
  have hcycle : Comb.bdry2 (orderCx (QCube (cmpRel (GenusVertex q))))
      (chain2 (markedSpineToFullCube q) d) = 0 := by
    rw [bdry2_chain2, hd, map_zero]
  exact qSquareCycleCoefficients_positive_zero _
    (markedSpineToFullCube_normalized_dimension q d)
    (normalizeOrdChain2_cycle _ hcycle)
    (markedSpineToFullCube_normalized_zero_at_origin q d) s hs

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

def qThreeCoordinateChain : (QThreeCube A →₀ ℤ) →ₗ[ℤ] (Cube V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun c : QThreeCube A => qCubeToCoordinate c.1)

omit [LinearOrder V] in
theorem qThreeCutFaceChain_apply (r : QThreeCube A →₀ ℤ) (σ : Finset V) :
    qThreeCutFaceChain r σ = qThreeCoordinateChain r (posCube σ) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp_all
  | single c n =>
      rw [qThreeCutFaceChain, Finsupp.linearCombination_single]
      simp only [qThreeCoordinateChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      by_cases hsgn : c.1.sgn = 0
      · by_cases hσ : σ = c.1.spx
        · subst σ
          simp [hsgn, Finsupp.single_apply, qCube_coordinate_pos_iff, eq_comm]
        · simp [hsgn, qCube_coordinate_pos_iff, hσ]
      · simp [hsgn, qCube_coordinate_pos_iff]

/-- The finite coordinate three-chain has precisely the ordinary boundary supplied by
its actual six-facet chains. -/
theorem qThreeCoordinateChain_boundary (r : QThreeCube A →₀ ℤ) (g : Cube V) :
    bdry (qThreeCoordinateChain r) g =
      Finsupp.linearCombination ℤ
        (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r g := by
  induction r using Finsupp.induction_linear with
  | zero => simp [bdry]
  | add r s hr hs =>
      simp only [map_add, Finsupp.add_apply]
      rw [← hr, ← hs]
      simp only [bdry, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  | single c n =>
      rw [Finsupp.linearCombination_single, Finsupp.smul_apply,
        qCubeCoordinateFacetChain_apply]
      simp only [qThreeCoordinateChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        bdry, cubeBdry_inl, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases he : Function.update g j CubeCoord.free = qCubeToCoordinate c.1
      · grind
      · simp_all

/-- Vanishing of ordinary positive-square boundary coefficients makes the actual cut
coefficient chain a simplicial cycle. -/
theorem qThreeCutFaceChain_cycle (r : QThreeCube A →₀ ℤ)
    (hpos : ∀ σ : Finset V,
      Finsupp.linearCombination ℤ
        (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r (posCube σ) = 0) :
    simpBdry (qThreeCutFaceChain r) = 0 := by
  funext σ
  have he := qThreeCoordinateChain_boundary r (posCube σ)
  rw [hpos σ, bdry_posCube] at he
  simpa only [simpBdry, qThreeCutFaceChain_apply, Pi.zero_apply] using he

omit [LinearOrder V] in
/-- Nonzero cut coefficients occur only on actual three-vertex simplices. -/
theorem qThreeCutFaceChain_support (r : QThreeCube A →₀ ℤ) (σ : Finset V)
    (hσ : qThreeCutFaceChain r σ ≠ 0) : σ.card = 3 ∧ IsSimplex A σ := by
  rw [qThreeCutFaceChain_apply] at hσ
  have hmem := Finsupp.mem_support_iff.mpr hσ
  obtain ⟨c, _, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  have hs : c.1.spx = σ := by
    have h := congrArg freeSet he
    simpa using h
  rw [← hs]
  exact ⟨c.2, c.1.isSimplex⟩

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- Coordinate transport preserves vanishing of all positive square coefficients. -/
theorem qSquareCoordinate_positive_zero (r : QSquare A →₀ ℤ)
    (hr : ∀ c : QSquare A, c.1.sgn = 0 → r c = 0) (σ : Finset V) :
    Finsupp.lmapDomain ℤ ℤ (fun c : QSquare A => qCubeToCoordinate c.1) r (posCube σ) = 0 := by
  let f : QSquare A → Cube V := fun c => qCubeToCoordinate c.1
  have hinj : Function.Injective f := by
    intro c d he
    exact Subtype.ext (qCubeToCoordinate_injective he)
  change Finsupp.mapDomain f r (posCube σ) = 0
  by_cases hσ : posCube σ ∈ Set.range f
  · obtain ⟨c, hc⟩ := hσ
    rw [← hc, Finsupp.mapDomain_apply_of_injective hinj]
    exact hr c ((qCube_coordinate_pos_iff c.1 σ).mp hc.symm).2
  · exact Finsupp.mapDomain_notin_range _ _ hσ

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


/-- The cut correction of an actual ordinary boundary of an old-spine cycle is killed
by the already constructed geometric genus collapse. -/
theorem genus_cutFaceChain_collapse_zero_of_old_boundary (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ)
    (he : Finsupp.lmapDomain ℤ ℤ
      (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
      (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))) =
      Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (Sum.elim 0 (fun σ => -qThreeCutFaceChain r σ)) = 0 := by
  apply genusChainCollapse_cutSurface_eq_zero q (qThreeCutFaceChain r)
    (by
      apply qThreeCutFaceChain_cycle
      intro σ
      rw [← he]
      exact qSquareCoordinate_positive_zero _ (markedSpineCycle_positive_square_zero q d hd) σ)
  · intro σ hnot
    by_contra hn
    exact hnot (qThreeCutFaceChain_support r σ hn).1
  · intro σ hnot
    by_contra hn
    exact hnot (genus_simplex_mem_faces q (qThreeCutFaceChain_support r σ hn).2)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


/-- Every capped-cover cycle has an actual old-spine augmentation whose recovered
ordinary coordinate chain is killed by the chosen geometric genus collapse. -/
theorem cappedCoverCycle_oldCoordinate_collapse_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
        (Finsupp.lmapDomain ℤ ℤ Sum.inl
          (Finsupp.lmapDomain ℤ ℤ
            (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
            (qSquareCycleCoefficients
              (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))))) = 0 := by
  obtain ⟨d, r, hd, hcycle, hr⟩ := cappedCoverCycle_old_coordinate_boundary q c hc
  exact ⟨d, hd, hcycle, (by
    let x := Finsupp.lmapDomain ℤ ℤ
      (Sum.inl : Cube (GenusVertex q) → Cube (GenusVertex q) ⊕ Finset (GenusVertex q))
      (Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r)
    have hsplit : (qThreeTruncatedCoordinateBoundary r) =
        x +
          Sum.elim (0 : Cube (GenusVertex q) → ℤ) (fun σ => -qThreeCutFaceChain r σ) := by
      funext f
      rw [qThreeTruncatedCoordinateBoundary_split, Finsupp.sub_apply]
      cases f with
      | inl g =>
          have hz : Finsupp.mapDomain
              Sum.inr
              (qThreeCutFaceChain r) (Sum.inl g) = 0 :=
            Finsupp.mapDomain_notin_range _ _ (by rintro ⟨σ, h⟩; cases h)
          simp [Finsupp.lmapDomain_apply, hz, x]
      | inr σ =>
          have hc : Finsupp.mapDomain
              (Sum.inr : Finset (GenusVertex q) → Cube (GenusVertex q) ⊕ Finset (GenusVertex q))
              (qThreeCutFaceChain r) (Sum.inr σ) = qThreeCutFaceChain r σ :=
            Finsupp.mapDomain_apply_of_injective Sum.inr_injective _ σ
          simp [Finsupp.lmapDomain_apply, hc, x, sub_eq_add_neg]
    have hz := genus_truncated_three_boundary_collapse_zero q r
    rw [hsplit, CollapseChain.cmap_add,
      genus_cutFaceChain_collapse_zero_of_old_boundary q d hcycle r hr, add_zero] at hz
    rw [hr]
    exact hz)⟩

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


/-- Every genuine two-flag of the surviving spine ends at an ordinary retained square,
not at a cut cell (all cut triangles were removed). -/
theorem markedSpineFace_top_old (f : (markedSpineCx q).F) :
    ∃ a : QOld (cmpRel (GenusVertex q)), f.1.1.2.2.1 = Sum.inl a := by
  have hd := (show truncatedCellDimension f.1.1.2.2.1 = 2 by
    have h01 := genusSpineCellDimension_strictMono q f.1.2.1
    have h12 := genusSpineCellDimension_strictMono q f.1.2.2
    change truncatedCellDimension f.1.1.1.1 < truncatedCellDimension f.1.1.2.1.1 at h01
    change truncatedCellDimension f.1.1.2.1.1 < truncatedCellDimension f.1.1.2.2.1 at h12
    have hmax := genusSpineCell_dimension_le_two q f.1.1.2.2
    omega)
  cases hc : f.1.1.2.2.1 with
  | inl a => simp
  | inr σ =>
      have hs := f.1.1.2.2.2
      rw [hc] at hs
      have hcard := genusSpine_cut_card_le_two q σ hs
      rw [hc] at hd
      change σ.1.card - 1 = 2 at hd
      omega

/-- A nonzero recovered square coefficient comes from an actual ordinary two-cell
surviving the chosen genus collapse. -/
theorem markedSpine_square_coefficient_support (d : (markedSpineCx q).F →₀ ℤ)
    (s : QSquare (cmpRel (GenusVertex q)))
    (hs : qSquareCycleCoefficients
      (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)) s ≠ 0) :
    ∃ a : QOld (cmpRel (GenusVertex q)),
      (Sum.inl a : GenusTruncatedCell q) ∈ genusSpineCellSet q ∧ a.1 = s.1 := by
  classical
  change normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)
    (squareFlag s.1 (qSquareLeft s) (qSquareRight s) (qSquare_directions_ne s)
      (qSquare_free_directions s) (false, 0, false)) ≠ 0 at hs
  obtain ⟨t, ht, he⟩ := normalizeOrdChain2_support _ _ (Finsupp.mem_support_iff.mpr hs)
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  have htop := congrArg (fun t => t.2.2) he
  simp only [squareFlag_top] at htop
  rw [← hf] at htop
  obtain ⟨a, ha⟩ := markedSpineFace_top_old q f
  have hmem := f.1.1.2.2.2
  rw [ha] at hmem
  refine ⟨a, hmem, ?_⟩
  change (genusSpineCellToOld q f.1.1.2.2).1 = s.1 at htop
  simpa [genusSpineCellToOld, truncatedCellRetraction, ha] using htop

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def markedSpineSquareCoefficients : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    (QSquare (cmpRel (GenusVertex q)) →₀ ℤ) :=
  qSquareCycleCoefficients.comp (normalizeOrdChain2.comp (chain2 (markedSpineToFullCube q)))

def markedSpineCoordinateChain : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    (Cube (GenusVertex q) →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ
    (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)).comp
      (markedSpineSquareCoefficients q)

def markedSpineExtendedCoordinateChain : ((markedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    ((Cube (GenusVertex q) ⊕ Finset (GenusVertex q)) →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ Sum.inl).comp (markedSpineCoordinateChain q)


theorem markedSpineExtendedCoordinateChain_zero_on_removed_face
    (d : (markedSpineCx q).F →₀ ℤ) (f : Cube (GenusVertex q) ⊕ Finset (GenusVertex q))
    (hf : f ∈ (genusChainCollapse q).map Prod.snd) :
    markedSpineExtendedCoordinateChain q d f = 0 := by
  cases f with
  | inl g =>
      change Finsupp.mapDomain
        Sum.inl
        (markedSpineCoordinateChain q d) (Sum.inl g) = 0
      rw [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]
      exact (by
        by_contra hn
        have hmem := Finsupp.mem_support_iff.mpr hn
        obtain ⟨s, hs, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
        obtain ⟨a, ha, hae⟩ := markedSpine_square_coefficient_support q d s
          (Finsupp.mem_support_iff.mp hs)
        have hnot := ha.2
        change Sum.inl (qCubeToCoordinate a.1) ∉ (genusChainCollapse q).map Prod.snd at hnot
        rw [hae, he] at hnot
        exact hnot hf)
  | inr σ =>
      exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨g, he⟩; cases he)

/-- The actual recovered coordinate chain of every old-spine two-chain is fixed by the
chosen geometric collapse because it has no coefficient on a removed face. -/
theorem markedSpineExtendedCoordinateChain_fixed (d : (markedSpineCx q).F →₀ ℤ) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (markedSpineExtendedCoordinateChain q d) = markedSpineExtendedCoordinateChain q d := by
  apply CollapseChain.cmap_of_forall_eq_zero
  intro p hp
  exact markedSpineExtendedCoordinateChain_zero_on_removed_face q d p.2
    (List.mem_map.mpr ⟨p, hp, rfl⟩)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb ASC
variable (q : ℕ) [NeZero q]

theorem genus_positive_old_cell_survives (c : QOld (cmpRel (GenusVertex q)))
    (hsgn : c.1.sgn = 0) (hdim : c.1.spx.card ≤ 2) :
    (Sum.inl c : GenusTruncatedCell q) ∈ genusSpineCellSet q := by
  refine ⟨hdim, ?_⟩
  intro hremoved
  obtain ⟨⟨t, f⟩, hp, he⟩ := List.mem_map.mp hremoved
  change f = Sum.inl (qCubeToCoordinate c.1) at he
  subst f
  have hi := (genusChainCollapse_isPairCollapse q).pair_inc hp
  by_cases htwo : c.1.spx.card = 2
  · simp only [spineInc, freeSet_qCubeToCoordinate, htwo] at hi
    rw [qCubeToCoordinate_sgn_zero c.1 hsgn] at hi
    obtain ⟨j, _, _, ht⟩ := mem_cofaces.mp hi
    have hpos : t = posCube (freeSet t) := by
      rw [ht, update_posCube, freeSet_posCube]
    exact genusChainCollapse_old_face_nonpositive q t (qCubeToCoordinate c.1) hp hpos
  · simp [spineInc, freeSet_qCubeToCoordinate, htwo] at hi


/-- The retained-cube retraction is an actual endomorphism of the surviving spine. -/
def genusSpineRetraction (c : GenusSpineCell q) : GenusSpineCell q :=
  ⟨oldCellIncl (truncatedCellRetraction c.1), (by
    cases hc : c.1 with
    | inl a => simpa [oldCellIncl, truncatedCellRetraction, hc] using c.2
    | inr σ =>
        have hs := c.2
        rw [hc] at hs
        have hcard := genusSpine_cut_card_le_two q σ hs
        apply genus_positive_old_cell_survives q (posQCube ⟨σ.1, σ.2⟩) rfl hcard)⟩

theorem genusSpineRetraction_monotone : Monotone (genusSpineRetraction q) :=
  fun _ _ h => oldCellIncl_monotone (truncatedCellRetraction_monotone h)

theorem genusSpine_le_retraction (c : GenusSpineCell q) : c ≤ genusSpineRetraction q c :=
  truncatedCell_le_retraction c.1

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


/-- The actual pointwise order comparison supplies a finite full-nerve homotopy chain. -/
theorem genusSpine_cycle_retraction_boundary (c : (orderCx (GenusSpineCell q)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (GenusSpineCell q)) c = 0) :
    ∃ y : OrdTet (GenusSpineCell q) →₀ ℤ, ordBoundary3 y =
      chain2 (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) c - c := by
  let g := genusSpineRetraction q
  let p := Nerve.prism id g (ordNerveChain2 c)
  have hp  :=
    Nerve.prism_mem_inc monotone_id (genusSpineRetraction_monotone q)
      (genusSpine_le_retraction q) (ordNerveChain2_mem_inc c)
  have hd := (ordNerveChain2_cycle_iff c).mpr hc
  have hb : Nerve.bdry p = Nerve.cmap g (ordNerveChain2 c) - ordNerveChain2 c := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry id g (ordNerveChain2 c)
  let b := Nerve.lengthProjection 4 p
  have hbi : b ∈ Nerve.Inc (GenusSpineCell q) := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 4 b = b := Nerve.lengthProjection_idempotent _ _
  have hbdry : Nerve.bdry b = Nerve.lengthProjection 3
      (Nerve.cmap g (ordNerveChain2 c)) - ordNerveChain2 c := by
    dsimp only [b]
    erw [← Nerve.lengthProjection_bdry, hb, map_sub, ordNerveChain2_lengthProjection]
  refine ⟨decodeOrdNerve3 b, ?_⟩
  apply ordNerveChain2_injective
  erw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hbi, hdeg, map_sub, hbdry]
  erw [← ordNerveChain2_chain2 g (genusSpineRetraction_monotone q),
    ordNerveChain2_lengthProjection]

/-- On the actual two-dimensional surviving spine, the retained-cube retraction fixes
normalized two-cycles exactly because there are no nondegenerate three-flags. -/
theorem genusSpine_normalized_retraction_cycle (c : (orderCx (GenusSpineCell q)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (GenusSpineCell q)) c = 0) :
    normalizeOrdChain2
      (chain2 (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) c) =
      normalizeOrdChain2 c := by
  obtain ⟨y, hy⟩ := genusSpine_cycle_retraction_boundary q c hc
  haveI := (show IsEmpty (StrictOrdTet (GenusSpineCell q)) by
    refine ⟨fun t => ?_⟩
    have h01 := genusSpineCellDimension_strictMono q t.2.1
    have h12 := genusSpineCellDimension_strictMono q t.2.2.1
    have h23 := genusSpineCellDimension_strictMono q t.2.2.2
    change truncatedCellDimension t.1.1.1 < truncatedCellDimension t.1.2.1.1 at h01
    change truncatedCellDimension t.1.2.1.1 < truncatedCellDimension t.1.2.2.1.1 at h12
    change truncatedCellDimension t.1.2.2.1.1 < truncatedCellDimension t.1.2.2.2.1 at h23
    have hmax := genusSpineCell_dimension_le_two q t.1.2.2.2
    omega)
  have hzero : normalizeOrdChain3 y = 0 := by
    ext t
    exact isEmptyElim t
  have he := congrArg normalizeOrdChain2 hy
  erw [normalizeOrdChain2_ordBoundary3, hzero, map_zero, map_sub] at he
  exact (sub_eq_zero.mp he.symm)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


/-- For an actual old-spine cycle, zero recovered square coefficients imply its normalized
full-cube image is the zero chain by the proved two-cycle subdivision dictionary. -/
theorem markedSpine_normalized_image_zero_of_coefficients (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (hcoeff : markedSpineSquareCoefficients q d = 0) :
    normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) = 0 := by
  have hcycle : Comb.bdry2 (orderCx (QCube (cmpRel (GenusVertex q))))
      (chain2 (markedSpineToFullCube q) d) = 0 := by
    rw [bdry2_chain2, hd, map_zero]
  have he := qCube_twoCycle_reconstruction _
    (markedSpineToFullCube_normalized_dimension q d) (normalizeOrdChain2_cycle _ hcycle)
  change qSquareChainSubdivision (markedSpineSquareCoefficients q d) = _ at he
  rw [hcoeff, map_zero] at he
  exact he.symm

/-- Every actual capped-cover cycle augments into an old-spine cycle whose normalized
full-cube chain image is exactly zero. -/
theorem cappedCoverCycle_old_normalized_image_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) = 0 := by
  obtain ⟨d, hd, hcycle, hcollapse⟩ := cappedCoverCycle_oldCoordinate_collapse_zero q c hc
  exact ⟨d, hd, hcycle, markedSpine_normalized_image_zero_of_coefficients q d hcycle
    (by
      have hfun : (markedSpineExtendedCoordinateChain q d :
          (Cube (GenusVertex q) ⊕ Finset (GenusVertex q)) → ℤ) = 0 := by
        rw [← markedSpineExtendedCoordinateChain_fixed q d]
        exact hcollapse
      have hfin : markedSpineExtendedCoordinateChain q d = 0 := by
        ext f
        exact congrFun hfun f
      have hcoord : markedSpineCoordinateChain q d = 0 := by
        apply Finsupp.mapDomain_injective
          Sum.inl_injective
        rw [Finsupp.mapDomain_zero]
        exact hfin
      apply Finsupp.mapDomain_injective
        (show Function.Injective
          (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1) from
          fun _ _ h => Subtype.ext (qCubeToCoordinate_injective h))
      rw [Finsupp.mapDomain_zero]
      exact hcoord)⟩

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A monotone map injective on the vertices supporting a strict two-chain reflects
zero of its actual normalized chain image. -/
theorem normalizedStrictChain2_zero_of_injOn (f : P → Q) (hf : Monotone f)
    (S : Set P) (hinj : Set.InjOn f S) (r : StrictOrdTri P →₀ ℤ)
    (hr : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hz : normalizedStrictChain2 f hf r = 0) : r = 0 := by
  classical
  let D := {t : StrictOrdTri P // t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S}
  let incl : D → StrictOrdTri P := Subtype.val
  have hstrict (t : D) : f t.1.1.1 < f t.1.1.2.1 ∧ f t.1.1.2.1 < f t.1.1.2.2 := by
    constructor
    · exact lt_of_le_of_ne (hf t.1.2.1.le)
        (fun he => t.1.2.1.ne (hinj t.2.1 t.2.2.1 he))
    · exact lt_of_le_of_ne (hf t.1.2.2.le)
        (fun he => t.1.2.2.ne (hinj t.2.2.1 t.2.2.2 he))
  let image : D → StrictOrdTri Q := fun t =>
    ⟨(f t.1.1.1, f t.1.1.2.1, f t.1.1.2.2), hstrict t⟩
  have himage : Function.Injective image := by
    intro a b he
    ext
    apply Subtype.ext
    apply Prod.ext
    · exact hinj a.2.1 b.2.1 (congrArg (fun t : StrictOrdTri Q => t.1.1) he)
    · apply Prod.ext
      · exact hinj a.2.2.1 b.2.2.1 (congrArg (fun t : StrictOrdTri Q => t.1.2.1) he)
      · exact hinj a.2.2.2 b.2.2.2 (congrArg (fun t : StrictOrdTri Q => t.1.2.2) he)
  let z := r.comapDomain incl Subtype.val_injective.injOn
  have hrecon : Finsupp.mapDomain incl z = r := by
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro t ht
    exact ⟨⟨t, hr t ht⟩, rfl⟩
  have hmap w :
      normalizedStrictChain2 f hf (Finsupp.mapDomain incl w) = Finsupp.mapDomain image w := by
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w z hw hz => simp only [Finsupp.mapDomain_add, map_add, hw, hz]
    | single t n =>
        rw [Finsupp.mapDomain_single, normalizedStrictChain2_single, Finsupp.mapDomain_single]
        have hn : normalizeOrdTriangle ((orderCxMap f hf).onF ((strictOrderIncl P).onF (incl t))) =
            Finsupp.single (image t) 1 := by
          change (if h : f t.1.1.1 < f t.1.1.2.1 ∧ f t.1.1.2.1 < f t.1.1.2.2 then
            Finsupp.single ⟨(f t.1.1.1, f t.1.1.2.1, f t.1.1.2.2), h⟩ 1
            else 0) = Finsupp.single (image t) 1
          rw [dif_pos (hstrict t)]
        rw [hn]
        simp
  have hz' : Finsupp.mapDomain image z = 0 := by rw [← hmap, hrecon, hz]
  have he : z = 0 := Finsupp.mapDomain_injective himage (hz'.trans Finsupp.mapDomain_zero.symm)
  rw [← hrecon, he, Finsupp.mapDomain_zero]

end FiniteChains.Comb
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def genusSpineOrdinaryCells : Set (GenusSpineCell q) :=
  {c | ∃ a : QOld (cmpRel (GenusVertex q)), c.1 = Sum.inl a}

def genusSpineCellToFullCube (c : GenusSpineCell q) : QCube (cmpRel (GenusVertex q)) :=
  (genusSpineCellToOld q c).1

theorem genusSpineCellToFullCube_monotone : Monotone (genusSpineCellToFullCube q) :=
  fun _ _ h => genusSpineCellToOld_monotone q h


theorem genusSpineRetraction_ordinary (c : GenusSpineCell q) :
    genusSpineRetraction q c ∈ genusSpineOrdinaryCells q :=
  ⟨truncatedCellRetraction c.1, rfl⟩

theorem genusSpine_normalized_retraction_support
    (z : (orderCx (GenusSpineCell q)).F →₀ ℤ)
    (t : StrictOrdTri (GenusSpineCell q))
    (ht : t ∈ (normalizeOrdChain2 (chain2
      (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) z)).support) :
    t.1.1 ∈ genusSpineOrdinaryCells q ∧ t.1.2.1 ∈ genusSpineOrdinaryCells q ∧
      t.1.2.2 ∈ genusSpineOrdinaryCells q := by
  classical
  obtain ⟨a, ha, he⟩ := normalizeOrdChain2_support _ _ ht
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  erw [← he, ← hb]
  exact ⟨genusSpineRetraction_ordinary q b.1.1,
    genusSpineRetraction_ordinary q b.1.2.1, genusSpineRetraction_ordinary q b.1.2.2⟩

/-- Every actual strict two-cycle of the surviving spine is supported on retained
ordinary cells, by the proved dimension-two retraction homotopy. -/
theorem genusSpine_cycle_ordinary_support (d : (genusSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (genusSpineCx q) d = 0) (t : (genusSpineCx q).F)
    (ht : t ∈ d.support) :
    t.1.1 ∈ genusSpineOrdinaryCells q ∧ t.1.2.1 ∈ genusSpineOrdinaryCells q ∧
      t.1.2.2 ∈ genusSpineOrdinaryCells q := by
  let z := chain2 (strictOrderIncl (GenusSpineCell q)) d
  have hcycle : Comb.bdry2 (orderCx (GenusSpineCell q)) z = 0 := by
    erw [bdry2_chain2, hd, map_zero]
  have he := genusSpine_normalized_retraction_cycle q z hcycle
  have hnorm  := normalizeOrdChain2_inclusion d
  erw [hnorm] at he
  apply genusSpine_normalized_retraction_support q z t
  rwa [he]

/-- The actual normalized map to full quotient cubes is faithful on surviving-spine
cycles; this is proved from ordinary-cell injectivity and the actual spine retraction. -/
theorem genusSpine_cycle_zero_of_normalized_full_image (d : (genusSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (genusSpineCx q) d = 0)
    (hz : normalizedStrictChain2 (genusSpineCellToFullCube q)
      (genusSpineCellToFullCube_monotone q) d = 0) : d = 0 :=
  normalizedStrictChain2_zero_of_injOn _ _ (genusSpineOrdinaryCells q)
    (by
      rintro c ⟨a, ha⟩ d ⟨b, hb⟩ he
      have hab : a = b := Subtype.ext (by
        simpa [genusSpineCellToFullCube, genusSpineCellToOld, truncatedCellRetraction, ha, hb] using he)
      apply Subtype.ext
      simp_all) d
    (genusSpine_cycle_ordinary_support q d hd) hz

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- The actual normalized full-cube comparison reflects zero on marked-spine cycles,
by the retained-cell retraction and faithful ordinary triangle coordinates. -/
theorem markedSpine_cycle_zero_of_normalized_full_image (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (hz : normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) = 0) : d = 0 := by
  let c := chain2 (componentIncl (genusSpineCx q) (spineBase q)) d
  have hcycle : Comb.bdry2 (genusSpineCx q) c = 0 := by
    erw [bdry2_chain2, hd, map_zero]
  have he : normalizedStrictChain2 (genusSpineCellToFullCube q)
      (genusSpineCellToFullCube_monotone q) c =
      normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) := by
    change normalizeOrdChain2 (Finsupp.mapDomain
        (orderCxMap (genusSpineCellToFullCube q) (genusSpineCellToFullCube_monotone q)).onF
        (Finsupp.mapDomain (strictOrderIncl (GenusSpineCell q)).onF
          (Finsupp.mapDomain (componentIncl (genusSpineCx q) (spineBase q)).onF d))) =
      normalizeOrdChain2 (Finsupp.mapDomain (markedSpineToFullCube q).onF d)
    erw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    rfl
  have hc := genusSpine_cycle_zero_of_normalized_full_image q c hcycle (he.trans hz)
  apply Finsupp.mapDomain_injective
    (componentIncl_injective_onF (spineBase q))
  erw [Finsupp.mapDomain_zero]
  exact hc

/-- Every actual capped-cover cycle has zero old-spine augmentation. -/
theorem cappedCoverCycle_old_augmentation_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧ d = 0 := by
  obtain ⟨d, hd, hcycle, hz⟩ := cappedCoverCycle_old_normalized_image_zero q c hc
  exact ⟨d, hd, markedSpine_cycle_zero_of_normalized_full_image q d hcycle hz⟩

/-- The complete augmentation of every actual capped-cover two-cycle is zero. This
includes all old spine faces as well as the previously proved cap coefficients. -/
theorem cappedCoverCycle_total_augmentation_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    Finsupp.mapDomain Prod.snd c = 0 := by
  obtain ⟨d, hd, rfl⟩ := cappedCoverCycle_old_augmentation_zero q c hc
  erw [Finsupp.mapDomain_zero] at hd
  exact hd.symm

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

/-- Collapsing the spanning tree reflects the two-cycle condition. -/
theorem cappedPresentationCycle_treeCycle
    (c : (univCover (cappedSpinePresentation q)).F →₀ ℤ)
    (hc : Comb.bdry2 (univCover (cappedSpinePresentation q)) c = 0) :
    Comb.bdry2 (cappedTreeCover q) c = 0 := by
  let T := cappedSpineTree q
  let N := relSub (cappedSpinePresentation q)
  have hN : ∀ f, SpanningTree.treeRel T f ∈ N := by
    intro f
    erw [cappedSpineTree_rel]
    exact rel_mem_relSub (cappedSpinePresentation q) f
  have hp : SpanningTree.piE T N (Comb.bdry2 (cappedTreeCover q) c) = 0 := by
    erw [SpanningTree.piE_bdry2]
    have hrel  :=
      cappedSpineTree_rel q
    change Finsupp.linearCombination ℤ
      (fun f => pathChain (liftPath
        (FreeGroup.toWord (SpanningTree.treeRel (cappedSpineTree q) f.2)) f.1)) c = 0
    erw [hrel]
    exact hc
  exact SpanningTree.treeChain_eq_zero (T := T) (N := N) (hN := hN)
    (SpanningTree.support_isTree_of_piE_eq_zero (T := T) (N := N) hp)
    (Comb.bdry1_bdry2 (X := cappedTreeCover q) c)

/-- The genuine capped presentation is Cockcroft. -/
theorem cappedSpinePresentation_isCockcroft :
    _root_.FiniteChains.IsCockcroft (cappedSpinePresentation q) := by
  apply (coverCycles_cockcroft_iff (cappedSpinePresentation q)).mp
  intro c hc
  exact cappedCoverCycle_total_augmentation_zero q c
    (cappedPresentationCycle_treeCycle q c hc)

end FiniteChains.Davis.Genus
end

namespace FiniteChains

variable {α J : Type*} [DecidableEq α] (ρ : J → FreeGroup α)

theorem fs_coverSecondBoundary_apply (u : J →₀ CoverRing (relSub ρ)) (i : α) :
    coverSecondBoundary (relSub ρ) ρ u i =
      ∑ j ∈ u.support, u j * foxMatrixPres ρ i j := by
  rw [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp
  change u j * proj (relSub ρ) (fox i (ρ j)) = _
  rw [foxMatrixPres, proj_eq_quotRingHom]

/-- A finitely supported chain whose boundary is divisible by `m` differs from a cycle
by `m` times a finitely supported chain. -/
theorem fs_exists_cycle_of_boundary_nsmul (m : ℕ)
    (u : J →₀ CoverRing (relSub ρ))
    (hu : ∀ i, ∃ w, coverSecondBoundary (relSub ρ) ρ u i = m • w) :
    ∃ u' : J →₀ CoverRing (relSub ρ),
      coverSecondBoundary (relSub ρ) ρ u' = 0 ∧
      ∃ z : J →₀ CoverRing (relSub ρ), u = u' + m • z := by
  let d := coverSecondBoundary (relSub ρ) ρ
  have hρ := rel_mem_relSub' ρ
  by_cases hm : m = 0
  · subst m
    refine ⟨u, ?_, 0, by simp⟩
    apply Finsupp.ext
    intro i
    obtain ⟨w, hw⟩ := hu i
    simpa using hw
  choose w hw using hu
  have hs : (Function.support w).Finite := by
    apply (d u).support.finite_toSet.subset
    intro i hi
    by_contra hn
    have hz : d u i = 0 := by simpa using hn
    have he  := (hw i).symm.trans hz
    exact hi ((nsmul_eq_zero_iff_of_ne m hm (w i)).mp he)
  let wf  := Finsupp.ofSupportFinite w hs
  have hd : d u = m • wf := by
    apply Finsupp.ext
    intro i
    simpa [wf] using hw i
  have hwc : coverFirstBoundary (relSub ρ) wf = 0 := by
    have hz := coverFirstBoundary_coverSecondBoundary (relSub ρ) ρ hρ u
    rw [hd, map_nsmul] at hz
    exact (nsmul_eq_zero_iff_of_ne m hm _).mp hz
  obtain ⟨z, hz⟩ := exists_coverSecondBoundary_preimage
    (relSub ρ) ρ hρ le_sup_left wf hwc
  refine ⟨u - m • z, ?_, z, by abel⟩
  rw [map_sub, map_nsmul, hz, hd, sub_self]

end FiniteChains

namespace FiniteChains.Comb
open MonoidAlgebra
universe u
variable {α J : Type u} {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
variable {Q K : Type u} [Group Q]

theorem fs_mapDomain_prodMap_id_apply (Φ : (FreeGroup α ⧸ Nsub) →* Q)
    (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) (q : Q) (j : J) :
    Finsupp.mapDomain (Prod.map (⇑Φ) (id : J → J)) u (q, j)
      = (MonoidAlgebra.mapDomainRingHom ℤ Φ (fsCoords Nsub J u j)).coeff q := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, h₁, h₂]
      simp [map_add]
  | single p n =>
      obtain ⟨q₀, j₀⟩ := p
      rw [Finsupp.mapDomain_single, fsCoords_single]
      show (Finsupp.single (Φ q₀, j₀) n) (q, j)
        = (MonoidAlgebra.mapDomain Φ ((Finsupp.single j₀ (MonoidAlgebra.single q₀ n)) j)).coeff q
      by_cases hj : j = j₀
      · subst hj
        rw [Finsupp.single_eq_same, MonoidAlgebra.mapDomain_single, MonoidAlgebra.coeff_single, Finsupp.single_apply,
          Finsupp.single_apply]
        by_cases hq : Φ q₀ = q
        · simp [hq]
        · simp [hq, Prod.ext_iff]
      · simp_all

/-- **Pushing a two-chain of the cover to the next stage is zero iff its Fox coordinates
die.**  Here `Φ` is the map of deck groups and `g` the (injective) inclusion of the sets of
two-cells. -/
theorem fs_mapDomain_prodMap_eq_zero_iff (Φ : (FreeGroup α ⧸ Nsub) →* Q) (g : J → K)
    (hg : Function.Injective g) (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0 ↔
      ∀ j, MonoidAlgebra.mapDomainRingHom ℤ Φ (fsCoords Nsub J u j) = 0 := by
  have hfac : (Prod.map (⇑Φ) g) = (Prod.map id g) ∘ (Prod.map (⇑Φ) id) := by
    funext p; rfl
  have hinj : Function.Injective (Prod.map (id : Q → Q) g) :=
    Function.Injective.prodMap Function.injective_id hg
  rw [hfac, Finsupp.mapDomain_comp]
  constructor
  · intro h j
    have h0 : Finsupp.mapDomain (Prod.map (⇑Φ) id) u = 0 := by
      refine Finsupp.mapDomain_injective hinj ?_
      rw [h, Finsupp.mapDomain_zero]
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun q => ?_
    rw [← fs_mapDomain_prodMap_id_apply Φ u q j, h0]
    simp
  · intro h
    have h0 : Finsupp.mapDomain (Prod.map (⇑Φ) id) u = 0 := by
      refine Finsupp.ext fun p => ?_
      obtain ⟨q, j⟩ := p
      rw [fs_mapDomain_prodMap_id_apply Φ u q j, h j]
      simp
    rw [h0, Finsupp.mapDomain_zero]


variable [DecidableEq α]

/-- The actual cellular two-cycle condition, for arbitrary cell sets. -/
theorem fs_univCover_zero_pi2_iff (ρ : J → FreeGroup α)
    (Φ : PresGroup ρ →* Q) (g : J → K) (hg : Function.Injective g) :
    (∀ u : ((PresGroup ρ) × J) →₀ ℤ, bdry2 (univCover ρ) u = 0 →
        Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0) ↔
    (∀ v : J →₀ CoverRing (relSub ρ),
        (∀ i, ∑ j ∈ v.support, v j * foxMatrixPres ρ i j = 0) →
        Finsupp.mapDomain g
          (v.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _)) = 0) := by
  have hcycle : ∀ u : ((PresGroup ρ) × J) →₀ ℤ,
      bdry2 (univCover ρ) u = 0 ↔
      coverSecondBoundary (relSub ρ) ρ (fsCoords (relSub ρ) J u) = 0 := by
    intro u
    rw [fs_coverComplex_bdry2]
    exact (map_eq_zero_iff _ (fsCoords (relSub ρ) α).injective).symm
  constructor
  · intro H v hv
    let u := (fsCoords (relSub ρ) J).symm v
    have he : fsCoords (relSub ρ) J u = v := LinearEquiv.apply_symm_apply _ v
    have hc : bdry2 (univCover ρ) u = 0 := by
      rw [hcycle, he]
      apply Finsupp.ext
      intro i
      simpa only [fs_coverSecondBoundary_apply, Finsupp.zero_apply] using hv i
    have hz := H u hc
    rw [fs_mapDomain_prodMap_eq_zero_iff Φ g hg] at hz
    rw [mapDomain_mapRange_eq_zero_iff Φ g hg]
    simpa only [he] using hz
  · intro H u hu
    have hc := (hcycle u).mp hu
    have hz := H (fsCoords (relSub ρ) J u) (fun i => by
      have hi := congrArg (fun c => c i) hc
      simpa only [fs_coverSecondBoundary_apply, Finsupp.zero_apply] using hi)
    rw [mapDomain_mapRange_eq_zero_iff Φ g hg] at hz
    exact (fs_mapDomain_prodMap_eq_zero_iff Φ g hg u).mpr hz

end FiniteChains.Comb

namespace FiniteChains.PathSubdivision

open Set Topology
open scoped unitInterval

universe u v

def intervalPath (a b : unitInterval) : Path a b where
  toFun s := ⟨(1 - (s : ℝ)) * a + s * b,by
    have hs : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.property.2
    constructor
    · exact add_nonneg (mul_nonneg hs a.property.1) (mul_nonneg s.property.1 b.property.1)
    · have h1 := mul_le_mul_of_nonneg_left a.property.2 hs
      have h2 := mul_le_mul_of_nonneg_left b.property.2 s.property.1
      nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp


theorem interval_simplyConnected : SimplyConnectedSpace unitInterval := by
  letI := (convex_Icc (0 : ℝ) 1).contractibleSpace
    ⟨0,by simp⟩
  infer_instance

variable {X : Type u} [TopologicalSpace X] {x y : X}

def cut (p : Path x y) (a b : unitInterval) : Path (p a) (p b) :=
  (intervalPath a b).map p.continuous

theorem cut_range (p : Path x y) {a b : unitInterval} (hab : a ≤ b) :
    Set.range (cut p a b) ⊆ p '' Set.Icc a b := by
  rintro z ⟨s,rfl⟩
  exact ⟨intervalPath a b s,(by
    change a ≤ (1 - (s : ℝ)) * a + s * b ∧
      (1 - (s : ℝ)) * a + s * b ≤ b
    have h1 := mul_nonneg s.property.1 (sub_nonneg.mpr (show a ≤ b from hab))
    have h2 := mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr (show a ≤ b from hab))
    constructor <;> nlinarith),rfl⟩

theorem cut_trans_homotopic (p : Path x y) (a b c : unitInterval) :
    ((cut p a b).trans (cut p b c)).Homotopic (cut p a c) := by
  letI := interval_simplyConnected
  have h := (SimplyConnectedSpace.paths_homotopic
    ((intervalPath a b).trans (intervalPath b c)) (intervalPath a c)).map p.toContinuousMap
  simpa only [Path.map_trans, Path.coe_toContinuousMap, cut] using h

theorem cut_self_homotopic (p : Path x y) (a : unitInterval) :
    (Path.refl (p a)).Homotopic (cut p a a) := by
  letI := interval_simplyConnected
  have h := (SimplyConnectedSpace.paths_homotopic (Path.refl a) (intervalPath a a)).map p.toContinuousMap
  have he : (Path.refl a).map p.continuous = Path.refl (p a) := by ext t; rfl
  rw [he] at h
  exact h

theorem cut_zero_one_homotopic (p : Path x y) :
    (cut p 0 1).Homotopic (p.cast p.source p.target) := by
  letI := interval_simplyConnected
  have h := (SimplyConnectedSpace.paths_homotopic (intervalPath 0 1) Path.id).map p.toContinuousMap
  have he : Path.id.map p.continuous = p.cast p.source p.target := by ext t; rfl
  rw [he] at h
  exact h

def concatenateCuts (p : Path x y) (t : ℕ → unitInterval) :
    (N : ℕ) → Path (p (t 0)) (p (t N))
  | 0 => Path.refl _
  | N+1 => (concatenateCuts p t N).trans (cut p (t N) (t (N+1)))

theorem concatenateCuts_homotopic (p : Path x y) (t : ℕ → unitInterval) (N : ℕ) :
    (concatenateCuts p t N).Homotopic (cut p (t 0) (t N)) := by
  induction N with
  | zero => exact cut_self_homotopic p _
  | succ N ih =>
    exact (ih.hcomp (Path.Homotopic.refl _)).trans (cut_trans_homotopic p _ _ _)

theorem exists_subdivision (p : Path x y) {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hp : ∀ s, ∃ i, p s ∈ U i) :
    ∃ (t : ℕ → unitInterval) (N : ℕ), t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      ∀ j < N, ∃ i, Set.range (cut p (t j) (t (j+1))) ⊆ U i := by
  obtain ⟨t,ht0,htm,⟨N,hN⟩,htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (fun s _ => Set.mem_iUnion.mpr (hp s))
  refine ⟨t,N,ht0,hN N le_rfl,htm,?_⟩
  intro j _
  obtain ⟨i,hi⟩ := htU j
  refine ⟨i,?_⟩
  intro z hz
  obtain ⟨s,hs,rfl⟩ := cut_range p (htm (Nat.le_succ j)) hz
  exact hi hs

end FiniteChains.PathSubdivision

namespace FiniteChains.OpenCoverPaths

open Set Topology CategoryTheory
open scoped unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X]

theorem property_cast_iff (P : ∀ {a b : X}, Path a b → Prop)
    {a b a' b' : X} (p : Path a b) (ha : a' = a) (hb : b' = b) :
    P (p.cast ha hb) ↔ P p := by
  subst a'; subst b'
  rfl

theorem path_induction {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (P : ∀ {a b : X}, Path a b → Prop)
    (hrefl : ∀ a, P (Path.refl a))
    (htrans : ∀ {a b c} (p : Path a b) (q : Path b c), P p → P q → P (p.trans q))
    (hhomotopy : ∀ {a b} {p q : Path a b}, p.Homotopic q → P p → P q)
    (hlocal : ∀ {a b} (p : Path a b), (∃ i, Set.range p ⊆ U i) → P p)
    {a b : X} (p : Path a b) : P p := by
  obtain ⟨t,N,ht0,htN,_,ht⟩ := PathSubdivision.exists_subdivision p U hU
    (fun s => hcover (p s))
  have hall : ∀ k ≤ N, P (PathSubdivision.concatenateCuts p t k) := by
    intro k
    induction k with
    | zero => intro _; exact hrefl _
    | succ k ih =>
      intro hk
      exact htrans _ _ (ih (by omega)) (hlocal _ (ht k (by omega)))
  have hend := hhomotopy (PathSubdivision.concatenateCuts_homotopic p t N) (hall N le_rfl)
  rw [ht0,htN] at hend
  have hp := hhomotopy (PathSubdivision.cut_zero_one_homotopic p) hend
  exact (property_cast_iff P p p.source p.target).mp hp

end FiniteChains.OpenCoverPaths

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical
universe u v w

variable {P : Type u} [Preorder P] {C : Type v} [Groupoid.{w} C]

/-- A choice of arrows from a base object turns a groupoid-valued order functor
into a cocycle. The opposite group makes multiplication follow path order. -/
def orderFunctorCocycle (F : P ⥤ C) (a : P)
    (d : ∀ p : P, F.obj a ⟶ F.obj p) : OrdCocycle P (End (F.obj a))ᵐᵒᵖ where
  val p q := if h : p ≤ q then
    MulOpposite.op (d p ≫ F.map (homOfLE h) ≫ Groupoid.inv (d q)) else 1
  comp {p q r} hpq hqr := by
    simp only [dif_pos hpq, dif_pos hqr, dif_pos (hpq.trans hqr)]
    apply MulOpposite.unop_injective
    change (d p ≫ F.map (homOfLE hpq) ≫ Groupoid.inv (d q)) ≫
      (d q ≫ F.map (homOfLE hqr) ≫ Groupoid.inv (d r)) =
      d p ≫ F.map (homOfLE (hpq.trans hqr)) ≫ Groupoid.inv (d r)
    have hc : homOfLE (hpq.trans hqr) = homOfLE hpq ≫ homOfLE hqr := rfl
    rw [hc, F.map_comp]
    simp only [Category.assoc, Groupoid.inv_eq_inv, IsIso.inv_hom_id_assoc]

/-- Combinatorial simple connectivity makes the arrows to all vertices coherent
with every order morphism, in an arbitrary target groupoid. -/
theorem orderFunctor_exists_coherent_arrows (F : P ⥤ C) (a : P)
    (d : ∀ p : P, F.obj a ⟶ F.obj p)
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    ∃ k : ∀ p : P, F.obj a ⟶ F.obj p,
      ∀ {p q : P} (h : p ⟶ q), k p ≫ F.map h = k q := by
  obtain ⟨k, _, hk⟩ := (orderFunctorCocycle F a d).exists_potential_of_simplyConnected
    hconn hsc a
  refine ⟨fun p => (k p).unop ≫ d p, ?_⟩
  intro p q h
  have he : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
  have h₁ := congrArg MulOpposite.unop (hk (leOfHom h))
  simp only [orderFunctorCocycle, dif_pos (leOfHom h), MulOpposite.unop_mul,
    MulOpposite.unop_op, End.mul_def, he] at h₁
  have h₂ := congrArg (fun e : End (F.obj a) => e ≫ d q) h₁
  simpa using h₂

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- A combinatorially connected simply connected poset admits topological path
classes to its vertices which commute with every realized comparable edge. -/
theorem orderNerveRealization_exists_vertex_coherence (P : Type) [PartialOrder P]
    (a : P) (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    ∃ k : ∀ p : P, FundamentalGroupoid.mk (orderNerveRealizationVertex a) ⟶
        FundamentalGroupoid.mk (orderNerveRealizationVertex p),
      ∀ {p q : P} (h : p ≤ q),
        k p ≫ Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath h) = k q := by
  letI : Nonempty P := ⟨a⟩
  letI := orderNerveRealization_pathConnectedSpace P hconn
  let F := orderNerveRealizationFundamentalFunctor P
  let d  := fun p =>
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath
      (orderNerveRealizationVertex a) (orderNerveRealizationVertex p))
  obtain ⟨k, hk⟩ := orderFunctor_exists_coherent_arrows F a d hconn hsc
  exact ⟨k, fun {p q} h => hk (homOfLE h)⟩

/-- Each point has a radial path from a supporting vertex. The radial path
stays inside every closed star whose corresponding open star contains the point. -/
theorem orderNerveRealization_exists_radial {P : Type} [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (p : P) (r : Path (orderNerveRealizationVertex p) x),
      ∀ v : P, x ∈ orderNerveRealizationOpenStar P v →
        (p ≤ v ∨ v ≤ p) ∧
        Set.range r ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
          Set (orderNerveRealization P)) := by
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex s.val 0
  let r₀ := (PathConnectedSpace.joined w z).somePath.map
    (orderNerveRealizationSimplex P s.val).hom.continuous
  let r  := r₀.cast hw.symm hx.symm
  refine ⟨s.val.obj 0, r, ?_⟩
  intro v hv
  rw [← hx] at hv
  obtain ⟨j, hj⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v).mp hv
  have hall : ∀ i, s.val.obj i ≤ v ∨ v ≤ s.val.obj i := by
    intro i
    rcases le_total i j with h | h
    · exact Or.inl (hj ▸ leOfHom (s.val.map (homOfLE h)))
    · exact Or.inr (hj ▸ leOfHom (s.val.map (homOfLE h)))
  refine ⟨hall 0, ?_⟩
  have hr : Set.range r ⊆ Set.range (orderNerveRealizationSimplex P s.val) := by
    rintro y ⟨t, rfl⟩
    exact ⟨(PathConnectedSpace.joined w z).somePath t, rfl⟩
  exact hr.trans (orderNerveRealizationSimplex_supported (orderNerveVertexStar P v) s.val hall)

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory

/-- Combinatorial connectivity and simple connectivity imply genuine topological
simple connectivity of the poset-nerve realization. No finiteness is required. -/
theorem orderNerveRealization_simplyConnected (P : Type) [PartialOrder P] [Nonempty P]
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    SimplyConnectedSpace (orderNerveRealization P) := by
  let a : P := Classical.choice inferInstance
  letI := orderNerveRealization_pathConnectedSpace P hconn
  obtain ⟨k, hk⟩ := orderNerveRealization_exists_vertex_coherence P a hconn hsc
  choose v r hr using (fun x : orderNerveRealization P => orderNerveRealization_exists_radial x)
  let R  :=
    fun x => k (v x) ≫ Path.Homotopic.Quotient.mk (r x)
  have hstar x b
      (hx : x ∈ orderNerveRealizationOpenStar P b) :
      ∃ p : Path (orderNerveRealizationVertex b) x,
        Set.range p ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b)) ∧
        k b ≫ Path.Homotopic.Quotient.mk p = R x := by
    obtain ⟨hcomp, hrad⟩ := hr x b hx
    have he : ∃ e : Path (orderNerveRealizationVertex b) (orderNerveRealizationVertex (v x)),
        Set.range e ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b)) ∧
        k b ≫ Path.Homotopic.Quotient.mk e = k (v x) := by
      rcases hcomp with h | h
      · refine ⟨(orderNerveRealizationEdgePath h).symm, ?_, ?_⟩
        · rw (config := { transparency := .default }) [Path.symm_range]
          exact orderNerveRealizationEdgePath_supported h b (Or.inl h) (Or.inl le_rfl)
        · change k b ≫ Groupoid.inv (Path.Homotopic.Quotient.mk
            (orderNerveRealizationEdgePath h)) = k (v x)
          rw (config := { transparency := .default }) [← hk h, Category.assoc, Groupoid.comp_inv, Category.comp_id]
      · exact ⟨orderNerveRealizationEdgePath h,
          orderNerveRealizationEdgePath_supported h b (Or.inl le_rfl) (Or.inr h), hk h⟩
    obtain ⟨e, he, hke⟩ := he
    refine ⟨e.trans (r x), ?_, ?_⟩
    · grind
    · change k b ≫ (Path.Homotopic.Quotient.mk e ≫ Path.Homotopic.Quotient.mk (r x)) = _
      rw (config := { transparency := .default }) [← Category.assoc, hke]
  have hlocal {x y : orderNerveRealization P} (p : Path x y)
      (hp : ∃ b, Set.range p ⊆ orderNerveRealizationOpenStar P b) :
      R x ≫ Path.Homotopic.Quotient.mk p = R y := by
    obtain ⟨b, hp⟩ := hp
    obtain ⟨e, he, hke⟩ := hstar x b (hp p.source_mem_range)
    obtain ⟨f, hf, hkf⟩ := hstar y b (hp p.target_mem_range)
    letI := orderNerveRealization_closedStar_contractible b
    have hC : IsSimplyConnected (orderNerveRealizationSubcomplex P
        (orderNerveVertexStar P b) : Set (orderNerveRealization P)) := by
      change SimplyConnectedSpace _
      infer_instance
    have hh : (e.trans p).Homotopic f := paths_homotopic_of_range_subset hC _ _ (by
      rw (config := { transparency := .default }) [Path.trans_range]
      exact Set.union_subset he (hp.trans (orderNerveRealizationOpenStar_subset_subcomplex b))) hf
    rw (config := { transparency := .default }) [← hke, ← hkf, Category.assoc]
    apply congrArg (fun q => k b ≫ q)
    exact Quotient.sound hh
  have hall {x y : orderNerveRealization P} (p : Path x y) :
      R x ≫ Path.Homotopic.Quotient.mk p = R y := by
    refine FiniteChains.OpenCoverPaths.path_induction
      (orderNerveRealizationOpenStar P) (orderNerveRealizationOpenStar_isOpen P)
      (orderNerveRealizationOpenStar_cover P)
      (fun {x y} q => R x ≫ Path.Homotopic.Quotient.mk q = R y) ?_ ?_ ?_ ?_ p
    · intro x
      exact Category.comp_id (R x)
    · intro x y z p q hp hq
      change R x ≫ (Path.Homotopic.Quotient.mk p ≫ Path.Homotopic.Quotient.mk q) = R z
      rw (config := { transparency := .default }) [← Category.assoc, hp, hq]
    · intro x y p q hpq hp
      have he : Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := Quotient.sound hpq
      rwa [← he]
    · exact hlocal
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun x p => ?_⟩
  have he : (Path.Homotopic.Quotient.mk p : End (FundamentalGroupoid.mk x)) =
      𝟙 (FundamentalGroupoid.mk x) := by
    apply (cancel_epi (R x)).mp
    simpa only [Category.comp_id] using hall p
  exact Quotient.exact he

end FiniteChains.Comb
end

namespace FiniteChains.Comb

/-- The actual realization of the path-class universal order is topologically
simply connected, without any connectedness assumption on the base poset. -/
theorem uOrderRealization_simplyConnected {P : Type} [PartialOrder P] (a : P) :
    SimplyConnectedSpace (orderNerveRealization (UOrder P a)) := by
  letI : Nonempty (UOrder P a) := ⟨UV.base (orderCx P) a⟩
  exact orderNerveRealization_simplyConnected (UOrder P a)
    uOrder_complex_isConnected uOrder_complex_simplyConnected

end FiniteChains.Comb

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [PartialOrder P] {G : Type v} [Group G]
  (c : OrdCocycle P G) (a : P)

/-- Actual upward edge lifting multiplies actual vertex reading by the actual cocycle value. -/
theorem readVertex_uOrderStep (p : UOrder P a) (q : P) (h : uOrderEnd p ≤ q) :
    c.readVertex a (uOrderStep p q h) = c.readVertex a p * c.val (uOrderEnd p) q :=
  c.readVertex_extend a (ordPos h) p rfl

/-- Comparable actual universal-cover vertices satisfy the cocycle transport formula. -/
theorem readVertex_of_le (p q : UOrder P a) (h : p ≤ q) :
    c.readVertex a q = c.readVertex a p * c.val (uOrderEnd p) (uOrderEnd q) := by
  obtain ⟨hle, he⟩ := h
  rw [← he]
  simpa only [uOrderStep_end] using c.readVertex_uOrderStep a p (uOrderEnd q) hle

/-- Reading down a genuine lifted comparability multiplies by the inverse cocycle value. -/
theorem readVertex_lower_of_le (p q : UOrder P a) (h : p ≤ q) :
    c.readVertex a p = c.readVertex a q * (c.val (uOrderEnd p) (uOrderEnd q))⁻¹ := by
  rw [c.readVertex_of_le a p q h]
  simp

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.PresModel
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (gen : α → G)

/-- The actual cone trivialization at a letter midpoint has the signed prefix value. -/
theorem trivVal_cmid_of_get (j : J) (k : ℕ) (a : α × Bool)
    (ha : (w j)[k]? = some a) :
    trivVal w gen j k CPos.cmid =
      (if a.2 then (1 : G) else gen a.1) * (prefixVal w gen j k)⁻¹ := by
  unfold trivVal
  rw [aFun_cedgL_of_get w ha]
  cases a.2 <;> simp [roseVal]

/-- Inverting the actual midpoint trivialization yields the positive prefix or negative-letter Fox prefix. -/
theorem trivVal_cmid_inv_of_get (j : J) (k : ℕ) (a : α × Bool)
    (ha : (w j)[k]? = some a) :
    (trivVal w gen j k CPos.cmid)⁻¹ =
      prefixVal w gen j k * (if a.2 then (1 : G) else (gen a.1)⁻¹) := by grind [trivVal_cmid_of_get, mul_inv_rev, inv_inv]

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (gen : α → G)
  (hrel : ∀ j, wordVal gen (w j) = 1) (a : PresPos w)

/-- The actual lifted cone midpoint reads as its apex reading times the signed word prefix. -/
theorem presUniversal_midpoint_reading (j : J) (k : ℕ) (b : α × Bool)
    (hb : (w j)[k]? = some b) (p q : UOrder (PresPos w) a) (hle : p ≤ q)
    (hp : uOrderEnd p = iCirc w (TCirc.pt w j k CPos.cmid))
    (hq : uOrderEnd q = apexOf w j) :
    (presCoc w gen hrel).readVertex a p =
      (presCoc w gen hrel).readVertex a q *
        (prefixVal w gen j k * (if b.2 then 1 else (gen b.1)⁻¹)) := by
  rw [(presCoc w gen hrel).readVertex_lower_of_le a p q hle, hp, hq]
  change (presCoc w gen hrel).readVertex a q * (trivVal w gen j k CPos.cmid)⁻¹ = _
  rw [trivVal_cmid_inv_of_get w gen j k b hb]

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

/-- Reading the actual midpoint of an actual lifted relator gives its actual signed prefix. -/
theorem presUniversalRelator_midpoint_reading
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)))
    (k : Fin (w p.val.2).length) :
    (presCoc w gen hrel).readVertex (ptBase w)
      (presCoverCircleInclusion (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd (presUniversalEnd_isPosetCover w hpos) p
        (relatorCirclePoint w p.val.2 k CPos.cmid)) =
      (presCoc w gen hrel).readVertex (ptBase w) p.val.1 *
        (prefixVal w gen p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹)) := by
  apply presUniversal_midpoint_reading w gen hrel (ptBase w) p.val.2 k.val _
    (List.getElem?_eq_getElem k.isLt)
  · exact (presCoverCircleInclusion_lt_apex w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos) p _).le
  · exact presCoverConeCircleOrderIso_symm_projection w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos) p.val.1 p.val.2 p.property _
  · grind

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

/-- The actual collapse in the universal presentation cover preserves actual vertex reading. -/
theorem presUniversalCylinderCollapse_reading
    (p : {p : UOrder (PresPos w) (ptBase w) //
      uOrderEnd p ∈ coneAdjBaseSet (S := circSet w)}) :
    (presCoc w gen hrel).readVertex (ptBase w)
      (presCoverCylinderCollapse w uOrderEnd (presUniversalEnd_isPosetCover w hpos) p).val =
        (presCoc w gen hrel).readVertex (ptBase w) p.val := by
  let f := uOrderEnd (a := ptBase w)
  let hf := presUniversalEnd_isPosetCover w hpos
  let q := presCoverCylinderCollapse w f hf p
  have hle  :=
    (coneAdjCoverBaseEnd_isPosetCover f hf).le_upTransform
      (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w)) p
  rw [(presCoc w gen hrel).readVertex_of_le (ptBase w) p.val q.val hle]
  change (presCoc w gen hrel).readVertex (ptBase w) p.val *
    (presCoc w gen hrel).val (f p.val) (f q.val) = _
  rw [← coneAdjCoverBaseEnd_spec f p, ← coneAdjCoverBaseEnd_spec f q]
  have hq : coneAdjCoverBaseEnd f q = cylCollapse (aHom w) (coneAdjCoverBaseEnd f p) :=
    cylinderCoverCollapse_projection w (coneAdjCoverBaseEnd_isPosetCover f hf) p
  rw [hq]
  change (presCoc w gen hrel).readVertex (ptBase w) p.val *
    roseVal gen (cylRetr (aHom w) (coneAdjCoverBaseEnd f p))
      (cylRetr (aHom w) (coneAdjCoverBaseEnd f p)) = _
  rw [roseVal_self, mul_one]

/-- The actual collapsed lifted-relator midpoint has the same signed prefix reading. -/
theorem presUniversalRelator_collapsed_midpoint_reading
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)))
    (k : Fin (w p.val.2).length) :
    (presCoc w gen hrel).readVertex (ptBase w)
      (presCoverCylinderCollapse (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos)
        (presCoverCircleCylinderInclusion (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
          (presUniversalEnd_isPosetCover w hpos) p
          (relatorCirclePoint w p.val.2 k CPos.cmid))).val =
      (presCoc w gen hrel).readVertex (ptBase w) p.val.1 *
        (prefixVal w gen p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹)) := by
  rw [presUniversalCylinderCollapse_reading w hpos gen hrel]
  exact presUniversalRelator_midpoint_reading w hpos gen hrel p k

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The actual lifted-letter midpoint coordinates are exactly the signed prefix coordinates. -/
theorem presUniversalLetter_midpoint_coordinates
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)))
    (k : Fin (w p.val.2).length) :
    presUniversalMidpointGroupEquiv ρ w hw hpos
      (presCoverRelatorLetterMidpoint (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos) p k) =
      ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 *
        (prefixVal w (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
          p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else
            (QuotientGroup.mk (FreeGroup.of ((w p.val.2)[k.val]).1) : PresGroup ρ)⁻¹)),
        ((w p.val.2)[k.val]).1) := by
  apply Prod.ext
  · exact presUniversalRelator_collapsed_midpoint_reading w hpos
      (fun i => (QuotientGroup.mk (FreeGroup.of i)))
      (presGroup_wordVal_eq_one ρ w hw) p k
  · rfl

/-- The selected incidence of an actual midpoint has that midpoint's group coordinates. -/
theorem presUniversalGeneratorGroupEquiv_midpoint
    (m : roseCoverMidpoints (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))))) :
    presUniversalGeneratorGroupEquiv ρ w hw hpos
      (roseCoverMidpointEdge _ (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) m) =
      presUniversalMidpointGroupEquiv ρ w hw hpos m := by
  change presUniversalMidpointGroupEquiv ρ w hw hpos
    ((roseCoverMidpointEdgeEquiv _ (cylinderCoverRoseEnd_isPosetCover w _
      (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))).symm
      ((roseCoverMidpointEdgeEquiv _ (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))) m)) = _
  rw [Equiv.symm_apply_apply]

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine universal relator boundary expressed in actual group coordinates. -/
def presUniversalGroupBoundary :
    (PresGroup ρ × J →₀ ℤ) →ₗ[ℤ] (PresGroup ρ × α →₀ ℤ) :=
  (presUniversalGeneratorGroupChainEquiv ρ w hw hpos).toLinearMap.comp
    ((presCoverRelatorGeneratorBoundary (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos)).comp
        (presUniversalRelatorGroupChainEquiv ρ w hw hpos).symm.toLinearMap)

/-- An actual relator boundary column is the sum of its signed prefix group-generator incidences. -/
theorem presUniversalGroupBoundary_actual_column
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) :
    presUniversalGroupBoundary ρ w hw hpos
      (Finsupp.single (presUniversalRelatorGroupEquiv ρ w hw hpos p) 1) =
      ∑ k : Fin (w p.val.2).length,
        (if ((w p.val.2)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single
            ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 *
              (prefixVal w (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
                p.val.2 k.val *
                (if ((w p.val.2)[k.val]).2 then 1 else
                  (QuotientGroup.mk (FreeGroup.of ((w p.val.2)[k.val]).1) : PresGroup ρ)⁻¹)),
              ((w p.val.2)[k.val]).1) 1 := by
  simp only [presUniversalGroupBoundary, LinearMap.comp_apply,
    LinearEquiv.coe_coe, presUniversalRelatorGroupChainEquiv,
    Finsupp.domLCongr_symm, Finsupp.domLCongr_single, Equiv.symm_apply_apply]
  rw [presCoverRelatorGeneratorBoundary_single]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  congr 1
  rw [presUniversalGeneratorGroupChainEquiv, Finsupp.domLCongr_single,
    presUniversalGeneratorGroupEquiv_midpoint, presUniversalLetter_midpoint_coordinates]

end FiniteChains.PresModel

namespace FiniteChains
universe u v
variable {G : Type u} {I : Type v}

/-- Integer coefficients on group/cell pairs are the corresponding group-ring cell coefficients. -/
def groupCellChainEquiv :
    (G × I →₀ ℤ) ≃ₗ[ℤ] (I →₀ MonoidAlgebra ℤ G) :=
  ((Finsupp.domLCongr (R := ℤ) (M := ℤ) (Equiv.prodComm G I)).trans
    (Finsupp.curryLinearEquiv ℤ)).trans
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv (S := ℤ) (M := G) ℤ).symm)

/-- Actual individual incidences keep their group coefficient and cell label under reindexing. -/
theorem groupCellChainEquiv_single (g : G) (i : I) (n : ℤ) :
    groupCellChainEquiv (Finsupp.single (g, i) n) =
      Finsupp.single i (MonoidAlgebra.single g n) := by simp_all [groupCellChainEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single, Finsupp.mapRange.linearEquiv_apply]

end FiniteChains

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The actual universal boundary in group-ring cell coordinates. -/
def presUniversalGroupRingBoundary :
    (J →₀ MonoidAlgebra ℤ (PresGroup ρ)) →ₗ[ℤ]
      (α →₀ MonoidAlgebra ℤ (PresGroup ρ)) :=
  groupCellChainEquiv.toLinearMap.comp
    ((presUniversalGroupBoundary ρ w hw hpos).comp groupCellChainEquiv.symm.toLinearMap)

/-- Actual geometric columns in generator-indexed group-ring coefficients. -/
theorem presUniversalGroupRingBoundary_actual_column
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) :
    presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single p.val.2 (MonoidAlgebra.single
        ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) 1)) =
      ∑ k : Fin (w p.val.2).length,
        (if ((w p.val.2)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single ((w p.val.2)[k.val]).1
            (MonoidAlgebra.single
              ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 *
                ((QuotientGroup.mk (FreeGroup.mk ((w p.val.2).take k.val)) : PresGroup ρ) *
                  (if ((w p.val.2)[k.val]).2 then 1 else
                    (QuotientGroup.mk (FreeGroup.of ((w p.val.2)[k.val]).1) : PresGroup ρ)⁻¹))) 1) := by
  have hs := groupCellChainEquiv_single
    ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) p.val.2 (1 : ℤ)
  rw [← hs]
  change groupCellChainEquiv (presUniversalGroupBoundary ρ w hw hpos
    (groupCellChainEquiv.symm (groupCellChainEquiv
      (Finsupp.single (presUniversalRelatorGroupEquiv ρ w hw hpos p) 1)))) = _
  rw [LinearEquiv.symm_apply_apply, presUniversalGroupBoundary_actual_column, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, groupCellChainEquiv_single]
  congr 3
  rw [prefixVal, presGroup_wordVal]

end FiniteChains.PresModel

namespace FiniteChains
variable {α : Type*} [DecidableEq α]

/-- The actual Fox word boundary is its finite signed-prefix sum. -/
theorem foxWordPathBoundary_prefix_sum (i : α) (g : FreeGroup α)
    (l : List (α × Bool)) :
    foxWordPathBoundary i g l =
      ∑ k : Fin l.length, grp (g * FreeGroup.mk (l.take k.val)) *
        foxWordIncidence i l[k.val] := by
  induction l generalizing g with
  | nil => rfl
  | cons p l ih =>
    rw [foxWordPathBoundary, ih]
    simp
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.take_zero, ← FreeGroup.one_eq_mk, mul_one,
      List.getElem_cons_zero, Fin.val_succ, List.take_succ_cons, List.getElem_cons_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hm : FreeGroup.mk (p :: l.take k.val) =
        foxWordLetter p * FreeGroup.mk (l.take k.val) := by
      rw [← fox_mk_single_letter, FreeGroup.mul_mk]
      rfl
    rw [hm, mul_assoc]

/-- The actual Fox derivative is the finite signed-prefix sum at the identity. -/
theorem fox_mk_prefix_sum (i : α) (l : List (α × Bool)) :
    fox i (FreeGroup.mk l) =
      ∑ k : Fin l.length, grp (FreeGroup.mk (l.take k.val)) *
        foxWordIncidence i l[k.val] := by
  rw [← foxWordPathBoundary_one]
  simpa using foxWordPathBoundary_prefix_sum i 1 l

end FiniteChains

namespace FiniteChains
variable {α : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal]

/-- Projected Fox coefficients are the signed group-ring incidences at actual word prefixes. -/
theorem coverFox_mk_prefix_sum (i : α) (l : List (α × Bool)) :
    proj N (fox i (FreeGroup.mk l)) =
      ∑ k : Fin l.length,
        if i = l[k.val].1 then
          MonoidAlgebra.single
            ((QuotientGroup.mk (FreeGroup.mk (l.take k.val)) : FreeGroup α ⧸ N) *
              (if l[k.val].2 then 1 else
                (QuotientGroup.mk (FreeGroup.of l[k.val].1) : FreeGroup α ⧸ N)⁻¹))
            (if l[k.val].2 then (1 : ℤ) else -1)
        else 0 := by
  rw [fox_mk_prefix_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hi : i = l[k.val].1
  · cases hb : l[k.val].2 <;>
      simp [foxWordIncidence, hi, hb, map_neg,
        MonoidAlgebra.single_mul_single, grp_eq_single, proj_single,
        QuotientGroup.mk_inv]
  · simp [foxWordIncidence, hi]

end FiniteChains

namespace FiniteChains
variable {α : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal]

/-- A translated projected Fox coefficient is the translated signed prefix-incidence sum. -/
theorem coverFox_translated_prefix_sum (g : FreeGroup α ⧸ N)
    (i : α) (l : List (α × Bool)) :
    MonoidAlgebra.single g (1 : ℤ) * proj N (fox i (FreeGroup.mk l)) =
      ∑ k : Fin l.length,
        if i = l[k.val].1 then
          MonoidAlgebra.single
            (g * ((QuotientGroup.mk (FreeGroup.mk (l.take k.val)) : FreeGroup α ⧸ N) *
              (if l[k.val].2 then 1 else
                (QuotientGroup.mk (FreeGroup.of l[k.val].1) : FreeGroup α ⧸ N)⁻¹)))
            (if l[k.val].2 then (1 : ℤ) else -1)
        else 0 := by
  rw [coverFox_mk_prefix_sum, Finset.mul_sum]
  simp

end FiniteChains

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine geometric boundary coefficient is the actual translated projected Fox derivative. -/
theorem presUniversalGroupRingBoundary_actual_fox
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) (i : α) :
    presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single p.val.2 (MonoidAlgebra.single
        ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) 1)) i =
      MonoidAlgebra.single ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) 1 *
        proj (relSub ρ) (fox i (ρ p.val.2)) := by
  classical
  rw [presUniversalGroupRingBoundary_actual_column, ← hw p.val.2,
    coverFox_translated_prefix_sum]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finsupp.smul_apply]
  by_cases hi : i = ((w p.val.2)[k.val]).1
  · subst i
    simp only [Finsupp.single_eq_same]
    cases hb : ((w p.val.2)[k.val]).2 <;>
      simp
  · simp_all

/-- Every group-translated geometric basis column is the corresponding Fox column. -/
theorem presUniversalGroupRingBoundary_fox_single (g : PresGroup ρ) (j : J) (i : α) :
    presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single j (MonoidAlgebra.single g 1)) i =
      MonoidAlgebra.single g 1 * proj (relSub ρ) (fox i (ρ j)) := by
  let p := (presUniversalRelatorGroupEquiv ρ w hw hpos).symm (g, j)
  have he := (presUniversalRelatorGroupEquiv ρ w hw hpos).apply_symm_apply (g, j)
  have hg : (presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 = g :=
    congrArg Prod.fst he
  have hj : p.val.2 = j := congrArg Prod.snd he
  simpa only [hg, hj] using presUniversalGroupRingBoundary_actual_fox ρ w hw hpos p i

/-- The genuine universal geometric boundary equals the actual algebraic Fox boundary. -/
theorem presUniversalGroupRingBoundary_eq_fox :
    presUniversalGroupRingBoundary ρ w hw hpos =
      (coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ := by
  apply Finsupp.lhom_ext
  intro j r
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp_all
  | single g n =>
    have hn : MonoidAlgebra.single g n = n • MonoidAlgebra.single g 1 := by
      simp [MonoidAlgebra.smul_single]
    change presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single j (MonoidAlgebra.single g n)) =
      (coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ
        (Finsupp.single j (MonoidAlgebra.single g n))
    rw [hn, ← Finsupp.smul_single, map_smul, map_smul]
    congr 1
    ext i
    rw [presUniversalGroupRingBoundary_fox_single]
    simp [coverSecondBoundary, coverFoxGradient, foxGradient_apply,
      Finsupp.linearCombination_single, Finsupp.smul_apply, smul_eq_mul]

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual relator-chain coordinates in the cell-indexed presentation group ring. -/
def presUniversalRelatorRingEquiv :=
  (presUniversalRelatorGroupChainEquiv ρ w hw hpos).trans
    (groupCellChainEquiv (I := J))

/-- Actual generator-chain coordinates in the cell-indexed presentation group ring. -/
def presUniversalGeneratorRingEquiv :=
  (presUniversalGeneratorGroupChainEquiv ρ w hw hpos).trans
    (groupCellChainEquiv (I := α))

/-- The actual geometric boundary commutes with the proved Fox coordinate equivalences. -/
theorem presUniversalFox_coordinates_commute
    (c : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) :
    presUniversalGeneratorRingEquiv ρ w hw hpos
      (presCoverRelatorGeneratorBoundary (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos) c) =
      coverSecondBoundary (relSub ρ) ρ (presUniversalRelatorRingEquiv ρ w hw hpos c) := by
  have h := LinearMap.congr_fun (presUniversalGroupRingBoundary_eq_fox ρ w hw hpos)
    (presUniversalRelatorRingEquiv ρ w hw hpos c)
  simpa only [presUniversalGroupRingBoundary, presUniversalGroupBoundary,
    presUniversalRelatorRingEquiv, presUniversalGeneratorRingEquiv,
    LinearEquiv.trans_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply] using h

/-- The genuine universal geometric generator-boundary kernel is the actual Fox kernel. -/
def presUniversalGeneratorFoxKernelEquiv :
    LinearMap.ker (presCoverRelatorGeneratorBoundary (P := UOrder (PresPos w) (ptBase w))
      w uOrderEnd (presUniversalEnd_isPosetCover w hpos)) ≃ₗ[ℤ]
    LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ) where
  toFun c := ⟨presUniversalRelatorRingEquiv ρ w hw hpos c.val, by
    change coverSecondBoundary (relSub ρ) ρ _ = 0
    rw [← presUniversalFox_coordinates_commute]
    rw [c.property, map_zero]⟩
  invFun c := ⟨(presUniversalRelatorRingEquiv ρ w hw hpos).symm c.val, by
    apply (presUniversalGeneratorRingEquiv ρ w hw hpos).injective
    rw [map_zero, presUniversalFox_coordinates_commute, LinearEquiv.apply_symm_apply]
    exact c.property⟩
  left_inv c := Subtype.ext ((presUniversalRelatorRingEquiv ρ w hw hpos).symm_apply_apply c.val)
  right_inv c := Subtype.ext ((presUniversalRelatorRingEquiv ρ w hw hpos).apply_symm_apply c.val)
  map_add' c d := Subtype.ext (map_add _ c.val d.val)
  map_smul' n c := Subtype.ext (map_smul _ n c.val)

/-- Actual strict universal presentation two-cycles have the genuine algebraic Fox kernel coordinates. -/
def presUniversalTwoCycleFoxKernelEquiv :
    LinearMap.ker (Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w)))) ≃ₗ[ℤ]
      LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ) :=
  (presCoverCycleRelatorGeneratorKernelEquiv w uOrderEnd
    (presUniversalEnd_isPosetCover w hpos) hpos).trans
      (presUniversalGeneratorFoxKernelEquiv ρ w hw hpos)

end FiniteChains.PresModel

namespace FiniteChains.PresModel
universe u
variable {α β J K : Type u} [DecidableEq α] [DecidableEq β]

/-- Reduced words with a cancelling pair. Choosing a compatible generator makes
these nonempty representatives commute literally with generator embeddings. -/
def presCanonicalWords (ρ : J → FreeGroup α) (a : α) (j : J) : List (α × Bool) :=
  (ρ j).toWord ++ [(a, true), (a, false)]

theorem presCanonicalWords_ne_nil (ρ : J → FreeGroup α) (a : α) (j : J) :
    presCanonicalWords ρ a j ≠ [] := by
  simp [presCanonicalWords]

theorem presCanonicalWords_positive (ρ : J → FreeGroup α) (a : α) (j : J) :
    0 < (presCanonicalWords ρ a j).length := by
  simp [presCanonicalWords]

theorem mk_presCanonicalWords (ρ : J → FreeGroup α) (a : α) (j : J) :
    FreeGroup.mk (presCanonicalWords ρ a j) = ρ j := by
  have hc : FreeGroup.mk [(a, true), (a, false)] = 1 := by
    change FreeGroup.of a * (FreeGroup.of a)⁻¹ = 1
    exact mul_inv_cancel _
  rw [presCanonicalWords, ← FreeGroup.mul_mk, hc, mul_one, FreeGroup.mk_toWord]

theorem presCanonicalWords_map (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
    (f : α ↪ β) (g : J ↪ K) (h : ∀ j, σ (g j) = FreeGroup.map f (ρ j))
    (a : α) (j : J) :
    presCanonicalWords σ (f a) (g j) =
      (presCanonicalWords ρ a j).map (fun p => (f p.1, p.2)) := by grind [presCanonicalWords, FiniteChains.toWord_map, List.map_append, List.map_cons, List.map_nil]

/-- A labelled inclusion of group presentations now gives a literal word embedding,
with no independent compatibility assumption on the representatives. -/
def canonicalPresWordEmbedding (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
    (f : α ↪ β) (g : J ↪ K) (h : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (a : α) :
    PresWordEmbedding (presCanonicalWords ρ a) (presCanonicalWords σ (f a)) where
  gen := f
  cell := g
  word := presCanonicalWords_map ρ σ f g h a

end FiniteChains.PresModel

namespace FiniteChains.TopologicalSingular

open Set Topology CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

abbrev Domain (n : ℕ) := stdSimplex ℝ (Fin (n + 1))

abbrev Simplex (X : Type u) [TopologicalSpace X] (n : ℕ) := C(Domain n, X)

abbrev Chain (X : Type u) [TopologicalSpace X] (n : ℕ) := Simplex X n →₀ ℤ

def simplices (X : Type u) [TopologicalSpace X] : SimplicialObject (Type u) where
  obj n := Simplex X n.unop.len
  map f := TypeCat.ofHom (fun σ => σ.comp ⟨stdSimplex.map f.unop, stdSimplex.continuous_map _⟩)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro σ
    ext z
    exact congrArg σ (stdSimplex.map_id_apply z)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro σ
    ext z
    exact congrArg σ (stdSimplex.map_comp_apply g.unop f.unop z).symm

def freeZ : Type u ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ (A →₀ ℤ)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ f.hom)
  map_id A := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_id ℤ ℤ
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_comp ℤ ℤ f.hom g.hom

def modules (X : Type u) [TopologicalSpace X] : SimplicialObject (ModuleCat.{u} ℤ) :=
  simplices X ⋙ freeZ

def complex (X : Type u) [TopologicalSpace X] : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  AlternatingFaceMapComplex.obj (modules X)

variable {X : Type u} [TopologicalSpace X]

def face {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) : Simplex X n :=
  (simplices X).δ i σ

theorem face_apply {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) (z : Domain n) :
    face i σ z = σ (stdSimplex.map (SimplexCategory.δ i) z) := rfl

def boundary (n : ℕ) : Chain X (n + 1) →ₗ[ℤ] Chain X n :=
  (AlternatingFaceMapComplex.objD (modules X) n).hom


theorem boundary_single (n : ℕ) (σ : Simplex X (n + 1)) (a : ℤ) :
    boundary n (Finsupp.single σ a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (face i σ) a := by
  rw [(show boundary (X := X) n = ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (face i) by
    simp only [boundary, AlternatingFaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
    rfl)]
  simp


theorem boundary_boundary (n : ℕ) (c : Chain X (n + 2)) : boundary n (boundary (n + 1) c) = 0 :=
  DFunLike.congr_fun (by
    exact congrArg ModuleCat.Hom.hom (AlternatingFaceMapComplex.d_squared (modules X) n)) c

theorem complex_d (n : ℕ) : (complex X).d (n + 1) n = ModuleCat.ofHom (boundary n) := AlternatingFaceMapComplex.obj_d_eq (modules X) n

def augmentation : Chain X 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : Simplex X 0 => (1 : ℤ))

@[simp] theorem augmentation_single (σ : Simplex X 0) (a : ℤ) :
    augmentation (Finsupp.single σ a) = a := by
  simp [augmentation]

theorem augmentation_boundary (c : Chain X 1) : augmentation (boundary 0 c) = 0 := by
  have he : augmentation.comp (boundary (X := X) 0) = 0 := by
    apply Finsupp.lhom_ext
    intro σ a
    change augmentation (boundary 0 (Finsupp.single σ a)) = 0
    rw [boundary_single]
    rw [Fin.sum_univ_two]
    change augmentation (1 • Finsupp.single (face 0 σ) a +
      (-1) • Finsupp.single (face 1 σ) a) = 0
    rw [one_smul, neg_smul, one_smul, map_add, map_neg,
      augmentation_single, augmentation_single, add_neg_cancel]
  exact DFunLike.congr_fun he c

def zeroSimplexEquiv : Simplex X 0 ≃ X where
  toFun σ := σ (stdSimplex.vertex 0)
  invFun x := ContinuousMap.const _ x
  left_inv σ := by
    letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
    ext z
    exact congrArg σ (Subsingleton.elim _ _)
  right_inv x := rfl

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def simplexMap (f : C(X, Y)) (n : ℕ) (σ : Simplex X n) : Simplex Y n := f.comp σ

@[simp] theorem simplexMap_apply (f : C(X, Y)) (n : ℕ) (σ : Simplex X n) (z : Domain n) :
    simplexMap f n σ z = f (σ z) := rfl

theorem face_simplexMap (f : C(X, Y)) {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) :
    face i (simplexMap f (n + 1) σ) = simplexMap f n (face i σ) := rfl

def map (f : C(X, Y)) (n : ℕ) : Chain X n →ₗ[ℤ] Chain Y n :=
  Finsupp.lmapDomain ℤ ℤ (simplexMap f n)

@[simp] theorem map_single (f : C(X, Y)) (n : ℕ) (σ : Simplex X n) (a : ℤ) :
    map f n (Finsupp.single σ a) = Finsupp.single (simplexMap f n σ) a :=
  Finsupp.mapDomain_single

theorem map_id (n : ℕ) : map (ContinuousMap.id X) n = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ a
  rw [map_single]
  rfl

theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    map (g.comp f) n = (map g n).comp (map f n) := by
  apply Finsupp.lhom_ext
  intro σ a
  simp
  rfl

theorem map_boundary (f : C(X, Y)) (n : ℕ) (c : Chain X (n + 1)) :
    map f n (boundary n c) = boundary n (map f (n + 1) c) := by
  have he : (map f n).comp (boundary n) = (boundary n).comp (map f (n + 1)) := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply, boundary_single, map_single, map_sum, map_smul,
      face_simplexMap]
  exact DFunLike.congr_fun he c

theorem augmentation_map (f : C(X, Y)) (c : Chain X 0) : augmentation (map f 0 c) = augmentation c := by
  have he : augmentation.comp (map f 0) = augmentation := by
    apply Finsupp.lhom_ext
    intro σ a
    simp
  exact DFunLike.congr_fun he c

end FiniteChains.TopologicalSingular

namespace FiniteChains.SingularPrism

variable {V : Type*} [AddCommGroup V]

def altSum {n : ℕ} (f : Fin n → V) : V := ∑ i, (-1 : ℤ) ^ i.val • f i

theorem altSum_sub {n : ℕ} (f g : Fin n → V) :
    altSum (fun i => f i - g i) = altSum f - altSum g := by
  simp only [altSum, smul_sub, Finset.sum_sub_distrib]

theorem altSum_succ {n : ℕ} (f : Fin (n + 1) → V) :
    altSum f = f 0 - altSum (fun i : Fin n => f i.succ) := by
  rw [altSum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one,
    neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg, altSum]

theorem altSum_comm {m n : ℕ} (f : Fin m → Fin n → V) :
    altSum (fun i => altSum (f i)) = altSum (fun j => altSum (fun i => f i j)) := by
  simp only [altSum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  congr 1
  funext j
  congr 1
  funext i
  rw [mul_comm]

def side {n : ℕ} (A : Fin (n + 1) → Fin (n + 2) → V) (i : Fin n) (j : Fin (n + 1)) : V :=
  if j ≤ i.castSucc then A i.succ j.castSucc else A i.castSucc j.succ


omit [AddCommGroup V] in
theorem side_zero_succ {n : ℕ} (A : Fin (n + 2) → Fin (n + 3) → V) (j : Fin (n + 1)) :
    side A 0 j.succ = A 0 j.succ.succ := rfl


omit [AddCommGroup V] in
theorem side_succ_succ {n : ℕ} (A : Fin (n + 2) → Fin (n + 3) → V)
    (i : Fin n) (j : Fin (n + 1)) :
    side A i.succ j.succ = side (fun i j => A i.succ j.succ) i j := by simp_all [side, Fin.le_def, Fin.val_succ, Fin.val_castSucc, Nat.add_le_add_iff_right]

theorem prism_cancellation (n : ℕ) (A : Fin (n + 1) → Fin (n + 2) → V)
    (hd : ∀ i : Fin n, A i.castSucc i.succ.castSucc = A i.succ i.succ.castSucc) :
    altSum (fun i => altSum (A i)) + altSum (fun i => altSum (side A i)) =
      A 0 0 - A (Fin.last n) (Fin.last (n + 1)) := by
  induction n with
  | zero =>
    simp [altSum, Fin.sum_univ_two, sub_eq_add_neg]
  | succ n ih =>
    let D : Fin (n + 1) → Fin (n + 2) → V := fun i j => A i.succ j.succ
    have hdD : ∀ i : Fin n, D i.castSucc i.succ.castSucc = D i.succ i.succ.castSucc := by
      intro i
      exact hd i.succ
    have hi := ih D hdD
    have hrow0 : altSum (A 0) = A 0 0 - A 0 1 +
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) := by
      rw [altSum_succ, altSum_succ]
      simp
      abel
    have hrow i : altSum (A i.succ) = A i.succ 0 - altSum (D i) :=
      altSum_succ _
    have hA : altSum (fun i => altSum (A i)) = A 0 0 - A 0 1 +
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) -
        altSum (fun i : Fin (n + 1) => A i.succ 0) + altSum (fun i => altSum (D i)) := by
      rw [altSum_succ, hrow0]
      simp_rw [hrow]
      rw [altSum_sub]
      abel
    have hbrow0 : altSum (side A 0) = A 1 0 -
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) := by
      rw [altSum_succ, (show side A 0 0 = A 1 0 by
        simp [side])]
      simp only [side_zero_succ]
    have hbrow (i : Fin n) : altSum (side A i.succ) =
        A i.succ.succ 0 - altSum (side D i) := by
      rw [altSum_succ, (show side A i.succ 0 = A i.succ.succ 0 by
        simp [side])]
      simp only [side_succ_succ]
      rfl
    have hB : altSum (fun i => altSum (side A i)) =
        altSum (fun i : Fin (n + 1) => A i.succ 0) -
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) + altSum (fun i => altSum (side D i)) := by
      rw [altSum_succ, hbrow0]
      simp_rw [hbrow]
      rw [altSum_sub, altSum_succ (fun i : Fin (n + 1) => A i.succ 0)]
      simp only [Fin.succ_zero_eq_one]
      abel
    rw [hA, hB]
    calc
      _ = A 0 0 - A 0 1 +
          (altSum (fun i => altSum (D i)) + altSum (fun i => altSum (side D i))) := by abel
      _ = A 0 0 - A 0 1 + (D 0 0 - D (Fin.last n) (Fin.last (n + 1))) := by rw [hi]
      _ = A 0 0 - A (Fin.last (n + 1)) (Fin.last (n + 2)) := by
        have hm : A 0 1 = A 1 1 := hd 0
        change A 0 0 - A 0 1 + (A 1 1 - A (Fin.last (n + 1)) (Fin.last (n + 2))) = _
        rw [hm]
        abel

end FiniteChains.SingularPrism

namespace FiniteChains.SingularPrism

open CategoryTheory

def cut (i : ℕ) {m : ℕ} (j : Fin m) : Fin 2 := if j.val ≤ i then 0 else 1

theorem cut_left {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
    cut i.succ.val ∘ j.castSucc.succAbove = (cut i.val : Fin (n + 2) → Fin 2) := by
  funext k
  have hh  := h
  simp only [Function.comp_apply, cut, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ]
  grind

theorem cut_right {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j) :
    cut i.castSucc.val ∘ j.succ.succAbove = (cut i.val : Fin (n + 2) → Fin 2) := by
  funext k
  have hh : i.val < j.val := h
  have hv : (j.succ.succAbove k).val = if k.val < j.val + 1 then k.val else k.val + 1 := by
    by_cases hk : k.val < j.val + 1
    · rw [Fin.succAbove_of_castSucc_lt _ _ hk, if_pos hk]
      rfl
    · rw [Fin.succAbove_of_le_castSucc _ _ (show j.succ ≤ k.castSucc from Nat.le_of_not_gt hk), if_neg hk]
      rfl
  have he : (j.succ.succAbove k).val ≤ i.val ↔ k.val ≤ i.val := by
    rw [hv]
    split_ifs <;> omega
  simp only [Function.comp_apply, cut, Fin.val_castSucc, he]

theorem cut_middle {n : ℕ} (i : Fin n) :
    cut i.succ.val ∘ i.succ.castSucc.succAbove =
      (cut i.castSucc.val ∘ i.succ.castSucc.succAbove : Fin (n + 1) → Fin 2) := by
  funext k
  simp only [Function.comp_apply, cut, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ]
  grind

theorem cut_first (n : ℕ) :
    cut 0 ∘ (0 : Fin (n + 2)).succAbove = (fun _ : Fin (n + 1) => (1 : Fin 2)) := rfl

theorem cut_last (n : ℕ) :
    cut n ∘ (Fin.last (n + 1)).succAbove = (fun _ : Fin (n + 1) => (0 : Fin 2)) := by
  funext k
  simp only [Function.comp_apply, Fin.succAbove_last, cut, Fin.val_castSucc]
  grind

theorem base_left {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
    i.succ.predAbove ∘ j.castSucc.succAbove = j.succAbove ∘ i.predAbove := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1) => f k)
    (SimplexCategory.δ_comp_σ_of_le h)

theorem base_right {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j) :
    i.castSucc.predAbove ∘ j.succ.succAbove = j.succAbove ∘ i.predAbove := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1) => f k)
    (SimplexCategory.δ_comp_σ_of_gt h)

theorem base_same {n : ℕ} (i : Fin (n + 1)) :
    i.predAbove ∘ i.castSucc.succAbove = id := by
  funext k
  exact Fin.predAbove_succAbove i k

theorem base_next {n : ℕ} (i : Fin (n + 1)) :
    i.predAbove ∘ i.succ.succAbove = id := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk n => f k)
    (SimplexCategory.δ_comp_σ_succ (i := i))

end FiniteChains.SingularPrism

namespace FiniteChains.SingularPrism

open Set Topology TopologicalSingular

theorem stdMap_const {m n : ℕ} (b : Fin n) (z : stdSimplex ℝ (Fin m)) :
    stdSimplex.map (fun _ : Fin m => b) z = stdSimplex.vertex b := by
  apply Subtype.ext
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  by_cases h : b = j
  · subst j
    simp
  · simp_all

def prismMap {n : ℕ} (i : Fin (n + 1)) : C(Domain (n + 1), unitInterval × Domain n) :=
  ⟨fun z => (stdSimplexHomeomorphUnitInterval (stdSimplex.map (cut i.val) z),
      stdSimplex.map i.predAbove z),
    (stdSimplexHomeomorphUnitInterval.continuous.comp (stdSimplex.continuous_map _)).prodMk
      (stdSimplex.continuous_map _)⟩






universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

def simplex {n : ℕ} (σ : Simplex X n) (i : Fin (n + 1)) : Simplex Y (n + 1) :=
  H.toContinuousMap.comp ⟨fun z => ((prismMap i z).1, σ (prismMap i z).2),
    (prismMap i).continuous.fst.prodMk (σ.continuous.comp (prismMap i).continuous.snd)⟩

theorem simplex_left {n : ℕ} (σ : Simplex X (n + 1)) (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : j ≤ i.castSucc) :
    face j.castSucc (simplex H σ i.succ) = simplex H (face j σ) i := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.succ (stdSimplex.map j.castSucc.succAbove z)).1,
      σ (prismMap i.succ (stdSimplex.map j.castSucc.succAbove z)).2) = _
  rw [(show prismMap i.succ (stdSimplex.map j.castSucc.succAbove z) =
      ((prismMap i z).1, stdSimplex.map j.succAbove (prismMap i z).2) by
    simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
    rw [cut_left i j h, base_left i j h])]
  rfl

theorem simplex_right {n : ℕ} (σ : Simplex X (n + 1)) (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : i.castSucc < j) :
    face j.succ (simplex H σ i.castSucc) = simplex H (face j σ) i := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.castSucc (stdSimplex.map j.succ.succAbove z)).1,
      σ (prismMap i.castSucc (stdSimplex.map j.succ.succAbove z)).2) = _
  rw [(show prismMap i.castSucc (stdSimplex.map j.succ.succAbove z) =
      ((prismMap i z).1, stdSimplex.map j.succAbove (prismMap i z).2) by
    simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
    rw [cut_right i j h, base_right i j h])]
  rfl

theorem simplex_middle {n : ℕ} (σ : Simplex X n) (i : Fin n) :
    face i.succ.castSucc (simplex H σ i.castSucc) = face i.succ.castSucc (simplex H σ i.succ) := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z)).1,
      σ (prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z)).2) = _
  rw [(show prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z) =
      prismMap i.succ (stdSimplex.map i.succ.castSucc.succAbove z) by
    apply Prod.ext
    · simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
      rw [cut_middle]
    · change stdSimplex.map i.castSucc.predAbove (stdSimplex.map i.succ.castSucc.succAbove z) =
        stdSimplex.map i.succ.predAbove (stdSimplex.map i.succ.castSucc.succAbove z)
      rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
      change stdSimplex.map (i.castSucc.predAbove ∘ i.castSucc.succ.succAbove) z =
        stdSimplex.map (i.succ.predAbove ∘ i.succ.castSucc.succAbove) z
      rw [base_next, base_same])]
  rfl

theorem simplex_first (n : ℕ) (σ : Simplex X n) :
    face 0 (simplex H σ 0) = simplexMap g n σ := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap 0 (stdSimplex.map (0 : Fin (n + 2)).succAbove z)).1,
      σ (prismMap 0 (stdSimplex.map (0 : Fin (n + 2)).succAbove z)).2) = _
  rw [(show prismMap 0 (stdSimplex.map (0 : Fin (n + 2)).succAbove z) = (1, z) by
    apply Prod.ext
    · change stdSimplexHomeomorphUnitInterval
        (stdSimplex.map (cut 0) (stdSimplex.map (0 : Fin (n + 2)).succAbove z)) = 1
      rw [stdSimplex.map_comp_apply, cut_first, stdMap_const]
      exact stdSimplexHomeomorphUnitInterval_one
    · change stdSimplex.map (0 : Fin (n + 1)).predAbove
        (stdSimplex.map (0 : Fin (n + 2)).succAbove z) = z
      rw [stdSimplex.map_comp_apply]
      change stdSimplex.map ((0 : Fin (n + 1)).predAbove ∘ (0 : Fin (n + 1)).castSucc.succAbove) z = z
      rw [base_same, stdSimplex.map_id_apply])]
  exact H.apply_one _

theorem simplex_last (n : ℕ) (σ : Simplex X n) :
    face (Fin.last (n + 1)) (simplex H σ (Fin.last n)) = simplexMap f n σ := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)).1,
      σ (prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)).2) = _
  rw [(show prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z) = (0, z) by
    apply Prod.ext
    · change stdSimplexHomeomorphUnitInterval
        (stdSimplex.map (cut n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)) = 0
      rw [stdSimplex.map_comp_apply, cut_last, stdMap_const]
      exact stdSimplexHomeomorphUnitInterval_zero
    · change stdSimplex.map (Fin.last n).predAbove
        (stdSimplex.map (Fin.last (n + 1)).succAbove z) = z
      rw [stdSimplex.map_comp_apply]
      change stdSimplex.map ((Fin.last n).predAbove ∘ (Fin.last n).succ.succAbove) z = z
      rw [base_next, stdSimplex.map_id_apply])]
  exact H.apply_zero _

end FiniteChains.SingularPrism

namespace FiniteChains.SingularPrism

open Set Topology TopologicalSingular

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

def prism (n : ℕ) : Chain X n →ₗ[ℤ] Chain Y (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • Finsupp.lmapDomain ℤ ℤ (fun σ => simplex H σ i)

theorem prism_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    prism H n (Finsupp.single σ r) = altSum (fun i => Finsupp.single (simplex H σ i) r) := by
  simp only [prism, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, altSum]

theorem boundary_prism_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    boundary n (prism H n (Finsupp.single σ r)) =
      altSum (fun i => altSum (fun j => Finsupp.single (face j (simplex H σ i)) r)) := by
  simp only [prism_single, altSum, map_sum, map_zsmul, boundary_single]


theorem prism_identity_zero_single (σ : Simplex X 0) (r : ℤ) :
    boundary 0 (prism H 0 (Finsupp.single σ r)) =
      TopologicalSingular.map g 0 (Finsupp.single σ r) - TopologicalSingular.map f 0 (Finsupp.single σ r) := by
  let A  := fun i j => Finsupp.single (face j (simplex H σ i)) r
  have hh := prism_cancellation 0 A (fun i => Fin.elim0 i)
  have hz : altSum (fun i : Fin 0 => altSum (side A i)) = 0 := by simp [altSum]
  rw [hz, add_zero] at hh
  rw [boundary_prism_single, TopologicalSingular.map_single, TopologicalSingular.map_single]
  simpa only [A, simplex_first, simplex_last] using hh

theorem prism_identity_succ_single (n : ℕ) (σ : Simplex X (n + 1)) (r : ℤ) :
    boundary (n + 1) (prism H (n + 1) (Finsupp.single σ r)) +
      prism H n (boundary n (Finsupp.single σ r)) =
      TopologicalSingular.map g (n + 1) (Finsupp.single σ r) -
        TopologicalSingular.map f (n + 1) (Finsupp.single σ r) := by
  let A  :=
    fun i j => Finsupp.single (face j (simplex H σ i)) r
  have hd : ∀ i : Fin (n + 1), A i.castSucc i.succ.castSucc = A i.succ i.succ.castSucc := by
    intro i
    exact congrArg (fun τ => Finsupp.single τ r) (simplex_middle H σ i)
  have hh := prism_cancellation (n + 1) A hd
  have hs : side A = fun i j => Finsupp.single (simplex H (face j σ) i) r := by
    funext i j
    unfold side
    split_ifs with hij
    · exact congrArg (fun τ => Finsupp.single τ r) (simplex_left H σ i j hij)
    · exact congrArg (fun τ => Finsupp.single τ r) (simplex_right H σ i j (lt_of_not_ge hij))
  rw [hs, altSum_comm (fun i j => Finsupp.single (simplex H (face j σ) i) r)] at hh
  rw [boundary_prism_single, (show prism H n (boundary n (Finsupp.single σ r)) =
      altSum (fun j => altSum (fun i => Finsupp.single (simplex H (face j σ) i) r)) by
    simp only [boundary_single, map_sum, map_zsmul, prism_single, altSum]), TopologicalSingular.map_single, TopologicalSingular.map_single]
  simpa only [A, simplex_first, simplex_last] using hh

theorem prism_identity_zero (c : Chain X 0) :
    boundary 0 (prism H 0 c) = TopologicalSingular.map g 0 c - TopologicalSingular.map f 0 c := by
  have he : (boundary 0).comp (prism H 0) = TopologicalSingular.map g 0 - TopologicalSingular.map f 0 := by
    apply Finsupp.lhom_ext
    exact prism_identity_zero_single H
  exact DFunLike.congr_fun he c

theorem prism_identity_succ (n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (prism H (n + 1) c) + prism H n (boundary n c) =
      TopologicalSingular.map g (n + 1) c - TopologicalSingular.map f (n + 1) c := by
  have he : (boundary (n + 1)).comp (prism H (n + 1)) + (prism H n).comp (boundary n) =
      TopologicalSingular.map g (n + 1) - TopologicalSingular.map f (n + 1) := by
    apply Finsupp.lhom_ext
    exact prism_identity_succ_single H n
  exact DFunLike.congr_fun he c

include H in
theorem homotopic_maps_difference_bounds (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    TopologicalSingular.map g (n + 1) c - TopologicalSingular.map f (n + 1) c ∈
      LinearMap.range (boundary (n + 1)) := by
  refine ⟨prism H (n + 1) c, ?_⟩
  simpa only [hc, map_zero, add_zero] using prism_identity_succ H n c

end FiniteChains.SingularPrism

namespace FiniteChains.TopologicalSingular

open Set Topology SingularPrism

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def constantCone (y : Y) (n : ℕ) : Chain X n →ₗ[ℤ] Chain Y (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun _ => ContinuousMap.const (Domain (n + 1)) y)

theorem constantCone_single (y : Y) (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    constantCone y n (Finsupp.single σ r) = Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r :=
  Finsupp.mapDomain_single

theorem face_constant {n : ℕ} (y : Y) (i : Fin (n + 2)) :
    face i (ContinuousMap.const (Domain (n + 1)) y) = ContinuousMap.const (Domain n) y := rfl

theorem constantCone_identity_single (y : Y) (n : ℕ) (σ : Simplex X (n + 1)) (r : ℤ) :
    boundary (n + 1) (constantCone y (n + 1) (Finsupp.single σ r)) +
      constantCone y n (boundary n (Finsupp.single σ r)) =
        map (ContinuousMap.const X y) (n + 1) (Finsupp.single σ r) := by
  simp only [constantCone_single, boundary_single, face_constant, map_sum, map_zsmul, map_single]
  change altSum (fun _ : Fin (n + 3) => Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r) +
    altSum (fun _ : Fin (n + 2) => Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r) =
      Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r
  rw [altSum_succ]
  exact sub_add_cancel _ _



theorem nullhomotopic_cycle_bounds (f : C(X, Y)) (hf : f.Nullhomotopic)
    (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    map f (n + 1) c ∈ LinearMap.range (boundary (n + 1)) := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  have h₁ := homotopic_maps_difference_bounds H n c hc
  have h₂ := (show map (ContinuousMap.const X y) (n + 1) c ∈ LinearMap.range (boundary (n + 1)) by
    refine ⟨constantCone y (n + 1) c, ?_⟩
    simpa only [hc, map_zero, add_zero] using (show boundary (n + 1) (constantCone y (n + 1) c) + constantCone y n (boundary n c) =
      map (ContinuousMap.const X y) (n + 1) c by
      have he : (boundary (n + 1)).comp (constantCone y (n + 1)) +
          (constantCone y n).comp (boundary n) = map (ContinuousMap.const X y) (n + 1) := by
        apply Finsupp.lhom_ext
        exact constantCone_identity_single y n
      exact DFunLike.congr_fun he c))
  have hm := (LinearMap.range (boundary (X := Y) (n + 1))).sub_mem h₂ h₁
  convert hm using 1
  abel


theorem contractible_cycle_bounds [ContractibleSpace X] (n : ℕ) (c : Chain X (n + 1))
    (hc : boundary n c = 0) : ∃ b : Chain X (n + 2), boundary (n + 1) b = c := by
  have hm : c ∈ LinearMap.ker (boundary (X := X) n) := hc
  rw [(show LinearMap.ker (boundary (X := X) n) = LinearMap.range (boundary (n + 1)) by
    apply le_antisymm
    · intro c hc
      have hm := nullhomotopic_cycle_bounds (ContinuousMap.id X) (id_nullhomotopic X) n c hc
      simpa only [map_id, LinearMap.id_apply] using hm
    · rintro c ⟨b, rfl⟩
      exact boundary_boundary n b)] at hm
  exact hm

end FiniteChains.TopologicalSingular

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.TopologicalSingular

open CategoryTheory AlgebraicTopology

universe u
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def simplicesMap (f : C(X, Y)) : simplices X ⟶ simplices Y where
  app n := TypeCat.ofHom (simplexMap f n.unop.len)
  naturality _ _ _ := rfl

def chainMap (f : C(X, Y)) : complex X ⟶ complex Y :=
  AlternatingFaceMapComplex.map (Functor.whiskerRight (simplicesMap f) freeZ)

theorem chainMap_f (f : C(X, Y)) (n : ℕ) :
    (chainMap f).f n = ModuleCat.ofHom (map f n) := rfl

theorem chainMap_id : chainMap (ContinuousMap.id X) = 𝟙 (complex X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact map_id n

theorem chainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    chainMap (g.comp f) = chainMap f ≫ chainMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact map_comp f g n

def prismComponent {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (i j : ℕ) : (complex X).X i ⟶ (complex Y).X j :=
  if h : j = i + 1 then h ▸ ModuleCat.ofHom (SingularPrism.prism H i) else 0

theorem prismComponent_succ {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i : ℕ) :
    prismComponent H i (i + 1) = ModuleCat.ofHom (SingularPrism.prism H i) := by
  simp [prismComponent]

def chainHomotopy {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    _root_.Homotopy (chainMap g) (chainMap f) where
  hom := prismComponent H
  zero i j hij := by
    have hne : j ≠ i + 1 := by
      intro he
      apply hij
      subst j
      exact rfl
    simp only [prismComponent, dif_neg hne]
  comm i := by
    cases i with
    | zero =>
      rw [_root_.Homotopy.dNext_zero_chainComplex, zero_add,
        _root_.Homotopy.prevD_chainComplex, prismComponent_succ, complex_d, chainMap_f, chainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change map g 0 c = boundary 0 (SingularPrism.prism H 0 c) + map f 0 c
      rw [SingularPrism.prism_identity_zero]
      abel
    | succ i =>
      rw [_root_.Homotopy.dNext_succ_chainComplex, _root_.Homotopy.prevD_chainComplex,
        prismComponent_succ, prismComponent_succ, complex_d, complex_d, chainMap_f, chainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change map g (i + 1) c = SingularPrism.prism H i (boundary i c) +
        boundary (i + 1) (SingularPrism.prism H (i + 1) c) + map f (i + 1) c
      have hh := SingularPrism.prism_identity_succ H i c
      rw [add_comm (SingularPrism.prism H i (boundary i c)), hh]
      abel

def chainHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (complex X) (complex Y) where
  hom := chainMap e.toFun
  inv := chainMap e.invFun
  homotopyHomInvId := by
    rw [← chainMap_comp, ← chainMap_id]
    exact (chainHomotopy e.left_inv.some).symm
  homotopyInvHomId := by
    rw [← chainMap_comp, ← chainMap_id]
    exact (chainHomotopy e.right_inv.some).symm

def homologyIsoOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (complex X).homology n ≅ (complex Y).homology n :=
  (chainHomotopyEquiv e).toHomologyIso n

end FiniteChains.TopologicalSingular
end

section
open scoped ContinuousMap
namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology

/-- Removing the universe lift from singular simplices is a simplicial
isomorphism, not merely a degreewise bijection. -/
def simplicesMathlibIso (X : TopCat.{0}) :
    simplices X ≅ TopCat.toSSet.obj X :=
  NatIso.ofComponents (fun n => (((simplexCoordinates n.unop.len).symm.arrowCongr (Homeomorph.refl X)).toEquiv.trans
      (TopCat.toSSetObjEquiv X n).symm).toIso) (by
    intro n m a
    apply ConcreteCategory.hom_ext
    intro σ
    change Simplex X n.unop.len at σ
    apply (TopCat.toSSetObjEquiv X m).injective
    apply ContinuousMap.ext
    intro z
    change σ (stdSimplex.map a.unop (simplexCoordinates m.unop.len z)) =
      σ (simplexCoordinates n.unop.len (Convexity.StdSimplex.map a.unop z))
    exact congrArg σ (simplexCoordinates_map a.unop z).symm)

/-- The explicit integral chains agree with Mathlib's free singular chains. -/
def freeComplexMathlibIso (X : TopCat.{0}) :
    complex X ≅ AlternatingFaceMapComplex.obj (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ) :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℤ)).mapIso
    (Functor.isoWhiskerRight (simplicesMathlibIso X) (ModuleCat.free ℤ))


/-- The actual explicit singular chain complex computes the coefficients and
singular-homology functor occurring in `Whitehead.Acyclic`. -/
def complexMathlibIso (X : TopCat.{0}) :
    complex X ≅ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X :=
  freeComplexMathlibIso X ≪≫ FiniteChains.freeSingularChainComplexIso X


def homologyMathlibIso (X : TopCat.{0}) (n : ℕ) :
    (complex X).homology n ≅ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj X :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (complexMathlibIso X)

theorem homologyMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap f.hom) n ≫ (homologyMathlibIso Y n).hom =
      (homologyMathlibIso X n).hom ≫ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f := by
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _
  rw [← Functor.map_comp, ← Functor.map_comp, (show chainMap f.hom ≫ (complexMathlibIso Y).hom =
      (complexMathlibIso X).hom ≫ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map f by
    dsimp only [complexMathlibIso, Iso.trans_hom]
    rw [← Category.assoc, (show chainMap f.hom ≫ (freeComplexMathlibIso Y).hom =
      (freeComplexMathlibIso X).hom ≫ AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ)) by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro σ r
      change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single σ r)) =
        Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single σ r))
      simp
      rfl), Category.assoc,
      FiniteChains.freeSingularChainComplexIso_natural, Category.assoc])]

/-- Homotopy equivalent spaces have isomorphic actual integral singular homology. -/
def mathlibHomologyIsoOfHomotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) ≅
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y) :=
  (homologyMathlibIso (TopCat.of X) n).symm ≪≫ homologyIsoOfHomotopyEquiv e n ≪≫
    homologyMathlibIso (TopCat.of Y) n

end FiniteChains.TopologicalSingular

namespace Whitehead
open CategoryTheory

/-- Acyclicity in the original statement is invariant under homotopy equivalence. -/
theorem acyclic_iff_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) : Acyclic X ↔ Acyclic Y := by
  constructor
  · intro h n hn
    exact (h n hn).of_iso
      (FiniteChains.TopologicalSingular.mathlibHomologyIsoOfHomotopyEquiv e n).symm
  · intro h n hn
    exact (h n hn).of_iso
      (FiniteChains.TopologicalSingular.mathlibHomologyIsoOfHomotopyEquiv e n)

end Whitehead
end

namespace Whitehead
open scoped Topology Classical

variable {X Y D : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]

def CoverPullback (f : C(X, Y)) (p : C(D, Y)) :=
  {z : X × D // f z.1 = p z.2}

instance (f : C(X, Y)) (p : C(D, Y)) : TopologicalSpace (CoverPullback f p) :=
  inferInstanceAs (TopologicalSpace {z : X × D // f z.1 = p z.2})

def coverPullbackProjection (f : C(X, Y)) (p : C(D, Y)) : C(CoverPullback f p, X) :=
  ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

def coverPullbackMap (f : C(X, Y)) (p : C(D, Y)) : C(CoverPullback f p, D) :=
  ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩


def coverPullbackLocalChart {F : Type} [TopologicalSpace F]
    (f : C(X, Y)) (p : C(D, Y)) (U : Set Y) (e : p ⁻¹' U ≃ₜ U × F)
    (he : ∀ d, (e d).1.val = p d.val) :
    (coverPullbackProjection f p) ⁻¹' (f ⁻¹' U) ≃ₜ (f ⁻¹' U) × F where
  toFun z := (⟨z.val.val.1, z.property⟩,
    (e ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact z.property⟩).2)
  invFun w := ⟨⟨(w.1.val, (e.symm (⟨f w.1.val, w.1.property⟩, w.2)).val),
    ((he (e.symm ((⟨f w.1.val, w.1.property⟩), (w.2)))).symm.trans
    (congrArg (fun w : U × F => w.1.val) (e.apply_symm_apply ((⟨f w.1.val, w.1.property⟩), (w.2))))).symm⟩,
    w.1.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext rfl ?_
    let d : p ⁻¹' U := ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact z.property⟩
    have hd : (⟨f z.val.val.1, z.property⟩, (e d).2) = e d := by
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact z.val.property.trans (he d).symm
    change (e.symm (⟨f z.val.val.1, z.property⟩, (e d).2)).val = d.val
    rw [hd, e.symm_apply_apply]
  right_inv w := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem coverPullbackProjection_isCoveringMap (f : C(X, Y)) (p : C(D, Y))
    (hp : IsCoveringMap p) : IsCoveringMap (coverPullbackProjection f p) := by
  intro x
  obtain ⟨hdisc, U, hx, hU, _, e, he⟩ := hp (f x)
  have h : IsEvenlyCovered (coverPullbackProjection f p) x (p ⁻¹' {f x}) := by
    refine ⟨hdisc, f ⁻¹' U, hx, hU.preimage f.continuous,
      (hU.preimage f.continuous).preimage (coverPullbackProjection f p).continuous,
      coverPullbackLocalChart f p U e he, ?_⟩
    exact fun _ => rfl
  exact h.to_isEvenlyCovered_preimage

theorem coverPullbackProjection_surjective (f : C(X, Y)) (p : C(D, Y))
    (hp : Function.Surjective p) : Function.Surjective (coverPullbackProjection f p) := by
  intro x
  obtain ⟨d, hd⟩ := hp (f x)
  exact ⟨⟨(x, d), hd.symm⟩, rfl⟩

def coverPullbackDeck (f : C(X, Y)) (p : C(D, Y))
    (h : D ≃ₜ D) (hh : ∀ d, p (h d) = p d) : CoverPullback f p ≃ₜ CoverPullback f p where
  toFun z := ⟨(z.val.1, h z.val.2), z.property.trans (hh z.val.2).symm⟩
  invFun z := ⟨(z.val.1, h.symm z.val.2), z.property.trans (by
    have he := hh (h.symm z.val.2)
    rw [h.apply_symm_apply] at he
    exact he)⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (h.symm_apply_apply z.val.2)
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (h.apply_symm_apply z.val.2)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem coverPullbackProjection_regular (f : C(X, Y)) (p : C(D, Y))
    (hp : Regular p) : Regular (coverPullbackProjection f p) := by
  intro a b hab
  have hpab  :=
    a.property.symm.trans ((congrArg f hab).trans b.property)
  obtain ⟨h, hh, he⟩ := hp a.val.2 b.val.2 hpab
  refine ⟨coverPullbackDeck f p h hh, fun _ => rfl, ?_⟩
  apply Subtype.ext
  exact Prod.ext hab he

def coverPullbackIdentity (p : C(D, Y)) : CoverPullback (ContinuousMap.id Y) p ≃ₜ D where
  toFun := coverPullbackMap (ContinuousMap.id Y) p
  invFun d := ⟨(p d, d), rfl⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := (coverPullbackMap (ContinuousMap.id Y) p).continuous
  continuous_invFun := (p.continuous.prodMk continuous_id).subtype_mk _

def coverPullbackComposition {Z : Type} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (p : C(D, Z)) :
    CoverPullback f (coverPullbackProjection g p) ≃ₜ CoverPullback (g.comp f) p where
  toFun z := ⟨(z.val.1, z.val.2.val.2),
    (congrArg g z.property).trans z.val.2.property⟩
  invFun z := ⟨(z.val.1, ⟨(f z.val.1, z.val.2), z.property⟩), rfl⟩
  left_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    apply Subtype.ext
    exact Prod.ext z.property rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem coverPullbackComposition_map {Z : Type} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (p : C(D, Z))
    (z : CoverPullback f (coverPullbackProjection g p)) :
    coverPullbackMap (g.comp f) p (coverPullbackComposition f g p z) =
      coverPullbackMap g p (coverPullbackMap f (coverPullbackProjection g p) z) := rfl

end Whitehead

namespace Whitehead
open scoped unitInterval Topology Classical

variable {X Y D : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]

def coverPullbackHomotopyLift {f₀ f₁ : C(X, Y)} (p : C(D, Y)) (hp : IsCoveringMap p)
    (H : f₀.Homotopy f₁) : C(I × CoverPullback f₀ p, D) :=
  hp.liftHomotopy
    (H.toContinuousMap.comp ⟨fun tz => (tz.1, tz.2.val.1),
      continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))⟩)
    (coverPullbackMap f₀ p) (fun z => (H.apply_zero z.val.1).trans z.property)

theorem coverPullbackHomotopyLift_lifts {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) (t : I) (z : CoverPullback f₀ p) :
    p (coverPullbackHomotopyLift p hp H (t, z)) = H (t, z.val.1) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, z)

@[simp] theorem coverPullbackHomotopyLift_zero {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) (z : CoverPullback f₀ p) :
    coverPullbackHomotopyLift p hp H (0, z) = z.val.2 :=
  hp.liftHomotopy_zero _ _ _ z

def coverPullbackTransport {f₀ f₁ : C(X, Y)} (p : C(D, Y)) (hp : IsCoveringMap p)
    (H : f₀.Homotopy f₁) : C(CoverPullback f₀ p, CoverPullback f₁ p) where
  toFun z := ⟨(z.val.1, coverPullbackHomotopyLift p hp H (1, z)),
    (H.apply_one z.val.1).symm.trans (coverPullbackHomotopyLift_lifts p hp H 1 z).symm⟩
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    ((coverPullbackHomotopyLift p hp H).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _

theorem coverPullbackTransport_symm_apply {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) (z : CoverPullback f₀ p) :
    coverPullbackTransport p hp H.symm (coverPullbackTransport p hp H z) = z := by
  let z₁ := coverPullbackTransport p hp H z
  let R  := fun t => coverPullbackHomotopyLift p hp H (unitInterval.symm t, z)
  let T  := fun t => coverPullbackHomotopyLift p hp H.symm (t, z₁)
  have hR : Continuous R := (coverPullbackHomotopyLift p hp H).continuous.comp
    (unitInterval.continuous_symm.prodMk continuous_const)
  have hT : Continuous T := (coverPullbackHomotopyLift p hp H.symm).continuous.comp
    (continuous_id.prodMk continuous_const)
  have hproj : p ∘ R = p ∘ T := by
    funext t
    change p (coverPullbackHomotopyLift p hp H (unitInterval.symm t, z)) =
      p (coverPullbackHomotopyLift p hp H.symm (t, z₁))
    rw [coverPullbackHomotopyLift_lifts, coverPullbackHomotopyLift_lifts]
    rfl
  have hzero : R 0 = T 0 := by
    change coverPullbackHomotopyLift p hp H (unitInterval.symm 0, z) =
      coverPullbackHomotopyLift p hp H.symm (0, z₁)
    rw [unitInterval.symm_zero, coverPullbackHomotopyLift_zero]
    rfl
  have he := congrFun (hp.eq_of_comp_eq hR hT hproj 0 hzero) 1
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change coverPullbackHomotopyLift p hp H.symm (1, z₁) = z.val.2
  change coverPullbackHomotopyLift p hp H (unitInterval.symm 1, z) =
    coverPullbackHomotopyLift p hp H.symm (1, z₁) at he
  simpa only [unitInterval.symm_one, coverPullbackHomotopyLift_zero] using he.symm

def coverPullbackHomotopyHomeomorph {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) : CoverPullback f₀ p ≃ₜ CoverPullback f₁ p where
  toFun := coverPullbackTransport p hp H
  invFun := coverPullbackTransport p hp H.symm
  left_inv := coverPullbackTransport_symm_apply p hp H
  right_inv z := by
    simpa only [ContinuousMap.Homotopy.symm_symm] using
      coverPullbackTransport_symm_apply p hp H.symm z
  continuous_toFun := (coverPullbackTransport p hp H).continuous
  continuous_invFun := (coverPullbackTransport p hp H.symm).continuous

def coverPullbackMapHomotopy {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) :
    ContinuousMap.Homotopy (coverPullbackMap f₀ p)
      ((coverPullbackMap f₁ p).comp (coverPullbackTransport p hp H)) where
  toContinuousMap := coverPullbackHomotopyLift p hp H
  map_zero_left := coverPullbackHomotopyLift_zero p hp H
  map_one_left _ := rfl

def coverPullbackMapEquivOfHomotopicId (f : C(Y, Y)) (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f.Homotopy (ContinuousMap.id Y)) :
    ContinuousMap.HomotopyEquiv (CoverPullback f p) D := by
  let E := ((coverPullbackHomotopyHomeomorph p hp H).trans (coverPullbackIdentity p)).toHomotopyEquiv
  have h : (coverPullbackMap f p).Homotopic E.toFun := ⟨coverPullbackMapHomotopy p hp H⟩
  exact {
    toFun := coverPullbackMap f p
    invFun := E.invFun
    left_inv := ((ContinuousMap.Homotopic.refl E.invFun).comp h).trans E.left_inv
    right_inv := (h.comp (ContinuousMap.Homotopic.refl E.invFun)).trans E.right_inv }

/-- The projection from the pullback to the original total space is a
homotopy equivalence when the base map is. Two-of-six avoids imposing any
coherence or stationarity condition on the given base homotopies. -/
def coverPullbackMapHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (p : C(D, Y)) (hp : IsCoveringMap p) :
    ContinuousMap.HomotopyEquiv (CoverPullback e.toFun p) D := by
  let q := coverPullbackProjection e.toFun p
  have hq := coverPullbackProjection_isCoveringMap e.toFun p hp
  let r := coverPullbackProjection e.invFun q
  let f := coverPullbackMap e.toFun r
  let g := coverPullbackMap e.invFun q
  let h := coverPullbackMap e.toFun p
  let E := (coverPullbackComposition e.toFun e.invFun q).toHomotopyEquiv.trans
    (coverPullbackMapEquivOfHomotopicId (e.invFun.comp e.toFun) q hq
      (Classical.choice e.left_inv))
  let F := (coverPullbackComposition e.invFun e.toFun p).toHomotopyEquiv.trans
    (coverPullbackMapEquivOfHomotopicId (e.toFun.comp e.invFun) p hp
      (Classical.choice e.right_inv))
  have hE : E.toFun = g.comp f := rfl
  have hF : F.toFun = h.comp g := rfl
  exact ContinuousMap.HomotopyEquiv.twoOfSixRight f g h E hE F hF

@[simp] theorem coverPullbackMapHomotopyEquiv_toFun (e : ContinuousMap.HomotopyEquiv X Y)
    (p : C(D, Y)) (hp : IsCoveringMap p) :
    (coverPullbackMapHomotopyEquiv e p hp).toFun = coverPullbackMap e.toFun p := rfl

end Whitehead

namespace Whitehead
open scoped Topology unitInterval

theorem connectedSpace_of_homotopyEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : ConnectedSpace X := by
  let y₀ : Y := Classical.choice inferInstance
  let H := Classical.choice e.left_inv
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨e.invFun y₀, Set.eq_univ_of_forall fun x => ?_⟩
  have hi  :=
    (isConnected_range e.invFun.continuous).subset_connectedComponent
      ⟨y₀, rfl⟩ ⟨e.toFun x, rfl⟩
  have hc : Continuous (fun t : I => H (t, x)) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  have hx  :=
    (isConnected_range hc).subset_connectedComponent
      ⟨0, H.apply_zero x⟩ ⟨1, H.apply_one x⟩
  rw [connectedComponent_eq hi]
  exact hx

/-- Pull an actual connected acyclic regular covering back along a homotopy
equivalence of the bases. No local connectedness or CW structure is needed
on the total space of the given covering. -/
theorem hasAcyclicRegularCover_of_homotopyEquiv (K L : TwoComplex)
    (e : ContinuousMap.HomotopyEquiv K L) (h : HasAcyclicRegularCover L) :
    HasAcyclicRegularCover K := by
  obtain ⟨D, tD, p, hp, hsurj, hconn, hreg, hac⟩ := h
  letI := tD
  letI : ConnectedSpace D := hconn
  let P := CoverPullback e.toFun p
  let E := coverPullbackMapHomotopyEquiv e p hp
  refine ⟨P, inferInstance, coverPullbackProjection e.toFun p,
    coverPullbackProjection_isCoveringMap e.toFun p hp,
    coverPullbackProjection_surjective e.toFun p hsurj, ?_,
    coverPullbackProjection_regular e.toFun p hreg, ?_⟩
  · exact connectedSpace_of_homotopyEquiv E
  · exact (acyclic_iff_of_homotopyEquiv E).mpr hac

end Whitehead

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

def inclusion (A : Set X) : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩


theorem map_inclusion_injective (A : Set X) (n : ℕ) : Function.Injective (map (inclusion A) n) := by
  exact Finsupp.mapDomain_injective (by
    intro σ τ he
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact DFunLike.congr_fun he z)

def subChains (A : Set X) (n : ℕ) : Submodule ℤ (Chain X n) :=
  LinearMap.range (map (inclusion A) n)

theorem boundary_mem_subChains (A : Set X) (n : ℕ) {c : Chain X (n + 1)}
    (hc : c ∈ subChains A (n + 1)) : boundary n c ∈ subChains A n := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨boundary n b, map_boundary (inclusion A) n b⟩

theorem subChains_mono {A B : Set X} (h : A ⊆ B) (n : ℕ) : subChains A n ≤ subChains B n := by
  let j : C(A, B) := ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩
  rintro _ ⟨c, rfl⟩
  refine ⟨map j n c, ?_⟩
  have he : (inclusion B).comp j = inclusion A := rfl
  have hm := DFunLike.congr_fun (map_comp j (inclusion B) n) c
  rw [he] at hm
  exact hm.symm

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem single_mem_subChains (A : Set X) (n : ℕ) (σ : Simplex X n) (r : ℤ)
    (hσ : ∀ z, σ z ∈ A) : Finsupp.single σ r ∈ subChains A n := by
  let τ : Simplex A n := ⟨fun z => ⟨σ z, hσ z⟩, σ.continuous.subtype_mk _⟩
  refine ⟨Finsupp.single τ r, ?_⟩
  rw [map_single]
  rfl

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

def pathSimplex {a b : X} (γ : Path a b) : Simplex X 1 :=
  ⟨fun z => γ (stdSimplexHomeomorphUnitInterval z),
    γ.continuous.comp stdSimplexHomeomorphUnitInterval.continuous⟩

@[simp] theorem face_pathSimplex_zero {a b : X} (γ : Path a b) :
    face (0 : Fin 2) (pathSimplex γ) = ContinuousMap.const _ b := by
  letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
  ext z
  rw [show z = stdSimplex.vertex 0 from Subsingleton.elim _ _]
  rw [face_apply, stdSimplex.map_vertex]
  exact γ.target

@[simp] theorem face_pathSimplex_one {a b : X} (γ : Path a b) :
    face (1 : Fin 2) (pathSimplex γ) = ContinuousMap.const _ a := by
  letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
  ext z
  rw [show z = stdSimplex.vertex 0 from Subsingleton.elim _ _]
  rw [face_apply, stdSimplex.map_vertex]
  exact γ.source

theorem boundary_pathSimplex {a b : X} (γ : Path a b) (r : ℤ) :
    boundary 0 (Finsupp.single (pathSimplex γ) r) =
      Finsupp.single (ContinuousMap.const _ b) r - Finsupp.single (ContinuousMap.const _ a) r := by
  rw [boundary_single]
  rw [Fin.sum_univ_two]
  change 1 • Finsupp.single (face 0 (pathSimplex γ)) r +
    (-1) • Finsupp.single (face 1 (pathSimplex γ)) r = _
  rw [one_smul, neg_smul, one_smul, face_pathSimplex_zero, face_pathSimplex_one, sub_eq_add_neg]

def pathCone [PathConnectedSpace X] (root : X) : Chain X 0 →ₗ[ℤ] Chain X 1 :=
  Finsupp.linearCombination ℤ (fun σ : Simplex X 0 =>
    Finsupp.single (pathSimplex (PathConnectedSpace.somePath root (zeroSimplexEquiv σ))) 1)



theorem ker_augmentation_eq_range_boundary [PathConnectedSpace X] :
    LinearMap.ker (augmentation (X := X)) = LinearMap.range (boundary 0) := by
  apply le_antisymm
  · intro c hc
    let root  := Classical.arbitrary X
    refine ⟨pathCone root c, ?_⟩
    rw [(show boundary 0 (pathCone root c) = c - augmentation c • Finsupp.single (ContinuousMap.const _ root) 1 by
      have he : (boundary 0).comp (pathCone root) = LinearMap.id -
          augmentation.smulRight (Finsupp.single (ContinuousMap.const _ root) 1) := by
        apply Finsupp.lhom_ext
        intro σ a
        simp only [LinearMap.comp_apply, (show pathCone root (Finsupp.single σ a) =
      Finsupp.single (pathSimplex (PathConnectedSpace.somePath root (zeroSimplexEquiv σ))) a by
          rw [pathCone, Finsupp.linearCombination_single, Finsupp.smul_single]
          simp), boundary_pathSimplex, LinearMap.sub_apply,
          LinearMap.id_apply, LinearMap.smulRight_apply, augmentation_single, Finsupp.smul_single,
          smul_eq_mul, mul_one]
        rw [show ContinuousMap.const (Domain 0) (zeroSimplexEquiv σ) = σ from zeroSimplexEquiv.symm_apply_apply σ]
      exact DFunLike.congr_fun he c), show augmentation c = 0 from hc, zero_smul, sub_zero]
  · rintro c ⟨d, rfl⟩
    exact augmentation_boundary d

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Exactness in a contractible subspace gives a filling that stays in it. -/
theorem contractible_supported_cycle_bounds (A : Set X) [ContractibleSpace A]
    (n : ℕ) (c : Chain X (n + 1)) (hc : c ∈ subChains A (n + 1))
    (hz : boundary n c = 0) :
    ∃ b : Chain X (n + 2), b ∈ subChains A (n + 2) ∧ boundary (n + 1) b = c := by
  obtain ⟨a, rfl⟩ := hc
  have ha : boundary n a = 0 := by
    apply map_inclusion_injective A n
    rw [map_boundary, hz, map_zero]
  obtain ⟨b, hb⟩ := contractible_cycle_bounds n a ha
  refine ⟨map (inclusion A) (n + 2) b, ⟨b, rfl⟩, ?_⟩
  rw [← map_boundary, hb]

/-- The same support control holds in augmented degree zero. -/
theorem connected_supported_zero_bounds (A : Set X) [PathConnectedSpace A]
    (c : Chain X 0) (hc : c ∈ subChains A 0) (hz : augmentation c = 0) :
    ∃ b : Chain X 1, b ∈ subChains A 1 ∧ boundary 0 b = c := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a ∈ LinearMap.ker augmentation := by
    change augmentation a = 0
    simpa only [augmentation_map] using hz
  rw [ker_augmentation_eq_range_boundary] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨map (inclusion A) 1 b, ⟨b, rfl⟩, ?_⟩
  rw [← map_boundary, hb]

end FiniteChains.TopologicalSingular

namespace FiniteChains.VertexChains

open CategoryTheory AlgebraicTopology

universe u v
abbrev Vertices (V : Type u) (n : ℕ) := Fin (n + 1) → V
abbrev Chain (V : Type u) (n : ℕ) := Vertices V n →₀ ℤ

def simplices (V : Type u) : SimplicialObject (Type u) where
  obj n := Vertices V n.unop.len
  map f := TypeCat.ofHom (fun v => v ∘ f.unop.toOrderHom)

def modules (V : Type u) := simplices V ⋙ TopologicalSingular.freeZ

variable {V : Type u} {W : Type v}

theorem linearMap_ext_basis {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    {f g : (ι →₀ ℤ) →ₗ[ℤ] M} (h : ∀ v, f (Finsupp.single v 1) = g (Finsupp.single v 1)) : f = g := by
  apply Finsupp.lhom_ext
  intro v r
  have he : Finsupp.single v r = r • Finsupp.single v (1 : ℤ) := by simp
  grind

def face {n : ℕ} (i : Fin (n + 2)) (v : Vertices V (n + 1)) : Vertices V n :=
  v ∘ i.succAbove

def boundary (n : ℕ) : Chain V (n + 1) →ₗ[ℤ] Chain V n :=
  (AlternatingFaceMapComplex.objD (modules V) n).hom


theorem boundary_single (n : ℕ) (v : Vertices V (n + 1)) (r : ℤ) :
    boundary n (Finsupp.single v r) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Finsupp.single (face i v) r := by
  rw [(show boundary (V := V) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Finsupp.lmapDomain ℤ ℤ (face i) by
    simp only [boundary, AlternatingFaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
    rfl)]
  simp

theorem boundary_boundary (n : ℕ) (c : Chain V (n + 2)) : boundary n (boundary (n + 1) c) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (AlternatingFaceMapComplex.d_squared (modules V) n)
  exact DFunLike.congr_fun h c

def augmentation : Chain V 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : Vertices V 0 => 1)

@[simp] theorem augmentation_single (v : Vertices V 0) (r : ℤ) :
    augmentation (Finsupp.single v r) = r := by simp [augmentation]

theorem augmentation_boundary (c : Chain V 1) : augmentation (boundary 0 c) = 0 := by
  have he : augmentation.comp (boundary (V := V) 0) = 0 := by
    apply Finsupp.lhom_ext
    intro v r
    change augmentation (boundary 0 (Finsupp.single v r)) = 0
    rw [boundary_single, Fin.sum_univ_two]
    simp
  exact DFunLike.congr_fun he c

def map (f : V → W) (n : ℕ) : Chain V n →ₗ[ℤ] Chain W n :=
  Finsupp.lmapDomain ℤ ℤ (fun v => f ∘ v)

@[simp] theorem map_single (f : V → W) (n : ℕ) (v : Vertices V n) (r : ℤ) :
    map f n (Finsupp.single v r) = Finsupp.single (f ∘ v) r := Finsupp.mapDomain_single

theorem map_boundary (f : V → W) (n : ℕ) (c : Chain V (n + 1)) :
    map f n (boundary n c) = boundary n (map f (n + 1) c) := by
  have he : (map f n).comp (boundary n) = (boundary n).comp (map f (n + 1)) := by
    apply Finsupp.lhom_ext
    intro v r
    simp only [LinearMap.comp_apply, boundary_single, map_single, map_sum, map_zsmul]
    rfl
  exact DFunLike.congr_fun he c

def cone (p : V) (n : ℕ) : Chain V n →ₗ[ℤ] Chain V (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun v : Vertices V n => Fin.cons p v)

@[simp] theorem cone_single (p : V) (n : ℕ) (v : Vertices V n) (r : ℤ) :
    cone p n (Finsupp.single v r) = Finsupp.single (Fin.cons p v) r := Finsupp.mapDomain_single

theorem face_cone_zero (p : V) {n : ℕ} (v : Vertices V n) : face 0 (Fin.cons p v) = v := rfl

theorem face_cone_succ (p : V) {n : ℕ} (v : Vertices V (n + 1)) (i : Fin (n + 2)) :
    face i.succ (Fin.cons p v) = Fin.cons p (face i v) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · simp [face]



theorem boundary_cone_zero (p : V) (c : Chain V 0) :
    boundary 0 (cone p 0 c) = c - augmentation c • Finsupp.single (fun _ : Fin 1 => p) 1 := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add v r c _ _ ih =>
    rw [map_add, map_add, (show boundary 0 (cone p 0 (Finsupp.single v r)) =
      Finsupp.single v r - r • Finsupp.single (fun _ : Fin 1 => p) 1 by
      rw [cone_single, boundary_single, Fin.sum_univ_two, face_cone_zero, (show face 1 (Fin.cons p v) = fun _ => p by
        funext j
        have hj : j = 0 := by ext; omega
        subst j
        rfl)]
      simp [sub_eq_add_neg]), ih, map_add, augmentation_single, add_smul]
    abel

theorem boundary_cone_single (p : V) (n : ℕ) (v : Vertices V (n + 1)) (r : ℤ) :
    boundary (n + 1) (cone p (n + 1) (Finsupp.single v r)) =
      Finsupp.single v r - cone p n (boundary n (Finsupp.single v r)) := by
  rw [cone_single, boundary_single, Fin.sum_univ_succ, face_cone_zero, boundary_single]
  simp only [Fin.val_zero, pow_zero, one_smul, face_cone_succ, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Finset.sum_neg_distrib, map_sum, map_zsmul, cone_single, sub_eq_add_neg]

theorem boundary_cone (p : V) (n : ℕ) (c : Chain V (n + 1)) :
    boundary (n + 1) (cone p (n + 1) c) = c - cone p n (boundary n c) := by
  have he : (boundary (n + 1)).comp (cone p (n + 1)) =
      LinearMap.id - (cone p n).comp (boundary n) := by
    apply Finsupp.lhom_ext
    exact boundary_cone_single p n
  exact DFunLike.congr_fun he c

theorem map_cone (f : V → W) (p : V) (n : ℕ) (c : Chain V n) :
    map f (n + 1) (cone p n c) = cone (f p) n (map f n c) := by
  have he : (map f (n + 1)).comp (cone p n) = (cone (f p) n).comp (map f n) := by
    apply Finsupp.lhom_ext
    intro v r
    simp
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact DFunLike.congr_fun he c

end FiniteChains.VertexChains

namespace FiniteChains.VertexChains

universe u v
variable {V : Type u} {W : Type v}
variable (center : ∀ n, Vertices V n → V)

def subdivide : (n : ℕ) → Chain V n →ₗ[ℤ] Chain V n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℤ (fun v : Vertices V (n + 1) =>
      cone (center (n + 1) v) n (subdivide n (boundary n (Finsupp.single v 1))))

theorem subdivide_zero (c : Chain V 0) : subdivide center 0 c = c := rfl

theorem subdivide_succ_single (n : ℕ) (v : Vertices V (n + 1)) (r : ℤ) :
    subdivide center (n + 1) (Finsupp.single v r) =
      r • cone (center (n + 1) v) n (subdivide center n (boundary n (Finsupp.single v 1))) := by
  simp only [subdivide, Finsupp.linearCombination_single]

theorem boundary_subdivide (n : ℕ) :
    (boundary n).comp (subdivide center (n + 1)) = (subdivide center n).comp (boundary n) := by
  induction n with
  | zero =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul, subdivide_zero]
    rw [boundary_cone_zero, augmentation_boundary, zero_smul, sub_zero]
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul]
    rw [boundary_cone]
    have hz : boundary n (subdivide center (n + 1)
        (boundary (n + 1) (Finsupp.single v 1))) = 0 := by
      rw [← LinearMap.comp_apply, ih, LinearMap.comp_apply, boundary_boundary, map_zero]
    rw [hz, map_zero, sub_zero]

theorem subdivide_boundary (n : ℕ) (c : Chain V (n + 1)) :
    subdivide center n (boundary n c) = boundary n (subdivide center (n + 1) c) :=
  (DFunLike.congr_fun (boundary_subdivide center n) c).symm

theorem subdivide_naturality (other : ∀ n, Vertices W n → W) (f : V → W)
    (hf : ∀ n v, f (center n v) = other n (f ∘ v)) (n : ℕ) :
    (map f n).comp (subdivide center n) = (subdivide other n).comp (map f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivide_succ_single, one_smul, map_single]
    rw [map_cone, hf]
    have he := DFunLike.congr_fun ih (boundary n (Finsupp.single v 1))
    dsimp only [LinearMap.comp_apply] at he
    rw [he, map_boundary, map_single]

end FiniteChains.VertexChains

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u v
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {A : Set E} {B : Set F} (hA : Convex ℝ A) (hB : Convex ℝ B)

def affineEval {n : ℕ} (v : Vertices A n) : TopologicalSingular.Simplex A n :=
  ⟨fun z => ⟨∑ i, z.val i • (v i).val,
    hA.sum_mem (fun i _ => z.property.1 i) z.property.2 (fun i _ => (v i).property)⟩, by
    apply Continuous.subtype_mk
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const⟩

theorem affineEval_apply {n : ℕ} (v : Vertices A n) (z : TopologicalSingular.Domain n) :
    (affineEval hA v z).val = ∑ i, z.val i • (v i).val := rfl

theorem affineEval_reindex {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (v : Vertices A n) (z : TopologicalSingular.Domain m) :
    affineEval hA (v ∘ f) z = affineEval hA v (stdSimplex.map f z) := by
  ext
  change (∑ i, z.val i • (v (f i)).val) = ∑ j, (stdSimplex.map f z).val j • (v j).val
  symm
  calc
    _ = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => f i = j), z.val i • (v (f i)).val := by
      apply Finset.sum_congr rfl
      intro j _
      change (FunOnFinite.linearMap ℝ ℝ f z.val) j • (v j).val = _
      rw [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ f (fun i => z.val i • (v (f i)).val)

theorem face_affineEval {n : ℕ} (i : Fin (n + 2)) (v : Vertices A (n + 1)) :
    TopologicalSingular.face i (affineEval hA v) = affineEval hA (face i v) := by
  apply ContinuousMap.ext
  intro z
  exact (affineEval_reindex hA i.succAbove v z).symm

def realize (n : ℕ) : VertexChains.Chain A n →ₗ[ℤ] TopologicalSingular.Chain A n :=
  Finsupp.lmapDomain ℤ ℤ (affineEval hA)

@[simp] theorem realize_single (n : ℕ) (v : Vertices A n) (r : ℤ) :
    realize hA n (Finsupp.single v r) = Finsupp.single (affineEval hA v) r :=
  Finsupp.mapDomain_single

theorem realize_boundary (n : ℕ) (c : VertexChains.Chain A (n + 1)) :
    realize hA n (VertexChains.boundary n c) = TopologicalSingular.boundary n (realize hA (n + 1) c) := by
  have he : (realize hA n).comp (VertexChains.boundary n) =
      (TopologicalSingular.boundary n).comp (realize hA (n + 1)) := by
    apply Finsupp.lhom_ext
    intro v r
    simp only [LinearMap.comp_apply, VertexChains.boundary_single, realize_single,
      TopologicalSingular.boundary_single, map_sum, map_zsmul, face_affineEval]
  exact DFunLike.congr_fun he c

def center (n : ℕ) (v : Vertices A n) : A := affineEval hA v stdSimplex.barycenter

theorem center_val (n : ℕ) (v : Vertices A n) :
    (center hA n v).val = ∑ i, ((n + 1 : ℕ) : ℝ)⁻¹ • (v i).val := by
  simp only [center, affineEval_apply, stdSimplex.barycenter_apply, Fintype.card_fin]

def restriction (f : E →L[ℝ] F) (hf : MapsTo f A B) : C(A, B) :=
  ⟨fun a => ⟨f a.val, hf a.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem affineEval_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) {n : ℕ} (v : Vertices A n) :
    TopologicalSingular.simplexMap (restriction f hf) n (affineEval hA v) =
      affineEval hB (restriction f hf ∘ v) := by
  apply ContinuousMap.ext
  intro z
  ext
  change f (∑ i, z.val i • (v i).val) = ∑ i, z.val i • f (v i).val
  simp

theorem center_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ) (v : Vertices A n) :
    restriction f hf (center hA n v) = center hB n (restriction f hf ∘ v) :=
  DFunLike.congr_fun (affineEval_naturality hA hB f hf v) stdSimplex.barycenter

theorem realize_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ)
    (c : VertexChains.Chain A n) :
    TopologicalSingular.map (restriction f hf) n (realize hA n c) =
      realize hB n (VertexChains.map (restriction f hf) n c) := by
  have he : (TopologicalSingular.map (restriction f hf) n).comp (realize hA n) =
      (realize hB n).comp (VertexChains.map (restriction f hf) n) := by
    apply Finsupp.lhom_ext
    intro v r
    simp
    rw [affineEval_naturality hA hB f hf]
  exact DFunLike.congr_fun he c

def standardVertices (d : ℕ) : Vertices (TopologicalSingular.Domain d) d :=
  fun i => stdSimplex.vertex i

theorem affineEval_standardVertices (d : ℕ) :
    affineEval (convex_stdSimplex ℝ (Fin (d + 1))) (standardVertices d) =
      ContinuousMap.id (TopologicalSingular.Domain d) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  funext j
  simp [affineEval, standardVertices, Finset.sum_apply, Pi.single_apply]

end FiniteChains.AffineVertexChains

namespace FiniteChains.VertexChains

universe u v
variable {V : Type u} {W : Type v}
variable (center : ∀ n, Vertices V n → V)

def subdivideHomotopy : (n : ℕ) → Chain V n →ₗ[ℤ] Chain V (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ (fun v : Vertices V (n + 1) =>
      cone (v 0) (n + 1) (subdivide center (n + 1) (Finsupp.single v 1) -
        Finsupp.single v 1 - subdivideHomotopy n (boundary n (Finsupp.single v 1))))

theorem subdivideHomotopy_zero (c : Chain V 0) : subdivideHomotopy center 0 c = 0 := rfl

theorem subdivideHomotopy_succ_single (n : ℕ) (v : Vertices V (n + 1)) (r : ℤ) :
    subdivideHomotopy center (n + 1) (Finsupp.single v r) =
      r • cone (v 0) (n + 1) (subdivide center (n + 1) (Finsupp.single v 1) -
        Finsupp.single v 1 - subdivideHomotopy center n (boundary n (Finsupp.single v 1))) := by
  simp only [subdivideHomotopy, Finsupp.linearCombination_single]


theorem subdivideHomotopy_step (n : ℕ)
    (h : ∀ c : Chain V (n + 1), boundary n (subdivideHomotopy center n (boundary n c)) =
      subdivide center n (boundary n c) - boundary n c) :
    (boundary (n + 1)).comp (subdivideHomotopy center (n + 1)) +
      (subdivideHomotopy center n).comp (boundary n) = subdivide center (n + 1) - LinearMap.id := by
  apply linearMap_ext_basis
  intro v
  change boundary (n + 1) (subdivideHomotopy center (n + 1) (Finsupp.single v 1)) +
    subdivideHomotopy center n (boundary n (Finsupp.single v 1)) =
    subdivide center (n + 1) (Finsupp.single v 1) - Finsupp.single v 1
  rw [subdivideHomotopy_succ_single, one_smul, boundary_cone]
  have hz : boundary n (subdivide center (n + 1) (Finsupp.single v 1) - Finsupp.single v 1 -
      subdivideHomotopy center n (boundary n (Finsupp.single v 1))) = 0 := by
    rw [map_sub, map_sub, ← subdivide_boundary, h, sub_self]
  rw [hz, map_zero, sub_zero]
  abel

theorem subdivideHomotopy_identity (n : ℕ) :
    (boundary (n + 1)).comp (subdivideHomotopy center (n + 1)) +
      (subdivideHomotopy center n).comp (boundary n) = subdivide center (n + 1) - LinearMap.id := by
  induction n with
  | zero =>
    apply subdivideHomotopy_step
    intro c
    exact (by
      rw [subdivideHomotopy_zero, map_zero, subdivide_zero, sub_self])
  | succ n ih =>
    apply subdivideHomotopy_step
    intro c
    have he := DFunLike.congr_fun ih (boundary (n + 1) c)
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, boundary_boundary, map_zero, add_zero] using he

theorem subdivideHomotopy_identity_succ (n : ℕ) (c : Chain V (n + 1)) :
    boundary (n + 1) (subdivideHomotopy center (n + 1) c) +
      subdivideHomotopy center n (boundary n c) = subdivide center (n + 1) c - c :=
  DFunLike.congr_fun (subdivideHomotopy_identity center n) c

theorem subdivideHomotopy_naturality (other : ∀ n, Vertices W n → W) (f : V → W)
    (hf : ∀ n v, f (center n v) = other n (f ∘ v)) (n : ℕ) :
    (map f (n + 1)).comp (subdivideHomotopy center n) =
      (subdivideHomotopy other n).comp (map f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, subdivideHomotopy_succ_single, one_smul, map_single]
    rw [map_cone]
    simp only [map_sub]
    have hs := DFunLike.congr_fun (subdivide_naturality center other f hf (n + 1)) (Finsupp.single v 1)
    have ht := DFunLike.congr_fun ih (boundary n (Finsupp.single v 1))
    dsimp only [LinearMap.comp_apply] at hs ht
    rw [hs, ht, map_boundary, map_single]
    rfl

end FiniteChains.VertexChains

namespace FiniteChains.VertexChains

universe u
variable {V : Type u}

theorem map_mem_of_supported {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    (S : Set ι) (T : Submodule ℤ M) (L : (ι →₀ ℤ) →ₗ[ℤ] M)
    (hL : ∀ v ∈ S, L (Finsupp.single v 1) ∈ T)
    {c : ι →₀ ℤ} (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c ∈ T := by
  have he : Finsupp.supported ℤ ℤ S ≤ T.comap L := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact hL v hv
  exact he hc

def carried (S : Set V) (n : ℕ) : Submodule ℤ (Chain V n) :=
  Finsupp.supported ℤ ℤ {v | ∀ i, v i ∈ S}

theorem single_mem_carried (S : Set V) {n : ℕ} (v : Vertices V n) (r : ℤ) (hv : ∀ i, v i ∈ S) :
    Finsupp.single v r ∈ carried S n := Finsupp.single_mem_supported ℤ r hv


theorem cone_mem_carried (S : Set V) (p : V) (hp : p ∈ S) (n : ℕ) {c : Chain V n}
    (hc : c ∈ carried S n) : cone p n c ∈ carried S (n + 1) := by
  apply map_mem_of_supported _ _ (cone p n) ?_ hc
  intro v hv
  rw [cone_single]
  apply single_mem_carried
  intro i
  exact Fin.cases hp (fun j => hv j) i

variable (center : ∀ n, Vertices V n → V) (S : Set V)
variable (hcenter : ∀ n v, (∀ i, v i ∈ S) → center n v ∈ S)

include hcenter in
theorem subdivide_mem_carried (n : ℕ) {c : Chain V n} (hc : c ∈ carried S n) :
    subdivide center n c ∈ carried S n := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    apply map_mem_of_supported _ _ (subdivide center (n + 1)) ?_ hc
    intro v hv
    rw [subdivide_succ_single, one_smul]
    apply cone_mem_carried S _ (hcenter _ _ hv)
    apply ih
    exact (by
      apply map_mem_of_supported _ _ (boundary n) ?_ (single_mem_carried S v 1 hv)
      intro v hv
      rw [boundary_single]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      exact single_mem_carried S _ 1 (fun j => hv (i.succAbove j)))

end FiniteChains.VertexChains

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

theorem affineEval_mem_of_vertices {S : Set E} (hS : Convex ℝ S) {n : ℕ}
    (v : Vertices A n) (hv : ∀ i, (v i).val ∈ S) (z : TopologicalSingular.Domain n) :
    (affineEval hA v z).val ∈ S :=
  hS.sum_mem (fun i _ => z.property.1 i) z.property.2 (fun i _ => hv i)



theorem subdivide_vertices_mem_convexHull {n : ℕ} (v : Vertices A n)
    {w : Vertices A n} (hw : w ∈ (subdivide (center hA) n (Finsupp.single v 1)).support) (i : Fin (n + 1)) :
    (w i).val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) := by
  have hc := (subdivide_mem_carried (center hA) _ (fun n v hv => (affineEval_mem_of_vertices hA (convex_convexHull ℝ _) v hv stdSimplex.barycenter)) n (single_mem_carried {x : A | x.val ∈ convexHull ℝ (Set.range (fun j => (v j).val))} v 1
      (fun j => subset_convexHull ℝ _ ⟨j, rfl⟩)))
  exact hc hw i

def shrink (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem shrink_nonneg (n : ℕ) : 0 ≤ shrink n := by unfold shrink; positivity

theorem shrink_lt_one (n : ℕ) : shrink n < 1 := by
  unfold shrink
  exact (div_lt_one (by positivity)).mpr (by linarith)


theorem center_dist_convexHull_le {n : ℕ} (v : Vertices A n) (D : ℝ)
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range (fun j => (v j).val))) :
    dist (center hA n v).val x ≤ shrink n * D := by
  obtain ⟨y, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge hx (center hA n v).val
  rw [dist_comm] at hj
  exact hj.trans (by simpa only [dist_comm] using (show dist (center hA n v).val (v j).val ≤ shrink n * D by
    let a  := ((n + 1 : ℕ) : ℝ)⁻¹
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hsum : ∑ i : Fin (n + 1), a = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, a]
      exact mul_inv_cancel₀ (by positivity)
    have hv : (center hA n v).val - (v j).val = ∑ i, a • ((v i).val - (v j).val) := by
      rw [center_val]
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
      rfl
    have hd : (∑ i : Fin (n + 1), dist (v i).val (v j).val) ≤ n * D := by
      calc
        _ = ∑ i ∈ Finset.univ.erase j, dist (v i).val (v j).val := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), dist_self, add_zero]
        _ ≤ ∑ _i ∈ Finset.univ.erase j, D := Finset.sum_le_sum (fun i _ => hD i j)
        _ = _ := by simp
    rw [dist_eq_norm, hv]
    calc
      _ ≤ ∑ i, ‖a • ((v i).val - (v j).val)‖ := norm_sum_le _ _
      _ = a * ∑ i, dist (v i).val (v j).val := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, ← dist_eq_norm, Finset.mul_sum]
      _ ≤ a * (n * D) := mul_le_mul_of_nonneg_left hd ha
      _ = shrink n * D := by simp only [a, shrink, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]; ring))

theorem affineEval_dist_le {n : ℕ} (v : Vertices A n) (D : ℝ)
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) (z w : TopologicalSingular.Domain n) :
    dist (affineEval hA v z).val (affineEval hA v w).val ≤ D := by
  have hm (t : TopologicalSingular.Domain n) :
      (affineEval hA v t).val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) :=
    affineEval_mem_of_vertices hA (convex_convexHull ℝ (Set.range (fun j => (v j).val))) v
      (fun j => subset_convexHull ℝ _ ⟨j, rfl⟩) t
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hij⟩ := convexHull_exists_dist_ge2 (hm z) (hm w)
  grind

end FiniteChains.AffineVertexChains

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

def MeshBound {n : ℕ} (v : Vertices A n) (D : ℝ) : Prop :=
  ∀ i j, dist (v i).val (v j).val ≤ D

def meshChains (n : ℕ) (D : ℝ) : Submodule ℤ (VertexChains.Chain A n) :=
  Finsupp.supported ℤ ℤ {v | MeshBound v D}


theorem subdivide_single_mem_mesh (n : ℕ) (v : Vertices A n) (D : ℝ) (hD₀ : 0 ≤ D)
    (hD : MeshBound v D) :
    subdivide (center hA) n (Finsupp.single v 1) ∈ meshChains n (shrink n * D) := by
  induction n generalizing D with
  | zero =>
    rw [subdivide_zero]
    refine Finsupp.single_mem_supported ℤ 1 ?_
    intro i j
    have hij : i = j := by ext; omega
    rw [hij, dist_self]
    simp [shrink]
  | succ n ih =>
    rw [subdivide_succ_single, one_smul, VertexChains.boundary_single]
    simp only [map_sum, map_zsmul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply map_mem_of_supported
      {w : Vertices A n | (∀ j, (w j).val ∈ convexHull ℝ (Set.range (fun j => (v j).val))) ∧
        MeshBound w (shrink n * D)} _ (cone (center hA (n + 1) v) n) ?_ ?_
    · intro w hw
      rw [cone_single]
      refine Finsupp.single_mem_supported ℤ 1 ?_
      intro a b
      refine Fin.cases ?_ (fun a => ?_) a
      · refine Fin.cases ?_ (fun b => ?_) b
        · simpa using mul_nonneg (shrink_nonneg (n + 1)) hD₀
        · exact center_dist_convexHull_le hA v D hD (hw.1 b)
      · refine Fin.cases ?_ (fun b => ?_) b
        · rw [dist_comm]
          exact center_dist_convexHull_le hA v D hD (hw.1 a)
        · exact (hw.2 a b).trans (mul_le_mul_of_nonneg_right (by
          simp only [shrink, Nat.cast_add, Nat.cast_one]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith) hD₀)
    · intro w hw
      refine ⟨?_, (ih (face i v) D hD₀ (fun a b => hD (i.succAbove a) (i.succAbove b))) hw⟩
      intro j
      apply convexHull_mono ?_ (subdivide_vertices_mem_convexHull hA (face i v) hw j)
      rintro x ⟨k, rfl⟩
      exact ⟨i.succAbove k, rfl⟩


theorem iterated_subdivide_mem_mesh (k n : ℕ) (D : ℝ) (hD₀ : 0 ≤ D) {c : VertexChains.Chain A n}
    (hc : c ∈ meshChains n D) :
    ((subdivide (center hA) n)^[k]) c ∈ meshChains n ((shrink n) ^ k * D) := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have he := (map_mem_of_supported _ _ (subdivide (center hA) n)
    (fun v hv => subdivide_single_mem_mesh hA n v ((shrink n) ^ k * D) (mul_nonneg (pow_nonneg (shrink_nonneg n) k) hD₀) hv) ih)
    simpa only [pow_succ', mul_assoc] using he

end FiniteChains.AffineVertexChains

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u v
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {A : Set E} {B : Set F} (hA : Convex ℝ A) (hB : Convex ℝ B)

theorem realize_subdivide_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ)
    (c : VertexChains.Chain A n) :
    TopologicalSingular.map (restriction f hf) n (realize hA n (subdivide (center hA) n c)) =
      realize hB n (subdivide (center hB) n (VertexChains.map (restriction f hf) n c)) := by
  rw [realize_naturality hA hB]
  have he := DFunLike.congr_fun
    (subdivide_naturality (center hA) (center hB) (restriction f hf)
      (center_naturality hA hB f hf) n) c
  simp_all

theorem realize_subdivideHomotopy_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ)
    (c : VertexChains.Chain A n) :
    TopologicalSingular.map (restriction f hf) (n + 1)
        (realize hA (n + 1) (subdivideHomotopy (center hA) n c)) =
      realize hB (n + 1) (subdivideHomotopy (center hB) n (VertexChains.map (restriction f hf) n c)) := by
  rw [realize_naturality hA hB]
  have he := DFunLike.congr_fun
    (subdivideHomotopy_naturality (center hA) (center hB) (restriction f hf)
      (center_naturality hA hB f hf) n) c
  simp_all

def standardMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    C(TopologicalSingular.Domain m, TopologicalSingular.Domain n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

def standardLinearMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    (Fin (m + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ⟨FunOnFinite.linearMap ℝ ℝ f, FunOnFinite.continuous_linearMap ℝ ℝ f⟩

theorem standardLinearMap_mapsTo {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    MapsTo (standardLinearMap f) (TopologicalSingular.Domain m) (TopologicalSingular.Domain n) := by
  intro z hz
  exact (stdSimplex.map f ⟨z, hz⟩).property

theorem standardMap_vertices {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    standardMap f ∘ standardVertices m = standardVertices n ∘ f := by
  funext i
  exact stdSimplex.map_vertex f i

theorem realize_standard_subdivide_naturality {d e k : ℕ}
    (f : Fin (d + 1) → Fin (e + 1)) (c : VertexChains.Chain (TopologicalSingular.Domain d) k) :
    TopologicalSingular.map (standardMap f) k
        (realize (convex_stdSimplex ℝ (Fin (d + 1))) k
          (subdivide (center (convex_stdSimplex ℝ (Fin (d + 1)))) k c)) =
      realize (convex_stdSimplex ℝ (Fin (e + 1))) k
        (subdivide (center (convex_stdSimplex ℝ (Fin (e + 1)))) k
          (VertexChains.map (standardMap f) k c)) :=
  realize_subdivide_naturality _ _ (standardLinearMap f) (standardLinearMap_mapsTo f) k c

theorem realize_standard_homotopy_naturality {d e k : ℕ}
    (f : Fin (d + 1) → Fin (e + 1)) (c : VertexChains.Chain (TopologicalSingular.Domain d) k) :
    TopologicalSingular.map (standardMap f) (k + 1)
        (realize (convex_stdSimplex ℝ (Fin (d + 1))) (k + 1)
          (subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (d + 1)))) k c)) =
      realize (convex_stdSimplex ℝ (Fin (e + 1))) (k + 1)
        (subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (e + 1)))) k
          (VertexChains.map (standardMap f) k c)) :=
  realize_subdivideHomotopy_naturality _ _ (standardLinearMap f) (standardLinearMap_mapsTo f) k c

end FiniteChains.AffineVertexChains

namespace FiniteChains.SingularSubdivision

open AffineVertexChains

def generator (n : ℕ) : VertexChains.Chain (TopologicalSingular.Domain n) n :=
  Finsupp.single (standardVertices n) 1

def model (n : ℕ) : TopologicalSingular.Chain (TopologicalSingular.Domain n) n :=
  realize (convex_stdSimplex ℝ (Fin (n + 1))) n
    (VertexChains.subdivide (center (convex_stdSimplex ℝ (Fin (n + 1)))) n (generator n))

def homotopyModel (n : ℕ) : TopologicalSingular.Chain (TopologicalSingular.Domain n) (n + 1) :=
  realize (convex_stdSimplex ℝ (Fin (n + 1))) (n + 1)
    (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (n + 1)))) n (generator n))

theorem boundary_model (n : ℕ) :
    TopologicalSingular.boundary n (model (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) n (model n) := by
  rw [model, ← realize_boundary, ← VertexChains.subdivide_boundary, generator,
    VertexChains.boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (by
    simpa only [VertexChains.map_single, standardMap_vertices, VertexChains.face, model, generator]
      using (realize_standard_subdivide_naturality i.succAbove
        (Finsupp.single (standardVertices n) 1)).symm)


theorem homotopyModel_identity (n : ℕ) :
    TopologicalSingular.boundary (n + 1) (homotopyModel (n + 1)) +
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) (n + 1) (homotopyModel n)) =
      model (n + 1) - Finsupp.single (ContinuousMap.id (TopologicalSingular.Domain (n + 1))) 1 := by
  have he := congrArg (realize (convex_stdSimplex ℝ (Fin (n + 2))) (n + 1))
    (VertexChains.subdivideHomotopy_identity_succ
      (center (convex_stdSimplex ℝ (Fin (n + 2)))) n (generator (n + 1)))
  rw [map_add, map_sub, realize_boundary, (show realize (convex_stdSimplex ℝ (Fin (n + 2))) (n + 1)
        (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (n + 2)))) n
          (VertexChains.boundary n (generator (n + 1)))) =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) (n + 1) (homotopyModel n) by
    rw [generator, VertexChains.boundary_single]
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (by
      simpa only [VertexChains.map_single, standardMap_vertices, VertexChains.face, homotopyModel, generator]
        using (realize_standard_homotopy_naturality i.succAbove
          (Finsupp.single (standardVertices n) 1)).symm))] at he
  simpa only [homotopyModel, model, generator, realize_single, affineEval_standardVertices] using he

end FiniteChains.SingularSubdivision

namespace FiniteChains.SingularSubdivision

open TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def fromModel {k l : ℕ} (m : Chain (Domain k) l) : Chain X k →ₗ[ℤ] Chain X l :=
  Finsupp.linearCombination ℤ (fun σ : Simplex X k => TopologicalSingular.map σ l m)

theorem fromModel_single {k l : ℕ} (m : Chain (Domain k) l) (σ : Simplex X k) (r : ℤ) :
    fromModel m (Finsupp.single σ r) = r • TopologicalSingular.map σ l m :=
  Finsupp.linearCombination_single ℤ r σ

theorem fromModel_naturality {k l : ℕ} (m : Chain (Domain k) l) (f : C(X, Y)) (c : Chain X k) :
    TopologicalSingular.map f l (fromModel m c) = fromModel m (TopologicalSingular.map f k c) := by
  have he : (TopologicalSingular.map f l).comp (fromModel m) =
      (fromModel m).comp (TopologicalSingular.map f k) := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp only [LinearMap.comp_apply, fromModel_single, one_smul, map_single]
    exact (DFunLike.congr_fun (map_comp σ f l) m).symm
  exact DFunLike.congr_fun he c

def subdivide (n : ℕ) : Chain X n →ₗ[ℤ] Chain X n := fromModel (model n)

def homotopy (n : ℕ) : Chain X n →ₗ[ℤ] Chain X (n + 1) := fromModel (homotopyModel n)

theorem subdivide_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    subdivide n (Finsupp.single σ r) = r • TopologicalSingular.map σ n (model n) := fromModel_single _ _ _

theorem homotopy_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    homotopy n (Finsupp.single σ r) = r • TopologicalSingular.map σ (n + 1) (homotopyModel n) :=
  fromModel_single _ _ _

theorem push_face {n k : ℕ} (σ : Simplex X (n + 1)) (i : Fin (n + 2)) (c : Chain (Domain n) k) :
    TopologicalSingular.map σ k (TopologicalSingular.map (standardMap i.succAbove) k c) =
      TopologicalSingular.map (face i σ) k c :=
  (DFunLike.congr_fun (map_comp (standardMap i.succAbove) σ k) c).symm

theorem subdivide_boundary (n : ℕ) (c : Chain X (n + 1)) :
    subdivide n (boundary n c) = boundary n (subdivide (n + 1) c) := by
  have he : (subdivide n).comp (boundary n) = (boundary n).comp (subdivide (X := X) (n + 1)) := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp only [LinearMap.comp_apply, boundary_single, map_sum, map_zsmul, subdivide_single, one_smul]
    rw [← map_boundary, boundary_model]
    simp only [map_sum, map_zsmul, push_face]
  exact DFunLike.congr_fun he c

theorem homotopy_identity_succ (n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (homotopy (n + 1) c) + homotopy n (boundary n c) = subdivide (n + 1) c - c := by
  have he : (boundary (n + 1)).comp (homotopy (X := X) (n + 1)) +
      (homotopy n).comp (boundary n) = subdivide (n + 1) - LinearMap.id := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    have hm := congrArg (TopologicalSingular.map σ (n + 1)) (homotopyModel_identity n)
    simp only [map_add, map_sub, map_sum, map_zsmul, map_boundary, push_face, map_single] at hm
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      simplexMap, ContinuousMap.comp_id, homotopy_single, subdivide_single, boundary_single, map_sum, map_zsmul, one_smul] using hm
  exact DFunLike.congr_fun he c

theorem subdivide_naturality (f : C(X, Y)) (n : ℕ) (c : Chain X n) :
    TopologicalSingular.map f n (subdivide n c) = subdivide n (TopologicalSingular.map f n c) :=
  fromModel_naturality (model n) f c

end FiniteChains.SingularSubdivision

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

def simplexLinearMap {n : ℕ} (v : Vertices A n) : (Fin (n + 1) → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i).val

theorem simplexLinearMap_apply {n : ℕ} (v : Vertices A n) (z : Fin (n + 1) → ℝ) :
    simplexLinearMap v z = ∑ i, z i • (v i).val := by
  simp [simplexLinearMap]

include hA in
theorem simplexLinearMap_mapsTo {n : ℕ} (v : Vertices A n) :
    MapsTo (simplexLinearMap v) (TopologicalSingular.Domain n) A := by
  intro z hz
  rw [simplexLinearMap_apply]
  exact (affineEval hA v ⟨z, hz⟩).property




theorem subdivide_realize (n : ℕ) (c : VertexChains.Chain A n) :
    SingularSubdivision.subdivide n (realize hA n c) = realize hA n (subdivide (center hA) n c) := by
  have he : (SingularSubdivision.subdivide n).comp (realize hA n) =
      (realize hA n).comp (subdivide (center hA) n) := by
    apply VertexChains.linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, realize_single, SingularSubdivision.subdivide_single, one_smul]
    have hn := realize_subdivide_naturality (convex_stdSimplex ℝ (Fin (n + 1))) hA
      (simplexLinearMap v) (simplexLinearMap_mapsTo hA v) n (Finsupp.single (standardVertices n) 1)
    rw [(show restriction (simplexLinearMap v) (simplexLinearMap_mapsTo hA v) = affineEval hA v by
      apply ContinuousMap.ext
      intro z
      ext
      exact simplexLinearMap_apply v z.val), VertexChains.map_single, (show affineEval hA v ∘ standardVertices n = v by
      funext i
      exact (show affineEval hA v (stdSimplex.vertex i) = v i by
        ext
        simp [affineEval, Pi.single_apply]))] at hn
    exact hn
  exact DFunLike.congr_fun he c

theorem iterated_subdivide_realize (k n : ℕ) (c : VertexChains.Chain A n) :
    ((SingularSubdivision.subdivide n)^[k]) (realize hA n c) =
      realize hA n (((subdivide (center hA) n)^[k]) c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, subdivide_realize]

end FiniteChains.AffineVertexChains

namespace FiniteChains.SingularSubdivision

open TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem iterated_subdivide_naturality (f : C(X, Y)) (k n : ℕ) (c : Chain X n) :
    TopologicalSingular.map f n (((subdivide n)^[k]) c) =
      ((subdivide n)^[k]) (TopologicalSingular.map f n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, subdivide_naturality]

theorem iterated_subdivide_single_model (k n : ℕ) (σ : Simplex X n) :
    ((subdivide n)^[k]) (Finsupp.single σ 1) =
      TopologicalSingular.map σ n
        (realize (convex_stdSimplex ℝ (Fin (n + 1))) n
          (((VertexChains.subdivide (center (convex_stdSimplex ℝ (Fin (n + 1)))) n)^[k]) (generator n))) := by
  have hg : Finsupp.single σ 1 =
      TopologicalSingular.map σ n (realize (convex_stdSimplex ℝ (Fin (n + 1))) n (generator n)) := by
    rw [generator, realize_single, affineEval_standardVertices, map_single]
    rfl
  conv_lhs => rw [hg]
  rw [← iterated_subdivide_naturality, iterated_subdivide_realize]

end FiniteChains.SingularSubdivision

namespace FiniteChains.SingularSubdivision

open Set Topology TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

def smallChains (U : ι → Set X) (n : ℕ) : Submodule ℤ (Chain X n) :=
  Finsupp.supported ℤ ℤ {σ | ∃ i, ∀ z, σ z ∈ U i}

theorem single_mem_small (U : ι → Set X) (n : ℕ) (σ : Simplex X n) (r : ℤ)
    (hσ : ∃ i, ∀ z, σ z ∈ U i) : Finsupp.single σ r ∈ smallChains U n :=
  Finsupp.single_mem_supported ℤ r hσ

theorem boundary_mem_small (U : ι → Set X) (n : ℕ) {c : Chain X (n + 1)}
    (hc : c ∈ smallChains U (n + 1)) : boundary n c ∈ smallChains U n := by
  apply VertexChains.map_mem_of_supported _ _ (boundary n) ?_ hc
  rintro σ ⟨j, hj⟩
  rw [boundary_single]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact single_mem_small U n _ 1 ⟨j, fun z => hj _⟩


theorem fromModel_mem_small (U : ι → Set X) {k l : ℕ} (m : Chain (Domain k) l)
    {c : Chain X k} (hc : c ∈ smallChains U k) : fromModel m c ∈ smallChains U l := by
  apply VertexChains.map_mem_of_supported _ _ (fromModel m) ?_ hc
  intro σ hσ
  rw [fromModel_single, one_smul]
  exact (by
    obtain ⟨j, hj⟩ := hσ
    induction m using Finsupp.induction with
    | zero => simp
    | single_add τ r m _ _ ih =>
      rw [map_add, map_single]
      exact Submodule.add_mem _ (single_mem_small U l _ r ⟨j, fun z => hj (τ z)⟩) ih)


theorem homotopy_mem_small (U : ι → Set X) (n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : homotopy n c ∈ smallChains U (n + 1) :=
  fromModel_mem_small U (homotopyModel n) hc

theorem iterated_subdivide_mem_small (U : ι → Set X) (k n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : ((subdivide n)^[k]) c ∈ smallChains U n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (fromModel_mem_small U (model n) ih)

theorem iterated_subdivide_small_of_le (U : ι → Set X) {k l : ℕ} (hkl : k ≤ l)
    (n : ℕ) {c : Chain X n} (hc : ((subdivide n)^[k]) c ∈ smallChains U n) :
    ((subdivide n)^[l]) c ∈ smallChains U n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [Nat.add_comm k a, Function.iterate_add_apply]
  exact iterated_subdivide_mem_small U a n hc



theorem exists_subdivision_small (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X n) :
    ∃ k, ((subdivide n)^[k]) c ∈ smallChains U n := by
  choose K hK using fun σ => (show ∃ k, ((subdivide n)^[k]) (Finsupp.single σ 1) ∈ smallChains U n by
    obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
      isCompact_univ
      (fun i => (hU i).preimage σ.continuous)
      (by
        intro z _
        obtain ⟨i, hi⟩ := (fun z => hcover (σ z)) z
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (shrink_lt_one n)
    refine ⟨k, ?_⟩
    rw [iterated_subdivide_single_model]
    apply VertexChains.map_mem_of_supported {v | MeshBound v ((shrink n) ^ k * 1)} (smallChains U n)
      ((TopologicalSingular.map σ n).comp (realize (convex_stdSimplex ℝ (Fin (n + 1))) n)) ?_ ?_
    · intro v hv
      rw [LinearMap.comp_apply, realize_single, map_single]
      obtain ⟨i, hi⟩ := hball (affineEval (convex_stdSimplex ℝ (Fin (n + 1))) v (stdSimplex.vertex 0))
        (Set.mem_univ _)
      apply single_mem_small
      refine ⟨i, fun z => hi ?_⟩
      exact (affineEval_dist_le _ v _ hv z (stdSimplex.vertex 0)).trans_lt (by simpa using hk)
    · exact iterated_subdivide_mem_mesh (convex_stdSimplex ℝ (Fin (n + 1))) k n 1 zero_le_one
        (Finsupp.single_mem_supported ℤ 1 (by
          intro i j
          exact (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (n + 1)))
            (standardVertices n i).property (standardVertices n j).property).trans diam_stdSimplex_le)))
  let N := c.support.sup K
  refine ⟨N, ?_⟩
  rw [← Module.End.pow_apply]
  apply VertexChains.map_mem_of_supported c.support (smallChains U n)
    ((subdivide n) ^ N) ?_ (fun _ h => h)
  intro σ hσ
  rw [Module.End.pow_apply]
  exact iterated_subdivide_small_of_le U (Finset.le_sup hσ) n (hK σ)

end FiniteChains.SingularSubdivision

namespace FiniteChains.SingularSubdivision

open Set Topology TopologicalSingular

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}


theorem iterated_subdivide_boundary (k n : ℕ) (c : Chain X (n + 1)) :
    ((subdivide n)^[k]) (boundary n c) = boundary n (((subdivide (n + 1))^[k]) c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, subdivide_boundary]

def iteratedHomotopy (n : ℕ) : ℕ → Chain X n →ₗ[ℤ] Chain X (n + 1)
  | 0 => 0
  | k + 1 => (homotopy n).comp ((subdivide n) ^ k) + iteratedHomotopy n k

theorem iteratedHomotopy_zero (n : ℕ) (c : Chain X n) : iteratedHomotopy n 0 c = 0 := rfl

theorem iteratedHomotopy_succ (n k : ℕ) (c : Chain X n) :
    iteratedHomotopy n (k + 1) c = homotopy n (((subdivide n)^[k]) c) + iteratedHomotopy n k c := by simp_all [iteratedHomotopy, LinearMap.add_apply, LinearMap.comp_apply, Module.End.pow_apply]

theorem iteratedHomotopy_identity_succ (k n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (iteratedHomotopy (n + 1) k c) + iteratedHomotopy n k (boundary n c) =
      ((subdivide (n + 1))^[k]) c - c := by
  induction k with
  | zero => simp only [iteratedHomotopy_zero, map_zero, add_zero, Function.iterate_zero_apply, sub_self]
  | succ k ih =>
    rw [iteratedHomotopy_succ, iteratedHomotopy_succ, map_add, iterated_subdivide_boundary]
    calc
      _ = (boundary (n + 1) (homotopy (n + 1) (((subdivide (n + 1))^[k]) c)) +
            homotopy n (boundary n (((subdivide (n + 1))^[k]) c))) +
          (boundary (n + 1) (iteratedHomotopy (n + 1) k c) +
            iteratedHomotopy n k (boundary n c)) := by abel
      _ = (subdivide (n + 1) (((subdivide (n + 1))^[k]) c) - ((subdivide (n + 1))^[k]) c) +
          (((subdivide (n + 1))^[k]) c - c) := by rw [homotopy_identity_succ, ih]
      _ = _ := by rw [Function.iterate_succ_apply']; abel

theorem iteratedHomotopy_mem_small (U : ι → Set X) (k n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : iteratedHomotopy n k c ∈ smallChains U (n + 1) := by
  induction k with
  | zero => rw [iteratedHomotopy_zero]; exact Submodule.zero_mem _
  | succ k ih =>
    rw [iteratedHomotopy_succ]
    exact Submodule.add_mem _ (homotopy_mem_small U n (iterated_subdivide_mem_small U k n hc)) ih

variable (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)

include hU hcover in
theorem exists_small_cycle_representative (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    ∃ d : Chain X (n + 1), d ∈ smallChains U (n + 1) ∧ boundary n d = 0 ∧
      d - c ∈ LinearMap.range (boundary (n + 1)) := by
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover (n + 1) c
  refine ⟨_, hk, ?_, iteratedHomotopy (n + 1) k c, ?_⟩
  · rw [← iterated_subdivide_boundary, hc, (show ((subdivide n)^[k]) 0 = 0 by
    simp)]
  · simpa only [hc, map_zero, add_zero] using iteratedHomotopy_identity_succ k n c

end FiniteChains.SingularSubdivision

namespace FiniteChains.SingularSubdivision

open CategoryTheory CategoryTheory.Limits TopologicalSingular Set

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

def smallBoundary (U : ι → Set X) (n : ℕ) :
    smallChains U (n + 1) →ₗ[ℤ] smallChains U n :=
  ((boundary n).comp (smallChains U (n + 1)).subtype).codRestrict _
    (fun c => boundary_mem_small U n c.property)

theorem smallBoundary_squared (U : ι → Set X) (n : ℕ) :
    (smallBoundary U n).comp (smallBoundary U (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact boundary_boundary n c.val

end FiniteChains.SingularSubdivision

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision

/-- Every positive-dimensional singular cycle is homologous to one whose
individual simplices each lie in an open vertex star. -/
theorem orderNerveRealization_exists_small_cycle (P : Type) [PartialOrder P]
    (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0) :
    ∃ d : Chain (orderNerveRealization P) (n + 1),
      d ∈ smallChains (orderNerveRealizationOpenStar P) (n + 1) ∧
      boundary n d = 0 ∧ d - c ∈ LinearMap.range (boundary (n + 1)) :=
  exists_small_cycle_representative (orderNerveRealizationOpenStar P)
    (orderNerveRealizationOpenStar_isOpen P) (orderNerveRealizationOpenStar_cover P) n c hc

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Opposite AlgebraicTopology
open TopologicalSingular
open scoped Simplicial


/-- The actual continuous singular simplex associated with an order simplex. -/
def orderNerveSingularSimplex {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (op ⦋n⦌)) :
    Simplex (orderNerveRealization P) n :=
  (simplicesMathlibIso (orderNerveRealization P)).inv.app (op ⦋n⦌)
    ((orderNerveRealizationUnit P).app (op ⦋n⦌) s)

theorem orderNerveSingularSimplex_apply {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (op ⦋n⦌)) (z : Domain n) :
    orderNerveSingularSimplex s z = orderNerveRealizationSimplex P s (ULift.up ((simplexCoordinates n).symm z)) := rfl

theorem orderNerveSingularSimplex_face {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (op ⦋n + 1⦌)) (i : Fin (n + 2)) :
    face i (orderNerveSingularSimplex s) = orderNerveSingularSimplex ((nerve P).δ i s) := by
  apply ContinuousMap.ext
  intro z
  erw [face_apply, orderNerveSingularSimplex_apply, orderNerveSingularSimplex_apply]
  have h := congrArg (fun f => f (ULift.up ((simplexCoordinates n).symm z)))
    (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s)
  change orderNerveRealizationSimplex P s
    (ULift.up (Convexity.StdSimplex.map (SimplexCategory.δ i) ((simplexCoordinates n).symm z))) = _ at h
  have he : Convexity.StdSimplex.map (SimplexCategory.δ i) ((simplexCoordinates n).symm z) =
      (simplexCoordinates (n + 1)).symm (stdSimplex.map (SimplexCategory.δ i) z) := by
    apply (simplexCoordinates (n + 1)).injective
    rw [simplexCoordinates_map, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  rw [he] at h
  exact h

theorem orderNerveSingularSimplex_supported {P : Type} [PartialOrder P]
    {n : ℕ} (A : Set P) (s : (nerve P).obj (op ⦋n⦌))
    (hs : ∀ i, s.obj i ∈ A) (z : Domain n) :
    orderNerveSingularSimplex s z ∈ (orderNerveRealizationSubcomplex P A :
      Set (orderNerveRealization P)) := by
  erw [orderNerveSingularSimplex_apply]
  exact orderNerveRealizationSimplex_supported A s hs ⟨ULift.up ((simplexCoordinates n).symm z), rfl⟩

/-- The canonical chain comparison, with explicit continuous simplices as basis. -/
def orderNerveExplicitSingularMap (P : Type) [PartialOrder P] :
    AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶ complex (orderNerveRealization P) :=
  orderNerveRealizationChainComparison P ≫ (freeComplexMathlibIso (orderNerveRealization P)).inv

theorem orderNerveExplicitSingularMap_single {P : Type} [PartialOrder P]
    (n : ℕ) (s : (nerve P).obj (op ⦋n⦌)) (r : ℤ) :
    (orderNerveExplicitSingularMap P).f n (Finsupp.single s r) =
      Finsupp.single (orderNerveSingularSimplex s) r := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single s r)) = _
  simp
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- The vertices with positive coordinates at a realization point form a
finite chain. This remains true in an infinite, non-locally-finite realization. -/
theorem orderNerveRealization_activeVertices_finite_chain {P : Type} [PartialOrder P]
    (x : orderNerveRealization P) :
    {v | x ∈ orderNerveRealizationOpenStar P v}.Finite ∧
      IsChain (· ≤ ·) {v | x ∈ orderNerveRealizationOpenStar P v} := by
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  have hs : {v | x ∈ orderNerveRealizationOpenStar P v} = Set.range s.val.obj := by
    ext v
    rw [← he]
    exact orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v
  rw [hs]
  refine ⟨Set.finite_range s.val.obj, ?_⟩
  rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ _
  rcases le_total i j with hij | hij
  · exact Or.inl (leOfHom (s.val.map (homOfLE hij)))
  · exact Or.inr (leOfHom (s.val.map (homOfLE hij)))

/-- All open vertex stars that contain the entire singular simplex. -/
def orderNerveSingularStarIndices {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) : Set P :=
  {v | ∀ z, σ z ∈ orderNerveRealizationOpenStar P v}

theorem orderNerveSingularStarIndices_chain {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) :
    IsChain (· ≤ ·) (orderNerveSingularStarIndices σ) :=
  (orderNerveRealization_activeVertices_finite_chain (σ (stdSimplex.vertex 0))).2.mono
    (fun _ h => h (stdSimplex.vertex 0))

/-- Every star containing a simplex also contains each of its faces. -/
theorem orderNerveSingularStarIndices_face {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) (n + 1))
    (i : Fin (n + 2)) :
    orderNerveSingularStarIndices σ ⊆
      orderNerveSingularStarIndices (TopologicalSingular.face i σ) := by
  intro v hv z
  exact hv _

/-- The common closed-star subposet of every star containing a singular simplex.
Taking all such stars makes this carrier monotone under passage to faces. -/
def orderNerveSingularCarrier {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) : Set P :=
  {p | ∀ v ∈ orderNerveSingularStarIndices σ, p ≤ v ∨ v ≤ p}

theorem orderNerveSingularCarrier_face {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) (n + 1))
    (i : Fin (n + 2)) :
    orderNerveSingularCarrier (TopologicalSingular.face i σ) ⊆ orderNerveSingularCarrier σ := by
  intro p hp v hv
  exact hp v (orderNerveSingularStarIndices_face σ i hv)

theorem orderNerveSingularStarIndices_subset_carrier {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) :
    orderNerveSingularStarIndices σ ⊆ orderNerveSingularCarrier σ := by
  intro p hp v hv
  exact (orderNerveSingularStarIndices_chain σ).total hp hv

/-- The whole singular simplex lies in its genuine supported CW carrier. -/
theorem orderNerveSingularSimplex_mem_carrier {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)
    (z : TopologicalSingular.Domain n) :
    σ z ∈ (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
      Set (orderNerveRealization P)) := by
  intro p hp
  by_contra he
  apply hp
  intro v hv
  by_contra hcomp
  exact he (orderNerveRealizationOpenStar_subset_subcomplex v (hv z) p hcomp)

/-- The carrier of a star-small simplex has a universally comparable vertex,
so its order realization is contractible. -/

theorem orderNerveSingularCarrier_subcomplex_contractible {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) :
    ContractibleSpace (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
      Set (orderNerveRealization P)) := by
  letI := (show ContractibleSpace (orderNerveRealization (orderNerveSingularCarrier σ)) by
    obtain ⟨v, hv⟩ := hσ
    let a : orderNerveSingularCarrier σ :=
      ⟨v, orderNerveSingularStarIndices_subset_carrier σ hv⟩
    exact orderNerveRealization_contractible_of_comparable a (fun p => p.property v hv))
  exact (orderNerveRealizationSubtypeHomeomorph (orderNerveSingularCarrier σ)).symm.contractibleSpace

end FiniteChains.Comb

namespace FiniteChains.Comb
open scoped Classical

/-- The lower of a vertex and a fixed comparable center. -/
def orderComparableLower {P : Type*} [PartialOrder P] (v p : P) : P :=
  if p ≤ v then p else v


theorem orderComparableLower_le_center {P : Type*} [PartialOrder P] (v p : P) :
    orderComparableLower v p ≤ v := by grind [orderComparableLower]

theorem orderComparableLower_le_self {P : Type*} [PartialOrder P] (v : P)
    (hv : ∀ p, p ≤ v ∨ v ≤ p) (p : P) : orderComparableLower v p ≤ p := by grind [orderComparableLower]

/-- A universally comparable vertex gives explicit augmented nerve fillings
in every degree via the already proved prism contraction. -/
theorem orderNerve_cycle_bounds_of_comparable {P : Type*} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p)
    {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) (hcycle : Nerve.bdry c = 0) :
    ∃ b ∈ Nerve.Inc P, Nerve.bdry b = c :=
  Nerve.exists_bdry_eq_of_cycle (orderComparableLower v) v
    (by
      intro a b hab
      by_cases ha : a ≤ v
      · by_cases hb : b ≤ v
        · simpa [orderComparableLower, ha, hb] using hab
        · simp [orderComparableLower, ha, hb]
      · have hb : ¬ b ≤ v := fun h => ha (hab.trans h)
        simp [orderComparableLower, ha, hb]) (orderComparableLower_le_self v hv)
    (orderComparableLower_le_center v) hc hcycle

/-- The carrier used for a small singular simplex is also acyclic on the
combinatorial side. Both exactness statements are proved independently. -/
theorem orderNerveSingularCarrier_nerve_acyclic {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) :
    Nerve.AcyclicIn (orderNerveSingularCarrier σ) := by
  obtain ⟨v, hv⟩ := hσ
  have hv' := orderNerveSingularStarIndices_subset_carrier σ hv
  apply Nerve.acyclicIn_of_subtype (orderNerveSingularCarrier σ) ⟨v, hv'⟩
  intro c hc hcycle
  exact orderNerve_cycle_bounds_of_comparable
    ⟨v, hv'⟩ (fun p => p.property v hv) hc hcycle

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

/-- Singular simplices whose whole image is contained in an open vertex star. -/
abbrev OrderSmallSimplex (P : Type) [PartialOrder P] (n : ℕ) :=
  {σ : TopologicalSingular.Simplex (orderNerveRealization P) n //
    (orderNerveSingularStarIndices σ).Nonempty}

/-- The small-chain submodule is genuinely free on the small singular simplices. -/
def orderSmallChainEquiv (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n ≃ₗ[ℤ] (OrderSmallSimplex P n →₀ ℤ) :=
  Finsupp.supportedEquivFinsupp _

def orderSmallSimplexFace {P : Type} [PartialOrder P] {n : ℕ}
    (i : Fin (n + 2)) (σ : OrderSmallSimplex P (n + 1)) : OrderSmallSimplex P n :=
  ⟨TopologicalSingular.face i σ.val, by
    obtain ⟨v, hv⟩ := σ.property
    exact ⟨v, orderNerveSingularStarIndices_face σ.val i hv⟩⟩

def orderSmallSingle {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) (r : ℤ) : smallChains (orderNerveRealizationOpenStar P) n :=
  ⟨Finsupp.single σ.val r, Finsupp.single_mem_supported ℤ r σ.property⟩

theorem orderSmallChainEquiv_symm_single {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) (r : ℤ) :
    (orderSmallChainEquiv P n).symm (Finsupp.single σ r) = orderSmallSingle σ r := by
  apply Subtype.ext
  exact Finsupp.supportedEquivFinsupp_symm_single _ σ r

/-- The free small-chain basis has the actual alternating singular differential. -/
theorem orderSmallSingle_boundary {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P (n + 1)) (r : ℤ) :
    smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ r) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • orderSmallSingle (orderSmallSimplexFace i σ) r := by
  apply Subtype.ext
  change TopologicalSingular.boundary n (Finsupp.single σ.val r) = _
  simp only [TopologicalSingular.boundary_single, Submodule.coe_sum, Submodule.coe_smul]
  rfl

theorem orderSmallSingle_spans {P : Type} [PartialOrder P] {n : ℕ}
    {M : Type*} [AddCommMonoid M] [Module ℤ M]
    (f g : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] M)
    (h : ∀ σ : OrderSmallSimplex P n, f (orderSmallSingle σ 1) = g (orderSmallSingle σ 1)) :
    f = g := by
  apply LinearMap.ext
  intro c
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  have he : f.comp (orderSmallChainEquiv P n).symm.toLinearMap =
      g.comp (orderSmallChainEquiv P n).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro σ r
    have hs : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hs, map_smul, map_smul]
    congr 1
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, orderSmallChainEquiv_symm_single] using h σ
  exact DFunLike.congr_fun he d

/-- The basis carriers decrease along every face. -/
theorem orderSmallSimplexFace_carrier {P : Type} [PartialOrder P] {n : ℕ}
    (i : Fin (n + 2)) (σ : OrderSmallSimplex P (n + 1)) :
    orderNerveSingularCarrier (orderSmallSimplexFace i σ).val ⊆ orderNerveSingularCarrier σ.val :=
  orderNerveSingularCarrier_face σ.val i

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

def orderSmallChosenVertex {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) : P := σ.property.choose

theorem orderSmallChosenVertex_mem {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) :
    orderSmallChosenVertex σ ∈ orderNerveSingularCarrier σ.val :=
  orderNerveSingularStarIndices_subset_carrier σ.val σ.property.choose_spec

/-- The comparison begins by choosing a vertex of a star containing each point. -/
def orderSmallToNerve0 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ (fun σ : OrderSmallSimplex P 0 =>
    FreeAbelianGroup.of [orderSmallChosenVertex σ])).comp (orderSmallChainEquiv P 0).toLinearMap

theorem orderSmallToNerve0_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) (r : ℤ) :
    orderSmallToNerve0 (orderSmallSingle σ r) = r • FreeAbelianGroup.of [orderSmallChosenVertex σ] := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallToNerve0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

theorem orderSmallToNerve0_single_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) :
    orderSmallToNerve0 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallToNerve0_single, one_smul]
  apply Nerve.of_mem_incOn (by simp)
  intro p hp
  have hp' : p = orderSmallChosenVertex σ := by simpa using hp
  rw [hp']
  exact orderSmallChosenVertex_mem σ

theorem orderSmallToNerve0_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    Nerve.lengthProjection 1 (orderSmallToNerve0 c) = orderSmallToNerve0 c := by
  have he : (Nerve.lengthProjection 1).toIntLinearMap.comp orderSmallToNerve0 =
      (orderSmallToNerve0 : smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp [orderSmallToNerve0_single]
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve0_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    Nerve.bdry (orderSmallToNerve0 c) = augmentation c.val • FreeAbelianGroup.of ([] : List P) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve0 =
      (augmentation.comp (smallChains (orderNerveRealizationOpenStar P) 0).subtype).smulRight
        (FreeAbelianGroup.of []) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderSmallToNerve0 (orderSmallSingle σ 1)) =
      augmentation (Finsupp.single σ.val 1) • FreeAbelianGroup.of []
    rw [orderSmallToNerve0_single, one_smul, augmentation_single, one_smul, Nerve.bdry_of]
    simp [Nerve.bdryOn]
  exact DFunLike.congr_fun he c

/-- Each small one-simplex has an actual nerve filling of its already assigned
endpoint boundary, supported in its own carrier. -/
theorem orderSmallOneFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection 2 b = b ∧ Nerve.bdry b =
        orderSmallToNerve0 (smallBoundary (orderNerveRealizationOpenStar P) 0 (orderSmallSingle σ 1)) := by
  let c := orderSmallToNerve0
    (smallBoundary (orderNerveRealizationOpenStar P) 0 (orderSmallSingle σ 1))
  have hc : c ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
    dsimp only [c]
    rw [orderSmallSingle_boundary, map_sum]
    apply AddSubgroup.sum_mem
    intro i _
    rw [map_zsmul]
    apply AddSubgroup.zsmul_mem
    exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
      (orderSmallToNerve0_single_carrier (orderSmallSimplexFace i σ))
  have hcycle : Nerve.bdry c = 0 := by
    rw [orderSmallToNerve0_boundary]
    change augmentation (boundary 0 (Finsupp.single σ.val 1)) • _ = 0
    rw [augmentation_boundary, zero_smul]
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property c hc hcycle
  refine ⟨Nerve.lengthProjection 2 b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact orderSmallToNerve0_length _

def orderSmallOneFill {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) : Nerve.Ch P := (orderSmallOneFill_exists σ).choose

def orderSmallToNerve1 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ orderSmallOneFill).comp (orderSmallChainEquiv P 1).toLinearMap

theorem orderSmallToNerve1_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) (r : ℤ) :
    orderSmallToNerve1 (orderSmallSingle σ r) = r • orderSmallOneFill σ := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallToNerve1, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

/-- The constructed low-degree map commutes with the actual singular differential. -/
theorem orderSmallToNerve1_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    Nerve.bdry (orderSmallToNerve1 c) =
      orderSmallToNerve0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve1 =
      orderSmallToNerve0.comp (smallBoundary (orderNerveRealizationOpenStar P) 0) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve1_single, one_smul]
    exact (orderSmallOneFill_exists σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- The data needed to extend a carried approximation by one degree. -/
structure OrderSmallNerveStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 1) (map c) = map c
  closed_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    Nerve.bdry (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) = 0

def orderSmallNerveStageZero : OrderSmallNerveStage P 0 where
  map := orderSmallToNerve0
  carrier := orderSmallToNerve0_single_carrier
  homogeneous := orderSmallToNerve0_length
  closed_boundary c := by
    rw [orderSmallToNerve0_boundary]
    change augmentation (boundary 0 c.val) • _ = 0
    rw [augmentation_boundary, zero_smul]


/-- Every new simplex can be filled in its own acyclic order carrier. -/
theorem orderSmallNerveStage_fill {n : ℕ} (s : OrderSmallNerveStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b =
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property _
    (by
      rw [orderSmallSingle_boundary, map_sum]
      apply AddSubgroup.sum_mem
      intro i _
      rw [map_smul]
      apply AddSubgroup.zsmul_mem
      exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
        ((s.carrier) (orderSmallSimplexFace i σ))) (s.closed_boundary _)
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact s.homogeneous _

def orderSmallNerveStageNextMap {n : ℕ} (s : OrderSmallNerveStage P n) :
    smallChains (orderNerveRealizationOpenStar P) (n + 1) →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallNerveStage_fill s σ).choose)).comp
    (orderSmallChainEquiv P (n + 1)).toLinearMap

theorem orderSmallNerveStageNextMap_single {n : ℕ} (s : OrderSmallNerveStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    orderSmallNerveStageNextMap s (orderSmallSingle σ 1) =
      (orderSmallNerveStage_fill s σ).choose := by
  have he := (orderSmallChainEquiv P (n + 1)).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P (n + 1) =>
    (orderSmallNerveStage_fill s τ).choose))
      ((orderSmallChainEquiv P (n + 1)) (orderSmallSingle σ 1)) = _
  simp_all

theorem orderSmallNerveStageNextMap_boundary {n : ℕ} (s : OrderSmallNerveStage P n)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    Nerve.bdry (orderSmallNerveStageNextMap s c) =
      s.map (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  have he : Nerve.bdry.toIntLinearMap.comp (orderSmallNerveStageNextMap s) =
      s.map.comp (smallBoundary (orderNerveRealizationOpenStar P) n) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderSmallNerveStageNextMap s (orderSmallSingle σ 1)) = _
    rw [orderSmallNerveStageNextMap_single]
    exact (orderSmallNerveStage_fill s σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

def orderSmallNerveStageNext {n : ℕ} (s : OrderSmallNerveStage P n) :
    OrderSmallNerveStage P (n + 1) where
  map := orderSmallNerveStageNextMap s
  carrier σ := by
    rw [orderSmallNerveStageNextMap_single]
    exact (orderSmallNerveStage_fill s σ).choose_spec.1
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 2)).toIntLinearMap.comp
        (orderSmallNerveStageNextMap s) = orderSmallNerveStageNextMap s := by
      apply orderSmallSingle_spans
      intro σ
      change Nerve.lengthProjection (n + 2)
        (orderSmallNerveStageNextMap s (orderSmallSingle σ 1)) = _
      rw [orderSmallNerveStageNextMap_single]
      exact (orderSmallNerveStage_fill s σ).choose_spec.2.1
    exact DFunLike.congr_fun he c
  closed_boundary c := by
    rw [orderSmallNerveStageNextMap_boundary]
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    change smallBoundary (orderNerveRealizationOpenStar P) n
      (smallBoundary (orderNerveRealizationOpenStar P) (n + 1) c) = 0 at hd
    rw [hd, map_zero]

/-- A carried approximation exists simultaneously in all dimensions. -/
def orderSmallNerveStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderSmallNerveStage P n
  | 0 => orderSmallNerveStageZero
  | n + 1 => orderSmallNerveStageNext (orderSmallNerveStage P n)

def orderSmallToNerve (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Nerve.Ch P :=
  (orderSmallNerveStage P n).map

theorem orderSmallToNerve_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderSmallToNerve P n (orderSmallSingle σ 1) ∈
      Nerve.IncOn (orderNerveSingularCarrier σ.val) :=
  (orderSmallNerveStage P n).carrier σ

theorem orderSmallToNerve_length (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    Nerve.lengthProjection (n + 1) (orderSmallToNerve P n c) = orderSmallToNerve P n c :=
  (orderSmallNerveStage P n).homogeneous c

theorem orderSmallToNerve_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    Nerve.bdry (orderSmallToNerve P (n + 1) c) =
      orderSmallToNerve P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  orderSmallNerveStageNextMap_boundary (orderSmallNerveStage P n) c

theorem orderSmallToNerve_mem_inc (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) n) :
    orderSmallToNerve P n c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul, orderSmallChainEquiv_symm_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallToNerve_carrier n σ)) r

end FiniteChains.Comb

namespace FiniteChains.Nerve
open FreeAbelianGroup

/-- The recursive list boundary is the alternating face sum in every degree. -/
theorem bdryOn_ofFn {P : Type*} (n : ℕ) (v : Fin (n + 1) → P) :
    bdryOn (List.ofFn v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        of (List.ofFn (fun j : Fin n => v (i.succAbove j))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, bdryOn_cons, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      map_sum, map_zsmul, Fin.val_succ, pow_succ, mul_neg, mul_one]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [neg_smul]
    congr 1
    rw [consMap_of, List.ofFn_succ]
    simp

end FiniteChains.Nerve

namespace FiniteChains.Comb
open CategoryTheory FreeAbelianGroup
open scoped Simplicial
variable {P : Type} [PartialOrder P]

/-- An order-nerve simplex, with all its vertices retained in order. -/
def orderNerveVertexList {n : ℕ} (s : ComposableArrows P n) : List P :=
  List.ofFn s.obj

theorem orderNerveVertexList_chain {n : ℕ} (s : ComposableArrows P n) :
    List.IsChain (· ≤ ·) (orderNerveVertexList s) := by
  rw [orderNerveVertexList, List.isChain_iff_pairwise, List.pairwise_ofFn]
  intro i j hij
  exact s.monotone hij.le

theorem orderNerveVertexList_length {n : ℕ} (s : ComposableArrows P n) :
    (orderNerveVertexList s).length = n + 1 := List.length_ofFn

theorem orderNerveVertexList_injective (n : ℕ) :
    Function.Injective (orderNerveVertexList (P := P) (n := n)) := by
  intro s t h
  exact CategoryTheory.Functor.ext (fun i => congrFun (List.ofFn_injective h) i)

/-- Every increasing list of the required length is a genuine Mathlib simplex. -/
def orderNerveOfVertexList (n : ℕ) (l : List P)
    (hl : List.IsChain (· ≤ ·) l) (hlen : l.length = n + 1) :
    ComposableArrows P n :=
  (show Monotone (fun i : Fin (n + 1) => l[i.val]'(by omega)) from by
      intro i j hij
      rcases hij.eq_or_lt with he | he
      · exact le_of_eq (congrArg (fun k : Fin (n + 1) => l[k.val]'(by omega)) he)
      · exact (List.pairwise_iff_getElem.mp (List.isChain_iff_pairwise.mp hl))
          i.val j.val (by omega) (by omega) he).functor


/-- Coefficient-preserving encoding, in arbitrary degree. -/
def orderNerveGradedEncode (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => of (orderNerveVertexList s))

theorem orderNerveGradedEncode_single (n : ℕ) (s : ComposableArrows P n) (r : ℤ) :
    orderNerveGradedEncode n (Finsupp.single s r) = r • of (orderNerveVertexList s) :=
  Finsupp.linearCombination_single ℤ r s

def orderNerveGradedDecodeList (n : ℕ) (l : List P) :
    ComposableArrows P n →₀ ℤ := by
  classical
  exact if h : ∃ s : ComposableArrows P n, orderNerveVertexList s = l
    then Finsupp.single h.choose 1 else 0

def orderNerveGradedDecode (n : ℕ) :
    Nerve.Ch P →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) :=
  (lift (orderNerveGradedDecodeList n)).toIntLinearMap

theorem orderNerveGradedDecode_of (n : ℕ) (l : List P) :
    orderNerveGradedDecode n (of l) = orderNerveGradedDecodeList n l :=
  lift_apply_of _ _

theorem orderNerveGradedDecodeList_vertexList (n : ℕ) (s : ComposableArrows P n) :
    orderNerveGradedDecodeList n (orderNerveVertexList s) = Finsupp.single s 1 := by
  have h : ∃ t : ComposableArrows P n, orderNerveVertexList t = orderNerveVertexList s := ⟨s, rfl⟩
  rw [orderNerveGradedDecodeList, dif_pos h]
  rw [orderNerveVertexList_injective n h.choose_spec]

theorem orderNerveGradedDecode_encode (n : ℕ) (c : ComposableArrows P n →₀ ℤ) :
    orderNerveGradedDecode n (orderNerveGradedEncode n c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single s r =>
    rw [orderNerveGradedEncode_single, map_smul, orderNerveGradedDecode_of,
      orderNerveGradedDecodeList_vertexList]
    simp

theorem orderNerveGradedEncode_injective (n : ℕ) :
    Function.Injective (orderNerveGradedEncode (P := P) n) := by
  intro c d h
  simpa only [orderNerveGradedDecode_encode] using congrArg (orderNerveGradedDecode n) h

theorem orderNerveGradedEncode_decode (n : ℕ) {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    orderNerveGradedEncode n (orderNerveGradedDecode n c) = Nerve.lengthProjection (n + 1) c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [orderNerveGradedDecode_of, Nerve.lengthProjection_of]
    by_cases hlen : l.length = n + 1
    · have he := (show orderNerveVertexList (orderNerveOfVertexList n l hl hlen) = l by
      apply List.ext_getElem
      · simpa [orderNerveVertexList] using hlen.symm
      · intro i hi hj
        simp only [orderNerveVertexList, List.getElem_ofFn]
        rfl)
      rw [if_pos hlen, ← he, orderNerveGradedDecodeList_vertexList,
        orderNerveGradedEncode_single, one_smul]
    · have he : ¬ ∃ s : ComposableArrows P n, orderNerveVertexList s = l := by
        rintro ⟨s, rfl⟩
        exact hlen (orderNerveVertexList_length s)
      rw [if_neg hlen, orderNerveGradedDecodeList, dif_neg he, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp_all
  | neg x _ hx => simp_all

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
open scoped Simplicial
variable {P : Type} [PartialOrder P]

/-- The free simplicial-module boundary, with its exact integer coefficients. -/
theorem mathlibOrderNerve_d_single (n : ℕ) (s : ComposableArrows P (n + 1)) (r : ℤ) :
    (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom (Finsupp.single s r) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Finsupp.single ((nerve P).δ i s) r := by
  simp [AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, ModuleCat.free]

/-- Mathlib's differential and the augmented list boundary coincide in every positive degree. -/
theorem orderNerveGradedEncode_boundary (n : ℕ) (c : ComposableArrows P (n + 1) →₀ ℤ) :
    orderNerveGradedEncode n ((AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) n).hom c) =
      Nerve.bdry (orderNerveGradedEncode (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single s r =>
    erw [mathlibOrderNerve_d_single, map_sum, orderNerveGradedEncode_single,
      map_zsmul, Nerve.bdry_of]
    unfold orderNerveVertexList
    erw [Nerve.bdryOn_ofFn, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    erw [map_smul, orderNerveGradedEncode_single, smul_comm]
    rfl

/-- Realize a homogeneous part of the augmented nerve by the canonical unit. -/
def orderNerveGradedRealize (P : Type) [PartialOrder P] (n : ℕ) :
    Nerve.Ch P →ₗ[ℤ] Chain (orderNerveRealization P) n :=
  ((orderNerveExplicitSingularMap P).f n).hom.comp (orderNerveGradedDecode n)

theorem orderNerveGradedRealize_boundary (n : ℕ) {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    boundary n (orderNerveGradedRealize P (n + 1) c) =
      orderNerveGradedRealize P n (Nerve.bdry c) := by
  have hd : (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom
      (orderNerveGradedDecode (n + 1) c) = orderNerveGradedDecode n (Nerve.bdry c) := by
    apply orderNerveGradedEncode_injective n
    erw [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hc,
      orderNerveGradedEncode_decode _ (Nerve.bdry_mem_inc hc), Nerve.lengthProjection_bdry]
  have he := congrArg (fun f => f (orderNerveGradedDecode (n + 1) c))
    ((orderNerveExplicitSingularMap P).comm (n + 1) n)
  erw [complex_d, AlternatingFaceMapComplex.obj_d_eq] at he
  change (boundary n) ((orderNerveExplicitSingularMap P).f (n + 1)
      (orderNerveGradedDecode (n + 1) c)) =
    (orderNerveExplicitSingularMap P).f n (orderNerveGradedDecode n (Nerve.bdry c))
  erw [← hd]
  exact he

theorem orderNerveGradedRealize_supported (n : ℕ) (A : Set P)
    {c : Nerve.Ch P} (hc : c ∈ Nerve.IncOn A) :
    orderNerveGradedRealize P n c ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) n := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    change (orderNerveExplicitSingularMap P).f n (orderNerveGradedDecode n
      (FreeAbelianGroup.of l)) ∈ _
    erw [orderNerveGradedDecode_of]
    by_cases h : ∃ s : ComposableArrows P n, orderNerveVertexList s = l
    · rw (config := { transparency := .default }) [orderNerveGradedDecodeList, dif_pos h, orderNerveExplicitSingularMap_single]
      apply single_mem_subChains
      intro z
      apply orderNerveSingularSimplex_supported
      intro i
      apply hl.2
      have hs : h.choose.obj i ∈ orderNerveVertexList h.choose := List.mem_ofFn.mpr ⟨i, rfl⟩
      exact (congrArg (fun L => h.choose.obj i ∈ L) h.choose_spec).mp hs
    · rw (config := { transparency := .default }) [orderNerveGradedDecodeList, dif_neg h, map_zero]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | neg x _ hx => simp_all

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open Topology
open scoped Classical

theorem open_iff_of_sheet {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] (f : C(E, X))
    {U : Set E} {V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (e : U ≃ₜ V) (he : ∀ z : U, (e z).val = f z.val)
    {W : Set X} (hW : W ⊆ V) :
    IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U) := by
  constructor
  · intro h
    exact (h.preimage f.continuous).inter hU
  · intro h
    have hp : IsOpen (e ⁻¹' (Subtype.val ⁻¹' W)) := by
      have hh := h.preimage (continuous_subtype_val : Continuous (Subtype.val : U → E))
      convert hh using 1
      ext z
      change (e z).val ∈ W ↔ f z.val ∈ W ∧ z.val ∈ U
      rw [he z]
      simp
    have hv := e.isOpen_preimage.mp hp
    have hi := hV.isOpenMap_subtype_val _ hv
    have hr : (Subtype.val : V → X) '' (Subtype.val ⁻¹' W) = W := by
      ext x
      constructor
      · simp
      · intro hx
        exact ⟨⟨x, hW hx⟩, hx, rfl⟩
    rwa [hr] at hi

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A sheet over a chosen lifted vertex, with its target identified with the chosen base star. -/
def realizationSheetHomeomorph (hf : IsPosetCover f) (q : Q)
    (v : {p : P // f p = q}) :
    orderNerveRealizationOpenStar P v.val ≃ₜ orderNerveRealizationOpenStar Q q :=
  (hf.vertexOpenStarHomeomorph v.val).trans
    (Homeomorph.setCongr (congrArg (orderNerveRealizationOpenStar Q) v.property))

theorem realizationSheetHomeomorph_coe (hf : IsPosetCover f) (q : Q)
    (v : {p : P // f p = q}) (z : orderNerveRealizationOpenStar P v.val) :
    (hf.realizationSheetHomeomorph q v z).val = orderNerveRealizationMap f hf.mono z.val :=
  hf.vertexOpenStarHomeomorph_coe v.val z

/-- Every actual open vertex star is an evenly covered neighborhood. -/
theorem realizationMap_evenlyCovered (hf : IsPosetCover f) (q : Q)
    (x : orderNerveRealization Q) (hx : x ∈ orderNerveRealizationOpenStar Q q) :
    IsEvenlyCovered (orderNerveRealizationMap f hf.mono) x
      (orderNerveRealizationMap f hf.mono ⁻¹' {x}) := by
  let I := {p : P // f p = q}
  letI : TopologicalSpace I := ⊥
  letI : DiscreteTopology I := ⟨rfl⟩
  obtain ⟨v, hv⟩ := hf.surj q
  letI : Nonempty I := ⟨⟨v, hv⟩⟩
  letI : Nonempty (orderNerveRealization P) := ⟨orderNerveRealizationVertex v⟩
  let F : C(orderNerveRealization P, orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap f hf.mono, (orderNerveRealizationMap f hf.mono).hom.continuous⟩
  let U : I → Set (orderNerveRealization P) := fun i => orderNerveRealizationOpenStar P i.val
  let V := orderNerveRealizationOpenStar Q q
  let e  := hf.realizationSheetHomeomorph q
  have he : ∀ i z, (e i z).val = F z.val :=
    hf.realizationSheetHomeomorph_coe q
  let t := IsOpen.trivializationDiscrete (f := F) U V
    (orderNerveRealizationOpenStar_isOpen Q q)
    (fun i {_} hW => open_iff_of_sheet F (orderNerveRealizationOpenStar_isOpen P i.val)
      (orderNerveRealizationOpenStar_isOpen Q q) (e i) (he i) hW)
    (by
      intro i a ha b hb hab
      have hh  :=
        Subtype.ext ((he i ⟨a, ha⟩).trans (hab.trans (he i ⟨b, hb⟩).symm))
      exact congrArg Subtype.val ((e i).injective hh))
    (by
      intro i y hy
      refine ⟨((e i).symm ⟨y, hy⟩).val, ((e i).symm ⟨y, hy⟩).property, ?_⟩
      rw [← he i, (e i).apply_symm_apply])
    (by
      intro i j hij
      exact hf.realizationOpenStar_disjoint (fun h => hij (Subtype.ext h))
        (i.property.trans j.property.symm))
    (by
      intro y hy
      obtain ⟨p, hp, hyp⟩ := (orderNerveRealizationMap_mem_openStar_iff f hf.mono y q).mp hy
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hyp⟩)
  exact (IsEvenlyCovered.of_trivialization (t := t) hx).to_isEvenlyCovered_preimage

/-- The realization of every poset covering is a genuine Mathlib covering map. -/
theorem realizationMap_isCoveringMap (hf : IsPosetCover f) :
    IsCoveringMap (orderNerveRealizationMap f hf.mono) := by
  intro x
  obtain ⟨q, hq⟩ := orderNerveRealizationOpenStar_cover Q x
  exact hf.realizationMap_evenlyCovered q x hq

end IsPosetCover
end FiniteChains.Comb

namespace FiniteChains.Comb
open Topology
open scoped Classical

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- The realized projection is injective on each of its open-star sheets. -/
theorem realizationMap_injOn_openStar (hf : IsPosetCover f) (v : P) :
    (orderNerveRealizationOpenStar P v).InjOn (orderNerveRealizationMap f hf.mono) := by
  intro x hx y hy hxy
  have hh : hf.vertexOpenStarHomeomorph v ⟨x, hx⟩ =
      hf.vertexOpenStarHomeomorph v ⟨y, hy⟩ := by
    ext
    simpa only [hf.vertexOpenStarHomeomorph_coe] using hxy
  simp_all

/-- An order deck transformation realizes to a genuine topological deck transformation. -/
theorem realization_deck_commutes (hf : IsPosetCover f) (e : P ≃o P)
    (he : ∀ p, f (e p) = f p) (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf.mono (orderNerveRealizationOrderIso e x) =
      orderNerveRealizationMap f hf.mono x := by
  change orderNerveRealizationMap f hf.mono
    (orderNerveRealizationMap e e.monotone x) = _
  rw [orderNerveRealizationMap_comp]
  have h : (f ∘ e) = f := funext he
  simp only [h]

/-- Transitivity of order deck transformations on vertex fibers implies regularity
of the actual covering, on all points of all topological fibers. -/
theorem realizationMap_regular (hf : IsPosetCover f)
    (hdeck : ∀ v w : P, f v = f w →
      ∃ e : P ≃o P, (∀ p, f (e p) = f p) ∧ e v = w) :
    Whitehead.Regular
      ⟨orderNerveRealizationMap f hf.mono,
        (orderNerveRealizationMap f hf.mono).hom.continuous⟩ := by
  intro x y hxy
  obtain ⟨v, hxv⟩ := orderNerveRealizationOpenStar_cover P x
  have hx  :=
    (orderNerveRealizationMap_mem_openStar_iff f hf.mono x (f v)).mpr ⟨v, rfl, hxv⟩
  have hy  := hxy ▸ hx
  obtain ⟨w, hw, hyw⟩ :=
    (orderNerveRealizationMap_mem_openStar_iff f hf.mono y (f v)).mp hy
  obtain ⟨e, he, hev⟩ := hdeck v w hw.symm
  refine ⟨orderNerveRealizationOrderIso e, hf.realization_deck_commutes e he, ?_⟩
  have hxe : orderNerveRealizationOrderIso e x ∈ orderNerveRealizationOpenStar P w := by
    rw [← hev]
    change 0 < orderNerveRealizationCoordinates P
      (orderNerveRealizationMap e e.monotone x) (e v)
    rw [orderNerveRealizationCoordinates_map_injective e e.monotone e.injective]
    exact hxv
  exact hf.realizationMap_injOn_openStar w hxe hyw
    ((hf.realization_deck_commutes e he x).trans hxy)

end IsPosetCover
end FiniteChains.Comb

namespace FiniteChains.Comb
open Topology

variable {P : Type} [PartialOrder P] (a : P)

/-- The actual endpoint projection on geometric realizations. -/
def uOrderRealizationProjection :
    C(orderNerveRealization (UOrder P a), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap uOrderEnd uOrderEnd_monotone,
    (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone).hom.continuous⟩

theorem uOrderRealizationProjection_isCoveringMap (hc : IsConnected (orderCx P)) :
    IsCoveringMap (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_isCoveringMap

theorem uOrderRealizationProjection_surjective (hc : IsConnected (orderCx P)) :
    Function.Surjective (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_surjective

end FiniteChains.Comb

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]


/-- Functorial map between the actual ordered universal covers. -/
def uOrderMap (f : P → Q) (hf : Monotone f) (a : P) :
    UOrder P a →o UOrder Q (f a) :=
  ⟨@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf), (by
    intro v w hvw
    have he (v : UOrder P a) :
        uOrderEnd (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) = f (uOrderEnd v) :=
      @endV_univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v
    refine ⟨(he v).le.trans ((hf hvw.1).trans (he w).ge), ?_⟩
    have h := univLiftV_extend (X := orderCx P) (Y := orderCx Q) a (orderCxMap f hf) (eb := ordPos hvw.1) (c := v) rfl
    have hw : extend (ordPos hvw.1) v = w := hvw.2
    erw [hw] at h
    change extend (ordPos _) (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) = _
    calc
      _ = extend ((orderCxMap f hf).onE (ordPos hvw.1).1, true)
          (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) := by
        congr 1
        apply Prod.ext
        · apply Subtype.ext
          exact Prod.ext (he v) (he w)
        · rfl
      _ = _ := h.symm)⟩

theorem uOrderMap_end (f : P → Q) (hf : Monotone f) (a : P) (v : UOrder P a) :
    uOrderEnd (uOrderMap f hf a v) = f (uOrderEnd v) :=
  @endV_univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v

theorem uOrderMap_realization_projection (f : P → Q) (hf : Monotone f) (a : P)
    (x : orderNerveRealization (UOrder P a)) :
    orderNerveRealizationMap uOrderEnd uOrderEnd_monotone
      (orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone x) =
    orderNerveRealizationMap f hf
      (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone x) := by
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hm : (⟨uOrderEnd ∘ uOrderMap f hf a,
      uOrderEnd_monotone.comp (uOrderMap f hf a).monotone⟩ :
      {g : UOrder P a → Q // Monotone g}) =
      ⟨f ∘ uOrderEnd, hf.comp uOrderEnd_monotone⟩ :=
    Subtype.ext (funext (uOrderMap_end f hf a))
  simp_all

end FiniteChains.Comb

namespace FiniteChains.Comb.LocalSystem
open CategoryTheory
universe u
variable {P : Type u} [PartialOrder P] (F : P ⥤ Type u)

def Cover := Σ p : P, F.obj p

instance coverPartialOrder : PartialOrder (Cover F) where
  le x y := ∃ h : x.1 ≤ y.1, F.map (homOfLE h) x.2 = y.2
  le_refl x := ⟨le_rfl, by simp⟩
  le_trans x y z hxy hyz := by
    obtain ⟨hxy, hfx⟩ := hxy
    obtain ⟨hyz, hfy⟩ := hyz
    refine ⟨hxy.trans hyz, ?_⟩
    have hh := ConcreteCategory.congr_hom (F.map_comp (homOfLE hxy) (homOfLE hyz)) x.2
    change F.map (homOfLE (hxy.trans hyz)) x.2 =
      F.map (homOfLE hyz) (F.map (homOfLE hxy) x.2) at hh
    rw [hh, hfx, hfy]
  le_antisymm x y hxy hyx := by
    rcases x with ⟨p, x⟩
    rcases y with ⟨q, y⟩
    obtain ⟨hpq, hx⟩ := hxy
    obtain ⟨hqp, _⟩ := hyx
    obtain rfl := le_antisymm hpq hqp
    have hxy : x = y := by simpa using hx
    cases hxy
    rfl

def projection : Cover F → P := Sigma.fst

theorem projection_monotone : Monotone (projection F) := fun _ _ h => h.choose

theorem projection_isPosetCover
    (hF : ∀ {p q : P} (h : p ≤ q), Function.Bijective (F.map (homOfLE h)))
    (hne : ∀ p, Nonempty (F.obj p)) : IsPosetCover (projection F) := by
  refine ⟨projection_monotone F, fun p => ⟨⟨p, Classical.choice (hne p)⟩, rfl⟩, ?_, ?_⟩
  · intro x q hxq
    refine ⟨⟨q, F.map (homOfLE hxq) x.2⟩, ⟨⟨hxq, rfl⟩, rfl⟩, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hxy, hy⟩, hr⟩
    change r = q at hr
    subst r
    exact congrArg (Sigma.mk q) hy.symm
  · intro x q hqx
    obtain ⟨v, hv⟩ := (hF hqx).2 x.2
    refine ⟨⟨q, v⟩, ⟨⟨hqx, hv⟩, rfl⟩, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hyx, hy⟩, hr⟩
    change r = q at hr
    subst r
    exact congrArg (Sigma.mk q) ((hF hqx).1 (hy.trans hv.symm))

end FiniteChains.Comb.LocalSystem

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Topology
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def fibreFunctor : P ⥤ Type :=
  orderNerveRealizationFundamentalFunctor P ⋙ hp.monodromyFunctor

abbrev Cover := LocalSystem.Cover (fibreFunctor p hp)
def projection : Cover p hp → P := LocalSystem.projection (fibreFunctor p hp)

theorem projection_monotone : Monotone (projection p hp) :=
  LocalSystem.projection_monotone (fibreFunctor p hp)

def point (v : Cover p hp) : E := v.2.val

theorem point_projection (v : Cover p hp) : p (point p hp v) = orderNerveRealizationVertex v.1 :=
  v.2.property


theorem projection_isPosetCover (hs : Function.Surjective p) : IsPosetCover (projection p hp) := by
  apply LocalSystem.projection_isPosetCover (fibreFunctor p hp)
  · exact fun h => (hp.monodromy_bijective (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath h)))
  · intro a
    obtain ⟨x, hx⟩ := hs (orderNerveRealizationVertex a)
    exact ⟨⟨x, hx⟩⟩

/-- The defining incidence square retains the actual covering lift. -/
theorem comparable_transport {v w : Cover p hp} (h : v ≤ w) :
    hp.monodromy (Path.Homotopic.Quotient.mk
      (orderNerveRealizationEdgePath h.choose)) v.2 = w.2 := h.choose_spec

end FiniteChains.Comb.TopologicalOrderCover

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

def strictMap : Hom (strictOrderCx P) (strictOrderCx Q) := strictOrderCxMap f hf.strictMono

theorem strictMap_isCovering : IsCovering hf.strictMap := by
  refine ⟨hf.surj, ?_, ?_⟩
  · intro a
    change P at a
    constructor
    · rintro ⟨⟨e, b⟩, he⟩ ⟨⟨e', b'⟩, he'⟩ hEq
      have hb : b = b' := congrArg (fun g : Germ (strictOrderCx Q) _ => g.val.2) hEq
      subst b'
      have hpair : (f e.val.1, f e.val.2) = (f e'.val.1, f e'.val.2) :=
        congrArg (fun g : Germ (strictOrderCx Q) _ => g.val.1.val) hEq
      have h₁ := congrArg Prod.fst hpair
      have h₂ := congrArg Prod.snd hpair
      apply Subtype.ext
      refine Prod.ext ?_ rfl
      cases b with
      | false =>
          have hea : e.val.2 = a := he
          have hea' : e'.val.2 = a := he'
          have hfst := hf.down_inj (a := a)
            (by rw [← hea]; exact e.property.le)
            (by rw [← hea']; exact e'.property.le) h₁
          exact Subtype.ext (Prod.ext hfst (hea.trans hea'.symm))
      | true =>
          have hea : e.val.1 = a := he
          have hea' : e'.val.1 = a := he'
          have hsnd := hf.up_inj (a := a)
            (by rw [← hea]; exact e.property.le)
            (by rw [← hea']; exact e'.property.le) h₂
          exact Subtype.ext (Prod.ext (hea.trans hea'.symm) hsnd)
    · rintro ⟨⟨d, b⟩, hd⟩
      cases b with
      | true =>
          have hfa : f a = d.val.1 := hd.symm
          obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a d.val.2 (by rw [hfa]; exact d.property.le)
          have hac' : a < c := lt_of_le_of_ne hac (fun he =>
            d.property.ne (hfa.symm.trans ((congrArg f he).trans hfc)))
          refine ⟨⟨(⟨(a, c), hac'⟩, true), rfl⟩, ?_⟩
          exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfa hfc)) rfl)
      | false =>
          have hfa : f a = d.val.2 := hd.symm
          obtain ⟨c, ⟨hca, hfc⟩, _⟩ := hf.down a d.val.1 (by rw [hfa]; exact d.property.le)
          have hca' : c < a := lt_of_le_of_ne hca (fun he =>
            d.property.ne (hfc.symm.trans ((congrArg f he).trans hfa)))
          refine ⟨⟨(⟨(c, a), hca'⟩, false), rfl⟩, ?_⟩
          exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfc hfa)) rfl)
  · constructor
    · intro t t' hEq
      have hbase : t.val.1 = t'.val.1 := congrArg (fun z => z.val.2) hEq
      have htri : (f t.val.1, f t.val.2.1, f t.val.2.2) =
          (f t'.val.1, f t'.val.2.1, f t'.val.2.2) := congrArg (fun z => z.val.1.val) hEq
      have hmid := hf.up_inj t.property.1.le
        (by rw [hbase]; exact t'.property.1.le)
        (congrArg (fun z : Q × Q × Q => z.2.1) htri)
      have htop := hf.up_inj (t.property.1.trans t.property.2).le
        (by rw [hbase]; exact (t'.property.1.trans t'.property.2).le)
        (congrArg (fun z : Q × Q × Q => z.2.2) htri)
      exact Subtype.ext (Prod.ext hbase (Prod.ext hmid htop))
    · rintro ⟨⟨s, a⟩, hs⟩
      change P at a
      have hfa : f a = s.val.1 := hs.symm
      obtain ⟨b, ⟨hab, hfb⟩, _⟩ := hf.up a s.val.2.1 (by rw [hfa]; exact s.property.1.le)
      obtain ⟨c, ⟨hbc, hfc⟩, _⟩ := hf.up b s.val.2.2 (by rw [hfb]; exact s.property.2.le)
      have hab' : a < b := lt_of_le_of_ne hab (fun he =>
        s.property.1.ne (hfa.symm.trans ((congrArg f he).trans hfb)))
      have hbc' : b < c := lt_of_le_of_ne hbc (fun he =>
        s.property.2.ne (hfb.symm.trans ((congrArg f he).trans hfc)))
      refine ⟨⟨(a, b, c), hab', hbc'⟩, ?_⟩
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfa (Prod.ext hfb hfc))) rfl)

end FiniteChains.Comb.IsPosetCover

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Topology
open scoped unitInterval
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def deckSubgroup : Subgroup (Equiv.Perm E) where
  carrier := {g | Continuous g ∧ Continuous g.symm ∧ ∀ x, p (g x) = p x}
  one_mem' := ⟨continuous_id, continuous_id, fun _ => rfl⟩
  mul_mem' {g h} hg hh := by
    refine ⟨hg.1.comp hh.1, hh.2.1.comp hg.2.1, ?_⟩
    intro x
    exact (hg.2.2 (h x)).trans (hh.2.2 x)
  inv_mem' {g} hg := by
    refine ⟨hg.2.1, hg.1, ?_⟩
    intro x
    have hh := hg.2.2 (g.symm x)
    convert hh.symm using 1 <;> simp only [Equiv.apply_symm_apply]

def deckHomeomorph (g : deckSubgroup p) : E ≃ₜ E where
  toEquiv := g.val
  continuous_toFun := g.property.1
  continuous_invFun := g.property.2.1

def deckFibre (g : deckSubgroup p) (x : orderNerveRealization P) :
    (p ⁻¹' {x}) ≃ (p ⁻¹' {x}) where
  toFun e := ⟨g.val e.val, (g.property.2.2 e.val).trans e.property⟩
  invFun e := ⟨g.val.symm e.val, by
    have hh := g.property.2.2 (g.val.symm e.val)
    rw [g.val.apply_symm_apply] at hh
    exact hh.symm.trans e.property⟩
  left_inv e := Subtype.ext (g.val.symm_apply_apply e.val)
  right_inv e := Subtype.ext (g.val.apply_symm_apply e.val)

theorem monodromy_deck (g : deckSubgroup p)
    {x y : orderNerveRealization P} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    hp.monodromy γ (deckFibre p g x e) = deckFibre p g y (hp.monodromy γ e) := by
  obtain ⟨γ⟩ := γ
  have h₀ : γ 0 = p e.val := γ.source.trans e.property.symm
  have h₁ : γ 0 = p (g.val e.val) := h₀.trans (g.property.2.2 e.val).symm
  let L := hp.liftPath γ e.val h₀
  let M  := (deckHomeomorph p g).toContinuousMap.comp L
  have hM : M = hp.liftPath γ (g.val e.val) h₁ := by
    apply (hp.eq_liftPath_iff' h₁).mpr
    constructor
    · funext t
      change p (g.val (L t)) = γ t
      rw [g.property.2.2]
      exact congrFun (hp.liftPath_lifts γ e.val h₀) t
    · change g.val (hp.liftPath γ e.val h₀ 0) = g.val e.val
      rw [hp.liftPath_zero]
  apply Subtype.ext
  exact (congrArg (fun k : C(unitInterval, E) => k 1) hM).symm

def deck (g : deckSubgroup p) : Cover p hp ≃o Cover p hp where
  toFun v := ⟨v.1, deckFibre p g (orderNerveRealizationVertex v.1) v.2⟩
  invFun v := ⟨v.1, (deckFibre p g (orderNerveRealizationVertex v.1)).symm v.2⟩
  left_inv v := by
    refine Sigma.ext rfl ?_
    exact heq_of_eq ((deckFibre p g _).symm_apply_apply v.2)
  right_inv v := by
    refine Sigma.ext rfl ?_
    exact heq_of_eq ((deckFibre p g _).apply_symm_apply v.2)
  map_rel_iff' := by
    intro v w
    constructor
    · rintro ⟨hvw, hval⟩
      refine ⟨hvw, ?_⟩
      apply (deckFibre p g (orderNerveRealizationVertex w.1)).injective
      exact (monodromy_deck p hp g
        (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath hvw)) v.2).symm.trans hval
    · rintro ⟨hvw, hval⟩
      refine ⟨hvw, ?_⟩
      exact (monodromy_deck p hp g
        (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath hvw)) v.2).trans
        (congrArg (deckFibre p g (orderNerveRealizationVertex w.1)) hval)

theorem deck_one (v : Cover p hp) : deck p hp 1 v = v := rfl

theorem deck_mul (g h : deckSubgroup p) (v : Cover p hp) :
    deck p hp (g * h) v = deck p hp g (deck p hp h v) := rfl

def strictDeckAction : DeckAction (strictOrderCx (Cover p hp)) (deckSubgroup p) where
  smulV := fun g => deck p hp g
  smulE g e := ⟨(deck p hp g e.val.1, deck p hp g e.val.2), (deck p hp g).strictMono e.property⟩
  smulF g t := ⟨(deck p hp g t.val.1, deck p hp g t.val.2.1, deck p hp g t.val.2.2),
    (deck p hp g).strictMono t.property.1, (deck p hp g).strictMono t.property.2⟩
  one_smulV := deck_one p hp
  mul_smulV := deck_mul p hp
  one_smulE _ := Subtype.ext (Prod.ext (deck_one p hp _) (deck_one p hp _))
  mul_smulE g h _ := Subtype.ext (Prod.ext (deck_mul p hp g h _) (deck_mul p hp g h _))
  one_smulF _ := Subtype.ext (Prod.ext (deck_one p hp _) (Prod.ext (deck_one p hp _) (deck_one p hp _)))
  mul_smulF g h _ := Subtype.ext (Prod.ext (deck_mul p hp g h _)
    (Prod.ext (deck_mul p hp g h _) (deck_mul p hp g h _)))
  src_smul _ _ := rfl
  tgt_smul _ _ := rfl
  base_smul _ _ := rfl
  att_smul _ _ := rfl

def strictProjection (hs : Function.Surjective p) :
    Hom (strictOrderCx (Cover p hp)) (strictOrderCx P) := (projection_isPosetCover p hp hs).strictMap

theorem strictProjection_isCovering (hs : Function.Surjective p) :
    IsCovering (strictProjection p hp hs) := (projection_isPosetCover p hp hs).strictMap_isCovering

theorem strictDeck_edges (hs : Function.Surjective p) (g : deckSubgroup p)
    (e : (strictOrderCx (Cover p hp)).E) :
    (strictProjection p hp hs).onE ((strictDeckAction p hp).smulE g e) =
      (strictProjection p hp hs).onE e := rfl

theorem strictDeck_faces (hs : Function.Surjective p) (g : deckSubgroup p)
    (t : (strictOrderCx (Cover p hp)).F) :
    (strictProjection p hp hs).onF ((strictDeckAction p hp).smulF g t) =
      (strictProjection p hp hs).onF t := rfl

theorem strictProjection_isRegular [ConnectedSpace E] (hs : Function.Surjective p)
    (hr : Whitehead.Regular p) : IsRegular (strictProjection p hp hs) (strictDeckAction p hp) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro v w hvw
  have hproj  :=
    (point_projection p hp v).trans
      ((congrArg (orderNerveRealizationVertex (P := P)) hvw).trans (point_projection p hp w).symm)
  obtain ⟨e, he, hev⟩ := hr (point p hp v) (point p hp w) hproj
  let g : deckSubgroup p := ⟨e.toEquiv, e.continuous, e.symm.continuous, he⟩
  have hgv : (strictDeckAction p hp).smulV g v = w := by
    rcases v with ⟨v, x⟩
    rcases w with ⟨w, y⟩
    change v = w at hvw
    subst w
    refine Sigma.ext rfl ?_
    exact heq_of_eq (Subtype.ext hev)
  refine ⟨g, hgv, ?_⟩
  intro h hh
  have hpoint  :=
    (congrArg (point p hp) hh).trans (congrArg (point p hp) hgv).symm
  apply Subtype.ext
  apply Equiv.ext
  exact congrFun (hp.eq_of_comp_eq h.property.1 g.property.1
    (funext (fun x => (h.property.2.2 x).trans (g.property.2.2 x).symm))
    (point p hp v) hpoint)

end FiniteChains.Comb.TopologicalOrderCover
