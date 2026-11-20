/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.WiredPotentialSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped Matrix

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (A : Configuration G)

/-- The genuine finite index set of open edges, retaining every selected unordered edge. -/
abbrev OpenEdgeIndex := {e : G.edgeSet // e ∈ A}

/-- An orientation is chosen for each actual open edge; its unordered endpoints
are required to be the edge itself. -/
structure SignedFlowOrientation where
  source : OpenEdgeIndex G A → V
  target : OpenEdgeIndex G A → V
  endpoints : ∀ e, s(source e, target e) = e.1.1

local instance openEdgeIndexFintype : Fintype (OpenEdgeIndex G A) := Fintype.ofFinite _
local instance openEdgeIndexDecidableEq : DecidableEq (OpenEdgeIndex G A) := Classical.decEq _

section
variable (o : SignedFlowOrientation G A)
include o

/-- Signed vertex-edge incidence matrix: +1 at the source and −1 at the target. -/
def signedIncidenceMatrix :
    Matrix (OpenEdgeIndex G A) V ℝ := fun e v =>
  if v = o.source e then 1 else if v = o.target e then -1 else 0

/-- The signed gradient is the genuine incidence map from vertex potentials to edge differences. -/
def signedGradient :
    (V → ℝ) →ₗ[ℝ] (OpenEdgeIndex G A → ℝ) :=
  Matrix.mulVecLin (signedIncidenceMatrix G A o)

/-- The signed divergence is the transpose incidence map, with outflow minus inflow. -/
def signedDivergence :
    (OpenEdgeIndex G A → ℝ) →ₗ[ℝ] (V → ℝ) :=
  Matrix.mulVecLin ((signedIncidenceMatrix G A o)ᵀ)

end

omit [Fintype V] [DecidableEq V] in
lemma signedFlow_source_ne_target (o : SignedFlowOrientation G A) (e : OpenEdgeIndex G A) :
    o.source e ≠ o.target e := by
  have hdiag := G.not_isDiag_of_mem_edgeSet e.1.2
  have hnot : ¬ (s(o.source e, o.target e)).IsDiag := by simpa [o.endpoints e] using hdiag
  intro heq
  exact hnot (Sym2.mk_isDiag_iff.2 heq)

section
variable (o : SignedFlowOrientation G A) (f : V → ℝ)

theorem signedGradient_apply (e : OpenEdgeIndex G A) :
    signedGradient G A o f e = f (o.source e) - f (o.target e) := by
  calc
    _ = ∑ v, ((if v = o.source e then f v else 0) +
          (if v = o.target e then -f v else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [signedIncidenceMatrix]
      by_cases hs : v = o.source e
      · grind [signedFlow_source_ne_target G A o e]
      · grind
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']
      ring

theorem signedDivergence_apply
    (F : OpenEdgeIndex G A → ℝ) (v : V) :
    signedDivergence G A o F v =
      (∑ e, if o.source e = v then F e else 0) -
      (∑ e, if o.target e = v then F e else 0) := by
  have hterm (e : OpenEdgeIndex G A) :
      (signedIncidenceMatrix G A o e v) * F e =
        (if o.source e = v then F e else 0) +
          (if o.target e = v then -F e else 0) := by
    grind [signedIncidenceMatrix, signedFlow_source_ne_target]
  calc
    _ = ∑ e,
        ((if o.source e = v then F e else 0) +
          (if o.target e = v then -F e else 0)) := Finset.sum_congr rfl fun e a => hterm e
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have hneg : (∑ e,
          if o.target e = v then -F e else 0) =
          -(∑ e, if o.target e = v then F e else 0) := by
        rw [← Finset.sum_neg_distrib]
        grind
      grind

theorem signedGradient_mem_ker_iff :
    f ∈ LinearMap.ker (signedGradient G A o) ↔
      ∀ e : OpenEdgeIndex G A, f (o.source e) = f (o.target e) := by
  constructor
  · intro h e
    have he' : f (o.source e) - f (o.target e) = 0 := by
      simpa [signedGradient_apply] using (congrFun h e)
    linarith
  · intro h
    funext e
    simp [signedGradient_apply, h e]

theorem signedGradient_ker_eq_componentConstantFunctions :
    LinearMap.ker (signedGradient G A o) =
      componentConstantFunctions G (BoundaryCondition.free (∅)) A := by
  ext f
  rw [signedGradient_mem_ker_iff G A o f, componentConstant_iff_local]
  constructor
  · intro h
    constructor
    · intro u v hadj
      rcases ((openGraph_adj A u v).mp hadj) with ⟨edge, hedgeA, hval⟩
      have hedgeA' : edge ∈ A := by exact hedgeA
      grind [o.endpoints ⟨edge, hedgeA'⟩]
    · simp_all
  · rintro ⟨hopen, hboundary⟩ e
    exact hopen ((openGraph_adj A _ _).2 ⟨e.1, by simp, (o.endpoints e).symm⟩)

end

omit [DecidableEq V] in
theorem openEdgeIndex_card : Fintype.card (OpenEdgeIndex G A) = A.card := by
  simp

variable (o : SignedFlowOrientation G A)

private theorem finrank_range_signedDivergence :
    Module.finrank ℝ (LinearMap.range (signedDivergence G A o)) =
      (signedIncidenceMatrix G A o).rank := Trans.trans (Eq.symm (Matrix.rank_eq_finrank_range_toLin (signedIncidenceMatrix G A o)ᵀ (Pi.basisFun ℝ V) (Pi.basisFun ℝ (OpenEdgeIndex G A)))) (Matrix.rank_transpose (signedIncidenceMatrix G A o))

theorem signedFlowDimension :
    Module.finrank ℝ (LinearMap.ker (signedDivergence G A o)) + Fintype.card V =
      A.card + componentCount (BoundaryCondition.free (∅)) A := by
  classical
  have hgrad := LinearMap.finrank_range_add_finrank_ker (signedGradient G A o)
  rw [signedGradient_ker_eq_componentConstantFunctions G A o,
    componentConstantFunctions_finrank, Module.finrank_fintype_fun_eq_card] at hgrad
  have hgradRank : (signedIncidenceMatrix G A o).rank +
      componentCount (BoundaryCondition.free (∅)) A = Fintype.card V := hgrad
  have hdiv := LinearMap.finrank_range_add_finrank_ker (signedDivergence G A o)
  grind [finrank_range_signedDivergence G A o, Module.finrank_fintype_fun_eq_card, openEdgeIndex_card]

end
end PottsDiscontinuity.FK
