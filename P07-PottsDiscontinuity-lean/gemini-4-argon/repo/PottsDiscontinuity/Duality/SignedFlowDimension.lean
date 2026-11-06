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

abbrev OpenEdgeIndex := {e : G.edgeSet // e ∈ A}

structure SignedFlowOrientation where
  source : OpenEdgeIndex G A → V
  target : OpenEdgeIndex G A → V
  endpoints : ∀ e, s(source e, target e) = e.1.1

local instance openEdgeIndexFintype : Fintype (OpenEdgeIndex G A) := Fintype.ofFinite _
local instance openEdgeIndexDecidableEq : DecidableEq (OpenEdgeIndex G A) := Classical.decEq _

def signedIncidenceMatrix (o : SignedFlowOrientation G A) :
    Matrix (OpenEdgeIndex G A) V ℝ := fun e v =>
  if v = o.source e then 1 else if v = o.target e then -1 else 0

def signedGradient (o : SignedFlowOrientation G A) :
    (V → ℝ) →ₗ[ℝ] (OpenEdgeIndex G A → ℝ) :=
  Matrix.mulVecLin (signedIncidenceMatrix G A o)

def signedDivergence (o : SignedFlowOrientation G A) :
    (OpenEdgeIndex G A → ℝ) →ₗ[ℝ] (V → ℝ) :=
  Matrix.mulVecLin ((signedIncidenceMatrix G A o)ᵀ)

omit [Fintype V] [DecidableEq V] in
lemma signedFlow_source_ne_target (o : SignedFlowOrientation G A) (e : OpenEdgeIndex G A) :
    o.source e ≠ o.target e := fun heq => by
  have hdiag : ¬ (e.1.1).IsDiag := G.not_isDiag_of_mem_edgeSet e.1.2
  rw [← o.endpoints e] at hdiag
  exact hdiag (Sym2.mk_isDiag_iff.2 heq)

theorem signedGradient_apply (o : SignedFlowOrientation G A)
    (f : V → ℝ) (e : OpenEdgeIndex G A) :
    signedGradient G A o f e = f (o.source e) - f (o.target e) := by
  change (∑ v : V, signedIncidenceMatrix G A o e v * f v) = _
  have h : ∀ v : V, signedIncidenceMatrix G A o e v * f v =
      (if v = o.source e then f v else 0) - (if v = o.target e then f v else 0) := fun v => by
    simp only [signedIncidenceMatrix]
    by_cases hs : v = o.source e
    · subst v; simp [signedFlow_source_ne_target G A o e]
    · by_cases ht : v = o.target e
      · subst v; simp [hs]
      · simp [hs, ht]
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq']

theorem signedDivergence_apply (o : SignedFlowOrientation G A)
    (F : OpenEdgeIndex G A → ℝ) (v : V) :
    signedDivergence G A o F v =
      (∑ e : OpenEdgeIndex G A, if o.source e = v then F e else 0) -
      (∑ e : OpenEdgeIndex G A, if o.target e = v then F e else 0) := by
  change (∑ e : OpenEdgeIndex G A, signedIncidenceMatrix G A o e v * F e) = _
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [signedIncidenceMatrix]
  by_cases hs : v = o.source e
  · subst v; simp [(signedFlow_source_ne_target G A o e).symm]
  · by_cases ht : v = o.target e
    · subst v; simp [hs, signedFlow_source_ne_target G A o e]
    · simp [hs, ht, eq_comm]

theorem signedGradient_ker_eq_componentConstantFunctions
    (o : SignedFlowOrientation G A) :
    LinearMap.ker (signedGradient G A o) =
      componentConstantFunctions G (BoundaryCondition.free (∅ : Set V)) A := by
  ext f
  rw [LinearMap.mem_ker, funext_iff, componentConstant_iff_local]
  simp only [signedGradient_apply, Pi.zero_apply, sub_eq_zero]
  constructor
  · intro h
    refine ⟨fun {u v} hadj => ?_, fun {u v} hboundary =>
      congrArg f ((BoundaryCondition.free_rel (∅ : Set V) u v).mp hboundary)⟩
    rcases (openGraph_adj G A u v).mp hadj with ⟨edge, hedgeA, hval⟩
    let e : OpenEdgeIndex G A := ⟨edge, by simpa using hedgeA⟩
    have hpair : s(u, v) = s(o.source e, o.target e) := by rw [o.endpoints e, hval]
    rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h e
    · exact (h e).symm
  · rintro ⟨hopen, _⟩ e
    exact hopen ((openGraph_adj G A _ _).2 ⟨e.1, by simp, (o.endpoints e).symm⟩)

theorem signedFlowDimension (o : SignedFlowOrientation G A) :
    Module.finrank ℝ (LinearMap.ker (signedDivergence G A o)) + Fintype.card V =
      A.card + componentCount G (BoundaryCondition.free (∅ : Set V)) A := by
  classical
  let bV : Module.Basis V ℝ (V → ℝ) := Pi.basisFun ℝ V
  let bE : Module.Basis (OpenEdgeIndex G A) ℝ (OpenEdgeIndex G A → ℝ) :=
    Pi.basisFun ℝ (OpenEdgeIndex G A)
  have hgrad := LinearMap.finrank_range_add_finrank_ker (signedGradient G A o)
  have hmapG : Matrix.toLin bV bE (signedIncidenceMatrix G A o) = signedGradient G A o := by
    simp [signedGradient, bV, bE, Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
  have hmapD : Matrix.toLin bE bV ((signedIncidenceMatrix G A o)ᵀ) = signedDivergence G A o := by
    simp [signedDivergence, bV, bE, Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
  have hrG : Module.finrank ℝ (LinearMap.range (signedGradient G A o)) =
      (signedIncidenceMatrix G A o).rank := by
    rw [← hmapG]; exact (Matrix.rank_eq_finrank_range_toLin _ bE bV).symm
  have hrD : Module.finrank ℝ (LinearMap.range (signedDivergence G A o)) =
      (signedIncidenceMatrix G A o).rank := by
    rw [← hmapD, ← Matrix.rank_transpose]; exact (Matrix.rank_eq_finrank_range_toLin _ bV bE).symm
  rw [signedGradient_ker_eq_componentConstantFunctions G A o,
    componentConstantFunctions_finrank, Module.finrank_fintype_fun_eq_card, hrG] at hgrad
  have hdiv := LinearMap.finrank_range_add_finrank_ker (signedDivergence G A o)
  rw [hrD, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hdiv
  omega

end
end PottsDiscontinuity.FK
