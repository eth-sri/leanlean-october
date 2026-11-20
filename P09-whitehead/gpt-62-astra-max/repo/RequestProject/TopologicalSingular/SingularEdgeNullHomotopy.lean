module

public import RequestProject.TopologicalSingular.SimplexPrismRetraction
public import RequestProject.TopologicalSingular.SingularPathHomotopy
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X]

theorem simplexOne_boundary_endpoints (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    stdSimplexHomeomorphUnitInterval z = 0 ∨ stdSimplexHomeomorphUnitInterval z = 1 := by
  have hs := (Fin.sum_univ_two z.val).symm.trans z.property.2
  obtain ⟨i, hi⟩ := hz
  fin_cases i
  · right
    apply Subtype.ext <;> simp_all
  · left
    apply Subtype.ext
    exact hi

/-- In a simply connected space, a singular edge whose two vertices are at
the basepoint contracts to the constant edge while fixing both vertices. -/
theorem singularEdge_nullhomotopic [SimplyConnectedSpace X] (x : X) (tau : Simplex X 1)
    (h0 : tau (stdSimplex.vertex 0) = x) (h1 : tau (stdSimplex.vertex 1) = x) :
    Nonempty (ContinuousMap.HomotopyRel tau (ContinuousMap.const (Domain 1) x) (simplexBoundary 1)) := by
  let p : Path x x := {
    toFun := fun t => tau _
    continuous_toFun := tau.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
    source' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_zero.symm)).trans h0
    target' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_one.symm)).trans h1 }
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x)
  refine ⟨{
    toFun := fun w => G _
    continuous_toFun := G.continuous.comp (continuous_fst.prodMk
      (stdSimplexHomeomorphUnitInterval.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · aesop
  · simp
  · intro t z hz
    rcases simplexOne_boundary_endpoints z hz with he | he
    · have hv := stdSimplexHomeomorphUnitInterval.injective
        (he.trans stdSimplexHomeomorphUnitInterval_zero.symm)
      simp_all
    · have hv := stdSimplexHomeomorphUnitInterval.injective
        (he.trans stdSimplexHomeomorphUnitInterval_one.symm)
      simp_all

end FiniteChains.TopologicalSingular
