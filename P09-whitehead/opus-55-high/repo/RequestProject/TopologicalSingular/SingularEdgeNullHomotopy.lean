import RequestProject.TopologicalSingular.SimplexPrismRetraction
import RequestProject.TopologicalSingular.SingularChainH1


namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X]

theorem simplexOne_boundary_endpoints z (hz : z ∈ simplexBoundary 1) :
    stdSimplexHomeomorphUnitInterval z = 0 ∨ stdSimplexHomeomorphUnitInterval z = 1 := by
  have hs : z.val 0 + z.val 1 = 1 := (Fin.sum_univ_two z.val).symm.trans z.property.2
  obtain ⟨i, hi⟩ := hz
  fin_cases i
  · aesop
  aesop

/-- In a simply connected space, a singular edge whose two vertices are at
the basepoint contracts to the constant edge while fixing both vertices. -/
theorem singularEdge_nullhomotopic [SimplyConnectedSpace X] (x : X) (tau : Simplex X 1)
    (h0 : tau (stdSimplex.vertex 0) = x) (h1 : tau (stdSimplex.vertex 1) = x) :
    Nonempty (ContinuousMap.HomotopyRel tau (ContinuousMap.const (Domain 1) x) (simplexBoundary 1)) := by
  let p : Path x x := {
    toFun := fun t => tau (stdSimplexHomeomorphUnitInterval.symm t)
    continuous_toFun := tau.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
    source' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_zero.symm)).trans h0
    target' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_one.symm)).trans h1 }
  cases' SimplyConnectedSpace.paths_homotopic p (Path.refl x) with G
  refine ⟨{
    toFun := fun w => G (w.1, stdSimplexHomeomorphUnitInterval w.2)
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
