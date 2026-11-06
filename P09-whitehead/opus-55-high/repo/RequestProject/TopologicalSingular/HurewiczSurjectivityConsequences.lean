import RequestProject.TopologicalSingular.HurewiczSurjectivity
import RequestProject.Tac


bwd

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [SimplyConnectedSpace X]

/-- A map killing actual pi2 kills every H2 class when its domain is simply
connected, since the Hurewicz images exhaust that domain's H2. -/
theorem singularH2_pushdown_zero_of_killsPi2 (x : X) (f : C(X, Y)) (hf : Whitehead.KillsPi2 f)
    q :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).hom q) = 0 := by
  obtain ⟨a, rfl⟩ := singularHurewicz2_surjective x q
  exact singularHurewicz2_pushdown_zero_of_killsPi2 f hf x a

theorem singularH2_map_eq_zero_of_killsPi2 (x : X) (f : C(X, Y)) (hf : Whitehead.KillsPi2 f) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  exact singularH2_pushdown_zero_of_killsPi2 x f hf q
