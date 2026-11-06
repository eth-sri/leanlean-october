import RequestProject.TopologicalSingular.SquareSingularHomotopy
import RequestProject.TopologicalSingular.CycleClasses
import RequestProject.TopologicalSingular.MathlibComparison
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The homology class obtained from an actual based square. The relative
homotopy proof supplies the required three-dimensional singular filling. -/
def pi2CycleClass x : HomotopyGroup (Fin 2) X x → (complex X).homology 2 :=
  Quotient.lift (fun p => singularCycleClass 1 _ (squareCycle_boundary p))
    (fun _ _ h => (singularCycleClass_eq_iff 1 _ _ _ _).mpr
      (squareCycle_homotopic_difference_bounds h.symm))

theorem pi2CycleClass_mk x (p : GenLoop (Fin 2) X x) :
    pi2CycleClass x (Quotient.mk _ p) = singularCycleClass 1 (squareCycle p) (squareCycle_boundary p) := rfl

theorem pi2CycleClass_one (x : X) : pi2CycleClass x 1 = 0 := by
  change singularCycleClass 1 (squareCycle (GenLoop.const (x := x))) (squareCycle_boundary _) = 0
  simp [squareCycle_const, singularCycleClass_zero]

theorem pi2CycleClass_natural (f : C(X, Y)) x z :
    (HomologicalComplex.homologyMap (chainMap f) 2) (pi2CycleClass x z) =
      pi2CycleClass (f x) (Whitehead.pi2Map f x z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    change (HomologicalComplex.homologyMap (chainMap f) 2)
      (singularCycleClass 1 _ (squareCycle_boundary p)) = singularCycleClass 1
        (squareCycle (Whitehead.mapSquare f p)) (squareCycle_boundary _)
    simpa [squareCycle_map] using
      (singularCycleClass_natural f 1 _ _)

/-- The canonical degree-two Hurewicz function lands in the exact integral
singular homology functor used by Whitehead's statement. Additivity and the
simply-connected isomorphism theorem are separate obligations. -/
def singularHurewicz2 x : HomotopyGroup (Fin 2) X x →
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) :=
  fun z => (homologyMathlibIso _ 2).hom (pi2CycleClass x z)

theorem singularHurewicz2_one (x : X) : singularHurewicz2 x 1 = 0 := by
  rw [singularHurewicz2, pi2CycleClass_one, map_zero]

theorem singularHurewicz2_natural (f : C(X, Y)) x z :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f)).hom (singularHurewicz2 x z)) =
        singularHurewicz2 (f x) (Whitehead.pi2Map f x z) := by
  have he := congrArg (· (pi2CycleClass x z))
    (homologyMathlibIso_natural (TopCat.ofHom f) 2)
  change (homologyMathlibIso (TopCat.of Y) 2).hom
    ((HomologicalComplex.homologyMap (chainMap f) 2) (pi2CycleClass x z)) =
      ((((singularHomologyFunctor _ 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)).hom (singularHurewicz2 x z)) at he
  rw [pi2CycleClass_natural] at he
  exact he.symm

theorem singularHurewicz2_pushdown_zero_of_killsPi2 (f : C(X, Y)) (hf : Whitehead.KillsPi2 f)
    x z :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f)).hom (singularHurewicz2 x z)) = 0 := by
  rw [singularHurewicz2_natural, (Whitehead.killsPi2_iff f).mp hf x z, singularHurewicz2_one]
