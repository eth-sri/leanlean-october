module

public import RequestProject.TopologicalSingular.Pi2HurewiczMap
public import RequestProject.TopologicalSingular.SquareSubdivisionPrism
public import RequestProject.TopologicalSingular.SquareConcatenationGeometry

@[expose] public section

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X : Type} [TopologicalSpace X] {x : X}

variable (p q : GenLoop (Fin 2) X x)

theorem squareCycle_transAt_difference_bounds :
    squareCycle p + squareCycle q - squareCycle (GenLoop.transAt 0 p q) ∈
      LinearMap.range (boundary 2) := by
  have he := squareCycle_rectangle_sum_difference_bounds (GenLoop.transAt 0 p q)
  rwa [transAt_leftRectangle, transAt_rightRectangle] at he

theorem squareCycleClass_transAt :
    singularCycleClass 1 (squareCycle (GenLoop.transAt 0 p q)) (squareCycle_boundary _) =
      singularCycleClass 1 _ (squareCycle_boundary p) +
        singularCycleClass 1 _ (squareCycle_boundary q) := by
  rw [← singularCycleClass_add]
  apply Eq.symm
  exact (singularCycleClass_eq_iff 1 _ _ _ _).mpr (squareCycle_transAt_difference_bounds p q)

variable (x : X)

variable (a b : HomotopyGroup (Fin 2) X x)

theorem pi2CycleClass_mul :
    pi2CycleClass x (a * b) = pi2CycleClass x a + pi2CycleClass x b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      calc
        _ = pi2CycleClass x _ :=
          congrArg _ (HomotopyGroup.mul_spec (i := 0) (p := p) (q := q))
        _ = _ := by
          simp [pi2CycleClass_mk, squareCycleClass_transAt, add_comm]

variable {x}

/-- Vanishing of the genuine Hurewicz image is exactly the existence of an
integral singular filling of the square's fundamental cycle. -/
theorem singularHurewicz2_mk_eq_zero_iff (p : GenLoop _ X x) :
    singularHurewicz2 x (Quotient.mk _ p) = 0 ↔
      ∃ b : Chain X 3, boundary 2 b = squareCycle p := by
  have hi := (ModuleCat.mono_iff_injective (homologyMathlibIso (TopCat.of X) 2).hom).mp
    inferInstance
  have he : singularHurewicz2 x (Quotient.mk _ p) = 0 ↔
      singularCycleClass 1 _ (squareCycle_boundary p) = 0 := by
    constructor
    · intro h
      apply hi
      rw [map_zero]
      exact h
    · intro h
      change (homologyMathlibIso (TopCat.of X) 2).hom
        (singularCycleClass 1 (squareCycle p) (squareCycle_boundary p)) = 0
      simp_all
  rw [he]
  constructor
  · intro h
    have hc := (singularCycleClass_eq_iff 1 _ 0 (squareCycle_boundary p) _).mp
      (h.trans (singularCycleClass_zero 1).symm)
    simp_all
  · intro h
    have hc := (singularCycleClass_eq_iff 1 _ 0 (squareCycle_boundary p) (map_zero _)).mpr
      (by simp_all)
    exact hc.trans (singularCycleClass_zero 1)

end FiniteChains.TopologicalSingular
