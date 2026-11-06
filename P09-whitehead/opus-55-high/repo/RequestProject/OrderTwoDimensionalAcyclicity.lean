import RequestProject.OrderNerveHomologyDimension
import RequestProject.OrderNervePositiveFillings
import RequestProject.TopologicalSingular.MathlibH1Comparison
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable (P : Type) [PartialOrder P]

/-- In dimension two the first and second actual singular homology groups
are the only positive-degree obstructions to the acyclicity in Challenge. -/
theorem orderRealization_acyclic_iff_homology_one_two [(nerve P).HasDimensionLE 2] :
    Whitehead.Acyclic (orderNerveRealization P) ↔
      Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) ∧
      Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  constructor
  · tauto
  · rintro ⟨h1, h2⟩ n hn
    by_cases he1 : n = 1
    · simp_all
    by_cases he2 : n = 2
    · simp_all
    exact orderNerve_singularHomology_isZero_of_dimension P 2 n (by omega)

/-- Genuine finite fillings in the order nerve annihilate actual singular H2. -/
theorem orderRealization_homology_two_isZero_of_fillings
    (hfill : ∀ c : OrdTri P →₀ ℤ, bdry2 (orderCx P) c = 0 →
      ∃ b, ordBoundary3 b = c) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  have hz (z : OrderNerveH2 P) : z = 0 := by
    induction z using Submodule.Quotient.induction_on with
    | H c =>
      exact (orderNerveH2Class_eq_zero_iff P c.val c.property).mpr
        (hfill c.val c.property)
  letI : Subsingleton (OrderNerveH2 P) := ⟨by simp_all⟩
  letI := (orderCellSingularH2Equiv P).surjective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- The weak nerve's degenerate chains introduce no extra H2 obstruction. -/
theorem orderRealization_homology_two_isZero_of_strict_cycles_zero
    (hz : ∀ c : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) c = 0 → c = 0) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  apply orderRealization_homology_two_isZero_of_fillings P
  apply weak_twoCycle_filling_of_strict
  intro c hc
  exact ⟨0, by simp_all⟩
