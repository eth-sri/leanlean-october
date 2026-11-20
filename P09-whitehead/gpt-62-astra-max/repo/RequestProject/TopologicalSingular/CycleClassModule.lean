module

public import RequestProject.TopologicalSingular.CycleClasses

@[expose] public section

namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u

variable (S : ShortComplex (ModuleCat.{u} ℤ))

theorem shortComplexCycleClass_smul
    (r : ℤ) (c : S.X₂) (hc : S.g c = 0) :
    shortComplexCycleClass S (r • c) (by rw [map_zsmul, hc, zsmul_zero]) =
      r • shortComplexCycleClass S c hc := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp only [map_zsmul, shortComplexCycleClass_i]

theorem shortComplexCycleClass_surjective
    (q : S.homology) : ∃ (c : S.X₂) (hc : S.g c = 0), shortComplexCycleClass S c hc = q := by
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance q
  refine ⟨S.iCycles y, (congrArg (fun f => f y) S.iCycles_g), ?_⟩
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i, ← hy]
  exact (congrArg (fun f => f y) S.homology_π_ι).symm

variable {X : Type u} [TopologicalSpace X]

variable (n : ℕ)

theorem singularCycleClass_smul (r : ℤ) (c : Chain X _) (hc : boundary n c = 0) :
    singularCycleClass n (r • c) (by simp_all) =
      r • singularCycleClass n c hc := by
  solve_by_elim [shortComplexCycleClass_smul, singularCycle_condition]

/-- Taking a homology class is linear on the actual kernel of the boundary. -/
noncomputable def singularCycleClassLinear :
    LinearMap.ker (boundary (X := X) n) →ₗ[ℤ] (complex X).homology (n + 1) where
  toFun c := singularCycleClass n c.val c.property
  map_add' c d := singularCycleClass_add n c.val d.val c.property d.property
  map_smul' r c := (singularCycleClass_smul n r c.val c.property).trans
      (int_smul_eq_zsmul inferInstance r _).symm

theorem singularCycleClass_representative (q : (complex X).homology _) :
    ∃ (c : Chain X _) (hc : boundary n c = 0), singularCycleClass n c hc = q := by
  obtain ⟨c, hc, hq⟩ := shortComplexCycleClass_surjective _ q
  have hz : boundary n c = 0 := by
    change (complex X).d _ _ c = 0 at hc
    rw [ChainComplex.next_nat_succ, complex_d] at hc
    exact hc
  solve_by_elim

end FiniteChains.TopologicalSingular
