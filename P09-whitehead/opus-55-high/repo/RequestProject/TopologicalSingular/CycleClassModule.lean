import RequestProject.TopologicalSingular.CycleClasses
import RequestProject.Tac


bwd

namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u

theorem shortComplexCycleClass_smul S
    r c hc :
    shortComplexCycleClass S (r • c) (by rw [map_zsmul, hc, zsmul_zero]) =
      r • shortComplexCycleClass S c hc := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp [map_zsmul, shortComplexCycleClass_i]

theorem shortComplexCycleClass_surjective S
    q : ∃ (c : S.X₂) (hc : S.g c = 0), shortComplexCycleClass S c hc = q := by
  cases' (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance q with y hy
  have hc := congrArg (· y) S.iCycles_g
  refine ⟨S.iCycles y, hc, ?_⟩
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i, ← hy]
  exact (congrArg (· y) S.homology_π_ι).symm

variable {X : Type u} [TopologicalSpace X]

theorem singularCycleClass_smul n (r : ℤ) (c : Chain X (n + 1)) hc :
    singularCycleClass n (r • c) (by simp_all) =
      r • singularCycleClass n c hc := by
  simpa [singularCycleClass, int_smul_eq_zsmul] using
    (shortComplexCycleClass_smul ((complex X).sc (n + 1)) r c _)

/-- Taking a homology class is linear on the actual kernel of the boundary. -/
noncomputable def singularCycleClassLinear n :
    LinearMap.ker (boundary (X := X) n) →ₗ[ℤ] (complex X).homology (n + 1) where
  toFun c := singularCycleClass n c.val c.property
  map_add' c d := singularCycleClass_add n c.val d.val c.property d.property
  map_smul' r c := (singularCycleClass_smul n r c.val c.property).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ ((complex X).homology (n + 1))) r _).symm

theorem singularCycleClass_representative n q :
    ∃ (c : Chain X (n + 1)) (hc : boundary n c = 0), singularCycleClass n c hc = q := by
  obtain ⟨c, hc, hq⟩ := shortComplexCycleClass_surjective _ q
  have hz : boundary n c = 0 := by
    change (complex X).d _ _ c = 0 at hc
    rwa [ChainComplex.next_nat_succ, complex_d] at hc
  tauto
