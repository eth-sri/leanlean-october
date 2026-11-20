module

public import RequestProject.TopologicalSingular.SingularChainHomotopy

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u

variable (S : ShortComplex (ModuleCat.{u} ℤ))

variable (c : S.X₂) (hc : S.g c = 0)

noncomputable def shortComplexCycleClass :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨c, hc⟩)

theorem shortComplexCycleClass_i :
    S.homologyι (shortComplexCycleClass S c hc) = S.pOpcycles c := by
  have he := congrArg (fun f => f (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) S.homology_π_ι
  change S.homologyι (shortComplexCycleClass S c hc) =
    S.pOpcycles (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (fun f => f ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  simp_all

theorem shortComplexCycleClass_eq_iff
    (c d : S.X₂) (hc : S.g c = 0) (hd : S.g d = 0) :
    shortComplexCycleClass S c hc = shortComplexCycleClass S d hd ↔
      c - d ∈ LinearMap.range S.f.hom := by
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_iff c d).mp
    simpa only [shortComplexCycleClass_i] using congrArg S.homologyι h
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [shortComplexCycleClass_i, shortComplexCycleClass_i]
    exact (S.moduleCat_pOpcycles_eq_iff c d).mpr h

theorem shortComplexCycleClass_zero :
    shortComplexCycleClass S 0 (map_zero S.g.hom) = 0 := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp [shortComplexCycleClass_i, map_zero]

theorem shortComplexCycleClass_add
    (c d : S.X₂) (hc : S.g c = 0) (hd : S.g d = 0) :
    shortComplexCycleClass S (c + d) (by simp_all) =
      shortComplexCycleClass S c hc + shortComplexCycleClass S d hd := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp [map_add, shortComplexCycleClass_i]

theorem shortComplexCycleClass_natural {S T : ShortComplex (ModuleCat.{u} ℤ)}
    (φ : S ⟶ T) (c : S.X₂) (hc : S.g c = 0) (ht : T.g _ = 0) :
    (ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc) =
      shortComplexCycleClass T (φ.τ₂ c) ht := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i]
  have he := congrArg (fun f => f (S.moduleCatCyclesIso.inv ⟨c, hc⟩))
    (ShortComplex.π_homologyMap_ι φ)
  change T.homologyι ((ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc)) =
    T.pOpcycles (φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩))) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (fun f => f ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  simp_all

variable {X : Type u} [TopologicalSpace X]

variable (n : ℕ)

theorem singularCycle_condition {c : Chain X _} (hc : boundary n c = 0) :
    ((complex X).sc _).g c = 0 := by
  change (complex X).d _ _ c = 0
  rw [ChainComplex.next_nat_succ, complex_d]
  exact hc

/-- The actual Mathlib homology class of an explicit positive-degree cycle. -/
noncomputable def singularCycleClass (c : Chain X _) (hc : boundary n c = 0) :
    (complex X).homology (n + 1) :=
  shortComplexCycleClass _ c (singularCycle_condition n hc)

theorem singularCycleClass_eq_iff (c d : Chain X _)
    (hc : boundary n c = 0) (hd : boundary n d = 0) :
    singularCycleClass n c hc = singularCycleClass n d hd ↔
      c - d ∈ LinearMap.range (boundary _) := by
  rw [singularCycleClass, singularCycleClass, shortComplexCycleClass_eq_iff]
  change c - d ∈ LinearMap.range
    ((complex X).d _ _).hom ↔ _
  rw [ChainComplex.prev, complex_d]
  rfl

theorem singularCycleClass_zero : singularCycleClass (X := X) n 0 (map_zero _) = 0 :=
  shortComplexCycleClass_zero _

theorem singularCycleClass_add (c d : Chain X _)
    (hc : boundary n c = 0) (hd : boundary n d = 0) :
    singularCycleClass n (c + d) (by simp_all) =
      singularCycleClass n c hc + singularCycleClass n d hd :=
  by apply shortComplexCycleClass_add

theorem singularCycleClass_natural {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) (c : Chain X _) (hc : boundary n c = 0) :
    (HomologicalComplex.homologyMap (chainMap f) _) (singularCycleClass n c hc) =
      singularCycleClass n (map f _ c) (by rw [← map_boundary, hc, map_zero]) := by
  apply shortComplexCycleClass_natural

end FiniteChains.TopologicalSingular
