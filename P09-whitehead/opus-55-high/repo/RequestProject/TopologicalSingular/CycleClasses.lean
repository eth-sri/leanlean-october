import RequestProject.TopologicalSingular.SingularChainHomotopy
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u

def shortComplexCycleClass (S : ShortComplex (ModuleCat.{u} ℤ))
    c (hc : S.g c = 0) :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨c, hc⟩)

theorem shortComplexCycleClass_i (S : ShortComplex (ModuleCat.{u} ℤ))
    c hc :
    S.homologyι (shortComplexCycleClass S c hc) = S.pOpcycles c := by
  have he := congrArg (· (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) S.homology_π_ι
  change S.homologyι (shortComplexCycleClass S c hc) =
    S.pOpcycles (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (· ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  simp_all

theorem shortComplexCycleClass_eq_iff S
    c d hc hd :
    shortComplexCycleClass S c hc = shortComplexCycleClass S d hd ↔
      c - d ∈ LinearMap.range S.f.hom := by
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_iff c d).mp
    simpa [shortComplexCycleClass_i] using congrArg S.homologyι h
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [shortComplexCycleClass_i, shortComplexCycleClass_i]
    exact (S.moduleCat_pOpcycles_eq_iff c d).mpr h

theorem shortComplexCycleClass_zero S :
    shortComplexCycleClass S 0 (map_zero S.g.hom) = 0 := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  grind [shortComplexCycleClass_i, map_zero]

theorem shortComplexCycleClass_add S
    c d hc hd :
    shortComplexCycleClass S (c + d) (by simp_all) =
      shortComplexCycleClass S c hc + shortComplexCycleClass S d hd := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp [map_add, shortComplexCycleClass_i]

theorem shortComplexCycleClass_natural {S T : ShortComplex (ModuleCat.{u} ℤ)}
    (φ : S ⟶ T) c hc ht :
    (ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc) =
      shortComplexCycleClass T (φ.τ₂ c) ht := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i]
  have he := congrArg (· (S.moduleCatCyclesIso.inv ⟨c, hc⟩))
    (ShortComplex.π_homologyMap_ι φ)
  change T.homologyι ((ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc)) =
    T.pOpcycles (φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩))) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (· ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  simp_all

variable {X : Type u} [TopologicalSpace X]

theorem singularCycle_condition n {c} (hc : boundary n c = 0) :
    ((complex X).sc (n + 1)).g c = 0 := by
  change (complex X).d _ _ c = 0
  rw [ChainComplex.next_nat_succ, complex_d]
  exact hc

/-- The actual Mathlib homology class of an explicit positive-degree cycle. -/
def singularCycleClass n (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    (complex X).homology (n + 1) :=
  shortComplexCycleClass _ c (singularCycle_condition n hc)

theorem singularCycleClass_eq_iff n (c d : Chain X (n + 1))
    hc hd :
    singularCycleClass n c hc = singularCycleClass n d hd ↔
      c - d ∈ LinearMap.range (boundary (n + 1)) := by
  rw [singularCycleClass, singularCycleClass, shortComplexCycleClass_eq_iff]
  change c - d ∈ LinearMap.range
    ((complex X).d _ _).hom ↔ _
  rw [ChainComplex.prev, complex_d]
  rfl

theorem singularCycleClass_zero n : singularCycleClass (X := X) n 0 (map_zero _) = 0 :=
  shortComplexCycleClass_zero _

theorem singularCycleClass_add n (c d : Chain X (n + 1))
    hc hd :
    singularCycleClass n (c + d) (by simp_all) =
      singularCycleClass n c hc + singularCycleClass n d hd :=
  shortComplexCycleClass_add _ _ _ _ _

theorem singularCycleClass_natural {Y} [TopologicalSpace Y] (f : C(X, Y))
    n c hc :
    (HomologicalComplex.homologyMap (chainMap f) (n + 1)) (singularCycleClass n c hc) =
      singularCycleClass n (map f (n + 1) c) (by rw [← map_boundary, hc, map_zero]) := shortComplexCycleClass_natural
    ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map
      (chainMap f)) c _ _
