import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex


namespace FiniteChains.TopologicalSingular
open CategoryTheory

/-- A chain map is injective on homology when every cycle whose image bounds
already bounds in the source complex. -/
theorem shortComplex_homologyMap_injective_of_reflects_boundaries
    {S T : ShortComplex (ModuleCat ℤ)} (φ : S ⟶ T)
    (h : ∀ c, S.g c = 0 →
      (∃ b, T.f b = φ.τ₂ c) → ∃ a, S.f a = c) :
    Function.Injective (ShortComplex.homologyMap φ) := by
  have hzero : ∀ q, (ShortComplex.homologyMap φ) q = 0 → q = 0 := by
    intro q hq
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance q
    have hy := congrArg (· y) S.iCycles_g
    have ht : T.pOpcycles (φ.τ₂ (S.iCycles y)) = 0 := by
      have he := congrArg (· y) (ShortComplex.π_homologyMap_ι φ)
      change T.homologyι ((ShortComplex.homologyMap φ) (S.homologyπ y)) =
        T.pOpcycles (φ.τ₂ (S.iCycles y)) at he
      simp_all
    obtain ⟨a, ha⟩ := h _ hy ((T.moduleCat_pOpcycles_eq_zero_iff _).mp ht)
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [map_zero]
    have he := congrArg (· y) S.homology_π_ι
    change S.homologyι (S.homologyπ y) = S.pOpcycles (S.iCycles y) at he
    rw [he]
    exact (S.moduleCat_pOpcycles_eq_zero_iff _).mpr ⟨a, ha⟩
  intro a b hab
  apply sub_eq_zero.mp
  simp_all

theorem shortComplex_homologyMap_mono_of_reflects_boundaries
    {S T : ShortComplex (ModuleCat ℤ)} (φ : S ⟶ T)
    (h : ∀ c, S.g c = 0 →
      (∃ b, T.f b = φ.τ₂ c) → ∃ a, S.f a = c) :
    Mono (ShortComplex.homologyMap φ) :=
  (ModuleCat.mono_iff_injective _).mpr (shortComplex_homologyMap_injective_of_reflects_boundaries φ h)
