module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic

@[expose] public section


namespace MonoidAlgebra

variable {G M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Linear extension of a family indexed by the basis of an integral group ring. -/
noncomputable def linearCombination (f : G → M) : MonoidAlgebra ℤ G →ₗ[ℤ] M :=
  (Finsupp.linearCombination ℤ f).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap


theorem apply_linearCombination (L : M →ₗ[ℤ] N) (f : G → M) (w : MonoidAlgebra ℤ G) :
    L (linearCombination f w) = linearCombination (L ∘ f) w :=
  Finsupp.apply_linearCombination ℤ L f w.coeff


end MonoidAlgebra

namespace FiniteChains
universe u v
variable {G : Type u} {I : Type v}

/-- Integer coefficients on group/cell pairs are the corresponding group-ring cell coefficients. -/
noncomputable def groupCellChainEquiv :
    (G × I →₀ ℤ) ≃ₗ[ℤ] (I →₀ MonoidAlgebra ℤ G) :=
  ((Finsupp.domLCongr (R := ℤ) (M := ℤ) (Equiv.prodComm G I)).trans
    (Finsupp.curryLinearEquiv ℤ)).trans
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv (S := ℤ) (M := G) ℤ).symm)

theorem groupCellChainEquiv_apply (c : (G × I) →₀ ℤ) (i : I) (g : G) :
    (groupCellChainEquiv c i).coeff g = c (g, i) := by
  aesop

/-- Actual individual incidences keep their group coefficient and cell label under reindexing. -/
theorem groupCellChainEquiv_single (g : G) (i : I) (n : ℤ) :
    groupCellChainEquiv (Finsupp.single (g, i) n) =
      Finsupp.single i (MonoidAlgebra.single g n) := by
  simp only [groupCellChainEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single,
    Finsupp.mapRange.linearEquiv_apply]
  simp_all

end FiniteChains
