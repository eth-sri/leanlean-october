import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import RequestProject.Tac


bwd

namespace FiniteChains
universe u v
variable {G : Type u} {I : Type v}

/-- Integer coefficients on group/cell pairs are the corresponding group-ring cell coefficients. -/
noncomputable def groupCellChainEquiv :
    (G × I →₀ ℤ) ≃ₗ[ℤ] (I →₀ MonoidAlgebra ℤ G) :=
  ((Finsupp.domLCongr (R := ℤ) (M := ℤ) (Equiv.prodComm G I)).trans
    (Finsupp.curryLinearEquiv ℤ)).trans
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv (S := ℤ) (M := G) ℤ).symm)

/-- Actual individual incidences keep their group coefficient and cell label under reindexing. -/
theorem groupCellChainEquiv_single (g : G) (i : I) n :
    groupCellChainEquiv (Finsupp.single (g, i) n) =
      Finsupp.single i (MonoidAlgebra.single g n) := by
  simp only [groupCellChainEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single,
    Finsupp.mapRange.linearEquiv_apply]
  simp
