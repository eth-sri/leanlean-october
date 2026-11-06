module

public import RequestProject.Oriented

public import RequestProject.PresUnivCoverIso
public import RequestProject.Cockcroft
public import RequestProject.CockcroftExtension

@[expose] public section

backwardOptions



/-!
# The Cockcroft property: the topological definition and the Fox one agree

Two definitions of "Cockcroft" occur in this development.

* `FiniteChains.Comb.IsCockcroft X` — the topological one, used by the interface
  `FiniteChains.combData` of Theorem A: the Hurewicz map `π₂(X) → H₂(X)` vanishes, where
  `π₂(X)` is the module of two-cycles of the universal cover built from homotopy classes of
  edge paths and the Hurewicz map pushes such a cycle down to `X`.
* `FiniteChains.IsCockcroft ρ` — the one used throughout Section 3: every Fox cycle of the
  presentation has zero augmentation.

Using the identification of the two models of the universal cover
(`RequestProject/PresUnivCoverIso.lean`) this file proves that for the complex of a finite
presentation the two agree: `FiniteChains.Comb.isCockcroft_presComplex_iff`.
-/


namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] in
/-- **The augmentation of the coordinates is the pushforward to the base.**  Summing the
coefficients of a cellular two-chain of the cover over a fibre is the same as augmenting its
coordinate vector. -/
theorem augQ_coords (v : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ) (j : J) :
    augQ (relSub ρ) (coords (relSub ρ) J v j) = Finsupp.mapDomain Prod.snd v j := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [map_add, Finsupp.mapDomain_add]
      simp only [Finsupp.add_apply, Pi.add_apply, map_add] at *
      rw [hv, hw]
  | single qj n =>
      obtain ⟨q, j₀⟩ := qj
      rw [coords_single, Finsupp.mapDomain_single]
      by_cases h : j = j₀
      · subst h
        simp
      · rw [Pi.single_eq_of_ne h, Finsupp.single_apply, if_neg (Ne.symm h), map_zero]

end Comb
end FiniteChains
