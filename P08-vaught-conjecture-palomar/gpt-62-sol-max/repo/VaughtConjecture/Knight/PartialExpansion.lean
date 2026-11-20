/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionInjectivity

@[expose] public section

namespace VaughtConjecture.Knight.PartialExpansion

open TypeTower KnightRealization

universe w w'

variable {M : Type w} {σ τ ρ : Ordinal.{0}}

/-- Realizations admitting an actual model expansion on the same carrier. -/
abbrev Domain (h : σ ≤ ρ) (M : Type w) :=
  {R : KnightRealization (blockStage σ) M //
    R.ProlongsToOnIn IsModelClass (blockStage_mono h)}

/-- Expansion is only defined on its existence domain. -/
noncomputable def value (h : σ ≤ ρ) (R : Domain h M) : KnightRealization (blockStage ρ) M :=
  R.2.choose

theorem isModel (h : σ ≤ ρ) (R : Domain h M) : (value h R).IsModel :=
  R.2.choose_spec.1

@[simp] theorem reduct_value (h : σ ≤ ρ) (R : Domain h M) :
    (value h R).reduct (blockStage_mono h) = R.1 :=
  R.2.choose_spec.2

/-- Independence from the particular expansion witness, not merely from its existence proof. -/
theorem value_eq (h : σ ≤ ρ) (R : Domain h M)
    {W : KnightRealization (blockStage ρ) M} (hW : W.IsModel)
    (hWR : W.reduct (blockStage_mono h) = R.1) : value h R = W :=
  eq_of_reduct_eq_of_le ρ σ h _ _ (isModel h R) hW ((reduct_value h R).trans hWR.symm)

/-- Independently supplied existence proofs at two heights produce coherent values. -/
theorem coherent (hστ : σ ≤ τ) (hτρ : τ ≤ ρ)
    (R : Domain (hστ.trans hτρ) M) (S : Domain hστ M) (hRS : R.1 = S.1) :
    (value (hστ.trans hτρ) R).reduct (blockStage_mono hτρ) = value hστ S := by
  apply (value_eq hστ S ((isModel _ R).reduct _) ?_).symm
  rw [Realization.reduct_reduct, reduct_value, hRS]

end VaughtConjecture.Knight.PartialExpansion
