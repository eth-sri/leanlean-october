/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.ModelTheory.CountingCountable
public import InfinitaryLogic.Descriptive.BFEquivBorel
public import Architect

/-!
# Morley's Counting Theorem via Scott-Height Stratification

This file proves the full Morley counting theorem: for any Lω₁ω sentence φ,
the number of isomorphism classes of countable models is either ≤ ℵ₁ or exactly
2^ℵ₀. The theorem is parametrized by the Silver–Burgess dichotomy
(`SilverBurgessDichotomy`), which the repository proves unconditionally
(`silverBurgessDichotomy` in `Conditional/GandyHarrington.lean`, via the
classical `G₀`-dichotomy route); supplying it makes the conclusion axiom-clean.

The proof stratifies by Scott height. For each α < ω₁, BFEquiv_α is a Borel
equivalence relation on ModelsOf φ, coarser than isomorphism. If any BFEquiv_α
has 2^ℵ₀ classes, iso has ≥ 2^ℵ₀ hence = 2^ℵ₀. If all have ≤ ℵ₀, then for
each α, the iso classes with height ≤ α inject into BFEquiv_α classes, giving
≤ ℵ₀ iso classes per stratum, hence ≤ ℵ₁ total over ω₁ strata.

## Main Result

- `morley_counting`: Morley counting theorem for all countable models, parametrized
  by `SilverBurgessDichotomy` (proved in this repository).
-/

@[expose] public section

universe u v

namespace FirstOrder

namespace Language

open Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ### BFEquiv setoid on coded models -/

/-- The BFEquiv α equivalence relation on coded ℕ-models of φ (at the empty tuple). -/
def bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Setoid ↥(ModelsOf φ) where
  r c₁ c₂ := @BFEquiv L ℕ c₁.1.toStructure ℕ c₂.1.toStructure α 0 Fin.elim0 Fin.elim0
  iseqv := by
    refine ⟨fun c => ?_, fun {c₁ c₂} h => ?_, fun {c₁ c₂ c₃} h₁ h₂ => ?_⟩
    · exact @BFEquiv.refl L ℕ c.1.toStructure 0 α Fin.elim0
    · exact @BFEquiv.symm L ℕ c₁.1.toStructure ℕ c₂.1.toStructure 0 α
        Fin.elim0 Fin.elim0 h
    · exact @BFEquiv.trans L ℕ c₁.1.toStructure ℕ c₂.1.toStructure
        ℕ c₃.1.toStructure (n := 0) (α := α)
        (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0) h₁ h₂

omit [Countable (Σ l, L.Relations l)] in
/-- Iso implies BFEquiv α: isoSetoid refines bfEquivSetoid. -/
theorem isoSetoid_refines_bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0})
    {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ → (bfEquivSetoid φ α).r c₁ c₂ := by
  intro ⟨e⟩
  unfold bfEquivSetoid
  simp only
  conv_rhs => rw [show (Fin.elim0 : Fin 0 → ℕ) = e ∘ Fin.elim0 from
    (comp_fin_elim0 e).symm]
  exact @equiv_implies_BFEquiv L ℕ ℕ c₁.1.toStructure c₂.1.toStructure e α 0 Fin.elim0



omit [Countable (Σ l, L.Relations l)] in
/-- The depth-`α` projection of isomorphism classes onto back-and-forth classes. -/
def bfProj (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Quotient (isoSetoid φ) → Quotient (bfEquivSetoid φ α) :=
  Quotient.map id (fun _a _b h => isoSetoid_refines_bfEquivSetoid φ α h)

omit [Countable (Σ l, L.Relations l)] in
@[simp] theorem bfProj_mk (φ : L.Sentenceω) (α : Ordinal.{0}) (c : ↥(ModelsOf φ)) :
    bfProj φ α (Quotient.mk _ c) = Quotient.mk _ c := rfl





/-! ### Height function on iso classes -/



/-! ### Morley counting: ℕ-coded models -/








/-! ### Full Morley counting theorem -/


end Language

end FirstOrder
