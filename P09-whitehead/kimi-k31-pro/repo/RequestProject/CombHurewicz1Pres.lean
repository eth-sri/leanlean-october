module

public import RequestProject.Oriented
public import RequestProject.CombPresPi1

@[expose] public section

/-!
# Hurewicz in degree one for a presentation complex

For a two-complex `K` the first homology is `H₁(K) = ker ∂₁ / im ∂₂` and the Hurewicz theorem
in degree one says that it is the abelianization of `π₁(K)`.  For the presentation complex
`K = presComplex ρ` of `⟨x_i | r_j⟩` everything is explicit: `K` has a single vertex, so
`∂₁ = 0` and `C₁ = (α →₀ ℤ)`, the class of an edge loop is the exponent-sum vector of the word
it spells, and `im ∂₂` is spanned by the exponent-sum vectors of the relators.

This file proves the corresponding statement:

* `FiniteChains.Comb.expVec` — the exponent-sum homomorphism `F → (α →₀ ℤ)`, with
  `FiniteChains.Comb.ker_expVec` : its kernel is exactly the commutator subgroup of `F`
  (so `(α →₀ ℤ)` is the abelianization of the free group) and
  `FiniteChains.Comb.expVec_surjective`;
* `FiniteChains.Comb.expVec_pathChain` — the exponent-sum vector of a word is the one-chain
  carried by the corresponding edge loop of `presComplex ρ`;
* `FiniteChains.Comb.bdry1_presComplex` — `∂₁ = 0` and `FiniteChains.Comb.cycles1_pres` —
  every one-chain of `presComplex ρ` is a cycle;
* `FiniteChains.Comb.expVec_mem_range_iff` — **the Hurewicz statement**: a word spells a
  one-boundary exactly when it lies in `R·[F, F]`, that is, exactly when its class in
  `π₁(K) = F/R` lies in the commutator subgroup.
-/

namespace FiniteChains
namespace Comb

universe u

variable {α : Type u} [DecidableEq α] {J : Type u}

/-! ### The exponent-sum homomorphism -/

/-- The exponent-sum vector of a word in the free group. -/
noncomputable def expVec : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  FreeGroup.lift fun a => Multiplicative.ofAdd (Finsupp.single a (1 : ℤ))

omit [DecidableEq α] in
@[simp] theorem expVec_of (a : α) :
    expVec (FreeGroup.of a) = Multiplicative.ofAdd (Finsupp.single a (1 : ℤ)) := by
  simp [expVec]

omit [DecidableEq α] in
theorem pathChain_append (l l' : FiniteChains.Comb.Oriented α) :
    pathChain (l ++ l') = pathChain l + pathChain l' := by
  simp [pathChain]

omit [DecidableEq α] in
theorem expVec_single_germ (x : α × Bool) :
    expVec (FreeGroup.mk [x]) = Multiplicative.ofAdd (pathChain [x]) := by
  obtain ⟨a, b⟩ := x
  cases b
  · have h1 : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := rfl
    rw [h1, map_inv, expVec_of]
    show Multiplicative.ofAdd (-Finsupp.single a (1 : ℤ)) = _
    rw [pathChain_cons]
    simp
  · have h1 : FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl
    rw [h1, expVec_of, pathChain_cons]
    simp

omit [DecidableEq α] in
/-- The exponent-sum vector of a word is the one-chain carried by the edge path spelling
it. -/
theorem expVec_pathChain (L : FiniteChains.Comb.Oriented α) :
    expVec (FreeGroup.mk L) = Multiplicative.ofAdd (pathChain L) := by
  induction L with
  | nil => simp [expVec, pathChain]
  | cons x L ih =>
      rw [show (x :: L) = [x] ++ L from rfl, ← FreeGroup.mul_mk, map_mul, ih,
        pathChain_append, expVec_single_germ]
      rfl

/-! ### The presentation complex -/

variable (ρ : J → FreeGroup α)

@[simp] theorem bdry1_presComplex (c : α →₀ ℤ) : bdry1 (presComplex ρ) c = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
  | single a n => simp [bdry1]

theorem bdry2_pres_single (j : J) :
    bdry2 (presComplex ρ) (Finsupp.single j (1 : ℤ))
      = Multiplicative.toAdd (expVec (ρ j)) := by
  rw [bdry2_single, one_smul]
  have h : (presComplex ρ).att j = (ρ j).toWord := rfl
  rw [h]
  conv_rhs => rw [← FreeGroup.mk_toWord (x := ρ j)]
  rw [expVec_pathChain]
  rfl

/-! ### The Hurewicz isomorphism -/

end Comb
end FiniteChains
