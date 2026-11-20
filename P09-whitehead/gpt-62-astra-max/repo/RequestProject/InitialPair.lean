module

public import Mathlib

@[expose] public section

open scoped commutatorElement

/-!
# The group computation of Lemma 3.1

Lemma 3.1 builds, over an acyclic complex `D` with presentation
`⟨x_i (i ∈ I) | r_j (j ∈ J)⟩` and exponent-sum matrix `M`, the complex

  `Y_D = ⟨x_i, a_i, b_i | r_j, x_i[a_i,b_i]⁻¹, [a_i,a_k], [a_i,b_k], [b_i,a_k], [b_i,b_k]⟩`,

and computes `G(Y_D) = ⊕_i (ℤ a_i ⊕ ℤ b_i)`.  The group-theoretic heart of that
computation is the elimination step proved here: after `x_i` has been eliminated
by `x_i = [a_i, b_i]`, the cross-commutators make the elements
`U_i = [a_i, b_i]` commute, the relators `r_j` become `∏_i U_i^{M_{ij}} = 1`,
and surjectivity of the exponent-sum matrix `M` — which holds because `D` is
acyclic, `M` being then an isomorphism — forces `U_i = 1` for every `i`.
Consequently all the generators `a_i, b_i` commute.

Only this group theory is formalized; the passage from the complex to the
presentation, and the homotopy-theoretic half of Lemma 3.1 (Cockcroftness of
`Y_D` and the vanishing on `π₂`), are not.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

variable {G : Type*} [Group G] {I J : Type*}

/-- The commutator `U i = ⁅a i, b i⁆` of the `i`-th added pair of generators. -/
def pairComm (a b : I → G) (i : I) : G := ⁅a i, b i⁆

/-- The cross-commutator relations of `Y_D`: generators with different indices commute. -/
def CrossCommuting (a b : I → G) : Prop :=
  ∀ i k : I, i ≠ k →
    Commute (a i) (a k) ∧ Commute (a i) (b k) ∧ Commute (b i) (a k) ∧ Commute (b i) (b k)

/-- The cross-commutators make the elements `U_i` commute. -/
theorem commute_pairComm (a b : I → G) (hab : CrossCommuting a b) (i k : I) :
    Commute (pairComm a b i) (pairComm a b k) := by
  classical
  by_cases hik : i = k
  · subst hik; exact Commute.refl _
  · obtain ⟨haa, hab', hba, hbb⟩ := hab i k hik
    have ha : Commute (a i) (pairComm a b k) :=
      ((haa.mul_right hab').mul_right haa.inv_right).mul_right hab'.inv_right
    have hb : Commute (b i) (pairComm a b k) :=
      ((hba.mul_right hbb).mul_right hba.inv_right).mul_right hbb.inv_right
    exact ((ha.mul_left hb).mul_left ha.inv_left).mul_left hb.inv_left

end FiniteChains
