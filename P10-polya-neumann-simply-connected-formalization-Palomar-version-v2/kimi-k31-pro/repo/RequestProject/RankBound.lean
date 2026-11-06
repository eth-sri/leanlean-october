module

public import RequestProject.Coercivity

/-!
# Uniform Cayley bound and resonance rank (Lemmas 7.8, 7.9 and Proposition 7.10)

This file formalizes the functional-analytic core of the end of Section 7 of the paper.

* **Lemma 7.8 (reduced lower bound)** `reduced_lower_bound`: if `E ↦ R_E` and `E ↦ S_E` are
  operator-norm continuous at `E₀`, `R_{E₀} = α I + C` with `α > 0`, `C` compact, and `S_{E₀}`
  is injective, then there is `A₀ > 0` with `Re ⟨z, R_E z⟩ ≥ -A₀ ‖S_E z‖²` for all `E` near `E₀`.
  (In the paper `R_E` is the reduced form on the subspace `Z`, on which its pole vanishes, so
  only its regular part enters.)
* **Lemma 7.9 (boundary lower bound with finitely many conditions)** `boundary_lower_bound`:
  the algebraic deduction of `Re ⟨g, 𝒜_E g⟩ ≥ -(A₀ + b) ‖O_E^* g‖²` on `{g : L_E g = 0}` from
  the decomposition identities and the reduced lower bound, where `‖B_E‖ ≤ b`.
* **Proposition 7.10 (uniform Cayley bound and resonance rank)**
  `finrank_le_of_boundary_bound`, `card_le_of_boundary_bound`: under the boundary lower bound
  with `m` linear conditions and the Cayley factorization `⟨g, 𝒜_E g⟩ = -⟨x, K_E x⟩`,
  `x = O_E^* g`, every orthonormal family of eigenvectors of `K_E` with eigenvalues `> A ≥ A₁`
  lying in the range of `O_E^*` has at most `m` members; for `m = 0` there are none.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology Module
open scoped InnerProductSpace

/-! ### Lemma 7.8 -/

section Reduced

variable {Z Y : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- **Lemma 7.8 (reduced lower bound).** Let `E ↦ R_E : Z → Z` and `E ↦ S_E : Z → Y` be
operator-norm continuous at `E₀`, with `R_{E₀} = α I + C` (`α > 0`, `C` compact) and `S_{E₀}`
injective. Then there is `A₀ > 0` such that for all `E` near `E₀`,
`Re ⟨z, R_E z⟩ ≥ -A₀ ‖S_E z‖²` for every `z`. -/
theorem reduced_lower_bound (α : ℝ) (hα : 0 < α) (C : Z →L[ℂ] Z) (hC : IsCompactOperator C)
    (R : ℝ → Z →L[ℂ] Z) (S : ℝ → Z →L[ℂ] Y) (E₀ : ℝ) (hR : ContinuousAt R E₀)
    (hS : ContinuousAt S E₀) (hR₀ : R E₀ = (α : ℂ) • ContinuousLinearMap.id ℂ Z + C)
    (hinj : Function.Injective (S E₀)) :
    ∃ A₀ > 0, ∀ᶠ E in 𝓝 E₀, ∀ z : Z, -(A₀ * ‖S E z‖ ^ 2) ≤ (⟪z, R E z⟫_ℂ).re := by
  obtain ⟨A, hA, ε, hε, δ, hδ, h⟩ := compact_perturbation_coercive_nhds α hα C hC (S E₀) hinj
  refine ⟨A, hA, ?_⟩
  have h1 : ∀ᶠ E in 𝓝 E₀, ‖R E - R E₀‖ < δ := by
    have := (hR.sub_const (R E₀)).norm
    simp at this
    exact this.eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ E in 𝓝 E₀, ‖S E - S E₀‖ < δ := by
    have := (hS.sub_const (S E₀)).norm
    simp at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [h1, h2] with E hE1 hE2 z
  rw [hR₀] at hE1
  have := h (R E) (S E) hE1 hE2 z
  have : 0 ≤ ε / 2 * ‖z‖ ^ 2 := by positivity
  linarith

end Reduced

/-! ### Lemma 7.9 -/

section Boundary

variable {G X W : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

end Boundary

/-! ### Proposition 7.10 -/

section Rank

variable {G X : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]

end Rank

end PolyaNeumann
