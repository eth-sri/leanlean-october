import Mathlib.Tactic

import RequestProject.Fox

/-!
# Words with vanishing exponent sums are products of commutators

Rule 3 of Section 3.4 factors a word `r⁰` with zero exponent sums in every
generator as a product `∏_{h=1}^q [u_h, v_h]`, padding with `[1,1]` until
`q ≥ 2`.  The paper gives an explicit sorting algorithm; what the construction
actually uses is the existence of such a factorization, i.e. that the kernel of
the exponent-sum homomorphism on a free group is its commutator subgroup.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped commutatorElement

namespace FiniteChains

variable {α : Type*} [DecidableEq α]

/-- The total exponent-sum homomorphism of a free group. -/
noncomputable def expSumTotal : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  FreeGroup.lift fun k => Multiplicative.ofAdd (Finsupp.single k (1 : ℤ))

variable (w : FreeGroup α)
theorem expSumTotal_apply  (i : α) :
    Multiplicative.toAdd (expSumTotal w) i = Multiplicative.toAdd (expSum i w) := by
  induction w using FreeGroup.induction_on <;> aesop (add simp [expSumTotal])

variable (h : ∀ i : α, Multiplicative.toAdd (expSum i w) = 0)
include h in
/-- A word with vanishing exponent sums lies in the commutator subgroup. -/
theorem mem_commutator_of_expSum_eq_zero 
     :
    w ∈ commutator (FreeGroup α) := by
  classical
  have hw : expSumTotal w = 1 := by
    aesop (add simp [expSumTotal_apply])
  -- the retraction of the abelianization onto the free abelian group on the generators
  set psi : Multiplicative (α →₀ ℤ) →* Abelianization (FreeGroup α) :=
    MonoidHom.mk' (fun x => Additive.toMul
        (Finsupp.liftAddHom
          (fun k => (zmultiplesHom (Additive (Abelianization (FreeGroup α))))
            (Additive.ofMul (Abelianization.of (FreeGroup.of k))))
          (Multiplicative.toAdd x)))
      (fun x y => by simp [map_add]) with hpsi
  set phi : Abelianization (FreeGroup α) →* Multiplicative (α →₀ ℤ) :=
    Abelianization.lift expSumTotal with hphi
  have hcomp : psi.comp phi = MonoidHom.id (Abelianization (FreeGroup α)) := by
    ext <;> simp_all [expSumTotal]
  have hof : Abelianization.of w = 1 := by
    have h1 : phi (Abelianization.of w) = 1 := by simp [hphi, hw]
    calc Abelianization.of w
        = psi (phi (Abelianization.of w)) := by
          rw [← MonoidHom.comp_apply, hcomp, MonoidHom.id_apply]
      _ = 1 := by rw [h1, map_one]
  rwa [show Abelianization.of w = QuotientGroup.mk' (commutator (FreeGroup α)) w from rfl,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hof

include h in
/-- **Rule 3 of Section 3.4.**  A word with vanishing exponent sums in every generator is a
product of `q ≥ 2` commutators, as required before substituting a block `B_q`. -/
theorem exists_commutator_factorization 
     :
    ∃ (q : ℕ) (u v : Fin q → FreeGroup α), 2 ≤ q ∧
      w = (List.ofFn fun j : Fin q => ⁅u j, v j⁆).prod := by
  classical
  have hw  := mem_commutator_of_expSum_eq_zero w h
  have hsub : w ∈ Submonoid.closure (commutatorSet (FreeGroup α)) := by
    have h1 : w ∈ Submonoid.closure
        (commutatorSet (FreeGroup α) ∪ (commutatorSet (FreeGroup α))⁻¹) := by
      rw [← Subgroup.closure_toSubmonoid]
      rwa [commutator_eq_closure] at hw
    have h2 : (commutatorSet (FreeGroup α) ∪ (commutatorSet (FreeGroup α))⁻¹)
        = commutatorSet (FreeGroup α) := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hx
        · obtain ⟨a, b, hab⟩ := hx
          exact ⟨b, a, by rw [← commutatorElement_inv, hab, inv_inv]⟩
      · exact fun hx => Or.inl hx
    rwa [h2] at h1
  obtain ⟨l, hl, hlp⟩ := Submonoid.exists_list_of_mem_closure hsub
  -- pad with two trivial commutators so that `q ≥ 2`
  set l' : List (FreeGroup α) := l ++ [1, 1] with hl'
  have hmem : ∀ x ∈ l', ∃ ab : FreeGroup α × FreeGroup α, x = ⁅ab.1, ab.2⁆ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, b, hab⟩ := hl x hx
      exact ⟨(a, b), hab.symm⟩
    · have : x = 1 := by
        simp_all
      exact ⟨(1, 1), by simp [this]⟩
  choose ab hab using hmem
  refine ⟨l'.length, fun j => (ab l'[(j : ℕ)] (List.getElem_mem j.2)).1,
    fun j => (ab l'[(j : ℕ)] (List.getElem_mem j.2)).2, ?_, ?_⟩
  · simp [hl']
  · have hofn : (List.ofFn fun j : Fin l'.length =>
        ⁅(ab l'[(j : ℕ)] (List.getElem_mem j.2)).1,
          (ab l'[(j : ℕ)] (List.getElem_mem j.2)).2⁆) = l' := by
      rw [show (fun j : Fin l'.length =>
          ⁅(ab l'[(j : ℕ)] (List.getElem_mem j.2)).1,
            (ab l'[(j : ℕ)] (List.getElem_mem j.2)).2⁆)
          = fun j : Fin l'.length => l'[(j : ℕ)] from
        funext fun j => (hab _ (List.getElem_mem j.2)).symm]
      exact List.ofFn_getElem
    rw [hofn, hl', List.prod_append, hlp]
    simp

end FiniteChains
