import RequestProject.Fox
import RequestProject.Tac


/-!
# Words with vanishing exponent sums are products of commutators

Rule 3 of Section 3.4 factors a word `r⁰` with zero exponent sums in every
generator as a product `∏_{h=1}^q [u_h, v_h]`, padding with `[1,1]` until
`q ≥ 2`.  The paper gives an explicit sorting algorithm; what the construction
actually uses is the existence of such a factorization, i.e. that the kernel of
the exponent-sum homomorphism on a free group is its commutator subgroup.
-/

bwd

open scoped commutatorElement

namespace FiniteChains

variable {α : Type*} [DecidableEq α]

/-- The total exponent-sum homomorphism of a free group. -/
noncomputable def expSumTotal : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  FreeGroup.lift fun k => Multiplicative.ofAdd (Finsupp.single k (1 : ℤ))

theorem expSumTotal_apply w (i : α) :
    Multiplicative.toAdd (expSumTotal w) i = Multiplicative.toAdd (expSum i w) := by
  induction w using FreeGroup.induction_on with
  | one => rfl
  | of k =>
      simp [expSumTotal, expSum, FreeGroup.lift_apply_of, Finsupp.single_apply, eq_comm]
  | inv_of k h =>
      simp_all
  | mul u v hu hv =>
      simp_all

/-- A word with vanishing exponent sums lies in the commutator subgroup. -/
theorem mem_commutator_of_expSum_eq_zero w
    (h : ∀ i, Multiplicative.toAdd (expSum i w) = 0) :
    w ∈ commutator (FreeGroup α) := by
  classical
  have hw : expSumTotal w = 1 := by
    have h0 : Multiplicative.toAdd (expSumTotal w) = 0 := by
      grind [expSumTotal_apply]
    simpa using h0
  -- the retraction of the abelianization onto the free abelian group on the generators
  set psi : Multiplicative (α →₀ ℤ) →* Abelianization (FreeGroup α) :=
    MonoidHom.mk' (fun x => Additive.toMul
        (Finsupp.liftAddHom
          (fun k => (zmultiplesHom _)
            (Additive.ofMul (Abelianization.of (FreeGroup.of k))))
          x.toAdd))
      (by simp) with hpsi
  set phi : Abelianization (FreeGroup α) →* Multiplicative (α →₀ ℤ) :=
    Abelianization.lift expSumTotal with hphi
  have hcomp : psi.comp phi = MonoidHom.id _ := by
    refine Abelianization.hom_ext _ _ (FreeGroup.ext_hom _ _ fun k => ?_)
    simp [hpsi, hphi, expSumTotal, FreeGroup.lift_apply_of]
  have hof : Abelianization.of w = 1 := by
    calc Abelianization.of w
        = psi (phi (Abelianization.of w)) := by
          rw [← MonoidHom.comp_apply, hcomp, MonoidHom.id_apply]
      _ = 1 := by simp_all
  rwa [show Abelianization.of w = QuotientGroup.mk' _ w from rfl,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hof

/-- **Rule 3 of Section 3.4.**  A word with vanishing exponent sums in every generator is a
product of `q ≥ 2` commutators, as required before substituting a block `B_q`. -/
theorem exists_commutator_factorization w
    (h : ∀ i, Multiplicative.toAdd (expSum i w) = 0) :
    ∃ (q : ℕ) (u v : Fin q → FreeGroup α), 2 ≤ q ∧
      w = (List.ofFn fun j => ⁅u j, v j⁆).prod := by
  classical
  have hw := mem_commutator_of_expSum_eq_zero w h
  have hsub : w ∈ Submonoid.closure (commutatorSet _) := by
    have h1 : w ∈ Submonoid.closure
        (commutatorSet _ ∪ (commutatorSet _)⁻¹) := by
      simp_all [← Subgroup.closure_toSubmonoid, commutator_eq_closure]
    have h2 : (commutatorSet _ ∪ (commutatorSet _)⁻¹)
        = commutatorSet (FreeGroup α) := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hx
        · obtain ⟨a, b, hab⟩ := hx
          exact ⟨b, a, by rw [← commutatorElement_inv, hab, inv_inv]⟩
      simp_all
    simp_all
  obtain ⟨l, hl, hlp⟩ := Submonoid.exists_list_of_mem_closure hsub
  -- pad with two trivial commutators so that `q ≥ 2`
  set l' : List (FreeGroup α) := l ++ [1, 1] with hl'
  have hmem : ∀ x ∈ l', ∃ ab : FreeGroup α × FreeGroup α, x = ⁅ab.1, ab.2⁆ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, b, hab⟩ := hl x hx
      tauto
    · exact ⟨(1, 1), by simp_all⟩
  choose ab hab using hmem
  refine ⟨l'.length, fun j => (ab _ (List.getElem_mem j.2)).1,
    fun j => (ab _ (List.getElem_mem j.2)).2, ?_, ?_⟩
  · grind
  · have hofn : (List.ofFn fun j =>
        ⁅(ab _ (List.getElem_mem j.2)).1,
          (ab _ (List.getElem_mem j.2)).2⁆) = l' := by
      rw [show (fun j : Fin l'.length =>
          ⁅(ab _ (List.getElem_mem j.2)).1,
            (ab _ (List.getElem_mem j.2)).2⁆)
          = fun j => l'[j] from
        funext fun j => (hab _ _).symm]
      exact List.ofFn_getElem
    rw [hofn, hl', List.prod_append, hlp]
    simp
