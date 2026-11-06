import Mathlib.Tactic

import Mathlib
import RequestProject.FoxCommutator

/-!
# The universal-coefficient input of Section 2

At the end of Section 2 the paper says: "The universal coefficient theorem gives
`H₂(K_N;ℤ) = 0` and torsion-free `N/[N,N]`", and earlier, in the derivation of (2.3), that
"Fox cycles modulo `p` lift integrally when the universal cover has `H₁ = 0`"
(the reference to Hatcher).

Both assertions are consequences of one purely algebraic fact about the cellular chain
complex of the cover, which is the complex of free `ℤ[G/N]`-modules whose second boundary
is the Fox boundary `∂_{2,N}`.  The requirements (2.2) are imposed integrally *and modulo
every prime*; modulo `p` the requirement says exactly that the boundary is injective after
reduction mod `p`, which in the free (hence torsion-free) setting is the lifting property
`LiftsMod` below.  Given the requirement for every prime, the homology

  `H₁ = (cycles) / im ∂`

is torsion free, and `H₂ = ker ∂ = 0` is immediate from the integral requirement.

This file proves that algebraic statement in general (`mem_range_of_nsmul_mem_range`,
`isAddTorsionFree_quotient_range_of_liftsMod`) and specializes it to the Fox boundary
(`foxHomologyOne_torsionFree`).  Together with the dictionary `H₁(K_N) = N/[N,N]` — the one
topological input that is not formalized here — this is the hypothesis
`IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))` used in
`RequestProject/FoxCommutator.lean`.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains



variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]





/-- `f` is *injective modulo `n`*: whenever `f u` is divisible by `n`, already `u` is.
For maps between free modules this is injectivity of the reduction `f ⊗ ℤ/n`. -/
def LiftsMod (f : U →+ V) (n : ℕ)  :=
  ∀ u : U, (∃ w : V, f u = n • w) → ∃ u' : U, u = n • u'

/-- **The lifting step.**  If the target is torsion free and `f` is injective modulo every
prime, then every element whose multiple lies in the image already lies in the image. -/
theorem mem_range_of_nsmul_mem_range (f : U →+ V) [IsAddTorsionFree V]
    (hmod : ∀ p : ℕ, p.Prime → LiftsMod f p) :
    ∀ n : ℕ, n ≠ 0 → ∀ x : V, n • x ∈ f.range → x ∈ f.range := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    rcases eq_or_ne n 1 with rfl | hn1
    · simpa using hx
    · obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m := by
        solve_by_elim [Nat.exists_prime_and_dvd]
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hpos  := hp.ne_zero
      obtain ⟨u, hu⟩ := hx
      -- `p` divides `f u`, hence `u`
      obtain ⟨u', hu'⟩ := hmod p hp u ⟨m • x, by rw [hu, mul_smul]⟩
      have hmx : m • x = f u' := by
        simp_all [mul_smul]
      have : m • x ∈ f.range := ⟨u', hmx.symm⟩
      rcases eq_or_ne m 1 with rfl | hm1
      · simpa using this
      · refine ih m ?_ hm x this
        have h2 := hp.two_le
        have hm' := Nat.pos_of_ne_zero hm
        nlinarith

/-!
## The Fox complex
-/

/-- Finitely supported functions into a torsion-free group are torsion free. -/
instance isAddTorsionFree_finsupp {α : Type*} {A : Type*} [AddCommGroup A]
    [IsAddTorsionFree A] : IsAddTorsionFree (α →₀ A) := by
  solve_by_elim [IsAddTorsionFree.nsmul_right_injective]

/-- Group rings over `ℤ` are torsion free as additive groups. -/
instance isAddTorsionFree_monoidAlgebra {Q : Type*} [Monoid Q] :
    IsAddTorsionFree (MonoidAlgebra ℤ Q) :=
  by
    constructor
    intro n hn a b hab
    let e := (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Q)).toAddMonoidHom
    have hc  := calc
      _ = e (n • a) := (map_nsmul e n a).symm
      _ = e (n • b) := congrArg e hab
      _ = _ := map_nsmul e n b
    apply MonoidAlgebra.coeff_injective
    exact IsAddTorsionFree.nsmul_right_injective hn hc

variable {G : Type*} [Group G] {I J : Type*}

/-!
## Removing the torsion-freeness hypothesis from the application of Lemma 2.1
-/

/-- A group written multiplicatively out of a torsion-free additive group is torsion free. -/
instance isMulTorsionFree_multiplicative {A : Type*} [AddMonoid A] [IsAddTorsionFree A] :
    IsMulTorsionFree (Multiplicative A) := by
  solve_by_elim [IsAddTorsionFree.nsmul_right_injective]

end FiniteChains
