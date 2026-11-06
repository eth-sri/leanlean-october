import Mathlib
import RequestProject.FoxCommutator
import RequestProject.Tac


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

bwd

namespace FiniteChains

open Function

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]



/-- `f` is *injective modulo `n`*: whenever `f u` is divisible by `n`, already `u` is.
For maps between free modules this is injectivity of the reduction `f ⊗ ℤ/n`. -/
def LiftsMod (f : U →+ V) (n : ℕ) :=
  ∀ u, (∃ w : V, f u = n • w) → ∃ u' : U, u = n • u'

/-- **The lifting step.**  If the target is torsion free and `f` is injective modulo every
prime, then every element whose multiple lies in the image already lies in the image. -/
theorem mem_range_of_nsmul_mem_range (f : U →+ V) [IsAddTorsionFree V]
    (hmod : ∀ p, p.Prime → LiftsMod f p) :
    ∀ n, n ≠ 0 → ∀ x, n • x ∈ f.range → x ∈ f.range := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    rcases eq_or_ne n 1 with rfl | hn1
    · simpa using hx
    · obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m := by
        obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hn1
        tauto
      have hm : m ≠ 0 := by simp_all
      have hpos := hp.ne_zero
      cases' hx with u hu
      -- `p` divides `f u`, hence `u`
      cases' hmod p hp u ⟨m • x, by rw [hu, mul_smul]⟩ with u' hu'
      have hmx : m • x = f u' := by
        refine IsAddTorsionFree.nsmul_right_injective hpos ?_
        simp [← mul_smul, ← hu, hu', map_nsmul]
      have : m • x ∈ f.range := by simp_all
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
instance isAddTorsionFree_finsupp {α : Type*} {A} [AddCommGroup A]
    [IsAddTorsionFree A] : IsAddTorsionFree (α →₀ A) := by
  infer_instance

/-- Group rings over `ℤ` are torsion free as additive groups. -/
instance isAddTorsionFree_monoidAlgebra {Q} [Monoid Q] :
    IsAddTorsionFree (MonoidAlgebra ℤ Q) :=
  by
    constructor
    intro n hn a b hab
    let e := (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Q)).toAddMonoidHom
    have hc : n • a.coeff = n • b.coeff := calc
      _ = e (n • a) := by tauto
      _ = e (n • b) := congrArg e hab
      _ = _ := map_nsmul e n b
    simp_all

variable {G : Type*} [Group G] {I J : Type*}

/-!
## Removing the torsion-freeness hypothesis from the application of Lemma 2.1
-/
