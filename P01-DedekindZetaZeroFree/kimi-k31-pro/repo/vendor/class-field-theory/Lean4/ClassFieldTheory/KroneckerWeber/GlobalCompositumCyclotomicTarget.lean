module

public import ClassFieldTheory.KroneckerWeber.Setup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The common local cyclotomic target

At a ramified prime `p`, the structured local embedding of `L` has order
`(p^f - 1) * p^e`, while the global conductor has order `p^e * c` with
`c` prime to `p`.  Their common target has order
`((p^f - 1) * c) * p^e`; crucially, it uses the same exponent `e`.
-/

noncomputable section

namespace KroneckerWeber

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The prime-to-`p` factor of the common local target. -/
noncomputable def kroneckerWeberLocalCompositumCoprimePart
    (p : Nat.Primes) : ℕ :=
  (p.1 ^ kroneckerWeberLocalUnramifiedDegree (L := L) p - 1) *
    kroneckerWeberConductorCoprimePart (L := L) p

/-- The common local cyclotomic order, retaining exactly the conductor
exponent chosen at `p`. -/
noncomputable def kroneckerWeberLocalCompositumOrder
    (p : Nat.Primes) : ℕ :=
  kroneckerWeberLocalCompositumCoprimePart (L := L) p *
    p.1 ^ kroneckerWeberLocalRamificationExponent (L := L) p



/-- The common local cyclotomic order is positive. -/
theorem kroneckerWeberLocalCompositumOrder_pos
    (p : Nat.Primes) :
    0 < kroneckerWeberLocalCompositumOrder (L := L) p := by
  rw [kroneckerWeberLocalCompositumOrder,
    kroneckerWeberLocalCompositumCoprimePart]
  apply Nat.mul_pos
  · apply Nat.mul_pos
    · exact Nat.sub_pos_of_lt
        (one_lt_pow₀ p.2.one_lt
          (kroneckerWeberLocalUnramifiedDegree_pos (L := L) p).ne')
    · rw [kroneckerWeberConductorCoprimePart]
      exact Finset.prod_pos fun q _ ↦ pow_pos q.2.pos _
  · exact pow_pos p.2.pos _





end KroneckerWeber

end
