/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Bad reduction of an integer polynomial at a prime: degree loss or failure of absolute
irreducibility modulo `p`. -/

@[expose] public section
namespace CCDN
open MvPolynomial

variable {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ)

/-- Bad reduction at `p`: `p` is prime and the reduction of `f` over the algebraic closure of
`𝔽_p` either has smaller total degree than `f` or is not irreducible. -/
noncomputable def HypersurfaceBadReduction   :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree ≠ f.totalDegree ∨
      ¬Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)

/-- At a prime `p`, good reduction means that the reduction over the algebraic closure of
`𝔽_p` keeps the total degree and is irreducible. -/
lemma not_hypersurfaceBadReduction_iff 
    [Fact p.Prime] :
    ¬HypersurfaceBadReduction f p ↔
      (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree = f.totalDegree ∧
        Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) := by
  simp [HypersurfaceBadReduction, Fact.out]

end CCDN
