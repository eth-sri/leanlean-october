/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.MvPolynomial.Degrees
import CCDN.LowerBound.GridCurveConstruction
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Principal

/-! Enlarging the ambient affine space preserves the irreducible grid equation. -/

public section
namespace CCDN
open MvPolynomial

variable {K σ τ : Type*}

/-- Renaming the variables of an irreducible polynomial along an injective map keeps it irreducible.
-/
lemma irreducible_rename_of_injective  [Field K]
    (i : σ → τ) (hi : Function.Injective i) (f : MvPolynomial σ K)
    (hf : Irreducible f) : Irreducible (rename i f) := by
  classical
  let e := Equiv.ofInjective i hi
  have he : rename i f = rename Subtype.val (renameEquiv K e f) := by
    aesop
  rw [he]
  apply Prime.irreducible
  apply (prime_rename_iff (Set.range i)).mpr
  apply irreducible_iff_prime.mp
  exact (MulEquiv.irreducible_iff (f := renameEquiv K e)).mpr hf

/-- Renaming the variables along a map with a left inverse preserves the total degree. -/
lemma totalDegree_rename_of_leftInverse  [CommRing K]
    (i : σ → τ) (r : τ → σ) (hr : Function.LeftInverse r i)
    (f : MvPolynomial σ K) : (rename i f).totalDegree = f.totalDegree := by
  apply le_antisymm (totalDegree_rename_le i f)
  have h := totalDegree_rename_le r (rename i f)
  have he : rename r (rename i f) = f := by
    rw [rename_rename]
    have hc : r ∘ i = id := funext hr
    simp [hc, rename_id]
  rwa [he] at h

end CCDN
