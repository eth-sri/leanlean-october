module
public import GafniTao.FordExponentialSum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Ford's zero-representation domination principle

This is Proposition ZRD in Section 2 of Ford's source.  For a finite family
of integer-valued functions, the number of ordered pairs whose value vectors
have a prescribed difference is at most the number whose difference is zero.

The theorem is stated for an arbitrary additive commutative group.  Ford's
literal application is obtained by taking the codomain to be a finite vector
of integers.  The proof is the source Cauchy--Schwarz argument on the exact
fiber-count function; no Fourier integral or unproved moment estimate enters.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

variable {β Γ : Type*} [DecidableEq β] [AddCommGroup Γ] [DecidableEq Γ]

/-- The exact ordered-pair representation count at displacement `w`. -/
def fordRepresentationCount (B : Finset β) (F : β → Γ) (w : Γ) : ℕ :=
  ((B ×ˢ B).filter fun xy => F xy.1 - F xy.2 = w).card




