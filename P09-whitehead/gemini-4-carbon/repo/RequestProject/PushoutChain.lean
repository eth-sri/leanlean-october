module

public import RequestProject.CombPushout

@[expose] public section

/-!
# Descending a chain along a covering: the combinatorial part of Proposition 3.11

Proposition 3.11 takes a chain `D = L₀ ⊆ L₁ ⊆ ⋯ ⊆ Lₙ` over an acyclic regular cover
`p : D → K` and descends it to a chain over `K` by forming the cellular pushouts
`Eᵢ = K ∪_p Lᵢ`.  Using the pushout of `RequestProject/CombPushout.lean` this file builds the
descended sequence and proves everything about it except the homotopy-theoretic statement
that its inclusions are zero on `π₂`:

* `FiniteChains.Comb.chainIncl` — the inclusion `L₀ ⊆ Lᵢ` obtained by composing the steps of
  the chain, and its injectivity;
* `FiniteChains.Comb.descentChain` — the descended sequence `E₀ = K`, `Eᵢ = K ∪_p Lᵢ`;
* `FiniteChains.Comb.descentChain_sub` — **every term is a subcomplex of the next**, so the
  descended sequence really is a chain of two-complexes starting at `K`;
* `FiniteChains.Comb.descentChain_finite_E`, `FiniteChains.Comb.descentChain_finite_F` — the
  stages are finite as soon as `K` is finite and each `Lᵢ` has only finitely many cells off
  `L₀`;
* `FiniteChains.Comb.descentChain_isConnected` — the stages are connected;
* `FiniteChains.Comb.exists_descentChain` — the packaged existence statement.

The chain upstairs is indexed by all of `ℕ`; a chain of finite length `n` is put in this form
by repeating its last term (`FiniteChains.Comb.sub_truncate`).
-/

namespace FiniteChains
namespace Comb

universe u

variable {K : Complex2.{u}} {c : ℕ → Complex2.{u}}

/-! ### The inclusions of a chain -/

variable (c) in
/-- The chosen inclusion of one term of the chain into the next. -/
noncomputable def chainStep (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) : Hom (c i) (c (i + 1)) :=
  (hsub i).choose

theorem chainStep_injV (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    Function.Injective (chainStep c hsub i).onV := (hsub i).choose_spec.1

theorem chainStep_injE (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    Function.Injective (chainStep c hsub i).onE := (hsub i).choose_spec.2.1

variable (c) in
/-- The inclusion of the first term of the chain into the `i`-th one. -/
noncomputable def chainIncl (hsub : ∀ i, Sub (c i) (c (i + 1))) : ∀ i : ℕ, Hom (c 0) (c i)
  | 0 => Hom.id (c 0)
  | i + 1 => (chainStep c hsub i).comp (chainIncl hsub i)

theorem chainIncl_injV (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ∀ i, Function.Injective (chainIncl c hsub i).onV
  | 0 => fun _ _ h => h
  | i + 1 => (chainStep_injV hsub i).comp (chainIncl_injV hsub i)

theorem chainIncl_injE (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ∀ i, Function.Injective (chainIncl c hsub i).onE
  | 0 => fun _ _ h => h
  | i + 1 => (chainStep_injE hsub i).comp (chainIncl_injE hsub i)

/-! ### The descended chain -/

variable (K) in
/-- **The chain `Eᵢ = K ∪_p Lᵢ` downstairs.**  The zeroth term is `K` itself; the `(i+1)`-st
is the cellular pushout of `K ← L₀ ⊆ L_{i+1}` along the covering `p`. -/
noncomputable def descentChain (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ℕ → Complex2.{u}
  | 0 => K
  | i + 1 =>
      pushoutComplex p (chainIncl c hsub (i + 1)) (chainIncl_injV hsub (i + 1))
        (chainIncl_injE hsub (i + 1))

@[simp] theorem descentChain_zero (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    descentChain K p hsub 0 = K := rfl

/-! ### Finiteness of the stages -/

/-! ### Strictness of the descended chain -/

/-! ### The packaged statement -/

end Comb
end FiniteChains
