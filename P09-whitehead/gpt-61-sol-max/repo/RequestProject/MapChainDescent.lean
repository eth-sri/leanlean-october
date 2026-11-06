import Mathlib.Tactic

import RequestProject.MinimalGap
import RequestProject.Pi2GenerationDescent

/-!
# Proposition 3.11 for chains given by explicit inclusions

Condition (1) of Theorem A speaks about a chain of **inclusions** `K = E₀ ⊊ E₁ ⊊ ⋯ ⊊ Eₙ`
each of which is zero on `π₂`.  The interface `FiniteChains.combData` renders "the inclusion
is zero on `π₂`" by the stronger condition *every* injective cellular map `Eᵢ → Eᵢ₊₁` is zero
on `π₂`; this is convenient for the implication `(1) ⇒ (2)`, but the descent of
Proposition 3.11 produces one specific inclusion per step and says nothing about the others.
This file works with the faithful, map-carrying form throughout.

* `FiniteChains.Comb.inclFrom` — the inclusion `L₀ ⊆ Lᵢ` of a chain given by explicit maps;
* `FiniteChains.Comb.RelChainW` — a relative chain of Proposition 3.7 **with its
  inclusions**, together with the finiteness bookkeeping needed downstairs;
* `FiniteChains.Comb.RelChainW.desc`, `FiniteChains.Comb.RelChainW.descInc` — the descended
  chain `E₀ = K`, `Eᵢ₊₁ = K ∪_p Lᵢ₊₁` of Proposition 3.11 together with its inclusions, and
  the proofs that these are injective, that the stages are finite and connected;
* `FiniteChains.Comb.RelChainW.zeroPi2_descInc_zero` — **the first arrow is zero on `π₂`**
  (unconditionally);
* `FiniteChains.Comb.Pi2GeneratedByUpstairs` — the generation statement (3.5) of the paper,
  the one remaining input of step 2 of the proof of Proposition 3.11;
* `FiniteChains.Comb.RelChainW.zeroPi2_descInc` — granted (3.5), **all** arrows of the
  descended chain are zero on `π₂`;
* `FiniteChains.Comb.RelChainW.toTopChainDisc` — the descended chain as a chain in the sense
  of `RequestProject/ComponentChain.lean`, whence
* `FiniteChains.Comb.hasAcyclicRegularCover_of_hasMapChains`,
  `FiniteChains.Comb.theoremA_maps` — **Theorem A for finite connected combinatorial
  two-complexes with condition (1) in its faithful form**, from two inputs: the extension
  step of Lemmas 3.1, 3.9, 3.10 (`FiniteChains.Comb.MapStep`) and the generation statement
  (3.5).
-/

namespace FiniteChains.Comb



/-! ### Chains with explicit inclusions -/

/-- The inclusion of the first term of a chain into its `i`-th term. -/
def inclFrom (c : ℕ → Complex2.{u}) (inc : ∀ i, Hom (c i) (c (i + 1))) :
    ∀ i, Hom (c 0) (c i)
  | 0 => Hom.id (c 0)
  | i + 1 => (inc i).comp (inclFrom c inc i)



/-- **A relative chain of Proposition 3.7 carrying its inclusions.**  The chain is indexed by
all of `ℕ` (a chain of length `n` is extended by repeating its last term); the conditions of
Proposition 3.7 are imposed up to the index `n`.  On top of them the structure records what
the descent of Proposition 3.11 needs: the stages are connected, each term has only finitely
many cells off `D`, and each step adds a two-cell. -/
structure RelChainW (D : Complex2.{u}) (c : ℕ → Complex2.{u}) (n : ℕ) where
  /-- The inclusion of one term into the next. -/
  inc : ∀ i, Hom (c i) (c (i + 1))
  incV : ∀ i, Function.Injective (inc i).onV
  incE : ∀ i, Function.Injective (inc i).onE
  incF : ∀ i, Function.Injective (inc i).onF
  /-- The chain starts at the acyclic core `D`. -/
  base : c 0 = D
  /-- Every stage is connected. -/
  conn : ∀ i, IsConnected (c i)
  /-- Every stage is Cockcroft. -/
  cockcroft : ∀ i ≤ n, IsCockcroft (c i)
  /-- Every inclusion is zero on `π₂`. -/
  zero : ∀ i < n, ZeroPi2 (inc i)
  /-- `π₁(D)` dies from the first stage on. -/
  pi1 : ∀ i, 1 ≤ i → i ≤ n → Pi1Trivial (inclFrom c inc i)
  /-- Every stage has only finitely many edges off `D`. -/
  finE : ∀ i, Finite (OffE (inclFrom c inc i))
  /-- Every stage has only finitely many two-cells off `D`. -/
  finF : ∀ i, Finite (OffF (inclFrom c inc i))
  /-- Every step adds a two-cell. -/
  adds : ∀ i < n, Nonempty (OffF (inc i))

namespace RelChainW

variable {D : Complex2.{u}} {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelChainW D c n)





/-! ### The descended chain -/

variable (K : Complex2.{u}) (p : Hom (c 0) K)







/-! ### The induced maps of pushouts are inclusions -/

section

variable {L L' : Complex2.{u}} {D' : Complex2.{u}} (q : Hom D' K) (j : Hom D' L) (j' : Hom D' L')
  (k : Hom L L') (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
  (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
  (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')

include hkj in
theorem pushoutFunctor_injV (hkV : Function.Injective k.onV) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onV := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.V, F.onV (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffV j, F.onV (Sum.inr w) = Sum.inr ⟨k.onV w.1, off_map_V hkV hkj w⟩ :=
    fun w => pushV_of_off q j' ⟨k.onV w.1, off_map_V hkV hkj w⟩
  rintro (a | w) (b | w') h
  · grind
  · rw [hinl, hinr] at h
    simp at h
  · rw [hinr, hinl] at h
    simp at h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkV (congrArg Subtype.val (Sum.inr_injective h))))

include hkj in
theorem pushoutFunctor_injE (hkE : Function.Injective k.onE) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onE := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.E, F.onE (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffE j, F.onE (Sum.inr w) = Sum.inr ⟨k.onE w.1, off_map_E hkE hkj w⟩ :=
    fun w => pushE_of_off q j' ⟨k.onE w.1, off_map_E hkE hkj w⟩
  rintro (a | w) (b | w') h
  · grind
  · rw [hinl, hinr] at h
    simp at h
  · rw [hinr, hinl] at h
    simp at h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkE (congrArg Subtype.val (Sum.inr_injective h))))

include hkj in
theorem pushoutFunctor_injF (hkF : Function.Injective k.onF) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onF := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.F, F.onF (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffF j, F.onF (Sum.inr w) = Sum.inr ⟨k.onF w.1, off_map_F hkF hkj w⟩ :=
    fun w => pushF_of_off q j' ⟨k.onF w.1, off_map_F hkF hkj w⟩
  rintro (a | w) (b | w') h
  · grind
  · rw [hinl, hinr] at h
    simp at h
  · rw [hinr, hinl] at h
    simp at h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkF (congrArg Subtype.val (Sum.inr_injective h))))

end

/-! ### Finiteness and connectivity of the stages -/

/-! ### The arrows are zero on `π₂` -/

end RelChainW








/-! ### Strictness of the descended chain -/








/-! ### Non-vacuity: the constant chain -/

/-! ### Assembling Theorem A -/

end FiniteChains.Comb

