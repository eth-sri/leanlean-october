module

public import RequestProject.ComponentComplex
public import RequestProject.TreeChainTopological
public import RequestProject.CombData
public import RequestProject.Pigeonhole
public import RequestProject.SubgroupCompactness
public import RequestProject.Pi2GenerationDescent

@[expose] public section

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

universe u

/-! ### Chains with explicit inclusions -/

/-- The inclusion of the first term of a chain into its `i`-th term. -/
def inclFrom (c : ℕ → Complex2.{u}) (inc : ∀ i, Hom (c i) (c (i + 1))) :
    ∀ i, Hom (c 0) (c i)
  | 0 => Hom.id (c 0)
  | i + 1 => (inc i).comp (inclFrom c inc i)

namespace RelChainW

variable (K : Complex2.{u}) {L L' : Complex2.{u}} {D' : Complex2.{u}}
  (q : Hom D' K) (j : Hom D' L) (j' : Hom D' L')
  (k : Hom L L') (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
  (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
  (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')

include hkj in
theorem pushoutFunctor_injV (hkV : Function.Injective k.onV) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onV := by
  have hinr (w : OffV j) : (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onV (Sum.inr w) =
      Sum.inr ⟨k.onV w.1, off_map_V hkV hkj w⟩ := pushV_of_off q j' ⟨k.onV w.1, off_map_V hkV hkj w⟩
  rintro (a | w) (b | w') h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · rw [hinr] at h; cases h
  · rw [hinr] at h; cases h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkV (congrArg Subtype.val (Sum.inr.inj h))))

include hkj in
theorem pushoutFunctor_injE (hkE : Function.Injective k.onE) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onE := by
  have hinr (w : OffE j) : (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onE (Sum.inr w) =
      Sum.inr ⟨k.onE w.1, off_map_E hkE hkj w⟩ := pushE_of_off q j' ⟨k.onE w.1, off_map_E hkE hkj w⟩
  rintro (a | w) (b | w') h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · rw [hinr] at h; cases h
  · rw [hinr] at h; cases h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkE (congrArg Subtype.val (Sum.inr.inj h))))

include hkj in
theorem pushoutFunctor_injF (hkF : Function.Injective k.onF) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onF := by
  have hinr (w : OffF j) : (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onF (Sum.inr w) =
      Sum.inr ⟨k.onF w.1, off_map_F hkF hkj w⟩ := pushF_of_off q j' ⟨k.onF w.1, off_map_F hkF hkj w⟩
  rintro (a | w) (b | w') h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · rw [hinr] at h; cases h
  · rw [hinr] at h; cases h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkF (congrArg Subtype.val (Sum.inr.inj h))))
