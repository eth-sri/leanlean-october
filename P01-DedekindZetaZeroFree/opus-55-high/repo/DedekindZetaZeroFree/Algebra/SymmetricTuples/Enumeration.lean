module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/Data/Sym/Basic.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace Sym
end Sym

namespace DedekindZetaZeroFree.TauCeti

namespace Sym

variable {α β : Type*} {m n : ℕ}

def ofFn (f : Fin n → α) : Sym α n :=
  Sym.ofVector (List.Vector.ofFn f)

@[simp]
theorem coe_ofFn (f : Fin n → α) : (ofFn f : Multiset α) = ↑(List.ofFn f) :=
  congrArg _ (List.Vector.toList_ofFn f)

theorem count_coe_ofFn [DecidableEq α] (f : Fin n → α) (a : α) :
    Multiset.count a (ofFn f : Multiset α) = (Finset.univ.filter fun i => f i = a).card := by
  have hmap : (ofFn f : Multiset α) = Multiset.map f Finset.univ.val := by
    simp
  rw [hmap, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  simp only [eq_comm]

theorem ofFn_surjective : Function.Surjective (ofFn : (Fin n → α) → Sym α n) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
  have hlen : l.length = n := by simpa using hs
  subst hlen
  exact ⟨l.get, Subtype.ext (by simp)⟩

theorem ofFn_comp_perm (σ : Equiv.Perm (Fin n)) (f : Fin n → α) : ofFn (f ∘ σ) = ofFn f :=
  Sym.coe_injective <| by simpa using Multiset.coe_eq_coe.2 (σ.ofFn_comp_perm f)

theorem ofFn_eq_ofFn_iff {f g : Fin n → α} :
    ofFn f = ofFn g ↔ ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  ·
    have hcard : ∀ c : α, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := fun c => by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← count_coe_ofFn g c, ← count_coe_ofFn f c, h]
    exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
      funext fun i => Equiv.ofFiberEquiv_map _ i⟩
  · rintro ⟨σ, rfl⟩
    exact (ofFn_comp_perm σ f).symm

end Sym

noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)

@[simp]
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := by
  simp [symFinTwoEquiv, Fin.sum_univ_two, Multiset.nsmul_singleton]
