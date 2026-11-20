module

public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section

namespace Light

open ThreeSumApsp

/-- Polynomial growth in the product of the incremented input parameters. -/
noncomputable def listScale : Scale (List ℕ) (Fin 0) where
  dom _ := True
  hidden ps := ((ps.map (· + 1)).prod : ℕ)
  base i := i.elim0
  one_le_hidden ps _ := Nat.one_le_cast.2 (Nat.succ_le_of_lt (List.prod_pos (by simp)))
  one_le_base i := i.elim0

abbrev PolyBoundedList (f : List ℕ → ℕ) := listScale.SoftO f 0

namespace PolyBoundedList

theorem param (i : ℕ) : PolyBoundedList fun ps => ps[i]?.getD 0 := by
  apply Scale.SoftO.of_le_hidden
  intro ps h
  clear h
  change (ps[i]?.getD 0 : ℝ) ≤ ((ps.map (· + 1)).prod : ℕ)
  apply Nat.cast_le.2
  induction ps generalizing i with
  | nil => simp
  | cons n ps ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.getD_some, List.map_cons, List.prod_cons]
      exact (Nat.le_succ n).trans (Nat.le_mul_of_pos_right _ (List.prod_pos (by simp)))
    | succ j =>
      grind

theorem of_polyBound {f : List ℕ → ℕ} {s k : ℕ}
    (h : ∀ ps, f ps ≤ polyBound s k ps) : PolyBoundedList f :=
  (show PolyBoundedList (polyBound s k) from by
    have hs : PolyBoundedList fun ps => (ps.map (· + 1)).prod := .of_le_hidden fun _ _ => le_rfl
    unfold polyBound
    growth [hs]).of_le fun ps _ => h ps

theorem comp₂ {F : ℕ → ℕ → ℕ} {A B : List ℕ → ℕ} (h : PolyBounded F)
    (hA : PolyBoundedList A) (hB : PolyBoundedList B) :
    PolyBoundedList fun ps => F (A ps) (B ps) := by
  obtain ⟨K, k, hK⟩ := h.exists_nat_le
  exact (show PolyBoundedList (fun ps => K * ((A ps + 1) * (B ps + 1)) ^ k) by
    growth [hA, hB]).of_le fun ps _ => hK _ _

theorem exists_le {f : List ℕ → ℕ} (h : PolyBoundedList f) :
    ∃ s k : ℕ, ∀ ps, f ps ≤ polyBound s k ps := by
  obtain ⟨C, k, _, hC⟩ := Scale.SoftO.exists_le h
  refine ⟨Nat.size ⌈C⌉₊, k, fun ps => ?_⟩
  have h' : (f ps : ℝ) ≤ C * (((ps.map (· + 1)).prod : ℕ) : ℝ) ^ k := by
    simp_all [listScale, Scale.mon] <;> omega
  have hC' : C ≤ (2 : ℝ) ^ (Nat.size ⌈C⌉₊) :=
    (Nat.le_ceil C).trans (by exact_mod_cast (Nat.lt_size_self ⌈C⌉₊).le)
  unfold polyBound
  exact_mod_cast h'.trans (mul_le_mul_of_nonneg_right hC' (by positivity))

theorem polyNeed {need : List ℕ → Need} (hw : PolyBoundedList fun ps => (need ps).word)
    (hc : PolyBoundedList fun ps => (need ps).cells)
    (hd : PolyBoundedList fun ps => (need ps).depth) :
    PolyNeedN need := by
  obtain ⟨s, k, h⟩ := exists_le
    (f := fun ps => (need ps).word + (need ps).cells + (need ps).depth) (by growth [hw, hc, hd])
  exact ⟨s, k, fun ps => by have := h ps; omega⟩

end PolyBoundedList

end Light
