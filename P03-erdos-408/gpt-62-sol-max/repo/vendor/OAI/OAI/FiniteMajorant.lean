module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Order

@[expose] public section

namespace OAI

/-- A finite family admits a common upper bound above any prescribed floor. -/
theorem exists_real_majorant {ι : Type*} [Finite ι] (a : ℝ) (f : ι → ℝ) :
    ∃ C, a < C ∧ ∀ i, f i ≤ C := by
  obtain ⟨B, hB⟩ := Finite.bddAbove_range f
  have hlt := lt_add_of_pos_right (max B a) zero_lt_one
  exact ⟨_, (le_max_right B a).trans_lt hlt,
    fun i => (hB ⟨i, rfl⟩).trans ((le_max_left B a).trans hlt.le)⟩

theorem exists_finset_real_majorant {ι : Type*} (s : Finset ι) (a : ℝ) (f : ι → ℝ) :
    ∃ C, a < C ∧ ∀ i ∈ s, f i ≤ C :=
  let ⟨C, hC, hb⟩ := exists_real_majorant a (fun i : s => f i)
  ⟨C, hC, fun i hi => hb ⟨i, hi⟩⟩

end OAI
