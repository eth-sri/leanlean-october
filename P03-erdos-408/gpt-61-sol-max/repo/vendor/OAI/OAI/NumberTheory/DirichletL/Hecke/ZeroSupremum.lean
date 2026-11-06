module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.Euler
public import OAI.NumberTheory.DirichletL.Supremum

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

def zeroRealParts  :=
  {x | ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
    (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ s.re = x}

def zeroSetWithSentinel  := insert (1 / 2) zeroRealParts

def beta  := sSup zeroSetWithSentinel

theorem zeroRealParts_le_one  {x}  (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

section
variable (χ : Character) {s : ℂ}

theorem zero_re_le_beta     (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt    
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  grind [half_le_beta, zero_re_le_beta]

end

end SevenEighths.HeckeZeroSupremum

end

end OAI
