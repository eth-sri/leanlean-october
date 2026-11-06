module

public import Chazelle.Core.SpecPhases

/-!
# WP-G, part 11: reading the grade table

The grade table (`GradeRaw`) holds robustly below the entry allocator `A` of the oracles.  Every
word the oracles read from it (the handle words, the powers of two, the halving table, the
entries and their descriptor and normal-form handles) then lies below `A` (`grade_addrs`): a
word at or above `A` could be replaced by a padding value (`pad`) that contradicts a value the
table pins down.  So these words keep their values while the oracles write above `A`.
-/

namespace Chazelle.Core

@[expose] public section

namespace ShootCut

/-- The memory `m` below `A`, the value `Z` from `A` on. -/
def pad (m : ℕ → ℕ) (A Z : ℕ) : ℕ → ℕ := fun a => if a < A then m a else Z

section
variable {m : ℕ → ℕ} {A Z a : ℕ}
theorem pad_lt (h : a < A) : pad m A Z a = m a := ite_eq_left h

theorem pad_ge (h : A ≤ a) : pad m A Z a = Z := ite_eq_right (by omega)


end

theorem robust_pad {A : ℕ} {m : ℕ → ℕ} {Φ : (ℕ → ℕ) → Prop} (h : Robust A m Φ) (Z : ℕ) :
    Φ (pad m A Z) := h _ fun _ ha => pad_lt ha

variable {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {h A : ℕ}

/-- The address of the entry `(g, i)`. -/
def entryAddr (m : ℕ → ℕ) (h g i : ℕ) : ℕ := m (m (h + 2) + g) + 3 * i

/-- **The grade table lies below its bound** (handle words, powers of two, halving table). -/
theorem grade_low (hR : Robust A m fun m' => GradeRaw O P m' h A) :
    h + 3 < A ∧ (∀ j, j ≤ topGrade P.n + 1 → m (h + 1) + 2 + j < A) ∧
      (∀ x, x ≤ P.n → m (h + 3) + x < A) := by
  -- the handle `h` itself
  have hh : h < A := by
    by_contra hA
    have := (robust_pad hR (topGrade P.n + 2)).1
    rw [pad_ge (by omega)] at this
    omega
  have h1 : h + 1 < A := by
    by_contra hA
    have := (robust_pad hR (A + P.n + 1)).2.1.1
    rw [pad_ge (show A ≤ h + 1 by omega), pad_ge (show A ≤ A + P.n + 1 by omega)] at this
    omega
  have h3 : h + 3 < A := by
    by_contra hA
    have := (robust_pad hR (A + 1)).2.2.1 0 (Nat.zero_le _)
    rw [pad_ge (show A ≤ h + 3 by omega), pad_ge (show A ≤ A + 1 + 0 by omega)] at this
    omega
  refine ⟨h3, fun j hj => ?_, fun x hx => ?_⟩
  · by_contra hA
    have := ((robust_pad hR (2 ^ j + 1)).2.1.2.2.1 j hj).1
    rw [pad_lt h1, pad_ge (show A ≤ m (h + 1) + 2 + j by omega)] at this
    omega
  · by_contra hA
    have := (robust_pad hR (x / 2 + 1)).2.2.1 x hx
    rw [pad_lt (show h + 3 < A by omega), pad_ge (show A ≤ m (h + 3) + x by omega)] at this
    omega

/-- **The grade context carries a halving table** (finding R-D3). -/
theorem gradeCtx_halves (O : OracleIface) : (gradeCtx O).Halves := by
  intro P m g A hh
  obtain ⟨h1, -, h3⟩ := grade_low hh
  exact ⟨h1, fun x hx => ⟨h3 x hx, hh.holds.2.2.1 x hx⟩⟩

/-- **The entries lie below the bound**: the row word, the entry and its three words. -/
theorem grade_entry (hR : Robust A m fun m' => GradeRaw O P m' h A) {g i : ℕ} (hg : g < m h)
    (hi : i < gradeCount P.n g) :
    h + 2 < A ∧ m (h + 2) + g < A ∧ entryAddr m h g i + 2 < A := by
  have hh : h < A := by
    by_contra hA
    have := (robust_pad hR (topGrade P.n + 2)).1
    rw [pad_ge (by omega)] at this
    omega
  -- a descriptor whose words are all the padding value `Z > n` is impossible
  have key : ∀ Z, A ≤ Z → P.n < Z → ∀ D, A ≤ D →
      ¬ (∃ (H : Host) (C : Chain), ChainDescAt (pad m A Z) D (Qof P) H C ∧
        C.m = gradeLen P.n g i) := by
    rintro Z hZA hZn D hD ⟨H, C, hC, hm⟩
    have e2 := hC.2.2.2.1
    rw [pad_ge (by omega)] at e2
    grind [gradeLen]
  have h2 : h + 2 < A := by
    by_contra hA
    set Z := A + P.n + 1
    obtain ⟨H, C, N, hC, -, -, -, -, -, hm, -⟩ := (robust_pad hR Z).2.2.2 g i
      (by rw [pad_lt hh]; exact hg) hi
    grind [Chazelle.Core.ShootCut.pad_ge]
  have hr : m (h + 2) + g < A := by
    by_contra hA
    set Z := A + P.n + 1
    obtain ⟨H, C, N, hC, -, -, -, -, -, hm, -⟩ := (robust_pad hR Z).2.2.2 g i
      (by rw [pad_lt hh]; exact hg) hi
    grind [Chazelle.Core.ShootCut.pad_ge, Chazelle.Core.ShootCut.pad_lt]
  have hE : entryAddr m h g i < A := by
    by_contra hA
    set Z := A + P.n + 1
    obtain ⟨H, C, N, hC, -, -, -, -, -, hm, -⟩ := (robust_pad hR Z).2.2.2 g i
      (by rw [pad_lt hh]; exact hg) hi
    grind [Chazelle.Core.ShootCut.pad_ge, Chazelle.Core.ShootCut.pad_lt, entryAddr]
  -- the descriptor word is below the bound (`ChainWF`)
  obtain ⟨H₀, C₀, N₀, -, hwf₀, -⟩ := hR.holds.2.2.2 g i hg hi
  
  have hE2 : entryAddr m h g i + 2 < A := by
    by_contra hA
    set Z := A + m (entryAddr m h g i) + 1
    obtain ⟨H, C, N, -, -, -, -, -, -, -, -, -, -, e1, -⟩ := (robust_pad hR Z).2.2.2 g i
      (by rw [pad_lt hh]; exact hg) hi
    have eE : m (m (h + 2) + g) + 3 * i = entryAddr m h g i := rfl
    grind [Chazelle.Core.ShootCut.pad_ge, Chazelle.Core.ShootCut.pad_lt]
  omega

end ShootCut

end

end Chazelle.Core
