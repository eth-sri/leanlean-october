module

public import Mathlib

/-!
T1, unit U-1123, PC run 20261020T0003Z-10609. P0043 Wu 2008 Lemma 2.2 with Υ₁₁ repaired to
p₄ < N^{1/2−3κ₁}, F-0050, in the REAL exponent model: a prime factor q of a is recorded by the real
number log q / log N, with no rounding to multiples of 1/D. The integer form is in `Sum`.

Parameters: any κ₁, κ₂ meeting Wu's hypotheses of Lemma 2.2, κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2,
3κ₁ − κ₂ ≤ 1/6, `Admissible`; em = 1/2 − 3κ₁, e13 = 1/3.

Plain math twin: for a finite set d of distinct reals, each at least κ₁, with sum below 1,
4·[#d ≤ 2] ≥ 3 + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁, the terms as in Wu's lemma.
KNOWN mathematics, Wu's lemma with its range fixed. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuReal
open Finset

@[expose] public noncomputable section
open scoped Classical

/-- Wu's values, κ₁ = 1/13.27 and κ₂ = 1/8.24. The lemma is proved for every admissible pair. -/
def wk1 : ℝ := 100 / 1327
def wk2 : ℝ := 100 / 824
def em (k1 : ℝ) : ℝ := 1 / 2 - 3 * k1
def e13 : ℝ := 1 / 3

/-- Wu's hypotheses on κ₁, κ₂ for Lemma 2.2, p. 371: κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2,
3κ₁ − κ₂ < 1/6. The proof below needs only the non-strict last one. -/
def Admissible (k1 k2 : ℝ) : Prop :=
  1 / 18 ≤ k1 ∧ k1 < k2 ∧ 3 * k1 + k2 < 1 / 2 ∧ 3 * k1 - k2 ≤ 1 / 6

lemma wu_admissible : Admissible wk1 wk2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [wk1, wk2] <;> norm_num

/-- The small exponents: those below `k2`. -/
abbrev Aset (k2 : ℝ) (d : Finset ℝ) : Finset ℝ := d.filter (· < k2)
/-- The medium exponents: `k2 ≤ e < em k1`. -/
abbrev Bset (k1 k2 : ℝ) (d : Finset ℝ) : Finset ℝ := d.filter (fun e => k2 ≤ e ∧ e < em k1)
/-- The exponents `em k1 ≤ e < 1/3`. -/
abbrev Cset (k1 : ℝ) (d : Finset ℝ) : Finset ℝ := d.filter (fun e => em k1 ≤ e ∧ e < e13)
/-- `p₁ = e` is the least and `p₂ = f` the second least exponent of `d`. -/
abbrev low2 (d : Finset ℝ) (e f : ℝ) : Prop := ∀ q ∈ d, f ≤ q ∨ q = e

/-- Υ₂ = 1 iff there is no exponent below `k2`. -/
abbrev U2 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := if Aset k2 d = ∅ then 1 else 0
/-- Υ₃: the exponents below `1/3`. -/
abbrev U3 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := #(d.filter (· < e13))
/-- Υ₄: the exponents below `em k1`. -/
abbrev U4 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := #(d.filter (· < em k1))
/-- Υ₅: pairs of exponents below `k2`. -/
abbrev U5 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := ((#(Aset k2 d)).choose 2 : ℕ)
abbrev U6 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := ((#(Aset k2 d)) * #(Bset k1 k2 d) : ℕ)
abbrev U7 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ :=
  #((d ×ˢ d).filter (fun p => p.1 < p.2 ∧ (em k1) ≤ p.1 ∧ p.1 + 2 * p.2 < 1 ∧ low2 d p.1 p.2))
abbrev U8 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ :=
  #((d ×ˢ d).filter (fun p => p.1 < e13 ∧ e13 ≤ p.2 ∧ p.1 + 2 * p.2 < 1 ∧ low2 d p.1 p.2))
abbrev U9 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ :=
  #((d ×ˢ d).filter (fun p => k2 ≤ p.1 ∧ p.1 < (em k1) ∧ (em k1) ≤ p.2 ∧ p.1 + 2 * p.2 < 1 ∧
    ∀ q ∈ d, 1 ≤ p.1 + p.2 + 2 * q ∨ q = p.1 ∨ q = p.2))
abbrev U10 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := ((#(Aset k2 d) - 2).choose 2 : ℕ)
abbrev U11 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := ((#(Aset k2 d) - 2) * #(Bset k1 k2 d) : ℕ)
abbrev rhs (k1 k2 : ℝ) (d : Finset ℝ) : ℤ :=
  3 + U2 k1 k2 d + U5 k1 k2 d + U6 k1 k2 d - U3 k1 k2 d - U4 k1 k2 d - 2 * U7 k1 k2 d - U8 k1 k2 d - U9 k1 k2 d - U10 k1 k2 d - U11 k1 k2 d
abbrev lhs (d : Finset ℝ) : ℤ := if #d ≤ 2 then 4 else 0

/-! ## Finset helpers -/

lemma sum3_le {S : Finset ℝ} (hS : ∀ x ∈ S, 0 ≤ x) {a b c : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hab : a < b) (hbc : b < c) : a + b + c ≤ ∑ x ∈ S, x := by
  have hsub : ({a, b, c} : Finset ℝ) ⊆ S := by grind
  have := sum_le_sum_of_subset_of_nonneg (f := id) hsub (fun x hx _ => hS x hx)
  rw [sum_insert (by simp; constructor <;> intro h <;> linarith),
    sum_insert (by simp; intro h; linarith), sum_singleton] at this
  simpa [add_assoc] using this

lemma one_le_card_of_mem {α : Type*} {s : Finset α} {x : α} (h : x ∈ s) : (1 : ℤ) ≤ #s := by
  exact_mod_cast card_pos.2 ⟨x, h⟩

lemma two_le_card_of_mem {s : Finset ℝ} {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (2 : ℤ) ≤ #s := by
  have := card_le_card (show ({x, y} : Finset ℝ) ⊆ s by grind)
  rw [card_pair hne] at this; exact_mod_cast this

/-- The two least elements of a set of reals with at least two elements. -/
lemma exists_two_least {α : Type*} [LinearOrder α] {S : Finset α} (h : 2 ≤ #S) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ q ∈ S, q = a ∨ b ≤ q := by
  let f := S.orderEmbOfFin (k := #S) rfl
  have h0 : 0 < #S := by omega
  have h1 : 1 < #S := by omega
  refine ⟨f ⟨0, h0⟩, f ⟨1, h1⟩, S.orderEmbOfFin_mem _ _, S.orderEmbOfFin_mem _ _,
    f.strictMono (by simp), fun q hq => ?_⟩
  obtain ⟨i, rfl⟩ := (Set.mem_range).1 (by
    change q ∈ Set.range (S.orderEmbOfFin (k := #S) rfl)
    rw [S.range_orderEmbOfFin]; exact hq)
  have hi : i.val = 0 ∨ 1 ≤ i.val := by omega
  rcases hi with h | h
  · left; congr 1; exact Fin.ext h
  · right; exact f.le_iff_le.2 (by omega)

/-- The three least elements of a set of reals with at least three elements. -/
lemma exists_three_least {α : Type*} [LinearOrder α] {S : Finset α} (h : 3 ≤ #S) :
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c ∧ ∀ q ∈ S, q = a ∨ q = b ∨ c ≤ q := by
  let f := S.orderEmbOfFin (k := #S) rfl
  have h0 : 0 < #S := by omega
  have h1 : 1 < #S := by omega
  have h2 : 2 < #S := by omega
  refine ⟨f ⟨0, h0⟩, f ⟨1, h1⟩, f ⟨2, h2⟩,
    S.orderEmbOfFin_mem _ _, S.orderEmbOfFin_mem _ _, S.orderEmbOfFin_mem _ _, ?_, ?_, ?_⟩
  · exact f.strictMono (by simp)
  · exact f.strictMono (by simp)
  · intro q hq
    obtain ⟨i, rfl⟩ := (Set.mem_range).1 (by
      change q ∈ Set.range (S.orderEmbOfFin (k := #S) rfl)
      rw [S.range_orderEmbOfFin]; exact hq)
    have hi : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val := by omega
    rcases hi with h|h|h
    · left; congr 1; exact Fin.ext h
    · right; left; congr 1; exact Fin.ext h
    · right; right; exact f.le_iff_le.2 (by omega)

lemma nn {α : Type*} (s : Finset α) : (0 : ℤ) ≤ (#s : ℤ) := by positivity

section bounds
variable (k1 k2 : ℝ) (d : Finset ℝ)

end bounds

section pair_bounds

lemma U8_lb {k1 k2 : ℝ} {d : Finset ℝ} {p1 p2 : ℝ} (h1d : p1 ∈ d) (h2d : p2 ∈ d)
    (h1 : p1 < e13) (h2 : e13 ≤ p2) (hsum : p1 + 2 * p2 < 1) (hlow : low2 d p1 p2) :
    (1 : ℤ) ≤ U8 k1 k2 d :=
  one_le_card_of_mem (x := (p1, p2)) (mem_filter.2 ⟨mem_product.2 ⟨h1d, h2d⟩, h1, h2, hsum, hlow⟩)

lemma U9_lb {k1 k2 : ℝ} {d : Finset ℝ} {p1 p2 : ℝ} (h1d : p1 ∈ d) (h2d : p2 ∈ d)
    (h12 : p1 < p2) (hp1 : k2 ≤ p1) (hp1m : p1 < em k1) (hp2 : em k1 ≤ p2)
    (hsum : p1 + 2 * p2 < 1) (hlow : low2 d p1 p2)
    (hother : ∀ q ∈ d, q ≠ p1 → q ≠ p2 → e13 ≤ q)
    (hc : 1 ≤ k2 + em k1 + 2 * e13) : (1 : ℤ) ≤ U9 k1 k2 d := by
  refine one_le_card_of_mem (x := (p1, p2)) (mem_filter.2 ⟨mem_product.2 ⟨h1d, h2d⟩,
    hp1, hp1m, hp2, hsum, fun q hq => ?_⟩)
  rcases hlow q hq with hq2 | hq1
  · by_cases h : q = p2
    · exact Or.inr (Or.inr h)
    · left
      have := hother q hq (by intro h'; subst h'; linarith) h
      linarith
  · exact Or.inr (Or.inl hq1)

end pair_bounds

/-- **Wu 2008 Lemma 2.2, Υ₁₁ repaired, pointwise in the real exponent model.** -/
theorem pointwise (k1 k2 : ℝ) (hA : Admissible k1 k2) (d : Finset ℝ) (hk : ∀ e ∈ d, k1 ≤ e) (hs : ∑ x ∈ d, x < 1) :
    rhs k1 k2 d ≤ lhs d := by
  obtain ⟨h18, h12, hsumk, hdiff⟩ := hA
  have hk1 : 0 < k1 := by linarith
  have c2m : k2 < em k1 := by unfold em; linarith
  have cm3 : em k1 ≤ e13 := by unfold em e13; linarith
  have csum : 1 ≤ k2 + em k1 + 2 * e13 := by unfold em e13; linarith
  have hnn : ∀ x ∈ d, 0 ≤ x := fun x hx => by linarith [hk x hx]
  have n3 : (0 : ℤ) ≤ U3 k1 k2 d := nn _
  have n4 : (0 : ℤ) ≤ U4 k1 k2 d := nn _
  have n7 : (0 : ℤ) ≤ U7 k1 k2 d := nn _
  have n8 : (0 : ℤ) ≤ U8 k1 k2 d := nn _
  have n9 : (0 : ℤ) ≤ U9 k1 k2 d := nn _
  have n10 : (0 : ℤ) ≤ U10 k1 k2 d := by unfold U10; positivity
  have n11 : (0 : ℤ) ≤ U11 k1 k2 d := by unfold U11; positivity
  have hlhs : 0 ≤ lhs d := by unfold lhs; split_ifs <;> norm_num
  have h34 : ((#(Aset k2 d) : ℤ) + #(Bset k1 k2 d) + #(Cset k1 d)) ≤ U3 k1 k2 d ∧
      ((#(Aset k2 d) : ℤ) + #(Bset k1 k2 d)) ≤ U4 k1 k2 d := by
    
      have hme : em k1 ≤ e13 := by unfold em e13; linarith
      have hsubAB : Aset k2 d ∪ Bset k1 k2 d ⊆ d.filter (· < em k1) := by grind
      have hsub : (Aset k2 d ∪ Bset k1 k2 d) ∪ Cset k1 d ⊆ d.filter (· < e13) := by grind
      have hAB : Disjoint (Aset k2 d) (Bset k1 k2 d) := by
        rw [disjoint_left]; grind
      have hABC : Disjoint (Aset k2 d ∪ Bset k1 k2 d) (Cset k1 d) := by
        rw [disjoint_left]; grind
      have h4 := card_le_card hsubAB
      rw [card_union_of_disjoint hAB] at h4
      have h3 := card_le_card hsub
      rw [card_union_of_disjoint hABC, card_union_of_disjoint hAB] at h3
      exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
  obtain ⟨hU3, hU4⟩ := h34
  unfold rhs
  rcases Nat.lt_or_ge (#(Aset k2 d)) 1 with hA0 | hA1
  · -- A empty
    have hAe : Aset k2 d = ∅ := card_eq_zero.1 (by omega)
    have hU2' : U2 k1 k2 d = 1 := by simp [U2, hAe]
    have hU5' : U5 k1 k2 d = 0 := by simp [U5, hAe]
    have hU6' : U6 k1 k2 d = 0 := by simp [U6, hAe]
    rw [hU2', hU5', hU6']
    by_cases hd2 : #d ≤ 2
    · have hl : lhs d = 4 := by simp [lhs, hd2]
      rw [hl]; linarith
    · have hl : lhs d = 0 := by simp [lhs, hd2]
      rw [hl]
      have hd3 : 3 ≤ #d := by omega
      obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hq⟩ := exists_three_least hd3
      have hs3 : x + y + z < 1 := lt_of_le_of_lt (sum3_le hnn hx hy hz hxy hyz) hs
      have hx2 : k2 ≤ x := by
        by_contra h
        have : x ∈ Aset k2 d := mem_filter.2 ⟨hx, not_le.1 h⟩
        rw [hAe] at this; simpa using this
      have hlow : low2 d x y := by
        intro q hq'
        rcases hq q hq' with h | h | h
        · exact Or.inr h
        · exact Or.inl (le_of_eq h.symm)
        · exact Or.inl (by linarith)
      have hx2y : x + 2 * y < 1 := by linarith
      rcases lt_or_ge x (em k1) with hxem | hxem
      · rcases lt_or_ge y (em k1) with hyem | hyem
        · have h3 : (2 : ℤ) ≤ U3 k1 k2 d := two_le_card_of_mem
            (mem_filter.2 ⟨hx, by linarith [hxem, cm3]⟩) (mem_filter.2 ⟨hy, by linarith [hyem, cm3]⟩) (ne_of_lt hxy)
          have h4 : (2 : ℤ) ≤ U4 k1 k2 d := two_le_card_of_mem
            (mem_filter.2 ⟨hx, hxem⟩) (mem_filter.2 ⟨hy, hyem⟩) (ne_of_lt hxy)
          linarith
        · rcases lt_or_ge y e13 with hye | hye
          · have h3 : (2 : ℤ) ≤ U3 k1 k2 d := two_le_card_of_mem
              (mem_filter.2 ⟨hx, by linarith [hxem, cm3]⟩) (mem_filter.2 ⟨hy, hye⟩) (ne_of_lt hxy)
            rcases lt_or_ge z e13 with hze | hze
            · have h3' : (3 : ℤ) ≤ U3 k1 k2 d := by
                have h := card_le_card (show ({x, y, z} : Finset ℝ) ⊆ d.filter (· < e13) by grind)
                rw [card_insert_of_notMem (by simp; constructor <;> intro h' <;> linarith),
                  card_pair (ne_of_lt hyz)] at h
                exact_mod_cast h
              have h4 : (1 : ℤ) ≤ U4 k1 k2 d := one_le_card_of_mem (mem_filter.2 ⟨hx, hxem⟩)
              linarith
            · have h4 : (1 : ℤ) ≤ U4 k1 k2 d := one_le_card_of_mem (mem_filter.2 ⟨hx, hxem⟩)
              have h9 : (1 : ℤ) ≤ U9 k1 k2 d := U9_lb hx hy hxy hx2 hxem hyem hx2y hlow
                (fun q hq' hqx hqy => by
                  rcases hq q hq' with h | h | h
                  · exact absurd h hqx
                  · exact absurd h hqy
                  · exact le_trans hze h) csum
              linarith
          · have h3 : (1 : ℤ) ≤ U3 k1 k2 d := one_le_card_of_mem (mem_filter.2 ⟨hx, by linarith [hxem, cm3]⟩)
            have h4 : (1 : ℤ) ≤ U4 k1 k2 d := one_le_card_of_mem (mem_filter.2 ⟨hx, hxem⟩)
            have h8 : (1 : ℤ) ≤ U8 k1 k2 d := U8_lb hx hy (by linarith [hxem, cm3]) hye hx2y hlow
            have h9 : (1 : ℤ) ≤ U9 k1 k2 d := U9_lb hx hy hxy hx2 hxem hyem hx2y hlow
              (fun q hq' hqx hqy => by
                rcases hq q hq' with h | h | h
                · exact absurd h hqx
                · exact absurd h hqy
                · linarith) csum
            linarith
      · have h7 : (1 : ℤ) ≤ U7 k1 k2 d :=
          one_le_card_of_mem (x := (x, y))
            (mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, hxy, hxem, hx2y, hlow⟩)
        rcases lt_or_ge y e13 with hye | hye
        · have h3 : (2 : ℤ) ≤ U3 k1 k2 d := two_le_card_of_mem
            (mem_filter.2 ⟨hx, by linarith [hxem, cm3, hye, hxy]⟩) (mem_filter.2 ⟨hy, hye⟩) (ne_of_lt hxy)
          linarith
        · rcases lt_or_ge x e13 with hxe | hxe
          · have h3 : (1 : ℤ) ≤ U3 k1 k2 d := one_le_card_of_mem (mem_filter.2 ⟨hx, hxe⟩)
            have h8 : (1 : ℤ) ≤ U8 k1 k2 d := U8_lb hx hy hxe hye hx2y hlow
            linarith
          · exfalso
            have h13 : e13 = 1 / 3 := rfl
            linarith [hs3, hxe, hye, hyz, h13]
  · rcases Nat.lt_or_ge (#(Aset k2 d)) 2 with hA1' | hA2
    · -- A a singleton
      have hA1 : #(Aset k2 d) = 1 := by omega
      obtain ⟨p, hp⟩ := card_eq_one.1 hA1
      have hpA : p ∈ Aset k2 d := by rw [hp]; exact mem_singleton_self p
      have hpd : p ∈ d := (mem_filter.1 hpA).1
      have hpk : p < k2 := (mem_filter.1 hpA).2
      have hAne : Aset k2 d ≠ ∅ := ne_empty_of_mem hpA
      have hU2' : U2 k1 k2 d = 0 := by simp [U2, hAne]
      have hU5' : U5 k1 k2 d = 0 := by simp [U5, hA1]
      have hU6' : U6 k1 k2 d = #(Bset k1 k2 d) := by simp [U6, hA1]
      by_cases hd2 : #d ≤ 2
      · have hl : lhs d = 4 := by simp [lhs, hd2]
        rw [hl, hU2', hU5', hU6']
        linarith [n3, n4]
      · have hl : lhs d = 0 := by simp [lhs, hd2]
        rw [hl]
        have hd3 : 3 ≤ #d := by omega
        obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hq⟩ := exists_three_least hd3
        have hs3 : x + y + z < 1 := lt_of_le_of_lt (sum3_le hnn hx hy hz hxy hyz) hs
        have hxA : x ∈ Aset k2 d := by
          have hxk : x < k2 := by
            rcases hq p hpd with h | h | h
            · rw [← h]; exact hpk
            · rw [h] at hpk; linarith
            · linarith [hyz, h, hpk]
          exact mem_filter.2 ⟨hx, hxk⟩
        have hxp : x = p := by
          rw [hp] at hxA
          simpa using hxA
        have hlow : low2 d p y := by
          intro q hq'
          rcases hq q hq' with h | h | h
          · exact Or.inr (h.trans hxp)
          · exact Or.inl (le_of_eq h.symm)
          · exact Or.inl (by linarith [hxp, hyz, h])
        have hxy2 : p + 2 * y < 1 := by linarith [hxp, hs3, hyz]
        rcases lt_or_ge y e13 with hye | hye
        · have hyg : k2 ≤ y := by
            by_contra h
            have hyA : y ∈ Aset k2 d := mem_filter.2 ⟨hy, not_le.1 h⟩
            rw [hp] at hyA
            have hyp : y = p := by simpa using hyA
            rw [hxp, hyp] at hxy; exact absurd hxy (lt_irrefl p)
          rw [hU2', hU5', hU6']
          rcases lt_or_ge y (em k1) with hym | hym
          · have hB1 : (1 : ℤ) ≤ #(Bset k1 k2 d) := one_le_card_of_mem (mem_filter.2 ⟨hy, hyg, hym⟩)
            linarith [hU3, hU4, nn (Cset k1 d)]
          · have hC1 : (1 : ℤ) ≤ #(Cset k1 d) := one_le_card_of_mem (mem_filter.2 ⟨hy, hym, hye⟩)
            linarith [hU3, hU4, nn (Bset k1 k2 d)]
        · have hB0 : Bset k1 k2 d = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro q hqB
            simp only [Bset, mem_filter] at hqB
            grind
          have hC0 : Cset k1 d = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro q hqC
            simp only [Cset, mem_filter] at hqC
            grind
          have hU6'' : U6 k1 k2 d = 0 := by rw [hU6', hB0]; simp
          have hU3' : (1 : ℤ) ≤ U3 k1 k2 d := by
            have := hU3; rw [hA1, hB0, hC0] at this; simpa using this
          have hU4' : (1 : ℤ) ≤ U4 k1 k2 d := by
            have := hU4; rw [hA1, hB0] at this; simpa using this
          rw [hU2', hU5', hU6'']
          have h8 : (1 : ℤ) ≤ U8 k1 k2 d := U8_lb hpd hy (by linarith [hpk, c2m, cm3]) hye hxy2 hlow
          linarith
    · -- at least two small exponents
      have hAne : Aset k2 d ≠ ∅ := by
        intro h; rw [h] at hA2; simp at hA2
      have hU2' : U2 k1 k2 d = 0 := by simp [U2, hAne]
      rw [hU2']
      unfold U5 U6 U10 U11
      have hcast : ((2 * #(Aset k2 d) - 3 : ℕ) : ℤ) = 2 * (#(Aset k2 d) : ℤ) - 3 := by
        rw [Nat.cast_sub (by omega : 3 ≤ 2 * #(Aset k2 d))]
        push_cast; ring
      have hc5n : (#(Aset k2 d)).choose 2 =
          (#(Aset k2 d) - 2).choose 2 + (2 * #(Aset k2 d) - 3) := by
        let a := #(Aset k2 d)
        have ha2 : 2 ≤ a := hA2
        change a.choose 2 = (a - 2).choose 2 + (2 * a - 3)
        have h1 : (a - 1).choose 2 = (a - 2).choose 2 + (a - 2) := by
          have h := Nat.choose_succ_succ (a - 2) 1
          rw [show (a - 2).succ = a - 1 by omega, show (1 : ℕ).succ = 2 by rfl] at h
          simp only [Nat.choose_one_right] at h
          omega
        have h2 : a.choose 2 = (a - 1).choose 2 + (a - 1) := by
          have h := Nat.choose_succ_succ (a - 1) 1
          rw [show (a - 1).succ = a by omega, show (1 : ℕ).succ = 2 by rfl] at h
          simp only [Nat.choose_one_right] at h
          omega
        omega
      have hc5 : ((#(Aset k2 d)).choose 2 : ℤ) =
          (((#(Aset k2 d) - 2).choose 2 : ℕ) : ℤ) + ((2 * #(Aset k2 d) - 3 : ℕ) : ℤ) := by
        exact_mod_cast hc5n
      have hc6n : #(Aset k2 d) * #(Bset k1 k2 d) =
          (#(Aset k2 d) - 2) * #(Bset k1 k2 d) + 2 * #(Bset k1 k2 d) := by
        nth_rewrite 1 [show #(Aset k2 d) = #(Aset k2 d) - 2 + 2 by omega]
        ring
      have hc6 : (#(Aset k2 d) : ℤ) * #(Bset k1 k2 d) =
          (((#(Aset k2 d) - 2 : ℕ) : ℤ)) * #(Bset k1 k2 d) + 2 * #(Bset k1 k2 d) := by
        exact_mod_cast hc6n
      push_cast
      rw [hc5, hc6]
      linarith [hU3, hU4, n7, n8, n9, nn (Cset k1 d), hlhs]
end

end GoldbachLean.Wu2008.WuReal
