module

public import Mathlib

/-!
T1, unit U-1123, PC run 20261020T0003Z-10609. P0043 Wu 2008 Lemma 2.2 with Υ₁₁ repaired to
p₄ < N^{1/2−3κ₁}, F-0050, in the REAL exponent model: a prime factor q of a is recorded by the real
number log q / log N, with no rounding to multiples of 1/D. This removes the first limitation listed
in Wu2008Lemma22Fixed.lean. The integer form is Wu2008Lemma22Int.lean.

Parameters: any κ₁, κ₂ meeting Wu's hypotheses of Lemma 2.2, κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2,
3κ₁ − κ₂ ≤ 1/6, `Admissible`; em = 1/2 − 3κ₁, e13 = 1/3. Wu's values κ₁ = 1/13.27, κ₂ = 1/8.24 are
`wu_admissible`.
Plain math twin: for a finite set d of distinct reals, each at least κ₁, with sum below 1,
4·[#d ≤ 2] ≥ 3 + Υ₂ − Υ₃ − Υ₄ + Υ₅ + Υ₆ − 2Υ₇ − Υ₈ − Υ₉ − Υ₁₀ − Υ₁₁, the terms as in
Wu2008Lemma22Fixed.lean with every threshold divided by D. The proof is the same case split.
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

lemma wu_admissible : Admissible wk1 wk2 := by norm_num [Admissible, wk1, wk2]

def pairsLT (S : Finset ℝ) : Finset (ℝ × ℝ) := (S ×ˢ S).filter (fun p => p.1 < p.2)

/-- `p₁ = e` is the least and `p₂ = f` the second least exponent of `d`. -/
def low2 (d : Finset ℝ) (e f : ℝ) : Prop := ∀ q ∈ d, f ≤ q ∨ q = e

def U2 (k2 : ℝ) (d : Finset ℝ) : ℤ := if ∀ q ∈ d, k2 ≤ q then 1 else 0
def U3 (d : Finset ℝ) : ℤ := #(d.filter (· < e13))
def U4 (k1 : ℝ) (d : Finset ℝ) : ℤ := #(d.filter (· < em k1))
def U5 (k2 : ℝ) (d : Finset ℝ) : ℤ := #((d ×ˢ d).filter (fun p => p.1 < p.2 ∧ p.2 < k2))
def U6 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ := #((d ×ˢ d).filter (fun p => k1 ≤ p.1 ∧ p.1 < k2 ∧ k2 ≤ p.2 ∧ p.2 < em k1))
def U7 (k1 : ℝ) (d : Finset ℝ) : ℤ :=
  #((d ×ˢ d).filter (fun p => p.1 < p.2 ∧ em k1 ≤ p.1 ∧ p.1 + 2 * p.2 < 1 ∧ low2 d p.1 p.2))
def U8 (d : Finset ℝ) : ℤ :=
  #((d ×ˢ d).filter (fun p => p.1 < e13 ∧ e13 ≤ p.2 ∧ p.1 + 2 * p.2 < 1 ∧ low2 d p.1 p.2))
def U9 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ :=
  #((d ×ˢ d).filter (fun p => k2 ≤ p.1 ∧ p.1 < em k1 ∧ em k1 ≤ p.2 ∧ p.1 + 2 * p.2 < 1 ∧
    ∀ q ∈ d, 1 ≤ p.1 + p.2 + 2 * q ∨ q = p.1 ∨ q = p.2))
def quads (d : Finset ℝ) : Finset (ℝ × ℝ × ℝ × ℝ) := d ×ˢ d ×ˢ d ×ˢ d
def U10 (k2 : ℝ) (d : Finset ℝ) : ℤ :=
  #((quads d).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2 ∧
    t.2.2.2 < k2 ∧ low2 d t.1 t.2.1))
/-- Υ₁₁ with the repaired range `p₄ < N^{1/2−3κ₁}`. -/
def U11 (k1 k2 : ℝ) (d : Finset ℝ) : ℤ :=
  #((quads d).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < k2 ∧
    k2 ≤ t.2.2.2 ∧ t.2.2.2 < em k1 ∧ low2 d t.1 t.2.1))

def rhs (k1 k2 : ℝ) (d : Finset ℝ) : ℤ :=
  3 + U2 k2 d - U3 d - U4 k1 d + U5 k2 d + U6 k1 k2 d - 2 * U7 k1 d - U8 d - U9 k1 k2 d - U10 k2 d - U11 k1 k2 d
def lhs (d : Finset ℝ) : ℤ := if #d ≤ 2 then 4 else 0

/-! ## Finset helpers -/

lemma exists_min_split {S : Finset ℝ} (h : S.Nonempty) :
    ∃ a ∈ S, (∀ q ∈ S, a ≤ q) ∧ ∀ q ∈ S.erase a, a < q := by
  refine ⟨S.min' h, S.min'_mem h, fun q hq => S.min'_le q hq, fun q hq => ?_⟩
  exact lt_of_le_of_ne (S.min'_le q (mem_of_mem_erase hq)) (Ne.symm (mem_erase.1 hq).1)

lemma exists_two_least {S : Finset ℝ} (h : 2 ≤ #S) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ q ∈ S, q = a ∨ b ≤ q := by
  obtain ⟨a, ha, hmin, hlt⟩ := exists_min_split (S := S) (card_pos.1 (by omega))
  have hne : (S.erase a).Nonempty := card_pos.1 (by rw [card_erase_of_mem ha]; omega)
  obtain ⟨b, hb, hbmin, -⟩ := exists_min_split hne
  exact ⟨a, b, ha, mem_of_mem_erase hb, hlt b hb, fun q hq => by grind⟩

lemma exists_three_least {S : Finset ℝ} (h : 3 ≤ #S) :
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c ∧
      ∀ q ∈ S, q = a ∨ q = b ∨ c ≤ q := by
  obtain ⟨a, ha, -, hlt⟩ := exists_min_split (S := S) (card_pos.1 (by omega))
  have h2 : 2 ≤ #(S.erase a) := by rw [card_erase_of_mem ha]; omega
  obtain ⟨b, c, hb, hc, hbc, hq⟩ := exists_two_least h2
  exact ⟨a, b, c, ha, mem_of_mem_erase hb, mem_of_mem_erase hc, hlt b hb, hbc,
    fun q hqs => by grind⟩

lemma sum3_le {S : Finset ℝ} (hS : ∀ x ∈ S, 0 ≤ x) {a b c : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hab : a < b) (hbc : b < c) : a + b + c ≤ ∑ x ∈ S, x := by
  have h := sum_le_sum_of_subset_of_nonneg (f := id) (show ({a,b,c} : Finset ℝ) ⊆ S by grind)
    (fun x hx _ => hS x hx)
  simpa [sum_insert, hab.ne, hbc.ne, (hab.trans hbc).ne, add_assoc] using h

lemma one_le_card_of_mem {α : Type*} {s : Finset α} {x : α} (h : x ∈ s) : (1 : ℤ) ≤ #s := by
  exact_mod_cast card_pos.2 ⟨x, h⟩

lemma two_le_card_of_mem {s : Finset ℝ} {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (2 : ℤ) ≤ #s := by
  have h := card_le_card (show ({x, y} : Finset ℝ) ⊆ s by grind)
  rw [card_pair hne] at h
  exact_mod_cast h

lemma three_le_card_of_mem {s : Finset ℝ} {x y z : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (3 : ℤ) ≤ #s := by
  have h := card_le_card (show ({x, y, z} : Finset ℝ) ⊆ s by grind)
  have hxyz : ({x, y, z} : Finset ℝ).card = 3 := by grind
  rw [hxyz] at h
  exact_mod_cast h

/-! ## Structural lemmas -/

section structural
variable (k1 k2 : ℝ) (d : Finset ℝ)

def Aset (k2 : ℝ) (d : Finset ℝ) : Finset ℝ := d.filter (· < k2)
def Bset (k1 k2 : ℝ) (d : Finset ℝ) : Finset ℝ := d.filter (fun e => k2 ≤ e ∧ e < em k1)

lemma U6_eq (hk : ∀ e ∈ d, k1 ≤ e) : U6 k1 k2 d = #(Aset k2 d) * #(Bset k1 k2 d) := by
  rw [U6, ← Nat.cast_mul, ← card_product]
  congr 2
  ext ⟨a, b⟩
  grind [Aset, Bset]

lemma U5_eq : U5 k2 d = #(pairsLT (Aset k2 d)) := by
  unfold U5 pairsLT
  congr 2
  ext ⟨a, b⟩
  grind [Aset]

lemma U4_ge (h2m : k2 < em k1) : (#(Aset k2 d) : ℤ) + #(Bset k1 k2 d) ≤ U4 k1 d := by
  unfold U4
  have hsub : Aset k2 d ∪ Bset k1 k2 d ⊆ d.filter (· < em k1) := by grind [Aset, Bset]
  have hdisj : Disjoint (Aset k2 d) (Bset k1 k2 d) := by grind [disjoint_left, Aset, Bset]
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at this
  exact_mod_cast this

lemma U4_le_U3 (hm3 : em k1 ≤ e13) : U4 k1 d ≤ U3 d := by
  unfold U3 U4
  exact_mod_cast card_le_card (show d.filter (· < em k1) ⊆ d.filter (· < e13) by grind)

end structural

lemma nn {α : Type*} (s : Finset α) : (0 : ℤ) ≤ (#s : ℤ) := by positivity

/-- **Wu 2008 Lemma 2.2, Υ₁₁ repaired, pointwise in the real exponent model.** -/
theorem pointwise (k1 k2 : ℝ) (hA : Admissible k1 k2) (d : Finset ℝ) (hk : ∀ e ∈ d, k1 ≤ e) (hs : ∑ x ∈ d, x < 1) :
    rhs k1 k2 d ≤ lhs d := by
  have c12 := hA.2.1
  have c2m : k2 < em k1 := by unfold em; linarith [hA.2.2.1]
  have cm3 : em k1 ≤ e13 := by unfold em e13; linarith [hA.1]
  have csum : 1 ≤ k2 + em k1 + 2 * e13 := by unfold em e13; linarith [hA.2.2.2]
  have c1 : 0 < k1 := by linarith [hA.1]
  have hnn : ∀ x ∈ d, 0 ≤ x := fun x hx => by linarith [hk x hx]
  have h7 : 0 ≤ U7 k1 d := nn _
  have h8 : 0 ≤ U8 d := nn _
  have h9 : 0 ≤ U9 k1 k2 d := nn _
  have h10 : 0 ≤ U10 k2 d := nn _
  have h11 : 0 ≤ U11 k1 k2 d := nn _
  have h34 := U4_le_U3 k1 d cm3
  have h4 := U4_ge k1 k2 d c2m
  have hlhs : 0 ≤ lhs d := by unfold lhs; split_ifs <;> norm_num
  have hU6 := U6_eq k1 k2 d hk
  have hU5 := U5_eq k2 d
  unfold rhs
  set A := Aset k2 d
  set B := Bset k1 k2 d
  rcases Nat.lt_or_ge (#A) 2 with hA | hA
  swap
  · -- at least two small exponents
    obtain ⟨a1, a2, ha1, ha2, h12, hq⟩ := exists_two_least hA
    have ha1' := mem_filter.1 ha1
    have ha2' := mem_filter.1 ha2
    set A2 := (A.erase a1).erase a2 with hA2
    have hA2sub : ∀ y ∈ A2, y ∈ A ∧ a2 < y := by grind
    have hcardA : (#A : ℤ) = #A2 + 2 := by
      have h2 := card_erase_of_mem (show a2 ∈ A.erase a1 from mem_erase.2 ⟨h12.ne', ha2⟩)
      have h1 := card_erase_of_mem ha1
      rw [← hA2] at h2
      omega
    have hP : (#(pairsLT A) : ℤ) = #(pairsLT A2) + #A2 + (#A2 + 1) := by
      have h : #A = #A2 + 2 := by exact_mod_cast hcardA
      simp only [pairsLT, card_product_filter_lt, h]
      simp [Nat.choose_succ_succ]
      ring
    have hlow : low2 d a1 a2 := by grind [low2, Aset]
    have hU2 : U2 k2 d = 0 := by
      unfold U2; rw [if_neg]; intro h; have := h a1 ha1'.1; linarith [ha1'.2]
    have hU10 : (#(pairsLT A2) : ℤ) ≤ U10 k2 d := by
      unfold U10
      have := card_le_card_of_injOn (fun p : ℝ × ℝ => (a1, a2, p.1, p.2))
        (s := pairsLT A2) (t := (quads d).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧
          t.2.2.1 < t.2.2.2 ∧ t.2.2.2 < k2 ∧ low2 d t.1 t.2.1)) ?_ ?_
      · exact_mod_cast this
      · intro p hp
        grind [pairsLT, quads, Aset]
      · intro p _ p' _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.2.1 h.2.2.2
    have hU11 : (#A2 : ℤ) * #B ≤ U11 k1 k2 d := by
      unfold U11
      have := card_le_card_of_injOn (fun p : ℝ × ℝ => (a1, a2, p.1, p.2))
        (s := A2 ×ˢ B) (t := (quads d).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧
          t.2.2.1 < k2 ∧ k2 ≤ t.2.2.2 ∧ t.2.2.2 < em k1 ∧ low2 d t.1 t.2.1)) ?_ ?_
      · rw [card_product] at this; exact_mod_cast this
      · intro p hp
        grind [quads, Aset, Bset]
      · intro p _ p' _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.2.1 h.2.2.2
    rw [hU6, hU5, hP, hU2]
    rw [hcardA] at h4 hU6
    have e6 : ((#A2 : ℤ) + 2) * #B = #A2 * #B + 2 * #B := by ring
    rw [hcardA, e6]
    linarith
  rcases Nat.lt_or_ge (#A) 1 with hA0 | hA1
  · -- no small exponent
    have hA0' : A = ∅ := card_eq_zero.1 (by omega)
    have hall : ∀ q ∈ d, k2 ≤ q := by
      intro q hq; by_contra h
      have : q ∈ A := mem_filter.2 ⟨hq, by linarith [not_le.1 h]⟩
      rw [hA0'] at this; exact absurd this (Finset.notMem_empty q)
    have hU2 : U2 k2 d = 1 := by unfold U2; rw [if_pos hall]
    have hU5' : U5 k2 d = 0 := by rw [hU5, hA0']; rfl
    have hU6' : U6 k1 k2 d = 0 := by rw [hU6, hA0']; simp
    rw [hU2, hU5', hU6']
    by_cases hd : #d ≤ 2
    · have : lhs d = 4 := by unfold lhs; rw [if_pos hd]
      rw [this]; linarith [nn (d.filter (· < em k1)), h34, h4, nn A, nn B]
    have hd3 : 3 ≤ #d := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hq⟩ := exists_three_least hd3
    have hsum := sum3_le hnn ha hb hc hab hbc
    have hka := hall a ha
    have hlow : low2 d a b := by grind [low2]
    have hlhs0 : lhs d = 0 := by unfold lhs; rw [if_neg hd]
    rw [hlhs0]
    rcases lt_or_ge a (em k1) with hae | hae
    · have hU4a : (1 : ℤ) ≤ U4 k1 d := one_le_card_of_mem (mem_filter.2 ⟨ha, hae⟩)
      rcases lt_or_ge b (em k1) with hbe | hbe
      · have : (2 : ℤ) ≤ U4 k1 d := two_le_card_of_mem (mem_filter.2 ⟨ha, hae⟩)
          (mem_filter.2 ⟨hb, hbe⟩) (ne_of_lt hab)
        linarith
      rcases lt_or_ge b e13 with hb13 | hb13
      · have hU3b : (2 : ℤ) ≤ U3 d := two_le_card_of_mem (mem_filter.2 ⟨ha, by linarith⟩)
          (mem_filter.2 ⟨hb, hb13⟩) (ne_of_lt hab)
        rcases lt_or_ge c e13 with hc13 | hc13
        · have : (3 : ℤ) ≤ U3 d := three_le_card_of_mem (mem_filter.2 ⟨ha, by linarith⟩)
            (mem_filter.2 ⟨hb, hb13⟩) (mem_filter.2 ⟨hc, hc13⟩) hab hbc
          linarith
        · have : (1 : ℤ) ≤ U9 k1 k2 d := one_le_card_of_mem (x := (a, b)) (by grind)
          linarith
      · have hU3a : (1 : ℤ) ≤ U3 d := one_le_card_of_mem (mem_filter.2 ⟨ha, by linarith⟩)
        have : (1 : ℤ) ≤ U8 d := one_le_card_of_mem (x := (a, b)) (by grind)
        have : (1 : ℤ) ≤ U9 k1 k2 d := one_le_card_of_mem (x := (a, b)) (by grind)
        linarith
    · have hU7 : (1 : ℤ) ≤ U7 k1 d := one_le_card_of_mem (x := (a, b)) (by grind)
      rcases lt_or_ge b e13 with hb13 | hb13
      · have : (2 : ℤ) ≤ U3 d := two_le_card_of_mem (mem_filter.2 ⟨ha, by linarith⟩)
          (mem_filter.2 ⟨hb, hb13⟩) (ne_of_lt hab)
        linarith [nn (d.filter (· < em k1))]
      · rcases lt_or_ge a e13 with ha13 | ha13
        · have : (1 : ℤ) ≤ U3 d := one_le_card_of_mem (mem_filter.2 ⟨ha, ha13⟩)
          have : (1 : ℤ) ≤ U8 d := one_le_card_of_mem (x := (a, b)) (by grind)
          linarith [nn (d.filter (· < em k1))]
        · exfalso; unfold e13 at ha13; linarith
  · -- exactly one small exponent
    have hA1' : #A = 1 := by omega
    obtain ⟨a1, hA1eq⟩ := card_eq_one.1 hA1'
    have ha1 : a1 ∈ A := by rw [hA1eq]; exact mem_singleton_self _
    have ha1' := mem_filter.1 ha1
    have hU2 : U2 k2 d = 0 := by
      unfold U2; rw [if_neg]; intro h; have := h a1 ha1'.1; linarith [ha1'.2]
    have hU5' : U5 k2 d = 0 := by
      rw [hU5, hA1eq]
      simp [pairsLT]
    rw [hU2, hU5', hU6, hA1']
    have hU3a : (1 : ℤ) ≤ U3 d := one_le_card_of_mem (mem_filter.2 ⟨ha1'.1, by linarith [ha1'.2]⟩)
    by_cases hd : #d ≤ 2
    · have : lhs d = 4 := by unfold lhs; rw [if_pos hd]
      rw [this]; rw [hA1'] at h4; push_cast at h4 ⊢; linarith
    have hd3 : 3 ≤ #d := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hq⟩ := exists_three_least hd3
    have hsum := sum3_le hnn ha hb hc hab hbc
    have hlhs0 : lhs d = 0 := by unfold lhs; rw [if_neg hd]
    rw [hlhs0]
    rw [hA1'] at h4
    push_cast at h4 ⊢
    have ha_small : a < k2 := by grind
    have hlow : low2 d a b := by grind [low2]
    rcases lt_or_ge b e13 with hb13 | hb13
    · have : (2 : ℤ) ≤ U3 d := two_le_card_of_mem (mem_filter.2 ⟨ha, by linarith⟩)
        (mem_filter.2 ⟨hb, hb13⟩) (ne_of_lt hab)
      linarith
    · have : (1 : ℤ) ≤ U8 d := one_le_card_of_mem (x := (a, b)) (by grind)
      linarith

end

end GoldbachLean.Wu2008.WuReal

