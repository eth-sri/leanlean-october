module

public import RequestProject.SurfaceLink
public import RequestProject.GenusLoops

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open Cell ASC Relation Genus

variable (q : ℕ) [NeZero q]

omit [NeZero q] in
theorem gec_eq_iff' (m n : Fin (8 * q)) :
    gec q m = gec q n ↔
      (m.val / 2 / 4 = n.val / 2 / 4 ∧
        m.val / 2 % 4 % 2 = n.val / 2 % 4 % 2 ∧
        (m.val % 2 + (if 2 ≤ m.val / 2 % 4 then 1 else 0)) % 2
          = (n.val % 2 + (if 2 ≤ n.val / 2 % 4 then 1 else 0)) % 2) := by
  have hm2 : m.val % 2 = 0 ∨ m.val % 2 = 1 := by omega
  have hn2 : n.val % 2 = 0 ∨ n.val % 2 = 1 := by omega
  by_cases h2 : 2 ≤ m.val / 2 % 4 <;> by_cases h4 : 2 ≤ n.val / 2 % 4 <;>
    rcases hm2 with h1 | h1 <;> rcases hn2 with h3 | h3 <;>
    simp [gec, Prod.ext_iff, Fin.ext_iff, decide_eq_decide, h1, h2, h3, h4] <;> omega

theorem fpred_val_pos {n : Fin (8 * q)} {a : ℕ} (hv : n.val = a) (hpos : 0 < a) :
    (fpred n).val = a - 1 := by
  rw [fpred_val, hv, if_neg (by omega)]

theorem genus_polygonData : PolygonData (gvc q) (gec q) where
  three_le := by have := Nat.pos_of_neZero q; omega
  pairs i := by
    have hq := Nat.pos_of_neZero q; have hi := i.isLt
    refine ⟨⟨8 * (i.val / 2 / 4) + 2 * (if i.val / 2 % 4 < 2 then i.val / 2 % 4 + 2
        else i.val / 2 % 4 - 2) + (1 - i.val % 2), by split_ifs <;> omega⟩,
      by rw [Ne, Fin.ext_iff]; simp only []; split_ifs <;> omega,
      by rw [gec_eq_iff']; refine ⟨?_, ?_, ?_⟩ <;> simp only [] <;> split_ifs <;> omega,
      fun k hk => ?_⟩
    obtain ⟨h1, h2, h3⟩ := (gec_eq_iff' q k i).mp hk
    have := k.isLt
    rw [Fin.ext_iff, Fin.ext_iff]; simp only []
    split_ifs at h3 ⊢ <;> omega
  noLoop p := by
    have hq := Nat.pos_of_neZero q; have hp := p.isLt
    have hpar : (p + 1).val % 2 = (p.val + 1) % 2 := by
      rw [fin_succ_val]
      rcases Nat.lt_or_ge (p.val + 1) (8 * q) with h | h
      · rw [Nat.mod_eq_of_lt h]
      · rw [show p.val + 1 = 8 * q by omega, Nat.mod_self]; omega
    by_cases h : p.val % 2 = 0
    · rw [gvc, if_pos h, gvc, if_neg (by omega)]; simp
    · rw [gvc, if_neg h, gvc, if_pos (by omega)]; simp
  vc_surj := by
    have hq := Nat.pos_of_neZero q
    rintro (_ | ⟨h, i⟩)
    · exact ⟨⟨0, by omega⟩, by simp [gvc]⟩
    · have hh := h.isLt
      let k := 2 * (4 * h.val + if i then 1 else 0) + 1
      refine ⟨⟨k, by dsimp [k]; split_ifs <;> omega⟩, ?_⟩
      rw [gvc, if_neg (by dsimp [k]; split_ifs <;> omega)]
      simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff]
      refine ⟨by dsimp [k]; split_ifs <;> omega, ?_⟩
      have e2 : k / 2 % 4 % 2 = if i then 1 else 0 := by dsimp [k]; split_ifs <;> omega
      change decide (k / 2 % 4 % 2 = 1) = i
      rw [e2]; cases i <;> simp
  ec_surj := by
    have hq := Nat.pos_of_neZero q
    rintro ⟨h, i, b⟩
    have hh := h.isLt
    let k := 2 * (4 * h.val + if i then 1 else 0) + if b then 1 else 0
    refine ⟨⟨k, by dsimp [k]; split_ifs <;> omega⟩, ?_⟩
    have e1 : k / 2 / 4 = h.val := by dsimp [k]; split_ifs <;> omega
    have e2 : k / 2 % 4 = if i then 1 else 0 := by dsimp [k]; split_ifs <;> omega
    have e3 : k % 2 = if b then 1 else 0 := by dsimp [k]; split_ifs <;> omega
    simp only [gec, Prod.mk.injEq, Fin.ext_iff]
    refine ⟨e1, ?_, ?_⟩
    · change decide (k / 2 % 4 % 2 = 1) = i; rw [e2]; cases i <;> simp
    · change (decide (k % 2 = 1) ^^ decide (2 ≤ k / 2 % 4)) = b
      rw [e2, e3]; cases i <;> cases b <;> simp

theorem cornerAdj_of_vals {m n : Fin (8 * q)} {a b : ℕ} (hvc : gvc q m = gvc q n)
    (ha : m.val = a) (hb : (fpred n).val = b)
    (h1 : a / 2 / 4 = b / 2 / 4 := by omega) (h2 : a / 2 % 4 % 2 = b / 2 % 4 % 2 := by omega)
    (h3 : (a % 2 + (if 2 ≤ a / 2 % 4 then 1 else 0)) % 2
        = (b % 2 + (if 2 ≤ b / 2 % 4 then 1 else 0)) % 2 := by split_ifs <;> omega) :
    CornerAdj (gvc q) (gec q) m n :=
  ⟨hvc, .inr (.inl ((gec_eq_iff' q m (fpred n)).2 (by rw [ha, hb]; exact ⟨h1, h2, h3⟩)))⟩

theorem cornerAdj_even (a b : ℕ) (ha : a < 8 * q := by omega) (hb : b < 8 * q := by omega)
    (hae : a % 2 = 0 := by omega) (hbe : b % 2 = 0 := by omega) (hbp : 0 < b := by omega)
    (h1 : a / 2 / 4 = (b - 1) / 2 / 4 := by omega)
    (h2 : a / 2 % 4 % 2 = (b - 1) / 2 % 4 % 2 := by omega)
    (h3 : (a % 2 + (if 2 ≤ a / 2 % 4 then 1 else 0)) % 2
        = ((b - 1) % 2 + (if 2 ≤ (b - 1) / 2 % 4 then 1 else 0)) % 2 := by split_ifs <;> omega) :
    CornerAdj (gvc q) (gec q) ⟨a, ha⟩ ⟨b, hb⟩ :=
  cornerAdj_of_vals q (by simp [gvc, hae, hbe]) rfl (fpred_val_pos q rfl hbp) h1 h2 h3

theorem conn_within_block (h : ℕ) (hh : h < q) (t : ℕ) (ht : t < 4) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨8 * h, by omega⟩ ⟨8 * h + 2 * t, by omega⟩ := by
  have e1 := ReflTransGen.single (cornerAdj_even q (8 * h) (8 * h + 6))
  have e2 := e1.tail (cornerAdj_even q (8 * h + 6) (8 * h + 4))
  have e3 := e2.tail (cornerAdj_even q (8 * h + 4) (8 * h + 2))
  interval_cases t <;> first | exact .refl | simpa using e1 | simpa using e2 | simpa using e3

theorem conn_block_zero (h : ℕ) (hh : h < q) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨0, by have := Nat.pos_of_neZero q; omega⟩
      ⟨8 * h, by omega⟩ := by
  induction h with
  | zero => exact .refl
  | succ n ih =>
      have hn : n < q := by omega
      have h2 : ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨8 * n, by omega⟩ ⟨8 * n + 2, by omega⟩ :=
        by simpa using conn_within_block q n hn 1 (by omega)
      exact ((ih hn).trans h2).tail (cornerAdj_even q (8 * n + 2) (8 * (n + 1)))

theorem conn_even_zero (p : Fin (8 * q)) (hp : p.val % 2 = 0) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨0, by have := Nat.pos_of_neZero q; omega⟩ p := by
  have := Nat.pos_of_neZero q; have := p.isLt
  have hh : p.val / 8 < q := by omega
  have hwithin := conn_within_block q (p.val / 8) hh (p.val % 8 / 2) (by omega)
  rw [show (⟨8 * (p.val / 8) + 2 * (p.val % 8 / 2), by omega⟩ : Fin (8 * q)) = p
    from Fin.ext (by dsimp; omega)] at hwithin
  exact (conn_block_zero q (p.val / 8) hh).trans hwithin

theorem genus_cornersConnected : CornersConnected (gvc q) (gec q) := by
  have hq := Nat.pos_of_neZero q
  have mid_adj {i j : Fin (8 * q)} (hi : i.val % 2 ≠ 0) (hj : j.val % 2 ≠ 0)
      (hij : gvc q i = gvc q j) (hr : i.val / 2 % 4 < 2) (hjv : j.val = i.val + 4) :
      CornerAdj (gvc q) (gec q) i j := by
    have := i.isLt; have := j.isLt
    have h12 : i.val / 2 / 4 = j.val / 2 / 4 ∧
        (i.val / 2 % 4 % 2 = 1 ↔ j.val / 2 % 4 % 2 = 1) := by
      simpa [gvc, hi, hj, decide_eq_decide] using hij
    exact cornerAdj_of_vals q (a := i.val) (b := i.val + 3) hij rfl
      (by rw [fpred_val_pos q (a := j.val) rfl (by omega)]; omega)
  intro i j hij
  have hi8 := i.isLt; have hj8 := j.isLt
  by_cases hi : i.val % 2 = 0
  · have hj : j.val % 2 = 0 := by
      by_contra hj; simp [gvc, hi, hj] at hij
    letI : Std.Symm (CornerAdj (gvc q) (gec q)) := ⟨fun _ _ h => cornerAdj_symm h⟩
    exact (ReflTransGen.stdSymm.symm _ _ (conn_even_zero q i hi)).trans
      (conn_even_zero q j hj)
  · have hj : j.val % 2 ≠ 0 := fun hj => by simp [gvc, hi, hj] at hij
    have ⟨h1, h2⟩ : i.val / 2 / 4 = j.val / 2 / 4 ∧
        (i.val / 2 % 4 % 2 = 1 ↔ j.val / 2 % 4 % 2 = 1) := by
      simpa [gvc, hi, hj, decide_eq_decide] using hij
    have h2' : i.val / 2 % 4 % 2 = j.val / 2 % 4 % 2 := by
      by_cases ha : i.val / 2 % 4 % 2 = 1 <;> by_cases hb : j.val / 2 % 4 % 2 = 1 <;>
        simp [ha, hb] at h2 ⊢ <;> omega
    by_cases heq : i.val = j.val
    · rw [Fin.ext heq]
    rcases Nat.lt_or_ge (i.val / 2 % 4) 2 with hr | hr
    · exact .single (mid_adj hi hj hij hr (by omega))
    · exact .single (cornerAdj_symm (mid_adj hj hi hij.symm (by omega) (by omega)))

theorem genus_chain_card_le_three {s : Finset (SCell (gvc q) (gec q) (gc q))}
    (hs : s ∈ (orderComplex (SCell (gvc q) (gec q) (gc q))).faces) : s.card ≤ 3 :=
  (closedSurfacePoset_SCell (gc q) (genus_polygonData q)
    (genus_cornersConnected q)).toSurfaceRank.chain_card_le_three hs
