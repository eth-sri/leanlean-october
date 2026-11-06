module

public import Chazelle.Core.OracleShift

/-!
# Lemma 3.6 (WP-H), part 20: the answer of a degenerate start

When the origin of the ray lies on the chord at the ray's height next to it (the near end not
ahead), the ray runs along the chord and first meets the chain at the far end of the chord if
that end is on the chain (class `1`), and misses the chain otherwise (`deg_answer`).  Origins
outside the box, before it or past it, are covered: before the box the ray meets nothing, and it
enters the box on the chord.
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)

@[expose] public section

/-- **The answer of the query** in the output registers `flag`, `edge`. -/
def Answer (P : Polygon) (C : Chain) (z : Point) (σ : ℝ) (flag edge : ℕ) : Prop :=
  (flag = 1 → ∃ t, FirstHit C.set z σ t ∧ edge < P.n ∧ rayPt z σ t ∈ (Qof P).edge edge) ∧
    (flag ≠ 1 → NoHit C.set z σ)

variable {P : Polygon} {C : Chain} {V : QV}

theorem not_mem_set_of_abs {x y : ℝ} (hx : C.radius ≤ |x|) : ((x, y) : Point) ∉ C.set :=
  fun hm => by have := abs_fst_lt_radius_of_mem hm; simp only at this; linarith

theorem not_mem_set_of_chord {y a b x : ℝ} (h : Chazelle.Chain.IsHChordIn C.dom y a b)
    (hax : a < x) (hxb : x < b) : ((x, y) : Point) ∉ C.set := fun hm =>
  (h.open_mem x hax hxb).2 (Or.inl hm)

theorem sgnOf_one {b : ℕ} (h : b = 1) : sgnOf b = 1 := by unfold sgnOf; rw [ite_eq_left h]
theorem sgnOf_ne {b : ℕ} (h : b ≠ 1) : sgnOf b = -1 := by unfold sgnOf; rw [ite_eq_right h]

theorem rayPt_right (z : Point) (t : ℝ) : rayPt z 1 t = ((z.1 + t, z.2) : Point) := by
  simp only [rayPt]; ext <;> simp
theorem rayPt_left (z : Point) (t : ℝ) : rayPt z (-1) t = ((z.1 - t, z.2) : Point) := by
  simp only [rayPt]; ext <;> simp; ring

/-- **The answer of a degenerate start.** -/
theorem deg_answer {m : ℕ → ℕ} {N : NF} (h : ChordRecOK P C V m N) {z : Point}
    (hs : SemOK P C V z) {t : ℕ} (hpart : PartC P C V m t) (hf : FoundC V m t)
    (hdeg : DegC P C V m t) {flag edge : ℕ}
    (h1 : xpClass (farC V m t) = 1 → flag = 1 ∧ edge = symIdx (xpSym C V P.n (farC V m t) V.hz))
    (h0 : xpClass (farC V m t) ≠ 1 → flag = 0) :
    Answer P C z (sgnOf V.σb) flag edge := by
  have hR := C.radius_pos
  obtain ⟨ht, hpre, hpost⟩ := hpart
  obtain ⟨hK, hH⟩ := hf
  have hcs : C.set ⊆ Chain.box C.radius := C.set_subset_box
  by_cases hσ : V.σb = 1
  · -- rightwards: the chord `CH[t]`
    have hσ1 := sgnOf_one hσ
    rw [ite_eq_left hσ] at hK
    have hj : jCOf V t = t := by unfold jCOf; rw [ite_eq_left hσ]
    unfold DegC nearC at hdeg
    unfold farC at h1 h0
    rw [hj, ite_eq_left hσ] at hdeg h1 h0
    rw [ite_eq_left hσ] at hdeg
    rw [hj] at hH
    set i := chAt m V t
    have hi := h.lt t hK
    obtain ⟨-, -, hC, -, EL, ER⟩ := h.facts hi
    rw [hH] at hC EL ER
    have hgt : EndGtZ P C V (chR m V i) V.hz := by
      have := hpost hK
      rw [← Bool.not_eq_true, chPr_iff] at this
      by_contra hc
      exact this ⟨hi, Or.inr ⟨hH, fun _ => hc, fun h' => absurd hσ h'⟩⟩
    have hy : z.2 = ((Qof P).vtx V.hz).2 := hs.zy
    rw [hσ1]
    by_cases hp : C.radius ≤ z.1
    · -- past the box
      have hnh := noHit_past hcs (Or.inl rfl) (by rw [one_mul]; exact hp) (A := C.set) (z := z)
      have hc2 : xpClass (chR m V i) ≠ 1 := by
        intro hc1
        rcases hgt with h2 | ⟨-, hz⟩
        · omega
        · have hx := abs_lt.1 (ER.good hc1)
          rcases hs.zo with e | ⟨e, hz1⟩
          · rw [e] at hz; simp only at hz; linarith
          · rw [hσ1] at hz1; linarith
      exact ⟨fun hf1 => absurd hf1 (by rw [h0 hc2]; omega), fun _ => hnh⟩
    have hnp : NotPast C V z := ⟨fun _ => by push Not at hp; exact hp, fun h' => absurd hσ h'⟩
    have hb := (endGtZ_iff hσ hs.zo hnp ER.good).1 hgt
    have ha := not_lt.1 (fun h' => hdeg ((endGtZ_iff hσ hs.zo hnp EL.good).2 h'))
    unfold ζOf at hb ha; rw [ite_eq_left hσ] at hb ha
    set a := xv P C V (chL m V i) V.hz
    set b := xv P C V (chR m V i) V.hz
    have hza := le_max_left z.1 (-C.radius)
    have hRa := le_max_right z.1 (-C.radius)
    -- no chain point strictly between the origin and the far end
    have hfree : ∀ s, 0 < s → z.1 + s < b → rayPt z 1 s ∉ C.set := by
      intro s hs0 hsb
      rw [rayPt_right, hy]
      by_cases hx : z.1 + s ≤ -C.radius
      · exact not_mem_set_of_abs (by rw [abs_of_neg (by linarith)]; linarith)
      · push Not at hx
        exact not_mem_set_of_chord hC (by
          have : max z.1 (-C.radius) < z.1 + s := max_lt (by linarith) hx
          linarith) hsb
    have hpos := ER.1
    refine ⟨fun hf1 => ?_, fun hf1 => ?_⟩
    · have hc1 : xpClass (chR m V i) = 1 := by
        by_contra hc; have := h0 hc; omega
      obtain ⟨-, he⟩ := h1 hc1
      obtain ⟨hmem, hlt, hedge⟩ := ER.2.1 hc1
      rw [hpos] at hmem hedge
      have hpt : rayPt z 1 (b - z.1) = ((b, ((Qof P).vtx V.hz).2) : Point) := by
        rw [rayPt_right, hy]; ring_nf
      refine ⟨b - z.1, ⟨by linarith, by rw [hpt]; exact hmem, fun s hs0 hsl => hfree s hs0 (by
        linarith)⟩, by rw [he]; exact hlt, by rw [hpt, he]; exact hedge⟩
    · have hc : xpClass (chR m V i) ≠ 1 := fun hc1 => hf1 (h1 hc1).1
      have hbR : b = C.radius := by
        have hb2 : xpClass (chR m V i) = 2 := by
          rcases xpClass_cases (chR m V i) with e | e | e
          · exfalso; have := xv_c0 (P := P) (C := C) (V := V) (h := V.hz) e; linarith
          · exact absurd e hc
          · exact e
        exact xv_c2 hb2
      intro s hs0
      by_cases hsb : z.1 + s < b
      · exact hfree s hs0 hsb
      · rw [rayPt_right]
        exact not_mem_set_of_abs (by rw [abs_of_pos (by linarith)]; linarith)
  · -- leftwards: the chord `CH[t - 1]`
    have hσ1 := sgnOf_ne hσ
    rw [ite_eq_right hσ] at hK
    have hj : jCOf V t = t - 1 := by unfold jCOf; rw [ite_eq_right hσ]
    unfold DegC nearC at hdeg
    unfold farC at h1 h0
    rw [hj, ite_eq_right hσ] at hdeg h1 h0
    rw [ite_eq_right hσ] at hdeg
    rw [hj] at hH
    set i := chAt m V (t - 1)
    have hi := h.lt (t - 1) (by omega)
    obtain ⟨-, -, hC, -, EL, ER⟩ := h.facts hi
    rw [hH] at hC EL ER
    have hlt' : EndLtZ P C V (chL m V i) V.hz := by
      have := hpre (t - 1) (by omega)
      rw [chPr_iff] at this
      rcases this.2 with h' | ⟨-, -, h'⟩
      · exact absurd hH (ne_of_lt h')
      · exact h' hσ
    have hy : z.2 = ((Qof P).vtx V.hz).2 := hs.zy
    rw [hσ1]
    by_cases hp : z.1 ≤ -C.radius
    · have hnh := noHit_past hcs (Or.inr rfl) (by linarith) (A := C.set) (z := z)
      have hc2 : xpClass (chL m V i) ≠ 1 := by
        intro hc1
        rcases hlt' with h2 | ⟨-, hz⟩
        · omega
        · have hx := abs_lt.1 (EL.good hc1)
          rcases hs.zo with e | ⟨e, hz1⟩
          · rw [e] at hz; simp only at hz; linarith
          · rw [hσ1] at hz1; linarith
      exact ⟨fun hf1 => absurd hf1 (by rw [h0 hc2]; omega), fun _ => hnh⟩
    have hnp : NotPast C V z := ⟨fun h' => absurd h' hσ, fun _ => by push Not at hp; exact hp⟩
    have ha := (endLtZ_iff hσ hs.zo hnp EL.good).1 hlt'
    have hb := not_lt.1 (fun h' => hdeg ((endLtZ_iff hσ hs.zo hnp ER.good).2 h'))
    unfold ζOf at hb ha; rw [ite_eq_right hσ] at hb ha
    set a := xv P C V (chL m V i) V.hz
    set b := xv P C V (chR m V i) V.hz
    have hza := min_le_left z.1 C.radius
    have hRa := min_le_right z.1 C.radius
    have hfree : ∀ s, 0 < s → a < z.1 - s → rayPt z (-1) s ∉ C.set := by
      intro s hs0 hsa
      rw [rayPt_left, hy]
      by_cases hx : C.radius ≤ z.1 - s
      · exact not_mem_set_of_abs (by rw [abs_of_pos (by linarith)]; linarith)
      · push Not at hx
        exact not_mem_set_of_chord hC hsa (by
          have : z.1 - s < min z.1 C.radius := lt_min (by linarith) hx
          linarith)
    have hpos := EL.1
    refine ⟨fun hf1 => ?_, fun hf1 => ?_⟩
    · have hc1 : xpClass (chL m V i) = 1 := by
        by_contra hc; have := h0 hc; omega
      obtain ⟨-, he⟩ := h1 hc1
      obtain ⟨hmem, hlt, hedge⟩ := EL.2.1 hc1
      rw [hpos] at hmem hedge
      have hpt : rayPt z (-1) (z.1 - a) = ((a, ((Qof P).vtx V.hz).2) : Point) := by
        rw [rayPt_left, hy]; ring_nf
      refine ⟨z.1 - a, ⟨by linarith, by rw [hpt]; exact hmem, fun s hs0 hsl => hfree s hs0 (by
        linarith)⟩, by rw [he]; exact hlt, by rw [hpt, he]; exact hedge⟩
    · have hc : xpClass (chL m V i) ≠ 1 := fun hc1 => hf1 (h1 hc1).1
      have haR : a = -C.radius := by
        have hb0 : xpClass (chL m V i) = 0 := by
          rcases xpClass_cases (chL m V i) with e | e | e
          · exact e
          · exact absurd e hc
          · exfalso; have := xv_c2 (P := P) (C := C) (V := V) (h := V.hz) e; linarith
        exact xv_c0 hb0
      intro s hs0
      by_cases hsa : a < z.1 - s
      · exact hfree s hs0 hsa
      · rw [rayPt_left]
        exact not_mem_set_of_abs (by rw [abs_of_neg (by linarith)]; linarith)

end

end OracleR

end Chazelle.Core
