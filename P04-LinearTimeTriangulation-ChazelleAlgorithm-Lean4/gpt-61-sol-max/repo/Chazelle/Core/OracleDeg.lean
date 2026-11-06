module

public meta import Chazelle.Arithmetic

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
  fun hm => by have := abs_fst_lt_radius_of_mem hm; linarith

theorem not_mem_set_of_chord {y a b x : ℝ} (h : Chazelle.Chain.IsHChordIn C.dom y a b)
    (hax : a < x) (hxb : x < b) : ((x, y) : Point) ∉ C.set := fun hm =>
  (h.open_mem x hax hxb).2 (Or.inl hm)

theorem sgnOf_one {b : ℕ} (h : b = 1) : sgnOf b = 1 := by core_grind
theorem sgnOf_ne {b : ℕ} (h : b ≠ 1) : sgnOf b = -1 := by core_grind

section
variable (z : Point) (t : ℝ)
theorem rayPt_right : rayPt z 1 t = ((z.1 + t, z.2) : Point) := by
  simp_all [rayPt] 
theorem rayPt_left : rayPt z (-1) t = ((z.1 - t, z.2) : Point) := by
  ext <;> simp_all [rayPt] <;> ring


end

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
    have hj : jCOf V t = t := by simp_all [jCOf] 
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
      grind
    have hy : z.2 = ((Qof P).vtx V.hz).2 := hs.zy
    rw [hσ1]
    by_cases hp : C.radius ≤ z.1
    · -- past the box
      have hnh := noHit_past hcs (Or.inl rfl) (by simp_all) (A := C.set) (z := z)
      have hc2 : xpClass (chR m V i) ≠ 1 := by
        intro hc1
        rcases hgt with h2 | ⟨-, hz⟩
        · omega
        · have hx := abs_lt.1 (ER.good hc1)
          rcases hs.zo with e | ⟨e, hz1⟩
          · grind
          · rw [hσ1] at hz1; linarith
      exact ⟨fun hf1 => absurd hf1 (by omega), fun _ => hnh⟩
    have hnp : NotPast C V z := ⟨fun _ => by simp_all, fun h' => absurd hσ h'⟩
    have hb := (endGtZ_iff hσ hs.zo hnp ER.good).1 hgt
    have ha := not_lt.1 (fun h' => hdeg ((endGtZ_iff hσ hs.zo hnp EL.good).2 h'))
    unfold ζOf at hb ha; rw [ite_eq_left hσ] at hb ha
    set a := xv P C V (chL m V i) V.hz
    set b := xv P C V (chR m V i) V.hz
    have hza := le_max_left z.1 (-C.radius)
    have hRa := le_max_right z.1 (-C.radius)
    -- no chain point strictly between the origin and the far end
    have hfree : ∀ s, 0 < s → z.1 + s < b → rayPt z 1 s ∉ C.set := by
      grind [Chazelle.Core.OracleR.rayPt_right, Chazelle.Core.OracleR.not_mem_set_of_abs, Chazelle.Core.OracleR.not_mem_set_of_chord]
    have hpos := ER.1
    refine ⟨fun hf1 => ?_, fun hf1 => ?_⟩
    · have hc1 : xpClass (chR m V i) = 1 := by
        omega
      obtain ⟨-, he⟩ := h1 hc1
      obtain ⟨hmem, hlt, hedge⟩ := ER.2.1 hc1
      rw [hpos] at hmem hedge
      have hpt : rayPt z 1 (b - z.1) = ((b, ((Qof P).vtx V.hz).2) : Point) := by
        grind [rayPt_right]
      ram_grind
    · have hc : xpClass (chR m V i) ≠ 1 := fun hc1 => hf1 (h1 hc1).1
      have hbR : b = C.radius := by
        have hb2 : xpClass (chR m V i) = 2 := by
          rcases xpClass_cases (chR m V i) with e | e | e
          · exfalso; have := xv_c0 (P := P) (C := C) (V := V) (h := V.hz) e; linarith
          all_goals omega
        exact xv_c2 hb2
      intro s hs0
      by_cases hsb : z.1 + s < b
      · grind
      · rw [rayPt_right]
        exact not_mem_set_of_abs (by grind)
  · -- leftwards: the chord `CH[t - 1]`
    have hσ1 := sgnOf_ne hσ
    rw [ite_eq_right hσ] at hK
    have hj : jCOf V t = t - 1 := by simp_all [jCOf] 
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
      grind [chPr_iff]
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
          all_goals grind
      exact ⟨fun hf1 => absurd hf1 (by omega), fun _ => hnh⟩
    have hnp : NotPast C V z := ⟨fun h' => absurd h' hσ, fun _ => by simp_all⟩
    have ha := (endLtZ_iff hσ hs.zo hnp EL.good).1 hlt'
    have hb := not_lt.1 (fun h' => hdeg ((endLtZ_iff hσ hs.zo hnp ER.good).2 h'))
    unfold ζOf at hb ha; rw [ite_eq_right hσ] at hb ha
    set a := xv P C V (chL m V i) V.hz
    set b := xv P C V (chR m V i) V.hz
    have hza := min_le_left z.1 C.radius
    have hRa := min_le_right z.1 C.radius
    have hfree : ∀ s, 0 < s → a < z.1 - s → rayPt z (-1) s ∉ C.set := by
      grind [Chazelle.Core.OracleR.rayPt_left, Chazelle.Core.OracleR.not_mem_set_of_abs, Chazelle.Core.OracleR.not_mem_set_of_chord]
    have hpos := EL.1
    refine ⟨fun hf1 => ?_, fun hf1 => ?_⟩
    · have hc1 : xpClass (chL m V i) = 1 := by
        omega
      obtain ⟨-, he⟩ := h1 hc1
      obtain ⟨hmem, hlt, hedge⟩ := EL.2.1 hc1
      rw [hpos] at hmem hedge
      have hpt : rayPt z (-1) (z.1 - a) = ((a, ((Qof P).vtx V.hz).2) : Point) := by
        grind [rayPt_left]
      ram_grind
    · have hc : xpClass (chL m V i) ≠ 1 := fun hc1 => hf1 (h1 hc1).1
      have haR : a = -C.radius := by
        have hb0 : xpClass (chL m V i) = 0 := by
          rcases xpClass_cases (chL m V i) with e | e | e
          · exact e
          · omega
          · exfalso; have := xv_c2 (P := P) (C := C) (V := V) (h := V.hz) e; linarith
        exact xv_c0 hb0
      intro s hs0
      by_cases hsa : a < z.1 - s
      · grind
      · rw [rayPt_left]
        exact not_mem_set_of_abs (by grind)

end

end OracleR

end Chazelle.Core
