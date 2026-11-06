module

public import Chazelle.Golf

public import Chazelle.Core.OracleChordGeo

/-!
# Lemma 3.6 (WP-H), part 17: the chord search predicate is monotone

The chord table is sorted by height vertex, then by the class and the abscissa of the left end
(`ChLe`).  Two distinct chords of the domain at the same height do not overlap, so along the
table the right ends grow with the left ends; hence the search predicate `chPr` (the chord is
below the ray's height, or at it and not ahead of the origin) holds on a prefix of the table
(`chPr_mono`), which is what the binary search needs.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
open Chazelle.Visibility (rayPt hseg)

@[expose] public section

variable {P : Polygon} {C : Chain} {V : QV}

/-- **The chord records in memory.** -/
structure ChordRecOK (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (N : NF) : Prop where
  hT : TopOK P C V
  hN : IsNF (chainModel C) (Qof P) N
  nf : NFAt m V.NB N
  CB : m (V.NB + 3) = V.CB
  K : V.K = N.chords.length
  lt : ∀ q, q < V.K → chAt m V q < V.K
  inj : ∀ q q', q < V.K → q' < V.K → chAt m V q = chAt m V q' → q = q'
  sorted : ∀ q q', q ≤ q' → q' < V.K → ChLe P C V m (chAt m V q) (chAt m V q')

variable {m : ℕ → ℕ} {N : NF}

theorem ChordRecOK.recs (h : ChordRecOK P C V m N) {i : ℕ} (hi : i < V.K) :
    chH m V i = (N.chord i).h ∧ chL m V i = (N.chord i).lp ∧ chR m V i = (N.chord i).rp := by
  have := h.nf.2.2.2.2.2.1 i (by rw [← h.K]; exact hi)
  rw [h.CB] at this
  exact ⟨this.1, this.2.1, this.2.2.1⟩

/-- The facts of the chord record `i` in memory. -/
theorem ChordRecOK.facts (h : ChordRecOK P C V m N) {i : ℕ} (hi : i < V.K) :
    chH m V i < P.n ∧ ((Qof P).vtx (chH m V i)).2 ≤ C.top.2 ∧
    Chazelle.Chain.IsHChordIn C.dom ((Qof P).vtx (chH m V i)).2
      (xv P C V (chL m V i) (chH m V i)) (xv P C V (chR m V i) (chH m V i)) ∧
    (N.chord i).toSet (chainModel C) (Qof P) = hseg ((Qof P).vtx (chH m V i)).2
      (xv P C V (chL m V i) (chH m V i)) (xv P C V (chR m V i) (chH m V i)) ∧
    EndFacts P C V (chL m V i) (chH m V i) ∧ EndFacts P C V (chR m V i) (chH m V i) := by
  obtain ⟨e1, e2, e3⟩ := h.recs hi
  Ξ e1, e2, e3
  exact chord_facts h.hT h.hN (by rw [← h.K]; exact hi)

theorem xv_c0 {w h : ℕ} (hc : xpClass w = 0) : xv P C V w h = -C.radius := by
  unfold xv; rw [ite_eq_left hc]
theorem xv_c1 {w h : ℕ} (hc : xpClass w = 1) : xv P C V w h = xpX P C V w h := by
  unfold xv; rw [ite_eq_right (⋄), ite_eq_right (by omega)]
theorem xv_c2 {w h : ℕ} (hc : xpClass w = 2) : xv P C V w h = C.radius := by
  unfold xv; rw [ite_eq_right (⋄), ite_eq_left hc]

theorem xv_ge (P : Polygon) (C : Chain) (V : QV) {w h : ℕ} (he : EndGood P C V w h) :
    -C.radius ≤ xv P C V w h := by
  have hR := C.radius_pos
  unfold xv
  rcases xpClass_cases w with h0 | h1 | h2
  · Ξ ite_eq_left h0
  · rw [ite_eq_right (⋄), ite_eq_right (by omega)]; exact (abs_lt.1 (he h1)).1.le
  · rw [ite_eq_right (⋄), ite_eq_left h2]; linarith

theorem xv_le (P : Polygon) (C : Chain) (V : QV) {w h : ℕ} (he : EndGood P C V w h) :
    xv P C V w h ≤ C.radius := by
  have hR := C.radius_pos
  unfold xv
  rcases xpClass_cases w with h0 | h1 | h2
  · rw [ite_eq_left h0]; linarith
  · rw [ite_eq_right (⋄), ite_eq_right (by omega)]; exact (abs_lt.1 (he h1)).2.le
  · rw [ite_eq_right (⋄), ite_eq_left h2]

/-- The order of the table on the left ends is the order of their abscissae. -/
theorem chLe_xv {a b : ℕ} (ha : EndGood P C V (chL m V a) (chH m V a))
    (hb : EndGood P C V (chL m V b) (chH m V b)) (hle : ChLe P C V m a b)
    (hh : chH m V a = chH m V b) :
    xv P C V (chL m V a) (chH m V a) ≤ xv P C V (chL m V b) (chH m V b) := by
  rcases hle with hlt | ⟨-, hcl | ⟨hce, hx⟩⟩
  · omega
  · rcases xpClass_cases (chL m V a) with h0 | h1 | h2
    · rw [xv_c0 h0]; exact xv_ge P C V hb
    · have hb2 : xpClass (chL m V b) = 2 := by have := xpClass_le (chL m V b); omega
      rw [xv_c2 hb2]; exact xv_le P C V ha
    · have := xpClass_le (chL m V b); omega
  · rcases xpClass_cases (chL m V a) with h0 | h1 | h2
    · rw [xv_c0 h0, xv_c0 (show xpClass (chL m V b) = 0 by omega)]
    · rw [xv_c1 h1, xv_c1 (show xpClass (chL m V b) = 1 by omega)]; exact hx h1
    · rw [xv_c2 h2, xv_c2 (show xpClass (chL m V b) = 2 by omega)]

/-- **Two chords at one height do not overlap**: with the left end of `a` not after the left end
of `b`, the right end of `a` is not after the left end of `b`. -/
theorem chord_disjoint (h : ChordRecOK P C V m N) {a b : ℕ} (ha : a < V.K) (hb : b < V.K)
    (hab : a ≠ b) (hh : chH m V a = chH m V b)
    (hl : xv P C V (chL m V a) (chH m V a) ≤ xv P C V (chL m V b) (chH m V b)) :
    xv P C V (chR m V a) (chH m V a) ≤ xv P C V (chL m V b) (chH m V b) := by
  obtain ⟨-, -, Ha, Sa, -, -⟩ := h.facts ha
  obtain ⟨-, -, Hb, Sb, -, -⟩ := h.facts hb
  rw [← hh] at Hb Sb hl ⊢
  set y := ((Qof P).vtx (chH m V a)).2
  set la := xv P C V (chL m V a) (chH m V a)
  set ra := xv P C V (chR m V a) (chH m V a)
  set lb := xv P C V (chL m V b) (chH m V a)
  set rb := xv P C V (chR m V b) (chH m V a)
  by_contra hc
  push Not at hc
  have hab' := Ha.lt
  have hbb := Hb.lt
  -- a point inside both
  set x := (lb + min ra rb) / 2 with hx
  have hmin : lb < min ra rb := lt_min hc hbb
  have hx1 : lb < x := by rw [hx]; linarith
  have hx2 : x < min ra rb := by rw [hx]; linarith
  have hxa : ((x, y) : Point) ∈ hseg y la ra :=
    ⟨rfl, by show la ≤ x; linarith, by show x ≤ ra; linarith [min_le_left ra rb]⟩
  have hxb : ((x, y) : Point) ∈ hseg y lb rb :=
    ⟨rfl, by show lb ≤ x; linarith, by show x ≤ rb; linarith [min_le_right ra rb]⟩
  rcases Chazelle.Chain.hchordIn_inter Ha Hb hxa hxb with ⟨-, e1, e2⟩ | ⟨-, hp⟩
  · -- the same chord
    have hs : (N.chord a).toSet (chainModel C) (Qof P) = (N.chord b).toSet (chainModel C) (Qof P) := by
      Ξ Sa, Sb, e1, e2
    obtain ⟨-, hinj, -⟩ := h.hN
    exact hab (hinj a b (show a < N.chords.length by rw [← h.K]; exact ha)
      (show b < N.chords.length by rw [← h.K]; exact hb) hs)
  · rcases hp with e | e
    · have := congrArg Prod.fst e; simp only at this; linarith
    · have := congrArg Prod.fst e; simp only at this; linarith [min_le_right ra rb]

/-- `EndGtZ` is upward closed along good ends. -/
theorem endGtZ_mono {w h w' h' : ℕ} (he : EndGood P C V w h) (he' : EndGood P C V w' h')
    (hle : xv P C V w h ≤ xv P C V w' h') (hg : EndGtZ P C V w h) : EndGtZ P C V w' h' := by
  have hR := C.radius_pos
  have c1 : ∀ {u k : ℕ}, xpClass u = 1 → xv P C V u k = xpX P C V u k := fun hc => by
    unfold xv; rw [ite_eq_right (⋄), ite_eq_right (by omega)]
  have c2 : ∀ {u k : ℕ}, xpClass u = 2 → xv P C V u k = C.radius := fun hc => by
    unfold xv; rw [ite_eq_right (⋄), ite_eq_left hc]
  have c0 : ∀ {u k : ℕ}, xpClass u = 0 → xv P C V u k = -C.radius := fun hc => by
    unfold xv; rw [ite_eq_left hc]
  unfold EndGtZ at hg ⊢
  rcases xpClass_cases w' with h0 | h1 | h2
  · exfalso
    rw [c0 h0] at hle
    rcases hg with hg | ⟨hg1, -⟩
    · rw [c2 hg] at hle; linarith
    · rw [c1 hg1] at hle; linarith [(abs_lt.1 (he hg1)).1]
  · right; refine ⟨h1, ?_⟩
    rcases hg with hg | ⟨hg1, hz⟩
    · exfalso; rw [c2 hg, c1 h1] at hle; linarith [(abs_lt.1 (he' h1)).2]
    · rw [c1 hg1, c1 h1] at hle
      revert hz; cases V.zo with
      | none => exact id
      | some z => intro hz; show z.1 < _; linarith
  · exact Or.inl h2

/-- `EndLtZ` is downward closed along good ends. -/
theorem endLtZ_mono {w h w' h' : ℕ} (he : EndGood P C V w h) (he' : EndGood P C V w' h')
    (hle : xv P C V w h ≤ xv P C V w' h') (hg : EndLtZ P C V w' h') : EndLtZ P C V w h := by
  have hR := C.radius_pos
  have c1 : ∀ {u k : ℕ}, xpClass u = 1 → xv P C V u k = xpX P C V u k := fun hc => by
    unfold xv; rw [ite_eq_right (⋄), ite_eq_right (by omega)]
  have c2 : ∀ {u k : ℕ}, xpClass u = 2 → xv P C V u k = C.radius := fun hc => by
    unfold xv; rw [ite_eq_right (⋄), ite_eq_left hc]
  have c0 : ∀ {u k : ℕ}, xpClass u = 0 → xv P C V u k = -C.radius := fun hc => by
    unfold xv; rw [ite_eq_left hc]
  unfold EndLtZ at hg ⊢
  rcases xpClass_cases w with h0 | h1 | h2
  · exact Or.inl h0
  · right; refine ⟨h1, ?_⟩
    rcases hg with hg | ⟨hg1, hz⟩
    · exfalso; rw [c0 hg, c1 h1] at hle; linarith [(abs_lt.1 (he h1)).1]
    · rw [c1 hg1, c1 h1] at hle
      revert hz; cases V.zo with
      | none => exact id
      | some z => intro hz; show _ < z.1; linarith
  · exfalso
    rw [c2 h2] at hle
    rcases hg with hg | ⟨hg1, -⟩
    · rw [c0 hg] at hle; linarith
    · rw [c1 hg1] at hle; linarith [(abs_lt.1 (he' hg1)).2]

/-- **The search predicate holds on a prefix of the table.** -/
theorem chPr_iff (x : ℕ) : chPr P C V m x = true ↔ (x < V.K ∧ (chH m V x < V.hz ∨
    (chH m V x = V.hz ∧ ((V.σb = 1 → ¬ EndGtZ P C V (chR m V x) V.hz) ∧
      (V.σb ≠ 1 → EndLtZ P C V (chL m V x) V.hz))))) := by
  classical
  unfold chPr
  Ξ decide_eq_true_iff
  by_cases hσ : V.σb = 1
  · simp only [hσ, ite_true]; tauto
  · Ξ ite_eq_right hσ
    constructor
    · rintro ⟨h1, h2 | ⟨h3, h4⟩⟩
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr ⟨h3, fun h => absurd h hσ, fun _ => h4⟩⟩
    · rintro ⟨h1, h2 | ⟨h3, -, h5⟩⟩
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr ⟨h3, h5 hσ⟩⟩

theorem chPr_mono (h : ChordRecOK P C V m N) :
    ∀ i j, i ≤ j → j < V.K → chPr P C V m (chAt m V j) = true →
      chPr P C V m (chAt m V i) = true := by
  intro i j hij hj hpj
  have hi : i < V.K := ⋄
  have hle := h.sorted i j hij hj
  obtain ⟨a, hadef⟩ : ∃ a, chAt m V i = a := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, chAt m V j = b := ⟨_, rfl⟩
  have ha : a < V.K := hadef ▸ h.lt i hi
  have hb : b < V.K := hbdef ▸ h.lt j hj
  rw [hadef, hbdef] at hle
  rw [hbdef] at hpj
  Ξ hadef
  obtain ⟨-, -, -, -, ELa, ERa⟩ := h.facts ha
  obtain ⟨-, -, Hb, -, ELb, ERb⟩ := h.facts hb
  rw [chPr_iff] at hpj ⊢
  refine ⟨ha, ?_⟩
  obtain ⟨-, hpj⟩ := hpj
  have hle' := hle
  rcases hle with hlt | ⟨hh, -⟩
  · left; rcases hpj with h1 | ⟨h1, -⟩ <;> omega
  rcases hpj with h1 | ⟨h1, h2, h3⟩
  · left; omega
  right
  have hx := chLe_xv ELa.good ELb.good hle' hh
  have hA' : chH m V a = V.hz := ⋄
  rw [hA'] at ELa ERa hx
  rw [h1] at ELb ERb hx Hb
  refine ⟨hA', ?_, ?_⟩
  · intro hσ hg
    apply h2 hσ
    by_cases hab : a = b
    · rw [← hab]; exact hg
    have hd := chord_disjoint h ha hb hab hh (by rw [hA', h1]; exact hx)
    rw [hA', h1] at hd
    exact endGtZ_mono ERa.good ERb.good (by linarith [Hb.lt]) hg
  · intro hσ
    exact endLtZ_mono ELa.good ELb.good hx (h3 hσ)

end

end OracleR

end Chazelle.Core
