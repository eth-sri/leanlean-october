module

public import Chazelle.Core.OracleRamScan

/-!
# Lemma 3.6 (WP-H), RAM part 4: the scan of one arc

`arcScan` scans the arc record `j` (register `120080`) of the normal form: it reads the edges
`se`, `ee` of the ends of the arc (words `AB + 5 j + 1`, `AB + 5 j + 3`) and its spine position
`p` (word `POS + j`), computes the number `len + 1` of walk edges to scan
(`len = (p + 1 < A ? ee - se : ee + nW - se) + 2`, `nW = 2 m + 7`) and scans the walk edges
`(se + nW - 1 + k) mod nW`, `k ≤ len`, with `wstep`.

Registers written: those of `wstep` and `120070`, `120081 … 120088`.  Main result:
`arcScan_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- Read the arc record and the spine position. -/
def arcHead : Stmt := block [.addN 120086 120080 120080, .addN 120086 120086 120086,
  .addN 120086 120086 120080, .addN 120086 120086 120044, .addN 120087 120086 120011,
  .loadN 120081 120087, .addN 120087 120087 120048, .loadN 120082 120087,
  .addN 120087 120031 120080, .loadN 120083 120087, .addN 120087 120083 120011]

/-- The number of scanned walk edges, minus three. -/
def arcLen : Stmt :=
  .ifLtN 120087 120030 (.instr (.subN 120084 120082 120081))
    (block [.addN 120084 120082 120020, .subN 120084 120084 120081])

/-- The first walk edge and the loop bound. -/
def arcInit : Stmt :=
  .seq (block [.addN 120084 120084 120048, .addN 120070 120081 120020, .subN 120070 120070 120011])
    (.seq (modSub 120070 120020) (block [.constN 120085 0, .addN 120088 120084 120011]))

/-- One walk edge, then the next. -/
def arcBody : Stmt :=
  .seq wstep (.seq (block [.addN 120085 120085 120011, .addN 120070 120070 120011])
    (.ifLtN 120070 120020 .skip (.instr (.constN 120070 0))))

/-- **The scan of arc record `j`.** -/
def arcScan : Stmt := .seq arcHead (.seq arcLen (.seq arcInit (.whileLtN 120085 120088 arcBody)))

/-- The registers written by `arcScan`. -/
def BA (r : ℕ) : Bool := BW r || decide (r = 120070) || decide (120081 ≤ r ∧ r ≤ 120088)

theorem BA_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BA r = false := by
  simp only [BA, BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- The walk edges scanned for an arc starting on edge `se`. -/
def scanW (nW se k : ℕ) : ℕ := (se + nW - 1 + k) % nW

/-- The points scanned before step `t`. -/
def scanned (C : Chain) (nW se t : ℕ) : Set Point := {x | ∃ k, k < t ∧ x ∈ wseg C (scanW nW se k)}

theorem scanned_succ (C : Chain) (nW se t : ℕ) :
    scanned C nW se (t + 1) = scanned C nW se t ∪ wseg C (scanW nW se t) := by
  ext x
  simp only [scanned, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨k, hk, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
    · exact Or.inl ⟨k, h, hx⟩
    · exact Or.inr hx
  · rintro (⟨k, hk, hx⟩ | hx)
    · exact ⟨k, by omega, hx⟩
    · exact ⟨t, by omega, hx⟩

/-- **The invariant of the loop of `arcScan`.** -/
structure AInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config) (S : Set Point)
    (se len : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  t_le : c.nreg 120085 ≤ len + 1
  lim : c.nreg 120088 = len + 1
  w : c.nreg 120070 = scanW (2 * V.m + 7) se (c.nreg 120085)
  hit : Sweep.FirstHitOpt (S ∪ scanned C (2 * V.m + 7) se (c.nreg 120085)) z (sgnOf V.σb)
    (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))
  fr : FrameB BA c₀ c

theorem arcBody_inv {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} {z : Point} (hs : SemOK P C V z) {c₀ : Config} {S : Set Point} {se len : ℕ}
    (_hse : se < 2 * V.m + 7) {c : Config} (h : AInv P W C V z c₀ S se len c)
    (ht : c.nreg 120085 < c.nreg 120088) :
    ∃ c' k, Exec P W arcBody c c' k ∧ AInv P W C V z c₀ S se len c' ∧ k ≤ 1130 ∧
      len + 1 - c'.nreg 120085 < len + 1 - c.nreg 120085 := by
  have hv := hs.hv
  have hmn : C.m < P.n := by
    have := C.m_lt; rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] at this; exact this
  set t := c.nreg 120085 with ht_def
  have htl : t < len + 1 := by rw [h.lim] at ht; exact ht
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hb₁, v₁⟩ := wstep_exec (P := P) hG (by omega) hs.hD hv c h.wb h.q h.b
  have R₁ : ∀ r, BW r = false → c₁.nreg r = c.nreg r := f₁.1
  have x85 : c₁.nreg 120085 = t := R₁ _ (by decide)
  have x70 : c₁.nreg 120070 = scanW (2 * V.m + 7) se t := (R₁ _ (by decide)).trans h.w
  have hq₁ : QConst P V c₁ := h.q.frame f₁ BW_const
  have hwn : scanW (2 * V.m + 7) se t < 2 * V.m + 7 := Nat.mod_lt _ (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.addN 120085 120085 120011, .addN 120070 120070 120011]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
      (c₂.nreg 120085 = t + 1 ∧ c₂.nreg 120070 = scanW (2 * V.m + 7) se t + 1 ∧
        (∀ r, r ≠ 120085 → r ≠ 120070 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output) := by
    have w₁ := e₁.wb_right
    have hb1 : t + 1 ≤ W := by have := h.wb.1 120088; rw [h.lim] at this; omega
    have hb2 : scanW (2 * V.m + 7) se t + 1 ≤ W := by
      have := h.wb.1 120020; rw [h.q.nW] at this; omega
    exec_block
    · rw [x85, hq₁.one]; exact hb1
    · config_simp; rw [x70, hq₁.one]; exact hb2
    · refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [x85, hq₁.one]
      · config_simp; rw [x70, hq₁.one]
      · config_simp; upd_solve
  obtain ⟨v85, v70, r₂, m₂, rr₂, rm₂, o₂⟩ := v₂
  have hq₂ : QConst P V c₂ := hq₁.congr fun r h1 h2 => r₂ r (by omega) (by omega)
  -- wrap around
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃, m₃, rr₃, rm₃, o₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 120070 120020 .skip (.instr (.constN 120070 0))) c₂ c₃ k₃ ∧ k₃ ≤ 3 ∧
      c₃.nreg 120070 = scanW (2 * V.m + 7) se (t + 1) ∧
      (∀ r, r ≠ 120070 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have hsucc : scanW (2 * V.m + 7) se (t + 1) =
        (scanW (2 * V.m + 7) se t + 1) % (2 * V.m + 7) := by
      unfold scanW
      rw [show se + (2 * V.m + 7) - 1 + (t + 1) = (se + (2 * V.m + 7) - 1 + t) + 1 by omega,
        Nat.add_mod (se + (2 * V.m + 7) - 1 + t) 1, Nat.mod_eq_of_lt (show 1 < 2 * V.m + 7 by omega)]
    by_cases hlt : scanW (2 * V.m + 7) se t + 1 < 2 * V.m + 7
    · refine ⟨c₂, _, .ifLtN_true (by rw [v70, hq₂.nW]; exact hlt) (.skip e₂.wb_right), by omega,
        ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [v70, hsucc, Nat.mod_eq_of_lt hlt]
    · refine ⟨_, _, .ifLtN_false (by rw [v70, hq₂.nW]; exact hlt)
        (Exec.constN e₂.wb_right 120070 0 (by omega)), by omega, ?_, fun r hr => ?_, rfl, rfl,
        rfl, rfl⟩
      · config_simp
        rw [hsucc, show scanW (2 * V.m + 7) se t + 1 = 2 * V.m + 7 by omega, Nat.mod_self]
      · config_simp; upd_solve
  have R₂₃ : ∀ r, r ≠ 120085 → r ≠ 120070 → c₃.nreg r = c₁.nreg r := fun r h1 h2 =>
    (r₃ r h2).trans (r₂ r h1 h2)
  have fb₂₃ : FrameB BA c₁ c₃ := by
    refine ⟨fun r hr => R₂₃ r ?_ ?_, fun r _ => by rw [rr₃, rr₂], by rw [m₃, m₂], by rw [rm₃, rm₂],
      by rw [o₃, o₂]⟩
    · intro h; subst h; simp [BA] at hr
    · intro h; subst h; simp [BA] at hr
  have fb₁ : FrameB BA c c₁ := by
    refine ⟨fun r hr => f₁.1 r ?_, fun r hr => f₁.2.1 r ?_, f₁.2.2.1, f₁.2.2.2.1, f₁.2.2.2.2⟩ <;>
      · simp only [BA, Bool.or_eq_false_iff] at hr; exact hr.1.1
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, hq₂.congr fun r h1 h2 => r₃ r (by omega),
    ?_, ?_, ?_, ?_, ?_, h.fr.trans (fb₁.trans fb₂₃)⟩, by omega, ?_⟩
  · unfold BestOK
    rw [R₂₃ 120050 (by decide) (by decide), R₂₃ 120051 (by decide) (by decide),
      R₂₃ 120052 (by decide) (by decide)]
    exact hb₁
  · rw [r₃ _ (by decide), v85]; omega
  · rw [R₂₃ _ (by decide) (by decide), R₁ _ (by decide)]; exact h.lim
  · rw [v₃, r₃ _ (by decide), v85]
  · have hbo : bestOf c₃ = bestOf c₁ := by
      unfold bestOf
      rw [R₂₃ 120050 (by decide) (by decide), R₂₃ 120052 (by decide) (by decide)]
    rw [hbo, v₁, r₃ _ (by decide), v85, scanned_succ, ← Set.union_assoc, h.w]
    exact wupd_step hs h.hit _
  · rw [r₃ _ (by decide), v85]; omega

/-- The number of scanned walk edges of an arc, minus one, as the program computes it. -/
def lenOf (A nW se ee p : ℕ) : ℕ := (if p + 1 < A then ee - se else ee + nW - se) + 2

/-- **The scan of arc record `j`.** -/
theorem arcScan_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) {se ee p : ℕ}
    (hse : c.nmem (V.AB + 5 * c.nreg 120080 + 1) = se)
    (hee : c.nmem (V.AB + 5 * c.nreg 120080 + 3) = ee)
    (hp : c.nmem (V.POS + c.nreg 120080) = p) (hsen : se < 2 * V.m + 7)
    (heen : ee < 2 * V.m + 7) (hpA : p < V.A) (haddr : V.AB + 5 * c.nreg 120080 + 3 ≤ W)
    (hpos : V.POS + c.nreg 120080 ≤ W)
    {S : Set Point}
    (hS : Sweep.FirstHitOpt S z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))) :
    ∃ c' k, Exec P W arcScan c c' k ∧ k ≤ 1132 * (lenOf V.A (2 * V.m + 7) se ee p + 1) + 30 ∧
      FrameB BA c c' ∧ BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ scanned C (2 * V.m + 7) se (lenOf V.A (2 * V.m + 7) se ee p + 1)) z
        (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) := by
  have hv := hs.hv
  have hmn : C.m < P.n := by
    have := C.m_lt; rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] at this; exact this
  have hVm : V.m = C.m := hv.m
  have hAW : V.A ≤ W := by have := hw.1 120030; rw [hq.A] at this; exact this
  -- 1. the head
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W arcHead c c₁ k₁ ∧ k₁ = 11 ∧
      (c₁.nreg 120081 = se ∧ c₁.nreg 120082 = ee ∧ c₁.nreg 120083 = p ∧
        c₁.nreg 120087 = p + 1 ∧
        (∀ r, r ≠ 120081 → r ≠ 120082 → r ≠ 120083 → r ≠ 120086 → r ≠ 120087 →
          c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
        c₁.output = c.output) := by
    unfold arcHead
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; rw [hq.AB]; omega
    · config_simp; rw [hq.AB, hq.one]; omega
    · config_simp; rw [hq.AB, hq.one, hq.two]; omega
    · config_simp; rw [hq.POS]; omega
    · config_simp; rw [hq.POS, hq.one]
      rw [hp]; omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [hq.AB, hq.one, ← hse]; congr 1; ring
      · config_simp; rw [hq.AB, hq.one, hq.two]
        rw [← hee]; congr 1; ring
      · config_simp; rw [hq.POS]; exact hp
      · config_simp; rw [hq.POS, hq.one, hp]
      · config_simp; upd_solve
  obtain ⟨x81, x82, x83, x87, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have hq₁ : QConst P V c₁ := hq.congr fun r h1 h2 => r₁ r (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have w₁ := e₁.wb_right
  -- 2. the length
  set L0 := (if p + 1 < V.A then ee - se else ee + (2 * V.m + 7) - se) with hL0
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂⟩ : ∃ c₂ k₂, Exec P W arcLen c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
      c₂.nreg 120084 = L0 ∧ (∀ r, r ≠ 120084 → c₂.nreg r = c₁.nreg r) := by
    unfold arcLen
    by_cases hlt : p + 1 < V.A
    · refine ⟨_, _, .ifLtN_true (by rw [x87, hq₁.A]; exact hlt) (Exec.subN w₁ _ _ _), by omega,
        ?_, fun r hr => ?_⟩
      · config_simp; rw [x82, x81, hL0, ite_eq_left hlt]
      · config_simp; upd_solve
    · obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W
          (block [.addN 120084 120082 120020, .subN 120084 120084 120081]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
          (c₂.nreg 120084 = ee + (2 * V.m + 7) - se ∧
            ∀ r, r ≠ 120084 → c₂.nreg r = c₁.nreg r) := by
        exec_block
        · rw [x82, hq₁.nW]; have := hq.m; omega
        · refine ⟨rfl, ?_, fun r hr => ?_⟩
          · config_simp; rw [x82, hq₁.nW, x81]
          · config_simp; upd_solve
      exact ⟨c₂, _, .ifLtN_false (by rw [x87, hq₁.A]; exact hlt) e₂, by omega,
        by rw [v₂.1, hL0, ite_eq_right hlt], v₂.2⟩
  have w₂ := e₂.wb_right
  have hq₂ : QConst P V c₂ := hq₁.congr fun r h1 h2 => r₂ r (by omega)
  have hL0le : L0 ≤ 2 * (2 * V.m + 7) := by rw [hL0]; split_ifs <;> omega
  -- 3. the initialisation
  obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.addN 120084 120084 120048, .addN 120070 120081 120020, .subN 120070 120070 120011])
      c₂ c₃ k₃ ∧ k₃ = 3 ∧ (c₃.nreg 120084 = L0 + 2 ∧ c₃.nreg 120070 = se + (2 * V.m + 7) - 1 ∧
        ∀ r, r ≠ 120084 → r ≠ 120070 → c₃.nreg r = c₂.nreg r) := by
    exec_block
    · rw [v₂, hq₂.two]; have := hq.m; omega
    · config_simp; rw [r₂ _ (by decide), x81, hq₂.nW]; have := hq.m; omega
    · refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_⟩
      · config_simp; rw [v₂, hq₂.two]
      · config_simp; rw [r₂ _ (by decide), x81, hq₂.nW, hq₂.one]
      · config_simp; upd_solve
  obtain ⟨v84, v70, r₃⟩ := v₃
  have hq₃ : QConst P V c₃ := hq₂.congr fun r h1 h2 => r₃ r (by omega) (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄, -⟩ := modSub_exec (P := P) (r := 120070) (nr := 120020)
    (by decide) c₃ e₃.wb_right (by rw [v70, hq₃.nW]; omega)
  rw [v70, hq₃.nW] at v₄
  have hq₄ : QConst P V c₄ := hq₃.congr fun r h1 h2 => r₄ r (by omega)
  obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W
      (block [.constN 120085 0, .addN 120088 120084 120011]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      (c₅.nreg 120085 = 0 ∧ c₅.nreg 120088 = L0 + 2 + 1 ∧
        (∀ r, r ≠ 120085 → r ≠ 120088 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
        c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    have w₄ := e₄.wb_right
    exec_block
    · omega
    · config_simp; rw [r₄ _ (by decide), v84, hq₄.one]; have := hq.m; omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [r₄ _ (by decide), v84, hq₄.one]
      · config_simp; upd_solve
  obtain ⟨v85, v88, r₅, m₅, rr₅, rm₅, o₅⟩ := v₅
  have hlen : lenOf V.A (2 * V.m + 7) se ee p = L0 + 2 := rfl
  -- frames of the preparation
  have ex₀ : Exec P W (.seq arcHead (.seq arcLen arcInit)) c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have f₀' := exec_frameB ex₀ (B := fun r => decide (r = 120070) ||
    decide (120081 ≤ r ∧ r ≤ 120088)) (by decide)
  have f₀ : FrameB BA c c₅ := FrameB.mono f₀' fun r hr => by
    simp only [BA, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢; tauto
  have I₀ : AInv P W C V z c S se (L0 + 2) c₅ := by
    refine ⟨e₅.wb_right, hq₄.congr fun r h1 h2 => r₅ r (by omega) (by omega), ?_, by omega, v88,
      ?_, ?_, f₀⟩
    · unfold BestOK
      rw [f₀'.1 120050 (by decide), f₀'.1 120051 (by decide), f₀'.1 120052 (by decide)]
      exact hb
    · rw [r₅ _ (by decide) (by decide), v₄, v85]; rfl
    · have hbo : bestOf c₅ = bestOf c := by
        unfold bestOf; rw [f₀'.1 120050 (by decide), f₀'.1 120052 (by decide)]
      rw [hbo, v85]
      have : scanned C (2 * V.m + 7) se 0 = ∅ := by
        ext x; simp [scanned]
      rw [this, Set.union_empty]; exact hS
  -- 4. the loop
  obtain ⟨c₆, k₆, e₆, I₆, hex, hk₆⟩ := Exec.whileLtN_bounded (a := 120085) (b := 120088)
    (AInv P W C V z c S se (L0 + 2)) (fun d => L0 + 2 + 1 - d.nreg 120085) 1130
    (fun _ h => h.wb)
    (fun d hd ht => by
      obtain ⟨d', k, e, I, hk, hi⟩ := arcBody_inv (P := P) hG hW hs hsen hd ht
      exact ⟨d', k, e, I, hk, hi⟩) I₀
  have ht6 : c₆.nreg 120085 = L0 + 2 + 1 := by
    have := I₆.t_le; rw [I₆.lim] at hex; omega
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq (.seq e₃ (.seq e₄ e₅)) e₆)), ?_, I₆.fr, I₆.b, ?_⟩
  · rw [v85] at hk₆
    rw [hlen]; omega
  · have := I₆.hit
    rw [ht6] at this
    rw [hlen]; exact this

end

end OracleR

end Chazelle.Core
