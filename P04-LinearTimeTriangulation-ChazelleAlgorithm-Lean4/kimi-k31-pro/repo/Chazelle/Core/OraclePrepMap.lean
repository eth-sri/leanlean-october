module

public import Chazelle.Core.OraclePrepRot
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 2000000

/-!
# Lemma 3.6 (WP-H), preprocessing part 23: the planar map of the book in memory

`mapS`: from the chord arrays of a valid book, the dart arrays (tails, keys, opposite darts), the
darts sorted by (tail, key), the first positions, the rotation and the three handle words; the
result is robustly a planar map (`PlanarMapAt`) whose graph is the book graph (`mapS_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData

@[expose] public section

/-- **The planar map from the arrays.** -/
theorem planar_of_mem {B : BookData} (hV : B.Valid) {m : ℕ → ℕ} {Bh VT ROT : ℕ} {s : ℕ → ℕ}
    (hsd : SortedDarts (2 * B.E) (fun d => View.tail B.N (B.view d))
      (fun d => View.key B.N (B.view d)) s)
    (hvt : ∀ d, d < 2 * B.E → m (VT + d) = View.tail B.N (B.view d))
    (hop : ∀ d, d < 2 * B.E → m (VT + 4 * B.E + d) = oppN d)
    (hrot : ∀ t, t < 2 * B.E → m (ROT + s t) = rotN (2 * B.E) (fun d => View.tail B.N (B.view d)) s t)
    (h0 : m Bh = VT + 4 * B.E) (h1 : m (Bh + 1) = ROT) (h2 : m (Bh + 2) = VT) :
    PlanarMapAt m Bh B.N B.E ∧ memGraph m Bh B.N B.E = OracleQ.bookGraph B := by
  have hopp : ∀ d, d < 2 * B.E → m (m Bh + d) = oppN d := fun d hd => by rw [h0]; exact hop d hd
  have hvt' : ∀ d, d < 2 * B.E → m (m (Bh + 2) + d) = View.tail B.N (B.view d) := fun d hd => by
    rw [h2]; exact hvt d hd
  refine ⟨planarMapAt_of_arrays hV hopp (fun d hd => ?_) hvt', memGraph_eq hopp hvt'⟩
  obtain ⟨t, ht, rfl⟩ := hsd.surj d hd
  rw [h1, hrot t ht, ← rot_eq_csucc hV hsd ht]

/-! ## The set-up blocks -/

/-- The dart arrays at the allocator: `VT` (`60050`), `VT + 2 E` (`60051`), `VT + 4 E`
(`60052`); the allocator grows by `6 E`. -/
def vtS : Stmt :=
  block [.copyN 60050 9999, .addN 60051 60050 60037, .addN 60051 60051 60037,
    .addN 60052 60051 60037, .addN 60052 60052 60037, .addN 9999 60052 60037,
    .addN 9999 9999 60037]

theorem vtS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {E A₀ : ℕ}
    (hE : c.nreg 60037 = E) (hA : c.nreg 9999 = A₀) (hW : A₀ + 6 * E ≤ W) :
    ∃ c' k, Exec P W vtS c c' k ∧ k = 7 ∧
      FrameB (fun r => decide (r = 60050 ∨ r = 60051 ∨ r = 60052 ∨ r = 9999)) c c' ∧
      c'.rreg = c.rreg ∧ c'.nreg 60050 = A₀ ∧ c'.nreg 60051 = A₀ + 2 * E ∧ c'.nreg 60052 = A₀ + 4 * E ∧
      c'.nreg 9999 = A₀ + 6 * E := by
  have hwr : wr (fun r => decide (r = 60050 ∨ r = 60051 ∨ r = 60052 ∨ r = 9999)) vtS = true := by
    decide
  suffices H : ∃ c' k, Exec P W vtS c c' k ∧ k = 7 ∧ c'.rreg = c.rreg ∧
      c'.nreg 60050 = A₀ ∧ c'.nreg 60051 = A₀ + 2 * E ∧ c'.nreg 60052 = A₀ + 4 * E ∧
      c'.nreg 9999 = A₀ + 6 * E by
    obtain ⟨c', k, ex, hk, rr, a, b, d, e⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, rr, a, b, d, e⟩
  unfold vtS
  exec_block
  · config_simp; rwo [hA, hE]
  · config_simp; rwo [hA, hE]
  · config_simp; rwo [hA, hE]
  · config_simp; rwo [hA, hE]
  · config_simp; rwo [hA, hE]
  · config_simp; rwo [hA, hE]
  · exact ⟨rfl, rfl, by config_simp; rw [hA], by config_simp; rwring [hA, hE],
      by config_simp; rwring [hA, hE], by config_simp; rwring [hA, hE]⟩

/-- The inputs of the sort of the darts. -/
def sortPrep : Stmt :=
  block [.copyN 60004 60050, .copyN 60005 60051, .addN 60006 60037 60037, .copyN 60060 60006]

theorem sortPrep_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {E VT : ℕ}
    (hE : c.nreg 60037 = E) (h50 : c.nreg 60050 = VT) (h51 : c.nreg 60051 = VT + 2 * E)
    (hW : 2 * E ≤ W) :
    ∃ c' k, Exec P W sortPrep c c' k ∧ k = 4 ∧
      FrameB (fun r => decide ((60004 ≤ r ∧ r ≤ 60006) ∨ r = 60060)) c c' ∧
      c'.nreg 60004 = VT ∧ c'.nreg 60005 = VT + 2 * E ∧ c'.nreg 60006 = 2 * E ∧
      c'.nreg 60060 = 2 * E := by
  have hwr : wr (fun r => decide ((60004 ≤ r ∧ r ≤ 60006) ∨ r = 60060)) sortPrep = true := by
    decide
  suffices H : ∃ c' k, Exec P W sortPrep c c' k ∧ k = 4 ∧
      c'.nreg 60004 = VT ∧ c'.nreg 60005 = VT + 2 * E ∧ c'.nreg 60006 = 2 * E ∧
      c'.nreg 60060 = 2 * E by
    obtain ⟨c', k, ex, hk, a, b, d, e⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b, d, e⟩
  unfold sortPrep
  exec_block
  · config_simp; rwo [hE]
  · exact ⟨rfl, by config_simp; exact h50, by config_simp; exact h51,
      by config_simp; rwring [hE], by config_simp; rwring [hE]⟩

/-- Allocate `n` (register `rn`) words, base into `rb`. -/
def allocS (rb rn : ℕ) : Stmt := block [.copyN rb 9999, .addN 9999 9999 rn]

theorem allocS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {rb rn A n : ℕ}
    (hrb : rb ≠ 9999) (hA : c.nreg 9999 = A) (hn : c.nreg rn = n) (hrn : rn ≠ rb) (hW : A + n ≤ W) :
    ∃ c' k, Exec P W (allocS rb rn) c c' k ∧ k = 2 ∧
      FrameB (fun r => decide (r = rb ∨ r = 9999)) c c' ∧ c'.rreg = c.rreg ∧ c'.nreg rb = A ∧
      c'.nreg 9999 = A + n := by
  have hwr : wr (fun r => decide (r = rb ∨ r = 9999)) (allocS rb rn) = true := by
    simp [allocS, block, wr, wrOK]
  suffices H : ∃ c' k, Exec P W (allocS rb rn) c c' k ∧ k = 2 ∧ c'.rreg = c.rreg ∧
      c'.nreg rb = A ∧ c'.nreg 9999 = A + n by
    obtain ⟨c', k, ex, hk, rr, a, b⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, rr, a, b⟩
  unfold allocS
  exec_block
  · config_simp; rwo [upd_other _ _ _ (Ne.symm hrb), upd_other _ _ _ hrn, hA, hn]
  · exact ⟨rfl, rfl, by config_simp; rw [upd_other _ _ _ hrb]; simp [upd, hA],
      by config_simp; rw [upd_other _ _ _ (Ne.symm hrb), upd_other _ _ _ hrn, hA, hn]⟩

/-- The three handle words (`OPP`, `ROT`, `VT`) at the allocator; the handle into `60071`. -/
def hdS : Stmt :=
  block [.copyN 60071 9999, .addN 9999 9999 120048, .addN 9999 9999 120011, .storeN 60071 60052,
    .addN 60072 60071 120011, .storeN 60072 60062, .addN 60072 60072 120011, .storeN 60072 60050]

theorem hdS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {A OPP ROT VT : ℕ}
    (hA : c.nreg 9999 = A) (h1 : c.nreg 120011 = 1) (h2 : c.nreg 120048 = 2)
    (h52 : c.nreg 60052 = OPP) (h62 : c.nreg 60062 = ROT) (h50 : c.nreg 60050 = VT)
    (hW : A + 3 ≤ W) :
    ∃ c' k, Exec P W hdS c c' k ∧ k = 8 ∧
      (∀ r, r ≠ 60071 → r ≠ 60072 → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nmem = upd (upd (upd c.nmem A OPP) (A + 1) ROT) (A + 2) VT ∧
      c'.nreg 60071 = A ∧ c'.nreg 9999 = A + 3 := by
  unfold hdS
  exec_block
  · config_simp; rwo [hA, h2]
  · config_simp; rwo [hA, h2, h1]
  · config_simp; rwo [hA, h1]
  · config_simp; rwo [hA, h1]
  · refine ⟨rfl, fun r a b d => ?_, rfl, rfl, rfl, ?_, by config_simp; rw [hA],
      by config_simp; rw [hA, h2, h1]⟩
    · config_simp
      simp [upd_apply, a, b, d, ite_false]
    · config_simp; rw [hA, h1, h52, h62, h50]

/-! ## The map stage -/

/-- **The planar map of the book.** -/
def mapS : Stmt :=
  .seq vtS (.seq (passesS 6) (.seq sortPrep (.seq sortCore (.seq (allocS 60061 60034)
    (.seq fpS (.seq (allocS 60062 60060) (.seq rotS hdS)))))))

/-- The registers kept by `mapS`. -/
def MPres (r : ℕ) : Prop :=
  (60000 ≤ r ∧ r < 70000 ∧ (r < 60004 ∨ (60008 ≤ r ∧ r ≤ 60015) ∨ r = 60034 ∨ r = 60037 ∨
    60080 ≤ r)) ∨ (bandOf r ≠ 3 ∧ bandOf r ≠ 6 ∧ bandOf r ≠ 11 ∧ r ≠ 9999)

theorem MPres_not {r : ℕ} (h : MPres r) : ¬ ((60004 ≤ r ∧ r ≤ 60007) ∨ (60016 ≤ r ∧ r ≤ 60033) ∨
    (60035 ≤ r ∧ r ≤ 60036) ∨ (60038 ≤ r ∧ r ≤ 60079) ∨ r = 9999) := by
  ufo MPres bandOf at h

theorem b6_ne {r : ℕ} (hr : (decide (bandOf r = 6) || decide (r = 9999)) = false) :
    r ≠ 9999 ∧ (r < 60000 ∨ 70000 ≤ r) := by
  simp [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; ufo bandOf at hr

theorem mapS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {B : BookData}
    (hV : B.Valid) {CH1 CH2 A₀ : ℕ} (hN : c.nreg 60034 = B.N) (hI : c.nreg 60008 = B.I.length)
    (h1r : c.nreg 60001 = CH1) (h2r : c.nreg 60002 = CH2) (hone : c.nreg 120011 = 1)
    (htwo : c.nreg 120048 = 2) (hE : c.nreg 60037 = B.E) (hAl : c.nreg 9999 = A₀)
    (hP : PairsAt c.nmem CH1 CH2 (B.I ++ B.O)) (hC1 : CH1 + (B.I ++ B.O).length ≤ A₀)
    (hC2 : CH2 + (B.I ++ B.O).length ≤ A₀)
    (hroom : A₀ + 10 * B.E + SortR.sortCost 20 (2 * B.E) + B.N + 3 ≤ W) (hNW : 2 * B.N + 2 ≤ W) :
    ∃ c' k, Exec P W mapS c c' k ∧ k ≤ 400 * B.E + SortR.sortCost 20 (2 * B.E) + 100 ∧
      FrameN dBands c c' ∧ A₀ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + 10 * B.E + SortR.sortCost 20 (2 * B.E) + B.N + 3 ∧
      c'.nreg 60071 + 3 = c'.nreg ALLOC ∧
      (∀ r, MPres r → c'.nreg r = c.nreg r) ∧
      Robust (c'.nreg ALLOC) c'.nmem (fun m => PlanarMapAt m (c'.nreg 60071) B.N B.E ∧
        memGraph m (c'.nreg 60071) B.N B.E = OracleQ.bookGraph B) := by
  have hAL : ALLOC = 9999 := rfl
  set E := B.E with hEdef
  set N := B.N with hNdef
  have hLE : E = N + (B.I ++ B.O).length := by
    rw [hEdef, hNdef]; unfold BookData.E; sio only [List.length_append]
  -- 1. the dart arrays
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, rr₁, v50, v51, v52, v99⟩ :=
    vtS_exec (P := P) hw hE hAl (by omega)
  have K₁ : ∀ r, MPres r → c₁.nreg r = c.nreg r := fun r hr => F₁.1 r (by
    have := MPres_not hr; sio only [decide_eq_false_iff_not])
  have mp : ∀ r, (r = 60001 ∨ r = 60002 ∨ r = 60008 ∨ r = 60034 ∨ r = 60037) → MPres r :=
    fun r hr => Or.inl (by omega)
  have mq : ∀ r, (r = 120011 ∨ r = 120048) → MPres r :=
    fun r hr => Or.inr (by ufo bandOf)
  have DE : DartEnv N B.I.length CH1 CH2 A₀ E A₀ (B.I ++ B.O) c₁ :=
    { rN := by rw [K₁ _ (mp _ (by omega)), hN]
      rI := by rw [K₁ _ (mp _ (by omega)), hI]
      r1 := by rw [K₁ _ (mp _ (by omega)), h1r]
      r2 := by rw [K₁ _ (mp _ (by omega)), h2r]
      one := by rw [K₁ _ (mq _ (by omega)), hone]
      two := by rw [K₁ _ (mq _ (by omega)), htwo]
      rV := v50
      rK := v51
      rO := v52
      rE := by rw [K₁ _ (mp _ (by omega)), hE]
      pairs := by rwx [F₁.2.2.1]
      hE := hLE
      hC1 := hC1
      hC2 := hC2
      hlo := le_rfl
      ends := fun t ht => by
        have hm := getD_mem ht
        rcases List.mem_append.1 hm with h | h
        · have := hV.2.2.2.1 _ h; ufo ChordOK at this
        · have := hV.2.2.2.2.1 _ h; ufo ChordOK at this
      hI := by simp }
  -- 2. the passes
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, D₂, m₂, rm₂, o₂, J₂⟩ :=
    passesS_exec (P := P) e₁.wb_right (j := 6) le_rfl DE hNW (by omega)
  have arrs := fun d (hd : d < 2 * E) => darts_of B hV D₂ hd
  have K₂ : ∀ r, MPres r → c₂.nreg r = c₁.nreg r := fun r hr => r₂ r
    (by have := MPres_not hr; unfold BEd; sio only [decide_eq_false_iff_not])
    (by have := MPres_not hr; unfold BDV; sio only [decide_eq_false_iff_not])
    (by have := MPres_not hr; omega)
  -- 3. the inputs of the sort
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, w4, w5, w6, w60⟩ :=
    sortPrep_exec (P := P) e₂.wb_right J₂.rE J₂.rV J₂.rK (by omega)
  have K₃ : ∀ r, MPres r → c₃.nreg r = c₂.nreg r := fun r hr => F₃.1 r (by
    have := MPres_not hr; sio only [decide_eq_false_iff_not])
  have a99₃ : c₃.nreg 9999 = A₀ + 6 * E := by
    rw [F₃.1 _ (by decide), r₂ _ (by decide) (by decide) (by decide), v99]
  have one₃ : c₃.nreg 120011 = 1 := by
    rw [K₃ _ (mq _ (by omega)), K₂ _ (mq _ (by omega)), K₁ _ (mq _ (by omega)), hone]
  have hm₃ : c₃.nmem = c₂.nmem := F₃.2.2.1
  -- 4. the sort
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, al₄a, al₄b, R₄, sb₁, sb₂, hsort, hsurj, hlt⟩ :=
    sortCore_exec (P := P) e₃.wb_right (Z1 := A₀) (Z2 := A₀ + 2 * E) (n := 2 * E)
      (A₀ := A₀ + 6 * E) w4 w5 w6 one₃ a99₃ (by omega) (by omega) (by omega)
  rw [hAL] at al₄a al₄b
  have K₄ : ∀ r, MPres r → c₄.nreg r = c₃.nreg r := fun r hr => by
    rcases hr with h | h
    · exact R₄ r (by ufo bandOf) (by omega) (by omega) (by omega) (by omega)
    · exact F₄.1 r (by sio [dBands, bSort, bDecomp, bOPrep]) (by rw [hAL]; exact h.2.2.2)
  have mem₄ : ∀ a, a < A₀ + 6 * E → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [F₄.2.2.1 a (by rwx [hAL, a99₃]), hm₃]
  have k50 : c₄.nreg 60050 = A₀ := by
    rw [R₄ _ (by ufo bandOf) (by omega) (by omega) (by omega) (by omega),
      F₃.1 _ (by decide), r₂ _ (by decide) (by decide) (by decide), v50]
  have k52 : c₄.nreg 60052 = A₀ + 4 * E := by
    rw [R₄ _ (by ufo bandOf) (by omega) (by omega) (by omega) (by omega),
      F₃.1 _ (by decide), r₂ _ (by decide) (by decide) (by decide), v52]
  have k60 : c₄.nreg 60060 = 2 * E := by
    rw [R₄ _ (by ufo bandOf) (by omega) (by omega) (by omega) (by omega), w60]
  have k34 : c₄.nreg 60034 = N := by
    rw [K₄ _ (mp _ (by omega)), K₃ _ (mp _ (by omega)), K₂ _ (mp _ (by omega)),
      K₁ _ (mp _ (by omega)), hN]
  -- the sorted darts
  set Sb := c₄.nreg 60007 with hSb
  set F := c₄.nreg 9999 with hF
  -- 5. the first positions
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, rr₅, f61, f99⟩ := allocS_exec (P := P) e₄.wb_right (rb := 60061)
    (rn := 60034) (A := F) (n := N) (by decide) rfl k34 (by decide) (by omega)
  have hm₅ : c₅.nmem = c₄.nmem := F₅.2.2.1
  have K₅ : ∀ r, MPres r → c₅.nreg r = c₄.nreg r := fun r hr => F₅.1 r (by
    have := MPres_not hr; sio only [decide_eq_false_iff_not])
  have hGt : ∀ d, d < 2 * E → c₄.nmem (A₀ + d) = View.tail N (B.view d) := fun d hd => by
    rw [mem₄ _ (by omega)]; exact (arrs d hd).1
  have hGl : ∀ d, d < 2 * E → View.tail N (B.view d) < N := fun d hd =>
    tail_lt hV (view_ok hd)
  have hJ5 : FPJ Sb A₀ (2 * E) F c₅.nmem c₅ :=
    ⟨by rw [F₅.1 _ (by decide)], by rw [F₅.1 _ (by decide), k50],
      by rw [F₅.1 _ (by decide), k60], f61,
      by rw [K₅ _ (mq _ (by omega)), K₄ _ (mq _ (by omega)), one₃], fun _ _ => rfl⟩
  obtain ⟨c₆, k₆, e₆, hk₆, r₆, rr₆, mm₆, rm₆, o₆, J₆⟩ := fpS_exec (P := P) e₅.wb_right (N := N)
    hJ5 (by omega) (by omega) (fun t ht => by rw [hm₅]; exact hlt t ht)
    (fun d hd => by rw [hm₅, hGt d hd]; exact hGl d hd) (by omega)
  have K₆ : ∀ r, MPres r → c₆.nreg r = c₅.nreg r := fun r hr => r₆ r
    (by have := MPres_not hr; unfold BR; sio only [decide_eq_false_iff_not])
    (by have := MPres_not hr; omega)
  -- 6. the rotation
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, rr₇, g62, g99⟩ := allocS_exec (P := P) e₆.wb_right (rb := 60062)
    (rn := 60060) (A := F + N) (n := 2 * E) (by decide)
    (by rw [r₆ _ (by decide) (by decide), f99]) J₆.2.2.1 (by decide) (by omega)
  have hm₇ : c₇.nmem = c₆.nmem := F₇.2.2.1
  have K₇ : ∀ r, MPres r → c₇.nreg r = c₆.nreg r := fun r hr => F₇.1 r (by
    have := MPres_not hr; sio only [decide_eq_false_iff_not])
  have below7 : ∀ a, a < F → c₇.nmem a = c₄.nmem a := fun a ha => by
    rw [hm₇, mm₆, scat_below (fun i _ => by omega) ha, hm₅]
  have mS7 : ∀ t, t < 2 * E → c₇.nmem (Sb + t) = c₄.nmem (Sb + t) := fun t ht =>
    below7 _ (by omega)
  have mV7 : ∀ d, d < 2 * E → c₇.nmem (A₀ + d) = View.tail N (B.view d) := fun d hd => by
    rw [below7 _ (by omega)]; exact hGt d hd
  have hcong : ∀ t, t < 2 * E → c₇.nmem (A₀ + c₇.nmem (Sb + t)) =
      View.tail N (B.view (c₄.nmem (Sb + t))) := fun t ht => by
    rw [mS7 t ht, mV7 _ (hlt t ht)]
  have hfpv : ∀ t, t < 2 * E → c₇.nmem (F + View.tail N (B.view (c₄.nmem (Sb + t)))) =
      fpN (2 * E) (fun d => View.tail N (B.view d)) (fun t => c₄.nmem (Sb + t))
        (View.tail N (B.view (c₄.nmem (Sb + t)))) := fun t ht => by
    rw [hm₇, mm₆]
    refine fp_scat (G := fun d => View.tail N (B.view d)) (s := fun t => c₄.nmem (Sb + t))
      (fun i hi => ?_) _ ht
    rw [hm₅, hGt _ (hlt _ (by omega))]
  have hJ7 : RotJ Sb A₀ (2 * E) F (F + N) c₇.nmem c₇ :=
    ⟨by rw [F₇.1 _ (by decide)]; exact J₆.1, by rw [F₇.1 _ (by decide)]; exact J₆.2.1,
      by rw [F₇.1 _ (by decide)]; exact J₆.2.2.1, by rw [F₇.1 _ (by decide)]; exact J₆.2.2.2.1,
      g62, by rw [F₇.1 _ (by decide)]; exact J₆.2.2.2.2.1, fun _ _ => rfl⟩
  obtain ⟨c₈, k₈, e₈, hk₈, r₈, rr₈, mm₈, rm₈, o₈, J₈⟩ := rotS_exec (P := P) e₇.wb_right
    (N := N) hJ7 (by omega) (by omega) le_rfl (by omega)
    (fun t ht => by rw [mS7 t ht]; exact hlt t ht)
    (fun d hd => by rw [mV7 d hd]; exact hGl d hd)
    (fun t ht => by
      rw [hcong t ht, hfpv t ht, fpN_congr (G := fun d => c₇.nmem (A₀ + d)) (s := fun t => c₇.nmem (Sb + t))
        (G' := fun d => View.tail N (B.view d)) (s' := fun t => c₄.nmem (Sb + t)) (hcong)])
    (fun t ht => by
      rw [hcong t ht, fpN_congr (G := fun d => c₇.nmem (A₀ + d)) (s := fun t => c₇.nmem (Sb + t))
        (G' := fun d => View.tail N (B.view d)) (s' := fun t => c₄.nmem (Sb + t)) (hcong)]
      exact (fpN_spec' ht).1)
  have K₈ : ∀ r, MPres r → c₈.nreg r = c₇.nreg r := fun r hr => r₈ r
    (by have := MPres_not hr; unfold BR; sio only [decide_eq_false_iff_not])
    (by have := MPres_not hr; omega)
  -- 7. the handle
  obtain ⟨c₉, k₉, e₉, hk₉, K₉', rr₉, rm₉, o₉, mm₉, b71, b99⟩ := hdS_exec (P := P) e₈.wb_right
    (A := F + N + 2 * E) (OPP := A₀ + 4 * E) (ROT := F + N) (VT := A₀)
    (by rw [r₈ _ (by decide) (by decide), g99])
    J₈.2.2.2.2.2.1
    (by rw [K₈ _ (mq _ (by omega)), K₇ _ (mq _ (by omega)), K₆ _ (mq _ (by omega)),
      K₅ _ (mq _ (by omega)), K₄ _ (mq _ (by omega)), K₃ _ (mq _ (by omega)),
      K₂ _ (mq _ (by omega)), K₁ _ (mq _ (by omega)), htwo])
    (by rw [r₈ _ (by decide) (by decide), F₇.1 _ (by decide), r₆ _ (by decide) (by decide),
      F₅.1 _ (by decide), k52])
    J₈.2.2.2.2.1 J₈.2.1 (by omega)
  have K₉ : ∀ r, MPres r → c₉.nreg r = c₈.nreg r := fun r hr =>
    K₉' r (by have := MPres_not hr; omega) (by have := MPres_not hr; omega)
      (by have := MPres_not hr; omega)
  have ex : Exec P W mapS c c₉ _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉)))))))
  refine ⟨c₉, _, ex, by omega, ?_, by rwo [hAL, b99], by rwo [hAL, b99],
    by rw [hAL, b99, b71], fun r hr => by
      rw [K₉ r hr, K₈ r hr, K₇ r hr, K₆ r hr, K₅ r hr, K₄ r hr, K₃ r hr, K₂ r hr, K₁ r hr], ?_⟩
  · have hB6 : ∀ r, (decide (bandOf r = 6) || decide (r = 9999)) = true →
        bandOf r ∈ dBands ∨ r = ALLOC := fun r hr => by
      simp [Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with h | h
      · left; simp [dBands, bDecomp, h]
      · right; exact h
    have FA : FrameN dBands c c₃ := PF.frameN (B := fun r => decide (bandOf r = 6) || decide (r = 9999))
      ⟨fun r hr => by
        have := b6_ne hr
        rw [F₃.1 r (by sio only [decide_eq_false_iff_not]),
          r₂ r (by unfold BEd; sio only [decide_eq_false_iff_not])
            (by unfold BDV; sio only [decide_eq_false_iff_not]) (by omega),
          F₁.1 r (by sio only [decide_eq_false_iff_not])],
      fun r hr => by
        have := b6_ne hr
        rw [F₃.2.1 r (by sio only [decide_eq_false_iff_not]),
          rr₂ r (by unfold BEd; sio only [decide_eq_false_iff_not])
            (by unfold BDV; sio only [decide_eq_false_iff_not]), rr₁],
      fun a ha => by
        rw [hAL, hAl] at ha
        rw [hm₃, m₂ a (Or.inl ha), F₁.2.2.1],
      fun a ha => by rw [F₃.2.2.2.1, rm₂, F₁.2.2.2.1],
      by rw [F₃.2.2.2.2, o₂, F₁.2.2.2.2]⟩ hB6
      (by rw [hAL, F₃.2.1 _ (by decide), rr₂ _ (by decide) (by decide), rr₁])
    have FC : FrameN dBands c₄ c₉ :=
      PF.frameN (B := fun r => decide (bandOf r = 6) || decide (r = 9999))
      ⟨fun r hr => by
        have := b6_ne hr
        rw [K₉' r (by omega) (by omega) (by omega),
          r₈ r (by unfold BR; sio only [decide_eq_false_iff_not]) (by omega),
          F₇.1 r (by sio only [decide_eq_false_iff_not]),
          r₆ r (by unfold BR; sio only [decide_eq_false_iff_not]) (by omega),
          F₅.1 r (by sio only [decide_eq_false_iff_not])],
      fun r hr => by
        have := b6_ne hr
        rw [rr₉, rr₈ r (by unfold BR; sio only [decide_eq_false_iff_not]), rr₇,
          rr₆ r (by unfold BR; sio only [decide_eq_false_iff_not]), rr₅],
      fun a ha => by
        rw [hAL] at ha
        have ha' : a < F := ha
        rw [mm₉, upd_other _ _ _ (show a ≠ F + N + 2 * E + 2 by omega),
          upd_other _ _ _ (show a ≠ F + N + 2 * E + 1 by omega),
          upd_other _ _ _ (show a ≠ F + N + 2 * E by omega), mm₈,
          scat_below (fun i _ => by omega) (show a < F + N by omega), hm₇, mm₆,
          scat_below (fun i _ => by omega) ha', hm₅],
      fun a ha => by rw [rm₉, rm₈, F₇.2.2.2.1, rm₆, F₅.2.2.2.1],
      by rw [o₉, o₈, F₇.2.2.2.2, o₆, F₅.2.2.2.2]⟩ hB6
      (by rw [hAL, rr₉, rr₈ _ (by decide), rr₇, rr₆ _ (by decide), rr₅])
    exact (FA.trans F₄ (by rwo [hAL, hAl, a99₃])).trans FC
      (by rw [hAL, hAl]; show A₀ ≤ F; omega)
  · unfold Robust
    intro m' hm'
    rw [b71]
    have hA9 : c₉.nreg ALLOC = F + N + 2 * E + 3 := by rw [hAL, b99]
    have below9' : ∀ a, a < F + N + 2 * E → m' a = c₈.nmem a := by
      intro a ha
      have e1 := hm' a (by rwo [hA9])
      rw [e1, mm₉]
      simp [upd_apply]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    have below9 : ∀ a, a < F + N → m' a = c₇.nmem a := fun a ha => by
      rw [below9' a (by omega), mm₈, scat_below (fun i _ => by omega) ha]
    have hsort' : SortedSeq (fun d => (View.tail N (B.view d), View.key N (B.view d)))
        (fun t => c₄.nmem (Sb + t)) (2 * E) :=
      SortedSeq.congr (pr := fun i => c₃.nmem (A₀ + i)) (pr' := fun i => c₃.nmem (A₀ + 2 * E + i))
        hsort (fun t ht => ⟨by
          show c₃.nmem (A₀ + _) = _; rw [hm₃]; exact (arrs _ (hlt t ht)).1, by
          show c₃.nmem (A₀ + 2 * E + _) = _; rw [hm₃]; exact (arrs _ (hlt t ht)).2.1⟩)
    have hsd : SortedDarts (2 * B.E) (fun d => View.tail B.N (B.view d))
        (fun d => View.key B.N (B.view d)) (fun t => c₄.nmem (Sb + t)) :=
      sortedDarts_of hsort' hlt hsurj fun d d' hd hd' hg hk =>
        congrArg Fin.val (keyInj hV ⟨d, hd⟩ ⟨d', hd'⟩ hg hk)
    refine planar_of_mem hV (VT := A₀) (ROT := F + N) hsd (fun d hd => ?_) (fun d hd => ?_)
      (fun t ht => ?_) ?_ ?_ ?_
    · rw [below9 _ (by omega), mV7 d hd]
    · rw [below9 _ (by omega), below7 _ (by omega), mem₄ _ (by omega)]; exact (arrs d hd).2.2
    · have hst := hlt t ht
      rw [below9' _ (by omega), mm₈]
      have hgt : F + N + c₄.nmem (Sb + t) = (fun t => F + N + c₇.nmem (Sb + t)) t := by
        simp; rw [mS7 t ht]
      rw [hgt, scat_at ht fun j hj htj e => by
        try simp at e
        rw [mS7 j hj, mS7 t ht] at e
        have := inj_of_surj hlt hsurj hj ht (by omega)
        omega]
      exact rotN_congr mS7 hcong ht
    · rw [hm' _ (by rwo [hA9]), mm₉, upd_other _ _ _ (show F + N + 2 * E ≠ F + N + 2 * E + 2 by omega),
        upd_other _ _ _ (show F + N + 2 * E ≠ F + N + 2 * E + 1 by omega)]
      simp [upd, hEdef]
    · rw [hm' _ (by rwo [hA9]), mm₉,
        upd_other _ _ _ (show F + N + 2 * E + 1 ≠ F + N + 2 * E + 2 by omega)]
      simp [upd]
    · rw [hm' _ (by rwo [hA9]), mm₉]
      simp [upd]

end

end OracleR

end Chazelle.Core
