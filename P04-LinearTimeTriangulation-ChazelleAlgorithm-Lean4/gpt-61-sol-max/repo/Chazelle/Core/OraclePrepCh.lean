module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OraclePrepChCmp

/-!
# Lemma 3.6 (WP-H), preprocessing part 27: the chord table

`chSortS`: the chord records `0 … K - 1` sorted by `ChLe` (`chCmp`); the base of the sorted table
in `60120` (`chSort_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

theorem chLe_refl (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (a : ℕ) : ChLe P C V m a a :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, fun _ => le_rfl⟩⟩

theorem chLe_congr {P : Polygon} {C : Chain} {V : QV} {m m' : ℕ → ℕ} {i j : ℕ}
    (h : ∀ x, x = i ∨ x = j → m (V.CB + 5 * x) = m' (V.CB + 5 * x) ∧
      m (V.CB + 5 * x + 1) = m' (V.CB + 5 * x + 1)) :
    ChLe P C V m i j ↔ ChLe P C V m' i j := by
  simp_all [ChLe, chH, chL] 

/-- **The chord table.** -/
def chSortS : Stmt :=
  .seq (block [.copyN 60006 120039, .copyN 116000 120043, .copyN 116001 120039])
    (.seq itemS (.seq (.instr (.copyN 30004 60006))
      (.seq (SortR.sortStmt chCmp) (.instr (.copyN 60120 30005)))))

/-- The bands of the chord table. -/
def chBands : Finset ℕ := {bSort, bSign, bDecomp, bOPrep, bOQuery}

set_option maxHeartbeats 4000000 in
theorem chSort_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {c : Config} (hw : WordsBounded W c) {A₀ : ℕ} (hv : QVOK P C (qvOf c))
    (hq : QConst P (qvOf c) c) (hAl : c.nreg 9999 = A₀)
    (hrec : ∀ i, i < (qvOf c).K → (qvOf c).CB + 5 * i + 2 ≤ A₀)
    (hh : ∀ i, i < (qvOf c).K → c.nmem ((qvOf c).CB + 5 * i) < P.n)
    (htv : (qvOf c).tv < P.n) (hn : 0 < P.n)
    (hroom : A₀ + (qvOf c).K + SortR.sortCost 500 (qvOf c).K ≤ W) :
    ∃ c' k, Exec P W chSortS c c' k ∧ k ≤ 7 * (qvOf c).K + SortR.sortCost 500 (qvOf c).K + 20 ∧
      FrameN chBands c c' ∧ A₀ + (qvOf c).K ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + (qvOf c).K + SortR.sortCost 500 (qvOf c).K ∧
      (∀ r, bandOf r = 6 → r ≠ 60006 → r ≠ 60016 → r ≠ 60017 → r ≠ 60020 → r ≠ 60120 →
        c'.nreg r = c.nreg r) ∧
      (∀ r, 120010 ≤ r → r ≤ 120049 → c'.nreg r = c.nreg r) ∧
      A₀ + (qvOf c).K ≤ c'.nreg 60120 ∧ c'.nreg 60120 + (qvOf c).K ≤ c'.nreg ALLOC ∧
      (∀ q, q < (qvOf c).K → c'.nmem (c'.nreg 60120 + q) < (qvOf c).K) ∧
      (∀ q q', q < (qvOf c).K → q' < (qvOf c).K →
        c'.nmem (c'.nreg 60120 + q) = c'.nmem (c'.nreg 60120 + q') → q = q') ∧
      (∀ q q', q ≤ q' → q' < (qvOf c).K →
        ChLe P C (qvOf c) c.nmem (c'.nmem (c'.nreg 60120 + q)) (c'.nmem (c'.nreg 60120 + q'))) := by
  have hAL : ALLOC = 9999 := rfl
  set V := qvOf c with hV
  set K := V.K with hKdef
  have hK : c.nreg 120039 = K := rfl
  have hCB : c.nreg 120043 = V.CB := rfl
  -- 1. the inputs
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a6, a0, a1⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 60006 120039, .copyN 116000 120043, .copyN 116001 120039]) c c₁ k₁ ∧ k₁ = 3 ∧
      FrameB (fun r => decide (r = 60006 ∨ r = 116000 ∨ r = 116001)) c c₁ ∧
      c₁.nreg 60006 = K ∧ c₁.nreg 116000 = V.CB ∧ c₁.nreg 116001 = K := by
    have hwr : wr (fun r => decide (r = 60006 ∨ r = 116000 ∨ r = 116001))
      (block [.copyN 60006 120039, .copyN 116000 120043, .copyN 116001 120039]) = true := by decide
    suffices H : ∃ c₁ k₁, Exec P W (block [.copyN 60006 120039, .copyN 116000 120043,
        .copyN 116001 120039]) c c₁ k₁ ∧ k₁ = 3 ∧
        c₁.nreg 60006 = K ∧ c₁.nreg 116000 = V.CB ∧ c₁.nreg 116001 = K by
      obtain ⟨c₁, k₁, ex, hk, a, b, d⟩ := H
      exact ⟨c₁, k₁, ex, hk, exec_frameB ex hwr, a, b, d⟩
    exec_block
    ram_simp
  have h1 : c.nreg 120011 = 1 := hq.one
  -- 2. the items
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.copyN 30003 9999, .addN 9999 9999 60006]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg = upd (upd c₁.nreg 30003 A₀) 9999 (A₀ + K) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have w₁ := e₁.wb_right
    have a9 : c₁.nreg 9999 = A₀ := by ram_grind
    exec_block
    · omega_nf
    simp_all
  have b30 : c₂.nreg 30003 = A₀ := by ram_simp
  have b6 : c₂.nreg 60006 = K := by ram_simp
  have b11 : c₂.nreg 120011 = 1 := by rw [n₂]; config_simp; rw [F₁.1 _ (by decide), h1]
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mm₃, rm₃, o₃, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60020) (rn := 60006) (r1 := 120011) (ra := 60016) (rv := 60017)
    (body := block [.addN 60016 30003 60020, .copyN 60017 60020])
    (B := fun r => decide (r = 60016 ∨ r = 60017)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (JK c₂ (fun r => decide (r = 30003)) A₀) A₀
    (fun d d' hJ hr hm => JK.stable (rs := [60020]) (fun r hr' => by
      grind) hJ
      (fun r a b => hr r a (by grind)) hm)
    (n := K) (κ := 2) (fun i => A₀ + i) (fun i => i) (fun i _ => by omega)
    (fun i d hi hJ hwd hri => by
      have g30 : d.nreg 30003 = A₀ := by ram_grind
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (block [.addN 60016 30003 60020,
          .copyN 60017 60020]) d d' k ∧ k = 2 ∧ d'.nreg 60016 = A₀ + i ∧ d'.nreg 60017 = i := by
        exec_block
        · omega
        simp_all
      exact ⟨d', k, e, by omega, exec_frameB e (by decide), v1, v2⟩)
    e₂.wb_right (JK.refl _ _ _) b6 b11 (by  omega)
  have R₃ : ∀ r, r ≠ 60016 → r ≠ 60017 → r ≠ 60020 → c₃.nreg r = c₂.nreg r := fun r a b c' =>
    r₃ r (by simp; omega) c'
  -- 3. the count of the sort
  have e₄ := Exec.copyN (P := P) e₃.wb_right 30004 60006
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 30004 (c₃.nreg 60006) } with hc₄
  have R₄ : ∀ r, r ≠ 30004 → c₄.nreg r = c₃.nreg r := fun r hr => by
    rw [hc₄]; config_simp; rw [upd_other _ _ _ hr]
  have hm₄ : c₄.nmem = c₃.nmem := rfl
  have g9 : c₄.nreg 9999 = A₀ + K := by
    ram_simp
  have g30 : c₄.nreg 30003 = A₀ := by
    grind
  have g304 : c₄.nreg 30004 = K := by
    ram_simp
  have hitems : SortL.seg c₄.nmem (c₄.nreg 30003) (List.range K).length = List.range K := by
    rw [g30, List.length_range, hm₄, mm₃]
    unfold SortL.seg
    apply List.ext_getElem (by simp)
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    exact scat_at (g := fun i => A₀ + i) (f := fun i => i) h1 (fun j _ hj => by omega)
  have hmem₄ : ∀ a, a < A₀ → c₄.nmem a = c.nmem a := fun a ha => by
    rw [hm₄, mm₃, scat_below (fun i _ => by omega) ha, m₂, F₁.2.2.1]
  -- 4. the sort
  have hband : ∀ r, 120010 ≤ r → r ≤ 120049 → c₄.nreg r = c.nreg r := fun r a b => by
    rw [R₄ r (by omega), R₃ r (by omega) (by omega) (by omega), n₂]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      F₁.1 r (by grind)]
  have hJ₄ : ChCJ c c₄.nmem (A₀ + K) K c₄ :=
    ⟨by ram_simp,
      by ram_simp,
      hband, fun _ _ => rfl⟩
  have hW' : A₀ + K ≤ W := by  omega
  obtain ⟨c₅, k₅, e₅, hk₅, J₅, F₅, s₁, s₂, L', hseg, hperm, hpw⟩ := SortR.sortStmt_exec (P := P)
    (W := W) (chCmp_ok hG hW hv hq (m₀ := c₄.nmem) (A₀ := A₀ + K) (K := K)
      (fun i hi => by grind) hW'
      (fun i hi => by
        grind) htv hn) (by decide)
    (fun a b d h h' => chLeB_trans _ _ _ _ _ _ _ _ h h') (chLeB_total _ _ _ _ _)
    e₄.wb_right hJ₄ (by rw [hAL, g9]; exact chCJ_stable _ _ _ _) (List.range K) hitems
    (by grind) (by grind)
    (by grind)
  rw [List.length_range] at hseg s₂ hk₅
  rw [hAL, g9] at s₁
  -- 5. the base of the table
  have e₆ := Exec.copyN (P := P) e₅.wb_right 60120 30005
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 60120 (c₅.nreg 30005) } with hc₆
  have ex : Exec P W chSortS c c₆ _ := .seq e₁ (.seq (.seq e₂ e₃) (.seq e₄ (.seq e₅ e₆)))
  have v120 : c₆.nreg 60120 = c₅.nreg 30005 := by ram_simp
  have hm₆ : c₆.nmem = c₅.nmem := rfl
  have hsd : ∀ t, t < K → c₆.nmem (c₆.nreg 60120 + t) = L'.getD t 0 := fun t ht => by
    rw [hm₆, v120, ← hseg, SortL.seg_getD t ht]
  have hL'len : L'.length = K := by grind [SortL.seg_length]
  have hmemL : ∀ t, t < K → L'.getD t 0 < K := fun t ht => by
    have : L'.getD t 0 ∈ L' := by rw [NFLoc.getD_of_lt 0 (by omega)]; grind
    grind
  have hF5 : ∀ r, bandOf r = 6 → c₅.nreg r = c₄.nreg r := fun r hr =>
    F₅.1 r (by simp [hr, bSort, bSign, bOPrep, bOQuery])
      (by grind [ALLOC, bandOf])
  have hsurj : ∀ i, i < K → ∃ t, t < K ∧ L'.getD t 0 = i := fun i hi => by
    have : i ∈ L' := hperm.symm.subset (List.mem_range.2 hi)
    obtain ⟨t, ht, e⟩ := List.getElem_of_mem this
    exact ⟨t, by omega, by rw [NFLoc.getD_of_lt 0 ht, e]⟩
  have hlt' : ∀ t, t < K → c₆.nmem (c₆.nreg 60120 + t) < K := fun t ht => by
    grind
  have hsurj' : ∀ i, i < K → ∃ t, t < K ∧ c₆.nmem (c₆.nreg 60120 + t) = i := fun i hi => by
    obtain ⟨t, ht, e⟩ := hsurj i hi; exact ⟨t, ht, by grind⟩
  refine ⟨c₆, _, ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlt', fun q q' hq hq' e =>
    inj_of_surj hlt' hsurj' hq hq' e, ?_⟩
  ·  omega
  · have hAl' : c.nreg ALLOC = A₀ := hAl
    have F14 : FrameN chBands c c₄ := by
      refine PF.frameN (B := fun r => decide (r = 9999) || decide (60001 ≤ r ∧ r ≤ 60020) ||
        decide (116000 ≤ r ∧ r ≤ 116001) || decide (30003 ≤ r ∧ r ≤ 30004))
        ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩ (fun r hr => ?_) ?_
      · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        rw [R₄ r (by omega), R₃ r (by omega) (by omega) (by omega), n₂]
        simp only [upd]; split_ifs <;> first | omega | exact F₁.1 r (by
          simp only [decide_eq_false_iff_not]; omega)
      · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        show c₃.rreg r = c.rreg r
        rw [rr₃ r (by simp only [decide_eq_false_iff_not]; omega), rr₂,
          F₁.2.1 r (by simp only [decide_eq_false_iff_not]; omega)]
      · grind
      · show c₃.rmem a = c.rmem a; rw [rm₃, rm₂, F₁.2.2.2.1]
      · show c₃.output = c.output; rw [o₃, o₂, F₁.2.2.2.2]
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with ((h | h) | h) | h
        · omega
        · left; simp [chBands, bDecomp, bandOf]; omega
        · left; simp [chBands, bOPrep, bandOf]; omega
        grind [chBands, bSort, bandOf]
      · show c₃.rreg ALLOC = c.rreg ALLOC
        rw [rr₃ _ (by decide), rr₂, F₁.2.1 _ (by decide)]
    have F56 : FrameN chBands c₅ c₆ :=
      Frame.toN (NFLoc.frame_of_frameB (exec_frameB e₆ (B := fun r => decide (r = 60120))
        (by decide)) (fun r hr => by
          simp at hr; subst hr; exact ⟨by simp [chBands, bDecomp, bandOf], by decide⟩) 1)
    have g9' : c₄.nreg ALLOC = A₀ + K := g9
    exact (F14.trans (FrameN.mono (Frame.toN F₅) (by decide))
      (by grind)).trans F56
      (by grind)
  · have := F₅.2.2.2.2.2.1; rw [hAL, g9] at this; rw [hc₆]; exact this
  · have := F₅.2.2.2.2.2.2; rw [hAL, g9] at this; rw [hc₆]; show c₅.nreg 9999 ≤ _; omega
  · intro r hr a b d e f
    rw [hc₆]; config_simp
    rw [upd_other _ _ _ f, hF5 r hr, R₄ r (by grind [bandOf]),
      R₃ r b d e, n₂]
    rw [upd_other _ _ _ (by grind [bandOf]),
      upd_other _ _ _ (by grind [bandOf]),
      F₁.1 r (by simp only [decide_eq_false_iff_not]; unfold bandOf at hr; omega)]
  · intro r a b
    rw [hc₆]; config_simp; rw [upd_other _ _ _ (by omega)]; exact J₅.2.2.1 r a b
  · grind
  · rw [v120, hc₆]; config_simp; exact s₂
  · intro q q' hqq hq'
    rw [hsd q (by omega), hsd q' hq']
    have hA := hmemL q (by omega)
    have hB := hmemL q' hq'
    have hconv : ∀ i j, i < K → j < K →
        (ChLe P C V c₄.nmem i j ↔ ChLe P C V c.nmem i j) := fun i j hi hj =>
      chLe_congr fun x hx => by
        have : x < K := by rcases hx with rfl | rfl <;> assumption
        grind
    rcases eq_or_lt_of_le hqq with h | h
    · subst h; exact chLe_refl _ _ _ _ _
    · have := List.pairwise_iff_getElem.1 hpw q q' (by omega) (by omega) h
      rw [← NFLoc.getD_of_lt 0 (by omega), ← NFLoc.getD_of_lt 0 (by omega)] at this
      unfold chLeB at this
      grind

end

end OracleR

end Chazelle.Core
