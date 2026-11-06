module

public import Chazelle.Core.OraclePrepPosRam

/-!
# Lemma 3.6 (WP-H), preprocessing part 6: the model descriptor and the inverse table

* `mdS`: a fresh model descriptor `[0, D₀, …, D₄]` of the chain (`120040 := MD`), `mdS_exec`;
* `posS'`: the inverse `POS` of the arc-sequence table (`120031 := POS`), `posS'_exec`.

Each stage allocates its array at the allocator and writes memory only from there on (the frame
`PF` with the entry allocator).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-! ## The model descriptor -/

/-- The copy body: address `MD + 1 + i`, value `D[i]`. -/
def mdBody : Stmt := block [.addN 110035 120013 110039, .loadN 110036 110035, .addN 110037 110033 110039]

/-- **The model descriptor**: six words at the allocator, `0` then the chain descriptor. -/
def mdS : Stmt :=
  .seq (block [.copyN 120040 9999, .constN 110030 6, .addN 9999 9999 110030, .constN 110031 0,
      .storeN 120040 110031, .addN 110033 120040 120011, .constN 110038 5])
    (scatS 110039 110038 120011 110037 110036 mdBody)

/-- The registers written by `mdS`. -/
def BMD (r : ℕ) : Bool := decide (r = 9999) || decide (r = 120040) || decide (110030 ≤ r ∧ r ≤ 110039)

theorem mdS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {D A₀ : ℕ}
    (hD : c.nreg 120013 = D) (h1 : c.nreg 120011 = 1) (hA : c.nreg 9999 = A₀) (hDA : D + 5 ≤ A₀)
    (hW : A₀ + 6 ≤ W) :
    ∃ c' k, Exec P W mdS c c' k ∧ k ≤ 60 ∧ PF BMD A₀ c c' ∧ c'.nreg 9999 = A₀ + 6 ∧
      c'.nreg 120040 = A₀ ∧ c'.nmem A₀ = 0 ∧ ∀ i, i < 5 → c'.nmem (A₀ + 1 + i) = c.nmem (D + i) := by
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120040 9999,
      .constN 110030 6, .addN 9999 9999 110030, .constN 110031 0, .storeN 120040 110031,
      .addN 110033 120040 120011, .constN 110038 5]) c c₁ k₁ ∧ k₁ = 7 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 120040 A₀) 110030 6) 9999 (A₀ + 6)) 110031 0)
        110033 (A₀ + 1)) 110038 5 ∧
      c₁.nmem = upd c.nmem A₀ 0 ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · config_simp; rw [hA]; omega
    · omega
    · config_simp; rw [hA, h1]; omega
    · omega
    · refine ⟨rfl, ?_, ?_, rfl, rfl, rfl⟩
      · config_simp; rw [hA, h1]
      · config_simp; rw [hA]
  have hr₁ : ∀ r, BMD r = false → c₁.nreg r = c.nreg r := fun r hr => by
    simp only [BMD, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [n₁]; simp only [upd]; split_ifs <;> first | omega
  have v₃₃ : c₁.nreg 110033 = A₀ + 1 := by rw [n₁]; config_simp
  have v₃₈ : c₁.nreg 110038 = 5 := by rw [n₁]; config_simp
  have v₁₃ : c₁.nreg 120013 = D := by rw [hr₁ _ (by decide), hD]
  have v₁₁ : c₁.nreg 120011 = 1 := by rw [hr₁ _ (by decide), h1]
  -- the copy loop
  let J : Config → Prop := JK c₁ (fun r => decide (r = 110033) || decide (r = 120013)) A₀
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, mm₂, rm₂, o₂, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 110039) (rn := 110038) (r1 := 120011) (ra := 110037) (rv := 110036) (body := mdBody)
    (B := fun r => decide (110035 ≤ r ∧ r ≤ 110037)) (by decide) (by decide) (by decide)
    (by decide) (by decide) J A₀
    (fun d d' hJ hr hm => JK.stable (rs := [110039]) (fun r hr' => by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hr'
      rcases hr' with rfl | rfl <;> decide) hJ (fun r a b => hr r a (by simpa using b)) hm)
    (n := 5) (κ := 3) (fun i => A₀ + 1 + i) (fun i => c.nmem (D + i)) (fun i _ => by omega)
    (fun i d hi hJ hwd hri => by
      have g33 : d.nreg 110033 = A₀ + 1 := by rw [hJ.1 _ (by decide), v₃₃]
      have g13 : d.nreg 120013 = D := by rw [hJ.1 _ (by decide), v₁₃]
      have gm : d.nmem (D + i) = c.nmem (D + i) := by
        rw [hJ.2 _ (by omega), m₁, upd_other _ _ _ (by omega)]
      obtain ⟨d', k', e', hk', v1, v2⟩ : ∃ d' k', Exec P W mdBody d d' k' ∧ k' = 3 ∧
          d'.nreg 110037 = A₀ + 1 + i ∧ d'.nreg 110036 = c.nmem (D + i) := by
        unfold mdBody
        exec_block
        · rw [g13, hri]; omega
        · config_simp; rw [g33, hri]; omega
        · refine ⟨rfl, ?_, ?_⟩
          · config_simp; rw [g33, hri]
          · config_simp; rw [g13, hri, gm]
      exact ⟨d', k', e', by omega, exec_frameB e' (by decide), v1, v2⟩)
    e₁.wb_right (JK.refl _ _ _) v₃₈ v₁₁ (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    fun a ha => by rw [rm₂, rm₁], by rw [o₂, o₁]⟩, ?_, ?_, ?_, fun i hi => ?_⟩
  · simp only [BMD, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [r₂ r (by simp; omega) (by omega)]; exact hr₁ r (by simp [BMD]; omega)
  · rw [rr₂ r (by simp only [BMD, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
      rr₁]
  · rw [mm₂, scat_below (fun i _ => by omega) ha, m₁, upd_other _ _ _ (by omega)]
  · rw [r₂ _ (by decide) (by decide), n₁]; config_simp
  · rw [r₂ _ (by decide) (by decide), n₁]; config_simp
  · rw [mm₂, scat_other (fun i _ => by omega), m₁, upd_same]
  · rw [mm₂]
    exact scat_at (g := fun i => A₀ + 1 + i) hi (fun j _ hij => by omega)

/-! ## The inverse of the arc-sequence table -/

/-- The inverse body: address `POS + σ p`, value `p`. -/
def posBody : Stmt :=
  block [.addN 110045 120046 110049, .loadN 110044 110045, .addN 110047 120031 110044,
    .copyN 110046 110049]

/-- **The inverse table**: `POS[σ p] := p` for `p < A`, with `σ` the table at `SB` (`120046`). -/
def posTS : Stmt :=
  .seq (block [.copyN 120031 9999, .addN 9999 9999 120030])
    (scatS 110049 120030 120011 110047 110046 posBody)

/-- The registers written by `posTS`. -/
def BPT (r : ℕ) : Bool := decide (r = 9999) || decide (r = 120031) || decide (110044 ≤ r ∧ r ≤ 110049)

theorem posTS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {SB A A₀ : ℕ}
    {σ : ℕ → ℕ} (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hseq : ∀ p, p < A → c.nmem (SB + p) = σ p) (hSA : SB + A ≤ A₀)
    (hW : A₀ + 2 * A ≤ W) (hlt : ∀ p, p < A → σ p < A)
    (hinj : ∀ p q, p < A → q < A → σ p = σ q → p = q)
    (hsurj : ∀ j, j < A → ∃ p, p < A ∧ σ p = j) :
    ∃ c' k, Exec P W posTS c c' k ∧ k ≤ 8 * A + 5 ∧ PF BPT A₀ c c' ∧ c'.nreg 9999 = A₀ + A ∧
      c'.nreg 120031 = A₀ ∧ ∀ j, j < A → c'.nmem (A₀ + j) < A ∧ σ (c'.nmem (A₀ + j)) = j := by
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120031 9999,
      .addN 9999 9999 120030]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg = upd (upd c.nreg 120031 A₀) 9999 (A₀ + A) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · config_simp; rw [hAl, hA]; omega
    · refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
      config_simp; rw [hAl, hA]
  have hr₁ : ∀ r, BPT r = false → c₁.nreg r = c.nreg r := fun r hr => by
    simp only [BPT, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [n₁]; simp only [upd]; split_ifs <;> first | omega
  have v31 : c₁.nreg 120031 = A₀ := by rw [n₁]; config_simp
  have v46 : c₁.nreg 120046 = SB := by rw [hr₁ _ (by decide), hSB]
  have v30 : c₁.nreg 120030 = A := by rw [hr₁ _ (by decide), hA]
  have v11 : c₁.nreg 120011 = 1 := by rw [hr₁ _ (by decide), h1]
  let J : Config → Prop := JK c₁ (fun r => decide (r = 120031) || decide (r = 120046)) A₀
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, mm₂, rm₂, o₂, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 110049) (rn := 120030) (r1 := 120011) (ra := 110047) (rv := 110046) (body := posBody)
    (B := fun r => decide (110044 ≤ r ∧ r ≤ 110047)) (by decide) (by decide) (by decide)
    (by decide) (by decide) J A₀
    (fun d d' hJ hr hm => JK.stable (rs := [110049]) (fun r hr' => by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hr'
      rcases hr' with rfl | rfl <;> decide) hJ (fun r a b => hr r a (by simpa using b)) hm)
    (n := A) (κ := 4) (fun p => A₀ + σ p) (fun p => p) (fun i _ => by omega)
    (fun i d hi hJ hwd hri => by
      have g31 : d.nreg 120031 = A₀ := by rw [hJ.1 _ (by decide), v31]
      have g46 : d.nreg 120046 = SB := by rw [hJ.1 _ (by decide), v46]
      have gm : d.nmem (SB + i) = σ i := by rw [hJ.2 _ (by omega), m₁, hseq i hi]
      have hσ := hlt i hi
      obtain ⟨d', k', e', hk', v1, v2⟩ : ∃ d' k', Exec P W posBody d d' k' ∧ k' = 4 ∧
          d'.nreg 110047 = A₀ + σ i ∧ d'.nreg 110046 = i := by
        unfold posBody
        exec_block
        · rw [g46, hri]; omega
        · config_simp; rw [g31, g46, hri, gm]; omega
        · refine ⟨rfl, ?_, ?_⟩
          · config_simp; rw [g31, g46, hri, gm]
          · config_simp; rw [hri]
      exact ⟨d', k', e', by omega, exec_frameB e' (by decide), v1, v2⟩)
    e₁.wb_right (JK.refl _ _ _) v30 v11 (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by nlinarith, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    fun a ha => by rw [rm₂, rm₁], by rw [o₂, o₁]⟩, ?_, ?_, fun j hj => ?_⟩
  · simp only [BPT, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [r₂ r (by simp; omega) (by omega)]; exact hr₁ r (by simp [BPT]; omega)
  · rw [rr₂ r (by simp only [BPT, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
      rr₁]
  · rw [mm₂, scat_below (fun i _ => by omega) ha, m₁]
  · rw [r₂ _ (by decide) (by decide), n₁]; config_simp
  · rw [r₂ _ (by decide) (by decide), v31]
  · obtain ⟨p, hp, hpj⟩ := hsurj j hj
    have := scat_at (m := c₁.nmem) (g := fun p => A₀ + σ p) (f := fun p => p) hp
      (fun q hq hpq e => by
        have : σ q = σ p := by simpa using e
        exact absurd (hinj q p hq hp this) (by omega))
    try simp only at this
    rw [mm₂, ← hpj, this]
    exact ⟨hp, rfl⟩

/-! ## The table of powers -/

/-- The body of the table loop: `TB[j] := x`, `x := 2 x`, `j := j + 1`. -/
def tbBody : Stmt :=
  block [.addN 110042 120041 120042, .storeN 110042 110040, .addN 110040 110040 110040,
    .addN 120042 120042 120011]

/-- **The table of powers** `2 ^ j` for `2 ^ j ≤ A + K` at the allocator (`120041`), its length
`L = ⌈log₂ (A + K + 1)⌉` in `120042`. -/
def tbS : Stmt :=
  .seq (block [.copyN 120041 9999, .constN 120042 0, .constN 110040 1, .addN 110041 120030 120039,
      .addN 110041 110041 120011])
    (.seq (.whileLtN 110040 110041 tbBody) (.instr (.addN 9999 9999 120042)))

/-- The registers written by `tbS`. -/
def BTB (r : ℕ) : Bool :=
  decide (r = 9999) || decide (r = 120041) || decide (r = 120042) || decide (110040 ≤ r ∧ r ≤ 110042)

theorem clog_succ_le (x : ℕ) : Nat.clog 2 (x + 1) ≤ Nat.clog 2 x + 1 := by
  rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.le_pow_clog (by norm_num : 1 < 2) x
    omega

theorem tbS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {A K A₀ : ℕ}
    (hA : c.nreg 120030 = A) (hK : c.nreg 120039 = K) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hW : A₀ + 2 * (A + K) + 4 ≤ W) :
    ∃ c' k, Exec P W tbS c c' k ∧ k ≤ 8 * Nat.clog 2 (A + K + 1) + 12 ∧ PF BTB A₀ c c' ∧
      c'.nreg 9999 = A₀ + Nat.clog 2 (A + K + 1) ∧ c'.nreg 120041 = A₀ ∧
      c'.nreg 120042 = Nat.clog 2 (A + K + 1) ∧
      (∀ j, j < Nat.clog 2 (A + K + 1) → c'.nmem (A₀ + j) = 2 ^ j) ∧
      A < 2 ^ Nat.clog 2 (A + K + 1) ∧ K < 2 ^ Nat.clog 2 (A + K + 1) := by
  set Lf := Nat.clog 2 (A + K + 1) with hLf
  have hLpow : A + K + 1 ≤ 2 ^ Lf := Nat.le_pow_clog (by norm_num) _
  have hLle : Lf ≤ A + K + 1 := by
    rw [hLf, Nat.clog_le_iff_le_pow (by norm_num)]
    exact (Nat.lt_two_pow_self).le
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120041 9999,
      .constN 120042 0, .constN 110040 1, .addN 110041 120030 120039,
      .addN 110041 110041 120011]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 120041 A₀) 120042 0) 110040 1) 110041 (A + K + 1) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · omega
    · config_simp; rw [hA, hK]; omega
    · config_simp; rw [hA, hK, h1]; omega
    · refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
      config_simp; rw [hA, hK, h1, hAl]
  have hr₁ : ∀ r, BTB r = false → c₁.nreg r = c.nreg r := fun r hr => by
    simp only [BTB, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [n₁]; simp only [upd]; split_ifs <;> first | omega
  -- the loop
  let I : Config → Prop := fun d => WordsBounded W d ∧ ∃ j, d.nreg 120042 = j ∧
    d.nreg 110040 = 2 ^ j ∧ j ≤ Lf ∧ (∀ t, t < j → d.nmem (A₀ + t) = 2 ^ t) ∧
    (∀ r, r ≠ 110040 → r ≠ 110042 → r ≠ 120042 → d.nreg r = c₁.nreg r) ∧
    (∀ a, a < A₀ → d.nmem a = c₁.nmem a) ∧ d.rreg = c₁.rreg ∧ d.rmem = c₁.rmem ∧
    d.output = c₁.output
  have I₁ : I c₁ := ⟨e₁.wb_right, 0, by rw [n₁]; simp [upd], by rw [n₁]; simp [upd],
    Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero _), fun r a b c' => rfl,
    fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, ⟨w₂, j, hj, hx, hjL, htab, hr₂, hm₂, rr₂, rm₂, o₂⟩, hstop, hk₂⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 110040) (b := 110041) (body := tbBody) I
      (fun d => (Lf - d.nreg 120042) * 7) (fun d h => h.1)
      (fun d ⟨hwd, j, hj, hx, hjL, htab, hr, hm, rr, rm, o⟩ ht => by
        have g41 : d.nreg 120041 = A₀ := by rw [hr _ (by decide) (by decide) (by decide), n₁]; config_simp
        have g11 : d.nreg 120011 = 1 := by rw [hr _ (by decide) (by decide) (by decide), hr₁ _ (by decide), h1]
        have gl : d.nreg 110041 = A + K + 1 := by
          rw [hr _ (by decide) (by decide) (by decide), n₁]; config_simp
        rw [hx, gl] at ht
        have hjl : j < Lf := by rw [hLf, Nat.lt_clog_iff_pow_lt (by norm_num)]; exact ht
        obtain ⟨d', k', e', hk', n', m', rr', rm', o'⟩ : ∃ d' k', Exec P W tbBody d d' k' ∧ k' = 4 ∧
            d'.nreg = upd (upd (upd d.nreg 110042 (A₀ + j)) 110040 (2 ^ j + 2 ^ j)) 120042 (j + 1) ∧
            d'.nmem = upd d.nmem (A₀ + j) (2 ^ j) ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
            d'.output = d.output := by
          unfold tbBody
          exec_block
          · rw [g41, hj]; omega
          · config_simp; rw [hx]; omega
          · config_simp; rw [hj, g11]; omega
          · refine ⟨rfl, ?_, ?_, rfl, rfl, rfl⟩
            · config_simp; rw [g41, hj, hx, g11]
            · config_simp; rw [g41, hj, hx]
        refine ⟨d', k', e', ⟨e'.wb_right, j + 1, by rw [n']; config_simp, ?_, by omega,
          fun t ht' => ?_, fun r a b c' => ?_, fun a ha => ?_, by rw [rr', rr], by rw [rm', rm],
          by rw [o', o]⟩, ?_⟩
        · rw [n']; config_simp; rw [pow_succ]; ring
        · rw [m']
          rcases Nat.lt_or_ge t j with h | h
          · rw [upd_other _ _ _ (by omega)]; exact htab t h
          · rw [show t = j by omega, upd_same]
        · rw [n', upd_other _ _ _ c', upd_other _ _ _ a, upd_other _ _ _ b]; exact hr r a b c'
        · rw [m', upd_other _ _ _ (by omega)]; exact hm a ha
        · show (Lf - d'.nreg 120042) * 7 + k' + 2 ≤ (Lf - d.nreg 120042) * 7
          rw [hj, show d'.nreg 120042 = j + 1 by rw [n']; config_simp]
          have : (Lf - (j + 1)) * 7 + 7 = (Lf - j) * 7 := by
            rw [← Nat.succ_mul]; congr 1; omega
          omega)
      I₁
  -- the end of the loop
  have gl : c₂.nreg 110041 = A + K + 1 := by
    rw [hr₂ _ (by decide) (by decide) (by decide), n₁]; config_simp
  rw [hx, gl] at hstop
  have hjL' : j = Lf := by
    have : Lf ≤ j := by rw [hLf, Nat.clog_le_iff_le_pow (by norm_num)]; omega
    omega
  subst hjL'
  have a9 : c₁.nreg 9999 = A₀ := by rw [n₁]; config_simp; exact hAl
  have a42 : c₁.nreg 120042 = 0 := by rw [n₁]; config_simp
  rw [a42, Nat.sub_zero] at hk₂
  have g9 : c₂.nreg 9999 = A₀ := by rw [hr₂ _ (by decide) (by decide) (by decide), a9]
  have e₃ := Exec.addN (P := P) w₂ 9999 9999 120042 (by rw [hj, g9]; omega)
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), by omega, ⟨fun r hr => ?_, fun r _ => ?_, fun a ha => ?_,
    fun a _ => by simp only; rw [rm₂, rm₁], by simp only; rw [o₂, o₁]⟩, ?_, ?_, ?_, fun t ht => ?_,
    by omega, by omega⟩
  · simp only [BTB, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    config_simp
    rw [upd_other _ _ _ (by omega), hr₂ r (by omega) (by omega) (by omega)]
    exact hr₁ r (by simp [BTB]; omega)
  · simp only; rw [rr₂, rr₁]
  · simp only; rw [hm₂ a ha, m₁]
  · config_simp; rw [hj, g9]
  · config_simp; rw [hr₂ _ (by decide) (by decide) (by decide), n₁]; config_simp
  · config_simp; exact hj
  · simp only; exact htab t ht

end

end OracleR

end Chazelle.Core
