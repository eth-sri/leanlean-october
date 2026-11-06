module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFEnd

/-!
# WP-E, the search on the RAM (`FindOK`), part 10: the tests at an end of a node chord

`endTst s σ`: if the host edge `s + 1` of the end is in the edge range `[81021, 81025)`, test the
candidate `(s + 1, s + 2)` (height vertex `81152`) in the direction `σ` (towards the other end)
and then in the other direction; keep the far position (`s + 3`, `s + 4`) of the first test and
`s + 5 := [the flag was clear ∧ valid ∧ hit ∧ (s + 4 ≠ 0 ∨ 81021 ≤ s + 3)]` (`s + 8` keeps the
flag before the tests).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

variable {E : FEnv} {c₀ c : Config}

/-- **The test call with its outcome.** -/
theorem tcall_out (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hcand : c.nreg 81007 = 0 →
      CandOK E ⟨c.nreg 81060, c.nreg 81061⟩ (c.nreg 81062) (c.nreg 81063))
    (hroom : c.nreg ALLOC + tK E ≤ E.W) :
    FRS B E.P E.W c₀ (tcall E.sT) c (tK E) (fun c' => TKeep c c' ∧ FWin E c' ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg 81061 = 0 → GoodAt E reg (c.nreg 81060) (c.nreg 81063) → c'.nreg 81007 = 1) ∧
      (c.nreg 81007 = 0 → TOut E c c')) := by
  refine (tcall_fs hE hB hBT hI hw.1 hcand hroom).mono le_rfl
    (fun c' ⟨hk, hfl, h1, h0⟩ => ?_)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hw.1 with hz | ho
  · have hout := h0 hz
    exact ⟨hk, ⟨hfl, fun hf reg hregs => (hout.2.2 reg hregs).1 hf⟩, fun h => by omega,
      fun reg hregs hch hx1 hg => hout.good hE hregs hch hx1 hg, fun _ => hout⟩
  · obtain ⟨f1, t8, t9, t10⟩ := h1 ho
    refine ⟨hk, ⟨hfl, fun _ reg hregs => ?_⟩, fun _ => f1, fun _ _ _ _ _ => f1,
      fun h => by omega⟩
    rw [t8, t9, t10]; exact hw.2 ho reg hregs

/-- The validity bit of the first test. -/
def endVal (s : ℕ) : Stmt :=
  .ifLtN 81011 (s + 8) .skip (.ifLtN 81011 83010 (.ifLtN 81011 83011
    (.ifLtN 81011 (s + 4) (Stmt.block [.constN (s + 5) 1])
      (.ifLtN (s + 3) 81021 .skip (Stmt.block [.constN (s + 5) 1]))) .skip) .skip)

theorem endVal_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (_hs : SReg s) (hs5 : SReg (s + 5)) (h5 : c.nreg (s + 5) = 0)
    (_hd : ∀ q, FFix q → q ≠ s + 5) (_h8 : s + 8 ≠ s + 5) (_h3 : s + 3 ≠ s + 5) (_h4 : s + 4 ≠ s + 5) :
    FRS B E.P E.W c₀ (endVal s) c 11 (fun c' => c'.nreg (s + 5) ≤ 1 ∧
      (c'.nreg (s + 5) = 1 ↔ (c.nreg (s + 8) = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
        (0 < c.nreg (s + 4) ∨ c.nreg 81021 ≤ c.nreg (s + 3)))) ∧
      ∀ q, q ≠ s + 5 → c'.nreg q = c.nreg q) := by
  have k0 : c.nreg 81011 = 0 := by rw [hI.hin _ (by omega_nf), hE.k0]
  have hW1 : 1 ≤ E.W := by have := hE.hWh; grind [hostWords]
  have no : ¬ (c.nreg (s + 8) = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
      (0 < c.nreg (s + 4) ∨ c.nreg 81021 ≤ c.nreg (s + 3))) →
      FRS B E.P E.W c₀ .skip c 0 (fun c' => c'.nreg (s + 5) ≤ 1 ∧
      (c'.nreg (s + 5) = 1 ↔ (c.nreg (s + 8) = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
        (0 < c.nreg (s + 4) ∨ c.nreg 81021 ≤ c.nreg (s + 3)))) ∧
      ∀ q, q ≠ s + 5 → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI ⟨by omega, ⟨fun h => by omega, fun h => absurd h hn⟩, fun _ _ => rfl⟩
  have yes : (c.nreg (s + 8) = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
      (0 < c.nreg (s + 4) ∨ c.nreg 81021 ≤ c.nreg (s + 3))) →
      FRS B E.P E.W c₀ (Stmt.block [.constN (s + 5) 1]) c 1 (fun c' => c'.nreg (s + 5) ≤ 1 ∧
      (c'.nreg (s + 5) = 1 ↔ (c.nreg (s + 8) = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
        (0 < c.nreg (s + 4) ∨ c.nreg 81021 ≤ c.nreg (s + 3)))) ∧
      ∀ q, q ≠ s + 5 → c'.nreg q = c.nreg q) := fun hy =>
    (setR_fs hB hI hs5 hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨by omega, ⟨fun _ => hy, fun _ => v⟩, f⟩)
  by_cases a1 : c.nreg 81011 < c.nreg (s + 8)
  · exact (FRS.ifT a1 (no (fun h => by omega))).mono (by omega) (fun _ h => h)
  refine (FRS.ifF a1 ?_).mono (K := 11) le_rfl (fun _ h => h)
  by_cases a2 : c.nreg 81011 < c.nreg 83010
  · refine (FRS.ifT a2 ?_).mono (K := 9) (by omega) (fun _ h => h)
    by_cases a3 : c.nreg 81011 < c.nreg 83011
    · refine (FRS.ifT a3 ?_).mono (K := 7) (by omega) (fun _ h => h)
      by_cases a4 : c.nreg 81011 < c.nreg (s + 4)
      · exact (FRS.ifT a4 (yes ⟨by omega, by omega,
          by omega, Or.inl (by omega)⟩)).mono (by omega)
          (fun _ h => h)
      refine (FRS.ifF a4 ?_).mono (K := 5) le_rfl (fun _ h => h)
      by_cases a5 : c.nreg (s + 3) < c.nreg 81021
      · exact (FRS.ifT a5 (no (fun h => by
          omega))).mono (by omega) (fun _ h => h)
      · exact (FRS.ifF a5 (yes ⟨by omega, by omega,
          by omega, Or.inr (by omega)⟩)).mono (by omega) (fun _ h => h)
    · exact (FRS.ifF a3 (no (fun h => by omega))).mono (by omega) (fun _ h => h)
  · exact (FRS.ifF a2 (no (fun h => by omega))).mono (by omega) (fun _ h => h)

/-- The candidate of an end in direction `σ`, after saving the flag in `s + 8`. -/
def endCandL (s σ : ℕ) : List Instr := [.copyN (s + 8) 81007, .copyN 81060 (s + 1),
  .copyN 81061 (s + 2), .copyN 81062 81152, .constN 81063 σ]

/-- The two tests at an end. -/
def endRun (s σ : ℕ) (sT : Stmt) : Stmt :=
  .seq (Stmt.block (endCandL s σ)) (.seq (tcall sT)
    (.seq (Stmt.block [.copyN (s + 3) 83012, .copyN (s + 4) 83013]) (.seq (endVal s)
      (.seq (Stmt.block [.constN 81063 (1 - σ)]) (tcall sT)))))

/-- The cost bound of `endRun`. -/
def erK (E : FEnv) : ℕ := 2 * tK E + 19

/-- The registers an end's tests write below the test's registers. -/
def RunW (s q : ℕ) : Prop := VertW q ∨ q = s + 3 ∨ q = s + 4 ∨ q = s + 5 ∨ q = s + 8

/-- **The two tests at an end.** -/
theorem endRun_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {s σ : ℕ}
    (hs : 81100 ≤ s ∧ s + 9 < 83000) (hσ : σ ≤ 1) (h5 : c.nreg (s + 5) = 0)
    (hcand : ∀ σb, σb ≤ 1 → CandOK E ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ (c.nreg 81152) σb)
    (h52 : 81152 ≠ s + 8) (hroom : c.nreg ALLOC + erK E ≤ E.W) :
    FRS B E.P E.W c₀ (endRun s σ E.sT) c (erK E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ RunW s q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg (s + 2) = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg (c.nreg (s + 1)) σb →
          c'.nreg 81007 = 1) ∧
      c'.nreg (s + 5) ≤ 1 ∧ (c'.nreg (s + 5) = 1 → c.nreg 81007 = 0) ∧
      (c.nreg 81007 = 0 → ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg (s + 1) ∧
        ct.nreg 81061 = c.nreg (s + 2) ∧ ct.nreg 81063 = σ ∧
        c'.nreg (s + 3) = ct'.nreg 83012 ∧ c'.nreg (s + 4) = ct'.nreg 83013 ∧
        (c'.nreg (s + 5) = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
          (0 < ct'.nreg 83013 ∨ c.nreg 81021 ≤ ct'.nreg 83012))) ∧
        (ct'.nreg 81007 = 1 → c'.nreg 81007 = 1))) := by
  obtain ⟨hs1, hs2⟩ := hs
  have hW1 : 1 ≤ E.W := by omega_nf
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have wc : ∀ {c' c'' : Config}, FWin E c' → (∀ q, 81007 ≤ q → q ≤ 81010 → c''.nreg q = c'.nreg q) →
      FWin E c'' := fun hw' h => by
    grind [FWin]
  -- the candidate
  have ok1 : okB E.W c.nmem (endCandL s σ) c.nreg := by
    simp only [endCandL, okB, okI]
    ram_grind
  refine (FRS.seq (K₂ := 2 * tK E + 14) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_)).mono
    (by simp [endCandL, erK]; omega) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem (endCandL s σ) c.nreg q := fun q => by rw [h₁]
  have u8 : c₁.nreg (s + 8) = c.nreg 81007 := by
    rw [e₁]; simp [endCandL, regB, regI, upd, show s + 8 ≠ 81060 by omega,
      show s + 8 ≠ 81061 by omega, show s + 8 ≠ 81062 by omega, show s + 8 ≠ 81063 by omega]
  have u60 : c₁.nreg 81060 = c.nreg (s + 1) := by
    rw [e₁]; simp [endCandL, regB, regI, upd]
  have u61 : c₁.nreg 81061 = c.nreg (s + 2) := by
    rw [e₁]; simp [endCandL, regB, regI, upd, show s + 2 ≠ 81060 by omega]
  have u62 : c₁.nreg 81062 = c.nreg 81152 := by
    rw [e₁]; simp [endCandL, regB, regI, upd, show s ≠ 81144 by omega]
  have u63 : c₁.nreg 81063 = σ := by rw [e₁]; simp [endCandL, regB, regI, upd]
  have f₁ : ∀ q, q ≠ s + 8 → ¬ VertW q → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    unfold VertW at h2
    rw [e₁]; simp [endCandL, regB, regI, upd, h1, show q ≠ 81060 by omega,
      show q ≠ 81061 by omega, show q ≠ 81062 by omega, show q ≠ 81063 by omega]
  have fl₁ : ∀ q, 81007 ≤ q → q ≤ 81010 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    f₁ q (by omega) (by omega_nf)
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by omega_nf)
    (by omega_nf)
  -- the first test
  refine (FRS.seq (K₂ := tK E + 14) (tcall_out hE hB hBT hI₁ (wc hw fl₁)
    (fun _ => by grind) (by grind [erK]))
    (fun c₂ hI₂ hA₂ ⟨k₂, w₂, m₂, g₂, o₂⟩ => ?_)).mono (by omega) (fun _ h => h)
  have ok3 : okB E.W c₂.nmem [.copyN (s + 3) 83012, .copyN (s + 4) 83013] c₂.nreg := by
    simp only [okB, okI]
    ram_grind
  refine (FRS.seq (K₂ := tK E + 12) (FRS.block hB _ hI₂ ok3) (fun c₃ hI₃ hA₃ h₃ => ?_)).mono
    (by grind) (fun _ h => h)
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.copyN (s + 3) 83012, .copyN (s + 4) 83013]
      c₂.nreg q := fun q => by rw [h₃]
  have u3 : c₃.nreg (s + 3) = c₂.nreg 83012 := by
    rw [e₃]; simp [regB, regI, upd]
  have u4 : c₃.nreg (s + 4) = c₂.nreg 83013 := by
    rw [e₃]; simp [regB, regI, upd, show (83013 : ℕ) ≠ s + 3 by omega]
  have f₃ : ∀ q, q ≠ s + 3 → q ≠ s + 4 → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
    rw [e₃]; simp [regB, regI, upd, h1, h2]
  have h5₃ : c₃.nreg (s + 5) = 0 := by
    rw [f₃ _ (by omega) (by omega), k₂ _ (by omega) (by omega), f₁ _ (by omega)
      (by omega_nf), h5]
  refine (FRS.seq (K₂ := tK E + 1) (endVal_fs hE hB hI₃ (s := s) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ h5₃ (fun q hq => by grind [FFix]) (by omega) (by omega)
    (by omega)) (fun c₄ hI₄ hA₄ ⟨v₄, b₄, f₄⟩ => ?_)).mono (by omega) (fun _ h => h)
  refine (FRS.seq (K₂ := tK E) (setR_fs hB hI₄ (r := 81063) ⟨by norm_num, by norm_num⟩
    (by omega)) (fun c₅ hI₅ hA₅ ⟨u₅, f₅⟩ => ?_)).mono (by omega) (fun _ h => h)
  have g5 : ∀ q, q ≠ 81063 → q ≠ s + 5 → q ≠ s + 3 → q ≠ s + 4 →
      c₅.nreg q = c₂.nreg q := fun q h1 h2 h3 h4 => by
    rw [f₅ q h1, f₄ q h2, f₃ q h3 h4]
  have hw₅ : FWin E c₅ := wc w₂ (fun q h1 h2 => g5 q (by omega) (by omega) (by omega) (by omega))
  have hcand₂ : c₅.nreg 81007 = 0 → CandOK E ⟨c₅.nreg 81060, c₅.nreg 81061⟩ (c₅.nreg 81062)
      (c₅.nreg 81063) := fun _ => by
    rw [u₅, g5 81060 (by norm_num) (by omega) (by omega) (by omega),
      g5 81061 (by norm_num) (by omega) (by omega) (by omega),
      g5 81062 (by norm_num) (by omega) (by omega) (by omega),
      k₂ _ (by norm_num) (by norm_num), k₂ _ (by norm_num) (by norm_num),
      k₂ _ (by norm_num) (by norm_num), u60, u61, u62]
    exact hcand _ (by omega)
  have hroom₅ : c₅.nreg ALLOC + tK E ≤ E.W := by
        
    simp only [endCandL, List.length_cons, List.length_nil] at *
    unfold erK at hroom; omega
  refine (tcall_out hE hB hBT hI₅ hw₅ hcand₂ hroom₅).mono le_rfl
    (fun c₆ ⟨k₆, w₆, m₆, g₆, o₆⟩ => ?_)
  have back : ∀ q, 81011 ≤ q → q < 83000 → ¬ RunW s q → c₆.nreg q = c.nreg q := by
    intro q h1 h2 hq
    unfold RunW VertW at hq
    rw [k₆ q h1 h2, g5 q (by omega) (by omega) (by omega) (by omega), k₂ q h1 h2,
      f₁ q (by omega) (by omega_nf)]
  have m26 : c₂.nreg 81007 = 1 → c₆.nreg 81007 = 1 := fun h => m₆ (by
    rw [g5 _ (by norm_num) (by omega) (by omega) (by omega)]; exact h)
  have s5 : c₆.nreg (s + 5) = c₄.nreg (s + 5) := by
    rw [k₆ _ (by omega) (by omega), f₅ _ (by omega)]
  have s3 : c₆.nreg (s + 3) = c₂.nreg 83012 := by
    rw [k₆ _ (by omega) (by omega), f₅ _ (by omega), f₄ _ (by omega), u3]
  have s4 : c₆.nreg (s + 4) = c₂.nreg 83013 := by
    rw [k₆ _ (by omega) (by omega), f₅ _ (by omega), f₄ _ (by omega), u4]
  have i8 : c₃.nreg (s + 8) = c.nreg 81007 := by
    rw [f₃ _ (by omega) (by omega), k₂ _ (by omega) (by omega), u8]
  have i21 : c₃.nreg 81021 = c.nreg 81021 := by
    rw [hI₃.hin _ (by omega_nf), hI.hin _ (by omega_nf)]
  refine ⟨w₆, back, fun h => m26 (m₂ (by grind)),
    fun reg hregs hch hc2 σb hσb hg => ?_, by omega, fun h => ?_, fun hz => ?_⟩
  · rcases (show σb = σ ∨ σb = 1 - σ by omega) with rfl | rfl
    · grind
    · refine g₆ reg hregs hch ?_ ?_
      · rw [g5 81061 (by norm_num) (by omega) (by omega) (by omega),
          k₂ _ (by norm_num) (by norm_num), u61]; exact hc2
      · rw [u₅, g5 81060 (by norm_num) (by omega) (by omega) (by omega), k₂ _ (by norm_num) (by norm_num), u60]; exact hg
  · grind
  · have hout := o₂ (by grind)
    obtain ⟨t0, t1, -⟩ := hout
    refine ⟨c₁, c₂, o₂ (by grind), u60, u61, u63, s3,
      s4, ?_, m26⟩
    rw [s5, b₄, i8, f₃ _ (by omega) (by omega), f₃ _ (by omega) (by omega), u3, u4, i21]
    omega

end

end Restore

end Chazelle.Core
