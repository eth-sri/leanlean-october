module

public import Chazelle.Core.RestoreFEndS

/-!
# WP-E, the search on the RAM (`FindOK`), part 13: an end of a node chord

`endHead s p`: clear `s`, `s + 5`, `s + 6`; if `g' ≤ p < g' + L`, compare the piece-chain keys of
`(p, 0)` and `(p, h + 1)` (`s + 7 := [0 < param]`), set `s := [g' < p ∨ 0 < param]` (the end is
strictly inside the stretch) and, if so, the host edge `s + 1` and height code `s + 2` (`endMap`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)

variable {E : FEnv} {c₀ c : Config}

/-- The inner part of `endHead` (the end is in `[g', g' + L)`). -/
def endHeadIn (s p : ℕ) : Stmt :=
  .seq (cmpA (s + 7) p 81011 p 81155)
    (.seq (.ifLtN 81131 p (Stmt.block [.constN s 1])
      (.ifLtN 81011 (s + 7) (Stmt.block [.constN s 1]) .skip))
      (.ifLtN 81011 s (endMap s p) .skip))

/-- **The head of an end**: in-stretch bit, host edge and height code. -/
def endHead (s p : ℕ) : Stmt :=
  .seq (Stmt.block [.constN s 0, .constN (s + 5) 0, .constN (s + 6) 0])
    (.ifLtN p 81131 .skip (.ifLtN p 81135 (endHeadIn s p) .skip))

/-- The height code of an end: `h + 1` inside a walk edge, `0` at a vertex. -/
noncomputable def endCode (Cα : Chain) (Q : Polygon) (p h1 : ℕ) : ℕ :=
  if (chainModel Cα).key Q ⟨p, 0⟩ < (chainModel Cα).key Q ⟨p, h1⟩ then h1 else 0

/-- The registers `endHead` writes (besides the key registers). -/
def HeadW (s q : ℕ) : Prop := KeyW q ∨ q = s ∨ q = s + 1 ∨ q = s + 2 ∨ q = s + 5 ∨ q = s + 6 ∨
  q = s + 7 ∨ q = s + 8 ∨ q = s + 9

/-- The cost bound of `endHead`. -/
def ehK : ℕ := 11040

theorem endHead_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s p : ℕ} (hs : 81160 ≤ s ∧ s + 9 < 81190) (hp : p = 81153 ∨ p = 81154)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P (c.nreg ALLOC) c.nmem (c.nreg 81133))
    (hC : ChainDescAt c.nmem (c.nreg 81133) (Qof E.P) H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (h6 : 6 ≤ c.nreg 81131) (hg : c.nreg 81130 < E.M.W.n)
    (hL : c.nreg 81135 - c.nreg 81131 ≤ E.M.W.n)
    (hpe : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg p, c.nreg 81155⟩)
    (hroom : c.nreg ALLOC + ehK ≤ E.W) :
    FRS B E.P E.W c₀ (endHead s p) c ehK (fun c' =>
      BitIs c' s (c.nreg 81131 ≤ c.nreg p ∧ c.nreg p < c.nreg 81135 ∧
        (c.nreg 81131 < c.nreg p ∨ (chainModel Cα).key (Qof E.P) ⟨c.nreg p, 0⟩ <
          (chainModel Cα).key (Qof E.P) ⟨c.nreg p, c.nreg 81155⟩)) ∧
      (c'.nreg s = 1 → c'.nreg (s + 1) = (c.nreg 81130 + (c.nreg p - c.nreg 81131)) % E.M.W.n ∧
        c'.nreg (s + 2) = endCode Cα (Qof E.P) (c.nreg p) (c.nreg 81155) ∧
        BitIs c' (s + 7) ((chainModel Cα).key (Qof E.P) ⟨c.nreg p, 0⟩ <
          (chainModel Cα).key (Qof E.P) ⟨c.nreg p, c.nreg 81155⟩)) ∧
      c'.nreg (s + 5) = 0 ∧ c'.nreg (s + 6) = 0 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q) := by
  obtain ⟨hs1, hs2⟩ := hs
  have hW1 : 1 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  set g' := c.nreg 81131
  set pE := c.nreg p
  set h1 := c.nreg 81155
  set kz := (chainModel Cα).key (Qof E.P) ⟨pE, 0⟩
  set kh := (chainModel Cα).key (Qof E.P) ⟨pE, h1⟩
  have ok0 : okB E.W c.nmem [.constN s 0, .constN (s + 5) 0, .constN (s + 6) 0] c.nreg := by
    simp only [okB, okI]
    exact ⟨⟨Or.inl (Or.inl ⟨by omega, by omega⟩), by omega⟩,
      ⟨Or.inl (Or.inl ⟨by omega, by omega⟩), by omega⟩,
      ⟨Or.inl (Or.inl ⟨by omega, by omega⟩), by omega⟩, trivial⟩
  refine (FRS.seq (K₂ := 11035) (FRS.block hB _ hI ok0) (fun c₁ hI₁ hA₁ h₁ => ?_)).mono
    (by simp [ehK]) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.constN s 0, .constN (s + 5) 0, .constN (s + 6) 0]
      c.nreg q := fun q => by rw [h₁]
  have v0 : c₁.nreg s = 0 := by rw [e₁]; simp [regB, regI, upd]
  have v5 : c₁.nreg (s + 5) = 0 := by rw [e₁]; simp [regB, regI, upd]
  have v6 : c₁.nreg (s + 6) = 0 := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ s → q ≠ s + 5 → q ≠ s + 6 → c₁.nreg q = c.nreg q := fun q a b d => by
    rw [e₁]; simp [regB, regI, upd, a, b, d]
  have m₁ : c₁.nmem = c.nmem := by rw [h₁]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by unfold ALLOC; omega)
    (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  have r := fun q (hq : q < 81160 ∨ 81190 ≤ q) => f₁ q (by omega) (by omega) (by omega)
  have rp : c₁.nreg p = pE := r p (by omega)
  have r31 : c₁.nreg 81131 = g' := r 81131 (by omega)
  have r35 : c₁.nreg 81135 = c.nreg 81135 := r 81135 (by omega)
  have fin0 : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q :=
    fun c' h q a b hq => by
      unfold HeadW at hq
      rw [h q a b (by unfold HeadW; exact hq), f₁ q (by omega) (by omega) (by omega)]
  have no : ¬ (g' ≤ pE ∧ pE < c.nreg 81135 ∧ (g' < pE ∨ kz < kh)) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' =>
      BitIs c' s (g' ≤ pE ∧ pE < c.nreg 81135 ∧ (g' < pE ∨ kz < kh)) ∧
      (c'.nreg s = 1 → c'.nreg (s + 1) = (c.nreg 81130 + (pE - g')) % E.M.W.n ∧
        c'.nreg (s + 2) = endCode Cα (Qof E.P) pE h1 ∧ BitIs c' (s + 7) (kz < kh)) ∧
      c'.nreg (s + 5) = 0 ∧ c'.nreg (s + 6) = 0 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₁ ⟨BitIs.const_zero v0 hn, fun h => by omega, v5, v6,
      fin0 c₁ (fun _ _ _ _ => rfl)⟩
  by_cases a1 : c₁.nreg p < c₁.nreg 81131
  · exact (FRS.ifT a1 (no (fun h => by rw [rp, r31] at a1; omega))).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifF a1 ?_).mono (K := 11035) le_rfl (fun _ h => h)
  by_cases a2 : c₁.nreg p < c₁.nreg 81135
  swap
  · exact (FRS.ifF a2 (no (fun h => by rw [rp, r35] at a2; omega))).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifT a2 ?_).mono (K := 11033) (by omega) (fun _ h => h)
  rw [rp, r31] at a1
  rw [rp, r35] at a2
  -- the comparison
  have hpz : PosOK Cα (Qof E.P) E.P.n ⟨c₁.nreg p, c₁.nreg 81011⟩ := by
    rw [rp, r 81011 (by omega), hI.hin _ (by unfold FFix; omega), hE.k0]
    exact ⟨hpe.1, ⟨le_of_eq rfl, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩,
      fun _ => by show 6 ≤ pE; omega⟩
  have hph : PosOK Cα (Qof E.P) E.P.n ⟨c₁.nreg p, c₁.nreg 81155⟩ := by
    rwa [rp, r 81155 (by omega)]
  have ir : ∀ q, 80000 ≤ q → q < 90000 → InR q := fun q a b => ⟨a, b⟩
  have nk : ∀ q, 81000 ≤ q → q < 82000 → ¬ KeyW q := fun q a b h => by unfold KeyW at h; omega
  refine FRS.seq (K₂ := 21) (cmpA_fs hE hB hI₁ (r := s + 7) ⟨by omega, by omega⟩
    (ir p (by omega) (by omega)) (ir 81011 (by norm_num) (by norm_num)) (ir p (by omega) (by omega))
    (ir 81155 (by norm_num) (by norm_num)) (nk p (by omega) (by omega)) (nk _ (by norm_num)
    (by norm_num)) (nk p (by omega) (by omega)) (nk _ (by norm_num) (by norm_num))
    (by rwa [m₁, r 81133 (by omega), hA₁']) (by rwa [m₁, r 81133 (by omega)])
    hWm hpz hph (by rw [hA₁']; unfold ehK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨b7, _, f₂⟩ => ?_)
  rw [rp, r 81011 (by omega), hI.hin 81011 (by unfold FFix; omega), hE.k0,
    r 81155 (by omega)] at b7
  have g₂ : ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ s + 7 → q ≠ s + 8 →
      c₂.nreg q = c₁.nreg q := f₂
  have w0 : c₂.nreg s = 0 := by
    rw [g₂ s (by omega) (by omega) (nk s (by omega) (by omega)) (by omega) (by omega), v0]
  have k0₂ := k0_of hE hI₂
  have w31 : c₂.nreg 81131 = g' := by
    rw [g₂ _ (by norm_num) (by norm_num) (nk _ (by norm_num) (by norm_num)) (by omega)
      (by omega), r31]
  have w7 : c₂.nreg p = pE := by
    rw [g₂ _ (by omega) (by omega) (nk p (by omega) (by omega)) (by omega) (by omega), rp]
  -- the in-stretch bit
  have step : FRS B E.P E.W c₀ (.ifLtN 81131 p (Stmt.block [.constN s 1])
      (.ifLtN 81011 (s + 7) (Stmt.block [.constN s 1]) .skip)) c₂ 5 (fun c' =>
        BitIs c' s (g' < pE ∨ kz < kh) ∧ ∀ q, q ≠ s → c'.nreg q = c₂.nreg q) := by
    by_cases a3 : c₂.nreg 81131 < c₂.nreg p
    · exact (FRS.ifT a3 ((setR_fs hB hI₂ (r := s) ⟨by omega, by omega⟩ hW1).mono le_rfl
        (fun c' ⟨v, f⟩ => ⟨BitIs.const_one v (Or.inl (by rwa [w31, w7] at a3)), f⟩))).mono
        (by omega) (fun _ h => h)
    refine (FRS.ifF a3 ?_).mono (K := 5) le_rfl (fun _ h => h)
    by_cases a4 : c₂.nreg 81011 < c₂.nreg (s + 7)
    · exact (FRS.ifT a4 ((setR_fs hB hI₂ (r := s) ⟨by omega, by omega⟩ hW1).mono le_rfl
        (fun c' ⟨v, f⟩ => ⟨BitIs.const_one v (Or.inr (b7.2.1 (by have := b7.1; omega))), f⟩))).mono
        (by omega) (fun _ h => h)
    · exact (FRS.ifF a4 (FRS.skip (K := 0) hI₂ ⟨BitIs.const_zero w0 (fun h => by
        rcases h with h | h
        · rw [w31, w7] at a3; exact a3 h
        · have := b7.2.2 h; omega), fun _ _ => rfl⟩)).mono (by omega) (fun _ h => h)
  refine (FRS.seq (K₂ := 12) step (fun c₃ hI₃ hA₃ ⟨b0, f₃⟩ => ?_)).mono (by omega)
    (fun _ h => h)
  have fin : ∀ c' : Config, (∀ q, q ≠ s + 1 → q ≠ s + 2 → q ≠ s + 9 → c'.nreg q = c₃.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ HeadW s q → c'.nreg q = c.nreg q := by
    intro c' h q a b hq
    unfold HeadW at hq
    rw [h q (by omega) (by omega) (by omega), f₃ q (by omega), g₂ q a b (fun hk => hq (Or.inl hk)) (by omega)
      (by omega), f₁ q (by omega) (by omega) (by omega)]
  have s5 : ∀ c' : Config, (∀ q, q ≠ s + 1 → q ≠ s + 2 → q ≠ s + 9 → c'.nreg q = c₃.nreg q) →
      c'.nreg (s + 5) = 0 ∧ c'.nreg (s + 6) = 0 := fun c' h => by
    rw [h _ (by omega) (by omega) (by omega), h _ (by omega) (by omega) (by omega),
      f₃ _ (by omega), f₃ _ (by omega), g₂ _ (by omega) (by omega) (nk _ (by omega) (by omega))
      (by omega) (by omega), g₂ _ (by omega) (by omega) (nk _ (by omega) (by omega)) (by omega)
      (by omega)]
    exact ⟨v5, v6⟩
  have k0₃ := k0_of hE hI₃
  by_cases a5 : c₃.nreg 81011 < c₃.nreg s
  · have b7' : c₃.nreg (s + 7) ≤ 1 := by rw [f₃ _ (by omega)]; exact b7.1
    refine (FRS.ifT a5 ((endMap_fs hE hB hI₃ (s := s) (p := p) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega) (by omega)
      (fun q hq => by unfold FFix at hq; omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) ⟨by omega, by omega, by omega⟩
      (by rw [f₃ _ (by omega), f₃ _ (by omega), w31, w7]; omega)
      (by rwa [f₃ _ (by omega), g₂ _ (by norm_num) (by norm_num) (nk _ (by norm_num) (by norm_num))
        (by omega) (by omega), r 81130 (by omega)])
      (by rw [f₃ _ (by omega), f₃ _ (by omega), w31, w7]; omega) b7').mono le_rfl
      (fun c' ⟨u1, u2, u3, uf⟩ => ?_))).mono (by omega) (fun _ h => h)
    have e30 : c₃.nreg 81130 = c.nreg 81130 := by
      rw [f₃ _ (by omega), g₂ _ (by norm_num) (by norm_num) (nk _ (by norm_num) (by norm_num))
        (by omega) (by omega), r 81130 (by omega)]
    have e7 : c₃.nreg p = pE := by rw [f₃ _ (by omega), w7]
    have e31 : c₃.nreg 81131 = g' := by rw [f₃ _ (by omega), w31]
    have e55 : c₃.nreg 81155 = h1 := by
      rw [f₃ _ (by omega), g₂ _ (by norm_num) (by norm_num) (nk _ (by norm_num) (by norm_num))
        (by omega) (by omega), r 81155 (by omega)]
    have e77 : c₃.nreg (s + 7) = c₂.nreg (s + 7) := f₃ _ (by omega)
    refine ⟨(b0.of_eq (uf s (by omega) (by omega) (by omega))).congr ⟨fun h => ⟨not_lt.1 a1, a2, h⟩,
      fun h => h.2.2⟩, fun _ => ⟨by rw [u1, e30, e7, e31], ?_,
        b7.of_eq (by rw [uf _ (by omega) (by omega) (by omega), e77])⟩, (s5 c' uf).1, (s5 c' uf).2,
      fin c' uf⟩
    unfold endCode
    split_ifs with hk
    · rw [u2 (by rw [e77]; exact b7.2.2 hk), e55]
    · exact u3 (by
        rw [e77]; have h1 := b7.1; by_contra hne; exact hk (b7.2.1 (by omega)))
  · exact (FRS.ifF a5 (FRS.skip (K := 0) hI₃ ⟨(b0.congr ⟨fun h => ⟨not_lt.1 a1, a2, h⟩, fun h => h.2.2⟩),
      fun h => by omega, (s5 c₃ (fun _ _ _ _ => rfl)).1, (s5 c₃ (fun _ _ _ _ => rfl)).2,
      fin c₃ (fun _ _ _ _ => rfl)⟩)).mono (by omega) (fun _ h => h)

/-- **The tail of an end**: if it is strictly inside the stretch and its host edge is in the
edge range, the two tests (`endRun`), then the side bit (`endSd`). -/
def endTail (s σ : ℕ) (sT : Stmt) : Stmt :=
  .ifLtN 81011 s (.seq (.ifLtN (s + 1) 81021 .skip (.ifLtN (s + 1) 81025 (endRun s σ sT) .skip))
    (endSd s)) .skip

/-- The cost bound of `endTail`. -/
def etK (E : FEnv) : ℕ := erK E + 33095

/-- The registers `endTail` writes below the test's registers. -/
def TailW (s q : ℕ) : Prop := RunW s q ∨ SdW s q

theorem FWin.congr' {c c' : Config} (h : FWin E c)
    (hq : ∀ q, 81007 ≤ q → q ≤ 81010 → c'.nreg q = c.nreg q) : FWin E c' := by
  unfold FWin
  rwa [hq 81007 (by norm_num) (by norm_num), hq 81008 (by norm_num) (by norm_num),
    hq 81009 (by norm_num) (by norm_num), hq 81010 (by norm_num) (by norm_num)]

/-- The edge range of the candidates. -/
def InRange (c₀ : Config) (e : ℕ) : Prop := c₀.nreg 81021 ≤ e ∧ e < c₀.nreg 81025

theorem nfregs_of (hE : FGood E c₀) : ∃ reg, NFRegs E.M (Qof E.P) E.N reg := by
  obtain ⟨-, -, -, reg, h1, h2, h3, h4, -⟩ := hE.hNF
  exact ⟨reg, h1, h2, h3, h4⟩

theorem endTail_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {s σ : ℕ}
    (hs : 81160 ≤ s ∧ s + 9 < 81190) (hσ : σ ≤ 1) (h5 : c.nreg (s + 5) = 0)
    (h6 : c.nreg (s + 6) = 0) (hs1 : c.nreg s ≤ 1)
    (hcand : c.nreg s = 1 → InRange c₀ (c.nreg (s + 1)) → ∀ σb, σb ≤ 1 →
      CandOK E ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ (c.nreg 81152) σb)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hroom : c.nreg ALLOC + etK E ≤ E.W) :
    FRS B E.P E.W c₀ (endTail s σ E.sT) c (etK E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ TailW s q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (c.nreg s = 1 → InRange c₀ (c.nreg (s + 1)) →
        ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg (s + 2) = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg (c.nreg (s + 1)) σb →
          c'.nreg 81007 = 1) ∧
      c'.nreg (s + 5) ≤ 1 ∧
      (c'.nreg (s + 5) = 1 → c.nreg s = 1 ∧ InRange c₀ (c.nreg (s + 1)) ∧ c.nreg 81007 = 0) ∧
      (c.nreg s = 1 → InRange c₀ (c.nreg (s + 1)) → c.nreg 81007 = 0 →
        ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg (s + 1) ∧
        ct.nreg 81061 = c.nreg (s + 2) ∧ ct.nreg 81063 = σ ∧
        c'.nreg (s + 3) = ct'.nreg 83012 ∧ c'.nreg (s + 4) = ct'.nreg 83013 ∧
        (c'.nreg (s + 5) = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
          (0 < ct'.nreg 83013 ∨ c₀.nreg 81021 ≤ ct'.nreg 83012))) ∧
        (ct'.nreg 81007 = 1 → c'.nreg 81007 = 1)) ∧
      c'.nreg (s + 6) ≤ 1 ∧
      (c'.nreg (s + 5) = 1 → (0 < c.nreg 81141 ∨ c₀.nreg 81021 ≤ c.nreg 81140) →
        (c'.nreg (s + 6) = 1 ↔ (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ =
          E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ ∨
        sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
          (E.M.key (Qof E.P) ⟨c'.nreg (s + 3), c'.nreg (s + 4)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩))))) := by
  obtain ⟨hs1', hs2⟩ := hs
  have k0 := k0_of hE hI
  have i21 : ∀ c' : Config, FInv E.W c₀ c' → c'.nreg 81021 = c₀.nreg 81021 := fun c' h =>
    h.hin _ (by unfold FFix; omega)
  have i25 : ∀ c' : Config, FInv E.W c₀ c' → c'.nreg 81025 = c₀.nreg 81025 := fun c' h =>
    h.hin _ (by unfold FFix; omega)
  by_cases a0 : c.nreg 81011 < c.nreg s
  swap
  · have z : c.nreg s = 0 := by rw [k0] at a0; omega
    exact (FRS.ifF a0 (FRS.skip (K := 0) hI ⟨hw, fun _ _ _ _ => rfl, id, fun h => by omega,
      by omega, fun h => by omega, fun h => by omega, by omega, fun h => by omega⟩)).mono
      (by unfold etK; omega) (fun _ h => h)
  have o : c.nreg s = 1 := by rw [k0] at a0; omega
  refine (FRS.ifT a0 ?_).mono (K := erK E + 33093) (by unfold etK; omega) (fun _ h => h)
  -- the tests
  have part1 : FRS B E.P E.W c₀ (.ifLtN (s + 1) 81021 .skip
      (.ifLtN (s + 1) 81025 (endRun s σ E.sT) .skip)) c (erK E + 4) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ RunW s q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (InRange c₀ (c.nreg (s + 1)) →
        ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg (s + 2) = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg (c.nreg (s + 1)) σb →
          c'.nreg 81007 = 1) ∧
      c'.nreg (s + 5) ≤ 1 ∧
      (c'.nreg (s + 5) = 1 → InRange c₀ (c.nreg (s + 1)) ∧ c.nreg 81007 = 0) ∧
      (InRange c₀ (c.nreg (s + 1)) → c.nreg 81007 = 0 →
        ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg (s + 1) ∧
        ct.nreg 81061 = c.nreg (s + 2) ∧ ct.nreg 81063 = σ ∧
        c'.nreg (s + 3) = ct'.nreg 83012 ∧ c'.nreg (s + 4) = ct'.nreg 83013 ∧
        (c'.nreg (s + 5) = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
          (0 < ct'.nreg 83013 ∨ c₀.nreg 81021 ≤ ct'.nreg 83012))) ∧
        (ct'.nreg 81007 = 1 → c'.nreg 81007 = 1))) := by
    have out : ¬ InRange c₀ (c.nreg (s + 1)) → FRS B E.P E.W c₀ .skip c 0 (fun c' => FWin E c' ∧
        (∀ q, 81011 ≤ q → q < 83000 → ¬ RunW s q → c'.nreg q = c.nreg q) ∧
        (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
        (InRange c₀ (c.nreg (s + 1)) →
          ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
          c.nreg (s + 2) = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg (c.nreg (s + 1)) σb →
            c'.nreg 81007 = 1) ∧
        c'.nreg (s + 5) ≤ 1 ∧
        (c'.nreg (s + 5) = 1 → InRange c₀ (c.nreg (s + 1)) ∧ c.nreg 81007 = 0) ∧
        (InRange c₀ (c.nreg (s + 1)) → c.nreg 81007 = 0 →
          ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg (s + 1) ∧
          ct.nreg 81061 = c.nreg (s + 2) ∧ ct.nreg 81063 = σ ∧
          c'.nreg (s + 3) = ct'.nreg 83012 ∧ c'.nreg (s + 4) = ct'.nreg 83013 ∧
          (c'.nreg (s + 5) = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
            (0 < ct'.nreg 83013 ∨ c₀.nreg 81021 ≤ ct'.nreg 83012))) ∧
          (ct'.nreg 81007 = 1 → c'.nreg 81007 = 1))) := fun hn =>
      FRS.skip hI ⟨hw, fun _ _ _ _ => rfl, id, fun h => absurd h hn, by omega,
        fun h => by omega, fun h => absurd h hn⟩
    by_cases r1 : c.nreg (s + 1) < c.nreg 81021
    · exact (FRS.ifT r1 (out (fun h => by have := h.1; rw [i21 c hI] at r1; omega))).mono
        (by omega) (fun _ h => h)
    refine (FRS.ifF r1 ?_).mono (K := erK E + 4) le_rfl (fun _ h => h)
    by_cases r2 : c.nreg (s + 1) < c.nreg 81025
    swap
    · exact (FRS.ifF r2 (out (fun h => by have := h.2; rw [i25 c hI] at r2; omega))).mono
        (by omega) (fun _ h => h)
    have hr : InRange c₀ (c.nreg (s + 1)) :=
      ⟨by rw [i21 c hI] at r1; omega, by rwa [i25 c hI] at r2⟩
    refine (FRS.ifT r2 ((endRun_fs hE hB hBT hI hw ⟨by omega, by omega⟩ hσ h5 (hcand o hr)
      (by omega) (by unfold etK at hroom; omega)).mono le_rfl
      (fun c' ⟨w', f', m', g', v', v1', t'⟩ => ⟨w', f', m', fun _ => g', v',
        fun h => ⟨hr, v1' h⟩, fun _ hz => by have := t' hz; rwa [i21 c hI] at this⟩))).mono
      (by omega) (fun _ h => h)
  refine (FRS.seq (K₂ := 33087) part1 (fun c₁ hI₁ hA₁ ⟨w₁, f₁, m₁, g₁, v₁, vv₁, t₁⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have e1 : c₁.nreg (s + 1) = c.nreg (s + 1) := f₁ _ (by omega) (by omega)
    (by unfold RunW VertW; omega)
  have e2 : c₁.nreg (s + 2) = c.nreg (s + 2) := f₁ _ (by omega) (by omega)
    (by unfold RunW VertW; omega)
  have e40 : c₁.nreg 81140 = c.nreg 81140 := f₁ _ (by omega) (by omega)
    (by unfold RunW VertW; omega)
  have e41 : c₁.nreg 81141 = c.nreg 81141 := f₁ _ (by omega) (by omega)
    (by unfold RunW VertW; omega)
  obtain ⟨reg₀, hreg₀⟩ := nfregs_of hE
  have hxE : c₁.nreg (s + 5) = 1 → PosG E.M (Qof E.P) E.P.n ⟨c₁.nreg (s + 1), c₁.nreg (s + 2)⟩ :=
    fun h => by
      obtain ⟨hr, -⟩ := vv₁ h
      have hc := hcand o hr 0 (by omega)
      rw [e1, e2]
      exact posG_of_vlo hE hI hc.1 hc.2.1 (Or.inr (by rw [i21 c hI]; exact hr.1))
  have hxF : c₁.nreg (s + 5) = 1 → PosG E.M (Qof E.P) E.P.n ⟨c₁.nreg (s + 3), c₁.nreg (s + 4)⟩ :=
    fun h => by
      obtain ⟨hr, hz⟩ := vv₁ h
      obtain ⟨ct, ct', hT, -, -, -, h3, h4, hv, -⟩ := t₁ hr hz
      obtain ⟨b10, b11, b12⟩ := hv.1 h
      obtain ⟨-, hex, -⟩ := hT.2.2 reg₀ hreg₀
      obtain ⟨T, -, -, -, hfe, hfp, -⟩ := hex b10 b11
      rw [h3, h4]
      exact posG_of_vlo hE hI₁ hfe hfp (by rwa [i21 c₁ hI₁])
  have hr1 : c₁.nreg ALLOC + 33087 ≤ E.W := by
    have h' : c.nreg ALLOC + (erK E + 33095) ≤ E.W := hroom
    linarith
  refine (endSd_fs hE hB hI₁ ⟨by omega, by omega⟩ v₁ hxE hxF (by rwa [e40, e41])
    hr1).mono le_rfl (fun c' ⟨u6, us, uf⟩ => ?_)
  have back : ∀ q, 81011 ≤ q → q < 83000 → ¬ SdW s q → c'.nreg q = c₁.nreg q := fun q a b h =>
    uf q (by omega) (by omega) h
  have b5 : c'.nreg (s + 5) = c₁.nreg (s + 5) := back _ (by omega) (by omega)
    (by unfold SdW KeyW; omega)
  have b3 : c'.nreg (s + 3) = c₁.nreg (s + 3) := back _ (by omega) (by omega)
    (by unfold SdW KeyW; omega)
  have b4 : c'.nreg (s + 4) = c₁.nreg (s + 4) := back _ (by omega) (by omega)
    (by unfold SdW KeyW; omega)
  have bflag : ∀ q, 81007 ≤ q → q ≤ 81010 → c'.nreg q = c₁.nreg q := fun q a b =>
    uf q (by omega) (by omega) (by unfold SdW KeyW; omega)
  have bf7 : c'.nreg 81007 = c₁.nreg 81007 := bflag _ (by norm_num) (by norm_num)
  refine ⟨w₁.congr' bflag, fun q a b h => ?_, fun h => bf7 ▸ m₁ h,
    fun _ hr reg hr' hch h2 σb hσb hg => bf7 ▸ g₁ hr reg hr' hch h2 σb hσb hg,
    by rwa [b5], fun h => by rw [b5] at h; exact ⟨o, vv₁ h⟩, fun _ hr hz => ?_, u6,
    fun h hj => ?_⟩
  · unfold TailW at h
    rw [back q (by omega) (by omega) (fun h' => h (Or.inr h')),
      f₁ q a b (fun h' => h (Or.inl h'))]
  · obtain ⟨ct, ct', hT, a1, a2, a3, h3, h4, hv, hm⟩ := t₁ hr hz
    refine ⟨ct, ct', hT, a1, a2, a3, by rw [b3, h3], by rw [b4, h4], by rwa [b5],
      fun h => bf7 ▸ hm h⟩
  · rw [b5] at h
    have := us h (by rwa [e40, e41, i21 c₁ hI₁])
    rwa [e1, e2, e40, e41, ← b3, ← b4] at this

end

end Restore

end Chazelle.Core
