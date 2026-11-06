module

public import Chazelle.Core.RestoreFEndP

/-!
# WP-E, the search on the RAM (`FindOK`), part 15: the test condition at a candidate offset

`gEnd s o`: for the candidate host vertex `(81182, 0)` (key `κ`), `o := [if the end `s` is in the
stretch and its first test was valid then (κ ∈ (kE, kF) ↔ s + 6) else true]` — the condition
`GEnd` the test at the end leaves (`81196 … 81199`, `81190 … 81195` scratch).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)

variable {E : FEnv} {c₀ c : Config}

/-- The comparisons of the test condition. -/
def gEndC (s o : ℕ) : Stmt :=
  .seq (cmpM 81190 (s + 1) (s + 2) (s + 3) (s + 4)) (.seq (cmpM 81192 (s + 1) (s + 2) 81182 81011)
    (.seq (cmpM 81194 81182 81011 (s + 3) (s + 4)) (.seq (side3 81196 81190 81192 81194)
      (xnorR o 81196 (s + 6)))))

/-- **The test condition of the end `s` at the candidate vertex `81182`.** -/
def gEnd (s o : ℕ) : Stmt :=
  .seq (Stmt.block [.constN o 1])
    (.ifLtN 81011 s (.ifLtN 81011 (s + 5) (gEndC s o) .skip) .skip)

/-- The registers `gEnd` writes. -/
def GW (o q : ℕ) : Prop := KeyW q ∨ q = o ∨ (81190 ≤ q ∧ q ≤ 81196)

theorem gEnd_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s o : ℕ} (hs : 81160 ≤ s ∧ s + 9 < 81190) (ho : 81197 ≤ o ∧ o < 81200)
    (hs1 : c.nreg s ≤ 1) (hs5 : c.nreg (s + 5) ≤ 1) (hs6 : c.nreg (s + 6) ≤ 1)
    (hxE : c.nreg s = 1 → c.nreg (s + 5) = 1 →
      PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
    (hxF : c.nreg s = 1 → c.nreg (s + 5) = 1 →
      PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
    (hxU : PosG E.M (Qof E.P) E.P.n ⟨c.nreg 81182, 0⟩)
    (hroom : c.nreg ALLOC + 33100 ≤ E.W) :
    FRS B E.P E.W c₀ (gEnd s o) c 33100 (fun c' =>
      BitIs c' o (c.nreg s = 1 → c.nreg (s + 5) = 1 →
        (sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
          (E.M.key (Qof E.P) ⟨c.nreg 81182, 0⟩) ↔ c.nreg (s + 6) = 1)) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c.nreg q) := by
  obtain ⟨hs1', hs2⟩ := hs
  have hW1 : 1 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  refine (FRS.seq (K₂ := 33084) (setR_fs hB hI (r := o) ⟨by omega, by omega⟩ hW1)
    (fun c₁ hI₁ hA₁ ⟨v₁, f₁⟩ => ?_)).mono (by omega) (fun _ h => h)
  have k0 := k0_of hE hI₁
  have g : ∀ q, q ≠ o → c₁.nreg q = c.nreg q := f₁
  set P : Prop := c.nreg s = 1 → c.nreg (s + 5) = 1 →
    (sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
      (E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
      (E.M.key (Qof E.P) ⟨c.nreg 81182, 0⟩) ↔ c.nreg (s + 6) = 1) with hP
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c.nreg q :=
    fun c' h q a b hq => by rw [h q a b hq, g q (fun e => hq (Or.inr (Or.inl e)))]
  have vac : ¬ (c.nreg s = 1 ∧ c.nreg (s + 5) = 1) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' o P ∧
        ∀ q, 80000 ≤ q → q < 90000 → ¬ GW o q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₁ ⟨BitIs.const_one v₁ (fun a b => absurd ⟨a, b⟩ hn), fin c₁ (fun _ _ _ _ => rfl)⟩
  have q0 := g s (by omega)
  have q5 := g (s + 5) (by omega)
  by_cases a1 : c₁.nreg 81011 < c₁.nreg s
  swap
  · exact (FRS.ifF a1 (vac (fun h => by rw [k0, q0] at a1; omega))).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifT a1 ?_).mono (K := 33084) (by omega) (fun _ h => h)
  by_cases a2 : c₁.nreg 81011 < c₁.nreg (s + 5)
  swap
  · exact (FRS.ifF a2 (vac (fun h => by rw [k0, q5] at a2; omega))).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifT a2 ?_).mono (K := 33082) (by omega) (fun _ h => h)
  have h0 : c.nreg s = 1 := by rw [k0, q0] at a1; omega
  have h5 : c.nreg (s + 5) = 1 := by rw [k0, q5] at a2; omega
  -- the comparisons
  have nk : ∀ q, 81000 ≤ q → q < 82000 → ¬ KeyW q := fun q h1 h2 h => by unfold KeyW at h; omega
  have ir : ∀ q, 81000 ≤ q → q < 82000 → InR q := fun q h1 h2 => ⟨by omega, by omega⟩
  have r1 := g (s + 1) (by omega)
  have r2 := g (s + 2) (by omega)
  have r3 := g (s + 3) (by omega)
  have r4 := g (s + 4) (by omega)
  have r82 := g 81182 (by omega)
  have hxE' := hxE h0 h5
  have hxF' := hxF h0 h5
  refine (FRS.seq (K₂ := 22058) (cmpM_fs hE hB hI₁ (r := 81190) ⟨by norm_num, by norm_num⟩
    (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega))
    (ir _ (by omega) (by omega)) (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega)) (by rwa [r1, r2])
    (by rwa [r3, r4]) (by omega))
    (fun c₂ hI₂ hA₂ ⟨b0, b1, f₂⟩ => ?_)).mono (by omega) (fun _ h => h)
  have g₂ : ∀ q, 81100 ≤ q → q < 81190 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    f₂ q (by omega) (by omega) (nk q (by omega) (by omega)) (by omega) (by omega)
  have k0₂ := k0_of hE hI₂
  refine (FRS.seq (K₂ := 11036) (cmpM_fs hE hB hI₂ (r := 81192) ⟨by norm_num, by norm_num⟩
    (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega))
    (ir _ (by omega) (by omega)) (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (by rwa [g₂ (s + 1) (by omega) (by omega), g₂ (s + 2) (by omega) (by omega), r1, r2])
    (by rwa [g₂ 81182 (by omega) (by omega), k0₂, r82]) (by omega))
    (fun c₃ hI₃ hA₃ ⟨b2, b3, f₃⟩ => ?_)).mono (by omega) (fun _ h => h)
  rw [g₂ (s + 1) (by omega) (by omega), g₂ (s + 2) (by omega) (by omega), r1, r2,
    g₂ 81182 (by omega) (by omega), k0₂, r82] at b2
  have g₃ : ∀ q, 81100 ≤ q → q < 81190 → c₃.nreg q = c₁.nreg q := fun q h1 h2 => by
    rw [f₃ q (by omega) (by omega) (nk q (by omega) (by omega)) (by omega) (by omega), g₂ q h1 h2]
  have k0₃ := k0_of hE hI₃
  refine (FRS.seq (K₂ := 14) (cmpM_fs hE hB hI₃ (r := 81194) ⟨by norm_num, by norm_num⟩
    (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega)) (ir _ (by omega) (by omega))
    (ir _ (by omega) (by omega)) (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (nk _ (by omega) (by omega)) (nk _ (by omega) (by omega))
    (by rwa [g₃ 81182 (by omega) (by omega), k0₃, r82])
    (by rwa [g₃ (s + 3) (by omega) (by omega), g₃ (s + 4) (by omega) (by omega), r3, r4])
    (by omega)) (fun c₄ hI₄ hA₄ ⟨b4, b5, f₄⟩ => ?_)).mono (by omega) (fun _ h => h)
  rw [g₃ 81182 (by omega) (by omega), k0₃, r82, g₃ (s + 3) (by omega) (by omega),
    g₃ (s + 4) (by omega) (by omega), r3, r4] at b4
  have p4 : ∀ q, 81190 ≤ q → q ≤ 81193 → c₄.nreg q = c₃.nreg q := fun q h1 h2 =>
    f₄ q (by omega) (by omega) (nk q (by omega) (by omega)) (by omega) (by omega)
  have b0' := b0.of_eq (show c₄.nreg 81190 = c₂.nreg 81190 by
    rw [p4 _ (by norm_num) (by norm_num), f₃ _ (by norm_num) (by norm_num)
      (nk _ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)])
  have b2' := b2.of_eq (p4 81192 (by norm_num) (by norm_num))
  rw [r1, r2, r3, r4] at b0'
  refine (FRS.seq (K₂ := 6) (side3_fs hE hB hI₄ (r := 81196) ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) b0' b2' b4)
    (fun c₅ hI₅ hA₅ ⟨b6, f₅⟩ => ?_)).mono (by omega) (fun _ h => h)
  have e6 : c₅.nreg (s + 6) = c.nreg (s + 6) := by
    rw [f₅ _ (by omega), f₄ _ (by omega) (by omega) (nk _ (by omega) (by omega)) (by omega)
      (by omega), g₃ _ (by omega) (by omega), g _ (by omega)]
  have b7 : BitIs c₅ (s + 6) (c.nreg (s + 6) = 1) := ⟨by rwa [e6], by rw [e6]⟩
  refine (xnorR_fs hE hB hI₅ (r := o) ⟨by omega, by omega⟩ (by omega) (by omega) b6 b7).mono
    le_rfl (fun c' ⟨b8, f₈⟩ => ⟨b8.congr ?_, fun q a b hq => ?_⟩)
  · rw [hP, sideInArc_iff']
    exact ⟨fun h _ _ => h, fun h => h h0 h5⟩
  · have hk : ¬ KeyW q := fun h => hq (Or.inl h)
    have ho' : q ≠ o := fun h => hq (Or.inr (Or.inl h))
    have h9 : ¬ (81190 ≤ q ∧ q ≤ 81196) := fun h => hq (Or.inr (Or.inr h))
    rw [f₈ q ho', f₅ q (by omega), f₄ q a b hk (by omega) (by omega), f₃ q a b hk (by omega)
      (by omega), f₂ q a b hk (by omega) (by omega), g q ho']

/-! ## A candidate offset -/

/-- The host vertex `81182 := (g + u) mod n` and the piece-chain vertex `81183 := g' + u` of the
candidate offset `u` in `81180`. -/
def wPos : Stmt :=
  .seq (Stmt.block [.subN 81188 81017 81130])
    (.seq (.ifLtN 81180 81188 (Stmt.block [.addN 81182 81130 81180])
      (Stmt.block [.subN 81182 81180 81188])) (Stmt.block [.addN 81183 81131 81180]))

/-- `o := ¬ (end s in the stretch ∧ its vertex is the candidate's ∧ it is at a vertex)`. -/
def neEnd (s p o : ℕ) : Stmt :=
  .seq (Stmt.block [.constN o 1])
    (.ifLtN 81011 s (.ifLtN 81183 p .skip (.ifLtN p 81183 .skip
      (.ifLtN 81011 (s + 7) .skip (Stmt.block [.constN o 0])))) .skip)

/-- **The candidate check**: `81181 := [u < L ∧ 81021 ≤ vM ∧ (u is not an end) ∧ GA ∧ GB]`. -/
def wcand : Stmt :=
  .seq wPos (.seq (Stmt.block [.constN 81181 0])
    (.ifLtN 81180 81132 (.ifLtN 81182 81021 .skip
      (.seq (gEnd 81160 81197) (.seq (gEnd 81170 81198) (.seq (neEnd 81160 81153 81184)
        (.seq (neEnd 81170 81154 81185) (.seq (andR 81186 81184 81185)
          (.seq (andR 81187 81197 81198) (andR 81181 81186 81187)))))))) .skip))


theorem wPos_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hg : c.nreg 81130 < E.M.W.n) (hun : c.nreg 81180 < E.M.W.n)
    (hu' : c.nreg 81131 + c.nreg 81180 ≤ E.W) :
    FRS B E.P E.W c₀ wPos c 5 (fun c' =>
      c'.nreg 81182 = (c.nreg 81130 + c.nreg 81180) % E.M.W.n ∧
      c'.nreg 81183 = c.nreg 81131 + c.nreg 81180 ∧
      ∀ q, q ≠ 81182 → q ≠ 81183 → q ≠ 81188 → c'.nreg q = c.nreg q) := by
  set n := E.M.W.n
  have n17 : c.nreg 81017 = n := by rw [hI.hin _ (by unfold FFix; omega), hE.wn]
  have ok1 : okB E.W c.nmem [.subN 81188 81017 81130] c.nreg := by
    simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
  refine FRS.seq (K₂ := 4) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.subN 81188 81017 81130] c.nreg q := fun q => by
    rw [h₁]
  have v88 : c₁.nreg 81188 = n - c.nreg 81130 := by rw [e₁]; simp [regB, regI, upd, n17]
  have f₁ : ∀ q, q ≠ 81188 → c₁.nreg q = c.nreg q := fun q hq => by
    rw [e₁]; simp [regB, regI, upd, hq]
  have w30 := f₁ 81130 (by norm_num)
  have w80 := f₁ 81180 (by norm_num)
  have w31 := f₁ 81131 (by norm_num)
  have hnW : n ≤ E.W := by
    have := hI₁.hw.1 81017; rwa [hI₁.hin _ (by unfold FFix; omega), hE.wn] at this
  have step : FRS B E.P E.W c₀ (.ifLtN 81180 81188 (Stmt.block [.addN 81182 81130 81180])
      (Stmt.block [.subN 81182 81180 81188])) c₁ 3 (fun c' =>
        c'.nreg 81182 = (c.nreg 81130 + c.nreg 81180) % n ∧
        ∀ q, q ≠ 81182 → c'.nreg q = c₁.nreg q) := by
    by_cases hc : c₁.nreg 81180 < c₁.nreg 81188
    · have okc : okB E.W c₁.nmem [.addN 81182 81130 81180] c₁.nreg := by
        simp only [okB, okI]
        refine ⟨⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩, trivial⟩
        rw [w30, w80]; rw [v88, w80] at hc; omega
      refine (FRS.ifT hc (FRS.block hB _ hI₁ okc)).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.addN 81182 81130 81180] c₁.nreg q :=
        fun q => by rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [w30, w80, Nat.mod_eq_of_lt (by rw [v88, w80] at hc; omega)]
    · have okc : okB E.W c₁.nmem [.subN 81182 81180 81188] c₁.nreg := by
        simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
      refine (FRS.ifF hc (FRS.block hB _ hI₁ okc)).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN 81182 81180 81188] c₁.nreg q :=
        fun q => by rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [v88, w80] at hc ⊢
      have e2 : c.nreg 81130 + c.nreg 81180 = (c.nreg 81180 - (n - c.nreg 81130)) + n := by omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  refine FRS.seq (K₂ := 1) step (fun c₂ hI₂ hA₂ ⟨u2, f₂⟩ => ?_)
  have ok3 : okB E.W c₂.nmem [.addN 81183 81131 81180] c₂.nreg := by
    simp only [okB, okI]
    refine ⟨⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩, trivial⟩
    rwa [f₂ _ (by norm_num), f₂ _ (by norm_num), w31, w80]
  refine (FRS.block hB _ hI₂ ok3).mono (by simp) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c₂.nmem [.addN 81183 81131 81180] c₂.nreg q :=
    fun q => by rw [h']
  refine ⟨by rw [e']; simp [regB, regI, upd]; exact u2, ?_, fun q h1 h2 h3 => ?_⟩
  · rw [e']; simp only [regB, regI, upd, ite_true]
    rw [f₂ _ (by norm_num), f₂ _ (by norm_num), w31, w80]
  · rw [e']; simp [regB, regI, upd, h2]; rw [f₂ q h1, f₁ q h3]

theorem neEnd_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s p o : ℕ} (ho : SReg o) (hs1 : c.nreg s ≤ 1) (hos : o ≠ s) (hop : o ≠ p)
    (ho83 : o ≠ 81183) (ho7 : o ≠ s + 7) (_ho11 : o ≠ 81011) :
    FRS B E.P E.W c₀ (neEnd s p o) c 10 (fun c' =>
      BitIs c' o (¬ (c.nreg s = 1 ∧ c.nreg 81183 = c.nreg p ∧ c.nreg (s + 7) = 0)) ∧
      ∀ q, q ≠ o → c'.nreg q = c.nreg q) := by
  have hW1 : 1 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  refine (FRS.seq (K₂ := 9) (setR_fs hB hI ho hW1) (fun c₁ hI₁ _ ⟨v₁, f₁⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have k0 := k0_of hE hI₁
  have q0 := f₁ s (Ne.symm hos)
  have q83 := f₁ 81183 (Ne.symm ho83)
  have qp := f₁ p (Ne.symm hop)
  have q7 := f₁ (s + 7) (Ne.symm ho7)
  have yes : ¬ (c.nreg s = 1 ∧ c.nreg 81183 = c.nreg p ∧ c.nreg (s + 7) = 0) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' o
        (¬ (c.nreg s = 1 ∧ c.nreg 81183 = c.nreg p ∧ c.nreg (s + 7) = 0)) ∧
        ∀ q, q ≠ o → c'.nreg q = c.nreg q) := fun h =>
    FRS.skip hI₁ ⟨BitIs.const_one v₁ h, f₁⟩
  by_cases a1 : c₁.nreg 81011 < c₁.nreg s
  swap
  · exact (FRS.ifF a1 (yes (fun h => by rw [k0, q0] at a1; omega))).mono (by omega) (fun _ h => h)
  refine (FRS.ifT a1 ?_).mono (K := 9) (by omega) (fun _ h => h)
  by_cases a2 : c₁.nreg 81183 < c₁.nreg p
  · exact (FRS.ifT a2 (yes (fun h => by rw [q83, qp] at a2; omega))).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifF a2 ?_).mono (K := 7) le_rfl (fun _ h => h)
  by_cases a3 : c₁.nreg p < c₁.nreg 81183
  · exact (FRS.ifT a3 (yes (fun h => by rw [q83, qp] at a3; omega))).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifF a3 ?_).mono (K := 5) le_rfl (fun _ h => h)
  by_cases a4 : c₁.nreg 81011 < c₁.nreg (s + 7)
  · exact (FRS.ifT a4 (yes (fun h => by rw [k0, q7] at a4; omega))).mono (by omega)
      (fun _ h => h)
  · exact (FRS.ifF a4 ((setR_fs hB hI₁ ho (Nat.zero_le _)).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_zero v (fun h => h ⟨by rw [k0, q0] at a1; omega,
        by rw [q83, qp] at a2 a3; omega, by rw [k0, q7] at a4; omega⟩),
        fun q hq => (f q hq).trans (f₁ q hq)⟩))).mono (by omega) (fun _ h => h)

/-- The test condition of the end `s` at the host vertex `v`, in the configuration `c`. -/
def GAt (E : FEnv) (c : Config) (s v : ℕ) : Prop :=
  c.nreg s = 1 → c.nreg (s + 5) = 1 →
    (sideInArc (E.M.key (Qof E.P) ⟨c.nreg (s + 1), c.nreg (s + 2)⟩)
      (E.M.key (Qof E.P) ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)
      (E.M.key (Qof E.P) ⟨v, 0⟩) ↔ c.nreg (s + 6) = 1)

/-- The candidate condition of the offset `u`. -/
def WCand (E : FEnv) (c₀ c : Config) (u : ℕ) : Prop :=
  u < c.nreg 81132 ∧ c₀.nreg 81021 ≤ (c.nreg 81130 + u) % E.M.W.n ∧
    ¬ (c.nreg 81160 = 1 ∧ c.nreg 81131 + u = c.nreg 81153 ∧ c.nreg 81167 = 0) ∧
    ¬ (c.nreg 81170 = 1 ∧ c.nreg 81131 + u = c.nreg 81154 ∧ c.nreg 81177 = 0) ∧
    GAt E c 81160 ((c.nreg 81130 + u) % E.M.W.n) ∧ GAt E c 81170 ((c.nreg 81130 + u) % E.M.W.n)

/-- The facts of an end that the candidate check needs. -/
def EndOK (E : FEnv) (c : Config) (s : ℕ) : Prop :=
  c.nreg s ≤ 1 ∧ c.nreg (s + 5) ≤ 1 ∧ c.nreg (s + 6) ≤ 1 ∧
    (c.nreg s = 1 → c.nreg (s + 5) = 1 →
      PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 1), c.nreg (s + 2)⟩ ∧
      PosG E.M (Qof E.P) E.P.n ⟨c.nreg (s + 3), c.nreg (s + 4)⟩)

/-- The cost bound of `wcand`. -/
def wcK : ℕ := 66300

/-- The registers `wcand` writes. -/
def WcW (q : ℕ) : Prop := KeyW q ∨ (81181 ≤ q ∧ q ≤ 81199)

theorem wcand_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hA : EndOK E c 81160) (hBo : EndOK E c 81170) (hg : c.nreg 81130 < E.M.W.n)
    (hun : c.nreg 81180 < E.M.W.n) (hu' : c.nreg 81131 + c.nreg 81180 ≤ E.W)
    (hroom : c.nreg ALLOC + wcK ≤ E.W) :
    FRS B E.P E.W c₀ wcand c wcK (fun c' => BitIs c' 81181 (WCand E c₀ c (c.nreg 81180)) ∧
      c'.nreg 81183 = c.nreg 81131 + c.nreg 81180 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c.nreg q) := by
  have nk : ∀ q, 81000 ≤ q → q < 82000 → ¬ KeyW q := fun q h1 h2 h => by unfold KeyW at h; omega
  set u := c.nreg 81180
  set vM := (c.nreg 81130 + u) % E.M.W.n
  refine (FRS.seq (K₂ := 66295) (wPos_fs hE hB hI hg hun hu') (fun c₁ hI₁ hA₁ ⟨w82, w83, f₁⟩ => ?_)).mono
    (by unfold wcK; omega) (fun _ h => h)
  refine (FRS.seq (K₂ := 66294) (setR_fs hB hI₁ (r := 81181) ⟨by norm_num, by norm_num⟩
    (Nat.zero_le _)) (fun c₂ hI₂ hA₂ ⟨v81, f₂⟩ => ?_)).mono (by omega) (fun _ h => h)
  -- the registers of `c` below the candidate's
  have R2 : ∀ q, (q < 81181 ∨ (81189 < q ∧ q ≠ 81181)) → q ≠ 81182 → q ≠ 81183 → q ≠ 81188 →
      c₂.nreg q = c.nreg q := fun q h0 h1 h2 h3 => by
    rw [f₂ q (by omega), f₁ q h1 h2 h3]
  have r80 : c₂.nreg 81180 = u := R2 _ (by omega) (by omega) (by omega) (by omega)
  have r32 : c₂.nreg 81132 = c.nreg 81132 := R2 _ (by omega) (by omega) (by omega) (by omega)
  have r82 : c₂.nreg 81182 = vM := by rw [f₂ _ (by omega), w82]
  have r21 : c₂.nreg 81021 = c₀.nreg 81021 := hI₂.hin _ (by unfold FFix; omega)
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c₂.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c.nreg q := fun c' h q a b hq => by
    unfold WcW at hq
    rw [h q a b (by unfold WcW; exact hq), f₂ q (by omega), f₁ q (by omega) (by omega) (by omega)]
  have c283 : c₂.nreg 81183 = c.nreg 81131 + u := by rw [f₂ _ (by norm_num), w83]
  have no : ¬ WCand E c₀ c u → FRS B E.P E.W c₀ .skip c₂ 0 (fun c' =>
      BitIs c' 81181 (WCand E c₀ c u) ∧ c'.nreg 81183 = c.nreg 81131 + u ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WcW q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₂ ⟨BitIs.const_zero v81 hn, c283, fin c₂ (fun _ _ _ _ => rfl)⟩
  by_cases a1 : c₂.nreg 81180 < c₂.nreg 81132
  swap
  · exact (FRS.ifF a1 (no (fun h => by rw [r80, r32] at a1; exact a1 h.1))).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifT a1 ?_).mono (K := 66294) (by omega) (fun _ h => h)
  by_cases a2 : c₂.nreg 81182 < c₂.nreg 81021
  · exact (FRS.ifT a2 (no (fun h => by rw [r82, r21] at a2; have := h.2.1; omega))).mono
      (by omega) (fun _ h => h)
  refine (FRS.ifF a2 ?_).mono (K := 66292) le_rfl (fun _ h => h)
  have hvl : c₀.nreg 81021 ≤ vM := by rw [r82, r21] at a2; omega
  have hvn : vM < E.M.W.n := Nat.mod_lt _ (by omega)
  -- the ends' facts at `c₂`
  have slot : ∀ s, (s = 81160 ∨ s = 81170) → ∀ j, j ≤ 9 → c₂.nreg (s + j) = c.nreg (s + j) :=
    fun s hs j hj => R2 _ (by omega) (by omega) (by omega) (by omega)
  have eok : ∀ s, (s = 81160 ∨ s = 81170) → EndOK E c s → EndOK E c₂ s := by
    intro s hs ⟨e1, e5, e6, ex⟩
    have k0 := slot s hs 0 (by omega)
    simp only [Nat.add_zero] at k0
    refine ⟨by rwa [k0], by rwa [slot s hs 5 (by omega)],
      by rwa [slot s hs 6 (by omega)], fun h0 h5 => ?_⟩
    rw [k0] at h0; rw [slot s hs 5 (by omega)] at h5
    rw [slot s hs 1 (by omega), slot s hs 2 (by omega), slot s hs 3 (by omega),
      slot s hs 4 (by omega)]
    exact ex h0 h5
  have hxU : PosG E.M (Qof E.P) E.P.n ⟨c₂.nreg 81182, 0⟩ := by
    rw [r82]
    exact posG_of_vlo hE hI hvn ⟨le_of_eq rfl, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩
      (Or.inr (by rwa [hI.hin _ (by unfold FFix; omega)]))
  obtain ⟨a1', a5', a6', ax'⟩ := eok 81160 (Or.inl rfl) hA
  have hAW : c₂.nreg ALLOC + 66292 ≤ E.W := by unfold wcK at hroom; omega
  refine (FRS.seq (K₂ := 33138) (gEnd_fs hE hB hI₂ (s := 81160) (o := 81197) ⟨by norm_num,
    by norm_num⟩ ⟨by norm_num, by norm_num⟩ a1' a5' a6' (fun h0 h5 => (ax' h0 h5).1)
    (fun h0 h5 => (ax' h0 h5).2) hxU (by omega)) (fun c₃ hI₃ hA₃ ⟨g97, f₃⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have R3 : ∀ q, 80000 ≤ q → q < 90000 → ¬ GW 81197 q → c₃.nreg q = c₂.nreg q := f₃
  have eok₃ : EndOK E c₃ 81170 := by
    obtain ⟨b1, b5, b6, bx⟩ := eok 81170 (Or.inr rfl) hBo
    have t : ∀ j, j ≤ 9 → c₃.nreg (81170 + j) = c₂.nreg (81170 + j) := fun j hj =>
      R3 _ (by omega) (by omega) (by unfold GW KeyW; omega)
    have t0 := t 0 (by omega)
    simp only [Nat.add_zero] at t0
    refine ⟨by rwa [t0], by rwa [t 5 (by omega)], by rwa [t 6 (by omega)],
      fun h0 h5 => ?_⟩
    rw [t0] at h0; rw [t 5 (by omega)] at h5
    rw [t 1 (by omega), t 2 (by omega), t 3 (by omega), t 4 (by omega)]
    exact bx h0 h5
  obtain ⟨b1', b5', b6', bx'⟩ := eok₃
  have hxU₃ : PosG E.M (Qof E.P) E.P.n ⟨c₃.nreg 81182, 0⟩ := by
    rwa [R3 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega)]
  refine (FRS.seq (K₂ := 38) (gEnd_fs hE hB hI₃ (s := 81170) (o := 81198) ⟨by norm_num,
    by norm_num⟩ ⟨by norm_num, by norm_num⟩ b1' b5' b6' (fun h0 h5 => (bx' h0 h5).1)
    (fun h0 h5 => (bx' h0 h5).2) hxU₃ (by omega)) (fun c₄ hI₄ hA₄ ⟨g98, f₄⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have R4 : ∀ q, 80000 ≤ q → q < 90000 → ¬ GW 81198 q → c₄.nreg q = c₃.nreg q := f₄
  have s160 : c₄.nreg 81160 ≤ 1 := by
    rwa [R4 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega),
      R3 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega)]
  refine (FRS.seq (K₂ := 28) (neEnd_fs hE hB hI₄ (s := 81160) (p := 81153) (o := 81184)
    ⟨by norm_num, by norm_num⟩ s160 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)) (fun c₅ hI₅ hA₅ ⟨n84, f₅⟩ => ?_)).mono (by omega) (fun _ h => h)
  have s170 : c₅.nreg 81170 ≤ 1 := by
    rwa [f₅ _ (by norm_num), R4 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega)]
  refine (FRS.seq (K₂ := 18) (neEnd_fs hE hB hI₅ (s := 81170) (p := 81154) (o := 81185)
    ⟨by norm_num, by norm_num⟩ s170 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)) (fun c₆ hI₆ hA₆ ⟨n85, f₆⟩ => ?_)).mono (by omega) (fun _ h => h)
  have n84' := n84.of_eq (f₆ 81184 (by norm_num))
  refine (FRS.seq (K₂ := 12) (andR_fs hE hB hI₆ (r := 81186) ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) n84' n85) (fun c₇ hI₇ hA₇ ⟨a86, f₇⟩ => ?_)).mono (by omega)
    (fun _ h => h)
  have g97' : BitIs c₇ 81197 _ := g97.of_eq (by
    rw [f₇ _ (by norm_num), f₆ _ (by norm_num), f₅ _ (by norm_num),
      R4 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega)])
  have g98' : BitIs c₇ 81198 _ := g98.of_eq (by
    rw [f₇ _ (by norm_num), f₆ _ (by norm_num), f₅ _ (by norm_num)])
  refine (FRS.seq (K₂ := 6) (andR_fs hE hB hI₇ (r := 81187) ⟨by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) g97' g98') (fun c₈ hI₈ hA₈ ⟨a87, f₈⟩ => ?_)).mono (by omega)
    (fun _ h => h)
  refine (andR_fs hE hB hI₈ (r := 81181) ⟨by norm_num, by norm_num⟩ (by norm_num)
    (by norm_num) (a86.of_eq (f₈ 81186 (by norm_num))) a87).mono le_rfl
    (fun c₉ ⟨a81, f₉⟩ => ⟨a81.congr ?_, ?_, fun q a b hq => ?_⟩)
  · -- the condition, read back in `c`
    have T3 : ∀ q, (81100 ≤ q ∧ q < 81181) → c₃.nreg q = c.nreg q := fun q hq => by
      rw [R3 q (by omega) (by omega) (by unfold GW KeyW; omega)]
      by_cases h82 : q = 81182
      · omega
      exact R2 q (by omega) (by omega) (by omega) (by omega)
    have T4 : ∀ q, (81100 ≤ q ∧ q < 81181) → c₄.nreg q = c.nreg q := fun q hq => by
      rw [R4 q (by omega) (by omega) (by unfold GW KeyW; omega), T3 q hq]
    have T5 : ∀ q, (81100 ≤ q ∧ q < 81181) → c₅.nreg q = c.nreg q := fun q hq => by
      rw [f₅ q (by omega), T4 q hq]
    have c483 : c₄.nreg 81183 = c.nreg 81131 + u := by
      rw [R4 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega),
        R3 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega), f₂ _ (by norm_num), w83]
    have c583 : c₅.nreg 81183 = c.nreg 81131 + u := by rw [f₅ _ (by norm_num), c483]
    rw [T4 81160 ⟨by norm_num, by norm_num⟩, c483, T4 81153 ⟨by norm_num, by norm_num⟩,
      T4 (81160 + 7) ⟨by norm_num, by norm_num⟩, T5 81170 ⟨by norm_num, by norm_num⟩, c583,
      T5 81154 ⟨by norm_num, by norm_num⟩, T5 (81170 + 7) ⟨by norm_num, by norm_num⟩]
    have S2 : ∀ q, (81100 ≤ q ∧ q < 81181) → c₂.nreg q = c.nreg q := fun q hq =>
      R2 q (by omega) (by omega) (by omega) (by omega)
    have S3 : ∀ q, (81100 ≤ q ∧ q < 81181) → c₃.nreg q = c.nreg q := T3
    rw [S2 81160 ⟨by norm_num, by norm_num⟩, S2 (81160 + 5) ⟨by norm_num, by norm_num⟩,
      S2 (81160 + 1) ⟨by norm_num, by norm_num⟩, S2 (81160 + 2) ⟨by norm_num, by norm_num⟩,
      S2 (81160 + 3) ⟨by norm_num, by norm_num⟩, S2 (81160 + 4) ⟨by norm_num, by norm_num⟩,
      S2 (81160 + 6) ⟨by norm_num, by norm_num⟩, r82,
      S3 81170 ⟨by norm_num, by norm_num⟩, S3 (81170 + 5) ⟨by norm_num, by norm_num⟩,
      S3 (81170 + 1) ⟨by norm_num, by norm_num⟩, S3 (81170 + 2) ⟨by norm_num, by norm_num⟩,
      S3 (81170 + 3) ⟨by norm_num, by norm_num⟩, S3 (81170 + 4) ⟨by norm_num, by norm_num⟩,
      S3 (81170 + 6) ⟨by norm_num, by norm_num⟩,
      R3 81182 (by norm_num) (by norm_num) (by unfold GW KeyW; omega), r82]
    unfold WCand GAt
    rw [r80, r32] at a1
    exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨a1, hvl, h1, h2, h3, h4⟩,
      fun ⟨_, _, h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩
  · rw [f₉ _ (by norm_num), f₈ _ (by norm_num), f₇ _ (by norm_num), f₆ _ (by norm_num),
      f₅ _ (by norm_num), R4 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega),
      R3 _ (by norm_num) (by norm_num) (by unfold GW KeyW; omega), c283]
  · unfold WcW at hq
    have hk : ¬ KeyW q := fun h => hq (Or.inl h)
    have hr : ¬ (81181 ≤ q ∧ q ≤ 81199) := fun h => hq (Or.inr h)
    have gw : ∀ o, 81181 ≤ o → o ≤ 81199 → ¬ GW o q := fun o h1 h2 h => by
      rcases h with h | h | h
      · exact hk h
      · omega
      · omega
    rw [f₉ q (by omega), f₈ q (by omega), f₇ q (by omega), f₆ q (by omega), f₅ q (by omega),
      R4 q a b (gw _ (by norm_num) (by norm_num)), R3 q a b (gw _ (by norm_num) (by norm_num)),
      f₂ q (by omega),
      f₁ q (by omega) (by omega) (by omega)]

end

end Restore

end Chazelle.Core
