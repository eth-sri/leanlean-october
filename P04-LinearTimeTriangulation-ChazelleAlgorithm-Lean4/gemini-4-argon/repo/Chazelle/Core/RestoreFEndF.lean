module

public import Chazelle.Core.RestoreFEndP
public import Chazelle.Core.RestoreFWit
public import Chazelle.Core.RestoreFSide

/-!
# WP-E, the search on the RAM (`FindOK`), part 19: a whole end of a node chord

`endFull s p σ = endHead s p; endTail s σ`, with its result `EndRes` read in the start
configuration `c` (end edge register `p`, height code `81155`, stretch registers `81130 …`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)

variable {E : FEnv} {c₀ c : Config}

/-- **A whole end.** -/
def endFull (s p σ : ℕ) (sT : Stmt) : Stmt := .seq (endHead s p) (endTail s σ sT)

/-- The host edge of the end in `p`. -/
def eMof (E : FEnv) (c : Config) (p : ℕ) : ℕ :=
  (c.nreg 81130 + (c.nreg p - c.nreg 81131)) % E.M.W.n

/-- The registers an end writes. -/
def EndW (s q : ℕ) : Prop := KeyW q ∨ VertW q ∨ (s ≤ q ∧ q ≤ s + 9) ∨ (81190 ≤ q ∧ q ≤ 81195)

/-- **The result of an end**, read in its start configuration `c`. -/
def EndRes (E : FEnv) (c₀ : Config) (Cα : Chain) (s p σ : ℕ) (c c' : Config) : Prop :=
  let pE := c.nreg p
  let h1 := c.nreg 81155
  let pz : Prop := (chainModel Cα).key (Qof E.P) ⟨pE, 0⟩ < (chainModel Cα).key (Qof E.P) ⟨pE, h1⟩
  let eM := eMof E c p
  let code := endCode Cα (Qof E.P) pE h1
  BitIs c' s (c.nreg 81131 ≤ pE ∧ pE < c.nreg 81135 ∧ (c.nreg 81131 < pE ∨ pz)) ∧
  (c'.nreg s = 1 → c'.nreg (s + 1) = eM ∧ c'.nreg (s + 2) = code ∧ BitIs c' (s + 7) pz) ∧
  (c'.nreg s = 1 → InRange c₀ eM →
    ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
      code = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg eM σb → c'.nreg 81007 = 1) ∧
  (c'.nreg s = 1 → InRange c₀ eM → c.nreg 81007 = 0 →
    ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = eM ∧ ct.nreg 81061 = code ∧
      ct.nreg 81063 = σ ∧ c'.nreg (s + 3) = ct'.nreg 83012 ∧ c'.nreg (s + 4) = ct'.nreg 83013 ∧
      (c'.nreg (s + 5) = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
        (0 < ct'.nreg 83013 ∨ c₀.nreg 81021 ≤ ct'.nreg 83012))) ∧
      (ct'.nreg 81007 = 1 → c'.nreg 81007 = 1)) ∧
  (c'.nreg (s + 5) = 1 → c'.nreg s = 1 ∧ InRange c₀ eM ∧ c.nreg 81007 = 0) ∧
  (c'.nreg (s + 5) = 1 → (0 < c.nreg 81141 ∨ c₀.nreg 81021 ≤ c.nreg 81140) →
    (c'.nreg (s + 6) = 1 ↔ (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩ =
        E.M.key (Qof E.P) ⟨eM, code⟩ ∨
      sideInArc (E.M.key (Qof E.P) ⟨eM, code⟩)
        (E.M.key (Qof E.P) ⟨c'.nreg (s + 3), c'.nreg (s + 4)⟩)
        (E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩)))) ∧
  EndOK E c' s

/-- The cost bound of `endFull`. -/
def efK (E : FEnv) : ℕ := ehK + etK E

theorem endFull_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {s p σ : ℕ}
    (hs : 81160 ≤ s ∧ s + 9 < 81190) (hp : p = 81153 ∨ p = 81154) (hσ : σ ≤ 1)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c.nreg 81133))
    (hC : ChainDescAt c₀.nmem (c.nreg 81133) (Qof E.P) H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (h6 : 6 ≤ c.nreg 81131) (hg : c.nreg 81130 < E.M.W.n)
    (hL : c.nreg 81135 - c.nreg 81131 ≤ E.M.W.n)
    (hpe : PosOK Cα (Qof E.P) E.P.n ⟨c.nreg p, c.nreg 81155⟩)
    (hcand : c.nreg 81131 ≤ c.nreg p → c.nreg p < c.nreg 81135 →
      InRange c₀ (eMof E c p) → ∀ σb, σb ≤ 1 →
        CandOK E ⟨eMof E c p, endCode Cα (Qof E.P) (c.nreg p) (c.nreg 81155)⟩ (c.nreg 81152) σb)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    (hroom : c.nreg ALLOC + efK E ≤ E.W) :
    FRS B E.P E.W c₀ (endFull s p σ E.sT) c (efK E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ EndW s q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧ EndRes E c₀ Cα s p σ c c') := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hC', hwf'⟩ := chain_keep hwf hC (fun a ha => hI.hm a ha) hI.hA
  refine (FRS.seq (K₂ := etK E) (endHead_fs hE hB hI (s := s) (p := p) ⟨hs1, hs2⟩ hp hwf' hC' hWm
    h6 hg hL hpe (by unfold efK at hroom; omega)) (fun c₁ hI₁ hA₁ ⟨b0, bp, z5, z6, f₁⟩ => ?_)).mono
    (by unfold efK; omega) (fun _ h => h)
  have nk : ∀ q, 81000 ≤ q → q < 82000 → ¬ KeyW q := fun q h1 h2 h => by unfold KeyW at h; omega
  have F1' : ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → ¬ (s ≤ q ∧ q ≤ s + 9) →
      c₁.nreg q = c.nreg q :=
    fun q h1 h2 hk h3 => f₁ q h1 h2 (by
      unfold HeadW; rintro (h | h | h | h | h | h | h | h | h | h)
      · exact hk h
      all_goals omega)
  have F1 : ∀ q, 81000 ≤ q → q < 82000 → ¬ (s ≤ q ∧ q ≤ s + 9) → c₁.nreg q = c.nreg q :=
    fun q h1 h2 h3 => F1' q (by omega) (by omega) (nk q h1 h2) h3
  have hw₁ : FWin E c₁ := hw.congr' (fun q h1 h2 => F1 q (by omega) (by omega) (by omega))
  have j40 := F1 81140 (by norm_num) (by norm_num) (by omega)
  have j41 := F1 81141 (by norm_num) (by norm_num) (by omega)
  have j52 := F1 81152 (by norm_num) (by norm_num) (by omega)
  have hb0 := b0.1
  have hcand₁ : c₁.nreg s = 1 → InRange c₀ (c₁.nreg (s + 1)) → ∀ σb, σb ≤ 1 →
      CandOK E ⟨c₁.nreg (s + 1), c₁.nreg (s + 2)⟩ (c₁.nreg 81152) σb := by
    intro h1 hr σb hσb
    obtain ⟨u1, u2, -⟩ := bp h1
    obtain ⟨a, b, -⟩ := b0.2.1 h1
    rw [u1, u2, j52]; rw [u1] at hr
    exact hcand a b hr σb hσb
  refine (endTail_fs hE hB hBT hI₁ hw₁ (s := s) (σ := σ) ⟨hs1, hs2⟩ hσ z5 z6 hb0 hcand₁
    (by rwa [j40, j41]) (by unfold efK at hroom; omega)).mono le_rfl
    (fun c₂ ⟨w₂, f₂, m₂, g₂, v5, v5', t₂, v6, s6⟩ => ?_)
  -- reading back
  have F2 : ∀ q, 81011 ≤ q → q < 83000 → ¬ TailW s q → c₂.nreg q = c₁.nreg q := f₂
  have tw : ∀ j, j ≤ 9 → j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 8 → ¬ TailW s (s + j) :=
    fun j hj a b d e f h => by
      unfold TailW RunW SdW VertW KeyW at h; omega
  have t0 : ¬ TailW s s := by unfold TailW RunW SdW VertW KeyW; omega
  have k0 := F2 s (by omega) (by omega) t0
  have k1 := F2 (s + 1) (by omega) (by omega) (tw 1 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega))
  have k2 := F2 (s + 2) (by omega) (by omega) (tw 2 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega))
  have k7 := F2 (s + 7) (by omega) (by omega) (tw 7 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega))
  have flag₁ : c₁.nreg 81007 = c.nreg 81007 := F1 _ (by norm_num) (by norm_num) (by omega)
  obtain ⟨reg₀, hreg₀⟩ := nfregs_of hE
  refine ⟨w₂, fun q h1 h2 hq => ?_, fun h => m₂ (by rwa [flag₁]), ?_⟩
  · have hk : ¬ KeyW q := fun h => hq (Or.inl h)
    have hv : ¬ VertW q := fun h => hq (Or.inr (Or.inl h))
    have hs' : ¬ (s ≤ q ∧ q ≤ s + 9) := fun h => hq (Or.inr (Or.inr (Or.inl h)))
    have h9 : ¬ (81190 ≤ q ∧ q ≤ 81195) := fun h => hq (Or.inr (Or.inr (Or.inr h)))
    have ht : ¬ TailW s q := by
      unfold TailW RunW SdW
      rintro ((h | h | h | h | h) | (h | h | h))
      · exact hv h
      · omega
      · omega
      · omega
      · omega
      · exact hk h
      · omega
      · exact h9 h
    rw [F2 q h1 h2 ht, F1' q (by omega) (by omega) hk hs']
  -- the result
  refine ⟨b0.of_eq k0, fun h1 => ?_, fun h1 hr => ?_, fun h1 hr hz => ?_, fun h5 => ?_,
    fun h5 hj => ?_, ?_⟩
  · rw [k0] at h1
    obtain ⟨u1, u2, u7⟩ := bp h1
    exact ⟨by rw [k1, u1]; rfl, by rw [k2, u2], u7.of_eq k7⟩
  · rw [k0] at h1
    obtain ⟨u1, u2, -⟩ := bp h1
    intro reg hr' hch hc0 σb hσb hg
    exact g₂ h1 (by rwa [u1]) reg hr' hch (by rwa [u2]) σb hσb
      (by rwa [u1])
  · rw [k0] at h1
    obtain ⟨u1, u2, -⟩ := bp h1
    obtain ⟨ct, ct', hT, a1, a2, a3, h3, h4, hv, hm⟩ := t₂ h1 (by rwa [u1])
      (by rwa [flag₁])
    exact ⟨ct, ct', hT, by rw [a1, u1]; rfl, by rw [a2, u2], a3, h3, h4, hv, hm⟩
  · obtain ⟨a, b, d⟩ := v5' h5
    obtain ⟨u1, -, -⟩ := bp a
    exact ⟨by rwa [k0], by rwa [u1] at b, by rwa [← flag₁]⟩
  · obtain ⟨a, -, -⟩ := v5' h5
    obtain ⟨u1, u2, -⟩ := bp a
    have := s6 h5 (by rwa [j40, j41])
    rwa [j40, j41, u1, u2] at this
  · -- `EndOK`
    refine ⟨by rwa [k0], v5, v6, fun h1 h5 => ?_⟩
    obtain ⟨a, hr, hz⟩ := v5' h5
    obtain ⟨u1, u2, -⟩ := bp a
    have hc := hcand₁ a hr 0 (by omega)
    obtain ⟨ct, ct', hT, -, -, -, h3, h4, hv, -⟩ := t₂ a hr hz
    obtain ⟨b10, b11, b12⟩ := hv.1 h5
    obtain ⟨-, hex, -⟩ := hT.2.2 reg₀ hreg₀
    obtain ⟨T, -, -, -, hfe, hfp, -⟩ := hex b10 b11
    refine ⟨?_, ?_⟩
    · rw [k1, k2]
      exact posG_of_vlo hE hI₁ hc.1 hc.2.1 (Or.inr (by
        rw [hI₁.hin _ (by unfold FFix; omega)]; exact hr.1))
    · rw [h3, h4]
      exact posG_of_vlo hE hI₁ hfe hfp (by rwa [hI₁.hin _ (by unfold FFix; omega)])

end

end Restore

end Chazelle.Core
