module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFWit

/-!
# WP-E, the search on the RAM (`FindOK`), part 16: choosing the witness offset

`wsel`: try the offsets `u = 1`, then `p_A - g' + 1` (if the left end is in the stretch), then
`p_B - g' + 1` (if the right end is), stopping at the first that passes `wcand` (`81181`, the
offset in `81180`, its piece-chain vertex in `81183`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)

variable {E : FEnv} {c₀ c : Config}

/-- Try the offset `p - g' + 1` of the end `s` (edge register `p`) if it is in the stretch. -/
def wTry (s p : ℕ) : Stmt :=
  .ifLtN 81011 81181 .skip (.ifLtN 81011 s
    (.seq (Stmt.block [.subN 81180 p 81131, .addN 81180 81180 81012]) wcand) .skip)

/-- **The witness selection.** -/
def wsel : Stmt :=
  .seq (Stmt.block [.constN 81180 1]) (.seq wcand (.seq (wTry 81160 81153) (wTry 81170 81154)))

/-- The registers the witness selection writes. -/
def WsW (q : ℕ) : Prop := KeyW q ∨ (81180 ≤ q ∧ q ≤ 81199)

/-- The candidate condition depends only on the registers it reads. -/
theorem WCand.congr {c' : Config} (h : ∀ q, ¬ WsW q → 81100 ≤ q → q < 81200 → c'.nreg q = c.nreg q)
    {u : ℕ} : WCand E c₀ c' u ↔ WCand E c₀ c u := by
  have e : ∀ q, (81130 ≤ q ∧ q < 81180) → c'.nreg q = c.nreg q := fun q hq =>
    h q (by omega_nf) (by omega) (by omega)
  unfold WCand GAt
  ram_grind


/-- The invariant of the witness selection, relative to the start `c`. -/
def WsInv (E : FEnv) (c₀ c c' : Config) : Prop :=
  c'.nreg 81181 ≤ 1 ∧ (c'.nreg 81181 = 1 → WCand E c₀ c (c'.nreg 81180) ∧
    c'.nreg 81183 = c.nreg 81131 + c'.nreg 81180) ∧
  (∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c'.nreg q = c.nreg q) ∧ 1 ≤ c'.nreg 81180

theorem EndOK.congr {c c' : Config} {s : ℕ} (h : EndOK E c s)
    (he : ∀ j, j ≤ 6 → c'.nreg (s + j) = c.nreg (s + j)) : EndOK E c' s := by
  obtain ⟨e1, e5, e6, ex⟩ := h
  have e0 := he 0 (by omega)
  simp only [Nat.add_zero] at e0
  refine ⟨by omega, by ram_simp,
    by ram_simp, fun h0 h5 => ?_⟩
  ram_grind

section
variable (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) {c' : Config} (hI : FInv E.W c₀ c') (hA : EndOK E c 81160) (hBo : EndOK E c 81170)
include hE hB hI hA hBo
theorem wcand_inv
    (hfr : ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c'.nreg q = c.nreg q)
    (hg : c.nreg 81130 < E.M.W.n) (hun : c'.nreg 81180 < E.M.W.n)
    (hu' : c.nreg 81131 + c'.nreg 81180 ≤ E.W) (hu1 : 1 ≤ c'.nreg 81180)
    (hroom : c'.nreg ALLOC + wcK ≤ E.W) :
    FRS B E.P E.W c₀ wcand c' wcK (fun c'' => WsInv E c₀ c c'' ∧
      (WCand E c₀ c (c'.nreg 81180) → c''.nreg 81181 = 1) ∧ c''.nreg 81180 = c'.nreg 81180) := by
  have fr : ∀ q, ¬ WsW q → 81100 ≤ q → q < 81200 → c'.nreg q = c.nreg q := fun q h a b =>
    hfr q (by omega) (by omega) h
  have sl : ∀ s, (s = 81160 ∨ s = 81170) → ∀ j, j ≤ 6 → c'.nreg (s + j) = c.nreg (s + j) :=
    fun s hs j hj => fr _ (by omega_nf) (by omega) (by omega)
  refine (wcand_fs hE hB hI ((hA.congr (sl 81160 (Or.inl rfl)))) (hBo.congr (sl 81170 (Or.inr rfl)))
    (by ram_simp) hun
    (by grind [WsW, KeyW])
    hroom).mono le_rfl (fun c'' ⟨b, e83, f⟩ => ?_)
  have wc : WCand E c₀ c' (c'.nreg 81180) ↔ WCand E c₀ c (c'.nreg 81180) := WCand.congr fr
  ram_grind

/-- **One try.** -/
theorem wTry_fs
    (hv : WsInv E c₀ c c') {s p : ℕ} (hsp : (s = 81160 ∧ p = 81153) ∨ (s = 81170 ∧ p = 81154))
    (hg : c.nreg 81130 < E.M.W.n) (hL : c.nreg 81132 < E.M.W.n)
    (hgL : c.nreg 81131 + c.nreg 81132 ≤ E.W)
    (hp : c.nreg s = 1 → c.nreg 81131 ≤ c.nreg p ∧ c.nreg p - c.nreg 81131 < c.nreg 81132)
    (hroom : c'.nreg ALLOC + wcK + 6 ≤ E.W) :
    FRS B E.P E.W c₀ (wTry s p) c' (wcK + 6) (fun c'' => WsInv E c₀ c c'' ∧
      (c'.nreg 81181 = 1 → c''.nreg 81181 = 1) ∧
      (c.nreg s = 1 → WCand E c₀ c (c.nreg p - c.nreg 81131 + 1) → c''.nreg 81181 = 1)) := by
  
  have k0 := k0_of hE hI
  obtain ⟨v1, v2, v3, v4⟩ := hv
  have fr : ∀ q, ¬ WsW q → 81100 ≤ q → q < 81200 → c'.nreg q = c.nreg q := fun q h a b =>
    v3 q (by omega) (by omega) h
  have es : c'.nreg s = c.nreg s := fr s (by omega_nf) (by omega) (by omega)
  have ep : c'.nreg p = c.nreg p := fr p (by omega_nf) (by omega) (by omega)
  have e31 : c'.nreg 81131 = c.nreg 81131 := fr 81131 (by omega_nf) (by norm_num)
    (by norm_num)
  have hs1 : c.nreg s ≤ 1 := by rcases hsp with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hA.1, hBo.1]
  by_cases a1 : c'.nreg 81011 < c'.nreg 81181
  · have h1 : c'.nreg 81181 = 1 := by omega
    exact (FRS.ifT a1 (FRS.skip (K := 0) hI ⟨⟨v1, v2, v3, v4⟩, id, fun _ _ => h1⟩)).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifF a1 ?_).mono (K := wcK + 6) le_rfl (fun _ h => h)
  
  by_cases a2 : c'.nreg 81011 < c'.nreg s
  swap
  · exact (FRS.ifF a2 (FRS.skip (K := 0) hI ⟨⟨v1, v2, v3, v4⟩, fun h => by omega,
      fun h => by omega⟩)).mono (by omega) (fun _ h => h)
  refine (FRS.ifT a2 ?_).mono (K := wcK + 4) (by omega) (fun _ h => h)
  have hs : c.nreg s = 1 := by omega
  obtain ⟨hp1, hp2⟩ := hp hs
  have k1 : c'.nreg 81012 = 1 := by rw [hI.hin _ (by omega_nf), hE.k1]
  have ok : okB E.W c'.nmem [.subN 81180 p 81131, .addN 81180 81180 81012] c'.nreg := by
    simp only [okB, okI, regI, upd]
    refine ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩),
      ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩, trivial⟩
    ram_grind
  refine FRS.seq (K₂ := wcK) (FRS.block hB _ hI ok) (fun c₁ hI₁ hA₁ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c'.nmem [.subN 81180 p 81131, .addN 81180 81180 81012]
      c'.nreg q := fun q => by rw [h₁]
  have u80 : c₁.nreg 81180 = c.nreg p - c.nreg 81131 + 1 := by
    rw [e₁]; simp [regB, regI, upd, k1, ep, e31]
  have f₁ : ∀ q, q ≠ 81180 → c₁.nreg q = c'.nreg q := fun q hq => by
    rw [e₁]; simp [regB, regI, upd, hq]
  have hfr₁ : ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c₁.nreg q = c.nreg q := fun q a b h => by
    ram_grind
  refine (wcand_inv hE hB hI₁ hA hBo hfr₁ hg (by omega) (by omega)
    (by omega) (by omega)).mono le_rfl
    (fun c₂ ⟨iv, hw, u2⟩ => ⟨iv, fun h => by omega, fun _ h => hw (by ram_grind)⟩)


end

/-- The cost bound of `wsel`. -/
def wsK : ℕ := 3 * wcK + 20

theorem wsel_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hA : EndOK E c 81160) (hBo : EndOK E c 81170) (hg : c.nreg 81130 < E.M.W.n)
    (hL : c.nreg 81132 < E.M.W.n) (hgL : c.nreg 81131 + c.nreg 81132 ≤ E.W)
    (hL0 : 0 < c.nreg 81132)
    (hpA : c.nreg 81160 = 1 → c.nreg 81131 ≤ c.nreg 81153 ∧ c.nreg 81153 - c.nreg 81131 < c.nreg 81132)
    (hpB : c.nreg 81170 = 1 → c.nreg 81131 ≤ c.nreg 81154 ∧ c.nreg 81154 - c.nreg 81131 < c.nreg 81132)
    (hroom : c.nreg ALLOC + wsK ≤ E.W) :
    FRS B E.P E.W c₀ wsel c wsK (fun c' => c'.nreg 81181 ≤ 1 ∧
      (c'.nreg 81181 = 1 → WCand E c₀ c (c'.nreg 81180) ∧
        c'.nreg 81183 = c.nreg 81131 + c'.nreg 81180 ∧ 1 ≤ c'.nreg 81180) ∧
      ((WCand E c₀ c 1 ∨
        (c.nreg 81160 = 1 ∧ WCand E c₀ c (c.nreg 81153 - c.nreg 81131 + 1)) ∨
        (c.nreg 81170 = 1 ∧ WCand E c₀ c (c.nreg 81154 - c.nreg 81131 + 1))) →
          c'.nreg 81181 = 1) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c'.nreg q = c.nreg q) := by
  have hW1 : 1 ≤ E.W := by omega
  refine (FRS.seq (K₂ := 3 * wcK + 12) (setR_fs hB hI (r := 81180) ⟨by norm_num, by norm_num⟩ hW1)
    (fun c₁ hI₁ hA₁ ⟨v₁, f₁⟩ => ?_)).mono (by omega_nf) (fun _ h => h)
  have hfr₁ : ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c₁.nreg q = c.nreg q := fun q a b h =>
    f₁ q (fun e => h (Or.inr ⟨by omega, by omega⟩))
  refine (FRS.seq (K₂ := 2 * wcK + 12) (wcand_inv hE hB hI₁ hA hBo hfr₁ hg (by omega)
    (by omega) (by rw [v₁]) (by grind [wsK]))
    (fun c₂ hI₂ hA₂ ⟨iv₂, hw₂, _⟩ => ?_)).mono (by omega) (fun _ h => h)
  refine (FRS.seq (K₂ := wcK + 6) (wTry_fs hE hB hI₂ hA hBo iv₂ (Or.inl ⟨rfl, rfl⟩) hg hL hgL hpA
    (by grind [wsK])) (fun c₃ hI₃ hA₃ ⟨iv₃, m₃, t₃⟩ => ?_)).mono (by omega)
    (fun _ h => h)
  refine (wTry_fs hE hB hI₃ hA hBo iv₃ (Or.inr ⟨rfl, rfl⟩) hg hL hgL hpB
    (by grind [wsK])).mono le_rfl (fun c₄ ⟨iv₄, m₄, t₄⟩ => ?_)
  obtain ⟨b1, b2, b3, b4⟩ := iv₄
  grind

end

end Restore

end Chazelle.Core
