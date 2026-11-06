module

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
    h q (by unfold WsW KeyW; omega) (by omega) (by omega)
  unfold WCand GAt
  rw [e 81132 (by norm_num), e 81130 (by norm_num), e 81160 (by norm_num), e 81131 (by norm_num),
    e 81153 (by norm_num), e (81160 + 7) (by norm_num), e 81170 (by norm_num),
    e 81154 (by norm_num), e (81170 + 7) (by norm_num), e (81160 + 5) (by norm_num),
    e (81160 + 1) (by norm_num), e (81160 + 2) (by norm_num), e (81160 + 3) (by norm_num),
    e (81160 + 4) (by norm_num), e (81160 + 6) (by norm_num), e (81170 + 5) (by norm_num),
    e (81170 + 1) (by norm_num), e (81170 + 2) (by norm_num), e (81170 + 3) (by norm_num),
    e (81170 + 4) (by norm_num), e (81170 + 6) (by norm_num)]


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
  refine ⟨by rw [e0]; exact e1, by rw [he 5 (by omega)]; exact e5,
    by rw [he 6 (by omega)]; exact e6, fun h0 h5 => ?_⟩
  rw [e0] at h0; rw [he 5 (by omega)] at h5
  rw [he 1 (by omega), he 2 (by omega), he 3 (by omega), he 4 (by omega)]
  exact ex h0 h5

theorem wcand_inv (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) {c' : Config}
    (hI : FInv E.W c₀ c') (hA : EndOK E c 81160) (hBo : EndOK E c 81170)
    (hfr : ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c'.nreg q = c.nreg q)
    (hg : c.nreg 81130 < E.M.W.n) (hun : c'.nreg 81180 < E.M.W.n)
    (hu' : c.nreg 81131 + c'.nreg 81180 ≤ E.W) (hu1 : 1 ≤ c'.nreg 81180)
    (hroom : c'.nreg ALLOC + wcK ≤ E.W) :
    FRS B E.P E.W c₀ wcand c' wcK (fun c'' => WsInv E c₀ c c'' ∧
      (WCand E c₀ c (c'.nreg 81180) → c''.nreg 81181 = 1) ∧ c''.nreg 81180 = c'.nreg 81180) := by
  have fr : ∀ q, ¬ WsW q → 81100 ≤ q → q < 81200 → c'.nreg q = c.nreg q := fun q h a b =>
    hfr q (by omega) (by omega) h
  have sl : ∀ s, (s = 81160 ∨ s = 81170) → ∀ j, j ≤ 6 → c'.nreg (s + j) = c.nreg (s + j) :=
    fun s hs j hj => fr _ (by unfold WsW KeyW; omega) (by omega) (by omega)
  refine (wcand_fs hE hB hI ((hA.congr (sl 81160 (Or.inl rfl)))) (hBo.congr (sl 81170 (Or.inr rfl)))
    (by rw [fr 81130 (by unfold WsW KeyW; omega) (by norm_num) (by norm_num)]; exact hg) hun
    (by rw [fr 81131 (by unfold WsW KeyW; omega) (by norm_num) (by norm_num)]; exact hu')
    hroom).mono le_rfl (fun c'' ⟨b, e83, f⟩ => ?_)
  have wc : WCand E c₀ c' (c'.nreg 81180) ↔ WCand E c₀ c (c'.nreg 81180) := WCand.congr fr
  have u80 : c''.nreg 81180 = c'.nreg 81180 := f _ (by norm_num) (by norm_num)
    (by unfold WcW KeyW; omega)
  refine ⟨⟨b.1, fun h => ⟨by rw [u80]; exact wc.1 (b.2.1 h), by
    rw [e83, u80, fr 81131 (by unfold WsW KeyW; omega) (by norm_num) (by norm_num)]⟩,
    fun q a b' hq => ?_, by rw [u80]; exact hu1⟩, fun h => b.2.2 (wc.2 h), u80⟩
  have hq' : ¬ WcW q := fun h => hq (h.elim Or.inl (fun h' => Or.inr ⟨by omega, h'.2⟩))
  rw [f q a b' hq', hfr q a b' hq]

/-- **One try.** -/
theorem wTry_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) {c' : Config}
    (hI : FInv E.W c₀ c') (hA : EndOK E c 81160) (hBo : EndOK E c 81170)
    (hv : WsInv E c₀ c c') {s p : ℕ} (hsp : (s = 81160 ∧ p = 81153) ∨ (s = 81170 ∧ p = 81154))
    (hg : c.nreg 81130 < E.M.W.n) (hL : c.nreg 81132 < E.M.W.n)
    (hgL : c.nreg 81131 + c.nreg 81132 ≤ E.W)
    (hp : c.nreg s = 1 → c.nreg 81131 ≤ c.nreg p ∧ c.nreg p - c.nreg 81131 < c.nreg 81132)
    (hroom : c'.nreg ALLOC + wcK + 6 ≤ E.W) :
    FRS B E.P E.W c₀ (wTry s p) c' (wcK + 6) (fun c'' => WsInv E c₀ c c'' ∧
      (c'.nreg 81181 = 1 → c''.nreg 81181 = 1) ∧
      (c.nreg s = 1 → WCand E c₀ c (c.nreg p - c.nreg 81131 + 1) → c''.nreg 81181 = 1)) := by
  have hW1 : 1 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  have k0 := k0_of hE hI
  obtain ⟨v1, v2, v3, v4⟩ := hv
  have fr : ∀ q, ¬ WsW q → 81100 ≤ q → q < 81200 → c'.nreg q = c.nreg q := fun q h a b =>
    v3 q (by omega) (by omega) h
  have es : c'.nreg s = c.nreg s := fr s (by unfold WsW KeyW; omega) (by omega) (by omega)
  have ep : c'.nreg p = c.nreg p := fr p (by unfold WsW KeyW; omega) (by omega) (by omega)
  have e31 : c'.nreg 81131 = c.nreg 81131 := fr 81131 (by unfold WsW KeyW; omega) (by norm_num)
    (by norm_num)
  have hs1 : c.nreg s ≤ 1 := by rcases hsp with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hA.1, hBo.1]
  by_cases a1 : c'.nreg 81011 < c'.nreg 81181
  · have h1 : c'.nreg 81181 = 1 := by rw [k0] at a1; omega
    exact (FRS.ifT a1 (FRS.skip (K := 0) hI ⟨⟨v1, v2, v3, v4⟩, id, fun _ _ => h1⟩)).mono (by omega)
      (fun _ h => h)
  refine (FRS.ifF a1 ?_).mono (K := wcK + 6) le_rfl (fun _ h => h)
  have h0 : c'.nreg 81181 = 0 := by rw [k0] at a1; omega
  by_cases a2 : c'.nreg 81011 < c'.nreg s
  swap
  · exact (FRS.ifF a2 (FRS.skip (K := 0) hI ⟨⟨v1, v2, v3, v4⟩, fun h => by omega,
      fun h => by rw [k0, es] at a2; omega⟩)).mono (by omega) (fun _ h => h)
  refine (FRS.ifT a2 ?_).mono (K := wcK + 4) (by omega) (fun _ h => h)
  have hs : c.nreg s = 1 := by rw [k0, es] at a2; omega
  obtain ⟨hp1, hp2⟩ := hp hs
  have k1 : c'.nreg 81012 = 1 := by rw [hI.hin _ (by unfold FFix; omega), hE.k1]
  have ok : okB E.W c'.nmem [.subN 81180 p 81131, .addN 81180 81180 81012] c'.nreg := by
    simp only [okB, okI, regI, upd]
    refine ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩),
      ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩, trivial⟩
    simp only [ite_true, show (81012 : ℕ) ≠ 81180 by norm_num, ite_false, k1, ep, e31]
    omega
  refine FRS.seq (K₂ := wcK) (FRS.block hB _ hI ok) (fun c₁ hI₁ hA₁ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c'.nmem [.subN 81180 p 81131, .addN 81180 81180 81012]
      c'.nreg q := fun q => by rw [h₁]
  have u80 : c₁.nreg 81180 = c.nreg p - c.nreg 81131 + 1 := by
    rw [e₁]; simp [regB, regI, upd, k1, ep, e31]
  have f₁ : ∀ q, q ≠ 81180 → c₁.nreg q = c'.nreg q := fun q hq => by
    rw [e₁]; simp [regB, regI, upd, hq]
  have hfr₁ : ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c₁.nreg q = c.nreg q := fun q a b h => by
    rw [f₁ q (fun e => h (Or.inr ⟨by omega, by omega⟩)), v3 q a b h]
  refine (wcand_inv hE hB hI₁ hA hBo hfr₁ hg (by rw [u80]; omega) (by rw [u80]; omega)
    (by rw [u80]; omega) (by omega)).mono le_rfl
    (fun c₂ ⟨iv, hw, u2⟩ => ⟨iv, fun h => by omega, fun _ h => hw (by rw [u80]; exact h)⟩)

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
  have hW1 : 1 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  refine (FRS.seq (K₂ := 3 * wcK + 12) (setR_fs hB hI (r := 81180) ⟨by norm_num, by norm_num⟩ hW1)
    (fun c₁ hI₁ hA₁ ⟨v₁, f₁⟩ => ?_)).mono (by unfold wsK; omega) (fun _ h => h)
  have hfr₁ : ∀ q, 80000 ≤ q → q < 90000 → ¬ WsW q → c₁.nreg q = c.nreg q := fun q a b h =>
    f₁ q (fun e => h (Or.inr ⟨by omega, by omega⟩))
  refine (FRS.seq (K₂ := 2 * wcK + 12) (wcand_inv hE hB hI₁ hA hBo hfr₁ hg (by rw [v₁]; omega)
    (by rw [v₁]; omega) (by rw [v₁]) (by unfold wsK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨iv₂, hw₂, _⟩ => ?_)).mono (by omega) (fun _ h => h)
  refine (FRS.seq (K₂ := wcK + 6) (wTry_fs hE hB hI₂ hA hBo iv₂ (Or.inl ⟨rfl, rfl⟩) hg hL hgL hpA
    (by unfold wsK at hroom; omega)) (fun c₃ hI₃ hA₃ ⟨iv₃, m₃, t₃⟩ => ?_)).mono (by omega)
    (fun _ h => h)
  refine (wTry_fs hE hB hI₃ hA hBo iv₃ (Or.inr ⟨rfl, rfl⟩) hg hL hgL hpB
    (by unfold wsK at hroom; omega)).mono le_rfl (fun c₄ ⟨iv₄, m₄, t₄⟩ => ?_)
  obtain ⟨b1, b2, b3, b4⟩ := iv₄
  refine ⟨b1, fun h => ⟨(b2 h).1, (b2 h).2, b4⟩, fun h => ?_, b3⟩
  rcases h with h | ⟨h0, h⟩ | ⟨h0, h⟩
  · exact m₄ (m₃ (hw₂ (by rw [v₁]; exact h)))
  · exact m₄ (t₃ h0 h)
  · exact t₄ h0 h

end

end Restore

end Chazelle.Core
