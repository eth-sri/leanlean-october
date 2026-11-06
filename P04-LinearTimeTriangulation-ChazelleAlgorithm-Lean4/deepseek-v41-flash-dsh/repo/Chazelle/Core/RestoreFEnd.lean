module

public import Chazelle.Golf

public import Chazelle.Core.RestoreFLt
public import Chazelle.Core.RestoreFVert

/-!
# WP-E, the search on the RAM (`FindOK`), part 9: the ends of a node chord

Stretch registers: `81130` the host base vertex `g`, `81131` the piece-chain base vertex `g'`,
`81132` the length `L`, `81133` the piece chain's descriptor, `81134` its normal form, `81135`
`g' + L`.  Node registers: `81152` the height vertex `h` of the chord, `81153`/`81154` its left and
right walk edges, `81155 = h + 1`.

For an end in the walk edge register `p`, with result slot `s` (`81160` left, `81170` right):

* `endPre s p`: `s + 7 := [0 < param]` (piece-chain keys of `(p, 0)` and `(p, h + 1)`), and
  `s := [g' ≤ p < g' + L ∧ (g' < p ∨ 0 < param)]` (the end is strictly inside the stretch).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

variable {E : FEnv} {c₀ c : Config}

/-- A scratch register of the search outside the candidate and the test's registers. -/
def SReg (r : ℕ) : Prop := 81028 ≤ r ∧ r < 83000

/-- **Setting a scratch register.** -/
theorem setR_fs {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c) {r v : ℕ} (hr : SReg r)
    (hv : v ≤ E.W) :
    FRS B E.P E.W c₀ (Stmt.block [.constN r v]) c 1 (fun c' => c'.nreg r = v ∧
      ∀ q, q ≠ r → c'.nreg q = c.nreg q) := by
  unfold SReg at hr
  have ok : okB E.W c.nmem [.constN r v] c.nreg := by
    simp only [okB, okI]; exact ⟨⟨Or.inl (Or.inl ⟨⋄, ⋄⟩), hv⟩, trivial⟩
  refine (FRS.block hB _ hI ok).mono (✓) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem [.constN r v] c.nreg q := fun q => Ρ h'
  exact ⟨by rw [e']; simp [regB, regI, upd], fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩

/-- The host edge and height code of an end strictly inside the stretch. -/
def endMap (s p : ℕ) : Stmt :=
  .seq (Stmt.block [.subN (s + 1) p 81131, .subN (s + 9) 81017 81130])
    (.seq (.ifLtN (s + 1) (s + 9) (Stmt.block [.addN (s + 1) (s + 1) 81130])
      (Stmt.block [.subN (s + 1) (s + 1) (s + 9)]))
      (.seq (Stmt.block [.constN (s + 2) 0])
        (.ifLtN 81011 (s + 7) (Stmt.block [.copyN (s + 2) 81155]) .skip)))

/-- **The host position of an end.** -/
theorem endMap_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s p : ℕ} (hs : SReg s) (hs9 : SReg (s + 9)) (_hp1 : p ≠ s + 1) (_hp9 : p ≠ s + 9)
    (hsF : ∀ q, FFix q → q ≠ s + 1 ∧ q ≠ s + 2 ∧ q ≠ s + 9) (h7 : s + 7 ≠ s + 2)
    (h71 : s + 7 ≠ s + 1) (h79 : s + 7 ≠ s + 9) (h1 : s + 1 ≠ 81130) (h9 : s + 9 ≠ 81130)
    (h55 : 81155 ≠ s + 1 ∧ 81155 ≠ s + 2 ∧ 81155 ≠ s + 9)
    (hp : c.nreg 81131 ≤ c.nreg p) (hg : c.nreg 81130 < E.M.W.n)
    (hd : c.nreg p - c.nreg 81131 < E.M.W.n) (_hb7 : c.nreg (s + 7) ≤ 1) :
    FRS B E.P E.W c₀ (endMap s p) c 10 (fun c' =>
      c'.nreg (s + 1) = (c.nreg 81130 + (c.nreg p - c.nreg 81131)) % E.M.W.n ∧
      (c.nreg (s + 7) = 1 → c'.nreg (s + 2) = c.nreg 81155) ∧
      (c.nreg (s + 7) = 0 → c'.nreg (s + 2) = 0) ∧
      ∀ q, q ≠ s + 1 → q ≠ s + 2 → q ≠ s + 9 → c'.nreg q = c.nreg q) := by
  unfold SReg at hs hs9
  set n := E.M.W.n with hn
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81017 = n ∧ c'.nreg 81011 = 0 :=
    fun c' hI' => ⟨by rw [hI'.hin _ (by unfold FFix; omega), hE.wn],
      by rw [hI'.hin _ (by unfold FFix; omega), hE.k0]⟩
  obtain ⟨n17, k0⟩ := fx c hI
  have h17 : s + 1 ≠ 81017 := (hsF 81017 (by unfold FFix; omega)).1.symm
  have h17' : s + 9 ≠ 81017 := (hsF 81017 (by unfold FFix; omega)).2.2.symm
  have ok : okB E.W c.nmem [.subN (s + 1) p 81131, .subN (s + 9) 81017 81130] c.nreg := by
    simp only [okB, okI]
    exact ⟨Or.inl (Or.inl ⟨by omega, by omega⟩), Or.inl (Or.inl ⟨by omega, by omega⟩), trivial⟩
  refine FRS.seq (K₂ := 8) (FRS.block hB _ hI ok) (fun c₁ hI₁ _ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.subN (s + 1) p 81131, .subN (s + 9) 81017 81130]
      c.nreg q := fun q => by rw [h₁]
  have v1 : c₁.nreg (s + 1) = c.nreg p - c.nreg 81131 := by
    rw [e₁]; simp [regB, regI, upd]
  have v9 : c₁.nreg (s + 9) = n - c.nreg 81130 := by
    rw [e₁]; simp [regB, regI, upd, n17, show s ≠ 81016 by omega, show s ≠ 81129 by omega]
  have f₁ : ∀ q, q ≠ s + 1 → q ≠ s + 9 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₁]; simp [regB, regI, upd, h1, h2]
  have w30 := f₁ 81130 (Ne.symm h1) (Ne.symm h9)
  -- the host edge
  have step2 : FRS B E.P E.W c₀ (.ifLtN (s + 1) (s + 9) (Stmt.block [.addN (s + 1) (s + 1) 81130])
      (Stmt.block [.subN (s + 1) (s + 1) (s + 9)])) c₁ 3 (fun c' =>
        c'.nreg (s + 1) = (c.nreg 81130 + (c.nreg p - c.nreg 81131)) % n ∧
        ∀ q, q ≠ s + 1 → c'.nreg q = c₁.nreg q) := by
    by_cases hc : c₁.nreg (s + 1) < c₁.nreg (s + 9)
    · have okc : okB E.W c₁.nmem [.addN (s + 1) (s + 1) 81130] c₁.nreg := by
        simp only [okB, okI]
        refine ⟨⟨Or.inl (Or.inl ⟨by omega, by omega⟩), ?_⟩, trivial⟩
        have := hI₁.hw.1 81017
        rw [(fx c₁ hI₁).1] at this
        omega
      refine (FRS.ifT hc ((FRS.block hB _ hI₁ okc))).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.addN (s + 1) (s + 1) 81130] c₁.nreg q :=
        fun q => by rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [v1, w30, Nat.mod_eq_of_lt (by rw [v1, v9] at hc; omega)]; omega
    · have okc : okB E.W c₁.nmem [.subN (s + 1) (s + 1) (s + 9)] c₁.nreg := by
        simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by omega, by omega⟩), trivial⟩
      refine (FRS.ifF hc ((FRS.block hB _ hI₁ okc))).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN (s + 1) (s + 1) (s + 9)] c₁.nreg q :=
        fun q => by rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [v1, v9] at hc ⊢
      have e2 : c.nreg 81130 + (c.nreg p - c.nreg 81131) =
          (c.nreg p - c.nreg 81131 - (n - c.nreg 81130)) + n := by omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  refine FRS.seq (K₂ := 5) step2 (fun c₂ hI₂ _ ⟨u1, g₂⟩ => ?_)
  refine FRS.seq (K₂ := 4) (setR_fs hB hI₂ (r := s + 2) ⟨by omega, by omega⟩ (Nat.zero_le _))
    (fun c₃ hI₃ _ ⟨u2, g₃⟩ => ?_)
  have g7 : c₃.nreg (s + 7) = c.nreg (s + 7) := by
    rw [g₃ _ h7, g₂ _ h71, f₁ _ h71 h79]
  have g11 : c₃.nreg 81011 = 0 := (fx c₃ hI₃).2
  have fin : ∀ c' : Config, (∀ q, q ≠ s + 2 → c'.nreg q = c₃.nreg q) →
      ∀ q, q ≠ s + 1 → q ≠ s + 2 → q ≠ s + 9 → c'.nreg q = c.nreg q :=
    fun c' h q h1 h2 h3 => by rw [h q h2, g₃ q h2, g₂ q h1, f₁ q h1 h3]
  by_cases hc : c₃.nreg 81011 < c₃.nreg (s + 7)
  · have okc : okB E.W c₃.nmem [.copyN (s + 2) 81155] c₃.nreg := by
      simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by omega, by omega⟩), trivial⟩
    refine (FRS.ifT hc (FRS.block hB _ hI₃ okc)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₃.nmem [.copyN (s + 2) 81155] c₃.nreg q :=
      fun q => by rw [h']
    have f' : ∀ q, q ≠ s + 2 → c'.nreg q = c₃.nreg q := fun q hq => by
      rw [e']; simp [regB, regI, upd, hq]
    refine ⟨by rw [f' _ (by omega), g₃ _ (by omega), u1], fun _ => ?_, fun h0 => by
      rw [g11, g7, h0] at hc; omega, fin c' f'⟩
    rw [e']; simp only [regB, regI, upd, ite_true]
    rw [g₃ _ h55.2.1, g₂ _ h55.1, f₁ _ h55.1 h55.2.2]
  · exact (FRS.ifF hc (FRS.skip (K := 0) hI₃ ⟨by rw [g₃ _ (by omega), u1],
      fun h1 => by rw [g11, g7, h1] at hc; omega, fun _ => u2, fin c₃ (fun _ _ => rfl)⟩)).mono
      (by omega) (fun _ h => h)

end

end Restore

end Chazelle.Core
