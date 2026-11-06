module

public import Chazelle.Core.RestoreFHalf
public import Chazelle.Core.RestoreTRead

/-!
# WP-E, the search on the RAM (`FindOK`), part 14: loading the chord of a node

`chordLoad`: for the code `x` in `81150` (a chord node `2k`), `81121 := k` (halving), and the
chord record `k` of the piece's normal form (handle `81134`) into `81152` (`h`), `81153` (`lp`),
`81154` (`rp`), `81156` (`dn`), with `81155 := h + 1` (`81157`, `81158` scratch).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs

/-- The reads of the chord record. -/
def chordL : List Instr :=
  [.addN 81157 81121 81121, .addN 81157 81157 81157, .addN 81157 81157 81121,
    .addN 81158 81134 81014, .loadN 81158 81158, .addN 81157 81157 81158,
    .loadN 81152 81157, .addN 81157 81157 81012, .loadN 81153 81157,
    .addN 81157 81157 81012, .loadN 81154 81157, .addN 81157 81157 81012,
    .addN 81157 81157 81012, .loadN 81156 81157, .addN 81155 81152 81012]

/-- **Load the chord of the node `81150`.** -/
def chordLoad : Stmt := .seq (Stmt.block [.copyN 81120 81150]) (.seq halfS (Stmt.block chordL))

theorem chordL_eff (m f : ℕ → ℕ) (h3 : f 81014 = 3) (h1 : f 81012 = 1) :
    let a := f 81121 + f 81121 + (f 81121 + f 81121) + f 81121 + m (f 81134 + 3)
    regB m chordL f 81152 = m a ∧ regB m chordL f 81153 = m (a + 1) ∧
      regB m chordL f 81154 = m (a + 1 + 1) ∧ regB m chordL f 81156 = m (a + 1 + 1 + 1 + 1) ∧
      regB m chordL f 81155 = m a + 1 ∧
      ∀ q, q ≠ 81152 → q ≠ 81153 → q ≠ 81154 → q ≠ 81155 → q ≠ 81156 → q ≠ 81157 →
        q ≠ 81158 → regB m chordL f q = f q := by
  intro a
  refine ⟨by simp [chordL, regB, regI, upd, h3, a], by simp [chordL, regB, regI, upd, h3, h1, a],
    by simp [chordL, regB, regI, upd, h3, h1, a], by simp [chordL, regB, regI, upd, h3, h1, a],
    by simp [chordL, regB, regI, upd, h3, h1, a], fun q q1 q2 q3 q4 q5 q6 q7 =>
      regB_other m _ f (fun i hi => ?_)⟩
  simp only [chordL, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp only [dstI] <;> omega

variable {E : FEnv} {c₀ c : Config}

/-- The cost bound of `chordLoad`. -/
def clK (E : FEnv) (x : ℕ) : ℕ := halfK E.P.n x + 16

theorem chordLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem (c.nreg 81134) (c₀.nreg ALLOC) N) {x : ℕ}
    (hx : c.nreg 81150 = x) (hk : x / 2 < N.nChords) (hh : (N.chord (x / 2)).h + 1 ≤ E.W)
    (hroom : c.nreg ALLOC + clK E x ≤ E.W) :
    FRS B E.P E.W c₀ chordLoad c (clK E x) (fun c' => c'.nreg 81121 = x / 2 ∧
      c'.nreg 81152 = (N.chord (x / 2)).h ∧ c'.nreg 81153 = (N.chord (x / 2)).lp ∧
      c'.nreg 81154 = (N.chord (x / 2)).rp ∧ c'.nreg 81155 = (N.chord (x / 2)).h + 1 ∧
      c'.nreg 81156 = (N.chord (x / 2)).dn ∧
      ∀ q, ¬ (81120 ≤ q ∧ q ≤ 81124) → ¬ (81152 ≤ q ∧ q ≤ 81158) → c'.nreg q = c.nreg q) := by
  have ok0 : okB E.W c.nmem [.copyN 81120 81150] c.nreg := by
    simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), trivial⟩
  refine (FRS.seq (K₂ := halfK E.P.n x + 15) (FRS.block hB _ hI ok0)
    (fun c₁ hI₁ hA₁ h₁ => ?_)).mono (by simp [clK]; omega) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81120 81150] c.nreg q := fun q => by rw [h₁]
  have v20 : c₁.nreg 81120 = x := by rw [e₁]; simp [regB, regI, upd, hx]
  have f₁ : ∀ q, q ≠ 81120 → c₁.nreg q = c.nreg q := fun q hq => by
    rw [e₁]; simp [regB, regI, upd, hq]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by unfold ALLOC; omega)
  refine (FRS.seq (K₂ := 15) (halfS_fs hE hB hI₁ v20 (by rw [hA₁']; unfold clK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨k2, _, f₂⟩ => ?_)).mono (by omega) (fun _ h => h)
  have hN₂ : NFWithin c₂.nmem (c₂.nreg 81134) (c₀.nreg ALLOC) N := by
    rw [f₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      f₁ _ (by norm_num)]
    exact Robust.transport hN (fun a ha => hI₂.hm a ha)
  have hNA := hN₂.nfAt
  obtain ⟨-, hch, -⟩ := nf_bounds hN₂
  have hk' : x / 2 < N.chords.length := hk
  obtain ⟨hB7, -⟩ := nf_bounds hN₂
  have hcb := hch _ hk
  have hA0 : c₀.nreg ALLOC ≤ c₂.nreg ALLOC := hI₂.hA
  have hAW : c₂.nreg ALLOC ≤ E.W := hI₂.hw.1 ALLOC
  obtain ⟨r1, r2, r3, r4, r5⟩ := hNA.2.2.2.2.2.1 _ hk'
  have k3 : c₂.nreg 81014 = 3 := by rw [hI₂.hin _ (by unfold FFix; omega), hE.k3]
  have k1 : c₂.nreg 81012 = 1 := by rw [hI₂.hin _ (by unfold FFix; omega), hE.k1]
  set k := x / 2
  have hm5 : k + k + (k + k) + k + c₂.nmem (c₂.nreg 81134 + 3) + 4 < E.W := by omega
  have hh' : c₂.nmem (k + k + (k + k) + k + c₂.nmem (c₂.nreg 81134 + 3)) + 1 ≤ E.W := by
    rwa [show k + k + (k + k) + k + c₂.nmem (c₂.nreg 81134 + 3) =
      c₂.nmem (c₂.nreg 81134 + 3) + 5 * k by ring, r1]
  have hb3 : c₂.nreg 81134 + 3 ≤ E.W := by omega
  have ok : okB E.W c₂.nmem chordL c₂.nreg := by
    simp only [chordL, okB, okI, regI, upd]
    simp only [FScr, FOut, k2, k3, k1]
    norm_num
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, ?_⟩
    exact hh'
  refine (FRS.block hB _ hI₂ ok).mono (by simp [chordL]) (fun c₃ h₃ => ?_)
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem chordL c₂.nreg q := fun q => by rw [h₃]
  obtain ⟨u52, u53, u54, u56, u55, uf⟩ := chordL_eff c₂.nmem c₂.nreg k3 k1
  have ea : c₂.nreg 81121 + c₂.nreg 81121 + (c₂.nreg 81121 + c₂.nreg 81121) + c₂.nreg 81121 +
      c₂.nmem (c₂.nreg 81134 + 3) = c₂.nmem (c₂.nreg 81134 + 3) + 5 * k := by rw [k2]; ring
  rw [ea] at u52 u53 u54 u56 u55
  refine ⟨by rw [e₃, uf _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), k2], by rw [e₃, u52, r1], by rw [e₃, u53, r2],
    by rw [e₃, u54, show c₂.nmem (c₂.nreg 81134 + 3) + 5 * k + 1 + 1 = c₂.nmem (c₂.nreg 81134 + 3) + 5 * k + 2 by ring,
      r3], by rw [e₃, u55, r1],
    by rw [e₃, u56, show c₂.nmem (c₂.nreg 81134 + 3) + 5 * k + 1 + 1 + 1 + 1 = c₂.nmem (c₂.nreg 81134 + 3) + 5 * k + 4
      by ring, r5], fun q h1 h2 => ?_⟩
  rw [e₃, uf q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    f₂ q (by omega) (by omega) (by omega) (by omega) (by omega), f₁ q (by omega)]
end

end Restore

end Chazelle.Core
