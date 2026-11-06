module

public import Chazelle.Core.DownPhaseDrvDCall
public import Chazelle.Core.ShearInv
public import Chazelle.Core.FactsFullDegInt

/-!
# Down-phase restoration rounds (D8), part 8: one call of the splitting step

**`call_step`**: on a region `r` with more than `4` exit chords, `callS sF` calls the splitting
step (`FindOK`, complete since the full interior maps have degree `≤ 4`), appends the sound chord
`t` it returns, and writes the buckets of the two ends of `t` (two arc scans), within the
relative frame `Restore.RF drvBands B₀`.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam

@[expose] public section

/-! ## Frames -/

/-- A register is written by the rounds: a band of `drvBands`, not the allocator. -/
def InDrv (B : ℕ → Bool) : Prop := ∀ r, B r = true → bandOf r ∈ DrvR.drvBands ∧ r ≠ ALLOC

theorem mem_drvBands {r : ℕ} (h1 : 10000 ≤ r) (h2 : r < 230000) : bandOf r ∈ DrvR.drvBands := by
  simp only [DrvR.drvBands, phaseBands, bCore, Finset.mem_erase, Finset.mem_Icc, bandOf]
  omega

theorem rf_of_frameM {B : ℕ → Bool} (hB : InDrv B) {A₀ : ℕ} {c c' : Config} {k : ℕ}
    (h : FrameM B c c') (hm : ∀ a, a < A₀ → c'.nmem a = c.nmem a) :
    Restore.RF DrvR.drvBands A₀ c c' k := by
  have hnot : ∀ r, bandOf r ∉ DrvR.drvBands → B r = false := fun r hr => by
    cases h' : B r
    · rfl
    · exact absurd (hB r h').1 hr
  have hA : c'.nreg ALLOC = c.nreg ALLOC := h.1 _ (by
    cases h' : B ALLOC
    · rfl
    · exact absurd rfl (hB _ h').2)
  exact ⟨fun r hr _ => h.1 r (hnot r hr), fun r hr => h.2.1 r (hnot r hr), hm,
    fun a _ => by rw [h.2.2.1], h.2.2.2, by omega, by omega⟩

theorem rf_of_frameB {B : ℕ → Bool} (hB : InDrv B) {A₀ : ℕ} {c c' : Config} {k : ℕ}
    (h : FrameB B c c') : Restore.RF DrvR.drvBands A₀ c c' k :=
  rf_of_frameM hB (BuildRam.FrameB.toM h) (fun a _ => by rw [h.2.2.1])

theorem inDrv_scan : InDrv Bscan := by
  intro r hr
  simp only [Bscan, BuildRam.Bhalf, Bool.or_eq_true, decide_eq_true_eq] at hr
  exact ⟨mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩

theorem inDrv_appT : InDrv BappT := by
  intro r hr
  simp only [BappT, Bool.or_eq_true, decide_eq_true_eq] at hr
  exact ⟨mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩

theorem inDrv_eq {q : ℕ} (h1 : 10000 ≤ q) (h2 : q < 230000) (hq : q ≠ ALLOC) :
    InDrv (fun r => decide (r = q)) := by
  intro r hr
  simp only [decide_eq_true_eq] at hr
  subst hr
  exact ⟨mem_drvBands h1 h2, hq⟩

theorem inDrv_arg : InDrv (fun r => decide (81000 ≤ r ∧ r ≤ 81006)) := by
  intro r hr
  simp only [decide_eq_true_eq] at hr
  exact ⟨mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩

theorem find_bands : restoreBands ∪ DrvR.ioBandsD ⊆ DrvR.drvBands := by decide

/-- The splitting step keeps the registers of `bDownDrv` and `coreReg 1`. -/
theorem find_keeps {c c' : Config} {k : ℕ} (h : Frame (restoreBands ∪ DrvR.ioBandsD) c c' k)
    {q : ℕ} (hq : (210000 ≤ q ∧ q < 220000) ∨ q = 230001) : c'.nreg q = c.nreg q := by
  refine h.1 q ?_ (by unfold ALLOC; omega)
  have : bandOf q = 21 ∨ bandOf q = 23 := by unfold bandOf; omega
  rcases this with h' | h' <;> rw [h'] <;> decide

/-! ## The facts of the environment -/

namespace REnv

variable (E : REnv)

theorem hQ (hG : GoodEnv E.P) : E.Q.Simple := (shearInvariance (epsOf E.P) E.P).1 hG.1

theorem hGM (hG : GoodEnv E.P) : GoodModel E.M := Or.inr ⟨E.Q, E.hQ hG, rfl⟩

theorem nRegions_N : E.N.nRegions = E.R := by
  simp [NF.nRegions, BuildNF.buildNF, REnv.R]

end REnv

theorem RGood.hNF {E : REnv} {c₀ : Config} (hE : RGood E c₀) : IsNF E.M E.Q E.N :=
  (BuildNF.isNF_goodModel (E.hGM hE.hG) hE.hok hE.hperm hE.hsort).1

theorem desc_one {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} (h : ModelDescAt m B Q (interiorModel Q)) :
    m B = 1 := by
  rcases h with ⟨-, H, C, -, hC⟩ | ⟨h1, -, -⟩
  · exact absurd hC.symm (Restore.chainModel_ne_interior C Q)
  · exact h1

/-- **The buckets after appending a chord.** -/
theorem BktOK.snoc {M : Model} {Q : Polygon} {N : NF} {newL : List (ℕ × (ℕ × ℕ × ℕ))}
    {bk bk' : ℕ → ℕ} {r : ℕ} {t : ℕ × ℕ × ℕ} (h : BktOK M Q N newL bk)
    (hold : ∀ q, q < 2 * newL.length → bk' q = bk q)
    (h0 : ScanFound M Q N r (endPos t 0) (bk' (2 * newL.length)))
    (h1 : ScanFound M Q N r (endPos t 1) (bk' (2 * newL.length + 1))) :
    BktOK M Q N (newL ++ [(r, t)]) bk' := by
  have hg : ∀ q, q < 2 * (newL ++ [(r, t)]).length →
      (q < 2 * newL.length ∧ (newL ++ [(r, t)]).getD (q / 2) dflt = newL.getD (q / 2) dflt) ∨
      ((newL ++ [(r, t)]).getD (q / 2) dflt = (r, t) ∧
        (q = 2 * newL.length ∨ q = 2 * newL.length + 1)) := by
    intro q hq
    rw [List.length_append, List.length_singleton] at hq
    rcases Nat.lt_or_ge q (2 * newL.length) with hl | hl
    · left
      refine ⟨hl, ?_⟩
      rw [List.getD_append _ _ _ _ (by omega)]
    · right
      refine ⟨?_, by omega⟩
      rw [List.getD_append_right _ _ _ _ (by omega), show q / 2 - newL.length = 0 by omega]
      rfl
  constructor
  · intro q hq
    rcases hg q hq with ⟨hl, he⟩ | ⟨he, hq'⟩
    · rw [he, hold q hl]; exact h.key q hl
    · rw [he]
      rcases hq' with rfl | rfl
      · rw [show 2 * newL.length % 2 = 0 by omega]; exact h0.1
      · rw [show (2 * newL.length + 1) % 2 = 1 by omega]; exact h1.1
  · intro q hq
    rcases hg q hq with ⟨hl, he⟩ | ⟨he, hq'⟩
    · rw [he, hold q hl]; exact h.arc q hl
    · rw [he]
      rcases hq' with rfl | rfl
      · exact h0.2
      · exact h1.2

end

end DrvD

end Chazelle.Core
