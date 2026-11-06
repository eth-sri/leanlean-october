module

public import Chazelle.Core.RestoreFPairRun

/-!
# WP-E, the search on the RAM (`FindOK`), part 27: the loops over the ordered pairs of arcs

The outer loop runs `i` (`81030`) and the inner loop `j` (`81031`) over the `k` (`81032`) arcs of
region `r`; every pair runs `pairBody`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

variable {E : FEnv} {c₀ c : Config}

/-- **What the run of the pair `(i, j)` tells**, with the final flag `f`. -/
def PairDone (E : FEnv) (c₀ : Config) (i j f : ℕ) : Prop :=
  ∃ c₃ : Config, FInv E.W c₀ c₃ ∧ CutPost E (normOf E.M (Qof E.P) (arcOf E.N E.r i).s)
    (normOf E.M (Qof E.P) (arcOf E.N E.r i).e) c₃.nmem (c₃.nreg ALLOC) (c₃.nreg 81076) ∧
    c₃.nreg 81140 = (arcOf E.N E.r j).s.edge ∧ c₃.nreg 81141 = (arcOf E.N E.r j).s.hgt ∧
    ∀ i', i' < c₃.nmem (c₃.nreg 81076) →
      PieceDone (E.re c₃) c₃ c₃ (c₃.nreg 81076) i' f

theorem PairDone.mono {i j f f' : ℕ} (h : PairDone E c₀ i j f) (hf : f = 1 → f' = 1) :
    PairDone E c₀ i j f' := by
  obtain ⟨c₃, h1, h2, h3, h4, h5⟩ := h
  exact ⟨c₃, h1, h2, h3, h4, fun i' hi' => (h5 i' hi').mono hf⟩

/-- The piece obligations of the cut of arc `i` (piece bound `Kp`). -/
def PGood (E : FEnv) (c₀ : Config) (Kp i : ℕ) : Prop :=
  ∀ c', FInv E.W c₀ c' → CutPost E (normOf E.M (Qof E.P) (arcOf E.N E.r i).s)
    (normOf E.M (Qof E.P) (arcOf E.N E.r i).e) c'.nmem (c'.nreg ALLOC) (c'.nreg 81076) →
    ∀ i', i' < c'.nmem (c'.nreg 81076) → PieceGood (E.re c') c' (c'.nreg 81076) Kp i'

theorem nPair30 : ¬ PairW 81030 := by unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega
theorem nPair31 : ¬ PairW 81031 := by unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega
theorem nPair32 : ¬ PairW 81032 := by unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega

/-! ## The inner loop -/

/-- **The inner loop** over `j`. -/
def innerLoop (cu sT : Stmt) : Stmt :=
  .whileLtN 81031 81032 (.seq (pairBody cu sT) (Stmt.block [.addN 81031 81031 81012]))

/-- The invariant of the inner loop (from its start `c`). -/
def IInv (E : FEnv) (c₀ c : Config) (i k : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81031 → d.nreg q = c.nreg q) ∧
    (c.nreg 81007 = 1 → d.nreg 81007 = 1) ∧ d.nreg 81031 ≤ k ∧
    ∀ j, j < d.nreg 81031 → PairDone E c₀ i j (d.nreg 81007)

theorem innerLoop_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {i k Kp : ℕ}
    (hi : c.nreg 81030 = i) (hk : c.nreg 81032 = k) (h0 : c.nreg 81031 = 0)
    (hAi : ArcOK E i) (hA : ∀ t, t < k → ArcOK E t) (hPG : PGood E c₀ Kp i)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + (pairK E Kp + 3) * k ≤ E.W) :
    FRS B E.P E.W c₀ (innerLoop E.cu E.sT) c ((pairK E Kp + 3) * k + 2) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81031 → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧ ∀ j, j < k → PairDone E c₀ i j (c'.nreg 81007)) := by
  have hkW : k ≤ E.W := by
    have : k ≤ (pairK E Kp + 3) * k := Nat.le_mul_of_pos_left k (by omega)
    omega
  have hq0 : c.nreg 81032 - c.nreg 81031 = k := by rw [hk, h0]; rfl
  refine (FRS.while (a := 81031) (b := 81032) (body := .seq (pairBody E.cu E.sT)
    (Stmt.block [.addN 81031 81031 81012])) (IInv E c₀ c i k)
    (fun d => d.nreg 81032 - d.nreg 81031) (pairK E Kp + 1) (fun d _ hlt => by omega)
    (fun d hId hd hlt hroomd => ?_) hI ⟨hw, fun _ _ _ _ _ => rfl, id, by rw [h0]; omega,
      fun j hj => by rw [h0] at hj; omega⟩ (by rw [hq0]; omega)).mono (by rw [hq0])
    (fun c' hP => ?_)
  · obtain ⟨dw, df, dm, dle, dd⟩ := hd
    have d32 : d.nreg 81032 = k := by rw [df _ (by norm_num) (by norm_num) nPair32 (by norm_num), hk]
    have d30 : d.nreg 81030 = i := by rw [df _ (by norm_num) (by norm_num) nPair30 (by norm_num), hi]
    rw [d32] at hlt
    refine FRS.seq (K₁ := pairK E Kp) (K₂ := 1) (pairBody_fs hE hB hBT hId dw d30 rfl hAi
      (hA _ hlt) hPG hnW (by omega)) (fun c₁ hI₁ hA₁ h₁ => ?_)
    obtain ⟨w₁, f₁, m₁, pd⟩ := h₁
    have k1 : c₁.nreg 81012 = 1 := by rw [hI₁.hin _ (by unfold FFix; omega), hE.k1]
    have j₁ : c₁.nreg 81031 = d.nreg 81031 := f₁ _ (by norm_num) (by norm_num) nPair31
    have ok : okB E.W c₁.nmem [.addN 81031 81031 81012] c₁.nreg := by
      simp only [okB, okI, FScr, FOut, k1, j₁]; norm_num; omega
    refine (FRS.block hB _ hI₁ ok).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₁.nmem [.addN 81031 81031 81012] c₁.nreg q := fun q => by
      rw [h']
    have f' : ∀ q, q ≠ 81031 → c'.nreg q = c₁.nreg q := fun q h => by
      rw [e']; simp [regB, regI, upd, h]
    have v31 : c'.nreg 81031 = d.nreg 81031 + 1 := by
      rw [e']; simp [regB, regI, upd, k1, j₁]
    have g07 : c'.nreg 81007 = c₁.nreg 81007 := f' _ (by norm_num)
    have c32 : c'.nreg 81032 = k := by
      rw [f' _ (by norm_num), f₁ _ (by norm_num) (by norm_num) nPair32, d32]
    refine ⟨⟨w₁.congr' (fun q a b => f' q (by omega)), fun q a b hq h31 => by
      rw [f' q h31, f₁ q a b hq, df q a b hq h31], fun h => by rw [g07]; exact m₁ (dm h),
      by omega, fun j hj => ?_⟩, by omega⟩
    rw [g07]
    rcases Nat.lt_or_ge j (d.nreg 81031) with h | h
    · exact (dd j h).mono m₁
    · rwa [show j = d.nreg 81031 by omega]
  · obtain ⟨hP1, hex⟩ := hP
    obtain ⟨cw, cf, cm, cle, cd⟩ := hP1
    have c32 : c'.nreg 81032 = k := by
      rw [cf _ (by norm_num) (by norm_num) nPair32 (by norm_num), hk]
    exact ⟨cw, cf, cm, fun j hj => cd j (by omega)⟩

/-! ## The outer loop -/

/-- **The outer loop** over `i`. -/
def outerLoop (cu sT : Stmt) : Stmt :=
  .whileLtN 81030 81032 (.seq (Stmt.block [.constN 81031 0]) (.seq (innerLoop cu sT)
    (Stmt.block [.addN 81030 81030 81012])))

/-- The invariant of the outer loop (from its start `c`). -/
def OInv (E : FEnv) (c₀ c : Config) (k : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81030 → q ≠ 81031 →
    d.nreg q = c.nreg q) ∧ (c.nreg 81007 = 1 → d.nreg 81007 = 1) ∧ d.nreg 81030 ≤ k ∧
    ∀ i, i < d.nreg 81030 → ∀ j, j < k → PairDone E c₀ i j (d.nreg 81007)

/-- The cost bound of an outer step. -/
def outerK (E : FEnv) (Kp k : ℕ) : ℕ := (pairK E Kp + 3) * k + 4

theorem outerLoop_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {k Kp : ℕ}
    (hk : c.nreg 81032 = k) (h0 : c.nreg 81030 = 0)
    (hA : ∀ t, t < k → ArcOK E t) (hPG : ∀ t, t < k → PGood E c₀ Kp t)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + (outerK E Kp k + 2) * k ≤ E.W) :
    FRS B E.P E.W c₀ (outerLoop E.cu E.sT) c ((outerK E Kp k + 2) * k + 2) (fun c' =>
      FWin E c' ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → q ≠ 81030 → q ≠ 81031 →
        c'.nreg q = c.nreg q) ∧ (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      ∀ i, i < k → ∀ j, j < k → PairDone E c₀ i j (c'.nreg 81007)) := by
  have hkW : k ≤ E.W := by
    have : k ≤ (outerK E Kp k + 2) * k := Nat.le_mul_of_pos_left k (by unfold outerK; omega)
    omega
  have hq0 : c.nreg 81032 - c.nreg 81030 = k := by rw [hk, h0]; rfl
  refine (FRS.while (a := 81030) (b := 81032) (body := .seq (Stmt.block [.constN 81031 0])
    (.seq (innerLoop E.cu E.sT) (Stmt.block [.addN 81030 81030 81012]))) (OInv E c₀ c k)
    (fun d => d.nreg 81032 - d.nreg 81030) (outerK E Kp k) (fun d _ hlt => by omega)
    (fun d hId hd hlt hroomd => ?_) hI ⟨hw, fun _ _ _ _ _ _ => rfl, id, by rw [h0]; omega,
      fun i hi => by rw [h0] at hi; omega⟩ (by rw [hq0]; omega)).mono (by rw [hq0])
    (fun c' hP => ?_)
  · obtain ⟨dw, df, dm, dle, dd⟩ := hd
    have d32 : d.nreg 81032 = k := by
      rw [df _ (by norm_num) (by norm_num) nPair32 (by norm_num) (by norm_num), hk]
    rw [d32] at hlt
    have ok0 : okB E.W d.nmem [.constN 81031 0] d.nreg := by
      simp only [okB, okI, FScr, FOut]; norm_num
    refine FRS.seq (K₁ := 1) (K₂ := (pairK E Kp + 3) * k + 2 + 1) (FRS.block hB _ hId ok0)
      (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono (by unfold outerK; omega) (fun _ h => h)
    have e₁ : ∀ q, c₁.nreg q = regB d.nmem [.constN 81031 0] d.nreg q := fun q => by rw [h₁]
    have f₁ : ∀ q, q ≠ 81031 → c₁.nreg q = d.nreg q := fun q h => by
      rw [e₁]; simp [regB, regI, upd, h]
    have z31 : c₁.nreg 81031 = 0 := by rw [e₁]; simp [regB, regI, upd]
    have w₁ : FWin E c₁ := dw.congr' (fun q a b => f₁ q (by omega))
    refine FRS.seq (K₁ := (pairK E Kp + 3) * k + 2) (K₂ := 1)
      (innerLoop_fs hE hB hBT hI₁ w₁ (f₁ _ (by norm_num)) (by rw [f₁ _ (by norm_num), d32]) z31
        (hA _ hlt) hA (hPG _ hlt) hnW (by unfold outerK at hroomd; omega))
      (fun c₂ hI₂ hA₂ h₂ => ?_)
    obtain ⟨w₂, f₂, m₂, pd⟩ := h₂
    have k1 : c₂.nreg 81012 = 1 := by rw [hI₂.hin _ (by unfold FFix; omega), hE.k1]
    have i₂ : c₂.nreg 81030 = d.nreg 81030 := by
      rw [f₂ _ (by norm_num) (by norm_num) nPair30 (by norm_num), f₁ _ (by norm_num)]
    have ok : okB E.W c₂.nmem [.addN 81030 81030 81012] c₂.nreg := by
      simp only [okB, okI, FScr, FOut, k1, i₂]; norm_num; omega
    refine (FRS.block hB _ hI₂ ok).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.addN 81030 81030 81012] c₂.nreg q := fun q => by
      rw [h']
    have f' : ∀ q, q ≠ 81030 → c'.nreg q = c₂.nreg q := fun q h => by
      rw [e']; simp [regB, regI, upd, h]
    have v30 : c'.nreg 81030 = d.nreg 81030 + 1 := by
      rw [e']; simp [regB, regI, upd, k1, i₂]
    have g07 : c'.nreg 81007 = c₂.nreg 81007 := f' _ (by norm_num)
    have g07' : c₂.nreg 81007 = 1 → c'.nreg 81007 = 1 := fun h => by rwa [g07]
    have c32 : c'.nreg 81032 = k := by
      rw [f' _ (by norm_num), f₂ _ (by norm_num) (by norm_num) nPair32 (by norm_num),
        f₁ _ (by norm_num), d32]
    refine ⟨⟨w₂.congr' (fun q a b => f' q (by omega)), fun q a b hq h30 h31 => by
      rw [f' q h30, f₂ q a b hq h31, f₁ q h31, df q a b hq h30 h31],
      fun h => g07' (m₂ (by rw [f₁ _ (by norm_num)]; exact dm h)),
      by omega, fun i hi j hj => ?_⟩, by omega⟩
    rcases Nat.lt_or_ge i (d.nreg 81030) with h | h
    · exact ((dd i h j hj).mono (fun h => m₂ (by rwa [f₁ _ (by norm_num)]))).mono g07'
    · rw [show i = d.nreg 81030 by omega]; exact (pd j hj).mono g07'
  · obtain ⟨hP1, hex⟩ := hP
    obtain ⟨cw, cf, cm, cle, cd⟩ := hP1
    have c32 : c'.nreg 81032 = k := by
      rw [cf _ (by norm_num) (by norm_num) nPair32 (by norm_num) (by norm_num), hk]
    exact ⟨cw, cf, cm, fun i hi j hj => cd i (by omega) j hj⟩

end

end Restore

end Chazelle.Core
