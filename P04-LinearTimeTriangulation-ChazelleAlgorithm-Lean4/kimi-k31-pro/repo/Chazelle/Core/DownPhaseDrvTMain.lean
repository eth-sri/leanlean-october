module

public import Chazelle.Core.DownPhaseDrvTRun

/-!
# Down-phase transition (D2): `DrvR.TransSpec`

**`transSpec_of`**: for every count function `cnt` satisfying the transition count condition
`TransCnt` (the conclusion of `DownMath.cnt_trans`), the procedure `transS` meets the transition
contract `DrvR.TransSpec X cnt` of the down-phase driver (for every up-phase context `X`; the
transition does not use it).  **`transSpec`**: the instance `cnt = DownMath.cnt A B`, `1 ≤ A`.

From the canonical normal form `N` of the top chain (handle in `coreReg 2`): the `LeftInside`
bit (`orientT`), the inner-side shift (`c0S`), the filter (`filtS`, the list `transL` of the
pieces of the chords, `trans_math`), the build with its event list (`buildT`), and the
registers `1 … 5` of `bDownDrv` (`finT`) give the level invariant `Inv(p)`:
(I1) and (I2) from `Trans.transition`, (I3) from Lemma 2.3 (`DownMath.trans_count`).
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs BuildRam
open BuildNF (codeLe)
open SortL (seg)

@[expose] public section

/-- **The count condition of the transition** (the conclusion of `DownMath.cnt_trans` at
`p = topGrade n`). -/
def TransCnt (cnt : ℕ → ℕ) : Prop :=
  ∀ n K K₀ : ℕ, n - 1 ≤ 2 ^ topGrade n →
    K₀ * (gradeGran (topGrade n) + 1) ≤ 840 * (2 * (n - 1) + 1) → K ≤ K₀ →
      K * 2 ^ Cost.ceilBeta (topGrade n) ≤
        cnt (topGrade n) * (2 ^ topGrade n + 2 ^ Cost.ceilBeta (topGrade n))

/-- The count of the driver satisfies the condition. -/
theorem transCnt_cnt {A : ℕ} (hA : 1 ≤ A) (B : ℕ) : TransCnt (DownMath.cnt A B) :=
  fun _ _ _ hn hK₀ hK => DownMath.cnt_trans hA B hn hK₀ hK

theorem mem_drvBands {b : ℕ} : b ∈ DrvR.drvBands ↔ 1 ≤ b ∧ b ≤ 24 ∧ b ≠ 23 := by
  unfold DrvR.drvBands phaseBands bCore
  simp only [Finset.mem_erase, Finset.mem_Icc]
  omega

/-- A frame of the driver's bands from a write-set frame not touching the allocator. -/
theorem frame_drv {B : ℕ → Bool} {c c' : Config} {k : ℕ} (F : FrameM B c c')
    (hB : ∀ r, B r = true → bandOf r ∈ DrvR.drvBands) (hA : B ALLOC = false)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) : Frame DrvR.drvBands c c' k := by
  have hAA : c'.nreg ALLOC = c.nreg ALLOC := F.1 _ hA
  have hnot : ∀ r, bandOf r ∉ DrvR.drvBands → B r = false := fun r hr => by
    cases h : B r
    · rfl
    · exact absurd (hB r h) hr
  exact ⟨fun r hr _ => F.1 r (hnot r hr), fun r hr => F.2.1 r (hnot r hr), hm,
    fun a _ => by rw [F.2.2.1], F.2.2.2, by rw [hAA], by rw [hAA]; omega⟩

theorem band_of_range {r lo : ℕ} (h1 : 10000 * lo ≤ r) (h2 : r < 10000 * lo + 10000) :
    bandOf r = lo := by
  unfold bandOf; omega

section exec

variable {P : Polygon} {W : ℕ}

/-- The `LeftInside` bit as a register value. -/
theorem bit_eq {b : ℕ} {p : Prop} [Decidable p] (hb : b ≤ 1) (h : b = 1 ↔ p) :
    b = if decide p then 1 else 0 := by
  by_cases hp : p
  · simp only [hp, decide_true, ite_true]; exact h.2 hp
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    by_contra hb0; exact hp (h.1 (by omega))

set_option maxHeartbeats 8000000 in
/-- **The transition meets its contract**, for every count function satisfying the
transition count condition. -/
theorem transSpec_of {X : MemCtx} {cnt : ℕ → ℕ} (hcnt : TransCnt cnt) :
    DrvR.TransSpec X cnt := by
  classical
  refine ⟨transS, κT, fun P W c hw hpre hroom => ?_⟩
  obtain ⟨hE, C, N, hC, hNr, hN⟩ := hpre
  obtain ⟨hG, hW3, hWh, -, -, -⟩ := hE
  replace hroom : c.nreg ALLOC + κT * (P.n + 1) ≤ W := hroom
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hn : (Qof P).n = P.n := shear_n _ _
  have hn3 : 3 ≤ P.n := by have := hQ.1; rwa [hn] at this
  have hCm : C.m = P.n - 1 := by have := hC.2.2; omega
  set li := decide (Mountain.LeftInside (Qof P)) with hli_def
  have hli : li = true ↔ Mountain.LeftInside (Qof P) := decide_eq_true_iff
  -- the math
  obtain ⟨hok, hdeg, hwt, hlen, hcount⟩ := trans_math hG hC hN hli
  set L := transL li P.n (c0 C li) (triplesOf N) with hL
  set K₀ := N.chords.length with hK₀
  have hFK : (N.F (chainModel C) (Qof P)).ncard = K₀ := ncard_F hN.1.2.1
  rw [hFK] at hlen hcount
  have hcost := trans_cost_le hn3 hlen hcount
  set A := c.nreg ALLOC with hA
  -- 1. the bit
  obtain ⟨c₁, k₁, e₁, hk₁, b1, b2, F₁, m₁⟩ := orientT_exec hG hW3 c hw
  have hb₁ : c₁.nreg 190001 = if li then 1 else 0 := bit_eq b1 b2
  have hA₁ : c₁.nreg ALLOC = A := F₁.1 _ (by decide)
  -- 2. the shift
  obtain ⟨c₂, k₂, e₂, hk₂, v10, v14, v15, v16, v01, F₂, m₂⟩ :=
    c0S_exec hG hWh hC (li := li) c₁ e₁.wb_right hb₁ (by rw [hA₁]; unfold κT at hroom; omega)
  have hA₂ : c₂.nreg ALLOC = A := by rw [F₂.1 _ (by decide), hA₁]
  have hcore₂ : c₂.nreg 230002 = c.nreg (coreReg 2) := by
    rw [F₂.1 _ (by decide), F₁.1 _ (by decide)]; rfl
  have hlow₂ : ∀ a, a < A → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m₂ a (by rw [hA₁]; exact ha), m₁]
  have hNr₂ : Robust (c₂.nreg ALLOC) c₂.nmem (fun m => NFAt m (c₂.nreg 230002) N) := by
    rw [hA₂, hcore₂]; exact hNr.transport hlow₂
  -- 3. the filter
  obtain ⟨c₃, k₃, e₃, hk₃, hk₃', f21, f22, f36, f99, fCL, fD0, fD1, fmem, fg, frr, frm, fo⟩ :=
    filtS_exec c₂ e₂.wb_right (n := P.n) (c₀ := c0 C li) hNr₂ v01 (by rw [v10, hCm])
      v14 (by rw [v15, hCm]) v16 (by rw [hA₂]; omega)
  rw [hA₂] at f21 f22 f99 fCL fD0 fD1 fmem
  -- 4. the inputs of the build
  obtain ⟨c₄, k₄, e₄, hk₄, s0, s1, s2, F₄, m₄⟩ := setB_exec (P := P) c₃ e₃.wb_right
  have hA₄ : c₄.nreg ALLOC = A + 6 + 3 * K₀ := by rw [F₄.1 _ (by decide), f99]
  have hlenK : L.length ≤ K₀ := by
    have := transL_length_le li P.n (c0 C li) (triplesOf N)
    unfold triplesOf at this; rw [List.length_map] at this; exact this
  -- 5. the build
  have hdesc : ModelDescAt c₄.nmem A (Qof P) (interiorModel (Qof P)) := by
    right
    refine ⟨by rw [m₄, fD0], ?_, rfl⟩
    rw [m₄, fD1]
    cases h : li
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨fun h0 => absurd h0 (by norm_num), fun h1 => by
        have := hli.2 h1; rw [h] at this; exact absurd this (by simp)⟩
    · simp only [ite_true]
      exact ⟨fun _ => hli.1 h, fun _ => trivial⟩
  obtain ⟨c₅, k₅, e₅, hk₅, ⟨E, hperm, hsort, hE1, hE2, hNB, hNF⟩, g₅, F₅⟩ :=
    buildT_exec hG hWh c₄ e₄.wb_right (M := interiorModel (Qof P)) (L := L) (D := A)
      (B := A + 6) (by rw [hA₄]; exact ⟨by omega, fun h => by rw [m₄, fD0] at h; omega⟩)
      hdesc (Or.inr ⟨_, hQ, rfl⟩) hok (by rw [m₄]; exact fCL) (by rw [hA₄]; omega)
      (by rw [s0, f21]) (by rw [s1, f22]) (by rw [s2, f36])
      (by rw [hA₄]; unfold κT at hcost hroom; omega)
  -- 6. the registers of the driver
  obtain ⟨c₆, k₆, e₆, hk₆, w1, w2, w3, w4, w5, F₆, m₆⟩ := finT_exec (P := P) c₅ e₅.wb_right
  have hA₆ : c₆.nreg ALLOC = c₅.nreg ALLOC := F₆.1 _ (by decide)
  have h5 : ∀ r, 190021 ≤ r → r ≤ 190036 → c₅.nreg r = c₄.nreg r := fun r h1 h2 =>
    g₅ r (by rw [band_of_range (lo := 19) (by omega) (by omega)]; simp [bBuild, bSort, bSign])
      (by unfold ALLOC; omega) (by omega)
  have r1 : c₆.nreg 210001 = A := by
    rw [w1, h5 _ (by norm_num) (by norm_num), F₄.1 _ (by decide), f21]
  have r2 : c₆.nreg 210002 = A + 6 := by
    rw [w2, h5 _ (by norm_num) (by norm_num), F₄.1 _ (by decide), f22]
  have r3 : c₆.nreg 210003 = L.length := by
    rw [w3, h5 _ (by norm_num) (by norm_num), F₄.1 _ (by decide), f36]
  have hA₅ : c₄.nreg ALLOC ≤ c₅.nreg ALLOC := F₅.2.2.2.2.2.1
  have hlow₅ : ∀ a, a < c₄.nreg ALLOC → c₆.nmem a = c₃.nmem a := fun a ha => by
    rw [m₆, F₅.2.2.1 a ha, m₄]
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, ?_, ?_⟩
  · -- the cost
    show _ ≤ κT * (P.n + 1)
    omega
  · -- the invariant `Inv(p)`
    show c₆.nreg 210001 + 6 ≤ c₆.nreg ALLOC ∧ _
    refine ⟨by rw [r1, hA₆]; omega, ?_, L, E, ?_, ?_, ?_, ?_, ?_, hok, hperm, hsort, ?_, ?_, ?_,
      ?_⟩
    · show Robust (c₆.nreg ALLOC) c₆.nmem (fun m => ModelDescAt m (c₆.nreg 210001) (Qof P)
        (interiorModel (Qof P)))
      rw [r1]
      intro m' hm'
      have e0 : m' A = c₄.nmem A := by
        rw [hm' A (by rw [hA₆]; omega), hlow₅ A (by rw [hA₄]; omega), m₄]
      have e1 : m' (A + 1) = c₄.nmem (A + 1) := by
        rw [hm' (A + 1) (by rw [hA₆]; omega), hlow₅ (A + 1) (by rw [hA₄]; omega), m₄]
      rcases hdesc with ⟨h0, -⟩ | ⟨h0, h1, h2⟩
      · rw [m₄, fD0] at h0; omega
      · exact Or.inr ⟨by rw [e0]; exact h0, by rw [e1]; exact h1, h2⟩
    · show c₆.nreg 210003 = L.length; exact r3
    · show c₆.nreg 210002 + 3 * L.length ≤ c₆.nreg ALLOC
      rw [r2, hA₆]; omega
    · show Robust (c₆.nreg ALLOC) c₆.nmem (fun m => ChordListAt m (c₆.nreg 210002) L)
      rw [r2]
      intro m' hm' i hi
      obtain ⟨a1, a2, a3⟩ := fCL i hi
      have hq : ∀ q, q < 3 → m' (A + 6 + 3 * i + q) = c₃.nmem (A + 6 + 3 * i + q) := fun q hq => by
        rw [hm' _ (by rw [hA₆]; omega), hlow₅ _ (by rw [hA₄]; omega)]
      refine ⟨?_, ?_, ?_⟩
      · have := hq 0 (by norm_num); rw [Nat.add_zero] at this; rw [this]; exact a1
      · rw [hq 1 (by norm_num)]; exact a2
      · rw [hq 2 (by norm_num)]; exact a3
    · show c₆.nreg 210004 + 2 * L.length ≤ c₆.nreg ALLOC
      rw [w4, hA₆]; exact hE1
    · show Robust (c₆.nreg ALLOC) c₆.nmem (fun m => seg m (c₆.nreg 210004) (2 * L.length) = E)
      rw [w4]
      intro m' hm'
      rw [← hE2]
      unfold seg
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      rw [hm' _ (by rw [hA₆]; omega), m₆]
    · show NFWithin c₆.nmem (c₆.nreg 210005) (c₆.nreg ALLOC) _
      rw [w5, hA₆, m₆]; exact hNF
    · rw [F_buildNF]; exact hdeg
    · rw [F_buildNF]; exact hwt
    · exact hcnt P.n L.length K₀ (Nat.le_pow_clog (by norm_num) _) hcount hlenK
  · -- the frame
    have G₁ : Frame DrvR.drvBands c c₁ k₁ := frame_drv F₁ (fun r hr => by
        unfold B19 at hr; simp only [decide_eq_true_eq] at hr
        rw [band_of_range (lo := 19) (by omega) (by omega), mem_drvBands]; omega)
      (by decide) (fun a _ => by rw [m₁])
    have G₂ : Frame DrvR.drvBands c₁ c₂ k₂ := frame_drv F₂ (fun r hr => by
        unfold Bc0 Brute.Bm B19 WalkKey.Bk at hr
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        rw [mem_drvBands]; unfold bandOf; omega)
      (by decide) m₂
    have G₃ : Frame DrvR.drvBands c₂ c₃ k₃ := by
      refine ⟨fun r hr hra => fg r ?_ hra, fun r _ => by rw [frr], fun a ha => fmem a
        (by rw [hA₂] at ha; exact ha), fun a _ => by rw [frm], fo, by rw [f99, hA₂]; omega,
        by rw [f99, hA₂]; omega⟩
      by_contra hc
      push Not at hc
      exact hr (by rw [band_of_range (lo := 19) (by omega) (by omega), mem_drvBands]; omega)
    have G₄ : Frame DrvR.drvBands c₃ c₄ k₄ := frame_drv F₄ (fun r hr => by
        unfold BsetB at hr; simp only [decide_eq_true_eq] at hr
        rw [band_of_range (lo := 4) (by omega) (by omega), mem_drvBands]; omega)
      (by decide) (fun a _ => by rw [m₄])
    have G₅ : Frame DrvR.drvBands c₄ c₅ k₅ := F₅.mono (by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rw [mem_drvBands]
        rcases hb with rfl | rfl | rfl | rfl <;> simp [bBuild, bSort, bSign, bTrans]) le_rfl
    have G₆ : Frame DrvR.drvBands c₅ c₆ k₆ := frame_drv F₆ (fun r hr => by
        unfold BfinT at hr; simp only [decide_eq_true_eq] at hr
        rw [band_of_range (lo := 21) (by omega) (by omega), mem_drvBands]; omega)
      (by decide) (fun a _ => by rw [m₆])
    have := G₁.trans (G₂.trans (G₃.trans (G₄.trans (G₅.trans G₆))))
    simpa only [Finset.union_self] using this

/-- **The transition contract** for the count function of the driver. -/
theorem transSpec {X : MemCtx} {A : ℕ} (hA : 1 ≤ A) (B : ℕ) :
    DrvR.TransSpec X (DownMath.cnt A B) :=
  transSpec_of (transCnt_cnt hA B)

end exec

end

end DrvT

end Chazelle.Core
