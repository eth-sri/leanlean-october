module

public import Chazelle.Core.SweepEvStopTasks2
public import Chazelle.Core.SweepEvKey2Sel

/-!
# The sweep (WP-D), stage 2: the parent scan (task P of `SweepEvStopTasks2`)

`parScan`: for every chord `i < K₂` of `N₂` (normal form at `sw 4`), read its end in the direction
of the code `oB` (`lpos` for `oB = 1`, `rpos` for `oB = 0`, i.e. `endPos N₂ i (1 - oB)`) and compare
its key with the key of the position `(pE2, pH2)` of the walk of `C₂` (`callOff` on the descriptor
`sw 21` with base `K0 = 0`: equal keys iff both strict bits are `0`); on equality set
`oPar := i + 1`.  Scratch registers `sw 4068 … 4075` (`ParR`).

**`parTask : ParTask`** (cost `11040 (K₂ + 1)`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop

@[expose] public section

/-! ## Registers and program -/

def prI : ℕ := sw 4068
def prK : ℕ := sw 4069
def prB : ℕ := sw 4070
def prX : ℕ := sw 4071
def prE : ℕ := sw 4072
def prH : ℕ := sw 4073
/-- The comparison bits `prO`, `prO + 1`. -/
def prO : ℕ := sw 4074

/-- `oPar = 0`, `i = 0`, `K₂`, the base of the chord records. -/
def prInitL : List Instr :=
  [.constN oPar 0, .constN prI 0, .loadN prK (sw 4), .addN prB (sw 4) K3, .loadN prB prB]

/-- The address of the record of chord `i`. -/
def prAdrL : List Instr :=
  [.addN prX prB prI, .addN prX prX prI, .addN prX prX prI, .addN prX prX prI, .addN prX prX prI]

/-- The end: height code `h + 1`, edge at `+ 2 - oB`. -/
def prEndL : List Instr :=
  [.loadN prH prX, .addN prH prH K1, .addN prX prX K2, .subN prX prX oB, .loadN prE prX]

/-- One chord. -/
def prBody : Stmt :=
  .seq (block prAdrL) (.seq (block prEndL) (.seq (callOff (sw 21) prE prH pE2 pH2 K0 prO)
    (.seq (.ifLtN K0 prO .skip (.ifLtN K0 (prO + 1) .skip (block [.addN oPar prI K1])))
      (block [.addN prI prI K1]))))

/-- **The parent scan.** -/
def parScan : Stmt := .seq (block prInitL) (.whileLtN prI prK prBody)

/-- The invariant of the scan. -/
def PrInv (P : Polygon) (J : Merge.Junction) (N : NF) (c d : Config) : Prop :=
  EFr ParR c d ∧ d.nreg prK = N.nChords ∧ d.nreg prB = c.nmem (c.nreg (sw 4) + 3) ∧
  d.nreg prI ≤ N.nChords ∧ d.nreg oPar ≤ d.nreg prI ∧
  (0 < d.nreg oPar → (chainModel J.right).key (Qof P) (endPos N (d.nreg oPar - 1)
      (1 - c.nreg oB)) = (chainModel J.right).key (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩) ∧
  (d.nreg oPar = 0 → ∀ i, i < d.nreg prI → (chainModel J.right).key (Qof P)
      (endPos N i (1 - c.nreg oB)) ≠ (chainModel J.right).key (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩)

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c d : Config} {J : Merge.Junction} {N₁ N₂ : NF}

theorem prR_par {r : ℕ} (h1 : sw 4068 ≤ r) (h2 : r < sw 4080) : ParR r := Or.inr ⟨h1, h2⟩

/-! ## Blocks -/

theorem prAdr_irs (hI : IInv W c₀ d) (hW : d.nreg prB + 5 * d.nreg prI ≤ W) :
    IRS P W c₀ (block prAdrL) d 5 (fun d' => d'.nreg prX = d.nreg prB + 5 * d.nreg prI ∧
      (∀ q, q ≠ prX → d'.nreg q = d.nreg q) ∧ d'.nmem = d.nmem) := by
  simp only [prB, prI, sw, Nat.reduceAdd] at hW
  refine (IRS.block prAdrL hI ?_).mono le_rfl ?_
  · simp [prAdrL, okB, okI, regI, upd, prX, prB, prI, sw, IScr]
    omega
  · rintro d' rfl
    simp [prAdrL, regB, regI, upd, prX, prB, prI, sw]
    refine ⟨by ring_nf, ?_⟩
    intro r ha
    simp [ha]

theorem prEnd_irs (hI : IInv W c₀ d) (hK1 : d.nreg K1 = 1) (hK2 : d.nreg K2 = 2)
    (hW : d.nreg prX + 2 ≤ W) (hh : d.nmem (d.nreg prX) + 1 ≤ W) :
    IRS P W c₀ (block prEndL) d 5 (fun d' => d'.nreg prH = d.nmem (d.nreg prX) + 1 ∧
      d'.nreg prE = d.nmem (d.nreg prX + 2 - d.nreg oB) ∧
      (∀ q, q ≠ prX → q ≠ prH → q ≠ prE → d'.nreg q = d.nreg q) ∧ d'.nmem = d.nmem) := by
  simp only [prX, K1, K2, sw, Nat.reduceAdd] at hK1 hK2 hW hh
  refine (IRS.block prEndL hI ?_).mono le_rfl ?_
  · simp [prEndL, okB, okI, regI, upd, prX, prH, prE, oB, K1, K2, sw, IScr, hK1, hK2]
    omega
  · rintro d' rfl
    simp [prEndL, regB, regI, upd, prX, prH, prE, oB, K1, K2, sw, hK1, hK2]
    intro r ha hb hc
    simp [ha, hb, hc]

/-! ## One chord -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem prBody_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hpe : c.nreg pE2 < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pE2, c.nreg pH2⟩)
    (hp6 : c.nreg pH2 = 0 → 6 ≤ c.nreg pE2) (hoB : c.nreg oB ≤ 1)
    (hId : IInv W c₀ d) (hv : PrInv P J N₂ c d) (hlt : d.nreg prI < d.nreg prK)
    (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ prBody d 11030 (fun d' => PrInv P J N₂ c d' ∧
      N₂.nChords - d'.nreg prI < N₂.nChords - d.nreg prI) := by
  obtain ⟨fr, hK, hB, hIK, hPI, hpos, hneg⟩ := hv
  set i := d.nreg prI
  rw [hK] at hlt
  have kp : ∀ r, ¬ ParR r → 240000 ≤ r ∧ r < 250000 → d.nreg r = c.nreg r :=
    fun r h1 h2 => fr.kkeep h1 h2
  have nPar : ∀ r, (r = sw 4 ∨ r = oB ∨ r = pE2 ∨ r = pH2) → ¬ ParR r ∧ 240000 ≤ r ∧ r < 250000 := by
    intro r hr
    simp only [oB, pE2, pH2, sw] at hr
    simp only [ParR, oPar, sw]
    omega
  have eB : d.nreg oB = c.nreg oB := kp _ (nPar _ (by simp)).1 (nPar _ (by simp)).2
  have eE2 : d.nreg pE2 = c.nreg pE2 := kp _ (nPar _ (by simp)).1 (nPar _ (by simp)).2
  have eH2 : d.nreg pH2 = c.nreg pH2 := kp _ (nPar _ (by simp)).1 (nPar _ (by simp)).2
  -- the normal form
  have hNW := E.nw₂' hI
  have hNA : NFAt c.nmem (c.nreg (sw 4)) N₂ := hNW.holds
  obtain ⟨-, hb2, -⟩ := Restore.nf_bounds hNW
  obtain ⟨r0, r1, r2, -, -⟩ := hNA.2.2.2.2.2.1 i hlt
  have hb2i := hb2 i hlt
  have hAW := hI.hw.1 ALLOC
  have hhn := (regOf_spec E.hNF₂).2.2.2.2.2.1 i hlt
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hPn : P.n ≤ W := by have := E.hWh; unfold hostWords at this; omega
  have hmem : ∀ x, x < c.nreg ALLOC → d.nmem x = c.nmem x := fr.2.2
  set Xa := c.nmem (c.nreg (sw 4) + 3) + 5 * i
  -- 1. the address
  refine IRS.seq (K₁ := 5) (K₂ := 11025) (prAdr_irs hId (by rw [hB]; omega)) ?_
  rintro d₁ hI₁ hA₁ hA₁' ⟨a1, a2, a3⟩
  rw [hB] at a1
  have hK₁ := E.hK.fix hI₁
  have m1 : ∀ x, x < c.nreg ALLOC → d₁.nmem x = c.nmem x := fun x hx => by rw [a3]; exact hmem x hx
  -- 2. the end
  refine IRS.seq (K₁ := 5) (K₂ := 11020) (prEnd_irs hI₁ hK₁.2.1 hK₁.2.2.2.2.2.1 (by rw [a1]; omega)
    (by rw [a1, m1 _ (by omega), r0]; unfold NF.nChords at hlt; omega)) ?_
  rintro d₂ hI₂ hA₂ hA₂' ⟨b1, b2, b3, b4⟩
  have eB₁ : d₁.nreg oB = c.nreg oB := (a2 _ (by unfold oB prX sw; omega)).trans eB
  rw [a1, m1 _ (by omega), r0] at b1
  rw [a1, eB₁] at b2
  have hs : (⟨d₂.nreg prE, d₂.nreg prH⟩ : WPos) = endPos N₂ i (1 - c.nreg oB) := by
    rw [b1, b2]
    unfold endPos
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hoB with h0 | h1
    · rw [h0, ite_eq_right (by norm_num), m1 _ (by omega)]
      simp only [Nat.sub_zero]
      rw [r2]; rfl
    · rw [h1, ite_eq_left (by norm_num), show Xa + 2 - 1 = Xa + 1 by omega, m1 _ (by omega), r1]; rfl
  have hA := E.hNF₂.2.2.1 i hlt
  have hpE : ProperPos (chainModel J.right) (Qof P) P.n ⟨d₂.nreg prE, d₂.nreg prH⟩ := by
    rw [hs]; unfold endPos; split_ifs
    · exact ⟨hA.1.2.1, hA.1.2.2.1, by show (N₂.chord i).h + 1 ≤ P.n; rw [← hQn]; omega⟩
    · exact ⟨hA.2.2.1, hA.2.2.2.1, by show (N₂.chord i).h + 1 ≤ P.n; rw [← hQn]; omega⟩
  have heE : d₂.nreg prE < (chainModel J.right).W.n := by
    have : (⟨d₂.nreg prE, d₂.nreg prH⟩ : WPos).edge = (endPos N₂ i (1 - c.nreg oB)).edge := by
      rw [hs]
    simp only at this
    rw [this]; unfold endPos; split_ifs
    · exact hA.1.1
    · exact hA.2.1
  have hH0 : d₂.nreg prH ≠ 0 := by rw [b1]; omega
  have k2 : ∀ q, q ≠ prX → q ≠ prH → q ≠ prE → d₂.nreg q = d.nreg q := fun q h1 h2 h3 =>
    (b3 q h1 h2 h3).trans (a2 q h1)
  have eE2₂ : d₂.nreg pE2 = c.nreg pE2 := (k2 _ (by unfold pE2 prX sw; omega)
    (by unfold pE2 prH sw; omega) (by unfold pE2 prE sw; omega)).trans eE2
  have eH2₂ : d₂.nreg pH2 = c.nreg pH2 := (k2 _ (by unfold pH2 prX sw; omega)
    (by unfold pH2 prH sw; omega) (by unfold pH2 prE sw; omega)).trans eH2
  have hK₂ := E.hK.fix hI₂
  have hn0 : 0 < (chainModel J.right).W.n := by omega
  -- 3. the comparison
  refine IRS.seq (K₁ := 11008) (K₂ := 12) (callOff_irs (dsc := sw 21) (ex := prE) (hx := prH)
    (ey := pE2) (hy := pH2) (g := K0) (o := prO) hI₂ (E.ctx2' hI₂)
    ⟨by norm_num [sw], by norm_num [sw], by unfold prE sw; norm_num, by unfold prE sw; norm_num,
      by unfold prH sw; norm_num, by unfold prH sw; norm_num, by unfold pE2 sw; norm_num,
      by unfold pE2 sw; norm_num, by unfold pH2 sw; norm_num, by unfold pH2 sw; norm_num,
      by unfold K0 sw; norm_num, by unfold K0 sw; norm_num⟩
    ⟨by unfold prO sw; norm_num, by unfold prO sw; norm_num⟩ heE (by rwa [eE2₂])
    (by rwa [hK₂.1]) hpE (by rwa [eE2₂, eH2₂]) (fun h => absurd h hH0)
    (by rwa [eE2₂, eH2₂]) (by omega)) ?_
  rintro d₃ hI₃ hA₃ hA₃' ⟨o1, o2, k₃, ha₃, hm₃⟩
  have hg0 : ((d₂.nreg K0 : ℕ) : ℝ) = 0 := by rw [hK₂.1]; simp
  rw [hg0, Restore.off_zero (Restore.key_nonneg hpE), Restore.off_zero (Restore.key_nonneg
    (by rwa [eE2₂, eH2₂])), hs, eE2₂, eH2₂] at o1 o2
  set kE' := (chainModel J.right).key (Qof P) (endPos N₂ i (1 - c.nreg oB))
  set kP := (chainModel J.right).key (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩
  have k3 : ∀ q, (q = oPar ∨ q = prI ∨ q = prK ∨ q = prB ∨ q = K0 ∨ q = K1) →
      d₃.nreg q = d.nreg q := by
    intro q hq
    have hq' : q = 244064 ∨ q = 244068 ∨ q = 244069 ∨ q = 244070 ∨ q = 240610 ∨ q = 240611 := by
      simp only [oPar, prI, prK, prB, K0, K1, sw] at hq; omega
    rw [k₃ q (not_oracle_sw (by omega) (by omega)) (by unfold prO sw; omega)
      (by unfold prO sw; omega) (by unfold ALLOC; omega)]
    exact k2 q (by unfold prX; unfold sw; omega) (by unfold prH sw; omega) (by unfold prE sw; omega)
  have frd3 : EFr ParR d d₃ := by
    refine ⟨fun r hb hr hra => ?_, hA₁.trans (hA₂.trans ha₃), fun a ha => ?_⟩
    · have h1 : r ≠ prX := by rintro rfl; exact hr (prR_par (by unfold prX sw; omega) (by unfold prX sw; omega))
      have h2 : r ≠ prH := by rintro rfl; exact hr (prR_par (by unfold prH sw; omega) (by unfold prH sw; omega))
      have h3 : r ≠ prE := by rintro rfl; exact hr (prR_par (by unfold prE sw; omega) (by unfold prE sw; omega))
      have h4 : r ≠ prO := by rintro rfl; exact hr (prR_par (by unfold prO sw; omega) (by unfold prO sw; omega))
      have h5 : r ≠ prO + 1 := by rintro rfl; exact hr (prR_par (by unfold prO sw; omega) (by unfold prO sw; omega))
      rw [k₃ r hb h4 h5 hra, k2 r h1 h2 h3]
    · rw [hm₃ a (lt_of_lt_of_le ha (hA₁.trans hA₂)), b4, a3]
  have hK₃ := E.hK.fix hI₃
  have eI3 : d₃.nreg prI = i := k3 _ (by simp)
  have eP3 : d₃.nreg oPar = d.nreg oPar := k3 _ (by simp)
  have hiW : i + 1 ≤ W := by
    have := hI.hw.2 (c.nreg (sw 4)); rw [hNA.1] at this; unfold NF.nChords at hlt; omega
  -- the final increment
  have incr : ∀ d₄ : Config, IInv W c₀ d₄ → EFr ParR d d₄ → d₄.nreg prI = i →
      d₄.nreg K1 = 1 → d₄.nreg prK = N₂.nChords → d₄.nreg prB = c.nmem (c.nreg (sw 4) + 3) →
      d₄.nreg oPar ≤ i + 1 →
      (0 < d₄.nreg oPar → (chainModel J.right).key (Qof P) (endPos N₂ (d₄.nreg oPar - 1)
        (1 - c.nreg oB)) = kP) →
      (d₄.nreg oPar = 0 → ∀ i', i' < i + 1 → (chainModel J.right).key (Qof P)
        (endPos N₂ i' (1 - c.nreg oB)) ≠ kP) →
      IRS P W c₀ (block [.addN prI prI K1]) d₄ 1 (fun d' => PrInv P J N₂ c d' ∧
        N₂.nChords - d'.nreg prI < N₂.nChords - i) := by
    intro d₄ hI₄ fr4 eI eK1 eK eB4 hP1 hP2 hP3
    refine (IRS.block _ hI₄ (by
      simp only [okB, okI]
      exact ⟨⟨iscr_sw' (by norm_num) (by norm_num), by rw [eI, eK1]; omega⟩, trivial⟩)).mono le_rfl ?_
    rintro d' hd'
    have w1 : d'.nreg prI = i + 1 := by rw [hd']; simp [regB, regI, eI, eK1]
    have w2 : ∀ r, r ≠ prI → d'.nreg r = d₄.nreg r := fun r hr => by
      rw [hd']; simp [regB, regI, upd, hr]
    have fr' : EFr ParR d₄ d' := ⟨fun r _ hr _ => w2 r (by
        rintro rfl; exact hr (prR_par (by unfold prI sw; omega) (by unfold prI sw; omega))),
      by rw [w2 ALLOC (by unfold ALLOC prI sw; omega)], fun a _ => by rw [hd']⟩
    have eP : d'.nreg oPar = d₄.nreg oPar := w2 _ (by unfold oPar prI sw; omega)
    refine ⟨⟨fr.trans (fr4.trans fr'), by rw [w2 _ (by unfold prK prI sw; omega), eK],
      by rw [w2 _ (by unfold prB prI sw; omega), eB4], by rw [w1]; omega, by rwa [w1, eP],
      fun h => by rw [eP] at h ⊢; exact hP2 h, fun h => by rw [w1]; rw [eP] at h; exact hP3 h⟩,
      by rw [w1]; omega⟩
  have k01 : d₃.nreg K0 = 0 := hK₃.1
  by_cases h1 : d₃.nreg K0 < d₃.nreg prO
  · -- the end is before the position
    have h1' := h1
    rw [k01] at h1'
    have hlt' : kE' < kP := o1.2.1 (by have := o1.1; omega)
    refine (IRS.seq (K₁ := 0 + 2) (K₂ := 1) (IRS.ifT h1 (IRS.skip hI₃ rfl)) ?_).mono (by norm_num)
      (fun _ h => h)
    rintro d₄ hI₄ - - rfl
    exact incr d₃ hI₃ frd3 eI3 hK₃.2.1 (by rwa [k3 _ (by simp)]) (by rwa [k3 _ (by simp)])
      (by rw [eP3]; omega) (fun h => by rw [eP3] at h ⊢; exact hpos h)
      (fun h i' hi' => by
        rw [eP3] at h
        rcases Nat.lt_or_ge i' i with h' | h'
        · exact hneg h i' h'
        · rw [show i' = i by omega]; exact ne_of_lt hlt')
  · have h1' := h1
    rw [k01] at h1'
    have hnlt : ¬ kE' < kP := fun h => by have := o1.2.2 h; omega
    by_cases h2 : d₃.nreg K0 < d₃.nreg (prO + 1)
    · have h2' := h2
      rw [k01] at h2'
      have hgt : kP < kE' := o2.2.1 (by have := o2.1; omega)
      refine (IRS.seq (K₁ := 0 + 2 + 2) (K₂ := 1) (IRS.ifF h1
        (IRS.ifT h2 (IRS.skip hI₃ rfl))) ?_).mono (by norm_num) (fun _ h => h)
      rintro d₄ hI₄ - - rfl
      exact incr d₃ hI₃ frd3 eI3 hK₃.2.1 (by rwa [k3 _ (by simp)])
        (by rwa [k3 _ (by simp)]) (by rw [eP3]; omega)
        (fun h => by rw [eP3] at h ⊢; exact hpos h)
        (fun h i' hi' => by
          rw [eP3] at h
          rcases Nat.lt_or_ge i' i with h' | h'
          · exact hneg h i' h'
          · rw [show i' = i by omega]; exact ne_of_gt hgt)
    · have h2' := h2
      rw [k01] at h2'
      have hngt : ¬ kP < kE' := fun h => by have := o2.2.2 h; omega
      have heq : kE' = kP := le_antisymm (not_lt.1 hngt) (not_lt.1 hnlt)
      refine (IRS.seq (K₁ := 1 + 2 + 2) (K₂ := 1) (IRS.ifF h1
        (IRS.ifF h2 (IRS.block [.addN oPar prI K1] hI₃ (by
          simp only [okB, okI]
          exact ⟨⟨iscr_sw' (by norm_num) (by norm_num), by rw [eI3, hK₃.2.1]; omega⟩, trivial⟩)))) ?_).mono (by norm_num)
        (fun _ h => h)
      rintro d₄ hI₄ - - hd₄
      have w1 : d₄.nreg oPar = i + 1 := by rw [hd₄]; simp [regB, regI, eI3, hK₃.2.1]
      have w2 : ∀ r, r ≠ oPar → d₄.nreg r = d₃.nreg r := fun r hr => by
        rw [hd₄]; simp [regB, regI, upd, hr]
      have fr4 : EFr ParR d₃ d₄ := ⟨fun r _ hr _ => w2 r (fun h => hr (Or.inl h)),
        by rw [w2 ALLOC (by unfold ALLOC oPar sw; omega)], fun a _ => by rw [hd₄]⟩
      exact incr d₄ hI₄ (frd3.trans fr4) (by rw [w2 _ (by unfold prI oPar sw; omega), eI3])
        (by rw [w2 _ (by unfold K1 oPar sw; omega), hK₃.2.1])
        (by rwa [w2 _ (by unfold prK oPar sw; omega), k3 _ (by simp)])
        (by rwa [w2 _ (by unfold prB oPar sw; omega), k3 _ (by simp)])
        (by rw [w1]) (fun _ => by rwa [w1, Nat.add_sub_cancel])
        (fun h => by rw [w1] at h; omega)

/-! ## The scan -/

set_option maxHeartbeats 16000000 in
theorem parScan_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hpe : c.nreg pE2 < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pE2, c.nreg pH2⟩)
    (hp6 : c.nreg pH2 = 0 → 6 ≤ c.nreg pE2) (hoB : c.nreg oB ≤ 1)
    (hroom : c.nreg ALLOC + 11040 * (N₂.nChords + 1) ≤ W) :
    IRS P W c₀ parScan c (11040 * (N₂.nChords + 1)) (ParOut P J N₂ c) := by
  have hK := E.hK.fix hI
  have hNW := E.nw₂' hI
  have hNA : NFAt c.nmem (c.nreg (sw 4)) N₂ := hNW.holds
  obtain ⟨hb0, -⟩ := Restore.nf_bounds hNW
  have hAW := hI.hw.1 ALLOC
  unfold parScan
  have k3 : c.nreg K3 = 3 := hK.2.2.2.2.2.2
  refine (IRS.seq (K₁ := 5) (K₂ := 11032 * N₂.nChords + 2) (IRS.block prInitL hI (by
    simp only [sw, K3, Nat.reduceAdd] at k3 hb0 hAW
    simp [prInitL, okB, okI, regI, upd, oPar, prI, prK, prB, K3, sw, IScr, k3]
    omega)) ?_).mono (by omega) (fun _ h => h)
  rintro d hId hA hA' hd
  have v0 : d.nreg oPar = 0 := by rw [hd]; simp [prInitL, regB, regI, upd, oPar, prI, prK, prB, sw]
  have vI : d.nreg prI = 0 := by rw [hd]; simp [prInitL, regB, regI, upd, oPar, prI, prK, prB, sw]
  have vK : d.nreg prK = N₂.nChords := by
    rw [hd]; simp [prInitL, regB, regI, upd, oPar, prI, prK, prB, sw]; exact hNA.1
  have vB : d.nreg prB = c.nmem (c.nreg (sw 4) + 3) := by
    rw [hd]; simp [prInitL, regB, regI, upd, oPar, prI, prK, prB, K3, sw]
    have := hK.2.2.2.2.2.2; simp only [K3, sw] at this; rw [this]
  have frd : EFr ParR c d := by
    rw [hd]
    refine ⟨fun r _ hr _ => regB_other _ _ _ (fun i hi h => hr ?_), ?_, fun _ _ => rfl⟩
    · simp only [prInitL, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] at h <;> subst h <;>
        simp only [ParR, oPar, prI, prK, prB, sw] <;> norm_num
    · exact (regB_other _ _ _ (fun i hi h => by
        simp only [prInitL, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] at h <;>
          simp only [ALLOC, oPar, prI, prK, prB, sw] at h <;> omega)).ge
  have inv0 : PrInv P J N₂ c d := ⟨frd, vK, vB, by rw [vI]; omega, by rw [v0, vI],
    fun h => by rw [v0] at h; omega, fun _ i h => by rw [vI] at h; omega⟩
  refine (IRS.while (PrInv P J N₂ c) (fun d => N₂.nChords - d.nreg prI) 11030
    (fun d hv h => by have := hv.2.1; omega)
    (fun d hId hv hlt hroom => prBody_irs E hI hpe hpp hp6 hoB hId hv hlt hroom) hId inv0
    (by rw [vI]; omega)).mono (by rw [vI]; omega) ?_
  rintro d' ⟨⟨fr', hK', hB', hIK', hPI, hpos, hneg⟩, hex⟩
  rw [hK'] at hex
  refine ⟨by omega, hpos, fun h i hi => hneg h i (by omega), fr'.2.2, fr'.2.1,
    fun r hb hr hra => fr'.1 r hb hr hra⟩

/-- **Task P: the parent scan.** -/
theorem parTask : ParTask :=
  ⟨parScan, 11040, fun _ _ _ _ _ _ _ _ _ _ _ _ E hI hpe hpp hp6 hoB hroom =>
    parScan_irs E hI hpe hpp hp6 hoB hroom⟩

end

end SweepEv

end Chazelle.Core
