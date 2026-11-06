module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvKey2Skip

/-!
# The sweep (WP-D), stage 3: the next key (task K), the other steps

* `pre`: the key `(kE, kH)` := the least candidate, `dF = 0`, the flag `kqB` (the best candidate
  is at the key, one `callOff`), the label list under construction (the best's labels if `kqB`,
  else empty): `pre_irs`;
* `finLab`: the label list is copied to `(kN, kL)` iff `kqB = 1 ∨ kqA = 1`: `fin_irs`;
* `writeLog`: the log record `(kE, kH, kN, kL … kL + 3)` at `lB + 7 lC`, `lC += 1`:
  `writeLog_irs`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## The program -/

/-- Set the key and reset the flags. -/
def setKL : List Instr :=
  [.copyN kE kqE, .copyN kH kqH, .constN dF 0, .constN kqB 0, .constN kqA 0]

/-- The flag "the best candidate is at the key". -/
def bestAt : Stmt :=
  kqIsOne bF (.seq (callOff (sw 2) kE kH bE bH cGW kqO) (.ifLtN K0 kqO .skip (block [.constN kqB 1])))

/-- Copy the best's labels. -/
def cpBestL : List Instr :=
  [.copyN kqN bN, .copyN kqL bL, .copyN (kqL + 1) (bL + 1), .copyN (kqL + 2) (bL + 2),
    .copyN (kqL + 3) (bL + 3)]

/-- The initial label list under construction. -/
def initLab : Stmt := .ifLtN K0 kqB (block cpBestL) (block [.constN kqN 0])

/-- The steps before the skipping. -/
def kqPre : Stmt := .seq (block setKL) (.seq bestAt initLab)

/-- Copy the label list under construction to `(kN, kL)`. -/
def cpLabL : List Instr :=
  [.copyN kN kqN, .copyN kL kqL, .copyN (kL + 1) (kqL + 1), .copyN (kL + 2) (kqL + 2),
    .copyN (kL + 3) (kqL + 3)]

/-- **The new label list** (iff `kqB = 1 ∨ kqA = 1`). -/
def finLab : Stmt := .ifLtN K0 kqB (block cpLabL) (.ifLtN K0 kqA (block cpLabL) .skip)

/-- The address of the log record: `kqX = lB + 7 lC`. -/
def logAddrL : List Instr :=
  [.addN kqY lC lC, .addN kqX kqY kqY, .addN kqX kqX kqY, .addN kqX kqX lC, .addN kqX kqX lB]

/-- The registers of the log record. -/
def logRegs : List ℕ := [kE, kH, kN, kL, kL + 1, kL + 2, kL + 3]

/-- **The log record.** -/
def writeLog : Stmt :=
  .seq (block logAddrL) (.seq (storeL kqX logRegs) (block [.addN lC lC K1]))

/-- The registers `pre` writes. -/
def PreR (r : ℕ) : Prop :=
  r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = kqA ∨ r = kqO ∨ r = kqO + 1 ∨ LblR kqN kqL r

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c d : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- A copy of a label list. -/
theorem kqLblOf_copy {c c' : Config} {N L N' L' : ℕ} (hN : c'.nreg N' = c.nreg N)
    (hL : ∀ i, i < 4 → c'.nreg (L' + i) = c.nreg (L + i)) : lblOf c' N' L' = lblOf c N L := by
  simp_all [lblOf, List.mem_range] 

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **The steps before the skipping.** -/
theorem pre_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hId : IInv W c₀ d)
    (hpk : PosW P J (d.nreg kqE) (d.nreg kqH))
    (hbP : d.nreg bF = 1 → PosW P J (d.nreg bE) (d.nreg bH))
    (hmin : d.nreg bF = 1 →
      offK P J (d.nreg kqE) (d.nreg kqH) ≤ offK P J (d.nreg bE) (d.nreg bH))
    (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ kqPre d 11030 (fun d' =>
      EFr PreR d d' ∧ d'.nreg kE = d.nreg kqE ∧ d'.nreg kH = d.nreg kqH ∧ d'.nreg dF = 0 ∧
      d'.nreg kqA = 0 ∧ d'.nreg kqB ≤ 1 ∧
      (d'.nreg kqB = 1 ↔ (d.nreg bF = 1 ∧
        offK P J (d.nreg bE) (d.nreg bH) = offK P J (d.nreg kqE) (d.nreg kqH))) ∧
      (d'.nreg kqB = 1 → d'.nreg kqN = d.nreg bN ∧ lblOf d' kqN kqL = lblOf d bN bL) ∧
      (d'.nreg kqB ≠ 1 → lblOf d' kqN kqL = [] ∧ d'.nreg kqN = 0)) := by
  have hW : 1 ≤ W := by omega
  unfold kqPre
  refine (IRS.seq (K₁ := 5) (K₂ := 11025) (IRS.block setKL hId (by
    simp only [setKL, okB, okI]
    exact ⟨iscr_sw' (by norm_num) (by norm_num), iscr_sw' (by norm_num) (by norm_num),
      ⟨iscr_sw' (by norm_num) (by norm_num), by omega⟩, ⟨iscr_sw' (by norm_num) (by norm_num),
        by omega⟩, ⟨iscr_sw' (by norm_num) (by norm_num), by omega⟩, trivial⟩)) ?_).mono le_rfl
    (fun _ h => h)
  rintro d₁ hI₁ hA₁ hA₁' hd₁
  have v1 : d₁.nreg kE = d.nreg kqE := by aesop
  have v2 : d₁.nreg kH = d.nreg kqH := by aesop
  have v3 : d₁.nreg dF = 0 := by rw [hd₁]; simp [setKL, regB, regI, upd, kE, kH, dF, kqB, kqA, sw]
  have v4 : d₁.nreg kqB = 0 := by rw [hd₁]; simp [setKL, regB, regI, upd, kE, kH, dF, kqB, kqA, sw]
  have v5 : d₁.nreg kqA = 0 := by rw [hd₁]; simp [setKL, regB, regI, upd, kE, kH, dF, kqB, kqA, sw]
  have fr1 : EFr PreR d d₁ := by
    rw [hd₁]; exact kqEfr_block _ (by simp [setKL, dstI, PreR]) (by omega_nf)
  have kp1 : ∀ r, ¬ PreR r → 240000 ≤ r ∧ r < 250000 → d₁.nreg r = d.nreg r := fun r h1 h2 =>
    fr1.kkeep h1 h2
  have eBF : d₁.nreg bF = d.nreg bF := kp1 _ (by omega_nf) (by kqr)
  have eBE : d₁.nreg bE = d.nreg bE := kp1 _ (by omega_nf) (by kqr)
  have eBH : d₁.nreg bH = d.nreg bH := kp1 _ (by omega_nf) (by kqr)
  have hK₁ := E.hK.fix hI₁
  -- the flag
  have hB : IRS P W c₀ bestAt d₁ 11015 (fun d₂ => EFr PreR d₁ d₂ ∧ d₂.nreg kqB ≤ 1 ∧
      (d₂.nreg kqB = 1 ↔ (d.nreg bF = 1 ∧
        offK P J (d.nreg bE) (d.nreg bH) = offK P J (d.nreg kqE) (d.nreg kqH))) ∧
      (∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA → d₂.nreg r = d₁.nreg r)) := by
    unfold bestAt
    refine kqIsOne_irs (K := 11011) hI₁ hK₁ (fun h1 => ?_) (fun h1 => ?_)
    · rw [eBF] at h1
      have hbp := hbP h1
      have hgw₁ : d₁.nreg cGW = gW J := E.gw' hI₁
      have hgw₁' : ((d₁.nreg cGW : ℕ) : ℝ) = (gW J : ℝ) := by rw [hgw₁]
      refine IRS.seq (K₁ := 11008) (K₂ := 3) (callOff_irs (dsc := sw 2) (ex := kE) (hx := kH)
        (ey := bE) (hy := bH) (g := cGW) (o := kqO) hI₁ (E.ctxW' hI₁)
        ⟨by omega_nf, by omega_nf, by omega_nf, by omega_nf,
          by omega_nf, by omega_nf, by omega_nf,
          by omega_nf, by omega_nf, by omega_nf,
          by omega_nf, by omega_nf⟩
        ⟨by omega_nf, by omega_nf⟩ (by rw [v1]; exact hpk.1)
        (by rw [eBE]; exact hbp.1) (by rw [hgw₁]; exact kqGW_lt J) (by rw [v1, v2]; exact hpk.2.1)
        (by rw [eBE, eBH]; exact hbp.2.1) (by rw [v1, v2]; exact hpk.2.2)
        (by rw [eBE, eBH]; exact hbp.2.2) (by omega)) ?_
      rintro d₂ hI₂ hA₂ hA₂' ⟨b1, -, k₂, ha₂, hm₂⟩
      rw [hgw₁', v1, v2, eBE, eBH] at b1
      change BitIs d₂ kqO (offK P J (d.nreg kqE) (d.nreg kqH) <
        offK P J (d.nreg bE) (d.nreg bH)) at b1
      have fr2 : EFr PreR d₁ d₂ := ⟨fun r hr hX hra => k₂ r hr
        (fun h => hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
        (fun h => hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hra, ha₂, hm₂⟩
      have kp2 : ∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA ∨ r = kqB → d₂.nreg r = d₁.nreg r := by
        intro r hr
        have hr' : r = 242400 ∨ r = 242401 ∨ r = 242451 ∨ r = 242488 ∨ r = 242487 := by
          grind [kE, kH, dF, kqA, kqB, sw]
        exact k₂ r (not_oracle_sw (by omega) (by omega)) (by omega_nf)
          (by omega_nf) (by omega_nf)
      have k02 : d₂.nreg K0 = 0 := (E.hK.fix hI₂).1
      by_cases h2 : d₂.nreg K0 < d₂.nreg kqO
      · rw [k02] at h2
        have hlt := b1.2.1 (by have := b1.1; omega)
        refine IRS.mono (K := 0 + 2) (IRS.ifT (by omega) (IRS.skip hI₂ rfl))
          (by norm_num) ?_
        grind
      · rw [k02] at h2
        have hnlt : ¬ offK P J (d.nreg kqE) (d.nreg kqH) < offK P J (d.nreg bE) (d.nreg bH) :=
          fun h => by have := b1.2.2 h; omega
        have heq : offK P J (d.nreg bE) (d.nreg bH) = offK P J (d.nreg kqE) (d.nreg kqH) :=
          le_antisymm (not_lt.1 hnlt) (hmin h1)
        refine IRS.mono (K := 1 + 2) (IRS.ifF (by omega) (IRS.block _ hI₂
          ⟨⟨iscr_sw' (by norm_num) (by norm_num), hW⟩, trivial⟩)) (by norm_num) ?_
        rintro d' hd'
        have w1 : d'.nreg kqB = 1 := by rw [hd']; simp [regB, regI]
        have w2 : ∀ r, r ≠ kqB → d'.nreg r = d₂.nreg r := fun r hr => by
          rw [hd']; simp [regB, regI, upd, hr]
        refine ⟨fr2.trans ⟨fun r _ hr _ => w2 r (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
          by grind, fun a _ => by rw [hd']⟩, by omega,
          ⟨fun _ => ⟨h1, heq⟩, fun _ => w1⟩, fun r hr => ?_⟩
        rw [w2 r (by rcases hr with rfl | rfl | rfl | rfl <;> kqr)]
        grind
    · rw [eBF] at h1
      exact ⟨EFr.refl _ _, by omega, ⟨fun h => by omega, fun h => absurd h.1 h1⟩,
        fun _ _ => rfl⟩
  refine IRS.seq (K₁ := 11015) (K₂ := 10) hB ?_
  rintro d₂ hI₂ hA₂ hA₂' ⟨fr2, hb1, hbiff, kp2⟩
  have hK₂ := E.hK.fix hI₂
  have eBN : d₂.nreg bN = d.nreg bN := (fr2.kkeep (by omega_nf) (by kqr)).trans
    (kp1 _ (by omega_nf) (by kqr))
  have eBL : ∀ i, i < 4 → d₂.nreg (bL + i) = d.nreg (bL + i) := fun i hi =>
    (fr2.kkeep (by unfold PreR; kqr) (by kqr)).trans (kp1 _ (by unfold PreR; kqr) (by kqr))
  have common : ∀ d' : Config, EFr PreR d₂ d' → d'.nreg kqB = d₂.nreg kqB →
      (∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA → d'.nreg r = d₂.nreg r) →
      EFr PreR d d' ∧ d'.nreg kE = d.nreg kqE ∧ d'.nreg kH = d.nreg kqH ∧ d'.nreg dF = 0 ∧
      d'.nreg kqA = 0 ∧ d'.nreg kqB ≤ 1 ∧
      (d'.nreg kqB = 1 ↔ (d.nreg bF = 1 ∧
        offK P J (d.nreg bE) (d.nreg bH) = offK P J (d.nreg kqE) (d.nreg kqH))) := by
    intro d' fr hB' hk
    refine ⟨fr1.trans (fr2.trans fr), ?_, ?_, ?_, ?_, by omega, by grind⟩
    · grind
    · grind
    all_goals grind
  unfold initLab
  by_cases h3 : d₂.nreg K0 < d₂.nreg kqB
  · rw [hK₂.1] at h3
    have hB1 : d₂.nreg kqB = 1 := by omega
    refine IRS.mono (K := 5 + 2) (IRS.ifT (by rw [hK₂.1]; exact h3) (IRS.block cpBestL hI₂ (by
      simp only [cpBestL, okB, okI]
      exact ⟨iscr_sw' (by norm_num) (by norm_num), iscr_sw' (by norm_num) (by norm_num),
        iscr_sw (by omega_nf) (by omega_nf),
        iscr_sw (by omega_nf) (by omega_nf),
        iscr_sw (by omega_nf) (by omega_nf), trivial⟩)))
      (by norm_num) ?_
    rintro d' hd'
    have fr3 : EFr PreR d₂ d' := by
      rw [hd']; exact kqEfr_block _ (by simp [cpBestL, dstI, PreR, LblR, kqN, kqL, sw]) (by omega_nf)
    have w0 : ∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA ∨ r = kqB → d'.nreg r = d₂.nreg r := by
      intro r hr
      rw [hd']
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp [cpBestL, regB, regI, upd, kE, kH, dF, kqA, kqB, kqN, kqL, sw]
    have wN : d'.nreg kqN = d.nreg bN := by
      rw [hd', ← eBN]; simp [cpBestL, regB, regI, upd, kqN, kqL, bN, bL, sw]
    have wL : ∀ i, i < 4 → d'.nreg (kqL + i) = d.nreg (bL + i) := by
      intro i hi
      rw [← eBL i hi, hd']
      interval_cases i <;> simp [cpBestL, regB, regI, upd, kqN, kqL, bN, bL, sw]
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := common d' fr3 (w0 _ (by simp)) (fun r hr => w0 r (by tauto))
    refine ⟨c1, c2, c3, c4, c5, c6, c7, fun _ => ⟨wN, kqLblOf_copy wN wL⟩, fun h => ?_⟩
    grind
  · rw [hK₂.1] at h3
    have hB0 : d₂.nreg kqB ≠ 1 := by omega
    refine IRS.mono (K := 1 + 2) (IRS.ifF (by omega) (IRS.block _ hI₂
      ⟨⟨iscr_sw' (by norm_num) (by norm_num), by omega⟩, trivial⟩)) (by norm_num) ?_
    rintro d' hd'
    have fr3 : EFr PreR d₂ d' := by
      rw [hd']; exact kqEfr_block _ (by simp [dstI, PreR, LblR]) (by omega_nf)
    have wN : d'.nreg kqN = 0 := by rw [hd']; simp [regB, regI]
    have w0 : ∀ r, r ≠ kqN → d'.nreg r = d₂.nreg r := fun r hr => by
      rw [hd']; simp [regB, regI, upd, hr]
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := common d' fr3 (w0 _ (by kqr))
      (fun r hr => w0 r (by rcases hr with rfl | rfl | rfl | rfl <;> kqr))
    grind [lblOf]

set_option maxHeartbeats 4000000 in
/-- **The new label list.** -/
theorem fin_irs (hId : IInv W c₀ d) (hK₀ : Consts c₀) (hB : d.nreg kqB ≤ 1)
    (hA : d.nreg kqA ≤ 1) :
    IRS P W c₀ finLab d 9 (fun d' =>
      (∀ r, ¬ LblR kN kL r → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem ∧
      ((d.nreg kqB = 1 ∨ d.nreg kqA = 1) →
        lblOf d' kN kL = lblOf d kqN kqL ∧ d'.nreg kN = d.nreg kqN) ∧
      (¬ (d.nreg kqB = 1 ∨ d.nreg kqA = 1) → ∀ r, d'.nreg r = d.nreg r)) := by
  have hK := hK₀.fix hId
  have cp : IRS P W c₀ (block cpLabL) d 5 (fun d' =>
      (∀ r, ¬ LblR kN kL r → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem ∧
      ((d.nreg kqB = 1 ∨ d.nreg kqA = 1) →
        lblOf d' kN kL = lblOf d kqN kqL ∧ d'.nreg kN = d.nreg kqN)) := by
    refine (IRS.block cpLabL hId (by
      simp only [cpLabL, okB, okI]
      exact ⟨iscr_sw' (by norm_num) (by norm_num), iscr_sw' (by norm_num) (by norm_num),
        iscr_sw (by omega_nf) (by omega_nf),
        iscr_sw (by omega_nf) (by omega_nf),
        iscr_sw (by omega_nf) (by omega_nf), trivial⟩)).mono le_rfl ?_
    rintro d' hd'
    have wN : d'.nreg kN = d.nreg kqN := by
      simp_all [cpLabL, regB, regI, upd, kN, kL, kqN, kqL, sw] 
    refine ⟨fun r hr => ?_, by rw [hd'], fun _ => ⟨kqLblOf_copy wN fun i hi => ?_, wN⟩⟩
    · have h0 : r ≠ kN := fun h => hr (Or.inl h)
      have h1 : r ≠ kL := fun h => hr (Or.inr ⟨by omega, by omega⟩)
      have h2 : r ≠ kL + 1 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
      have h3 : r ≠ kL + 2 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
      have h4 : r ≠ kL + 3 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
      rw [hd']
      simp only [cpLabL, regB, regI]
      simp_all
    · rw [hd']
      interval_cases i <;> aesop
  unfold finLab
  by_cases h1 : d.nreg K0 < d.nreg kqB
  · refine (IRS.ifT h1 cp).mono (by norm_num) (fun _ ⟨a, b, e⟩ => ⟨a, b, e, fun h => ?_⟩)
    omega
  · refine (IRS.ifF (K := 5 + 2) h1 ?_).mono (by norm_num) (fun _ h => h)
    by_cases h2 : d.nreg K0 < d.nreg kqA
    · refine (IRS.ifT h2 cp).mono le_rfl (fun _ ⟨a, b, e⟩ => ⟨a, b, e, fun h => ?_⟩)
      omega
    · refine IRS.ifF h2 (IRS.skip hId ⟨fun _ _ => rfl, rfl, fun h => ?_, fun _ _ => rfl⟩)
      rw [hK.1] at h1 h2; omega

set_option maxHeartbeats 4000000 in
/-- **The log record.** -/
theorem writeLog_irs (hId : IInv W c₀ d) (hK₀ : Consts c₀) (hA : c₀.nreg ALLOC ≤ d.nreg lB)
    (hW : d.nreg lB + 7 * d.nreg lC + 7 ≤ W) :
    IRS P W c₀ writeLog d 20 (fun d' =>
      d'.nreg lC = d.nreg lC + 1 ∧ (∀ r, r ≠ kqX → r ≠ kqY → r ≠ lC → d'.nreg r = d.nreg r) ∧
      d'.nmem (d.nreg lB + 7 * d.nreg lC) = d.nreg kE ∧
      d'.nmem (d.nreg lB + 7 * d.nreg lC + 1) = d.nreg kH ∧
      d'.nmem (d.nreg lB + 7 * d.nreg lC + 2) = d.nreg kN ∧
      (∀ i, i < 4 → d'.nmem (d.nreg lB + 7 * d.nreg lC + 3 + i) = d.nreg (kL + i)) ∧
      (∀ y, (y < d.nreg lB + 7 * d.nreg lC ∨ d.nreg lB + 7 * d.nreg lC + 7 ≤ y) →
        d'.nmem y = d.nmem y)) := by
  have hK := hK₀.fix hId
  
  unfold writeLog
  refine IRS.seq (K₁ := 5) (K₂ := 15) (IRS.block logAddrL hId (by
    simp only [lC, lB, sw, Nat.reduceAdd] at hW
    simp [logAddrL, okB, okI, regI, upd, kqX, kqY, lC, lB, sw, IScr]
    omega)) ?_
  rintro d₁ hI₁ - - hd₁
  have a1 : d₁.nreg kqX = d.nreg lB + 7 * d.nreg lC := by
    rw [hd₁]; simp [logAddrL, regB, regI, upd, kqX, kqY, lC, lB, sw]; ring
  have a2 : ∀ r, r ≠ kqX → r ≠ kqY → d₁.nreg r = d.nreg r := fun r h1 h2 => by
    rw [hd₁]; simp [logAddrL, regB, regI, upd, h1, h2]
  have m1 : d₁.nmem = d.nmem := by rw [hd₁]
  have hK₁ := hK₀.fix hI₁
  refine IRS.seq (K₁ := 14) (K₂ := 1) (storeL_irs (x := kqX) (iscr_sw' (by norm_num) (by norm_num))
    (by kqr) logRegs hI₁ hK₁.2.1 (by simp [logRegs, kE, kH, kN, kL, kqX, sw])
    (by omega) (by simp_all [logRegs] )) ?_
  rintro d₂ hI₂ - - ⟨s1, s2, s3⟩
  have hK₂ := hK₀.fix hI₂
  have eLC : d₂.nreg lC = d.nreg lC := (s3 _ (by kqr)).trans (a2 _ (by kqr) (by kqr))
  refine (IRS.block [.addN lC lC K1] hI₂ ⟨⟨iscr_sw' (by norm_num) (by norm_num),
    by rw [eLC, hK₂.2.1]; omega⟩, trivial⟩).mono le_rfl ?_
  rintro d' hd'
  have w2 : ∀ r, r ≠ lC → d'.nreg r = d₂.nreg r := fun r hr => by
    rw [hd']; simp [regB, regI, upd, hr]
  have wm : d'.nmem = d₂.nmem := by rw [hd']
  have kr : ∀ r, r ≠ kqX → r ≠ kqY → d₂.nreg r = d.nreg r := fun r h1 h2 =>
    (s3 r h1).trans (a2 r h1 h2)
  have st : ∀ i (h : i < logRegs.length),
      d'.nmem (d.nreg lB + 7 * d.nreg lC + i) = d.nreg (logRegs[i]) := by
    intro i h
    have h7 : i < 7 := by simpa [logRegs] using h
    rw [wm, ← a1, s1 i h, a2]
    · interval_cases i <;> simp [logRegs, kE, kH, kN, kL, kqX, sw]
    · interval_cases i <;> simp [logRegs, kE, kH, kN, kL, kqY, sw]
  refine ⟨by rw [hd']; simp [regB, regI, hK₂.2.1, eLC], fun r h1 h2 h3 => by grind,
    by simpa [logRegs] using st 0 (by simp [logRegs]), by simpa [logRegs] using st 1 (by simp [logRegs]),
    by simpa [logRegs] using st 2 (by simp [logRegs]), fun i hi => ?_,
    fun y hy => by rw [wm, s2 y (by rw [a1]; simpa [logRegs] using hy), m1]⟩
  have := st (3 + i) (by core_grind)
  rw [← Nat.add_assoc] at this
  rw [this]
  interval_cases i <;> simp [logRegs]

end

end SweepEv

end Chazelle.Core
