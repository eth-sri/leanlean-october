module

public import Chazelle.Core.SweepIoCand1TabSpec
public import Chazelle.Core.SweepIoCand1E
public import Chazelle.Core.SweepIoCand1G

/-!
# The sweep RAM (WP-D), answers: the table step of a side-1 query

`tabB`: the block `tabL` loads the endpoint-table entry `j = qJ` (three words `(f, e, h)` at
`sw 302 + 3 j`) into `tbF, tbE, tbH` (scratch `sw 4820 … 4824`) and the tag `2` into `tbT`; if
`f ≥ 1` (so `f = 1`), the position `(e, h)` of the walk of `C` (descriptor `sw 2`) is offered to the
accumulator `accA` (`offer_irs`).  By `TabOK` (from `AEnv.hout`) the offered point is the first hit
of `C`; with `f = 0` the first hit of `C` is that of `C₂`.

**`tabStep : TabStepSpec`**.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The address register of the table step. -/
def tbA : ℕ := sw 4820
/-- The flag of the table entry. -/
def tbF : ℕ := sw 4821
/-- The walk edge of the table entry. -/
def tbE : ℕ := sw 4822
/-- The height code of the table entry. -/
def tbH : ℕ := sw 4823
/-- The tag `2` (the walk of `C`). -/
def tbT : ℕ := sw 4824

/-- The loads of the table entry `qJ`. -/
def tabL : List Instr :=
  [.copyN tbA (sw 302), .addN tbA tbA qJ, .addN tbA tbA qJ, .addN tbA tbA qJ, .loadN tbF tbA,
    .addN tbA tbA K1, .loadN tbE tbA, .addN tbA tbA K1, .loadN tbH tbA, .constN tbT 2]

/-- **The table step.** -/
def tabB : Stmt := .seq (block tabL) (.ifLtN tbF K1 .skip (offer accA (sw 2) tbE tbH tbT qD))

/-- The cost of the table step. -/
def tabK : ℕ := offerK + 20

theorem tabL_val (m f : ℕ → ℕ) (hk : f K1 = 1) :
    regB m tabL f tbA = f (sw 302) + 3 * f qJ + 2 ∧
      regB m tabL f tbF = m (f (sw 302) + 3 * f qJ) ∧
      regB m tabL f tbE = m (f (sw 302) + 3 * f qJ + 1) ∧
      regB m tabL f tbH = m (f (sw 302) + 3 * f qJ + 2) ∧
      regB m tabL f tbT = 2 ∧
      ∀ q, (q < tbA ∨ tbT < q) → regB m tabL f q = f q := by
  have hk' : f 240611 = 1 := hk
  simp only [tabL, regB, regI, upd, tbA, tbF, tbE, tbH, tbT, sw, qJ, K1]
  norm_num [hk']
  refine ⟨by ring, by ring_nf, by ring_nf, by ring_nf, fun q hq => ?_⟩
  split_ifs <;> first | rfl | omega

theorem tabL_ok {W : ℕ} (m f : ℕ → ℕ) (hk : f K1 = 1)
    (hW : f (sw 302) + 3 * f qJ + 2 ≤ W) : okB W m tabL f := by
  have hk' : f 240611 = 1 := hk
  have hW' : f 240302 + 3 * f 243227 + 2 ≤ W := hW
  have s : ∀ i, 4820 ≤ i → i ≤ 4824 → IScr (sw i) := fun i h1 h2 =>
    iscr_sw (by unfold sw; omega) (by unfold sw; omega)
  simp only [tabL, okB, okI, regI, upd, tbA, tbF, tbE, tbH, tbT, qJ, K1, sw]
  norm_num [hk']
  refine ⟨s 4820 (by norm_num) (by norm_num), ⟨s 4820 (by norm_num) (by norm_num), ?_⟩,
    ⟨s 4820 (by norm_num) (by norm_num), ?_⟩, ⟨s 4820 (by norm_num) (by norm_num), ?_⟩,
    s 4821 (by norm_num) (by norm_num), ⟨s 4820 (by norm_num) (by norm_num), ?_⟩,
    s 4822 (by norm_num) (by norm_num), ⟨s 4820 (by norm_num) (by norm_num), ?_⟩,
    s 4823 (by norm_num) (by norm_num), ⟨s 4824 (by norm_num) (by norm_num), ?_⟩⟩ <;> omega

set_option maxHeartbeats 4000000 in
/-- **The table step of a regular endpoint query of side `1`.** -/
theorem tabStep : TabStepSpec := by
  refine ⟨tabB, tabK, ?_⟩
  intro P W X Ok J H N₁ N₂ E c₀ c L z hA hI hj hz hd hzR hzs hzt hacc hroom
  have hK := hA.hK.fix hI
  have k1 : c.nreg K1 = 1 := hK.2.1
  set j := c.nreg qJ with hjdef
  set σ := dirOf (c.nreg qD) with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; unfold dirOf; split_ifs <;> simp
  have hB : c.nreg (sw 302) = rd c₀ bSweep 302 := hI.hin _ (by unfold IFix sw; omega)
  have htw := hA.htabw
  have hAl := hI.hA
  have hroom' : c.nreg ALLOC + offerK + 20 ≤ W := by unfold tabK at hroom; omega
  have hW : c.nreg (sw 302) + 3 * c.nreg qJ + 2 ≤ W := by
    rw [hB]; unfold offerK at hroom'; omega
  have hmem : ∀ i, i ≤ 2 → c.nmem (c.nreg (sw 302) + 3 * c.nreg qJ + i) =
      c₀.nmem (rd c₀ bSweep 302 + 3 * j + i) := by
    intro i hi
    rw [hB]
    exact hI.hm _ (by omega)
  -- the facts of the table entry
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTab, hFl⟩ := hA.hout
  have hT := hTab j hj (by rw [hz]; exact hzR) (by rw [hz]; exact hzs) (by rw [hz]; exact hzt)
  obtain ⟨hf1, hPW⟩ := hFl j hj
  have hfree : FreeAt J.whole z σ := by
    have := hT.1; rw [hz, hd] at this; exact this
  have hz2 : z.2 ≤ J.whole.top.2 := J.whole.snd_le_top_of_mem_set (J.right_set_subset hzR)
  obtain ⟨hτ0, hon⟩ := hit_onCB J.whole hz2 hσ hfree
  -- the loads
  refine IRS.seq (K₁ := 10) (K₂ := offerK + 2) (IRS.block tabL hI (tabL_ok _ _ k1 hW)) ?_ |>.mono
    (by unfold tabK; omega) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  obtain ⟨-, vF, vE, vH, vT, vo⟩ := tabL_val c.nmem c.nreg k1
  have o1 : ∀ q, (q < tbA ∨ tbT < q) → c₁.nreg q = c.nreg q := fun q hq => by
    rw [hc1]; exact vo q hq
  have m1 : c₁.nmem = c.nmem := by rw [hc1]
  have f1 : c₁.nreg tbF = c₀.nmem (rd c₀ bSweep 302 + 3 * j) := by
    rw [hc1]; simp only; rw [vF]; simpa using hmem 0 (by norm_num)
  have e1 : c₁.nreg tbE = c₀.nmem (rd c₀ bSweep 302 + 3 * j + 1) := by
    rw [hc1]; simp only; rw [vE]; exact hmem 1 (by norm_num)
  have h1 : c₁.nreg tbH = c₀.nmem (rd c₀ bSweep 302 + 3 * j + 2) := by
    rw [hc1]; simp only; rw [vH]; exact hmem 2 (by norm_num)
  have t1 : c₁.nreg tbT = 2 := by rw [hc1]; simp only; rw [vT]
  have a1 : c₁.nreg ALLOC = c.nreg ALLOC := o1 _ (by unfold ALLOC tbA sw; omega)
  have k1₁ : c₁.nreg K1 = 1 := (hA.hK.fix hI₁).2.1
  have qD1 : c₁.nreg qD = c.nreg qD := o1 _ (by unfold qD tbA sw; omega)
  have acc1 : AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z σ L c₁ :=
    hacc.transport (fun i hi => o1 _ (by unfold accA tbA sw; omega))
  have fr1 : ∀ r, ¬ (sw 4000 ≤ r ∧ r < sw 5000) → c₁.nreg r = c.nreg r := fun r hr =>
    o1 r (by unfold tbA tbT sw at *; omega)
  refine IRS.ite (fun hlt => ?_) (fun hge => ?_)
  · -- no entry: the first hit of `C` is that of `C₂`
    have hf0 : c₀.nmem (rd c₀ bSweep 302 + 3 * j) ≠ 1 := by rw [← f1]; omega
    have hT2 := hT.2
    unfold Sweep.tabOf at hT2
    rw [ite_eq_right hf0] at hT2
    rw [hz, hd] at hT2
    refine IRS.skip hI₁ ⟨⟨L, acc1, subset_rfl, fun τ h => Or.inl h, Or.inr hT2⟩,
      fun r _ _ _ h3 _ => fr1 r h3, by rw [a1], fun a _ => by rw [m1]⟩
  · -- an entry: offer the first hit of `C`
    have hf : c₀.nmem (rd c₀ bSweep 302 + 3 * j) = 1 := by rw [← f1]; rw [← f1] at hf1; omega
    obtain ⟨hPe, hPp, -⟩ := hPW hf
    have hT2 := hT.2
    unfold Sweep.tabOf at hT2
    rw [ite_eq_left hf] at hT2
    obtain ⟨-, hpt, -⟩ := hT2
    rw [hz, hd] at hpt
    have hM2 : ModB J (c.nreg bL) (c.nreg bR) (c₁.nreg tbT) = J.whole := by
      rw [t1]; simp [ModB]
    have hW3 : P.n + 3 ≤ W := by have := hA.hWh; unfold hostWords at this; omega
    have sw' : ∀ i, i < 10000 → 240000 ≤ sw i ∧ sw i < 250000 := fun i hi => by
      unfold sw; omega
    refine (offer_irs (A := accA) (dsc := sw 2) (e := tbE) (h := tbH) (t := tbT) (dR := qD)
      (Mod := ModB J (c.nreg bL) (c.nreg bR)) (R₀ := J.whole.radius) (z := z) (L := L)
      (τ := J.whole.hitParam z σ) hI₁ hA.hK hA.hG hW3
      (by unfold accA sw; omega)
      (by unfold tbE tbH tbT qD sw; omega)
      (by unfold accA tbE tbH tbT qD sw; omega)
      (by rw [qD1]; exact acc1) (by rw [t1])
      (by rw [hM2]; exact AEnv.ctxW hA hI₁) (by rw [hM2])
      (by rw [hM2, e1]; exact hPe) (by rw [hM2, e1, h1]; exact hPp)
      (by rw [hM2, e1, h1, qD1]; exact hpt) (Cand1.abs_lt_whole hzR).2
      (by rw [a1]; omega)).mono le_rfl ?_
    rintro c' ⟨hacc', hk, hal, hm⟩
    rw [qD1] at hacc'
    refine ⟨⟨insert (J.whole.hitParam z σ) L, hacc', Set.subset_insert _ _, fun τ hτ => ?_,
      Or.inl (Set.mem_insert _ _)⟩, fun r hr0 hr1 hr2 hr3 hr4 => ?_, by rw [← a1]; exact hal,
      fun a ha => by rw [hm a (by rw [a1]; exact ha), m1]⟩
    · rcases (Set.mem_insert_iff.1 hτ) with rfl | h
      · exact Or.inr ⟨hτ0, hon⟩
      · exact Or.inl h
    · rw [hk r hr0 (by unfold accA sw at *; omega) hr4]
      exact fr1 r hr3

end

end SweepIo

end Chazelle.Core
