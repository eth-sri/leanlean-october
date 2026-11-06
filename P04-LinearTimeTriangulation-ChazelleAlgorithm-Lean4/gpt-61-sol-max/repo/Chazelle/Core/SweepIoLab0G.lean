module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoLab0R

/-!
# The sweep RAM (WP-D), answers: the label candidates of a side-0 query, the gap regions

`gapS`: the list address `gL` (the allocator), the inputs of the local hit in the model of `C₂`
(model descriptor `sw 31`, normal form `sw 4`), then part 1 of the local hit (`lh1`) at the walk
positions `(2 m₂ + 6, 0)` and `(6, 0)` of `C₂` (the two copies of the top at the slit): the three
regions `nbrRegs N₂ j` of each, stored as six words at `gL`.
-/

namespace Chazelle.Core

namespace SweepIo

namespace Lab0

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Chain (sideInArc)
open OracleQ (sk ek)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The setup of the gap part. -/
def gS0 : List Instr :=
  [.copyN gL ALLOC, .copyN lMD (sw 31), .addN lCD lMD K1, .copyN lNF (sw 4),
    .subN lE (sw 34) K1, .constN lH 0]

/-- **The gap regions.** -/
def gapS : Stmt := .seq (block gS0) (.seq lh1 (.seq (block [.constN lE 6]) lh1))

/-- The cost of the gap part. -/
def gapK (T : ℕ) : ℕ := 6 + (lh1K T + (1 + lh1K T))

/-- **An answer of double identification** for the key `p` (parameter `0`). -/
def LocAt (C : Chain) (Q : Polygon) (N : NF) (p j : ℕ) : Prop :=
  j < N.arcs.length ∧
    (¬ (chainModel C).IsCut (N.F (chainModel C) Q) (p : ℝ) →
      N.F (chainModel C) Q = ∅ ∨
        sideInArc (sk (chainModel C) Q N j) (ek (chainModel C) Q N j) (p : ℝ)) ∧
    ((chainModel C).IsCut (N.F (chainModel C) Q) (p : ℝ) →
      sk (chainModel C) Q N j = (p : ℝ) ∨ ek (chainModel C) Q N j = (p : ℝ))

section
variable (M : Model) (Q : Polygon)
theorem key_zero (p : ℕ) : M.key Q ⟨p, 0⟩ = (p : ℝ) := by
  simp_all

theorem pp_zero (n p : ℕ) : ProperPos M Q n ⟨p, 0⟩ := by
  have : M.param Q ⟨p, 0⟩ = 0 := rfl
  exact ⟨by rw [this], by simp_all, Nat.zero_le _⟩


end

section
variable (m f : ℕ → ℕ)
theorem gS0_val :
    regB m gS0 f gL = f ALLOC ∧ regB m gS0 f lMD = f (sw 31) ∧
    regB m gS0 f lCD = f (sw 31) + f K1 ∧ regB m gS0 f lNF = f (sw 4) ∧
    regB m gS0 f lE = f (sw 34) - f K1 ∧ regB m gS0 f lH = 0 ∧
    ∀ q, q ≠ gL → ¬ (sw 1100 ≤ q ∧ q ≤ sw 1119) → regB m gS0 f q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q h1 h2 => regB_other _ _ _ (fun i hi => ?_)⟩
  · aesop
  · aesop
  · aesop
  · aesop
  · aesop
  · aesop
  · simp only [gS0, List.mem_cons, List.not_mem_nil, or_false] at hi
    core_grind

theorem gS0_ok (hb : f (sw 31) + f K1 ≤ W) : okB W m gS0 f := by
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  have hb' : f 240031 + f 240611 ≤ W := hb
  simp only [gS0, okB, okI, regI, upd, gL, lMD, lCD, lNF, lE, lH, K1, ALLOC, sw]
  simp_all +arith


end

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The gap regions**: the three regions at each of the walk vertices `2 m₂ + 6` and `6` of
`C₂`, as six words at the list address `gL`. -/
theorem gap_irs {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {E : ℕ} (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c)
    (hroom : c.nreg ALLOC + gapK (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ gapS c (gapK (c₀.nreg TLR)) (fun c' =>
      c'.nreg gL = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ gL → ¬ (sw 1100 ≤ r ∧ r ≤ sw 1119) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ∃ j₁ j₂, LocAt J.right (Qof P) N₂ (2 * J.right.m + 6) j₁ ∧
        LocAt J.right (Qof P) N₂ 6 j₂ ∧
        ∀ i, i < 3 → c'.nmem (c.nreg ALLOC + i) = (Sweep.nbrRegs N₂ j₁).getD i 0 ∧
          c'.nmem (c.nreg ALLOC + 3 + i) = (Sweep.nbrRegs N₂ j₂).getD i 0) := by
  have hS := sideD₂ hA
  have hK := hA.hK
  have hfix : ∀ q, IFix q → c.nreg q = c₀.nreg q := fun q hq => hI.hin q hq
  have e31 : c.nreg (sw 31) = c₀.nreg (sw 31) := hfix _ (by omega_nf)
  have e4 : c.nreg (sw 4) = c₀.nreg (sw 4) := hfix _ (by omega_nf)
  have e34 : c.nreg (sw 34) = 2 * J.right.m + 7 := (hfix _ (by omega_nf)).trans hS.hnr
  have k1 : c.nreg K1 = 1 := (hK.fix hI).2.1
  have hmdW : c.nreg (sw 31) + c.nreg K1 ≤ W := by
    rw [e31, k1]; have := hS.hmwf.1; ram_grind
  unfold gapS gapK
  unfold gapK at hroom
  refine IRS.seq (K₁ := 6) (K₂ := lh1K (c₀.nreg TLR) + (1 + lh1K (c₀.nreg TLR)))
    ((IRS.block gS0 hI (gS0_ok _ _ hmdW)).mono (by simp [gS0]) (fun _ h => h)) ?_
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨v1, v2, v3, v4, v5, v6, vo⟩ := gS0_val c.nmem c.nreg
  set c₁ : Config := { c with nreg := regB c.nmem gS0 c.nreg } with hc₁
  have eA1 : c₁.nreg ALLOC = c.nreg ALLOC :=
    vo ALLOC (by omega_nf) (by omega_nf)
  have eT1 : c₁.nreg TLR = c₀.nreg TLR := hI₁.hin _ (by omega_nf)
  have hL₁ : LCtx P W J.right N₂ E c₁ := lctx_of hS hI₁ hA.htab hA.hTB hA.hTW
    (by ram_grind)
    (by ram_grind)
    (by ram_grind)
  have hE1 : c₁.nreg lE = 2 * J.right.m + 6 := by
    grind
  have hH1 : c₁.nreg lH = 0 := v6
  have hn₂ : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
  refine IRS.seq (K₁ := lh1K (c₀.nreg TLR)) (K₂ := 1 + lh1K (c₀.nreg TLR))
    ((lh1_irs hI₁ hK hL₁ (by omega) (by rw [hH1]; exact pp_zero _ _ _ _)
      (by ram_grind)).mono (by rw [eT1]) (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hj1, hl1, hl2, hLL2, hAl2, hlist2, hm2, fr2, -, -, -⟩
  have fr2' : ∀ q, bandOf q ∉ oracleBands → ¬ (sw 1108 ≤ q ∧ q ≤ sw 1119) → q ≠ ALLOC →
      c₂.nreg q = c₁.nreg q := fun q h1 h2 h3 => fr2 q h1 h2 h3
  refine IRS.seq (K₁ := 1) (K₂ := lh1K (c₀.nreg TLR))
    (IRS.block [.constN lE 6] hI₂ ⟨⟨iscr_sw (by omega_nf) (by omega_nf),
      by omega⟩, trivial⟩) ?_
  rintro c₃ hI₃ hA₃ hA₃' rfl
  set c₃ : Config := { c₂ with nreg := regB c₂.nmem [.constN lE 6] c₂.nreg } with hc₃
  have o3 : ∀ q, q ≠ lE → c₃.nreg q = c₂.nreg q := fun q hq => by
    simp only [hc₃, regB, regI]; exact upd_other _ _ _ hq
  have hE3 : c₃.nreg lE = 6 := by simp only [hc₃, regB, regI]; ram_simp
  have nO : ∀ q, 240000 ≤ q → q < 250000 → bandOf q ∉ oracleBands := fun q h1 h2 =>
    not_oracle_sw h1 h2
  have k32 : ∀ q, (q = lMD ∨ q = lCD ∨ q = lNF ∨ q = lH ∨ q = gL) → c₃.nreg q = c₁.nreg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      (rw [o3 _ (by decide)]
       exact fr2' _ (nO _ (by decide) (by decide)) (by decide) (by decide))
  have hL₃ : LCtx P W J.right N₂ E c₃ := lctx_of hS hI₃ hA.htab hA.hTB hA.hTW
    (by ram_grind)
    (by ram_grind)
    (by ram_grind)
  have hH3 : c₃.nreg lH = 0 := by ram_grind
  have eT3 : c₃.nreg TLR = c₀.nreg TLR := hI₃.hin _ (by omega_nf)
  have eA3 : c₃.nreg ALLOC = c.nreg ALLOC + 3 := by
    ram_grind
  refine ((lh1_irs hI₃ hK hL₃ (by omega) (by rw [hH3]; exact pp_zero _ _ _ _)
      (by ram_grind)).mono (by rw [eT3]) ?_)
  rintro c₄ ⟨hj4, hl4, hl4', hLL4, hAl4, hlist4, hm4, fr4, -, -, -⟩
  have fr4' : ∀ q, bandOf q ∉ oracleBands → ¬ (sw 1108 ≤ q ∧ q ≤ sw 1119) → q ≠ ALLOC →
      c₄.nreg q = c₃.nreg q := fun q h1 h2 h3 => fr4 q h1 h2 h3
  
  refine ⟨?_, by omega, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_, c₂.nreg lJ, c₄.nreg lJ,
    ⟨hj1, ?_, ?_⟩, ⟨hj4, ?_, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩
  · rw [fr4' gL (nO _ (by decide) (by decide)) (by decide) (by decide),
      k32 _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
    omega
  · grind
  · have h3' : ¬ (sw 1108 ≤ r ∧ r ≤ sw 1119) :=
      fun h => h3 ⟨le_trans (show sw 1100 ≤ sw 1108 by decide) h.1, h.2⟩
    have h3e : r ≠ lE := by rintro rfl; exact h3 (by decide)
    rw [fr4' r h1 h3' h4, o3 r h3e, fr2' r h1 h3' h4]
    ram_grind
  · intro hc; rw [hE1, hH1, key_zero] at hl1; exact hl1 hc
  · intro hc; rw [hE1, hH1, key_zero] at hl2; exact hl2 hc
  · intro hc; rw [hE3, hH3, key_zero] at hl4; exact hl4 hc
  · intro hc; rw [hE3, hH3, key_zero] at hl4'; ram_grind
  · grind
  · rw [show c.nreg ALLOC + 3 + i = c₃.nreg ALLOC + i by rw [eA3], hlist4 i hi]

end

end Lab0

end SweepIo

end Chazelle.Core
