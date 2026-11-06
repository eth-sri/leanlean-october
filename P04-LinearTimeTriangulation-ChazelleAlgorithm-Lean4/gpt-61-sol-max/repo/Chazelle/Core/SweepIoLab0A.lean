module

public import Chazelle.Core.SweepIoLab0G

/-!
# The sweep RAM (WP-D), answers: the label candidates of a side-0 query, the binary search

`LSBody lsearch κ`: the body of `S0C.LSearchSpec` for a program `lsearch` and a constant `κ`.
`search_irs`: the target position is the arrival position `(zP, zPh)` of the query point, the
result `t = lsI` is the number of log keys before the key of the target (stated in the memory of
the base configuration).
-/

namespace Chazelle.Core

namespace SweepIo

namespace Lab0

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The body of the contract of the binary search.** -/
def LSBody (lsearch : Stmt) (κ : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c (sw 2) J.whole →
    (∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j) →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg (sw 301) < 2 ^ c.nreg TLR →
    c.nreg (sw 300) + 7 * c.nreg (sw 301) ≤ c.nreg ALLOC →
    c.nreg (sw 40) < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg (sw 301) → SweepEv.PosW P J (c.nmem (c.nreg (sw 300) + 7 * j))
      (c.nmem (c.nreg (sw 300) + 7 * j + 1))) →
    SweepEv.PosW P J (c.nreg S0C.lsxE) (c.nreg S0C.lsxH) →
    (∀ i j, i ≤ j → j < c.nreg (sw 301) →
      S0C.lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg S0C.lsxE, c.nreg S0C.lsxH⟩ j →
      S0C.lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg S0C.lsxE, c.nreg S0C.lsxH⟩ i) →
    c.nreg ALLOC + κ * (c.nreg TLR + 1) ≤ W →
    IRS P W c₀ lsearch c (κ * (c.nreg TLR + 1)) (fun c' =>
      c'.nreg S0C.lsI ≤ c.nreg (sw 301) ∧
      (∀ j, j < c'.nreg S0C.lsI →
        S0C.lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40))
          ⟨c.nreg S0C.lsxE, c.nreg S0C.lsxH⟩ j) ∧
      (∀ j, c'.nreg S0C.lsI ≤ j → j < c.nreg (sw 301) →
        ¬ S0C.lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40))
          ⟨c.nreg S0C.lsxE, c.nreg S0C.lsxH⟩ j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ S0C.LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a))

theorem lsBody_of (h : S0C.LSearchSpec) : ∃ ls κ, LSBody ls κ := h

section Env

variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

/-- The chain descriptor of `C` at `sw 2`. -/
theorem ctxW (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) :
    ChainCtx P W c (sw 2) J.whole := by
  obtain ⟨-, -, -, -, hJ, hJWF, -⟩ := hA.hst
  have h0 : ChainCtx P W c₀ (sw 2) J.whole :=
    ⟨hA.hG, hA.hWh, hJWF.2.2.1, ⟨H, hJ.2.2, hA.hostReg⟩, hA.hP, hA.hWm⟩
  exact h0.transport (hI.hin _ (by unfold IFix sw; omega)) hI.hm hI.hA

/-- The predicate of the search reads only the two words of the record. -/
theorem lsPr_congr {m m' : ℕ → ℕ} {AL G : ℕ} {x : WPos} {j : ℕ}
    (h0 : m' (AL + 7 * j) = m (AL + 7 * j)) (h1 : m' (AL + 7 * j + 1) = m (AL + 7 * j + 1)) :
    S0C.lsPr P J m' AL G x j ↔ S0C.lsPr P J m AL G x j := by
  unfold S0C.lsPr; rw [h0, h1]

/-- The block setting the target of the search. -/
def lsIn : List Instr := [.copyN S0C.lsxE zP, .copyN S0C.lsxH zPh]

set_option maxHeartbeats 4000000 in
/-- **The binary search at the arrival position of the query point.** -/
theorem search_irs {ls : Stmt} {κL : ℕ} (hls : LSBody ls κL)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) {z : Point} (hz : z ∈ J.left.set)
    {σ : ℝ} (hzP : c.nreg zP < (chainModel J.whole).W.n)
    (hpp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zP, c.nreg zPh⟩)
    (harr : Arrival (chainModel J.whole).W z σ (c.nreg zP)
      ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩))
    (hroom : c.nreg ALLOC + (2 + κL * (c₀.nreg TLR + 1)) ≤ W) :
    IRS P W c₀ (.seq (block lsIn) ls) c (2 + κL * (c₀.nreg TLR + 1)) (fun c' =>
      c'.nreg S0C.lsI ≤ rd c₀ bSweep 301 ∧
      (∀ j, j < c'.nreg S0C.lsI → S0C.lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40))
        ⟨c.nreg zP, c.nreg zPh⟩ j) ∧
      (∀ j, c'.nreg S0C.lsI ≤ j → j < rd c₀ bSweep 301 →
        ¬ S0C.lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) ⟨c.nreg zP, c.nreg zPh⟩ j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ (sw 4000 ≤ r ∧ r ≤ sw 4021) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  refine IRS.seq (K₁ := 2) (K₂ := κL * (c₀.nreg TLR + 1))
    (IRS.block lsIn hI ⟨s 4020 (by norm_num) (by norm_num), s 4021 (by norm_num) (by norm_num),
      trivial⟩) ?_
  rintro c₁ hI₁ hA₁ hA₁' rfl
  set c₁ : Config := { c with nreg := regB c.nmem lsIn c.nreg } with hc₁
  have v1 : c₁.nreg S0C.lsxE = c.nreg zP := by
    simp only [hc₁, lsIn, regB, regI, upd, S0C.lsxE, S0C.lsxH, zP, zPh, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  have v2 : c₁.nreg S0C.lsxH = c.nreg zPh := by
    simp only [hc₁, lsIn, regB, regI, upd, S0C.lsxE, S0C.lsxH, zP, zPh, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  have vo : ∀ q, q ≠ S0C.lsxE → q ≠ S0C.lsxH → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    regB_other _ _ _ (fun i hi => by
      simp only [lsIn, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp only [dstI] <;> intro h <;> subst h <;> simp at h1 h2)
  have hfix : ∀ q, IFix q → c₁.nreg q = c₀.nreg q := fun q hq => hI₁.hin q hq
  have eTB : c₁.nreg TBR = c₀.nreg TBR := hfix _ (by unfold IFix TBR sw; omega)
  have eTL : c₁.nreg TLR = c₀.nreg TLR := hfix _ (by unfold IFix TLR sw; omega)
  have e300 : c₁.nreg (sw 300) = rd c₀ bSweep 300 := hfix _ (by unfold IFix sw; omega)
  have e301 : c₁.nreg (sw 301) = rd c₀ bSweep 301 := hfix _ (by unfold IFix sw; omega)
  have e40 : c₁.nreg (sw 40) = c₀.nreg (sw 40) := hfix _ (by unfold IFix sw; omega)
  have hlog := hA.hlog
  have hm : ∀ a, a < c₀.nreg ALLOC → c₁.nmem a = c₀.nmem a := fun a ha => hI₁.hm a ha
  have hlsP : ∀ j, j < rd c₀ bSweep 301 →
      (S0C.lsPr P J c₁.nmem (c₁.nreg (sw 300)) (c₁.nreg (sw 40))
        ⟨c₁.nreg S0C.lsxE, c₁.nreg S0C.lsxH⟩ j ↔
      S0C.lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) ⟨c.nreg zP, c.nreg zPh⟩ j) := by
    intro j hj
    rw [e300, e40, v1, v2]
    exact lsPr_congr (hm _ (by omega)) (hm _ (by omega))
  have hG : c₁.nreg (sw 40) < (chainModel J.whole).W.n := by
    rw [e40, S0C.aenv_gW hA]; exact_mod_cast S0C.gW_lt J
  have hrec : ∀ j, j < c₁.nreg (sw 301) → SweepEv.PosW P J
      (c₁.nmem (c₁.nreg (sw 300) + 7 * j)) (c₁.nmem (c₁.nreg (sw 300) + 7 * j + 1)) := by
    intro j hj
    rw [e301] at hj
    rw [e300, hm _ (by omega), hm _ (by omega)]
    exact S0C.log_posW hA hj
  have hx : SweepEv.PosW P J (c₁.nreg S0C.lsxE) (c₁.nreg S0C.lsxH) := by
    rw [v1, v2]
    exact ⟨hzP, hpp, fun h0 => S0C.query_h6 hz harr h0⟩
  have hdc : ∀ i j, i ≤ j → j < c₁.nreg (sw 301) →
      S0C.lsPr P J c₁.nmem (c₁.nreg (sw 300)) (c₁.nreg (sw 40))
        ⟨c₁.nreg S0C.lsxE, c₁.nreg S0C.lsxH⟩ j →
      S0C.lsPr P J c₁.nmem (c₁.nreg (sw 300)) (c₁.nreg (sw 40))
        ⟨c₁.nreg S0C.lsxE, c₁.nreg S0C.lsxH⟩ i := by
    intro i j hij hj h
    rw [e301] at hj
    rw [hlsP i (by omega)]
    rw [hlsP j hj] at h
    exact S0C.log_mono hA _ hij hj h
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := vo _ (by decide) (by decide)
  have h := hls P W J c₀ c₁ hI₁ hA.hK (ctxW hA hI₁)
    (fun j hj => by
      rw [eTL] at hj
      rw [eTB, hm _ (by have := hA.hTW; omega)]
      exact hA.htab j hj)
    (by rw [eTB, eTL]; have := hA.hTW; have := hI₁.hA; omega)
    (by rw [e301, eTL]; have := hA.hbigE; omega)
    (by rw [e300, e301]; have := hI₁.hA; omega) hG hrec hx hdc
    (by rw [eTL, hA1]; omega)
  rw [eTL] at h
  refine h.mono le_rfl ?_
  rintro c' ⟨r1, r2, r3, r4, r5, r6⟩
  rw [e301] at r1
  refine ⟨r1, fun j hj => (hlsP j (by omega)).1 (r2 j hj),
    fun j hj hjE => fun h' => r3 j hj (by rw [e301]; exact hjE) ((hlsP j hjE).2 h'),
    fun r h1 h2 h3 => ?_, fun a ha => by rw [r6 a (by omega)]⟩
  rw [r4 r h1 (fun h => h2 (by unfold S0C.LSet at h; unfold sw at *; omega)) h3]
  exact vo r (by rintro rfl; exact h2 (by decide)) (by rintro rfl; exact h2 (by decide))

end Env

end

end Lab0

end SweepIo

end Chazelle.Core
