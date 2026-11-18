module

public import Chazelle.Core.DownPhaseOracleCuR6

/-!
# WP-M (E7-B, RAM part 21): the query of the interior cutter, executed

`queryC_exec`: after the set-up (`SEnv`, slots free), `queryC cu` answers with a list `ps` of at
most `4 G γ` pieces at the address in `150010`, above the entry allocator and below the final one;
the pieces are valid pieces of the interior walk (`PcV`) and form a path of unwrapped interior keys
from `e₁ + t₁` (the start of the query) to `e₁ + ee + t₂` (its end, `ee` the normalized offset).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open ShootCut (Pc KPath)

@[expose] public section

set_option maxRecDepth 20000 in
theorem roomC_one {A lg Gg cl W : ℕ} (h : A + (172 * Gg + 2408 * (cl + 1) + 6300) ≤ W)
    (hl : lg ≤ cl + 1) : A + 2 * Gg + 1204 * lg + 2600 ≤ W := by omega

set_option maxRecDepth 20000 in
theorem roomC_two {A A' k₃ lg lg₁ Gg cl W : ℕ}
    (h : A + (172 * Gg + 2408 * (cl + 1) + 6300) ≤ W) (hA : A' ≤ A + k₃)
    (hk : k₃ ≤ 2 * Gg + 1204 * lg₁ + 2600) (hl₁ : lg₁ ≤ cl + 1)
    (hl : lg ≤ cl + 1) : A' + 2 * Gg + 1204 * lg + 2600 ≤ W := by omega

set_option maxRecDepth 20000 in
theorem costC_one {k₂ k₃ lg Gg cl : ℕ} (h2 : k₂ = 5) (h3 : k₃ ≤ 2 * Gg + 1204 * lg + 2600)
    (hl : lg ≤ cl + 1) : k₂ + k₃ + 1 ≤ 4 * Gg + 2408 * (cl + 1) + 5300 := by omega

set_option maxRecDepth 20000 in
theorem costC_two {k₂ k₃ k₄ k₅ lg lg₁ Gg cl : ℕ} (h2 : k₂ = 5)
    (h3 : k₃ ≤ 2 * Gg + 1204 * lg₁ + 2600) (h4 : k₄ ≤ 8) (h5 : k₅ ≤ 2 * Gg + 1204 * lg + 2600)
    (hl₁ : lg₁ ≤ cl + 1) (hl : lg ≤ cl + 1) :
    k₂ + (k₃ + (k₄ + k₅)) + 2 ≤ 4 * Gg + 2408 * (cl + 1) + 5300 := by omega

set_option maxRecDepth 20000 in
theorem roomC_asm {A k₁ k₂ len Gg cl W : ℕ} (h : A + (172 * Gg + 2408 * (cl + 1) + 6300) ≤ W)
    (hk₁ : k₁ ≤ 900) (hk₂ : k₂ ≤ 4 * Gg + 2408 * (cl + 1) + 5300) (hl : len ≤ 4 * Gg) :
    A + k₁ + k₂ + 42 * len + 60 ≤ W := by omega

set_option maxRecDepth 20000 in
theorem costC_q {k₁ k₂ k₃ len Gg cl : ℕ} (hk₁ : k₁ ≤ 900)
    (hk₂ : k₂ ≤ 4 * Gg + 2408 * (cl + 1) + 5300) (hk₃ : k₃ ≤ 42 * len + 60) (hl : len ≤ 4 * Gg) :
    k₁ + (k₂ + k₃) ≤ 172 * Gg + 2408 * (cl + 1) + 6300 := by omega

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- **The query of the interior cutter.** -/
theorem queryC_exec {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H (gradeCtx O) OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) (hfree : ∀ j, j < 4 → c.nreg (170200 + 5 * j) = 0)
    (q : QFacts (Qof P) s.e₁ s.h₁ s.e₂ s.h₂)
    (hwt : (interiorModel (Qof P)).arcWt ((interiorModel (Qof P)).key (Qof P) ⟨s.e₁, s.h₁⟩)
      ((interiorModel (Qof P)).key (Qof P) ⟨s.e₂, s.h₂⟩) ≤ s.γ)
    (hroom : c.nreg ALLOC + (172 * G s.γ + 2408 * (Nat.clog 2 s.γ + 1) + 6300) ≤ W) :
    ∃ (c' : Config) (k : ℕ) (ps : List Pc), Exec P W (queryC cu) c c' k ∧
      k ≤ 172 * G s.γ + 2408 * (Nat.clog 2 s.γ + 1) + 6300 ∧
      ps ≠ [] ∧ ps.length ≤ 4 * G s.γ ∧
      c.nreg ALLOC ≤ c'.nreg 150010 ∧ c'.nmem (c'.nreg 150010) = ps.length ∧
      c'.nreg 150010 + 1 + 7 * ps.length ≤ c'.nreg ALLOC ∧
      (∀ j (hj : j < ps.length), rdPc c'.nmem (c'.nreg 150010) j = ps[j]'hj) ∧
      KPath (interiorModel (Qof P)) (Qof P) (Qof P).n
        ((s.e₁ : ℝ) + (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩) ps
        ((s.e₁ : ℝ) + eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂) +
          (interiorModel (Qof P)).param (Qof P) ⟨s.e₂, s.h₂⟩) ∧
      (∀ pc ∈ ps, PcV P (interiorModel (Qof P)) c'.nmem (c'.nreg ALLOC) (H s.γ) pc) ∧
      Frame ioBands c c' k := by
  have hQ : (Qof P).n = P.n := qn'
  have hn := hS.n3
  have hW := hS.hW
  unfold hostWords at hW
  have he1 : s.e₁ < P.n := by rw [← hQ]; exact q.he₁
  have he2 : s.e₂ < P.n := by rw [← hQ]; exact q.he₂
  have hh1 : s.h₁ ≤ P.n := by rw [← hQ]; exact q.hs.2.2
  have hh2 : s.h₂ ≤ P.n := by rw [← hQ]; exact q.he.2.2
  -- the normalized query
  obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, F₁⟩ := normI_exec c hw hS he1 he2 hh1 hh2 q.hs.1
  obtain ⟨hpS, hxy, hmod, heen, hee, hL1, hwtL, hwtn⟩ := qplan q
  set x := (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩ with hx
  set ee := eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂) with heed
  set t₂ := (interiorModel (Qof P)).param (Qof P) ⟨s.e₂, s.h₂⟩ with ht₂
  set V0 : ℝ := (s.e₁ : ℝ) + ((0 : ℕ) : ℝ) + x with hV0
  set V1 : ℝ := (s.e₁ : ℝ) + ee + t₂ with hV1
  have w₁ := e₁.wb_right
  have f₁ : ∀ r, Bnorm r = false → c₁.nreg r = c.nreg r := F₁.1
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => f₁ r (by
    simp only [Bnorm, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
    (fun a _ => by rw [F₁.2.2.1]) (by rw [f₁ _ (by decide)])
  have Fr₁ : Frame ioBands c c₁ k₁ := frameIO_of_frameB (B := Bnorm) (fun r hr => io_of_band (by
    simp only [Bnorm, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr; omega)) F₁ k₁
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by decide)
  have fs : ∀ j, j < 4 → c₁.nreg (170200 + 5 * j) = 0 := fun j hj => by
    rw [f₁ _ (by simp only [Bnorm, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)]
    exact hfree j hj
  have T₁ : SlotSt P (H s.γ) (G s.γ) s.e₁ V0 V0 0 c₁ := by
    refine ⟨?_, fun j _ hj => fs j hj, fun j hj => by rw [fs j hj]; omega, fun sl hsl => ?_⟩
    · rw [slotsOf_nil fs]; rfl
    · rw [slotsOf_nil fs] at hsl; simp at hsl
  have bandSet : ∀ {d d' : Config}, FrameB Bset d d' → ∀ r, (r < 170033 ∨ 170038 ≤ r) →
      d'.nreg r = d.nreg r := fun F r hr => F.1 r (by
        simp only [Bset, decide_eq_false_iff_not]; omega)
  have keepSet : ∀ {d d' : Config}, FrameB Bset d d' → SEnv P W O s d → SEnv P W O s d' :=
    fun F hS' => hS'.keep (fun r h1 h2 => bandSet F r (by omega)) (fun a _ => by rw [F.2.2.1])
      (by rw [bandSet F _ (by unfold ALLOC; omega)])
  have keepSetT : ∀ {d d' : Config} {V : ℝ} {k : ℕ}, FrameB Bset d d' →
      SlotSt P (H s.γ) (G s.γ) s.e₁ V0 V k d → SlotSt P (H s.γ) (G s.γ) s.e₁ V0 V k d' :=
    fun F hT => hT.keep (fun r h1 h2 => bandSet F r (by omega)) (fun a _ => by rw [F.2.2.1])
      (by rw [bandSet F _ (by unfold ALLOC; omega)])
  -- the branch
  have hbr : ∃ c₂ k₂, Exec P W (branchC cu) c₁ c₂ k₂ ∧
      k₂ ≤ 4 * G s.γ + 2408 * (Nat.clog 2 s.γ + 1) + 5300 ∧
      SlotSt P (H s.γ) (G s.γ) s.e₁ V0 V1 4 c₂ ∧ SEnv P W O s c₂ ∧ Frame ioBands c₁ c₂ k₂ := by
    unfold branchC
    by_cases hL : spanL ee (nh (Qof P) s.e₂ s.h₂) + 1 ≤ (Qof P).n
    · -- one sub-query
      have hcond : c₁.nreg 170032 < c₁.nreg 170010 := by rw [a32, S₁.r10, ← hQ]; omega
      obtain ⟨hsub, hset, hwL⟩ := plan_one q hL
      rw [← heed] at hsub hwL
      obtain ⟨c₂, k₂, e₂, hk₂, b33, b34, b35, b36, b37, Fs⟩ := setOne_exec (P := P) c₁ w₁
      have S₂ := keepSet Fs S₁
      have T₂ := keepSetT Fs T₁
      have hLγ : spanL ee (nh (Qof P) s.e₂ s.h₂) ≤ s.γ := hwL ▸ hwt
      have hlog := log_le_clog_succ hL1 hLγ
      have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
        rw [bandSet Fs _ (by unfold ALLOC; omega), hA₁]
      obtain ⟨c₃, k₃, e₃, hk₃, T₃, S₃, F₃, g₃⟩ := sqC_exec hcu c₂ e₂.wb_right S₂
        (b33.trans S₁.r1) (b34.trans S₁.r2) (b35.trans a31) (b36.trans a30) (b37.trans a32)
        hsub hLγ (off := 0) (by rw [Nat.add_zero, Nat.mod_eq_of_lt q.he₁]) (b := 0) (by norm_num)
        T₂ (by rw [hA₂]; exact roomC_one hroom hlog)
      have hV : (s.e₁ : ℝ) + ((0 : ℕ) : ℝ) + (ee : ℝ) + (interiorModel (Qof P)).param (Qof P)
          ⟨(s.e₁ + ee) % (Qof P).n, nh (Qof P) s.e₂ s.h₂⟩ = V1 := by
        rw [hmod, param_nh q.he₂]; push_cast; ring
      rw [hV] at T₃
      refine ⟨c₃, _, .ifLtN_true hcond (.seq e₂ e₃), costC_one hk₂ hk₃ hlog, T₃.mono (by norm_num),
        S₃, ((frameIO_of_frameB (fun r h => bset_io h) Fs k₂).trans F₃).mono (by simp) (by omega)⟩
    · -- two sub-queries
      push Not at hL
      have hcond : ¬ c₁.nreg 170032 < c₁.nreg 170010 := by rw [a32, S₁.r10, ← hQ]; omega
      obtain ⟨hsubA, hsubB, hset, hwn⟩ := plan_two q (by rw [← heed]; omega)
      rw [← heed] at hsubB
      have hnγ : P.n ≤ s.γ := by rw [← hQ]; exact hwn ▸ hwt
      have hee2 : 2 ≤ ee := by rcases hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
      have hmod2 : ((s.e₁ + 2) % (Qof P).n + (ee - 2)) % (Qof P).n = s.e₂ := by
        rw [Nat.mod_add_mod, show s.e₁ + 2 + (ee - 2) = s.e₁ + ee by omega, hmod]
      -- the first sub-query
      obtain ⟨c₂, k₂, e₂, hk₂, b33, b34, b35, b36, b37, Fs⟩ := setTwoA_exec (P := P) c₁ w₁ (by omega)
      have S₂ := keepSet Fs S₁
      have T₂ := keepSetT Fs T₁
      have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
        rw [bandSet Fs _ (by unfold ALLOC; omega), hA₁]
      have hlogA := log_le_clog_succ (L := 2) (γ := s.γ) (by norm_num) (by omega)
      obtain ⟨c₃, k₃, e₃, hk₃, T₃, S₃, F₃, g₃⟩ := sqC_exec hcu c₂ e₂.wb_right S₂ (u := s.e₁)
        (L := 2) (sh₀ := s.h₁) (ee := 2) (eh := 0)
        (b33.trans S₁.r1) (b34.trans S₁.r2) b35 b36 b37
        hsubA (by omega) (off := 0) (by rw [Nat.add_zero, Nat.mod_eq_of_lt q.he₁]) (b := 0)
        (by norm_num) T₂ (by rw [hA₂]; exact roomC_one hroom hlogA)
      -- the second sub-query
      have c31 : c₃.nreg 170031 = ee := by
        rw [g₃ _ (by norm_num) (by norm_num) (by decide), bandSet Fs _ (by omega)]; exact a31
      have c30 : c₃.nreg 170030 = nh (Qof P) s.e₂ s.h₂ := by
        rw [g₃ _ (by norm_num) (by norm_num) (by decide), bandSet Fs _ (by omega)]; exact a30
      have c32 : c₃.nreg 170032 = spanL ee (nh (Qof P) s.e₂ s.h₂) := by
        rw [g₃ _ (by norm_num) (by norm_num) (by decide), bandSet Fs _ (by omega)]; exact a32
      obtain ⟨c₄, k₄, e₄, hk₄, d33, d34, d35, d36, d37, Ft⟩ := setTwoB_exec (P := P) c₃
        e₃.wb_right S₃ he1
      have S₄ := keepSet Ft S₃
      have hA₄ : c₄.nreg ALLOC ≤ c.nreg ALLOC + k₃ := by
        rw [bandSet Ft _ (by unfold ALLOC; omega)]
        have := F₃.2.2.2.2.2.2; omega
      have hLB : spanL ee (nh (Qof P) s.e₂ s.h₂) - 2 ≤ s.γ := by
        have := hsubB.h2; rw [hQ] at this; omega
      have hlogB := log_le_clog_succ hsubB.h1 hLB
      have hV2 : (s.e₁ : ℝ) + ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + (interiorModel (Qof P)).param
          (Qof P) ⟨(s.e₁ + 2) % (Qof P).n, 0⟩ = (s.e₁ : ℝ) + ((2 : ℕ) : ℝ) +
          (interiorModel (Qof P)).param (Qof P) ⟨(s.e₁ + 2) % (Qof P).n, 0⟩ := by
        push_cast; ring
      rw [hV2] at T₃
      obtain ⟨c₅, k₅, e₅, hk₅, T₅, S₅, F₅, g₅⟩ := sqC_exec hcu c₄ e₄.wb_right S₄
        (u := (s.e₁ + 2) % (Qof P).n) (sh₀ := 0)
        (by rw [d33, hQ]) d34 (by rw [d35, c31]) (by rw [d36, c30]) (by rw [d37, c32])
        hsubB hLB (off := 2) rfl (b := 2) (by norm_num) (keepSetT Ft T₃)
        (roomC_two hroom hA₄ hk₃ hlogA hlogB)
      have hV : (s.e₁ : ℝ) + ((2 : ℕ) : ℝ) + ((ee - 2 : ℕ) : ℝ) + (interiorModel (Qof P)).param
          (Qof P) ⟨((s.e₁ + 2) % (Qof P).n + (ee - 2)) % (Qof P).n, nh (Qof P) s.e₂ s.h₂⟩ = V1 := by
        rw [hmod2, param_nh q.he₂, Nat.cast_sub hee2]; push_cast; ring
      rw [hV] at T₅
      refine ⟨c₅, _, .ifLtN_false hcond (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
        costC_two hk₂ hk₃ hk₄ hk₅ hlogA hlogB, T₅, S₅,
        ((((frameIO_of_frameB (fun r h => bset_io h) Fs k₂).trans F₃).trans
          (frameIO_of_frameB (fun r h => bset_io h) Ft k₄)).trans F₅).mono (by simp) (by omega)⟩
  obtain ⟨c₂, k₂, e₂, hk₂, T₂, S₂, F₂⟩ := hbr
  -- the assembly
  have hlen : ((slotsOf c₂ 4).flatMap (slotPcs c₂.nmem (Qof P).n)).length ≤ 4 * G s.γ := by
    have h1 := flat_len_le (m := c₂.nmem) (n := (Qof P).n) T₂.qG
    have h2 := slotsOf_length (c := c₂) (k := 4)
    have : (slotsOf c₂ 4).length * G s.γ ≤ 4 * G s.γ := Nat.mul_le_mul_right _ h2
    omega
  have hA₂ : c₂.nreg ALLOC ≤ c.nreg ALLOC + k₁ + k₂ := by
    have := F₂.2.2.2.2.2.2; have := Fr₁.2.2.2.2.2.2; omega
  obtain ⟨c₃, k₃, e₃, hk₃, d10, dO, dout, dA, F₃⟩ := asmC_exec (P := P) c₂ e₂.wb_right
    (n := (Qof P).n) (by rw [S₂.r10, hQ]) S₂.r11 rfl (by rw [hQ]; omega) T₂.ok T₂.bit
    (by have := roomC_asm hroom hk₁ hk₂ hlen; omega)
  set ps := (slotsOf c₂ 4).flatMap (slotPcs c₂.nmem (Qof P).n) with hps
  obtain ⟨hkp, hv, hne⟩ := slotsOK_out T₂.ok
  have hlt : V0 < V1 := by
    rw [param_nh q.he₂] at hxy
    rw [hV0, hV1]; push_cast; linarith
  have hsne : slotsOf c₂ 4 ≠ [] := by
    intro h
    have hok := T₂.ok
    rw [h] at hok
    exact absurd hok hlt.ne
  have hpne : ps ≠ [] := hne hsne
  have hF₃m : ∀ a, a < c₂.nreg ALLOC → c₃.nmem a = c₂.nmem a := F₃.2.2.1
  have hA₃ : c₂.nreg ALLOC ≤ c₃.nreg ALLOC := F₃.2.2.2.2.2.1
  refine ⟨c₃, _, ps, .seq e₁ (.seq e₂ e₃), costC_q hk₁ hk₂ hk₃ hlen, hpne, hlen,
    by rw [d10]; have := Fr₁.2.2.2.2.2.1; have := F₂.2.2.2.2.2.1; omega, by rw [d10, dO],
    by rw [d10, dA], fun j hj => ?_, ?_, fun pc hpc => (hv pc hpc).keep hF₃m hA₃,
    ((Fr₁.trans F₂).trans F₃).mono (by simp) (by omega)⟩
  · rw [d10]
    obtain ⟨h1, h2⟩ := slotPcs_fields (List.getElem_mem hj)
    exact rdPc_of_words (fun f hf => dout j hj f hf) h1 h2
  · have e0 : V0 = (s.e₁ : ℝ) + x := by rw [hV0]; push_cast; ring
    rw [← e0]
    exact hkp

end exec

end

end IOrc

end Chazelle.Core
