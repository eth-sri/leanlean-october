module

public import Chazelle.Core.SweepEvOrg

/-!
# The sweep (WP-D), stages 2–3: the end of a chord of `N₂` on the RAM, part 2 (the class)

After `orgHead`, `orgCls` classifies the (normalised) end position `(oE, oC)` of the model of `C₂`:
class `2` if its point `a` is not on `C₂` (a box wall), class `1` if `a` is on `C₂`, is neither the
shared vertex nor the top of `C₂`, and is not above the top of `C₁` (then the symbolic point of `a`
is in `oSym`), class `0` otherwise.  The tests: the walk edge (`pos_mem_set_iff`), the vertex index
`sideIdx (e - 6)` at height code `0` (`orgIdx`), and one sign-kernel height test against the top of
`C₁` (`orgHt`).

Fixed registers (`OrgK`): `2 m₂` (`sw 640`), `m₂` (`641`), the top index of `C₂` (`642`), the tour
start `sideS` of `C₂` (`643`), `2 m₂ + 6` (`644`), the symbolic point of the top of `C₁`
(`645 … 647`).
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sidePt)

@[expose] public section

/-! ## Fixed registers -/

def c2m : ℕ := sw 640
def cm : ℕ := sw 641
def cTop : ℕ := sw 642
def cS : ℕ := sw 643
def c2m6 : ℕ := sw 644
def cT1 : ℕ := sw 645
/-- The bit of the height test (an oracle register). -/
def oHb : ℕ := 50900

/-- The constants of the classification. -/
structure OrgK (P : Polygon) (J : Merge.Junction) (c : Config) : Prop where
  m2 : c.nreg c2m = 2 * J.right.m
  m1 : c.nreg cm = J.right.m
  top : c.nreg cTop = J.right.topIdx
  s : c.nreg cS = J.right.sideS J.right.sideBeta
  m26 : c.nreg c2m6 = 2 * J.right.m + 6
  t1 : ∃ s : SymPt, SymPtIn c cT1 s ∧ s.Lt P.n ∧ s.eval (Qof P) = J.left.top

theorem OrgK.fix {P : Polygon} {J : Merge.Junction} {W : ℕ} {c₀ c : Config} (h : OrgK P J c₀)
    (hI : IInv W c₀ c) : OrgK P J c := by
  have k : ∀ i, 640 ≤ i → i ≤ 647 → c.nreg (sw i) = c₀.nreg (sw i) := fun i h1 h2 =>
    hI.hin _ (by unfold IFix sw; omega)
  obtain ⟨a, b, d, e, f, s, hs, hl, he⟩ := h
  refine ⟨(k 640 le_rfl (by norm_num)).trans a, (k 641 (by norm_num) (by norm_num)).trans b,
    (k 642 (by norm_num) (by norm_num)).trans d, (k 643 (by norm_num) (by norm_num)).trans e,
    (k 644 (by norm_num) (by norm_num)).trans f, s, ?_, hl, he⟩
  exact symPtIn_transport hs (k 645 (by norm_num) (by norm_num))
    (k 646 (by norm_num) (by norm_num)) (k 647 (by norm_num) (by norm_num))

/-! ## Exact executions as run steps -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- An execution changing only scratch registers (listed) is a run step. -/
theorem irs_of_out {s : Stmt} {c' : Config} {k K : ℕ} {L : List ℕ} (hI : IInv W c₀ c)
    (ex : Exec P W s c c' k) (hk : k ≤ K) (ho : Out c c' L) (hL : ∀ r ∈ L, IScr r) :
    IRS P W c₀ s c K (fun c'' => c'' = c') := by
  obtain ⟨hr, hrr, hm, hrm, hout⟩ := ho
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (fun h => alloc_not_scr (hL _ h))
  exact IRS.ofExec hI ex hk (fun r hr' _ => hr r (fun h => hr' (hL r h))) hrr
    (fun a _ => by rw [hm]) hrm hout (by rw [hA]) (by rw [hA]; omega) rfl

/-! ## The vertex index -/

def oU : ℕ := sw 2232

/-- `oJ := sideE m ((S + (e - 6)) mod 2m)`, without words above `2m`. -/
def orgIdx : Stmt :=
  .seq (block [.subN oT oE K6, .subN oU c2m cS])
    (.seq (.ifLtN oT oU (.instr (.addN oT oT cS)) (.instr (.subN oT oT oU)))
      (.seq (condSub oT oT c2m)
        (.ifLtN cm oT (.instr (.subN oJ c2m oT)) (.instr (.copyN oJ oT)))))

theorem orgIdx_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c) (hO : OrgK P J c)
    (h6 : 6 ≤ c.nreg oE) (he : c.nreg oE ≤ 2 * J.right.m + 6) (hWm : 2 * J.right.m + 7 ≤ W) :
    IRS P W c₀ orgIdx c 12 (fun c' => c'.nmem = c.nmem ∧
      c'.nreg oJ = J.right.sideIdx J.right.sideBeta (c.nreg oE - 6) ∧
      ∀ r, r ≠ oT → r ≠ oU → r ≠ oJ → c'.nreg r = c.nreg r) := by
  obtain ⟨-, -, k6, -, -, -, -⟩ := hK
  obtain ⟨m2, m1, -, hS, -, -⟩ := hO
  have hSle := J.right.sideS_lt J.right.sideBeta
  have hm := J.right.one_le
  set i := c.nreg oE - 6 with hi
  set S := J.right.sideS J.right.sideBeta with hSdef
  set m := J.right.m with hmdef
  -- the block
  have e6 : c.nreg 240612 = 6 := k6
  have eS : c.nreg 240643 = S := hS
  have e2 : c.nreg 240640 = 2 * m := m2
  have eE : c.nreg 242210 = c.nreg oE := rfl
  have hb := IRS.block (P := P) [.subN oT oE K6, .subN oU c2m cS] hI (by
    simp only [okB, okI, oT, oU, sw]
    simp only [Nat.reduceAdd]
    exact ⟨iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num), trivial⟩)
  refine (IRS.seq (K₂ := 10) hb ?_).mono (by simp) (fun _ h => h)
  rintro c₁ hI₁ - - rfl
  set c₁ : Config := { c with nreg := regB c.nmem [.subN oT oE K6, .subN oU c2m cS] c.nreg }
    with hc₁
  have v1 : c₁.nreg oT = i := by
    show regB c.nmem [.subN oT oE K6, .subN oU c2m cS] c.nreg oT = i
    simp only [regB, regI]
    rw [upd_other _ _ _ (by unfold oT oU sw; omega), upd_same, k6]
  have v2 : c₁.nreg oU = 2 * m - S := by
    show regB c.nmem [.subN oT oE K6, .subN oU c2m cS] c.nreg oU = 2 * m - S
    simp only [regB, regI]
    rw [upd_same, upd_other _ _ _ (by unfold c2m oT sw; omega),
      upd_other _ _ _ (by unfold cS oT sw; omega), m2, hS]
  have o1 : ∀ r, r ≠ oT → r ≠ oU → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    simp only [hc₁, regB, regI, upd]; rw [ite_eq_right h2, ite_eq_right h1]
  have c1S : c₁.nreg cS = S := (o1 cS (by unfold cS oT sw; omega) (by unfold cS oU sw; omega)).trans hS
  -- the sum modulo `2m`, at most `2m`
  have hstep : IRS P W c₀ (.ifLtN oT oU (.instr (.addN oT oT cS)) (.instr (.subN oT oT oU))) c₁ 3
      (fun c' => c'.nmem = c₁.nmem ∧ c'.nreg oT ≤ 2 * m ∧
        (c'.nreg oT) % (2 * m) = (S + i) % (2 * m) ∧ ∀ r, r ≠ oT → c'.nreg r = c₁.nreg r) := by
    by_cases hlt : c₁.nreg oT < c₁.nreg oU
    · rw [v1, v2] at hlt
      refine (IRS.ifT (by rw [v1, v2]; exact hlt) (IRS.reg (P := P) hI₁
        (iscr_sw (by simp [oT, sw]) (by simp [oT, sw])) (Exec.addN hI₁.hw oT oT cS
          (by rw [v1, c1S]; omega)))).mono (by omega) ?_
      rintro c' rfl
      simp only [upd_same, v1, c1S]
      refine ⟨by simp, by omega, by rw [add_comm], fun r hr => by simp [upd, hr]⟩
    · rw [v1, v2] at hlt
      refine (IRS.ifF (by rw [v1, v2]; exact hlt) (IRS.reg (P := P) hI₁
        (iscr_sw (by simp [oT, sw]) (by simp [oT, sw])) (Exec.subN hI₁.hw oT oT oU))).mono (by omega) ?_
      rintro c' rfl
      simp only [upd_same, v1, v2]
      refine ⟨by simp, by omega, ?_, fun r hr => by simp [upd, hr]⟩
      rw [show S + i = (i - (2 * m - S)) + 2 * m by omega, Nat.add_mod_right]
  refine IRS.seq (K₂ := 7) hstep ?_ |>.mono (by omega) (fun _ h => h)
  rintro c₂ hI₂ - - ⟨hm₂, hle₂, hmod₂, k₂⟩
  have c2m2 : c₂.nreg c2m = 2 * m := by
    rw [k₂ c2m (by unfold c2m oT sw; omega), o1 c2m (by unfold c2m oT sw; omega)
      (by unfold c2m oU sw; omega), m2]
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := condSub_exec (P := P) hI₂.hw oT oT c2m
  refine IRS.seq (K₂ := 3) (irs_of_out hI₂ e₃ (show k₃ ≤ 3 by omega) o₃
    (fun r hr => by simp at hr; subst hr; exact iscr_sw (by simp [oT, sw]) (by simp [oT, sw]))) ?_ |>.mono
    (by omega) (fun _ h => h)
  rintro c₄ hI₄ - - hc4
  subst hc4
  have v3 : c₄.nreg oT = (S + i) % (2 * m) := by
    rw [v₃, c2m2, ← hmod₂]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show c₂.nreg oT = 2 * m by omega, Nat.mod_self]; omega
  have c3m : c₄.nreg c2m = 2 * m := by rw [o₃.1 c2m (by simp [c2m, oT, sw]), c2m2]
  have c3m1 : c₄.nreg cm = m := by
    rw [o₃.1 cm (by simp [cm, oT, sw]), k₂ cm (by unfold cm oT sw; omega),
      o1 cm (by unfold cm oT sw; omega) (by unfold cm oU sw; omega), m1]
  have hsIdx : J.right.sideIdx J.right.sideBeta i = Chazelle.Chain.sideE m (c₄.nreg oT) := by
    rw [Chazelle.Chain.sideIdx_eq, v3]
  have hmodlt : c₄.nreg oT < 2 * m := by rw [v3]; exact Nat.mod_lt _ (by omega)
  by_cases hlt : c₄.nreg cm < c₄.nreg oT
  · refine (IRS.ifT hlt (IRS.reg (P := P) hI₄ (iscr_sw (by simp [oJ, sw]) (by simp [oJ, sw]))
      (Exec.subN hI₄.hw oJ c2m oT))).mono (by omega) ?_
    rintro c' rfl
    refine ⟨by rw [o₃.2.2.1, hm₂], ?_, fun r h1 h2 h3 => ?_⟩
    · simp only [upd_same]
      rw [hsIdx, c3m]
      unfold Chazelle.Chain.sideE
      rw [c3m1] at hlt
      rw [ite_eq_right (by omega)]
    · simp only
      rw [upd_other _ _ _ h3, o₃.1 r (by simp [h1]), k₂ r h1, o1 r h1 h2]
  · refine (IRS.ifF hlt (IRS.reg (P := P) hI₄ (iscr_sw (by simp [oJ, sw]) (by simp [oJ, sw]))
      (Exec.copyN hI₄.hw oJ oT))).mono (by omega) ?_
    rintro c' rfl
    refine ⟨by rw [o₃.2.2.1, hm₂], ?_, fun r h1 h2 h3 => ?_⟩
    · simp only [upd_same]
      rw [hsIdx]
      unfold Chazelle.Chain.sideE
      rw [c3m1] at hlt
      rw [ite_eq_left (by omega)]
    · simp only
      rw [upd_other _ _ _ h3, o₃.1 r (by simp [h1]), k₂ r h1, o1 r h1 h2]

end

end SweepEv

end Chazelle.Core
