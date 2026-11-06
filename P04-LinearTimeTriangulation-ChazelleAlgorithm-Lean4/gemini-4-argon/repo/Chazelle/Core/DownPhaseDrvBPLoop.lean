module

public import Chazelle.Core.DownPhaseDrvBPt

/-!
# Down-phase base (D9), RAM: the points of a region

`ptLoop`: for `k < NP` (`r212017`, `r212016`) the point step `ptS`; the records `recs r` of the
region are appended (`ptLoop_exec`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)

@[expose] public section

/-- **The points of a region.** -/
def ptLoop : Stmt := .seq (.instr (.constN 212017 0)) (.whileLtN 212017 212016 ptS)

theorem flatMap_range_length_mono {α : Type*} (f : ℕ → List α) {m m' : ℕ} (h : m ≤ m') :
    ((List.range m).flatMap f).length ≤ ((List.range m').flatMap f).length := by
  induction m' with
  | zero => have : m = 0 := by omega
            subst this; exact le_rfl
  | succ m' ih =>
    rcases Nat.lt_or_ge m (m' + 1) with h' | h'
    · rw [List.range_succ, List.flatMap_append, List.length_append]
      exact (ih (by omega)).trans (Nat.le_add_right _ _)
    · have : m = m' + 1 := by omega
      subst this; exact le_rfl

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The points of a region**: its records are appended. -/
theorem ptLoop_exec {E : BEnv} (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List (ℕ × (ℕ × ℕ × ℕ))} (hS : PtSt E r PA c T)
    (hT : T.length + (E.recs r).length ≤ 2 * E.P.n) :
    ∃ c' k, Exec E.P E.W ptLoop c c' k ∧ k ≤ (ptK E.Cm + 2) * (E.pts r).length + 3 ∧
      PtSt E r PA c' (T ++ (E.recs r).map fun x => (r, x)) ∧ FrameM Bpt c c' ∧
      (∀ a, (a < E.B₂ ∨ E.B₂ + 10 * E.P.n ≤ a) → c'.nmem a = c.nmem a) := by
  set l := E.pts r
  set f := ptRecs E.li E.Q l
  have hrecs : E.recs r = (List.range l.length).flatMap f := regList_eq_flatMap _ _ _
  -- the counter
  have e₀ := Exec.constN (P := E.P) hS.wb 212017 0 (Nat.zero_le _)
  set c₀ : Config := { c with nreg := upd c.nreg 212017 0 } with hc₀
  have f₀ : FrameB (fun q => decide (q = 212017)) c c₀ := exec_frameB e₀ (by decide)
  have S₀ : PtSt E r PA c₀ T := hS.regStep e₀.wb_right (fun q hq => f₀.1 q (by
    rcases hq with hq | hq
    · unfold FixP FixB at hq; simp only [decide_eq_false_iff_not]; omega
    · simp only [decide_eq_false_iff_not]; omega)) f₀.2.2.1
  have FM₀ : FrameM Bpt c c₀ := (FrameB.toM f₀).mono fun q hq => by
    simp only [decide_eq_true_eq] at hq; subst hq; decide
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded E.W e ∧ e.nreg 212017 = j ∧
    e.nreg 212016 = l.length ∧ PtSt E r PA e (T ++ ((List.range j).flatMap f).map fun x => (r, x)) ∧
    FrameM Bpt c e ∧ (∀ a, (a < E.B₂ ∨ E.B₂ + 10 * E.P.n ≤ a) → e.nmem a = c.nmem a)
  have I0 : Inv 0 c₀ := ⟨e₀.wb_right, by simp [hc₀], S₀.np, by simpa using S₀, FM₀,
    fun a _ => by rw [f₀.2.2.1]⟩
  obtain ⟨c', k, ex, ⟨-, -, -, S', FM', M'⟩, hk⟩ := DrvR.forLoop (P := E.P) (W := E.W)
    (ir := 212017) (nr := 212016) (body := ptS) Inv (ptK E.Cm) l.length
    (fun j e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun j e hj ⟨hw, h1, h2, S, FM, M⟩ => by
      have hlen : (T ++ ((List.range j).flatMap f).map fun x => (r, x)).length +
          (f j).length ≤ 2 * E.P.n := by
        have := flatMap_range_length_mono f (show j + 1 ≤ l.length by omega)
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
          at this
        rw [List.length_append, List.length_map]
        rw [hrecs] at hT
        omega
      obtain ⟨e', k', x, hk', S', h17, FM'', M''⟩ := ptS_exec hE hr e S h1 (by omega) hlen
      refine ⟨e', k', x, ⟨x.wb_right, h17, S'.np, ?_, FM.trans FM'', fun a ha => ?_⟩, hk'⟩
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append,
          ← List.append_assoc]
        exact S'
      · rw [M'' a ha, M a ha])
    I0 (Nat.zero_le _)
  rw [Nat.sub_zero] at hk
  refine ⟨c', _, .seq e₀ ex, by omega, ?_, FM', M'⟩
  rwa [hrecs]

end exec

end

end DrvB

end Chazelle.Core
