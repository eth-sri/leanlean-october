module

public import Chazelle.Machine.FrameFields

public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Core.SortRam

/-!
# WP-I, part 66: the outputs and the allocator

`outS`: the outputs `130004 := DF`, `130005 := LAB`; `bumpS` raises `ALLOC` one by one to the
end `END` of the work area, so that the allocator grows by at most the step count.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- **Raise the allocator to `END`.** -/
def bumpS : Stmt := .whileLtN ALLOC 130086 (.instr (.addN ALLOC ALLOC 130001))

/-- The outputs. -/
def outS : Stmt := block [.copyN 130004 130078, .copyN 130005 130032]

section proofs

variable {P : Polygon} {W : ℕ}

theorem bumpS_exec {c : Config} (hw : WordsBounded W c) {E : ℕ} (h1 : c.nreg 130001 = 1)
    (hE : c.nreg 130086 = E) (hA : c.nreg ALLOC ≤ E) (hEW : E ≤ W) :
    ∃ c' k, Exec P W bumpS c c' k ∧ k ≤ 3 * (E - c.nreg ALLOC) + 2 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = E ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (Machine.NRegEqExcept ALLOC c c') ∧ Machine.NatRegFrame c c' := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c', k, e, ⟨hw', hA', hr', hm', hrr', hrm', ho'⟩, htest, hk, hψ⟩ :=
    Exec.whileLtN_growth (P := P) (W := W) (a := ALLOC) (b := 130086)
    (body := .instr (.addN ALLOC ALLOC 130001))
    (fun c' => WordsBounded W c' ∧ c'.nreg ALLOC ≤ E ∧ (Machine.NRegEqExcept ALLOC c c') ∧
      Machine.NatRegFrame c c')
    (fun c' => 3 * (E - c'.nreg ALLOC)) (fun c' => c'.nreg ALLOC) (fun c' h => h.1)
    (fun c1 ⟨hw1, hA1, hr1, hm1, hrr1, hrm1, ho1⟩ htest => by
      have e1 : c1.nreg 130001 = 1 := by simp_all
      have e2 : c1.nreg 130086 = E := by simp_all
      rw [e2] at htest
      have ex := Exec.addN (P := P) hw1 ALLOC ALLOC 130001 (by rw [e1]; omega)
      refine ⟨_, 1, ex, ⟨ex.wb_right, ?_, fun r hr => ?_, hm1, hrr1, hrm1, ho1⟩, ?_, ?_⟩
      · simp_all
      · simp_all
      · simp only [Machine.upd_same]; rw [e1]; omega
      · simp_all)
    ⟨hw, hA, fun r _ => rfl, rfl, rfl, rfl, rfl⟩
  have e2 : c'.nreg 130086 = E := by simp_all
  rw [e2] at htest
  exact ⟨c', k, e, hk, hw', by omega, hψ, hr', hm', hrr', hrm', ho'⟩

end proofs

end

end Chazelle.Core.Cluster
