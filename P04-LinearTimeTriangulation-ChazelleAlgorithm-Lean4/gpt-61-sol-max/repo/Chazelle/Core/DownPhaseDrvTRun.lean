module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvTBuild
public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase transition (D2), RAM part 7: the whole procedure and its cost

`transS = orientT ; c0S ; filtS ; setB ; buildT ; finT`: the `LeftInside` bit, the shift, the
filter, the inputs of the build, the build with its event pointer, and the registers `1 … 5`
of `bDownDrv` (descriptor, chord list, length, event list, normal form).

* `trans_cost_le`: the cost of the steps is at most `κT (n + 1)`, `κT = 1.6 · 10⁹`: the sort of
  the `K` kept chords costs `O(K log K)`, and `K (γ'_p + 1) = O(n)` (Lemma 2.3) with
  `γ'_p ≥ p ≥ log K - 12`;
* `setB_exec`, `finT_exec`: the two register blocks.
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs BuildRam

@[expose] public section

/-- The inputs of the build: descriptor, chord list, length. -/
def setB : Stmt := block [.copyN 40000 190021, .copyN 40001 190022, .copyN 40002 190036]

/-- The registers `1 … 5` of `bDownDrv`. -/
def finT : Stmt := block [.copyN 210001 190021, .copyN 210002 190022, .copyN 210003 190036,
  .copyN 210004 190020, .copyN 210005 40003]

/-- **The transition procedure.** -/
def transS : Stmt := .seq orientT (.seq c0S (.seq filtS (.seq setB (.seq buildT finT))))

/-- The cost constant of the transition. -/
def κT : ℕ := 1600000000

/-- The registers of `setB`. -/
def BsetB (r : ℕ) : Bool := decide (40000 ≤ r ∧ r ≤ 40002)

/-- The registers of `finT`. -/
def BfinT (r : ℕ) : Bool := decide (210001 ≤ r ∧ r ≤ 210005)

theorem wrM_setB : wrM BsetB setB = true := by decide
theorem wrM_finT : wrM BfinT finT = true := by decide

theorem le_gradeGran (g : ℕ) : g ≤ gradeGran g := by
  
  have h1 : gradeGran g = 2 ^ Cost.ceilBeta g + fuseLoss * (g * (Nat.clog 2 g + 2)) := rfl
  have h2 : fuseLoss = 1 := rfl
  grind

/-- **The cost of the transition.** -/
theorem trans_cost_le {n K K₀ : ℕ} (hn : 3 ≤ n) (hK : K ≤ K₀)
    (hK₀ : K₀ * (gradeGran (topGrade n) + 1) ≤ 840 * (2 * (n - 1) + 1)) :
    (14 * n + 120) + (260 * n + 1950) + (54 * K₀ + 21) + 3 +
      (κBuild * (K * (Nat.clog 2 K + 1) + 1) + 4) + 5 ≤ κT * (n + 1) := by
  set p := topGrade n with hp
  have hnp : n - 1 ≤ 2 ^ p := Nat.le_pow_clog (by norm_num) _
  have hgp : p ≤ gradeGran p := le_gradeGran p
  have hK₀n : K₀ ≤ 1680 * n := by
    grind
  have hKpow : K ≤ 2 ^ (p + 12) := by
    ring_nf <;> omega
  have hclog : Nat.clog 2 K ≤ p + 12 := Nat.clog_le_of_le_pow hKpow
  have hKK : K * (Nat.clog 2 K + 1) ≤ 13 * (K₀ * (gradeGran p + 1)) := by
    calc K * (Nat.clog 2 K + 1) ≤ K * (13 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ K₀ * (13 * (gradeGran p + 1)) := Nat.mul_le_mul hK (by omega)
      _ = 13 * (K₀ * (gradeGran p + 1)) := by ring
  omega_nf

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem setB_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧ c'.nreg 40000 = c.nreg 190021 ∧
      c'.nreg 40001 = c.nreg 190022 ∧ c'.nreg 40002 = c.nreg 190036 ∧
      FrameM BsetB c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, hm⟩ : ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧
      c'.nreg 40000 = c.nreg 190021 ∧ c'.nreg 40001 = c.nreg 190022 ∧
      c'.nreg 40002 = c.nreg 190036 ∧ c'.nmem = c.nmem := by
    unfold setB
    exec_block
    simp_all
  exact ⟨c', k, e, hk, h1, h2, h3, exec_frameM e wrM_setB, hm⟩

set_option maxHeartbeats 1000000 in
theorem finT_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W finT c c' k ∧ k = 5 ∧ c'.nreg 210001 = c.nreg 190021 ∧
      c'.nreg 210002 = c.nreg 190022 ∧ c'.nreg 210003 = c.nreg 190036 ∧
      c'.nreg 210004 = c.nreg 190020 ∧ c'.nreg 210005 = c.nreg 40003 ∧
      FrameM BfinT c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, h4, h5, hm⟩ : ∃ c' k, Exec P W finT c c' k ∧ k = 5 ∧
      c'.nreg 210001 = c.nreg 190021 ∧ c'.nreg 210002 = c.nreg 190022 ∧
      c'.nreg 210003 = c.nreg 190036 ∧ c'.nreg 210004 = c.nreg 190020 ∧
      c'.nreg 210005 = c.nreg 40003 ∧ c'.nmem = c.nmem := by
    unfold finT
    exec_block
    simp_all
  exact ⟨c', k, e, hk, h1, h2, h3, h4, h5, exec_frameM e wrM_finT, hm⟩

end exec

end

end DrvT

end Chazelle.Core
