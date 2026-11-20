module

public import Chazelle.Core.DownPhaseOracleTopM
public import Chazelle.Core.DownPhaseOracleRamC

/-!
# WP-M (E7-B, RAM part 4): the top of a chain by the grade table (O5)

`topLoop` runs the bottom-up dyadic cover of the vertex range `[x, y]` of `Q`
(`y ≤ n - 1`), one grade per iteration (registers `170050` `q_l`, `170051` `q_r`, `170052` the
grade `g`, `170053` `2^g`, `170054` `lo = q_l 2^g`, `170055` `hi = q_r 2^g`): an odd `q_l`
contributes the block `(g, q_l)` (its top from the grade table, or its end vertex for `g = 0`),
an odd `q_r` the block `(g, q_r - 1)`; the running maximum `170046` (a vertex index of `Q`) is
kept by one sign test per block (`cmpUpd`). The same program and cover proof serve both models.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The programs -/

/-- `170058 := q_l mod 2` (`170057 := q_l / 2` from the halving table). -/
def parL : Stmt :=
  block [.addN 170056 170017 170050, .loadN 170057 170056, .subN 170058 170050 170057,
    .subN 170058 170058 170057]

/-- `170058 := q_r mod 2`. -/
def parR : Stmt :=
  block [.addN 170056 170017 170051, .loadN 170057 170056, .subN 170058 170051 170057,
    .subN 170058 170058 170057]

/-- The candidate of the block `(g, q_l)` starting at `lo`: its end vertex for `g = 0`, else its top read from the grade table. -/
def candL : Stmt :=
  .ifLtN 170052 170011 (block [.addN 170059 170054 170011])
    (block [.addN 170056 170016 170052, .loadN 170056 170056, .addN 170056 170056 170050,
      .addN 170056 170056 170050, .addN 170056 170056 170050, .loadN 170056 170056,
      .constN 170067 3, .addN 170056 170056 170067, .loadN 170056 170056,
      .addN 170059 170054 170056])

/-- The right candidate for `g = 0` is the start of the block (its end is covered). -/
def candR : Stmt :=
  .ifLtN 170052 170011 (block [.copyN 170059 170055])
    (block [.addN 170056 170016 170052, .loadN 170056 170056, .addN 170056 170056 170051,
      .addN 170056 170056 170051, .addN 170056 170056 170051, .loadN 170056 170056,
      .constN 170067 3, .addN 170056 170056 170067, .loadN 170056 170056,
      .addN 170059 170055 170056])

/-- The running maximum: `170046 := 170059` if it is higher. -/
def cmpUpd : Stmt :=
  .seq (block [.constN 170060 0, .copyN 170061 170046, .constN 170063 0, .copyN 170064 170059])
    (.seq (SweepPrim.kbit 170060 170063 170060 1 170066)
      (.ifLtN 170012 170066 (block [.copyN 170046 170059]) .skip))

/-- The left block of a grade (if `q_l` is odd). -/
def stepL : Stmt :=
  .ifLtN 170012 170058
    (.seq candL (.seq cmpUpd (block [.addN 170050 170050 170011, .addN 170054 170054 170053])))
    .skip

/-- The right block of a grade (if `q_r` is odd). -/
def stepR : Stmt :=
  .ifLtN 170012 170058
    (.seq (block [.subN 170051 170051 170011, .subN 170055 170055 170053]) (.seq candR cmpUpd))
    .skip

/-- The next grade. -/
def halve : Stmt :=
  block [.addN 170056 170017 170050, .loadN 170050 170056, .addN 170056 170017 170051,
    .loadN 170051 170056, .addN 170052 170052 170011, .addN 170053 170053 170053]

/-- One grade of the cover. -/
def topBody : Stmt := .seq parL (.seq stepL (.seq parR (.seq stepR halve)))

/-- **The cover of `[x, y]`** (`x` in `170050`, `y` in `170051` on entry; the maximum already
covers both ends). -/
def topLoop : Stmt :=
  .seq (block [.constN 170052 0, .constN 170053 1, .copyN 170054 170050, .copyN 170055 170051])
    (.whileLtN 170050 170051 topBody)

/-- The height of vertex `v` of `Q`. -/
noncomputable abbrev Y (P : Polygon) (v : ℕ) : ℝ := ((Qof P).vtx v).2

/-- The top index read from the grade block descriptor. -/
def blkT (m : ℕ → ℕ) (h g b : ℕ) : ℕ := m (blkD m h g b + 3)


theorem pow_le_of_cap {g Λ d : ℕ} (hg : 1 ≤ g) (h1 : 2 ^ g ≤ d) (h2 : d ≤ 2 ^ (Λ - 1)) :
    g < Λ := by
  have h3 := h1.trans h2
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  
  have : 1 ≤ Λ - 1 := by
    omega
  omega

theorem Y_max_le {P : Polygon} {a b : ℕ} :
    Y P a ≤ Y P (if Y P a < Y P b then b else a) ∧ Y P b ≤ Y P (if Y P a < Y P b then b else a) := by
  split_ifs with h
  · exact ⟨h.le, le_rfl⟩
  · exact ⟨le_rfl, not_lt.1 h⟩


def decCfg (c : Config) : Config :=
  { c with nreg := upd (upd c.nreg 170051 (c.nreg 170051 - c.nreg 170011)) 170055
                          (c.nreg 170055 - c.nreg 170053) }


theorem log_half_lt {d d' : ℕ} (h : 2 * d' ≤ d) (hd : 0 < d) :
    Nat.log 2 (2 * d') < Nat.log 2 (2 * d) := by
  have e : Nat.log 2 (2 * d) = Nat.log 2 d + 1 := by
    rw [mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
  rw [e]
  have := Nat.log_mono_right (b := 2) h
  omega


end
end IOrc
end Chazelle.Core
