module

public import Chazelle.Core.SweepEvBatch2
public import Chazelle.Core.SweepEvTasks4

/-!
# The sweep (WP-D), stage 3: one iteration of the event loop (RAM)

`iter win key orgs sh g = win ; [bF := 0, bN := 0] ; orgs (orgDo sh g) ; key`.  `iter_irs`: from the
invariant `LoopInv`, one iteration runs within a fixed cost and its stages are related by
`IterRel` (the window `WinOut`, the reset, the batch invariant over `iterO`, the next key
`KeyOut`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- The reset of the best candidate. -/
def resetL : List Instr := [.constN bF 0, .constN bN 0]

/-- **One iteration of the event loop.** -/
def iter (win key : Stmt) (orgs : Stmt → Stmt) (sh g : Stmt) : Stmt :=
  .seq win (.seq (block resetL) (.seq (orgs (orgDo sh g)) key))

/-- The cost of one origin, for at most `2 (D + 1)` gathered arcs. -/
def odK (Fg D KG : ℕ) : ℕ := orgDoK Fg (2 * (D + 1)) KG

/-- The cost of one iteration. -/
def iterK (KW KK κO Fg D KG : ℕ) : ℕ :=
  KW + (2 + (((12 * D + 8) * (odK Fg D KG + κO) + κO) + KK))

theorem orgDoK_mono {Fg K K' KG : ℕ} (h : K ≤ K') : orgDoK Fg K KG ≤ orgDoK Fg K' KG := by
  unfold orgDoK evCandK evShotK ShotList.shotCost
  have := Nat.mul_le_mul_right (16 * Fg + 500000) (show K + 1 ≤ K' + 1 by omega)
  omega

theorem regArcs_length_le {N : NF} {rs : List ℕ} {B : ℕ}
    (h : ∀ r ∈ rs, (N.region r).arcs.length ≤ B) : (regArcs N rs).length ≤ rs.length * B := by
  induction rs with
  | nil => simp [regArcs]
  | cons r rs ih =>
    have h1 := h r List.mem_cons_self
    have h2 := ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    simp only [regArcs, List.flatMap_cons, List.length_append, List.length_cons] at h2 ⊢
    rw [Nat.succ_mul]
    omega

theorem regArcs_lt {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) {rs : List ℕ}
    (hrs : ∀ r ∈ rs, r < N.nRegions) : ∀ a ∈ regArcs N rs, a < N.arcs.length := by
  intro a ha
  unfold regArcs at ha
  obtain ⟨r, hr, har⟩ := List.mem_flatMap.1 ha
  exact (((regOf_spec hN).2.2.1.2.2.2 r (hrs r hr) a).1 har).1

/-- The registers an iteration does not write. -/
def KeepR (r : ℕ) : Prop :=
  240000 ≤ r ∧ r < 250000 ∧ ¬ WR r ∧ r ≠ bF ∧ r ≠ bN ∧ ¬ OrgR r ∧ ¬ LR r

end

end SweepEv

end Chazelle.Core
