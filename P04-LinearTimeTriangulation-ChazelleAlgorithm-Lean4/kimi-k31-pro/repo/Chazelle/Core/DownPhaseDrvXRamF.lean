module

public import Chazelle.Core.DownPhaseDrvXRamE
public import Chazelle.Rwx
public import Chazelle.SimpTactics

/-!
# Down phase, extraction (D6), RAM part 6: the main program; a kept chord

The statements `keptS` (a kept chord: its two interior walk edges, the two buckets, then the
five stores), `chS` (one chord record of `N_R`) and `loopS`; pure facts used by the run.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE)

@[expose] public section

/-! ## Pure facts -/

theorem two_mul_le_flatMap {α : Type} (l : List ℕ) (f : ℕ → List α)
    (h : ∀ a, 2 ≤ (f a).length) : 2 * l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := h a; omega

/-- A region has at most half as many arcs as its host has items. -/
theorem regHost_length_ge (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    2 * (N.region r).arcs.length ≤ (DrvR.regHost li n N r).length := by
  have hw : 2 * (N.region r).arcs.length ≤ (DrvR.walkItems li n N r).length := by
    unfold DrvR.walkItems
    have := two_mul_le_flatMap (List.range (N.region r).arcs.length)
      (fun t => DrvR.arcItems li n N r ((N.region r).arcs.getD t 0)
        ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0))
      (fun t => by unfold DrvR.arcItems; sio only [List.length_append, List.length_singleton])
    rwa [List.length_range] at this
  unfold DrvR.regHost
  split_ifs
  · exact hw
  · rwa [List.length_reverse]

/-- The host points of a well-formed host are in range. -/
theorem hpt_lt {n : ℕ} {H : Host} (hwf : HostWF n H) (hn : 0 < n) {k : ℕ}
    (hk : k < (H.pts n).length) : (hpt n H k).Lt n := by
  have hmem : hpt n H k ∈ H.pts n := by
    unfold hpt; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  unfold Host.pts at hmem
  obtain ⟨it, hit, hin⟩ := List.mem_flatMap.1 hmem
  have hw := hwf it hit
  rcases it with ⟨a, ℓ⟩ | x
  · simp only [HostItem.pts, List.mem_map, List.mem_range] at hin
    obtain ⟨t, -, ht⟩ := hin
    rw [← ht]; exact Nat.mod_lt _ hn
  · simp only [HostItem.pts, List.mem_singleton] at hin
    rwx [hin]

theorem pEdge_lt (li : Bool) {n : ℕ} {s : SymPt} (hs : s.Lt n) : pEdge li n s < n := by
  have hn : 0 < n := by cases s <;> simp only [SymPt.Lt] at hs <;> omega
  cases s with
  | vtx j => exact DownMath.ivB_lt li hs
  | onEdge e h =>
    simp only [pEdge]
    split_ifs
    · exact Nat.mod_lt _ hn
    · exact DownMath.qE_lt li hs.1

/-- Three registers encode a symbolic point. -/
def EncV (k a b : ℕ) : SymPt → Prop
  | .vtx j => k = 1 ∧ a = j
  | .onEdge e h => k = 2 ∧ a = e ∧ b = h

theorem enc_iff (d : Config) (s : SymPt) :
    Enc d s ↔ EncV (d.nreg 217070) (d.nreg 217071) (d.nreg 217072) s := by
  cases s <;> rfl

/-! ## The statements -/

/-- **A kept chord** (`217050 h`, `217053 h + 1`, the left host point in `217055 … 217057`, the
right one in `217070 … 217072`): interior walk edges, buckets, then the stores. -/
def keptS : Stmt := seqs [
  block [.copyN 217080 217070, .copyN 217081 217071, .copyN 217082 217072,
    .copyN 217070 217055, .copyN 217071 217056, .copyN 217072 217057],
  peS,
  block [.copyN 217084 217100, .copyN 217070 217080, .copyN 217071 217081, .copyN 217072 217082],
  peS,
  block [.copyN 217085 217100, .copyN 217110 217084, .copyN 217111 217053],
  bktS,
  block [.copyN 217086 217112, .copyN 217110 217085, .copyN 217111 217053],
  bktS,
  block [.copyN 217087 217112,
    .storeN 217045 217050, .addN 217045 217045 217027,
    .storeN 217045 217084, .addN 217045 217045 217027,
    .storeN 217045 217085, .addN 217045 217045 217027,
    .storeN 217046 217086, .addN 217046 217046 217027,
    .storeN 217046 217087, .addN 217046 217046 217027,
    .addN 217038 217038 217027]]

/-- **One chord record of `N_R`** (pointer `217040`). -/
def chS : Stmt := seqs [
  block [.loadN 217050 217040, .addN 217104 217040 217027, .loadN 217051 217104,
    .addN 217104 217104 217027, .loadN 217052 217104, .addN 217053 217050 217027,
    .copyN 217060 217051],
  clsS,
  block [.copyN 217054 217064, .copyN 217055 217070, .copyN 217056 217071, .copyN 217057 217072,
    .copyN 217060 217052],
  clsS,
  .ifLtN 217054 217027 (.ifLtN 217064 217027 .skip keptS) keptS,
  block [.addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217040 217040 217027,
    .addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217039 217039 217027]]

/-- The loop over the chord records of `N_R`. -/
def loopS : Stmt := .whileLtN 217039 217028 chS

/-! ## A kept chord -/

/-- The registers `keptS` writes. -/
def Bkept (r : ℕ) : Bool :=
  decide (r = 217038 ∨ r = 217045 ∨ r = 217046 ∨ (217070 ≤ r ∧ r ≤ 217072) ∨
    (217080 ≤ r ∧ r ≤ 217087) ∨ (217100 ≤ r ∧ r ≤ 217128) ∨ (217150 ≤ r ∧ r ≤ 217156) ∨
    (217160 ≤ r ∧ r ≤ 217162))

theorem wrM_kept : wrM Bkept keptS = true := by decide

end

end DrvX

end Chazelle.Core
