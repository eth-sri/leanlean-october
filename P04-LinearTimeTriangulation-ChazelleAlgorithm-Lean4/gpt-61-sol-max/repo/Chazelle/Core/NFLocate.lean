module

public import Chazelle.Core.NFLocateMath

/-!
# Double identification on the RAM (WP-C, target 2)

`locStmt dirS` answers a query of `LocateSpec` (band `bLocate`, `lr i = 50000 + i`: `lr 0` model
descriptor, `lr 1` normal form, `lr 2`, `lr 3` the query position; output `lr 4`):

1. `dirS`: a **direction procedure** (contract `DirOK`) writes the direction code of the query
   edge (`WalkKey.dirCode`) into register `10502`; it is the only part that depends on the model
   (interior or chain walk), see `NFLocateDir`;
2. `locSetup`: copy the query into `10500`, `10501` and read the header of the normal form (arc
   count `A` into `10504`, arc area `AB` into `10503`, sequence table `SB` into `10505` and the
   search inputs `lr 103`, `lr 104`);
3. `SearchR.searchStmt WalkKey.keyCmp`: the binary search of the sequence table for the
   partition point `t` of `WalkKey.KeyPred` (target 1 gives its comparison contract);
4. `locFinish`: answer the arc at position `t - 1` of the table, or at `A - 1` if `t = 0`.

`locate_exec` proves the postcondition of `LocateSpec` for the model and normal form of the
precondition, under the hypotheses the machine needs (see the module `NFLocateSpec` for the
discussion): positions of the walk proper (query and arc starts), the normal form readable below
the allocator, and the WP-B fact `NFLoc.ArcCoverSpec`.
-/

namespace Chazelle.Core

namespace NFLoc

open Machine Machine.Stmt Programs SignK SearchR WalkKey
open Chazelle.Chain (sideInArc)

@[expose] public section

/-! ## Frames -/

/-- A register-frame (`FrameB`) whose written registers lie in the bands `S` and avoid `ALLOC` is
a `Frame S`. -/
theorem frame_of_frameB {B : ℕ → Bool} {S : Finset ℕ} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → bandOf r ∈ S ∧ r ≠ ALLOC) (k : ℕ) : Frame S c c' k := by
  have hA : B ALLOC = false := by
    by_contra h'
    exact (hB ALLOC (by simpa using h')).2 rfl
  have hal := h.1 ALLOC hA
  refine ⟨fun r hr _ => h.1 r ?_, fun r hr => h.2.1 r ?_, fun a _ => by rw [h.2.2.1],
    fun a _ => by rw [h.2.2.2.1], h.2.2.2.2, by rw [hal], by rw [hal]; omega⟩
  · by_contra h'
    exact hr (hB r (by simpa using h')).1
  · by_contra h'
    exact hr (hB r (by simpa using h')).1

/-! ## The direction procedure -/

/-- The registers a direction procedure may write: `10000 … 10502` (the sign kernel and the
answer) and `lr 30 … lr 99`. -/
def Bdir (r : ℕ) : Bool := decide (10000 ≤ r ∧ r < 10503) || decide (50030 ≤ r ∧ r < 50100)

/-- **Contract of a direction procedure** under the precondition `DPre`: at most `κd` steps,
writes only `Bdir`, and leaves in `10502` the direction code of the query edge `lr 2` of the model
described at `lr 0`. -/
def DirOK (dirS : Stmt) (κd : ℕ) (DPre : Polygon → ℕ → Config → Prop) : Prop :=
  ∀ P W c, WordsBounded W c → DPre P W c →
    ∃ c' k, Exec P W dirS c c' k ∧ k ≤ κd ∧ FrameB Bdir c c' ∧
      ∀ M, ModelDescAt c.nmem (c.nreg 50000) (Qof P) M →
        c'.nreg 10502 = dirCode M (c.nreg 50002)

/-! ## The program -/

/-- Copy the query, read the header of the normal form. -/
def locSetup : Stmt := block [.copyN 10500 50002, .copyN 10501 50003, .constN 50020 1,
  .addN 50021 50001 50020, .loadN 10504 50021, .addN 50021 50021 50020, .addN 50021 50021 50020,
  .addN 50021 50021 50020, .loadN 10503 50021, .addN 50021 50021 50020, .addN 50021 50021 50020,
  .loadN 10505 50021, .copyN 50103 10505, .copyN 50104 10504]

/-- The cost bound: `(κd + 340) (⌈log₂ A⌉ + 1)`. -/
def locCost (κd A : ℕ) : ℕ := (κd + 340) * (Nat.clog 2 A + 1)

/-- The registers written by `locSetup` and `locFinish`. -/
def Bloc (r : ℕ) : Bool :=
  decide (10500 ≤ r ∧ r < 10506) || decide (50000 ≤ r ∧ r < 50030) ||
    decide (50100 ≤ r ∧ r < 50117)

theorem wr_locSetup : wr Bloc locSetup = true := by decide

theorem Bloc_band (r : ℕ) (h : Bloc r = true) : bandOf r ∈ ({bLocate, bSign} : Finset ℕ) ∧
    r ≠ ALLOC := by
  unfold Bloc at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  unfold bandOf bLocate bSign ALLOC
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem Bdir_band (r : ℕ) (h : Bdir r = true) : bandOf r ∈ ({bLocate, bSign} : Finset ℕ) ∧
    r ≠ ALLOC := by
  unfold Bdir at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  unfold bandOf bLocate bSign ALLOC
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ## Uniqueness of what the layout determines -/

theorem aRec_ext {a b : ARec} (h1 : a.reg = b.reg) (h2 : a.s.edge = b.s.edge)
    (h3 : a.s.hgt = b.s.hgt) (h4 : a.e.edge = b.e.edge) (h5 : a.e.hgt = b.e.hgt) : a = b := by
  obtain ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ := a
  obtain ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ := b
  simp_all

theorem cRec_ext {a b : CRec} (h1 : a.h = b.h) (h2 : a.lp = b.lp) (h3 : a.rp = b.rp)
    (h4 : a.up = b.up) (h5 : a.dn = b.dn) : a = b := by
  obtain ⟨_, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _⟩ := b
  simp_all

/-- The layout determines the arc records. -/
theorem nfAt_arcs_eq {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N'.arcs = N.arcs := by
  have hl : N'.arcs.length = N.arcs.length := h'.2.1.symm.trans h.2.1
  apply List.ext_getElem hl
  intro j hj hj'
  have e := h.2.2.2.2.2.2.1 j hj'
  have e' := h'.2.2.2.2.2.2.1 j hj
  have a1 : N.arc j = N.arcs[j] := getD_of_lt _ hj'
  have a2 : N'.arc j = N'.arcs[j] := getD_of_lt _ hj
  rw [← a1, ← a2]
  exact aRec_ext (e'.1.symm.trans e.1) (e'.2.1.symm.trans e.2.1) (e'.2.2.1.symm.trans e.2.2.1)
    (e'.2.2.2.1.symm.trans e.2.2.2.1) (e'.2.2.2.2.symm.trans e.2.2.2.2)

/-- The layout determines the chord records. -/
theorem nfAt_chords_eq {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N'.chords = N.chords := by
  have hl : N'.chords.length = N.chords.length := h'.1.symm.trans h.1
  apply List.ext_getElem hl
  intro j hj hj'
  have e := h.2.2.2.2.2.1 j hj'
  have e' := h'.2.2.2.2.2.1 j hj
  have a1 : N.chord j = N.chords[j] := getD_of_lt _ hj'
  have a2 : N'.chord j = N'.chords[j] := getD_of_lt _ hj
  rw [← a1, ← a2]
  exact cRec_ext (e'.1.symm.trans e.1) (e'.2.1.symm.trans e.2.1) (e'.2.2.1.symm.trans e.2.2.1)
    (e'.2.2.2.1.symm.trans e.2.2.2.1) (e'.2.2.2.2.symm.trans e.2.2.2.2)

/-! ## Correctness of the procedure -/

/-- On table entries, the predicate of the search is `KeyPred`. -/
theorem cmpPr_eq {P : Polygon} {M : Model} {N : NF} {m : ℕ → ℕ} {B : ℕ} (hN : NFAt m B N)
    (x : WPos) (hx : ProperPos M (Qof P) P.n x)
    (hst : ∀ j, j < N.arcs.length → ProperPos M (Qof P) P.n (N.arc j).s) {j : ℕ}
    (hj : j < N.arcs.length) :
    cmpPr P x (dirCode M x.edge) (m (B + 4)) N.arcs.length m j = true ↔
      KeyPred M (Qof P) x (N.arc j).s := by
  unfold cmpPr
  rw [ite_eq_left hj]
  obtain ⟨-, e1, e2, -⟩ := hN.2.2.2.2.2.2.1 j hj
  have hs : (⟨m (m (B + 4) + 5 * j + 1), m (m (B + 4) + 5 * j + 2)⟩ : WPos) = (N.arc j).s := by
    rw [e1, e2]
  rw [hs]
  exact keyDec_iff hx (hst j hj)

end

end NFLoc

end Chazelle.Core
