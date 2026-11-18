module

public import Chazelle.Core.SpecNF
public import Chazelle.Final.Interface
public import Chazelle.Machine.Structured

/-!
# Core specification, part 3: RAM conventions

Design decision D6 (`docs/design-chazelle-core.md` §6).  Programs of the visibility-map stage are
structured statements (`Chazelle.Machine.Stmt`) composed by `seq` (inlining; there are no
procedure calls), verified with the big-step cost semantics `Chazelle.Machine.Exec`.

## Registers

* `ALLOC` (natural register `9999`): the global **bump allocator**.  Every procedure may raise
  it and may write memory at addresses `≥` its value on entry; memory below it is read-only for
  the procedure.  A procedure raises it by at most its step count, so every address is at most
  the total cost, which is `≤ C (n + 1)`: this is how the word bound `K (n + 1)` is met.
* Registers `9990 … 9993`: the hand-off to the final stage (`REG_TRAP`, `REG_TRAPLEN`,
  `REG_CHORD`, `REG_CHORDLEN`).
* **Bands.**  Register `r` belongs to band `r / 10000`.  Band `0` (registers `< 10000`) is the
  final stage's and holds `ALLOC` and the hand-off registers; every procedure of the core owns
  one band `b ≥ 1` (table in the design document, §6.3) and may write only the bands of itself
  and of the procedures it inlines (`Frame`).  Inputs are passed in the callee's band.

## The judgement `Meets`

`Meets s bands Pre Post cost`: from every configuration satisfying `Pre` whose words are bounded by
`W` and whose allocator leaves room for `cost` more cells, `s` runs in at most `cost` steps (and
never exceeds `W`), establishes `Post`, and respects `Frame bands`.  `Meets.seq` (proved) composes
two judgements.

## Layouts

`NFAt` (normal forms, design doc §3.4), `HostAt`, `ChainDescAt`, `TrapTableAt`, `ChordTableAt`,
and `TablesReady`, the precondition of the final stage.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Machine (Stmt Exec)

/-! ## Registers and bands -/

/-- The allocator register. -/
def ALLOC : ℕ := 9999

/-- Hand-off: base address of the trapezoid table. -/
def REG_TRAP : ℕ := 9990
/-- Hand-off: length of the trapezoid table. -/
def REG_TRAPLEN : ℕ := 9991
/-- Hand-off: base address of the vertex-chord table. -/
def REG_CHORD : ℕ := 9992
/-- Hand-off: length of the vertex-chord table. -/
def REG_CHORDLEN : ℕ := 9993

/-- The band of a register. -/
def bandOf (r : ℕ) : ℕ := r / 10000

/-- Register `i` of band `b`. -/
def bandReg (b i : ℕ) : ℕ := 10000 * b + i

theorem bandOf_bandReg (b i : ℕ) (hi : i < 10000) : bandOf (bandReg b i) = b := by
  unfold bandOf bandReg
  omega

theorem bandOf_alloc : bandOf ALLOC = 0 := by decide

/-! ## Frames and the judgement -/

/-- **The frame of a procedure** writing the bands `bands`: other registers (except `ALLOC`)
are unchanged, memory below the entry value of `ALLOC` is unchanged, nothing is emitted, and
`ALLOC` grows by at most the step count `k`. -/
def Frame (bands : Finset ℕ) (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ bands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ bands → c'.rreg r = c.rreg r) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

/-- **The specification judgement** of a structured statement. -/
def Meets (s : Stmt) (bands : Finset ℕ) (Pre : Polygon → ℕ → Config → Prop)
    (Post : Polygon → Config → Config → Prop) (cost : Polygon → Config → ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c : Config), WordsBounded W c → Pre P W c →
    c.nreg ALLOC + cost P c ≤ W →
      ∃ c' k, Exec P W s c c' k ∧ k ≤ cost P c ∧ Post P c c' ∧ Frame bands c c' k

/-- Frames compose. -/
theorem Frame.trans {B₁ B₂ : Finset ℕ} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : Frame B₁ c c₁ k₁)
    (h₂ : Frame B₂ c₁ c₂ k₂) : Frame (B₁ ∪ B₂) c c₂ (k₁ + k₂) := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h₁
  obtain ⟨r₂, rr₂, m₂, rm₂, o₂, a₂, b₂⟩ := h₂
  refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, o₂.trans o₁,
    a₁.trans a₂, by omega⟩
  · rw [Finset.mem_union, not_or] at hr
    rw [r₂ r hr.2 hra, r₁ r hr.1 hra]
  · rw [Finset.mem_union, not_or] at hr
    rw [rr₂ r hr.2, rr₁ r hr.1]
  · rw [m₂ a (lt_of_lt_of_le ha a₁), m₁ a ha]
  · rw [rm₂ a (lt_of_lt_of_le ha a₁), rm₁ a ha]

/-- A frame for fewer bands is a frame for more. -/
theorem Frame.mono {B B' : Finset ℕ} {c c' : Config} {k k' : ℕ} (h : Frame B c c' k)
    (hB : B ⊆ B') (hk : k ≤ k') : Frame B' c c' k' := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h
  exact ⟨fun r hr hra => r₁ r (fun h => hr (hB h)) hra, fun r hr => rr₁ r (fun h => hr (hB h)),
    m₁, rm₁, o₁, a₁, by omega⟩

/-! ## Normal forms in memory -/

/-- **The memory layout of a normal form** at the handle `B` (design doc §3.4).  Header
`B … B+11`: `B` number of chords, `B+1` arcs, `B+2` regions, `B+3 … B+8` the bases
`CB, AB, RB, SB, LB, DB` of the chord, arc, region, sequence, list and decomposition areas,
`B+9` the root code, `B+10` the base `PB` of the leaf-parent table, `B+11` the number of
decomposition nodes.  Chord `i` at
`CB + 5 i`: `h, lp, rp, up, dn`.  Arc `j` at `AB + 5 j`: `reg, s.edge, s.hgt, e.edge, e.hgt`.
Region `r` at `RB + 5 r`: number of arcs, start of its arc list in the list area `LB`, number of
chords, start of its chord list, weight.  Arc-sequence table at `SB`.  Decomposition node `k` at
`DB + 3 k`: `par, lo, hi`.  Leaf parents at `PB`. -/
def NFAt (m : ℕ → ℕ) (B : ℕ) (N : NF) : Prop :=
  m B = N.chords.length ∧ m (B + 1) = N.arcs.length ∧ m (B + 2) = N.regions.length ∧
    m (B + 9) = N.root ∧ m (B + 11) = N.dec.length ∧
    (∀ i, i < N.chords.length →
      m (m (B + 3) + 5 * i) = (N.chord i).h ∧ m (m (B + 3) + 5 * i + 1) = (N.chord i).lp ∧
      m (m (B + 3) + 5 * i + 2) = (N.chord i).rp ∧ m (m (B + 3) + 5 * i + 3) = (N.chord i).up ∧
      m (m (B + 3) + 5 * i + 4) = (N.chord i).dn) ∧
    (∀ j, j < N.arcs.length →
      m (m (B + 4) + 5 * j) = (N.arc j).reg ∧ m (m (B + 4) + 5 * j + 1) = (N.arc j).s.edge ∧
      m (m (B + 4) + 5 * j + 2) = (N.arc j).s.hgt ∧ m (m (B + 4) + 5 * j + 3) = (N.arc j).e.edge ∧
      m (m (B + 4) + 5 * j + 4) = (N.arc j).e.hgt) ∧
    (∀ r, r < N.regions.length →
      m (m (B + 5) + 5 * r) = (N.region r).arcs.length ∧
      m (m (B + 5) + 5 * r + 2) = (N.region r).chords.length ∧
      m (m (B + 5) + 5 * r + 4) = (N.region r).wt ∧
      (∀ t, t < (N.region r).arcs.length →
        m (m (B + 7) + m (m (B + 5) + 5 * r + 1) + t) = (N.region r).arcs.getD t 0) ∧
      (∀ t, t < (N.region r).chords.length →
        m (m (B + 7) + m (m (B + 5) + 5 * r + 3) + t) = (N.region r).chords.getD t 0)) ∧
    (∀ j, j < N.seq.length → m (m (B + 6) + j) = N.seq.getD j 0) ∧
    (∀ k, k < N.dec.length →
      m (m (B + 8) + 3 * k) = (N.dnode k).par ∧ m (m (B + 8) + 3 * k + 1) = (N.dnode k).lo ∧
      m (m (B + 8) + 3 * k + 2) = (N.dnode k).hi) ∧
    (∀ r, r < N.lpar.length → m (m (B + 10) + r) = N.lpar.getD r 0)

/-- **Robust memory facts**: `Φ` holds of every memory that agrees with `m` below `A`. -/
def Robust (A : ℕ) (m : ℕ → ℕ) (Φ : (ℕ → ℕ) → Prop) : Prop :=
  ∀ m' : ℕ → ℕ, (∀ a, a < A → m' a = m a) → Φ m'

/-- **The normal form at `B` is protected below `E`**: it can be read at `B` from every memory
agreeing with `m` below `E`, so it survives every later frame once `E` is at most the allocator.
(Review finding F3/R3: the earlier definition bounded the areas but not the per-region list
offsets, so it did not imply this.) -/
def NFWithin (m : ℕ → ℕ) (B E : ℕ) (N : NF) : Prop := Robust E m fun m' => NFAt m' B N

/-- A robust fact holds. -/
theorem Robust.holds {A : ℕ} {m : ℕ → ℕ} {Φ : (ℕ → ℕ) → Prop} (h : Robust A m Φ) : Φ m :=
  h m fun _ _ => rfl

/-- A robust fact survives any change of the memory at or above its bound. -/
theorem Robust.transport {A : ℕ} {m m' : ℕ → ℕ} {Φ : (ℕ → ℕ) → Prop} (h : Robust A m Φ)
    (hm : ∀ a, a < A → m' a = m a) : Robust A m' Φ :=
  fun m'' h'' => h m'' fun a ha => (h'' a ha).trans (hm a ha)

/-- A robust fact is robust for any larger bound. -/
theorem Robust.mono {A A' : ℕ} {m : ℕ → ℕ} {Φ : (ℕ → ℕ) → Prop} (h : Robust A m Φ)
    (hA : A ≤ A') : Robust A' m Φ :=
  fun m'' h'' => h m'' fun a ha => h'' a (lt_of_lt_of_le ha hA)

/-- A robust fact at the allocator survives a frame. -/
theorem Robust.frame {B : Finset ℕ} {c c' : Config} {k : ℕ} {Φ : (ℕ → ℕ) → Prop}
    (h : Robust (c.nreg ALLOC) c.nmem Φ) (hf : Frame B c c' k) :
    Robust (c'.nreg ALLOC) c'.nmem Φ :=
  (h.transport fun a ha => hf.2.2.1 a ha).mono hf.2.2.2.2.2.1

/-- A normal form protected below `E` can be read. -/
theorem NFWithin.nfAt {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) : NFAt m B N :=
  Robust.holds h

/-! ## Hosts and chains in memory -/

/-- **Host layout** at `B`: the number of items, then three words per item: kind (`0` run, `1`
vertex, `2` edge point) and two arguments. -/
def HostAt (m : ℕ → ℕ) (B : ℕ) (H : Host) : Prop :=
  m B = H.length ∧ ∀ i, i < H.length →
    match H.getD i (.run 0 0) with
    | .run a ℓ => m (B + 1 + 3 * i) = 0 ∧ m (B + 2 + 3 * i) = a ∧ m (B + 3 + 3 * i) = ℓ
    | .pt (.vtx j) => m (B + 1 + 3 * i) = 1 ∧ m (B + 2 + 3 * i) = j
    | .pt (.onEdge e h) => m (B + 1 + 3 * i) = 2 ∧ m (B + 2 + 3 * i) = e ∧ m (B + 3 + 3 * i) = h

/-- **Chain descriptor** at `B`: host handle, start `s`, number of edges `m`, top index (relative
to the chain) and the orientation bit `sideBeta` (`1` = true).  The descriptor describes the chain
`C` of the host `H` realised in `Q`. -/
def ChainDescAt (m : ℕ → ℕ) (B : ℕ) (Q : Polygon) (H : Host) (C : Chain) : Prop :=
  HostAt m (m B) H ∧ C.P = H.poly Q ∧ m (B + 1) = C.s ∧ m (B + 2) = C.m ∧
    m (B + 3) = C.topIdx ∧ (m (B + 4) = 1 ↔ C.sideBeta = true)

/-- **Model descriptor** at `B`: `m B = 0` and a chain descriptor at `B + 1` (chain model), or
`m B = 1` (interior model of `Q`) with the orientation bit `m (B + 1) = 1 ↔ LeftInside Q`, which
fixes the direction of the interior walk (review finding C3: without it, comparing keys on one
walk edge would cost `O(n)`). -/
def ModelDescAt (m : ℕ → ℕ) (B : ℕ) (Q : Polygon) (M : Model) : Prop :=
  (m B = 0 ∧ ∃ H C, ChainDescAt m (B + 1) Q H C ∧ M = chainModel C) ∨
    (m B = 1 ∧ (m (B + 1) = 1 ↔ Mountain.LeftInside Q) ∧ M = interiorModel Q)

/-! ## Well-formed descriptors (review findings C7, C8) -/

/-- **The word bound of the procedures that handle host curves**: `256 n + 16`.  A well-formed
host (`HostWF`, at most `64` items) has at most `64 n` points (`Host.pts_length_le`), so the index
arithmetic modulo the number `N` of host points (values `< 2 N`) stays within the word bound.
The phases get this bound from their budget `κ (n + 1)` (take `κ ≥ 272`).  (Finding S6: `+ 8`
rather than `+ 3`, since walk edges of a chain model of `≤ 64 n` host points reach `128 n + 4`.
Finding R-W1: the search of Lemma 3.2 adds two walk positions of a chain model, `< 2 (128 n + 7)`,
hence `256 n + 16`.) -/
def hostWords (n : ℕ) : ℕ := 256 * n + 16

/-- **A well-formed chain descriptor** at `B`, stored below `E` (findings C7, C8): the
descriptor words `B … B + 4` and the host layout lie below `E`; the host has at most `64` items
and is well formed (`HostWF`: runs and points in range); the start of the chain is below the
number of host points.  With `E` the allocator, the descriptor survives every later frame. -/
def ChainWF (P : Polygon) (E : ℕ) (m : ℕ → ℕ) (B : ℕ) : Prop :=
  B + 5 ≤ E ∧ ∀ H C, ChainDescAt m B (Qof P) H C →
    H.length ≤ 64 ∧ HostWF P.n H ∧ m B + 3 * H.length + 4 ≤ E ∧ C.s < C.P.n

/-- **A well-formed model descriptor** at `B`, stored below `E`: six words below `E`, and a
well-formed chain descriptor if it describes a chain model (finding C7: a handle near the word
bound could not be read; C8: host descriptors). -/
def ModelDescWF (P : Polygon) (E : ℕ) (m : ℕ → ℕ) (B : ℕ) : Prop :=
  B + 6 ≤ E ∧ (m B = 0 → ChainWF P E m (B + 1))

theorem ChainWF.mono {P : Polygon} {E E' : ℕ} {m : ℕ → ℕ} {B : ℕ} (h : ChainWF P E m B)
    (hE : E ≤ E') : ChainWF P E' m B :=
  ⟨by have := h.1; omega, fun H C hC => by
    obtain ⟨h1, h2, h3, h4⟩ := h.2 H C hC
    exact ⟨h1, h2, by omega, h4⟩⟩

theorem ModelDescWF.mono {P : Polygon} {E E' : ℕ} {m : ℕ → ℕ} {B : ℕ} (h : ModelDescWF P E m B)
    (hE : E ≤ E') : ModelDescWF P E' m B :=
  ⟨by have := h.1; omega, fun h0 => (h.2 h0).mono hE⟩

/-! ## The hand-off to the final stage -/

/-- The trapezoid table at `B`: four words per record (`left, right, top, bot`). -/
def TrapTableAt (m : ℕ → ℕ) (B : ℕ) (T : Final.TrapTable) : Prop :=
  ∀ i, i < T.length →
    m (B + 4 * i) = (T.getD i ⟨0, 0, 0, 0⟩).left ∧ m (B + 4 * i + 1) = (T.getD i ⟨0, 0, 0, 0⟩).right ∧
      m (B + 4 * i + 2) = (T.getD i ⟨0, 0, 0, 0⟩).top ∧
      m (B + 4 * i + 3) = (T.getD i ⟨0, 0, 0, 0⟩).bot

/-- The vertex-chord table at `B`: three words per record (`src`, direction bit (`1` = right),
`dst`). -/
def ChordTableAt (m : ℕ → ℕ) (B : ℕ) (Cs : List Final.ChordRec) : Prop :=
  ∀ i, i < Cs.length →
    m (B + 3 * i) = (Cs.getD i ⟨0, false, 0⟩).src ∧
      (m (B + 3 * i + 1) = 1 ↔ (Cs.getD i ⟨0, false, 0⟩).dir = true) ∧
      m (B + 3 * i + 2) = (Cs.getD i ⟨0, false, 0⟩).dst

/-- **The precondition of the final stage**: valid tables for the geometry polygon `Q` in memory,
announced in the hand-off registers, below the allocator; nothing emitted yet. -/
def TablesReady (Q : Polygon) (c : Config) : Prop :=
  ∃ (T : Final.TrapTable) (Cs : List Final.ChordRec),
    Final.IsTrapTable Q T ∧ Final.IsVtxChordTable Q Cs ∧
    c.nreg REG_TRAPLEN = T.length ∧ TrapTableAt c.nmem (c.nreg REG_TRAP) T ∧
    c.nreg REG_CHORDLEN = Cs.length ∧ ChordTableAt c.nmem (c.nreg REG_CHORD) Cs ∧
    c.nreg REG_TRAP + 4 * T.length ≤ c.nreg ALLOC ∧
    c.nreg REG_CHORD + 3 * Cs.length ≤ c.nreg ALLOC ∧
    c.output = []

end

end Chazelle.Core
