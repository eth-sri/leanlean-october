module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoS0CandBsSpec

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 stop and table candidates

The initialisation of `S0CandSpec` builds a **slot table** at the base `sB = sw 620`: one slot of
three words per log record `i < E` and direction `s ≤ 1` (`s = 0`: east, `dS 0 = 1`; `s = 1`: west)
at `slotA B i s = B + 6 i + 3 s`: a flag, and (flag `1`) a walk position `(e, h)` of the model of
`C₂` whose point is a candidate origin (`CandAt`) for the point of log record `i` in the direction
of the slot (`SlotOK`).  Every stop record (direction code `b`, slot `sOf b`) and every regular
table entry `j` with flag `1` (slot `j % 2`) is attached at a log record with the same position
whose slot is flagged (`AuxCore`).

`Aux` is `AuxCore` up to the registers outside `sw 0 … 699` and `sw 11`, and the memory above a
bound `A₀` below the allocator: it is robust along `IInv` (`aux_iinv`) and under writes of
`sw 11` (`aux_sw11`); `aux_of_core` turns `AuxCore` at the end of the initialisation into `Aux`.

`InitPartSpec`: the contract of the initialisation (`InitSpec` with this `Aux`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Chain (sidePt)

@[expose] public section

/-- The base of the slot table. -/
def sB : ℕ := sw 620

/-- The slot of a stop record with direction code `b` (`0` for east). -/
def sOf (b : ℕ) : ℕ := if b = 1 then 0 else 1

/-- The direction of slot `s`. -/
noncomputable def dS (s : ℕ) : ℝ := if s = 0 then 1 else -1

/-- The address of slot `(i, s)`. -/
def slotA (B i s : ℕ) : ℕ := B + 6 * i + 3 * s

/-- The walk position of log record `i` (memory `m`, base `AL`). -/
def logPos (m : ℕ → ℕ) (AL i : ℕ) : WPos := ⟨m (AL + 7 * i), m (AL + 7 * i + 1)⟩

section
variable (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ)
include P J m
/-- The point of the walk of `C` at log record `i`. -/
noncomputable def logPt (AL i : ℕ) : Point :=
  sidePt (chainModel J.whole).W (logPos m AL i).edge
    ((chainModel J.whole).param (Qof P) (logPos m AL i))

/-- **A good slot**: flag `≤ 1`; flag `1`: a proper position of the model of `C₂` whose point is a
candidate origin for the point of log record `i` in the direction of the slot. -/
def SlotOK (B AL i s : ℕ) : Prop :=
  m (slotA B i s) ≤ 1 ∧
    (m (slotA B i s) = 1 →
      m (slotA B i s + 1) < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n ⟨m (slotA B i s + 1), m (slotA B i s + 2)⟩ ∧
      S0C.CandAt J ((chainModel J.right).pos (Qof P) ⟨m (slotA B i s + 1), m (slotA B i s + 2)⟩)
        (dS s) (logPt P J m AL i))


end

/-- A regular endpoint query: its origin is a point of `C₂`, neither the shared vertex nor the
top. -/
def ValidO (J : Merge.Junction) (Q : Polygon) (N : NF) (j : ℕ) : Prop :=
  endOrigin J Q N j ∈ J.right.set ∧ endOrigin J Q N j ≠ J.shared ∧
    endOrigin J Q N j ≠ J.right.top

section
variable (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config)
include P J N₂ c
/-- **The slot table** in the configuration `c`. -/
def AuxCore : Prop :=
  c.nreg sB + 6 * rd c bSweep 301 ≤ c.nreg ALLOC ∧
  rd c bSweep 300 + 7 * rd c bSweep 301 ≤ c.nreg ALLOC ∧
  rd c bSweep 200 + 5 * rd c bSweep 201 ≤ c.nreg ALLOC ∧
  rd c bSweep 302 + 3 * (2 * N₂.nChords) ≤ c.nreg ALLOC ∧
  (∀ i, i < rd c bSweep 301 → ∀ s, s ≤ 1 →
    SlotOK P J c.nmem (c.nreg sB) (rd c bSweep 300) i s) ∧
  (∀ x, x < rd c bSweep 201 → ∃ i, i < rd c bSweep 301 ∧
    c.nmem (rd c bSweep 300 + 7 * i) = c.nmem (rd c bSweep 200 + 5 * x) ∧
    (chainModel J.whole).param (Qof P) (logPos c.nmem (rd c bSweep 300) i) =
      (chainModel J.whole).param (Qof P)
        ⟨c.nmem (rd c bSweep 200 + 5 * x), c.nmem (rd c bSweep 200 + 5 * x + 1)⟩ ∧
    c.nmem (slotA (c.nreg sB) i (sOf (c.nmem (rd c bSweep 200 + 5 * x + 4)))) = 1) ∧
  (∀ j, j < 2 * N₂.nChords → ValidO J (Qof P) N₂ j → c.nmem (rd c bSweep 302 + 3 * j) = 1 →
    ∃ i, i < rd c bSweep 301 ∧
    c.nmem (rd c bSweep 300 + 7 * i) = c.nmem (rd c bSweep 302 + 3 * j + 1) ∧
    (chainModel J.whole).param (Qof P) (logPos c.nmem (rd c bSweep 300) i) =
      (chainModel J.whole).param (Qof P)
        ⟨c.nmem (rd c bSweep 302 + 3 * j + 1), c.nmem (rd c bSweep 302 + 3 * j + 2)⟩ ∧
    c.nmem (slotA (c.nreg sB) i (j % 2)) = 1)

/-- **The auxiliary fact of the side-0 initialisation**: the slot table, for every configuration
agreeing on the fixed registers (except `sw 11`) and on the memory below a bound `A₀`. -/
def Aux : Prop :=
  ∃ A₀, A₀ ≤ c.nreg ALLOC ∧ ∀ c' : Config, (∀ q, IFix q → q ≠ sw 11 → c'.nreg q = c.nreg q) →
    (∀ a, a < A₀ → c'.nmem a = c.nmem a) → A₀ ≤ c'.nreg ALLOC → AuxCore P J N₂ c'


end

/-- `Aux` is robust along `IInv`. -/
theorem aux_iinv {P : Polygon} {W : ℕ} {J : Merge.Junction} {N₂ : NF} {c₀ c : Config}
    (h : Aux P J N₂ c₀) (hI : IInv W c₀ c) : Aux P J N₂ c := by
  obtain ⟨A₀, hA₀, h⟩ := h
  refine ⟨A₀, le_trans hA₀ hI.hA, fun c' hr hm hA => h c' (fun q hq hq11 => ?_)
    (fun a ha => ?_) hA⟩
  all_goals ram_grind

/-- `Aux` survives a write of `sw 11`. -/
theorem aux_sw11 {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config} {v : ℕ}
    (h : Aux P J N₂ c) : Aux P J N₂ { c with nreg := upd c.nreg (sw 11) v } := by
  obtain ⟨A₀, hA₀, h⟩ := h
  have hAl : upd c.nreg (sw 11) v ALLOC = c.nreg ALLOC := upd_other _ _ _ (by omega_nf)
  refine ⟨A₀, by ram_grind,
    fun c' hr hm hA => h c' (fun q hq hq11 => ?_) hm hA⟩
  ram_simp 

theorem rd_sw (c : Config) (k : ℕ) : rd c bSweep k = c.nreg (sw k) := rfl

section
variable {P : Polygon} {J : Merge.Junction} {N₂ : NF}
/-- **`AuxCore` is local**: it depends only on the fixed registers other than `sw 11` and on the
memory below the allocator. -/
theorem auxCore_transport {c c' : Config}
    (h : AuxCore P J N₂ c) (hr : ∀ q, IFix q → q ≠ sw 11 → c'.nreg q = c.nreg q)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    AuxCore P J N₂ c' := by
  have fx : ∀ k, k < 700 → k ≠ 11 → c'.nreg (sw k) = c.nreg (sw k) := fun k hk h11 =>
    hr _ (by omega_nf) (by omega_nf)
  obtain ⟨b1, b2, b3, b4, hsl, hst, htb⟩ := h
  simp only [AuxCore, rd_sw] at *
  have eB : c'.nreg sB = c.nreg sB := fx 620 (by norm_num) (by norm_num)
  have e200 := fx 200 (by norm_num) (by norm_num)
  have e201 := fx 201 (by norm_num) (by norm_num)
  have e300 := fx 300 (by norm_num) (by norm_num)
  have e301 := fx 301 (by norm_num) (by norm_num)
  have e302 := fx 302 (by norm_num) (by norm_num)
  rw [eB, e200, e201, e300, e301, e302]
  set B := c.nreg sB
  set AL := c.nreg (sw 300)
  set E := c.nreg (sw 301)
  set AS := c.nreg (sw 200)
  set S := c.nreg (sw 201)
  set AT := c.nreg (sw 302)
  
  have mL0 : ∀ i, i < E → c'.nmem (AL + 7 * i) = c.nmem (AL + 7 * i) := fun i hi => by
    ram_grind
  have mS : ∀ x, x < S → ∀ d, d < 5 → c'.nmem (AS + 5 * x + d) = c.nmem (AS + 5 * x + d) :=
    fun x hx d hd => hm _ (by nlinarith)
  have mS0 : ∀ x, x < S → c'.nmem (AS + 5 * x) = c.nmem (AS + 5 * x) := fun x hx => by
    ram_grind
  have mT : ∀ j, j < 2 * N₂.nChords → ∀ d, d < 3 → c'.nmem (AT + 3 * j + d) = c.nmem (AT + 3 * j + d) :=
    fun j hj d hd => hm _ (by nlinarith)
  have mT0 : ∀ j, j < 2 * N₂.nChords → c'.nmem (AT + 3 * j) = c.nmem (AT + 3 * j) := fun j hj => by
    ram_grind
  have mB : ∀ i, i < E → ∀ s, s ≤ 1 → ∀ d, d < 3 →
      c'.nmem (slotA B i s + d) = c.nmem (slotA B i s + d) :=
    fun i hi s hs d hd => hm _ (by ram_grind)
  have mB0 : ∀ i, i < E → ∀ s, s ≤ 1 → c'.nmem (slotA B i s) = c.nmem (slotA B i s) :=
    fun i hi s hs => by ram_grind
  have hlogPos : ∀ i, i < E → logPos c'.nmem AL i = logPos c.nmem AL i := fun i hi => by
    grind [logPos]
  have hlogPt : ∀ i, i < E → logPt P J c'.nmem AL i = logPt P J c.nmem AL i := fun i hi => by
    grind [logPt]
  refine ⟨by omega, by omega, by omega, by omega, fun i hi s hs => ?_, fun x hx => ?_,
    fun j hj hv hf => ?_⟩
  · obtain ⟨f1, f2⟩ := hsl i hi s hs
    unfold SlotOK
    rw [mB0 i hi s hs, mB i hi s hs 1 (by norm_num), mB i hi s hs 2 (by norm_num),
      hlogPt i hi]
    ram_grind
  · obtain ⟨i, hi, e1, e2, e3⟩ := hst x hx
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · ram_grind
    · rw [hlogPos i hi, mS0 x hx, mS x hx 1 (by norm_num), e2]
    · rw [mS x hx 4 (by norm_num), mB0 i hi _ (by unfold sOf; grind), e3]
  · obtain ⟨i, hi, e1, e2, e3⟩ := htb j hj hv (by ram_grind)
    refine ⟨i, hi, ?_, ?_, ?_⟩
    · rw [mL0 i hi, mT j hj 1 (by norm_num), e1]
    · rw [hlogPos i hi, mT j hj 1 (by norm_num), mT j hj 2 (by norm_num), e2]
    ram_grind

/-- **`AuxCore` gives `Aux`.** -/
theorem aux_of_core {c : Config}
    (h : AuxCore P J N₂ c) : Aux P J N₂ c :=
  ⟨c.nreg ALLOC, le_rfl, fun _c' hr hm hA => auxCore_transport h hr hm hA⟩

/-- **`Aux` at a configuration gives `AuxCore` there.** -/
theorem core_of_aux {c : Config}
    (h : Aux P J N₂ c) : AuxCore P J N₂ c := by
  obtain ⟨A₀, hA₀, h⟩ := h
  grind


end

/-- **The contract of the initialisation** of the side-0 stop and table candidates. -/
def InitPartSpec : Prop := ∃ (initC : Stmt) (κ : ℕ → ℕ), InitSpec initC Aux κ

end

end S0C

end SweepIo

end Chazelle.Core
