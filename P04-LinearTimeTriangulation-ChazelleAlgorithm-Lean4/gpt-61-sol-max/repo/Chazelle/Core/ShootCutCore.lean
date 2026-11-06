module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutItem
public import Chazelle.Core.ShootCutStep
public import Chazelle.Core.ShootCutBreak

/-!
# WP-G, part 14: the contract of `emit` and the invariants of the core

* `PcRegs`: the piece in the registers `150050 … 150058`;
* `EmitOK`: the contract of an `emit` statement with invariant `I` on the list of pieces handed so
  far: from any valid piece it extends the list, keeps the registers `Keep` of the core and the
  memory below `A₀`, and costs at most `K`;
* `CoreRegs`: the fixed registers of the core after the set-up;
* `PsOK`: the list of pieces from the start `s` to the walk vertex `v`: consecutive, valid.
-/

namespace Chazelle.Core

@[expose] public section

open Machine Machine.Stmt Programs SignK

namespace ShootCut

/-- The piece `pc` is in the registers `150050 …`. -/
def PcRegs (c : Config) (pc : Pc) : Prop :=
  c.nreg 150050 = pc.s.edge ∧ c.nreg 150051 = pc.s.hgt ∧ c.nreg 150052 = pc.e.edge ∧
    c.nreg 150053 = pc.e.hgt ∧ c.nreg 150054 = pc.kind ∧
    (pc.kind = 1 → c.nreg 150055 = pc.entry ∧ c.nreg 150056 = pc.x0 ∧ c.nreg 150057 = pc.dir ∧
      c.nreg 150058 = pc.pw)

/-- The registers of the core that `emit` keeps. -/
def Keep (r : ℕ) : Prop := (150000 ≤ r ∧ r < 150044) ∨ (150080 ≤ r ∧ r < 150100)

/-- The scratch registers of the core: `150020 …` of band `bCut`, the sign kernel (band `1`) and
the host routines (band `5`). -/
def Scr (r : ℕ) : Bool :=
  decide (150020 ≤ r ∧ r < 150100) || decide (10000 ≤ r ∧ r < 20000) ||
    decide (50000 ≤ r ∧ r < 60000)

/-- **The contract of `emit`**: its invariant survives the core's scratch writes, and it extends
the list by any valid piece. -/
structure EmitOK (P : Polygon) (W : ℕ) (emit : Stmt) (A₀ : ℕ) (Pv : Pc → Prop)
    (I : List Pc → Config → Prop) (K : ℕ) : Prop where
  stable : ∀ ps c c', I ps c → FrameB Scr c c' → I ps c'
  run : ∀ ps pc c, WordsBounded W c → I ps c → PcRegs c pc → Pv pc →
    ∃ c' k, Exec P W emit c c' k ∧ k ≤ K ∧ I (ps ++ [pc]) c' ∧
      (∀ r, Keep r → c'.nreg r = c.nreg r) ∧ (∀ a, a < A₀ → c'.nmem a = c.nmem a)

/-- The list of pieces goes from `s` to the walk position `v`, consecutively. -/
def Chained : WPos → List Pc → WPos → Prop
  | s, [], v => s = v
  | s, pc :: ps, v => pc.s = s ∧ Chained pc.e ps v

theorem Chained.append {s v : WPos} : ∀ {ps : List Pc}, Chained s ps v → ∀ pc : Pc, pc.s = v →
    Chained s (ps ++ [pc]) pc.e
  | [], h, pc, hpc => by simp_all [Chained] <;> omega_nf
  | _ :: _, h, pc, hpc => ⟨h.1, Chained.append h.2 pc hpc⟩

/-- The fixed registers of the core (after `cPre`). -/
structure CoreRegs (P : Polygon) (C : Chain) (H : Host) (Hh MD h γ mode : ℕ) (s e : WPos)
    (m₀ : ℕ → ℕ) (c : Config) : Prop where
  chain : ChainRegs C (H.pts P.n).length Hh c
  h00 : c.nreg 150000 = MD
  h01 : c.nreg 150001 = s.edge
  h02 : c.nreg 150002 = s.hgt
  h03 : c.nreg 150003 = e.edge
  h04 : c.nreg 150004 = e.hgt
  h09 : c.nreg 150009 = γ
  h13 : c.nreg 150013 = h
  h20 : c.nreg 150020 = mode
  h27 : c.nreg 150027 = P.n
  h31 : c.nreg 150031 = 2 * C.m + 5
  h32 : c.nreg 150032 = 2 * C.m + 6
  h33 : c.nreg 150033 = m₀ h
  h34 : c.nreg 150034 = m₀ (h + 2)
  h35 : c.nreg 150035 = m₀ (h + 3)
  h36 : c.nreg 150036 = m₀ (h + 1) + 2
  h90 : c.nreg 150090 = 0
  h92 : c.nreg 150092 = 2

end ShootCut

end

end Chazelle.Core
