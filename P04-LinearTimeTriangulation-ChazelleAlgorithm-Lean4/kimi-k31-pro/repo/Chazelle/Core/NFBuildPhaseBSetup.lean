module

public import Chazelle.Core.NFBuildFinal
public import Chazelle.Core.NFBuildPassStep

/-!
# WP-C (BuildNF), RAM part 20: the setup of phase B

`setupB` allocates the output tables and the work arrays of phase B at `H = ALLOC`
(`CT = H + 12`, `AT = CT + 5K`, `RT = AT + 10K`, `QT = RT + 5R`, `LT = QT + 2K`, `ST = LT + 4K`,
`WT = ST + 2K`, `CA = WT + 2K`, `FA = CA + 3R`, `FC = FA + R`, new `ALLOC = FC + R`, with
`R = K + 1`), and initialises the registers of the main pass.  `BConst`: the registers that stay
fixed during phase B.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The setup of phase B. -/
def setupB : Stmt :=
  block [.constN 42102 1, .constN 43013 3, .addN 43200 43002 43011,
    .copyN 44000 9999,
    .constN 43240 12, .addN 44001 44000 43240,
    .addN 43241 43002 43002, .addN 43241 43241 43241, .addN 43241 43241 43002,
    .addN 44002 44001 43241,
    .addN 43242 42001 42001, .addN 43242 43242 43242, .addN 43242 43242 42001,
    .addN 44003 44002 43242,
    .addN 43243 43200 43200, .addN 43243 43243 43243, .addN 43243 43243 43200,
    .addN 44004 44003 43243,
    .addN 44005 44004 42001,
    .addN 43244 42001 43002, .addN 43244 43244 43002, .addN 44006 44005 43244,
    .addN 44007 44006 42001, .addN 44008 44007 42001,
    .addN 43245 43200 43200, .addN 43245 43245 43200, .addN 44011 44008 43245,
    .addN 44012 44011 43200, .addN 9999 44012 43200,
    .constN 43100 0, .constN 43101 0, .constN 43102 0, .copyN 43103 30005, .copyN 43104 30005]

/-- The size of the tables of phase B. -/
def sizeB (K : ℕ) : ℕ := 35 * K + 22

/-- The registers that stay fixed during phase B (after its setup). -/
structure BConst (D T K B H lo hd kd : ℕ) (d : Config) : Prop where
  rD : d.nreg 40000 = D
  rT : d.nreg 42000 = T
  rN : d.nreg 42001 = 2 * K
  r1a : d.nreg 42102 = 1
  rB : d.nreg 43001 = B
  rK : d.nreg 43002 = K
  r0 : d.nreg 43010 = 0
  r1 : d.nreg 43011 = 1
  r3 : d.nreg 43013 = 3
  rR : d.nreg 43200 = K + 1
  rH : d.nreg 44000 = H
  rCT : d.nreg 44001 = H + 12
  rAT : d.nreg 44002 = H + 12 + 5 * K
  rRT : d.nreg 44003 = H + 12 + 15 * K
  rQT : d.nreg 44004 = H + 17 + 20 * K
  rLT : d.nreg 44005 = H + 17 + 22 * K
  rST : d.nreg 44006 = H + 17 + 26 * K
  rWT : d.nreg 44007 = H + 17 + 28 * K
  rCA : d.nreg 44008 = H + 17 + 30 * K
  rFA : d.nreg 44011 = H + 20 + 33 * K
  rFC : d.nreg 44012 = H + 21 + 34 * K
  rA : d.nreg 9999 = H + sizeB K
  rlo : d.nreg 44020 = lo
  rhd : d.nreg 44021 = hd
  r19 : d.nreg 41019 = 1
  r23 : d.nreg 41023 = kd

/-- The fixed registers. -/
def constRegs : List ℕ :=
  [40000, 42000, 42001, 42102, 43001, 43002, 43010, 43011, 43013, 43200, 44000, 44001, 44002,
    44003, 44004, 44005, 44006, 44007, 44008, 44011, 44012, 9999, 44020, 44021, 41019, 41023]

/-- The fixed registers survive a frame that does not write them. -/
theorem BConst.frame {D T K B H lo hd kd : ℕ} {d d' : Config} {Bw : ℕ → Bool}
    (h : BConst D T K B H lo hd kd d) (hf : FrameM Bw d d')
    (hB : ∀ r ∈ constRegs, Bw r = false) : BConst D T K B H lo hd kd d' := by
  have g : ∀ r ∈ constRegs, d'.nreg r = d.nreg r := fun r hr => hf.1 r (hB r hr)
  simp [constRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24, g25, g26⟩ := g
  exact ⟨by rw [g1, h.rD], by rw [g2, h.rT], by rw [g3, h.rN], by rw [g4, h.r1a],
    by rw [g5, h.rB], by rw [g6, h.rK], by rw [g7, h.r0], by rw [g8, h.r1], by rw [g9, h.r3],
    by rw [g10, h.rR], by rw [g11, h.rH], by rw [g12, h.rCT], by rw [g13, h.rAT],
    by rw [g14, h.rRT], by rw [g15, h.rQT], by rw [g16, h.rLT], by rw [g17, h.rST],
    by rw [g18, h.rWT], by rw [g19, h.rCA], by rw [g20, h.rFA], by rw [g21, h.rFC],
    by rw [g22, h.rA], by rw [g23, h.rlo], by rw [g24, h.rhd], by rw [g25, h.r19],
    by rw [g26, h.r23]⟩

section exec

variable {P : Polygon} {W : ℕ}

/-- The registers `setupB` writes. -/
def BsetupB (r : ℕ) : Bool :=
  decide (r ∈ [42102, 43013, 43200, 44000, 43240, 44001, 43241, 44002, 43242, 44003, 43243,
    44004, 44005, 43244, 44006, 44007, 44008, 43245, 44011, 44012, 9999, 43100, 43101,
    43102, 43103, 43104])

theorem wr_setupB : wr BsetupB setupB = true := by decide

/-- **The setup of phase B.** -/
theorem setupB_exec (d : Config) (hw : WordsBounded W d) {K H SE : ℕ}
    (hK : d.nreg 43002 = K) (hN : d.nreg 42001 = 2 * K) (h1 : d.nreg 43011 = 1)
    (hH : d.nreg 9999 = H) (hSE : d.nreg 30005 = SE) (hW : H + sizeB K ≤ W) :
    ∃ d' k, Exec P W setupB d d' k ∧ k = 34 ∧
      d'.nreg 42102 = 1 ∧ d'.nreg 43013 = 3 ∧ d'.nreg 43200 = K + 1 ∧ d'.nreg 44000 = H ∧
      d'.nreg 44001 = H + 12 ∧ d'.nreg 44002 = H + 12 + 5 * K ∧
      d'.nreg 44003 = H + 12 + 15 * K ∧ d'.nreg 44004 = H + 17 + 20 * K ∧
      d'.nreg 44005 = H + 17 + 22 * K ∧ d'.nreg 44006 = H + 17 + 26 * K ∧
      d'.nreg 44007 = H + 17 + 28 * K ∧ d'.nreg 44008 = H + 17 + 30 * K ∧
      d'.nreg 44011 = H + 20 + 33 * K ∧ d'.nreg 44012 = H + 21 + 34 * K ∧
      d'.nreg 9999 = H + sizeB K ∧ d'.nreg 43100 = 0 ∧ d'.nreg 43101 = 0 ∧
      d'.nreg 43102 = 0 ∧ d'.nreg 43103 = SE ∧ d'.nreg 43104 = SE := by
  unfold sizeB at hW
  have hW1 : 12 ≤ W := by omega
  unfold setupB
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hK, hN, h1, hH]; omega)
    | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> config_simp
  all_goals first
    | (simp (config := { failIfUnchanged := false }) only [hK, hN, h1, hH, hSE, sizeB]; omega)
    | (· simp (config := { failIfUnchanged := false }) only [hK, h1, hH, hSE])

end exec

end

end BuildRam

end Chazelle.Core
