module

meta import Chazelle.Programs.RamEval

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.RestoreDescGeo
public import Chazelle.Core.RestoreTestSpec
public import Chazelle.Core.RestoreTEnv

/-!
# WP-E, the search on the RAM (`FindOK`), part 1: run steps

After its initialisation (configuration `c₀`), every intermediate configuration `c` of the search
satisfies `FInv`: the fixed registers (`FFix`: the inputs `81000 … 81006` and the data
`81011 … 81027` set by the initialisation) are unchanged, the allocator has not decreased and the
memory below the initial allocator is unchanged.

`FRS B P W c₀ s c K Q`: from `c`, the statement `s` runs in at most `K` steps to a configuration
satisfying `FInv` and `Q`, within the relative frame (bands `B`, memory below `c₀`'s allocator).
The combinators mirror those of the test (`RS`): `FRS.seq`, `FRS.ifT`, `FRS.ifF`, `FRS.while`,
register instructions on scratch registers (`FScr`: band `bRestore` from `81017` on, including
the test's registers from `83000`), and `FRS.call` for a statement with a `Meets` contract.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs

/-- A fixed register of the search: the caller's registers `80000 … 80999`, the inputs
`81000 … 81006` and the data `81011 … 81027` set once at the start (constants, model and region
data). -/
@[ram_layout] def FFix (q : ℕ) : Prop := (80000 ≤ q ∧ q < 81007) ∨ (81011 ≤ q ∧ q < 81028)

/-- **The search invariant**, relative to the configuration `c₀` reached after the
initialisation. -/
structure FInv (W : ℕ) (c₀ c : Config) : Prop where
  hw : WordsBounded W c
  hin : ∀ q, FFix q → c.nreg q = c₀.nreg q
  hA : c₀.nreg ALLOC ≤ c.nreg ALLOC
  hm : MemEqBelow (c₀.nreg ALLOC) c.nmem c₀.nmem

/-- **A run step of the search.** -/
abbrev FRS (B : Finset ℕ) (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  RunSpec (FInv W c₀) (RF B (c₀.nreg ALLOC)) P W s c K Q

variable {B : Finset ℕ} {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem FRS.mono {s : Stmt} {K K' : ℕ} {Q Q' : Config → Prop} (h : FRS B P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : FRS B P W c₀ s c K' Q' :=
  RunSpec.mono h hK hQ

theorem FRS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : FRS B P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, FInv W c₀ c₁ → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ → Q₁ c₁ →
      FRS B P W c₀ t c₁ K₂ Q₂) : FRS B P W c₀ (.seq s t) c (K₁ + K₂) Q₂ :=
  RunSpec.seq h₁ (fun d hi _ ha hq => h₂ d hi ha hq)

theorem FRS.ifT {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a < c.nreg b) (h : FRS B P W c₀ t c K Q) :
    FRS B P W c₀ (.ifLtN a b t e) c (K + 2) Q :=
  RunSpec.ifT ht h

theorem FRS.ifF {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : ¬ c.nreg a < c.nreg b) (h : FRS B P W c₀ e c K Q) :
    FRS B P W c₀ (.ifLtN a b t e) c (K + 2) Q :=
  RunSpec.ifF ht h

theorem FRS.skip {K : ℕ} {Q : Config → Prop} (hI : FInv W c₀ c) (hq : Q c) :
    FRS B P W c₀ .skip c K Q :=
  RunSpec.skip hI.hw hI hq

/-- A scratch register of the search: band `bRestore` from `81028` on, or a register of an
oracle band (the arguments of the cutter). -/
@[ram_layout] def FScr (r : ℕ) : Prop := (81028 ≤ r ∧ r < 90000) ∨ bandOf r ∈ oracleBands

/-- An output register of the search (the flag and the triple). -/
@[ram_layout] def FOut (r : ℕ) : Prop := 81007 ≤ r ∧ r < 81011

theorem FInv.regs (hB : dBands ⊆ B) {c' : Config} {k : ℕ} (hI : FInv W c₀ c)
    (hw : WordsBounded W c')
    (hr : ∀ r, ¬ FOut r → ¬ FScr r → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : FInv W c₀ c' ∧ RF B (c₀.nreg ALLOC) c c' k := by
  have keep : ∀ q, FFix q → c'.nreg q = c.nreg q := fun q hq => hr q
    (by reg_omega)
    (by unfold FScr; unfold FFix at hq; rintro (h | h)
        · omega
        · exact band8_not_oracle (by omega) (by omega) h)
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by reg_omega)
    (by unfold FScr ALLOC; reg_omega)
  refine ⟨⟨hw, fun q hq => (keep q hq).trans (hI.hin q hq), by rw [hA]; exact hI.hA,
    fun a ha => by rw [hm]; exact hI.hm a ha⟩,
    (rf_of_regs' (fun r hr' => hr r ?_ ?_) hrr hm hrm ho).mono hB le_rfl⟩
  · unfold FOut; intro h
    exact hr' (by ram_rw [band8]; decide)
  · unfold FScr; rintro (h | h)
    · exact hr' (by ram_rw [band8]; decide)
    · exact hr' (Finset.mem_union_right _ h)

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem FRS.while {a b : ℕ} {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, FInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      FRS B P W c₀ body c Kb (fun c' => I c' ∧ μ c' < μ c))
    (hI : FInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + (Kb + 2) * μ c ≤ W) :
    FRS B P W c₀ (.whileLtN a b body) c ((Kb + 2) * μ c + 2)
      (fun c' => I c' ∧ ¬ c'.nreg a < c'.nreg b) :=
  RunSpec.whileN I μ Kb (fun _ h => h.hw) hpos hbody hI hc hroom

/-- **A call of a statement with a `Meets` contract** whose postcondition keeps the inputs and
the constants of the search. -/
theorem FRS.call {s : Stmt} {B' : Finset ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop} {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ B) (hI : FInv W c₀ c) (hpre : Pre P W c)
    (hroom : c.nreg ALLOC + cost P c ≤ W)
    (hprot : ∀ c', Post P c c' → ∀ q, FFix q → c'.nreg q = c.nreg q) :
    FRS B P W c₀ s c (cost P c) (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem) := by
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ := hs P W c hI.hw hpre hroom
  have hp := hprot c' hpost
  exact ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => (hp q hq).trans (hI.hin q hq),
    le_trans hI.hA hfr.2.2.2.2.2.1,
    fun a ha => (hfr.2.2.1 a (lt_of_lt_of_le ha hI.hA)).trans (hI.hm a ha)⟩,
    (RF.of_frame hfr hI.hA).mono hB le_rfl, hpost, hfr.2.2.2.2.2.1, hfr.2.2.1⟩

/-! ## Straight-line blocks -/

abbrev okB := okRegB (fun r => FScr r ∨ FOut r)

/-- **A straight-line block** of register instructions. -/
theorem FRS.block (hB : dBands ⊆ B) (l : List Instr) {c : Config} (hI : FInv W c₀ c)
    (hok : okB W c.nmem l c.nreg) : FRS B P W c₀ (Stmt.block l) c l.length
      (fun c' => c' = { c with nreg := regB c.nmem l c.nreg }) := by
  have e := Exec.regBlock (P := P) hI.hw hok
  obtain ⟨hI', hf⟩ := hI.regs hB e.wb_right (fun _ ho hs => hok.keeps (not_or.mpr ⟨hs, ho⟩))
    rfl rfl rfl rfl
  exact ⟨_, _, e, le_rfl, hI', hf, rfl⟩

/-- **A primitive call** (a step framed by the bands of the primitives). -/
theorem FRS.prim (hB : dBands ⊆ B) {s : Stmt} {c' : Config} {k k' K : ℕ} {Q : Config → Prop}
    (hI : FInv W c₀ c) (hex : Exec P W s c c' k) (hf₀ : Frame SweepPrim.primBands c c' k')
    (hkk : k' ≤ k)
    (hk : k ≤ K) (hq : Q c') : FRS B P W c₀ s c K Q := by
  have hf : Frame SweepPrim.primBands c c' k := ⟨hf₀.1, hf₀.2.1, hf₀.2.2.1, hf₀.2.2.2.1,
    hf₀.2.2.2.2.1,
    hf₀.2.2.2.2.2.1, by have := hf₀.2.2.2.2.2.2; omega⟩
  have h8 := fun q h1 h2 =>
    hf.1 q (by
      rw [band8 h1 h2]
      simp [SweepPrim.primBands, bRestore, bSign, bLocate]) (by unfold ALLOC; omega)
  refine ⟨c', k, hex, hk, ⟨hex.wb_right, fun q hq => ?_, hI.hA.trans hf.2.2.2.2.2.1,
    fun a ha => (hf.2.2.1 a (by have := hI.hA; omega)).trans (hI.hm a ha)⟩,
    (RF.of_frame hf hI.hA).mono (primBands_sub.trans hB) le_rfl, hq⟩
  frame_finish [FFix, h8]

end

end Restore

end Chazelle.Core
