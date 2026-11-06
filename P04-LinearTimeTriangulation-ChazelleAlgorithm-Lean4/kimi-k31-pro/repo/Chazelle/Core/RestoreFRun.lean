module

public import Chazelle.Core.RestoreDescGeo
public import Chazelle.Core.RestoreTestSpec
public import Chazelle.Core.RestoreTEnv
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

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
def FFix (q : ℕ) : Prop := (80000 ≤ q ∧ q < 81007) ∨ (81011 ≤ q ∧ q < 81028)

/-- **The search invariant**, relative to the configuration `c₀` reached after the
initialisation. -/
structure FInv (W : ℕ) (c₀ c : Config) : Prop where
  hw : WordsBounded W c
  hin : ∀ q, FFix q → c.nreg q = c₀.nreg q
  hA : c₀.nreg ALLOC ≤ c.nreg ALLOC
  hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a

/-- **A run step of the search.** -/
def FRS (B : Finset ℕ) (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ FInv W c₀ c' ∧ RF B (c₀.nreg ALLOC) c c' k ∧ Q c'

variable {B : Finset ℕ} {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem FRS.mono {s : Stmt} {K K' : ℕ} {Q Q' : Config → Prop} (h : FRS B P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : FRS B P W c₀ s c K' Q' := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k, ex, by omega, hI, hrf, hQ c' hq⟩

theorem FRS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : FRS B P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, FInv W c₀ c₁ → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ → Q₁ c₁ →
      FRS B P W c₀ t c₁ K₂ Q₂) : FRS B P W c₀ (.seq s t) c (K₁ + K₂) Q₂ := by
  obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hrf₁, hq₁⟩ := h₁
  obtain ⟨c', k₂, e₂, hk₂, hI', hrf₂, hq⟩ := h₂ c₁ hI₁ (by have := hrf₁.2.2.2.2.2.2; omega) hq₁
  exact ⟨c', k₁ + k₂, .seq e₁ e₂, by omega, hI', hrf₁.trans hrf₂, hq⟩

theorem FRS.ifT {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a < c.nreg b) (h : FRS B P W c₀ t c K Q) :
    FRS B P W c₀ (.ifLtN a b t e) c (K + 2) Q := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k + 1, .ifLtN_true ht ex, by omega, hI, hrf.mono subset_rfl (by omega), hq⟩

theorem FRS.ifF {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : ¬ c.nreg a < c.nreg b) (h : FRS B P W c₀ e c K Q) :
    FRS B P W c₀ (.ifLtN a b t e) c (K + 2) Q := by
  obtain ⟨c', k, ex, hk, hI, hrf, hq⟩ := h
  exact ⟨c', k + 2, .ifLtN_false ht ex, by omega, hI, hrf.mono subset_rfl (by omega), hq⟩

theorem FRS.skip {K : ℕ} {Q : Config → Prop} (hI : FInv W c₀ c) (hq : Q c) :
    FRS B P W c₀ .skip c K Q :=
  ⟨c, 0, .skip hI.hw, by omega, hI, RF.refl c 0, hq⟩

/-- A scratch register of the search: band `bRestore` from `81028` on, or a register of an
oracle band (the arguments of the cutter). -/
def FScr (r : ℕ) : Prop := (81028 ≤ r ∧ r < 90000) ∨ bandOf r ∈ oracleBands

/-- An output register of the search (the flag and the triple). -/
def FOut (r : ℕ) : Prop := 81007 ≤ r ∧ r < 81011

theorem FInv.regs (hB : dBands ⊆ B) {c' : Config} {k : ℕ} (hI : FInv W c₀ c)
    (hw : WordsBounded W c')
    (hr : ∀ r, ¬ FOut r → ¬ FScr r → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : FInv W c₀ c' ∧ RF B (c₀.nreg ALLOC) c c' k := by
  have keep : ∀ q, FFix q → c'.nreg q = c.nreg q := fun q hq => hr q
    (by unfold FOut; ufo FFix at hq)
    (by unfold FScr; unfold FFix at hq; rintro (h | h)
        · omega
        · exact band8_not_oracle (by omega) (by omega) h)
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by ufo FOut ALLOC)
    (by unfold FScr ALLOC; rintro (h | h)
        · omega
        · exact absurd h (by decide))
  refine ⟨⟨hw, fun q hq => (keep q hq).trans (hI.hin q hq), by rw [hA]; exact hI.hA,
    fun a ha => by rw [hm]; exact hI.hm a ha⟩,
    (rf_of_regs' (fun r hr' => hr r ?_ ?_) hrr hm hrm ho).mono hB le_rfl⟩
  · unfold FOut; intro h
    exact hr' (by rwd [band8 (by omega) (by omega)])
  · unfold FScr; rintro (h | h)
    · exact hr' (by rwd [band8 (by omega) (by omega)])
    · exact hr' (Finset.mem_union_right _ h)

/-- **One register instruction** on a scratch or output register. -/
theorem FRS.reg (hB : dBands ⊆ B) {i : Instr} {r v : ℕ} (hI : FInv W c₀ c)
    (hr : FScr r ∨ FOut r)
    (hex : Exec P W (.instr i) c { c with nreg := upd c.nreg r v } 1) :
    FRS B P W c₀ (.instr i) c 1 (fun c' => c' = { c with nreg := upd c.nreg r v }) := by
  obtain ⟨hI', hrf⟩ := hI.regs hB (c' := { c with nreg := upd c.nreg r v }) (k := 1) hex.wb_right
    (fun q h1 h2 => by
      simp only [upd]
      split_ifs with h
      · subst h; rcases hr with hr | hr
        · exact absurd hr h2
        · exact absurd hr h1
      · rfl) rfl rfl rfl rfl
  exact ⟨_, 1, hex, le_rfl, hI', hrf, rfl⟩

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem FRS.while {a b : ℕ} {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, FInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      FRS B P W c₀ body c Kb (fun c' => I c' ∧ μ c' < μ c))
    (hI : FInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + (Kb + 2) * μ c ≤ W) :
    FRS B P W c₀ (.whileLtN a b body) c ((Kb + 2) * μ c + 2)
      (fun c' => I c' ∧ ¬ c'.nreg a < c'.nreg b) := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · have hμ : 0 < μ c := hpos c hc ht
      obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hrf₁, hc₁, hμ₁⟩ := hbody c hI hc ht (by
        have : Kb ≤ (Kb + 2) * μ c := by nlinarith
        omega)
      have hA₁ := hrf₁.2.2.2.2.2.2
      have hroom₁ : c₁.nreg ALLOC + (Kb + 2) * μ c₁ ≤ W := by
        have : (Kb + 2) * (μ c₁ + 1) ≤ (Kb + 2) * μ c := Nat.mul_le_mul_left _ hμ₁
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      obtain ⟨c', k₂, e₂, hk₂, hI', hrf₂, hq⟩ := ih (μ c₁) (by omega) hI₁ hc₁ hroom₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, ?_, hI',
        (hrf₁.trans hrf₂).mono subset_rfl (by omega), hq⟩
      have : (Kb + 2) * (μ c₁ + 1) ≤ (Kb + 2) * n := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · exact ⟨c, 2, .whileLtN_false ht hI.hw, by omega, hI, RF.refl c 2, hc, ht⟩

/-- **A call of a statement with a `Meets` contract** whose postcondition keeps the inputs and
the constants of the search. -/
theorem FRS.call {s : Stmt} {B' : Finset ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop} {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ B) (hI : FInv W c₀ c) (hpre : Pre P W c)
    (hroom : c.nreg ALLOC + cost P c ≤ W)
    (hprot : ∀ c', Post P c c' → ∀ q, FFix q → c'.nreg q = c.nreg q) :
    FRS B P W c₀ s c (cost P c) (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) := by
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ := hs P W c hI.hw hpre hroom
  have hp := hprot c' hpost
  exact ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => (hp q hq).trans (hI.hin q hq),
    le_trans hI.hA hfr.2.2.2.2.2.1,
    fun a ha => (hfr.2.2.1 a (lt_of_lt_of_le ha hI.hA)).trans (hI.hm a ha)⟩,
    (RF.of_frame hfr hI.hA).mono hB le_rfl, hpost, hfr.2.2.2.2.2.1, hfr.2.2.1⟩

/-! ## Straight-line blocks -/

/-- The register effect of a straight-line register instruction (memory `m`). -/
def regI (m : ℕ → ℕ) : Instr → (ℕ → ℕ) → (ℕ → ℕ)
  | .constN r k, f => upd f r k
  | .copyN r a, f => upd f r (f a)
  | .addN r a b, f => upd f r (f a + f b)
  | .subN r a b, f => upd f r (f a - f b)
  | .loadN r a, f => upd f r (m (f a))
  | _, f => f

/-- The register effect of a block. -/
def regB (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → (ℕ → ℕ)
  | [], f => f
  | i :: l, f => regB m l (regI m i f)

/-- An instruction the block lemma covers: a register instruction writing a scratch or output
register, with its value within the word bound. -/
def okI (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN r k => (FScr r ∨ FOut r) ∧ k ≤ W
  | .copyN r _ => FScr r ∨ FOut r
  | .addN r a b => (FScr r ∨ FOut r) ∧ f a + f b ≤ W
  | .subN r _ _ => FScr r ∨ FOut r
  | .loadN r _ => FScr r ∨ FOut r
  | _ => False

/-- The side conditions of a block, along its run. -/
def okB (W : ℕ) (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → Prop
  | [], _ => True
  | i :: l, f => okI W f i ∧ okB W m l (regI m i f)

/-- One covered instruction. -/
theorem FRS.instr1 (hB : dBands ⊆ B) {i : Instr} (hI : FInv W c₀ c) (hi : okI W c.nreg i) :
    FRS B P W c₀ (.instr i) c 1 (fun c' => c' = { c with nreg := regI c.nmem i c.nreg }) := by
  cases i with
  | constN r k => exact FRS.reg hB hI hi.1 (Exec.constN hI.hw r k hi.2)
  | copyN r a => exact FRS.reg hB hI hi (Exec.copyN hI.hw r a)
  | addN r a b => exact FRS.reg hB hI hi.1 (Exec.addN hI.hw r a b hi.2)
  | subN r a b => exact FRS.reg hB hI hi (Exec.subN hI.hw r a b)
  | loadN r a => exact FRS.reg hB hI hi (Exec.loadN hI.hw r a)
  | _ => exact absurd hi (by simp [okI])

/-- **A straight-line block** of register instructions. -/
theorem FRS.block (hB : dBands ⊆ B) : ∀ (l : List Instr) {c : Config}, FInv W c₀ c →
    okB W c.nmem l c.nreg →
    FRS B P W c₀ (Stmt.block l) c l.length
      (fun c' => c' = { c with nreg := regB c.nmem l c.nreg })
  | [], c, hI, _ => FRS.skip hI rfl
  | i :: l, c, hI, hok => by
    obtain ⟨hi, hl⟩ := hok
    have h := FRS.seq (FRS.instr1 (P := P) hB hI hi) (fun c₁ hI₁ _ h₁ => by
      subst h₁
      exact FRS.block hB l hI₁ hl)
    simp only [List.length_cons]
    rw [Nat.add_comm]
    exact h.mono le_rfl (fun c' h' => h')

/-- The destination register of a covered instruction. -/
def dstI : Instr → ℕ
  | .constN r _ => r
  | .copyN r _ => r
  | .addN r _ _ => r
  | .subN r _ _ => r
  | .loadN r _ => r
  | _ => 0

theorem regI_other (m f : ℕ → ℕ) (i : Instr) {q : ℕ} (hq : dstI i ≠ q) :
    regI m i f q = f q := by
  cases i <;> simp only [regI, dstI] at hq ⊢ <;> exact upd_ne (Ne.symm hq)

/-- **A block leaves the registers it does not write.** -/
theorem regB_other (m : ℕ → ℕ) : ∀ (l : List Instr) (f : ℕ → ℕ) {q : ℕ},
    (∀ i ∈ l, dstI i ≠ q) → regB m l f q = f q
  | [], _, _, _ => rfl
  | i :: l, f, q, h => by
    rw [regB, regB_other m l _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact regI_other m f i (h i List.mem_cons_self)

/-- **A primitive call** (a step framed by the bands of the primitives). -/
theorem FRS.prim (hB : dBands ⊆ B) {s : Stmt} {c' : Config} {k k' K : ℕ} {Q : Config → Prop}
    (hI : FInv W c₀ c) (hex : Exec P W s c c' k) (hf₀ : Frame SweepPrim.primBands c c' k')
    (hkk : k' ≤ k)
    (hk : k ≤ K) (hq : Q c') : FRS B P W c₀ s c K Q := by
  have hf : Frame SweepPrim.primBands c c' k := ⟨hf₀.1, hf₀.2.1, hf₀.2.2.1, hf₀.2.2.2.1,
    hf₀.2.2.2.2.1,
    hf₀.2.2.2.2.2.1, by have := hf₀.2.2.2.2.2.2; omega⟩
  have h8 : ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q := fun q h1 h2 =>
    hf.1 q (by
      rw [band8 h1 h2]
      simp [SweepPrim.primBands, bRestore, bSign, bLocate]) (by ufo ALLOC)
  refine ⟨c', k, hex, hk, ⟨hex.wb_right, fun q hq => ?_, hI.hA.trans hf.2.2.2.2.2.1,
    fun a ha => (hf.2.2.1 a (by have := hI.hA; omega)).trans (hI.hm a ha)⟩,
    (RF.of_frame hf hI.hA).mono (primBands_sub.trans hB) le_rfl, hq⟩
  unfold FFix at hq
  rw [h8 q (by omega) (by omega)]; exact hI.hin q (by ufo FFix)

end

end Restore

end Chazelle.Core
