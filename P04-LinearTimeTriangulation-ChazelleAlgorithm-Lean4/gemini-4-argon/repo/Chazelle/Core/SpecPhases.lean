module

public import Chazelle.Core.SpecAssembly
public import Chazelle.Core.SpecMerge

/-!
# Core specification, part 6: the phases (WP-G, H, J, K, L, M, N) and their composition

The package specifications that were missing from parts 1–5 (specification review, design doc §8
item 5), and the **proved** composition `core_of_phases` of the phase-level specifications into
`CoreStageSpec`, in the style of `linear_of_core`.

## Phase-level specifications (composed here)

The core driver is `setup ; up ; down ; out` (no glue code).  Handles are passed in the registers
of the core band `bCore` (`coreReg i`):

| phase | package | reads | writes | post |
|---|---|---|---|---|
| `SetupSpec` | WP-L | — | `coreReg 0` | `SetupAt`: `n`, `p = ⌈log₂ (n-1)⌉`, tables of `2^i` and `⌈i/5⌉` |
| `UpPhaseSpec X` | WP-J | `0` | `1`, `2` | the up-phase data `X` at `coreReg 1`; a `γ'_p`-canonical normal form (`topGran`) of the top chain at `coreReg 2` |
| `DownPhaseSpec X` | WP-M | `0 … 2` | `3` | a normal form of the full interior visibility map of `Q = Qof P` at `coreReg 3` |
| `OutputSpec` | WP-N | `3` | band `0` | `TablesReady (Qof P)` |

Every phase has cost `κ (n + 1)` and writes only the bands `phaseBands` (`1 … 24`; the output
phase also band `0`, which holds the hand-off registers), and every phase keeps the core registers
it reads (`KeepsCore`).  Data left in memory is stated **robustly** (`Robust A m Φ`: `Φ` holds for
every memory agreeing with `m` below `A`), so it survives every later frame without locality
lemmas.  (This sidesteps a gap of `NFWithin`, which does not bound the per-region list offsets:
review finding R3 in the design doc.)

`X : MemCtx` is the up-phase data (canonical submaps and ray-shooting structures of all grade
chains).  The up and down phases must agree on it; the composition only needs *some* `X`
(`CorePhasesSpec`).  The intended instance is `gradeCtx O` for an oracle implementation `O`
(WP-H).

## Package-level specifications (proved by the packages, not composed here)

* `gradeStart`, `gradeLen`, `gradeCount`, `GradeRaw`, `gradeCtx O`: the grade table (paper
  p. 516) as a memory context;
* WP-G `ShootCutSpec O`: ray-shooter and arc-cutter (p. 501) built on `gradeCtx O`, with the
  paper's `f(γ)`, `g(γ) = O(λ)` and `h(γ) = γ'_{⌈log₂ γ⌉}` (p. 517);
* WP-H `OracleSpec`: an implementation of Lemma 3.6 (`OracleIface.Valid`);
* WP-J `Lemma41Spec O`: Lemma 4.1, a canonical submap of any portion `v_a … v_b` with
  `2^(λ-1) < b - a ≤ 2^λ`, `λ ≥ 7`, once grades `< λ` are processed, in
  `κ λ² (⌈log₂ λ⌉ + 1) 2^(74λ/75)` steps;
* the **granularity schedule** `gradeGran λ = 2^⌈βλ⌉ + λ (⌈log₂ λ⌉ + 2)` (consolidated revision,
  design doc §10) and its arithmetic (`gradeGran_step`, `gradeGran_mono`, `gradeGran_cap`,
  `gradeGran_le_real`, `clog_gradeGran_le`);
* WP-K `BruteSpec`: canonical submaps of chains by brute force in `κ (m + 1)³` steps (used for
  the grades below a constant).

The obligations of the phase packages are then (design doc §6):
* WP-J: `OracleSpec`, `ShootCutSpec`, `Lemma41Spec`, `BruteSpec`, … `→ ∃ O, UpPhaseSpec (gradeCtx O)`;
* WP-M: the same plus `MergeSpec`, `RestoreSpec` `→ DownPhaseSpec (gradeCtx O)` (Lemma 4.2 and
  the transition to the interior model).

The input is not padded to `2^p + 1` vertices: the last chain of each grade is short
(`gradeLen`).
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Machine (Stmt Exec)

/-! ## Conventions -/

/-- Register `i` of the core band (the driver's registers, used to pass handles between phases). -/
def coreReg (i : ℕ) : ℕ := bandReg bCore i

/-- The bands a phase may write: every procedure band (`1 … 24`, including the sweep band
`bSweep = 24` of the consolidated revision) and the core band, not the final stage's band `0`. -/
def phaseBands : Finset ℕ := Finset.Icc 1 24

/-- The bands the output phase may write (it also sets the hand-off registers of band `0`). -/
def outBands : Finset ℕ := Finset.range 25

/-- The core registers listed in `S` are unchanged. -/
def KeepsCore (S : Finset ℕ) (c c' : Config) : Prop :=
  ∀ i ∈ S, c'.nreg (coreReg i) = c.nreg (coreReg i)

/-! ## WP-L: setup -/

/-- The top grade: the least `p` with `n - 1 ≤ 2^p`. -/
def topGrade (n : ℕ) : ℕ := Nat.clog 2 (n - 1)

/-- **The canonical granularity of grade `g`** (consolidated revision, design doc §10;
formerly `gradeGranV2`): `γ'_g = 2^⌈βg⌉ + fuseLoss · g (⌈log₂ g⌉ + 2)`.  The paper's `2^⌈βg⌉`
plus a lower-order term absorbing the additive loss `fuseLoss` of the at most `1 + ⌈log₂ g⌉`
merge levels of Lemma 4.1 (`gradeGran_step`); within a factor `1201` of the paper's
(`gradeGran_le_real`). -/
noncomputable def gradeGran (g : ℕ) : ℕ :=
  2 ^ Cost.ceilBeta g + fuseLoss * (g * (Nat.clog 2 g + 2))

/-- The granularity of the canonical submap of the top chain, `γ'_p` (`gradeGran`). -/
noncomputable def topGran (n : ℕ) : ℕ := gradeGran (topGrade n)

/-- **The setup record** at `S`: `n`, the top grade `p`, the table of `2^i` (`i ≤ p + 1`) at
`S + 2`, the table of `⌈i/5⌉` (`i ≤ p + 1`) at `S + p + 4`; all of it below `E`. -/
def SetupAt (m : ℕ → ℕ) (S n E : ℕ) : Prop :=
  m S = n ∧ m (S + 1) = topGrade n ∧
    (∀ i, i ≤ topGrade n + 1 → m (S + 2 + i) = 2 ^ i ∧
      m (S + topGrade n + 4 + i) = Cost.ceilBeta i) ∧
    S + 2 * topGrade n + 6 ≤ E

/-- **WP-L: setup.**  From the initial state (with a good environment), writes a fresh setup
record and puts its handle in `coreReg 0`, in `κ (n + 1)` steps. -/
def SetupSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s phaseBands
    (fun P W _ => GoodEnv P ∧ P.n + 3 ≤ W)
    (fun P _ c' => Robust (c'.nreg ALLOC) c'.nmem
      fun m => SetupAt m (c'.nreg (coreReg 0)) P.n (c'.nreg ALLOC))
    (fun P _ => κ * (P.n + 1))

/-! ## The phases -/

/-- The top chain of the geometry polygon: all edges but the last (`v₀ … v_{n-1}`). -/
def TopChain (P : Polygon) (C : Chain) : Prop := C.P = Qof P ∧ C.s = 0 ∧ C.m + 1 = P.n

/-- **WP-J: the up phase** (§4.1) with up-phase data `X`.  Reads the setup handle in
`coreReg 0` (kept); writes the handle of `X` in `coreReg 1` (holding below the allocator, with
all grades processed: its oracles serve arcs of up to `n - 1` edges, review finding F4) and the
handle of a `γ'_p`-canonical normal form (`topGran`, degree cap `4`) of the
top chain in `coreReg 2`, in `κ (n + 1)` steps. -/
def UpPhaseSpec (X : MemCtx) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s phaseBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧ Robust (c.nreg ALLOC) c.nmem
      fun m => SetupAt m (c.nreg (coreReg 0)) P.n (c.nreg ALLOC))
    (fun P c c' => KeepsCore {0} c c' ∧
      X.holds P c'.nmem (c'.nreg (coreReg 1)) (c'.nreg ALLOC) ∧
      P.n - 1 ≤ X.cap P c'.nmem (c'.nreg (coreReg 1)) ∧
      ∃ C N, TopChain P C ∧ Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (c'.nreg (coreReg 2)) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (topGran P.n) 4)
    (fun P _ => κ * (P.n + 1))

/-! ## The composition (proved) -/

/-! ## Package-level specifications -/

/-! ### The grade table (paper p. 516) -/

/-- The first edge of chain `i` of grade `g`. -/
def gradeStart (g i : ℕ) : ℕ := i * 2 ^ g

/-- The number of edges of chain `i` of grade `g` of the curve `v₀ … v_{n-1}` (`n - 1` edges):
`2^g`, except for a short last chain (the input is not padded). -/
def gradeLen (n g i : ℕ) : ℕ := min (2 ^ g) (n - 1 - i * 2 ^ g)

/-- The number of chains of grade `g`: `⌈(n - 1) / 2^g⌉`. -/
def gradeCount (n g : ℕ) : ℕ := (n - 2) / 2 ^ g + 1

/-- **The raw grade table** at handle `h`: `m h = Λ`, the number of processed grades
(`Λ ≤ p + 1`); `m (h + 1)` the setup handle; `m (h + 2)` the base `T` of the row table; for every
grade `g < Λ` and chain `i < gradeCount n g`, the entry at `m (T + g) + 3 i` holds a chain
descriptor of chain `i` of grade `g` of `Q = Qof P`, the handle of a `γ'_g`-canonical normal
form (`gradeGran`) (degree cap `4`) of it, and the handle of an oracle structure (`O.At`) for them;
the hosts are well formed (consolidated revision, finding C8; the descriptors lie below the bound
of the context because the context is robust).  The descriptors are well formed and the normal
forms robust below the bound `A` of the context (review finding G4: a robust existential does not
give the single robust normal form a cutter piece needs). -/
def GradeRaw (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (h A : ℕ) : Prop :=
  m h ≤ topGrade P.n + 1 ∧ SetupAt m (m (h + 1)) P.n (m (h + 1) + 2 * topGrade P.n + 6) ∧
    (∀ x, x ≤ P.n → m (m (h + 3) + x) = x / 2) ∧
    ∀ g i, g < m h → i < gradeCount P.n g →
      ∃ (H : Host) (C : Chain) (N : NF),
        ChainDescAt m (m (m (m (h + 2) + g) + 3 * i)) (Qof P) H C ∧
        ChainWF P A m (m (m (m (h + 2) + g) + 3 * i)) ∧ C.P = Qof P ∧
        H.length ≤ 64 ∧ HostWF P.n H ∧
        C.s = gradeStart g i ∧ C.m = gradeLen P.n g i ∧
        NFWithin m (m (m (m (h + 2) + g) + 3 * i + 1)) A N ∧
        IsCanonicalNF (chainModel C) (Qof P) N (gradeGran g) 4 ∧
        O.At P m (m (m (m (h + 2) + g) + 3 * i + 2)) ∧
        m (m (m (m (h + 2) + g) + 3 * i + 2)) = m (m (m (h + 2) + g) + 3 * i) ∧
        m (m (m (m (h + 2) + g) + 3 * i + 2) + 1) = m (m (m (h + 2) + g) + 3 * i + 1) ∧
        m (m (m (m (h + 2) + g) + 3 * i + 2) + 2) = gradeGran g

/-- The grade table is monotone in its bound. -/
theorem GradeRaw.mono {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {h A A' : ℕ}
    (hr : GradeRaw O P m h A) (hA : A ≤ A') : GradeRaw O P m h A' := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  refine ⟨h1, h2, h3, fun g i hg hi => ?_⟩
  obtain ⟨H, C, N, hd, hwf, hP, hl, hH, hs, hm, hN, rest⟩ := h4 g i hg hi
  exact ⟨H, C, N, hd, hwf.mono hA, hP, hl, hH, hs, hm, hN.mono hA, rest⟩

/-- **The up-phase data** as a memory context.  Once grades `< Λ` are processed, arcs of weight
at most `2^(Λ-1)` can be shot at and cut (a subarc of `w` edges splits into `O(log w)` grade
chains of grade `≤ ⌈log₂ w⌉`, `Cost.dyadic_cover`). -/
noncomputable def gradeCtx (O : OracleIface) : MemCtx where
  holds P m h A := Robust A m fun m' => GradeRaw O P m' h A
  cap _ m h := 2 ^ (m h - 1)
  local_ _P _m _m' _g _A hmm' h := h.transport fun a ha => (hmm' a ha).symm
  mono _P _m _g _A _A' hA h := fun m' hm' =>
    (h m' fun a ha => hm' a (lt_of_lt_of_le ha hA)).mono hA

/-! ### WP-H: Lemma 3.6 -/

/-- **WP-H.**  An implementation of the ray-shooting structure of Lemma 3.6. -/
def OracleSpec : Prop := ∃ O : OracleIface, O.Valid

/-! ### WP-G: the oracles of the merges -/

/-- `⌈x^a⌉` for a natural `x` and a real exponent. -/
noncomputable def rpowCeil (x : ℕ) (a : ℝ) : ℕ := ⌈(x : ℝ) ^ a⌉₊

/-- The granularity of the pieces produced by the arc-cutter for arcs of weight `≤ γ`:
`h(γ) = γ'_{⌈log₂ γ⌉} ≤ 1201 · 2^⌈β⌈log₂ γ⌉⌉` (p. 517, with the revised schedule). -/
noncomputable def cutGran (γ : ℕ) : ℕ := gradeGran (Nat.clog 2 γ)

/-- **WP-G: the ray-shooter and the arc-cutter** (p. 501, built as on p. 517): for the up-phase
data `gradeCtx O`, a shooter with `F(γ) = κ (⌈log₂ γ⌉ + 1) ⌈h(γ)^{1/3} (γ + 1)^{2/3}⌉ + κ`
(`O(λ)` subarcs, each a Lemma 3.6 query) and a cutter with `G(γ) = κ (⌈log₂ γ⌉ + 1)` pieces of
granularity `h(γ)`. -/
def ShootCutSpec (O : OracleIface) : Prop :=
  ∃ (sh cu : Stmt) (κ : ℕ),
    ShooterOK sh oracleBands
      (fun γ => κ * (Nat.clog 2 γ + 1) * rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) + κ)
      (gradeCtx O) OkModel ∧
    CutterOK cu oracleBands (fun γ => κ * (Nat.clog 2 γ + 1)) cutGran (gradeCtx O) OkModel

/-! ### WP-J: Lemma 4.1 -/

/-- The bands of Lemma 4.1 (merges with their oracles and sweeps, and its own band). -/
def l41Bands : Finset ℕ := mergeBands ∪ oracleBands ∪ {bL41}

/-- Lemma 4.1's bound `λ² (⌈log₂ λ⌉ + 1) 2^(74λ/75)` (with the `+1` of the logarithm kept). -/
noncomputable def lemma41Nat (g : ℕ) : ℕ :=
  ⌈(g : ℝ) ^ 2 * ((Nat.clog 2 g : ℝ) + 1) * (2 : ℝ) ^ ((74 : ℝ) / 75 * g)⌉₊

/-- The first grade at which Lemma 4.1 is used (`gradeGran_cap`: from grade `7` on, the oracles
of the grades `< λ` serve every weight a merge of Lemma 4.1 needs; below it, `BruteSpec`). -/
def lemma41Start : ℕ := 7

/-- **WP-J: Lemma 4.1** (p. 517).  Band `bL41`: `0` the handle of the up-phase data (with at
least `λ` grades processed), `1` the start `a`, `2` the length `b - a`, `3` the grade
`λ ≥ lemma41Start = 7` (`2^(λ-1) < b - a ≤ 2^λ`); output `4`: a `γ'_λ`-canonical normal form
(`gradeGran`, degree cap `4`) of the chain `v_a … v_b` of `Q`, robust below the new allocator.
Cost `κ (lemma41Nat λ + 1)`.  (Consolidated revision: the revised schedule, `λ ≥ 7` so that the
merge targets `γ₀ + 1 ≤ γ'_λ < 2^(λ-1)` are served by the oracles (`gradeGran_cap`), and the
word bound `hostWords`.) -/
def Lemma41Spec (O : OracleIface) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s l41Bands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem (rd c bL41 0) (c.nreg ALLOC) ∧
      rd c bL41 3 ≤ c.nmem (rd c bL41 0) ∧ lemma41Start ≤ rd c bL41 3 ∧
      rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
      2 ^ (rd c bL41 3 - 1) < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
      Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bL41 4) N) ∧
      IsCanonicalNF (chainModel C) (Qof P) N (gradeGran (rd c bL41 3)) 4)
    (fun _ c => κ * (lemma41Nat (rd c bL41 3) + 1))

/-! ### WP-K: brute force -/

/-- The bands of the brute-force procedure (granularity enforcement and its own band). -/
def bruteBands : Finset ℕ := granBands ∪ {bBrute}

/-- **WP-K: brute-force canonical submaps** (the early grades, p. 516: "this work can be done
naively").  Band `bBrute`: `0` start `a`, `1` number of edges `m ≥ 1` (`a + m + 1 ≤ n`), `2` a
granularity `γ ≥ 1` with `m = 1` or `γ ≥ 2` (review finding K1: an interior top vertex of a chain of `≥ 2` edges always leaves an arc of weight `≥ 2`, so `γ = 1` is impossible there); output `3`: a `γ`-canonical normal form (degree cap `4`) of the chain
`v_a … v_{a+m}` of `Q`.  Cost `κ (m + 1)³`. -/
def BruteSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s bruteBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
      rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
      (rd c bBrute 1 = 1 ∨ 2 ≤ rd c bBrute 2))
    (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
      Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bBrute 3) N) ∧
      IsCanonicalNF (chainModel C) (Qof P) N (rd c bBrute 2) 4)
    (fun _ c => κ * (rd c bBrute 1 + 1) ^ 3)

/-! ### Arithmetic of the schedule (formerly `SpecMergeV2`) -/

theorem ceilBeta_mono {g g' : ℕ} (h : g ≤ g') : Cost.ceilBeta g ≤ Cost.ceilBeta g' := by
  unfold Cost.ceilBeta
  apply Nat.ceil_mono
  have hb : (0 : ℝ) ≤ Cost.beta := by rw [Cost.beta_eq]; norm_num
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) hb

theorem ceilBeta_succ_le (g : ℕ) : Cost.ceilBeta (g + 1) ≤ Cost.ceilBeta g + 1 := by
  unfold Cost.ceilBeta
  rw [Nat.ceil_le]
  have h1 := Nat.le_ceil (Cost.beta * (g : ℝ))
  rw [Cost.beta_eq] at h1 ⊢
  push_cast
  linarith

theorem clog_succ_le {g : ℕ} (hg : 1 ≤ g) : Nat.clog 2 (g + 1) ≤ Nat.clog 2 g + 1 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.le_pow_clog (b := 2) (by norm_num) g
  rw [pow_succ]
  omega

/-- **The recurrence of the revised schedule**:
`γ'_g + fuseLoss (⌈log₂ (g + 1)⌉ + 1) ≤ γ'_{g+1}`. -/
theorem gradeGran_step (g : ℕ) :
    gradeGran g + fuseLoss * (Nat.clog 2 (g + 1) + 1) ≤ gradeGran (g + 1) := by
  unfold gradeGran fuseLoss
  have h1 : 2 ^ Cost.ceilBeta g ≤ 2 ^ Cost.ceilBeta (g + 1) :=
    Nat.pow_le_pow_right (by norm_num) (ceilBeta_mono (Nat.le_succ g))
  have h2 : Nat.clog 2 g ≤ Nat.clog 2 (g + 1) := Nat.clog_mono_right 2 (Nat.le_succ g)
  have h3 : g * (Nat.clog 2 g + 2) + (Nat.clog 2 (g + 1) + 1) ≤
      (g + 1) * (Nat.clog 2 (g + 1) + 2) := by
    have := Nat.mul_le_mul_left g h2
    nlinarith
  omega

/-- The revised schedule is monotone. -/
theorem gradeGran_mono {g g' : ℕ} (h : g ≤ g') : gradeGran g ≤ gradeGran g' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_trans (Nat.le_add_right _ _) (gradeGran_step _))

/-- The revised schedule dominates the paper's: `2^⌈βg⌉ ≤ γ'_g` (fewer chords). -/
theorem two_pow_ceilBeta_le_gradeGran (g : ℕ) : 2 ^ Cost.ceilBeta g ≤ gradeGran g :=
  Nat.le_add_right _ _

/-- `γ'_{g+1} ≤ 2 γ'_g` for `g ≥ 2`. -/
theorem gradeGran_succ_le_two_mul {g : ℕ} (hg : 2 ≤ g) :
    gradeGran (g + 1) ≤ 2 * gradeGran g := by
  unfold gradeGran fuseLoss
  have h1 : 2 ^ Cost.ceilBeta (g + 1) ≤ 2 * 2 ^ Cost.ceilBeta g := by
    calc 2 ^ Cost.ceilBeta (g + 1) ≤ 2 ^ (Cost.ceilBeta g + 1) :=
          Nat.pow_le_pow_right (by norm_num) (ceilBeta_succ_le g)
      _ = 2 * 2 ^ Cost.ceilBeta g := by rw [pow_succ]; ring
  have h2 := clog_succ_le (g := g) (by omega)
  have hc : 1 ≤ Nat.clog 2 g := Nat.clog_pos (by norm_num) (by omega)
  have h3 : (g + 1) * (Nat.clog 2 (g + 1) + 2) ≤ 2 * (g * (Nat.clog 2 g + 2)) := by
    have := Nat.mul_le_mul_left (g + 1) (Nat.add_le_add_right h2 2)
    nlinarith
  omega

/-- **The cap condition**: from grade `7` on, `γ'_λ + 1 ≤ 2^(λ-1)`, so the oracles of the grades
`< λ` (which serve arcs of weight up to `2^(λ-1)`) serve every merge of Lemma 4.1 at grade `λ`
(inputs `≤ γ'_λ - 1`, fused weights `≤ γ'_λ`). -/
theorem gradeGran_cap {g : ℕ} (hg : lemma41Start ≤ g) : gradeGran g + 1 ≤ 2 ^ (g - 1) := by
  unfold lemma41Start at hg
  induction g, hg using Nat.le_induction with
  | base =>
    have hb : Cost.ceilBeta 7 ≤ 2 := by
      unfold Cost.ceilBeta
      rw [Nat.ceil_le, Cost.beta_eq]
      norm_num
    have hc : Nat.clog 2 7 ≤ 3 := Nat.clog_le_of_le_pow (by norm_num)
    have hp : 2 ^ Cost.ceilBeta 7 ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hb
    unfold gradeGran fuseLoss
    have : 7 * (Nat.clog 2 7 + 2) ≤ 7 * (3 + 2) := Nat.mul_le_mul_left 7 (by omega)
    norm_num at hp this ⊢
    omega
  | succ g hg ih =>
    have h2 := gradeGran_succ_le_two_mul (g := g) (by omega)
    have e : g + 1 - 1 = (g - 1) + 1 := by omega
    rw [e, pow_succ]
    omega

/-- **The revised schedule is within a constant factor of the paper's**:
`γ'_g ≤ 1201 · 2^⌈βg⌉`.  All oracle costs `f`, `g`, `h` of the paper are nondecreasing and at
most polynomial in `γ`, so they change by constant factors only. -/
theorem gradeGran_le_real (g : ℕ) :
    (gradeGran g : ℝ) ≤ 1201 * (2 : ℝ) ^ Cost.ceilBeta g := by
  unfold gradeGran fuseLoss
  have hc : Nat.clog 2 g ≤ g := Cost.clog_two_le_self g
  have hpoly : g * (Nat.clog 2 g + 2) ≤ 3 * g ^ 2 := by
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · subst h0; simp
    · have := Nat.mul_le_mul_left g (Nat.add_le_add_right hc 2)
      nlinarith
  have hsq := Cost.natPow_le_two_rpow 2 5 (by norm_num) g
  have hexp : (2 : ℝ) ^ ((g : ℝ) / (5 : ℕ)) ≤ (2 : ℝ) ^ Cost.ceilBeta g := by
    rw [← Real.rpow_natCast (2 : ℝ) (Cost.ceilBeta g)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := Cost.beta_mul_le_ceilBeta g
    rw [Cost.beta_eq] at this
    push_cast
    linarith
  have hpolyR : ((g * (Nat.clog 2 g + 2) : ℕ) : ℝ) ≤ 3 * (g : ℝ) ^ 2 := by exact_mod_cast hpoly
  push_cast at hsq hpolyR ⊢
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ Cost.ceilBeta g := by positivity
  nlinarith

/-- The oracle grade of a merge at grade `λ`: `⌈log₂ (γ'_λ + 1)⌉ ≤ ⌈βλ⌉ + 11`. -/
theorem clog_gradeGran_le (g : ℕ) :
    Nat.clog 2 (gradeGran g + 1) ≤ Cost.ceilBeta g + 11 := by
  apply Nat.clog_le_of_le_pow
  have h := gradeGran_le_real g
  have hN : gradeGran g ≤ 1201 * 2 ^ Cost.ceilBeta g := by exact_mod_cast h
  have h1 : 1 ≤ 2 ^ Cost.ceilBeta g := Nat.one_le_two_pow
  rw [pow_add]
  omega

end

end Chazelle.Core
