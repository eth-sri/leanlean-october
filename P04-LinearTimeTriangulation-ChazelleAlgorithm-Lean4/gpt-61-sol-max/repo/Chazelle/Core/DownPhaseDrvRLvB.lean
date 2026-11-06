module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRLvA
public import Chazelle.Core.DownPhaseDrvRMgC
public import Chazelle.Core.GradeCtx

/-!
# Down-phase driver (RAM side): one level, the region loop (definitions)

For every region `r = 0 … K` of the current normal form `N` (register `211010` the region,
`211011 = K + 1`):

* `lvRegA`, host RAM `sH` (`HostRamSpec`): the host `regHost li n N r` at `r215010`;
* `lvRegB`, region procedure `sR` (`RegionSpec`): model descriptor `r219210`, normal form
  `r219211`, granularity `r219212`;
* `lvRegC`, extraction `sX` (`ExtractRamSpec`): kept triples `r217010` (length `r217011`),
  buckets `r217012`;
* `lvRegE`, `lvRegD`: the largest length (`211013`), the table entry `T + 3 r` (triples, length,
  buckets), the total length (`211012`), `r := r + 1`.

The facts of a finished region: `RegOK` (the hypothesis of `LevelMathSpec` for region `r`) and
`RegMem` (its table entry and its lists in memory).  The loop invariant `LvInv`; the context
`LvCtx` (the configuration after `lvPar`).  `forLoopA`: `forLoop` with the allocator bounded by
the steps.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SignK
open BuildNF (codeLe)
open SortL (seg)

@[expose] public section

/-! ## The program -/

/-- The arguments of the host RAM. -/
def lvRegA : Stmt := block [.copyN 215000 210005, .copyN 215001 211010, .copyN 215002 211008]

/-- The arguments of the region procedure. -/
def lvRegB : Stmt :=
  block [.copyN 219200 215010, .copyN 219201 215012, .copyN 219202 211002, .copyN 219203 211004,
    .copyN 219204 211006, .copyN 219205 230001]

/-- The arguments of the extraction. -/
def lvRegC : Stmt :=
  block [.copyN 217000 210005, .copyN 217001 211010, .copyN 217002 211008,
    .copyN 217003 215010, .copyN 217004 215012, .copyN 217005 219210, .copyN 217006 219211]

/-- The table entry, the total, the next region. -/
def lvRegD : Stmt :=
  block [.addN 211020 211010 211010, .addN 211020 211020 211010, .addN 211020 211020 211009,
    .storeN 211020 217010, .addN 211020 211020 211014, .storeN 211020 217011,
    .addN 211020 211020 211014, .storeN 211020 217012,
    .addN 211012 211012 217011, .addN 211010 211010 211014]

/-- The largest length. -/
def lvRegE : Stmt := .ifLtN 211013 217011 (.instr (.copyN 211013 217011)) .skip

/-- **The body of the region loop.** -/
def lvBody (sH sR sX : Stmt) : Stmt :=
  .seq lvRegA (.seq sH (.seq lvRegB (.seq sR (.seq lvRegC (.seq sX (.seq lvRegE lvRegD))))))

/-- **The region loop.** -/
def lvLoop (sH sR sX : Stmt) : Stmt := .whileLtN 211010 211011 (lvBody sH sR sX)

/-! ## The facts of a region -/

/-- The registers the region loop keeps. -/
def LvFixed (q : ℕ) : Prop :=
  (210000 ≤ q ∧ q ≤ 210005) ∨ (211000 ≤ q ∧ q ≤ 211009) ∨ (211014 ≤ q ∧ q ≤ 211017) ∨
    q = 230000 ∨ q = 230001

/-- **The math facts of a finished region** (the hypothesis of `LevelMathSpec`). -/
noncomputable def RegOK (P : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (reg : ℕ → Set Point)
    (γ₀ r : ℕ) (C : Chain) (NR : NF) (γR : ℕ) (Lx : List (ℕ × ℕ × ℕ)) : Prop :=
  open Classical in
  C.P = (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r).poly (Qof P) ∧
    C.s = 0 ∧ C.m + 1 = C.P.n ∧
    IsCanonicalNF (chainModel C) (Qof P) NR γR regCap ∧ γ₀ ≤ γR ∧ γR ≤ γ₀ + 128 ∧
    {x | ∃ y ∈ Lx, x = (recOf y).toSet (interiorModel (Qof P)) (Qof P)} =
      Extract.kept (reg r) (NR.F (chainModel C) (Qof P)) ∧
    (Lx.map fun y => (recOf y).toSet (interiorModel (Qof P)) (Qof P)).Nodup ∧
    (∀ y ∈ Lx, (recOf y).Attached (interiorModel (Qof P)) (Qof P) ∧ y.1 < (Qof P).n) ∧
    ∀ q, q < 2 * Lx.length →
      ∃ j ∈ ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
        OnArcKey (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j (endPos Lx q)

/-- **The memory facts of a finished region**: its table entry at `T + 3 r` (triples, length,
buckets), the triples and the buckets at or above `B`, below `A`. -/
def RegMem (m : ℕ → ℕ) (A T B : ℕ) (Q : Polygon) (N : NF) (r : ℕ) (Lx : List (ℕ × ℕ × ℕ)) :
    Prop :=
  m (T + 3 * r + 1) = Lx.length ∧ B ≤ m (T + 3 * r) ∧ m (T + 3 * r) + 3 * Lx.length ≤ A ∧
    ChordListAt m (m (T + 3 * r)) Lx ∧ B ≤ m (T + 3 * r + 2) ∧
    m (T + 3 * r + 2) + 2 * Lx.length ≤ A ∧
    ∀ q, q < 2 * Lx.length → m (m (T + 3 * r + 2) + q) = keyBkt Q N (endPos Lx q)

/-- The memory facts of a region survive a change of the memory at or above `A` outside the
table, and a larger bound. -/
theorem RegMem.transport {m m' : ℕ → ℕ} {A A' T B : ℕ} {Q : Polygon} {N : NF} {r : ℕ}
    {Lx : List (ℕ × ℕ × ℕ)} (h : RegMem m A T B Q N r Lx) (hTB : T + 3 * r + 3 ≤ B)
    (hm : ∀ a, (a < A ∧ (a < B → T + 3 * r ≤ a ∧ a < T + 3 * r + 3)) → m' a = m a)
    (hA : A ≤ A') : RegMem m' A' T B Q N r Lx := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e0 : m' (T + 3 * r) = m (T + 3 * r) := hm _ ⟨by omega, fun _ => ⟨le_rfl, by omega⟩⟩
  have e1 : m' (T + 3 * r + 1) = m (T + 3 * r + 1) := hm _ ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩
  have e2 : m' (T + 3 * r + 2) = m (T + 3 * r + 2) := hm _ ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩
  refine ⟨by rw [e1, h1], by omega, by omega, ?_, by omega,
    by omega, fun q hq => ?_⟩
  · rw [e0]
    exact clAt_congr h4 fun x hx1 hx2 => hm x ⟨by omega, fun hx => by omega⟩
  ram_grind

/-- A host description below `A` is robust. -/
theorem hostAt_robust {m : ℕ → ℕ} {B A : ℕ} {H : Host} (h : HostAt m B H)
    (hA : B + 3 * H.length + 1 ≤ A) : Robust A m (fun m => HostAt m B H) := by
  intro m' hm'
  obtain ⟨h0, hi⟩ := h
  refine ⟨by ram_grind, fun i hi' => ?_⟩
  have := hi i hi'
  revert this
  rcases H.getD i (.run 0 0) with ⟨a, ℓ⟩ | ⟨⟨j⟩ | ⟨e, hh⟩⟩ <;> simp only <;> intro hh' <;>
    ram_grind

/-! ## Counted loops with the allocator -/

section loops

variable {P : Polygon} {W : ℕ}

/-- **A counted loop whose iterations allocate at most their steps.** -/
theorem forLoopA {ir nr : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (Kb N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c → ∃ c' k, Exec P W body c c' k ∧ Inv (j + 1) c' ∧ k ≤ Kb ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W (.whileLtN ir nr body) c c' k ∧ Inv N c' ∧ k ≤ (Kb + 2) * (N - j) + 2 ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  induction hn : N - j generalizing j c with
  | zero =>
    have hjN : j = N := by omega
    subst hjN
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    exact ⟨c, 2, .whileLtN_false (by omega) hw, hc, by omega, by omega⟩
  | succ t ih =>
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    have hlt : j < N := by omega
    obtain ⟨c₁, k₁, e₁, hI₁, hk₁, hA₁⟩ := hbody j c hlt hc
    obtain ⟨c', k₂, e₂, hI', hk₂, hA₂⟩ := ih hI₁ (by omega) (by omega)
    refine ⟨c', k₁ + 2 + k₂, .whileLtN_true (by omega) e₁ e₂, hI', ?_, by omega⟩
    ram_grind

end loops

/-! ## The context and the invariant -/

/-- **The context of the region loop**: the configuration `c₁` after `lvPar`, the state
`(L, E)` of `Inv(λ)` and the region correspondence `reg` of `N = buildNF I Q L E`. -/
structure LvCtx (O : OracleIface) (P : Polygon) (W : ℕ) (c₁ : Config) (L : List (ℕ × ℕ × ℕ))
    (E : List ℕ) (reg : ℕ → Set Point) (lam : ℕ) : Prop where
  good : GoodEnv P
  w3 : P.n + 3 ≤ W
  wh : hostWords P.n ≤ W
  setup : Robust (c₁.nreg 211009) c₁.nmem
    (fun m => SetupAt m (c₁.nreg (coreReg 0)) P.n (c₁.nreg 211009))
  holds : (gradeCtx O).holds P c₁.nmem (c₁.nreg (coreReg 1)) (c₁.nreg 211009)
  cap : P.n - 1 ≤ (gradeCtx O).cap P c₁.nmem (c₁.nreg (coreReg 1))
  h16 : 16 ≤ lam
  hlp : lam ≤ topGrade P.n
  hL : L ≠ []
  ok : ChordTriplesOK (interiorModel (Qof P)) (Qof P) L
  perm : E.Perm (List.range (2 * L.length))
  sort : E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L)
  deg : (interiorModel (Qof P)).DegLe
    ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4
  wt : (interiorModel (Qof P)).Semigranular
    ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P))
    (2 ^ (Cost.ceilBeta lam + 12))
  regs : Restore.NFRegs (interiorModel (Qof P)) (Qof P)
    (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) reg
  nf : NFWithin c₁.nmem (c₁.nreg 210005) (c₁.nreg 211009)
    (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
  r00 : c₁.nreg 210000 = lam
  r02 : c₁.nreg 211002 = nextLvl lam
  r04 : c₁.nreg 211004 = 2 ^ nextLvl lam
  r06 : c₁.nreg 211006 = 3 * 2 ^ (Cost.ceilBeta (nextLvl lam) + 10)
  r07 : c₁.nreg 211007 = 2 ^ (Cost.ceilBeta (nextLvl lam) + 12)
  r08 : c₁.nreg 211008 ≤ 1
  r08' : c₁.nreg 211008 = 1 ↔ Mountain.LeftInside (Qof P)
  r09 : c₁.nreg 211009 + 3 * (L.length + 1) = c₁.nreg ALLOC
  r14 : c₁.nreg 211014 = 1
  big : 3 * 2 ^ (Cost.ceilBeta (nextLvl lam) + 10) + 129 ≤ P.n - 1
  big2 : 2 ^ (Cost.ceilBeta (nextLvl lam) + 12) ≤ P.n - 1
  md : Robust (c₁.nreg 211009) c₁.nmem
    (fun m => ModelDescAt m (c₁.nreg 210001) (Qof P) (interiorModel (Qof P)))
  mdA : c₁.nreg 210001 + 6 ≤ c₁.nreg 211009
  r03 : c₁.nreg 210003 = L.length
  lA : c₁.nreg 210002 + 3 * L.length ≤ c₁.nreg 211009
  lmem : Robust (c₁.nreg 211009) c₁.nmem (fun m => ChordListAt m (c₁.nreg 210002) L)
  eA : c₁.nreg 210004 + 2 * L.length ≤ c₁.nreg 211009
  emem : Robust (c₁.nreg 211009) c₁.nmem (fun m => seg m (c₁.nreg 210004) (2 * L.length) = E)

/-- **The environment** at every configuration that keeps the core registers and the memory
below the table, with the allocator at or above the table. -/
theorem LvCtx.envD {O : OracleIface} {P : Polygon} {W : ℕ} {c₁ : Config} {L : List (ℕ × ℕ × ℕ)}
    {E : List ℕ} {reg : ℕ → Set Point} {lam : ℕ} (h : LvCtx O P W c₁ L E reg lam) {c : Config}
    (h0 : c.nreg (coreReg 0) = c₁.nreg (coreReg 0)) (h1 : c.nreg (coreReg 1) = c₁.nreg (coreReg 1))
    (hm : ∀ a, a < c₁.nreg 211009 → c.nmem a = c₁.nmem a) (hA : c₁.nreg 211009 ≤ c.nreg ALLOC) :
    EnvD (gradeCtx O) P W c := by
  refine ⟨h.good, h.w3, h.wh, ?_, ?_, ?_⟩
  · rw [h0]; exact setup_transport h.setup hm hA
  · rw [h1]
    exact (gradeCtx O).mono P _ _ _ _ hA
      ((gradeCtx O).local_ P c₁.nmem c.nmem _ _ (fun a ha => (hm a ha).symm) h.holds)
  · rw [h1, gradeCtx_capLocal O P c₁.nmem c.nmem _ _ hm h.holds]; exact h.cap

/-- **The invariant of the region loop** after `j` regions (`Kb` bounds the steps of one
iteration). -/
def LvInv (_O : OracleIface) (P : Polygon) (W : ℕ) (c₁ : Config) (L : List (ℕ × ℕ × ℕ))
    (E : List ℕ) (reg : ℕ → Set Point) (Kb j : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 211010 = j ∧ c.nreg 211011 = L.length + 1 ∧
    (∀ q, LvFixed q → c.nreg q = c₁.nreg q) ∧
    (∀ a, a < c₁.nreg 211009 → c.nmem a = c₁.nmem a) ∧
    (∀ a, a < c₁.nreg 211009 → c.rmem a = c₁.rmem a) ∧
    (∀ q, bandOf q ∉ drvBands → q ≠ ALLOC → c.nreg q = c₁.nreg q) ∧
    (∀ q, bandOf q ∉ drvBands → c.rreg q = c₁.rreg q) ∧ c.output = c₁.output ∧
    c₁.nreg ALLOC ≤ c.nreg ALLOC ∧ c.nreg ALLOC ≤ c₁.nreg ALLOC + j * Kb ∧
    ∃ (C : ℕ → Chain) (NR : ℕ → NF) (γR : ℕ → ℕ) (Lx : ℕ → List (ℕ × ℕ × ℕ)),
      c.nreg 211012 = ((List.range j).flatMap Lx).length ∧
      (∀ r, r < j → (Lx r).length ≤ c.nreg 211013) ∧
      (c.nreg 211013 = 0 ∨ ∃ r, r < j ∧ c.nreg 211013 = (Lx r).length) ∧
      ∀ r, r < j → RegOK P L E reg (c₁.nreg 211006) r (C r) (NR r) (γR r) (Lx r) ∧
        RegMem c.nmem (c.nreg ALLOC) (c₁.nreg 211009) (c₁.nreg ALLOC) (Qof P)
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r (Lx r)

end

end DrvR

end Chazelle.Core
