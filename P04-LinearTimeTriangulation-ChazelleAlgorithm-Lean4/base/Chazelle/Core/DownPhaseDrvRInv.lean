module

public import Chazelle.Core.DownPhaseNFSorted
public import Chazelle.Core.SpecPhases
public import Chazelle.Cost.DownPhase

/-!
# Down-phase driver (RAM side), D1 part 1: the level invariant and the component contracts

Design: `docs/design-downphase-driver.md` §§2–4, 7 (step 2: "D1 with the level body as an
abstract `Meets` hypothesis").

The down phase is `transition ; λ := p ; while 16 ≤ λ ∧ n₀ ≤ n : (level(λ) ; λ := ⌈λ/5⌉ + 11) ;
base ; coreReg 3 := handle` (`DownPhaseDrvRMain`).  This file fixes

* the registers of the driver state (band `bDownDrv = 21`, `rd c bDownDrv i`):
  `0` the level `λ`, `1` the interior model descriptor, `2` the chord list `L`, `3` its length
  `K`, `4` the event list `E`, `5` the handle of the normal form `buildNF I Q L E`, `6` the
  output handle of the base case; `7 … 14` are the driver's scratch registers;
* **`EnvD X P W c`**: the environment every component may assume and must not destroy (a good
  input, the word bounds `n + 3 ≤ W` and `hostWords n ≤ W`, the setup record at `coreReg 0` and
  the up-phase data `X` at `coreReg 1`, robust below the allocator, with capacity `≥ n - 1`);
* **`InvAt cnt P c λ`**: the level invariant `Inv(λ)` of the design (§2): the interior model
  descriptor, the chord list `L`, the `codeLe`-sorted event list `E` and the normal form
  `N = buildNF I Q L E` robust below the allocator, and
  (I1) `I.DegLe S 4`, (I2) `I.Semigranular S (2^(⌈βλ⌉+12))`,
  (I3) `K · 2^⌈βλ⌉ ≤ cnt λ · (2^p + 2^⌈βλ⌉)` (i.e. `K ≤ cnt λ (2^p / 2^⌈βλ⌉ + 1)`), where
  `S = N.F I Q`, `I = interiorModel Q`, `Q = Qof P`, `p = topGrade n`;
* the three component contracts **`TransSpec`**, **`LevelSpec`**, **`BaseSpec`**: the transition
  establishes `Inv(p)`, one level turns `Inv(λ)` into `Inv(⌈βλ⌉ + 11)` in
  `κ (K + 1) (lemma41Nat (⌈βλ⌉ + 11) + 1)` steps, and the base case turns `Inv(λ)` with
  `λ < 16` or `n < n₀` into the post of `DownPhaseSpec` (handle in register `6`).

The count bound `cnt : ℕ → ℕ` is a parameter (D10 decides it; it must be bounded,
`∀ λ, cnt λ ≤ C`, for the cost).  The threshold `n₀` is a parameter of the level and base
contracts (below it the driver goes straight to the base case).

Transport lemmas: `EnvD.frame` (any frame not writing the core band), `InvAt.transport`
(registers `1 … 5` kept, memory kept below the allocator, allocator not lowered).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt
open BuildNF (codeLe)
open SortL (seg)

@[expose] public section

/-! ## Levels and bands -/

/-- **The next level**: `μ(λ) = ⌈βλ⌉ + 11` (the recursion index of `Cost.DownRecurrence`). -/
noncomputable def nextLvl (lam : ℕ) : ℕ := Cost.ceilBeta lam + 11

/-- The next level is smaller from `16` on. -/
theorem nextLvl_lt {lam : ℕ} (h : 16 ≤ lam) : nextLvl lam < lam :=
  Cost.ceilBeta_add_eleven_lt h

/-- **The bands the components of the down phase may write**: every phase band except the core
band (so the handles of `coreReg 0 … 2` survive every component). -/
def drvBands : Finset ℕ := phaseBands.erase bCore

theorem bCore_notin_drvBands : bCore ∉ drvBands := by
  unfold drvBands; simp

theorem bDownDrv_mem_drvBands : bDownDrv ∈ drvBands := by
  unfold drvBands phaseBands bDownDrv bCore; decide

theorem drvBands_subset : drvBands ⊆ phaseBands := Finset.erase_subset _ _

/-! ## The environment -/

/-- **The environment of the down-phase components**: a good input, the word bounds, the setup
record at `coreReg 0` and the up-phase data `X` at `coreReg 1` (robust below the allocator),
whose oracles serve arcs of up to `n - 1` edges. -/
def EnvD (X : MemCtx) (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ P.n + 3 ≤ W ∧ hostWords P.n ≤ W ∧
    Robust (c.nreg ALLOC) c.nmem (fun m => SetupAt m (c.nreg (coreReg 0)) P.n (c.nreg ALLOC)) ∧
    X.holds P c.nmem (c.nreg (coreReg 1)) (c.nreg ALLOC) ∧
    P.n - 1 ≤ X.cap P c.nmem (c.nreg (coreReg 1))

theorem coreReg_band (i : ℕ) (hi : i < 10000) : bandOf (coreReg i) = bCore := by
  unfold coreReg; exact bandOf_bandReg _ _ hi

theorem coreReg_ne_alloc (i : ℕ) (hi : i < 10000) : coreReg i ≠ ALLOC := by
  unfold coreReg bandReg bCore ALLOC; omega

/-- The setup record survives a change of memory at or above its bound and a larger bound. -/
theorem setup_transport {A A' : ℕ} {m m' : ℕ → ℕ} {S n : ℕ}
    (h : Robust A m (fun m => SetupAt m S n A)) (hm : ∀ a, a < A → m' a = m a) (hA : A ≤ A') :
    Robust A' m' (fun m => SetupAt m S n A') := by
  intro m'' h''
  have := h m'' (fun a ha => (h'' a (lt_of_lt_of_le ha hA)).trans (hm a ha))
  exact ⟨this.1, this.2.1, this.2.2.1, le_trans this.2.2.2 hA⟩

/-- **The environment survives every frame that does not write the core band.** -/
theorem EnvD.transport {X : MemCtx} (hX : X.CapLocal) {P : Polygon} {W : ℕ} {c c' : Config}
    (h : EnvD X P W c) (h0 : c'.nreg (coreReg 0) = c.nreg (coreReg 0))
    (h1 : c'.nreg (coreReg 1) = c.nreg (coreReg 1)) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) : EnvD X P W c' := by
  obtain ⟨hG, hW3, hWh, hS, hXh, hcap⟩ := h
  refine ⟨hG, hW3, hWh, ?_, ?_, ?_⟩
  · rw [h0]; exact setup_transport hS hm hA
  · rw [h1]
    exact X.mono P _ _ _ _ hA (X.local_ P c.nmem c'.nmem _ _ (fun a ha => (hm a ha).symm) hXh)
  · rw [h1, hX P c.nmem c'.nmem _ _ hm hXh]; exact hcap

/-- **The environment survives every frame that does not write the core band.** -/
theorem EnvD.frame {X : MemCtx} (hX : X.CapLocal) {P : Polygon} {W : ℕ} {B : Finset ℕ}
    {c c' : Config} {k : ℕ} (h : EnvD X P W c) (hf : Frame B c c' k) (hB : bCore ∉ B) :
    EnvD X P W c' := by
  have hr : ∀ i, i < 10000 → c'.nreg (coreReg i) = c.nreg (coreReg i) := fun i hi =>
    hf.1 _ (by rw [coreReg_band i hi]; exact hB) (coreReg_ne_alloc i hi)
  exact h.transport hX (hr 0 (by norm_num)) (hr 1 (by norm_num)) hf.2.2.2.2.2.1 hf.2.2.1

/-! ## The level invariant -/

/-- **The level invariant `Inv(λ)`** (design §2), with count bound `cnt`.  Registers of band
`bDownDrv`: `1` the interior model descriptor, `2` the chord list `L`, `3` its length `K`, `4`
the event list `E`, `5` the normal form `N = buildNF I Q L E`; everything robust below the
allocator.  `E` is a `codeLe`-sorted permutation of the `2K` event codes; the triples are
admissible, distinct and attached (`ChordTriplesOK`).  With `S = N.F I Q`:
(I1) `I.DegLe S 4`; (I2) `I.Semigranular S (2^(⌈βλ⌉+12))`;
(I3) `K 2^⌈βλ⌉ ≤ cnt λ (2^p + 2^⌈βλ⌉)` with `p = topGrade n`. -/
def InvAt (cnt : ℕ → ℕ) (P : Polygon) (c : Config) (lam : ℕ) : Prop :=
  rd c bDownDrv 1 + 6 ≤ c.nreg ALLOC ∧
    Robust (c.nreg ALLOC) c.nmem
      (fun m => ModelDescAt m (rd c bDownDrv 1) (Qof P) (interiorModel (Qof P))) ∧
    ∃ (L : List (ℕ × ℕ × ℕ)) (E : List ℕ),
      rd c bDownDrv 3 = L.length ∧
      rd c bDownDrv 2 + 3 * L.length ≤ c.nreg ALLOC ∧
      Robust (c.nreg ALLOC) c.nmem (fun m => ChordListAt m (rd c bDownDrv 2) L) ∧
      rd c bDownDrv 4 + 2 * L.length ≤ c.nreg ALLOC ∧
      Robust (c.nreg ALLOC) c.nmem (fun m => seg m (rd c bDownDrv 4) (2 * L.length) = E) ∧
      ChordTriplesOK (interiorModel (Qof P)) (Qof P) L ∧
      E.Perm (List.range (2 * L.length)) ∧
      E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L) ∧
      NFWithin c.nmem (rd c bDownDrv 5) (c.nreg ALLOC)
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) ∧
      (interiorModel (Qof P)).DegLe
        ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4 ∧
      (interiorModel (Qof P)).Semigranular
        ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P))
        (2 ^ (Cost.ceilBeta lam + 12)) ∧
      L.length * 2 ^ Cost.ceilBeta lam ≤
        cnt lam * (2 ^ topGrade P.n + 2 ^ Cost.ceilBeta lam)

/-- **The invariant survives** when the registers `1 … 5` of `bDownDrv` are kept, the memory
below the allocator is kept, and the allocator is not lowered. -/
theorem InvAt.transport {cnt : ℕ → ℕ} {P : Polygon} {c c' : Config} {lam : ℕ}
    (h : InvAt cnt P c lam) (hr : ∀ i, 1 ≤ i → i ≤ 5 → rd c' bDownDrv i = rd c bDownDrv i)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    InvAt cnt P c' lam := by
  obtain ⟨hD, hDa, L, E, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hN, hdeg, hwt, hcnt⟩ := h
  have h1 := hr 1 le_rfl (by norm_num)
  refine ⟨by rw [h1]; omega, by rw [h1]; exact (hDa.transport hm).mono hA, L, E, ?_, ?_, ?_, ?_, ?_, hok, hperm, hsort, ?_,
    hdeg, hwt, hcnt⟩
  · rw [hr 3 (by norm_num) (by norm_num)]; exact hK
  · rw [hr 2 (by norm_num) (by norm_num)]; omega
  · rw [hr 2 (by norm_num) (by norm_num)]; exact (hLa.transport hm).mono hA
  · rw [hr 4 (by norm_num) (by norm_num)]; omega
  · rw [hr 4 (by norm_num) (by norm_num)]; exact (hEa.transport hm).mono hA
  · rw [hr 5 (by norm_num) (by norm_num)]; exact (hN.transport hm).mono hA

/-- (I3) as a bound on `K`: `K ≤ cnt λ (2^p + 2^⌈βλ⌉) / 2^⌈βλ⌉`. -/
theorem InvAt.len_le {cnt : ℕ → ℕ} {P : Polygon} {c : Config} {lam : ℕ}
    (h : InvAt cnt P c lam) :
    rd c bDownDrv 3 ≤
      cnt lam * (2 ^ topGrade P.n + 2 ^ Cost.ceilBeta lam) / 2 ^ Cost.ceilBeta lam := by
  obtain ⟨-, -, L, E, hK, -, -, -, -, -, -, -, -, -, -, hcnt⟩ := h
  rw [hK, Nat.le_div_iff_mul_le (by positivity)]
  exact hcnt

/-! ## The component contracts -/

/-- **D2, the transition** (design §4.1; math `Trans.transition`): from the input of
`DownPhaseSpec` (with the environment), establish `Inv(p)`, `p = topGrade n`, in `κ (n + 1)`
steps, writing only `drvBands`. -/
def TransSpec (X : MemCtx) (cnt : ℕ → ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧
      ∃ C N, TopChain P C ∧ Robust (c.nreg ALLOC) c.nmem (fun m => NFAt m (c.nreg (coreReg 2)) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (topGran P.n) 4)
    (fun P _ c' => InvAt cnt P c' (topGrade P.n))
    (fun P _ => κ * (P.n + 1))

/-- **One level of the down phase** (design §4.2–4.3: regions, leaves, merges, extraction,
splice, rebuild, restoration rounds): from `Inv(λ)` with `16 ≤ λ ≤ p` and `n₀ ≤ n` (λ in
register `0` of `bDownDrv`), establish `Inv(⌈βλ⌉ + 11)`, keeping register `0`, in
`κ (K + 1) (lemma41Nat (⌈βλ⌉ + 11) + 1)` steps (`K` the chord count, register `3`): a constant
number of Lemma 4.1 / merge budgets per region, and `K + 1` regions. -/
def LevelSpec (X : MemCtx) (cnt : ℕ → ℕ) (n₀ : ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧ n₀ ≤ P.n ∧ 16 ≤ rd c bDownDrv 0 ∧
      rd c bDownDrv 0 ≤ topGrade P.n ∧ InvAt cnt P c (rd c bDownDrv 0))
    (fun P c c' => rd c' bDownDrv 0 = rd c bDownDrv 0 ∧
      InvAt cnt P c' (nextLvl (rd c bDownDrv 0)))
    (fun _ c => κ * ((rd c bDownDrv 3 + 1) * (lemma41Nat (nextLvl (rd c bDownDrv 0)) + 1)))

/-- **D9, the base case** (design §4.4: region brute force, splice, `dropAug`,
`buildNFSorted`): from `Inv(λ)` with `λ < 16` or `n < n₀`, write in register `6` of `bDownDrv`
the handle of a normal form of the full interior visibility map of `Q`, robust below the
allocator, in `κ (n + 1)` steps. -/
def BaseSpec (X : MemCtx) (cnt : ℕ → ℕ) (n₀ : ℕ) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => EnvD X P W c ∧
      ∃ lam, lam ≤ topGrade P.n ∧ (lam < 16 ∨ P.n < n₀) ∧ InvAt cnt P c lam)
    (fun P _ c' => ∃ N, Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bDownDrv 6) N) ∧
      IsNF (interiorModel (Qof P)) (Qof P) N ∧
      N.F (interiorModel (Qof P)) (Qof P) = (interiorModel (Qof P)).Full)
    (fun P _ => κ * (P.n + 1))

end

end DrvR

end Chazelle.Core
