module

public import Chazelle.Core.SweepEvTasks3
public import Chazelle.Core.GranSize
public import Chazelle.Core.RestoreTRead
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000

/-!
# The sweep (WP-D), stage 3: the origin enumeration (task E), part 1

The per-origin statement `od` is abstract (`OdOK`: it maps `Inv O` to
`Inv (insert (2 oK + oS) O)`, keeps the registers `LR` other than `oK`, `oS` and `ER`, and the
auxiliary array), and `Inv` is stable under changes of the registers `LR` (`InvStab`).

* `odPair od`: both ends `oS = 0, 1` of the chord `uK` (`odPair_irs`);
* `regDo od`: both ends of every chord of the region `uR` of `N₂` (`regDo_irs`).

All loop registers are in `sw 2460 … 2479` (`LR`): `uK … uT`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## Registers -/

/-- The chord, the region, an address, the stop index, the list length, the list offset, the
list area, the list index. -/
def uK : ℕ := sw 2460
def uR : ℕ := sw 2461
def uA : ℕ := sw 2462
def uI : ℕ := sw 2463
def uLen : ℕ := sw 2464
def uOff : ℕ := sw 2465
def uR7 : ℕ := sw 2466
def uT : ℕ := sw 2467
def uY : ℕ := sw 2468

/-! ## The abstract per-origin statement -/

/-- The contract of the per-origin statement (as in `OrgsTask`). -/
def OdOK (P : Polygon) (W : ℕ) (c₀ : Config) (N₂ : NF) (od : Stmt) (Kod : ℕ)
    (Inv : Set ℕ → Config → Prop) : Prop :=
  ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c → c.nreg oK < N₂.nChords →
    c.nreg oS ≤ 1 → c.nreg ALLOC + Kod ≤ W →
    IRS P W c₀ od c Kod (fun c' => Inv (insert (2 * c.nreg oK + c.nreg oS) O) c' ∧
      (∀ r, (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r → c'.nreg r = c.nreg r) ∧
      (∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → c'.nmem x = c.nmem x))

/-- The stability of the invariant under changes of the loop registers (as in `OrgsTask`). -/
def InvStab (Inv : Set ℕ → Config → Prop) : Prop :=
  ∀ (O : Set ℕ) (c c' : Config), Inv O c → (∀ r, ¬ LR r → c'.nreg r = c.nreg r) →
    c'.nmem = c.nmem → c'.rmem = c.rmem → c'.rreg = c.rreg → c'.output = c.output → Inv O c'

/-- The auxiliary array of `c` is unchanged in `c'`. -/
def AuxKeep (c c' : Config) : Prop :=
  ∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → c'.nmem x = c.nmem x

/-- The two endpoint queries of chord `k`. -/
def pairS (k : ℕ) : Set ℕ := {j | ∃ s, s ≤ 1 ∧ j = 2 * k + s}

theorem er_not_lr {r : ℕ} (h : ER r) : ¬ LR r := by
  unfold ER at h; unfold LR
  unfold kN kL gN gR sP sC aB oK oS sw at *
  omega

/-- A block writing only loop registers keeps the invariant. -/
theorem inv_blk {Inv : Set ℕ → Config → Prop} (hst : InvStab Inv) {l : List Instr}
    (hl : ∀ i ∈ l, LR (dstI i)) {O : Set ℕ} {c : Config} (h : Inv O c) :
    Inv O { c with nreg := regB c.nmem l c.nreg } :=
  hst O c _ h (fun _r hr => regB_other _ _ _ (fun i hi he => hr (he ▸ hl i hi))) rfl rfl rfl rfl

/-- A block writing only loop registers keeps the read registers. -/
theorem er_blk {l : List Instr} (hl : ∀ i ∈ l, LR (dstI i)) {m f : ℕ → ℕ} {r : ℕ} (hr : ER r) :
    regB m l f r = f r :=
  regB_other _ _ _ (fun i hi he => er_not_lr hr (he ▸ hl i hi))

theorem auxKeep_trans {c c₁ c₂ : Config} (h₁ : AuxKeep c c₁) (hr : ∀ r, ER r → c₁.nreg r = c.nreg r)
    (h₂ : AuxKeep c₁ c₂) : AuxKeep c c₂ := fun x hx1 hx2 => by
  have ea : c₁.nreg aB = c.nreg aB := hr _ (by ufs ER)
  have es : c₁.nreg sC = c.nreg sC := hr _ (by ufs ER)
  rw [h₂ x (by omega) (by omega), h₁ x hx1 hx2]

/-! ## Both ends of one chord -/

def uPre0 : List Instr := [.copyN oK uK, .copyN oS K0]
def uPre1 : List Instr := [.copyN oK uK, .copyN oS K1]

/-- **Both ends of the chord `uK`.** -/
def odPair (od : Stmt) : Stmt := .seq (block uPre0) (.seq od (.seq (block uPre1) od))

theorem uPre0_lr : ∀ i ∈ uPre0, LR (dstI i) := by
  simp [uPre0, dstI, LR]

theorem uPre1_lr : ∀ i ∈ uPre1, LR (dstI i) := by
  simp [uPre1, dstI, LR]

theorem pair_union (O : Set ℕ) (k : ℕ) :
    insert (2 * k + 1) (insert (2 * k + 0) O) = O ∪ pairS k := by
  ext j
  simp only [mem_insert_iff, mem_union, pairS, mem_ofPred_eq]
  constructor
  · rintro (h | h | h)
    · exact Or.inr ⟨1, le_rfl, h⟩
    · exact Or.inr ⟨0, by omega, h⟩
    · exact Or.inl h
  · rintro (h | ⟨s, hs, h⟩)
    · exact Or.inr (Or.inr h)
    · rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inl h

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **Both ends of one chord.** -/
theorem odPair_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    (hI : IInv W c₀ c) {O : Set ℕ} (hinv : Inv O c) {k : ℕ} (hk : c.nreg uK = k)
    (hkn : k < N₂.nChords) (hroom : c.nreg ALLOC + (2 * Kod + 4) ≤ W) :
    IRS P W c₀ (odPair od) c (2 * Kod + 4) (fun c' => Inv (O ∪ pairS k) c' ∧
      (∀ r, ER r ∨ (LR r ∧ r ≠ oK ∧ r ≠ oS) → c'.nreg r = c.nreg r) ∧ AuxKeep c c') := by
  have hK := E.hK.fix hI
  have k0  := hK.1
  have k1  := hK.2.1
  refine IRS.mono (K := 2 + (Kod + (2 + Kod))) (IRS.seq (IRS.block uPre0 hI ?_) ?_) (by omega)
    (fun _ => id)
  · simp [uPre0, okB, okI, IScr, oK, oS, sw]
  rintro c₁ hI₁ hA1 hA1' hc1
  have r1 : c₁.nreg = regB c.nmem uPre0 c.nreg := by rw [hc1]
  have m1 : c₁.nmem = c.nmem := by rw [hc1]
  have v1k : c₁.nreg oK = k := by
    rw [r1]; simp [uPre0, regB, regI, upd, oK, oS, uK, sw] at hk ⊢; exact hk
  have v1s : c₁.nreg oS = 0 := by
    rw [r1]; simp [uPre0, regB, regI, upd, oK, oS, K0, sw] at k0 ⊢; exact k0
  have o1 : ∀ r, r ≠ oK → r ≠ oS → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [r1]
    exact regB_other _ _ _ (fun i hi he => by
      simp only [uPre0, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact h1 he.symm
      · exact h2 he.symm)
  have inv1 : Inv O c₁ := by rw [hc1]; exact inv_blk hst uPre0_lr hinv
  have nAk : ALLOC ≠ oK := by ufo ALLOC oK sw
  have nAs : ALLOC ≠ oS := by ufo ALLOC oS sw
  have eA1 : c₁.nreg ALLOC = c.nreg ALLOC := o1 _ nAk nAs
  refine IRS.seq (hod O _ hI₁ inv1 (by rwx [v1k]) (by rwo [v1s])
    (by omega)) ?_
  rw [v1k, v1s]
  rintro c₂ hI₂ hA2 hA2' ⟨inv2, keep2, aux2⟩
  have hk2 : c₂.nreg uK = k := by
    rw [keep2 _ (Or.inl ⟨by unfold LR uK; simp [sw], by ufo uK oK sw,
      by ufo uK oS sw⟩)]
    rw [o1 _ (by ufo uK oK sw) (by ufo uK oS sw), hk]
  have hK2 := E.hK.fix hI₂
  refine IRS.seq (IRS.block uPre1 hI₂ ?_) ?_
  · simp [uPre1, okB, okI, IScr, oK, oS, sw]
  rintro c₃ hI₃ hA3 hA3' hc3
  have r3 : c₃.nreg = regB c₂.nmem uPre1 c₂.nreg := by rw [hc3]
  have m3 : c₃.nmem = c₂.nmem := by rw [hc3]
  have v3k : c₃.nreg oK = k := by
    rw [r3]; simp [uPre1, regB, regI, upd, oK, oS, uK, sw] at hk2 ⊢; exact hk2
  have v3s : c₃.nreg oS = 1 := by
    have := hK2.2.1
    rw [r3]; simp [uPre1, regB, regI, upd, oK, oS, K1, sw] at this ⊢; exact this
  have o3 : ∀ r, r ≠ oK → r ≠ oS → c₃.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [r3]
    exact regB_other _ _ _ (fun i hi he => by
      simp only [uPre1, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact h1 he.symm
      · exact h2 he.symm)
  have inv3 : Inv (insert (2 * k + 0) O) c₃ := by rw [hc3]; exact inv_blk hst uPre1_lr inv2
  have eA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := o3 _ nAk nAs
  refine (hod _ _ hI₃ inv3 (by rwx [v3k]) (by rw [v3s])
    (by omega)).mono le_rfl ?_
  rintro c' ⟨inv', keep', aux'⟩
  rw [v3k, v3s] at inv'
  have ER_ne : ∀ r, ER r → r ≠ oK ∧ r ≠ oS := fun r h =>
    ⟨fun e => er_not_lr h (e ▸ Or.inl rfl), fun e => er_not_lr h (e ▸ Or.inr (Or.inl rfl))⟩
  have keepAll : ∀ r, ER r ∨ (LR r ∧ r ≠ oK ∧ r ≠ oS) → c'.nreg r = c.nreg r := fun r hr => by
    have hr' : (LR r ∧ r ≠ oK ∧ r ≠ oS) ∨ ER r := by
      rcases hr with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hne : r ≠ oK ∧ r ≠ oS := by
      rcases hr with h | h
      · exact ER_ne r h
      · exact h.2
    rw [keep' r hr', o3 r hne.1 hne.2, keep2 r hr', o1 r hne.1 hne.2]
  refine ⟨by rw [← pair_union]; exact inv', keepAll, ?_⟩
  have e3 : ∀ r, ER r → c₃.nreg r = c.nreg r := fun r h => by
    rw [o3 r (ER_ne r h).1 (ER_ne r h).2, keep2 r (Or.inr h), o1 r (ER_ne r h).1 (ER_ne r h).2]
  have e1 : ∀ r, ER r → c₁.nreg r = c.nreg r := fun r h => o1 r (ER_ne r h).1 (ER_ne r h).2
  have hEa : ER aB := by ufs ER
  have hEs : ER sC := by ufs ER
  intro x hx1 hx2
  rw [aux' x (by rwx [e3 _ hEa]) (by rwx [e3 _ hEa, e3 _ hEs]), m3,
    aux2 x (by rwx [e1 _ hEa]) (by rwx [e1 _ hEa, e1 _ hEs]), m1]

/-! ## The chords of one region -/

/-- The head of a region: its chord count `uLen`, list offset `uOff`, list area `uR7`; `uT = 0`. -/
def regHead : List Instr :=
  [.addN uA (sw 4) K5, .loadN uA uA, .addN uA uA uR, .addN uA uA uR, .addN uA uA uR,
    .addN uA uA uR, .addN uA uA uR, .addN uY uA K2, .loadN uLen uY, .addN uY uA K3,
    .loadN uOff uY, .addN uY (sw 4) K6, .addN uY uY K1, .loadN uR7 uY, .constN uT 0]

/-- Read the chord at place `uT` of the list. -/
def regBody0 : List Instr := [.addN uA uR7 uOff, .addN uA uA uT, .loadN uK uA]

def uInc : List Instr := [.addN uT uT K1]

/-- One chord of the region. -/
def regBody (od : Stmt) : Stmt := .seq (block regBody0) (.seq (odPair od) (block uInc))

/-- **Both ends of every chord of the region `uR`** of `N₂`. -/
def regDo (od : Stmt) : Stmt := .seq (block regHead) (.whileLtN uT uLen (regBody od))

/-- The cost of a region. -/
def regK (Kod D : ℕ) : ℕ := (2 * Kod + 10) * D + 17

theorem regHead_lr : ∀ i ∈ regHead, LR (dstI i) := by
  simp [regHead, dstI, LR, uA, uY, uLen, uOff, uR7, uT, oK, oS, sw]

theorem regBody0_lr : ∀ i ∈ regBody0, LR (dstI i) := by
  simp [regBody0, dstI, LR, uA, uK, oK, oS, sw]

theorem uInc_lr : ∀ i ∈ uInc, LR (dstI i) := by
  simp [uInc, dstI, LR, uT, oK, oS, sw]

theorem regHead_val (m f : ℕ → ℕ) (k5 : f K5 = 5) (k2 : f K2 = 2) (k3 : f K3 = 3)
    (k6 : f K6 = 6) (k1 : f K1 = 1) :
    regB m regHead f uLen = m (m (f (sw 4) + 5) + 5 * f uR + 2) ∧
    regB m regHead f uOff = m (m (f (sw 4) + 5) + 5 * f uR + 3) ∧
    regB m regHead f uR7 = m (f (sw 4) + 7) ∧ regB m regHead f uT = 0 := by
  simp only [K5, K2, K3, K6, K1, sw] at k5 k2 k3 k6 k1
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [regHead, regB, regI, upd, uA, uY, uLen, uOff, uR7, uT, uR, K5, K2, K3, K6, K1, sw,
      k5, k2, k3, k6, k1] <;> ring_nf

theorem regHead_ok (m f : ℕ → ℕ) (k5 : f K5 = 5) (k2 : f K2 = 2) (k3 : f K3 = 3)
    (k6 : f K6 = 6) (k1 : f K1 = 1) (hb1 : f (sw 4) + 7 ≤ W)
    (hb2 : m (f (sw 4) + 5) + 5 * f uR + 3 ≤ W) : okB W m regHead f := by
  simp only [K5, K2, K3, K6, K1, sw, uR, Nat.reduceAdd] at k5 k2 k3 k6 k1 hb1 hb2
  simp [regHead, okB, okI, regI, upd, uA, uY, uLen, uOff, uR7, uT, uR, K5, K2, K3, K6, K1, sw,
    k5, k2, k3, k6, k1, IScr]
  omega

theorem regBody0_val (m f : ℕ → ℕ) :
    regB m regBody0 f uK = m (f uR7 + f uOff + f uT) := by
  simp [regBody0, regB, regI, upd, uA, uK, uR7, uOff, uT, sw]

theorem regBody0_ok (m f : ℕ → ℕ) (hb : f uR7 + f uOff + f uT ≤ W) : okB W m regBody0 f := by
  simp only [uR7, uOff, uT, sw, Nat.reduceAdd] at hb
  simp [regBody0, okB, okI, regI, upd, uA, uK, uR7, uOff, uT, sw, IScr]
  omega

/-- The chords of a region as positions of its list. -/
theorem regO_eq (N : NF) (r : ℕ) : regO N r =
    {j | ∃ t, t < (N.region r).chords.length ∧ j ∈ pairS ((N.region r).chords.getD t 0)} := by
  ext j
  simp only [regO, pairS, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, s, hs, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hk
    exact ⟨t, ht, s, hs, by rw [List.getD_eq_getElem _ _ ht]⟩
  · rintro ⟨t, ht, s, hs, rfl⟩
    exact ⟨_, by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht, s, hs, rfl⟩

theorem pre_succ (l : List ℕ) (t : ℕ) :
    {j | ∃ t', t' < t + 1 ∧ j ∈ pairS (l.getD t' 0)} =
      {j | ∃ t', t' < t ∧ j ∈ pairS (l.getD t' 0)} ∪ pairS (l.getD t 0) := by
  ext j
  simp only [mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨t', ht', hj⟩
    rcases (by omega : t' < t ∨ t' = t) with h | rfl
    · exact Or.inl ⟨t', h, hj⟩
    · exact Or.inr hj
  · rintro (⟨t', ht', hj⟩ | hj)
    · exact ⟨t', by omega, hj⟩
    · exact ⟨t, by omega, hj⟩

/-- **Both ends of every chord of a region.** -/
theorem regDo_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    (hI : IInv W c₀ c) {O : Set ℕ} (hinv : Inv O c) {r : ℕ} (hr : c.nreg uR = r)
    (hrn : r < N₂.nRegions) (hroom : c.nreg ALLOC + regK Kod (c₀.nreg (sw 6)) ≤ W) :
    IRS P W c₀ (regDo od) c (regK Kod (c₀.nreg (sw 6))) (fun c' => Inv (O ∪ regO N₂ r) c' ∧
      (∀ q, ER q → c'.nreg q = c.nreg q) ∧ AuxKeep c c') := by
  have hK := E.hK.fix hI
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
  set D := c₀.nreg (sw 6) with hD
  set B := c₀.nreg (sw 4) with hBd
  have hB : c.nreg (sw 4) = B := hI.hin _ (by ufo IFix sw)
  have hNW := E.hNW₂
  have hNA : NFAt c₀.nmem B N₂ := hNW.holds
  obtain ⟨b1, -, -, b4, -, b6⟩ := Restore.nf_bounds hNW
  obtain ⟨-, -, -, reg, hRC, -, -, hRO, -⟩ := E.hNF₂
  have hlenD : (N₂.region r).chords.length ≤ D := Gran.chords_le E.hNF₂ hRC hRO E.hdeg₂ hrn
  set R5 := c₀.nmem (B + 5) with hR5
  set R7 := c₀.nmem (B + 7) with hR7
  set off := c₀.nmem (R5 + 5 * r + 3) with hoff
  set len := (N₂.region r).chords.length with hlen
  have hreg := hNA.2.2.2.2.2.2.2.1 r hrn
  have hlen0 : c₀.nmem (R5 + 5 * r + 2) = len := hreg.2.1
  have hch : ∀ t, t < len → c₀.nmem (R7 + off + t) = (N₂.region r).chords.getD t 0 :=
    hreg.2.2.2.2
  have hb4 := b4 r hrn
  have hb6 : ∀ t, t < len → R7 + off + t < c₀.nreg ALLOC := b6 r hrn
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 ALLOC
  have hm5 : c.nmem (B + 5) = R5 := hI.hm _ (by omega)
  -- the head
  have hok : okB W c.nmem regHead c.nreg := regHead_ok _ _ k5 k2 k3 k6 k1
    (by rwo [hB]) (by rwo [hB, hm5, hr])
  obtain ⟨vLen, vOff, vR7, vT⟩ := regHead_val c.nmem c.nreg k5 k2 k3 k6 k1
  rw [hB, hm5, hr, hI.hm _ (by omega)] at vLen vOff
  rw [hB, hI.hm _ (by omega)] at vR7
  rw [hlen0] at vLen
  refine IRS.mono (K := regHead.length + ((2 * Kod + 8 + 2) * len + 2))
    (IRS.seq (IRS.block regHead hI hok) ?_) ?_ (fun _ => id)
  rotate_left
  · have : (2 * Kod + 8 + 2) * len ≤ (2 * Kod + 10) * D := Nat.mul_le_mul_left _ hlenD
    sio only [regHead, List.length_cons, List.length_nil, regK]
  rintro c₁ hI₁ hA1 hA1' hc1
  have r1 : c₁.nreg = regB c.nmem regHead c.nreg := by rw [hc1]
  have m1 : c₁.nmem = c.nmem := by rw [hc1]
  have inv1 : Inv O c₁ := by rw [hc1]; exact inv_blk hst regHead_lr hinv
  have e1 : ∀ q, ER q → c₁.nreg q = c.nreg q := fun q h => by rw [r1]; exact er_blk regHead_lr h
  have eA1 : c₁.nreg ALLOC = c.nreg ALLOC := by
    rw [r1]; exact regB_other _ _ _ (fun i hi he => by
      have := regHead_lr i hi; rw [he] at this; unfold LR ALLOC oK oS at this; unfold sw at this
      omega)
  -- the loop
  let S : ℕ → Set ℕ := fun t => {j | ∃ t', t' < t ∧ j ∈ pairS ((N₂.region r).chords.getD t' 0)}
  let I : Config → Prop := fun c' => Inv (O ∪ S (c'.nreg uT)) c' ∧ c'.nreg uT ≤ len ∧
    c'.nreg uLen = len ∧ c'.nreg uOff = off ∧ c'.nreg uR7 = R7 ∧
    (∀ q, ER q → c'.nreg q = c.nreg q) ∧ AuxKeep c c'
  have S0 : S 0 = ∅ := by
    ext j; simp only [S, mem_ofPred_eq, mem_empty_iff_false, iff_false]; rintro ⟨t, ht, -⟩; omega
  have hI1 : I c₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, e1, fun x _ _ => by rw [m1]⟩
    · rw [r1, vT, S0, Set.union_empty]; exact inv1
    · rwo [r1, vT]
    · rw [r1, vLen]
    · rw [r1, vOff]
    · rw [r1, vR7]
  have hroomL : c₁.nreg ALLOC + (2 * Kod + 8 + 2) * (len - c₁.nreg uT) ≤ W := by
    have : (2 * Kod + 8 + 2) * len ≤ (2 * Kod + 10) * D := Nat.mul_le_mul_left _ hlenD
    ruo [eA1, r1, vT, Nat.sub_zero] regK at hroom
  have hw := IRS.while (P := P) (c₀ := c₀) (a := uT) (b := uLen) (body := regBody od) I
    (fun c' => len - c'.nreg uT) (2 * Kod + 8)
    (fun c' hc hlt => by rwo [hc.2.2.1] at hlt) ?_ hI₁ hI1 hroomL
  · refine (hw.mono (by rw [r1, vT, Nat.sub_zero]) ?_)
    rintro c' ⟨⟨hinv', hle, hlen', -, -, he', hax'⟩, hnlt⟩
    rw [hlen'] at hnlt
    have ht : c'.nreg uT = len := by omega
    refine ⟨?_, he', hax'⟩
    rw [regO_eq]
    rw [ht] at hinv'
    exact hinv'
  -- the body
  intro c₂ hI₂ hc2 hlt hroom2
  obtain ⟨inv2, hle2, hlen2, hoff2, hR72, he2, hax2⟩ := hc2
  rw [hlen2] at hlt
  set t := c₂.nreg uT with ht
  have hbt := hb6 t hlt
  have hok0 : okB W c₂.nmem regBody0 c₂.nreg := regBody0_ok _ _ (by
    rw [hR72, hoff2]; have := hI₂.hw.1 ALLOC; have := hI₂.hA; omega)
  unfold regBody
  refine IRS.mono (K := regBody0.length + (2 * Kod + 4 + uInc.length)) ?_
    (by sio [regBody0, uInc]) (fun _ => id)
  refine IRS.seq (K₁ := regBody0.length) (K₂ := 2 * Kod + 4 + uInc.length)
    (IRS.block regBody0 hI₂ hok0) ?_
  rintro c₃ hI₃ hA3 hA3' hc3
  have r3 : c₃.nreg = regB c₂.nmem regBody0 c₂.nreg := by rw [hc3]
  have m3 : c₃.nmem = c₂.nmem := by rw [hc3]
  have inv3 : Inv (O ∪ S t) c₃ := by rw [hc3]; exact inv_blk hst regBody0_lr inv2
  have o3 : ∀ q, ¬ LR q → c₃.nreg q = c₂.nreg q := fun q hq => by
    rw [r3]; exact regB_other _ _ _ (fun i hi he => hq (he ▸ regBody0_lr i hi))
  have keepL3 : ∀ q, q ≠ uA → q ≠ uK → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
    rw [r3]; exact regB_other _ _ _ (fun i hi he => by
      simp only [regBody0, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact h1 he.symm
      · exact h1 he.symm
      · exact h2 he.symm)
  have vK : c₃.nreg uK = (N₂.region r).chords.getD t 0 := by
    rw [r3, regBody0_val, hR72, hoff2, hI₂.hm _ hbt, hch t hlt]
  have hkn : (N₂.region r).chords.getD t 0 < N₂.nChords := by
    have hmem : (N₂.region r).chords.getD t 0 ∈ (N₂.region r).chords := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    exact (((hRO r hrn).1 _).1 hmem).1
  have nA : ALLOC ≠ uA ∧ ALLOC ≠ uK := by ufo ALLOC uA uK sw
  have eA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := keepL3 _ nA.1 nA.2
  have hl0 : regBody0.length = 3 := rfl
  have hl1 : uInc.length = 1 := rfl
  rw [hl0] at hA3'
  refine IRS.seq (K₁ := 2 * Kod + 4) (K₂ := uInc.length)
    (odPair_irs E hod hst hI₃ inv3 vK hkn (by omega)) ?_
  rintro c₄ hI₄ hA4 hA4' ⟨inv4, keep4, aux4⟩
  have lr4 : ∀ q, q = uT ∨ q = uLen ∨ q = uOff ∨ q = uR7 → c₄.nreg q = c₂.nreg q := by
    intro q hq
    have hq' : LR q ∧ q ≠ oK ∧ q ≠ oS := by
      rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;>
        simp [LR, uT, uLen, uOff, uR7, oK, oS, sw]
    rw [keep4 q (Or.inr hq'), keepL3 q (by rcases hq with rfl | rfl | rfl | rfl <;>
      simp [uT, uLen, uOff, uR7, uA, sw]) (by rcases hq with rfl | rfl | rfl | rfl <;>
      simp [uT, uLen, uOff, uR7, uK, sw])]
  have k14 : c₄.nreg K1 = 1 := (E.hK.fix hI₄).2.1
  have hT4 : c₄.nreg uT = t := lr4 _ (Or.inl rfl)
  refine (IRS.block uInc hI₄ ?_).mono le_rfl ?_
  · simp only [uInc, okB, okI]
    exact ⟨⟨iscr_sw (by ufo uT sw) (by ufo uT sw),
      by rw [hT4, k14]; have := hI₄.hw.1 uLen; rwo [lr4 _ (Or.inr (Or.inl rfl)), hlen2] at this⟩, trivial⟩
  rintro c' hc'
  have r' : c'.nreg = regB c₄.nmem uInc c₄.nreg := by rw [hc']
  have vT' : c'.nreg uT = t + 1 := by
    rw [r']; simp [uInc, regB, regI, upd_same]; rw [hT4, k14]
  have o' : ∀ q, q ≠ uT → c'.nreg q = c₄.nreg q := fun q hq => by
    rw [r']; simp only [uInc, regB, regI]; exact upd_other _ _ _ hq
  have e3 : ∀ q, ER q → c₃.nreg q = c.nreg q := fun q h => (o3 q (er_not_lr h)).trans (he2 q h)
  have eER : ∀ q, ER q → c'.nreg q = c.nreg q := fun q h => by
    rw [o' q (fun e => er_not_lr h (e ▸ Or.inr (Or.inr ⟨by simp [uT, sw], by simp [uT, sw]⟩))),
      keep4 q (Or.inl h), e3 q h]
  refine ⟨⟨?_, by rwo [vT'], ?_, ?_, ?_, eER, ?_⟩, by rwo [vT']⟩
  · have hS : S (t + 1) = S t ∪ pairS ((N₂.region r).chords.getD t 0) := pre_succ _ t
    rw [vT', hS, ← Set.union_assoc]
    rw [hc']; exact inv_blk hst uInc_lr inv4
  · rw [o' _ (by simp [uLen, uT, sw]), lr4 _ (Or.inr (Or.inl rfl)), hlen2]
  · rw [o' _ (by simp [uOff, uT, sw]), lr4 _ (Or.inr (Or.inr (Or.inl rfl))), hoff2]
  · rw [o' _ (by simp [uR7, uT, sw]), lr4 _ (Or.inr (Or.inr (Or.inr rfl))), hR72]
  · have m' : c'.nmem = c₄.nmem := by rw [hc']
    have hax3 : AuxKeep c c₃ := fun x h1 h2 => by rw [m3]; exact hax2 x h1 h2
    have := auxKeep_trans hax3 e3 aux4
    intro x h1 h2; rw [m']; exact this x h1 h2

end

end SweepEv

end Chazelle.Core
