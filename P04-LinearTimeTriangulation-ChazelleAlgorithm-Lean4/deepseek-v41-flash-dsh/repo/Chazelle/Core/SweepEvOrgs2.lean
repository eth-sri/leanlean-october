module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvOrgs

/-!
# The sweep (WP-D), stage 3: the origin enumeration (task E), part 2

`orgs od`: the regions of the label list (`kL … kL + 3`, up to `kN`), the gap regions (`gR`,
`gR + 1`, up to `gN`), each by `regDo`, then the parents of the stops `sP` and `sP + 1`
(`parDo`).  The steps are composed with `StepOK` (a run step adding a set of queries to the
invariant and keeping the read registers and the auxiliary array of the entry configuration).

**`orgsTask : OrgsTask`** (`κO = 200`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-! ## Steps -/

/-- **A step of the enumeration** relative to the entry `ci`: it adds the queries `S` to the
invariant and keeps the read registers and the auxiliary array of `ci`. -/
def StepOK (P : Polygon) (W : ℕ) (c₀ ci : Config) (Inv : Set ℕ → Config → Prop) (s : Stmt)
    (S : Set ℕ) (K : ℕ) : Prop :=
  ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → (∀ q, ER q → c.nreg q = ci.nreg q) → AuxKeep ci c →
    Inv O c → c.nreg ALLOC + K ≤ W →
    IRS P W c₀ s c K (fun c' => Inv (O ∪ S) c' ∧ (∀ q, ER q → c'.nreg q = ci.nreg q) ∧
      AuxKeep ci c')

theorem StepOK.seq {ci : Config} {Inv : Set ℕ → Config → Prop} {s t : Stmt} {S T : Set ℕ}
    {K K' : ℕ} (h₁ : StepOK P W c₀ ci Inv s S K) (h₂ : StepOK P W c₀ ci Inv t T K') :
    StepOK P W c₀ ci Inv (.seq s t) (S ∪ T) (K + K') := by
  intro O c hI he ha hinv hroom
  refine IRS.seq (h₁ O c hI he ha hinv (⋄)) ?_
  rintro c₁ hI₁ - hA1 ⟨inv1, he1, ha1⟩
  refine (h₂ (O ∪ S) c₁ hI₁ he1 ha1 inv1 (⋄)).mono le_rfl ?_
  rintro c' ⟨inv', he', ha'⟩
  exact ⟨by rw [← Set.union_assoc]; exact inv', he', ha'⟩

/-- Chaining the read registers and the auxiliary array. -/
theorem keep_chain {ci c c' : Config} (he : ∀ q, ER q → c.nreg q = ci.nreg q) (ha : AuxKeep ci c)
    (he' : ∀ q, ER q → c'.nreg q = c.nreg q) (ha' : AuxKeep c c') :
    (∀ q, ER q → c'.nreg q = ci.nreg q) ∧ AuxKeep ci c' := by
  refine ⟨fun q h => (he' q h).trans (he q h), ?_⟩
  have he2 := he
  intro x h1 h2
  have ea : c.nreg aB = ci.nreg aB := he2 _ (by unfold ER; simp)
  have es : c.nreg sC = ci.nreg sC := he2 _ (by unfold ER; simp)
  Ξ ha' x (⋄) (⋄), ha x h1 h2

/-! ## A region step -/

/-- **A region step**: if `i < cnt` (`ka` holds `i`), the region in register `src`. -/
def rStep (ka cnt src : ℕ) (od : Stmt) : Stmt :=
  .ifLtN ka cnt (.seq (block [.copyN uR src]) (regDo od)) .skip

theorem copyR_lr (src : ℕ) : ∀ i ∈ [Instr.copyN uR src], LR (dstI i) := by
  Θ dstI, LR, uR, oK, oS, sw

theorem rStep_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} {ka cnt src i : ℕ} (hka : ∀ c, IInv W c₀ c → c.nreg ka = i) (hcnt : ER cnt)
    (hsrc : ER src) (hval : i < ci.nreg cnt → ci.nreg src < N₂.nRegions) :
    StepOK P W c₀ ci Inv (rStep ka cnt src od)
      {j | i < ci.nreg cnt ∧ j ∈ regO N₂ (ci.nreg src)} (regK Kod (c₀.nreg (sw 6)) + 3) := by
  intro O c hI he ha hinv hroom
  have hk := hka c hI
  refine IRS.mono (K := 1 + regK Kod (c₀.nreg (sw 6)) + 2) (IRS.ite ?_ ?_) (⋄)
    (fun _ h => h)
  · intro hlt
    Ξ' hk, he _ hcnt at hlt
    refine IRS.seq (IRS.block [.copyN uR src] hI ⟨iscr_sw (by unfold uR sw; omega)
      (by unfold uR sw; omega), trivial⟩) ?_
    rintro c₁ hI₁ - hA1 hc1
    have r1 : c₁.nreg = regB c.nmem [.copyN uR src] c.nreg := Ρ hc1
    have m1 : c₁.nmem = c.nmem := Ρ hc1
    have vR : c₁.nreg uR = ci.nreg src := by
      rw [r1]; simp [regB, regI, upd_same]; exact he _ hsrc
    have inv1 : Inv O c₁ := by rw [hc1]; exact inv_blk hst (copyR_lr src) hinv
    have he1 : ∀ q, ER q → c₁.nreg q = c.nreg q := fun q h => by
      rw [r1]; exact er_blk (copyR_lr src) h
    refine (regDo_irs E hod hst hI₁ inv1 vR (hval hlt) (⋄)).mono le_rfl ?_
    rintro c' ⟨inv', he', ha'⟩
    have hS : {j | i < ci.nreg cnt ∧ j ∈ regO N₂ (ci.nreg src)} = regO N₂ (ci.nreg src) := by
      ext j; Θ hlt
    refine ⟨by rw [hS]; exact inv', keep_chain he ha (fun q h => (he' q h).trans (he1 q h))
      (fun x h1 h2 => by rw [ha' x (by rw [he1 _ (by unfold ER; simp)]; exact h1)
        (by rw [he1 _ (by unfold ER; simp), he1 _ (by unfold ER; simp)]; exact h2), m1])⟩
  · intro hlt
    Ξ' hk, he _ hcnt at hlt
    have hS : {j | i < ci.nreg cnt ∧ j ∈ regO N₂ (ci.nreg src)} = ∅ := by
      ext j; Θ hlt
    exact IRS.skip hI ⟨by rw [hS, Set.union_empty]; exact hinv, he, ha⟩

/-! ## A parent step -/

/-- The parent of the stop `uI`: its auxiliary word `aB + 5 uI + 4`. -/
def parBody : List Instr :=
  [.copyN uA aB, .addN uA uA uI, .addN uA uA uI, .addN uA uA uI, .addN uA uA uI, .addN uA uA uI,
    .addN uA uA K4, .loadN uK uA]

def uDec : List Instr := [.subN uK uK K1]

/-- **The parent of the stop `uI`** (if `uI < sC` and it has one). -/
def parDo (od : Stmt) : Stmt :=
  .ifLtN uI sC (.seq (block parBody) (.ifLtN K0 uK (.seq (block uDec) (odPair od)) .skip)) .skip

/-- The queries of the parent of stop `i`. -/
def parS (ci : Config) (i : ℕ) : Set ℕ :=
  {j | i < ci.nreg sC ∧ 0 < parOf ci i ∧ ∃ s, s ≤ 1 ∧ j = 2 * (parOf ci i - 1) + s}

theorem parBody_lr : ∀ i ∈ parBody, LR (dstI i) := by
  Θ parBody, dstI, LR, uA, uK, oK, oS, sw

theorem uDec_lr : ∀ i ∈ uDec, LR (dstI i) := by
  Θ uDec, dstI, LR, uK, oK, oS, sw

theorem parBody_val (m f : ℕ → ℕ) (k4 : f K4 = 4) :
    regB m parBody f uK = m (f aB + 5 * f uI + 4) := by
  ϴ' K4, sw at k4
  Θ parBody, regB, regI, upd, uA, uK, uI, aB, K4, sw, k4
  ring_nf

theorem parBody_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ uA) (h2 : q ≠ uK) :
    regB m parBody f q = f q :=
  regB_other _ _ _ (fun i hi he => by
    ϴ' parBody, List.mem_cons, List.not_mem_nil, or_false at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact h1 he.symm | exact h2 he.symm)

theorem parBody_ok (m f : ℕ → ℕ) (k4 : f K4 = 4) (hb : f aB + 5 * f uI + 4 ≤ W) :
    okB W m parBody f := by
  ϴ' K4, aB, uI, sw, Nat.reduceAdd at k4 hb
  Θ parBody, okB, okI, regI, upd, uA, uK, uI, aB, K4, sw, k4, IScr
  omega


theorem parDo_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} (hpar : ∀ i, i < ci.nreg sC → parOf ci i ≤ N₂.nChords)
    (haux : ci.nreg aB + 5 * ci.nreg sC ≤ ci.nreg ALLOC) (hA : ci.nreg ALLOC ≤ W)
    {O : Set ℕ} (hI : IInv W c₀ c) (he : ∀ q, ER q → c.nreg q = ci.nreg q) (ha : AuxKeep ci c)
    (hinv : Inv O c) {i : ℕ} (hi : c.nreg uI = i) (hroom : c.nreg ALLOC + (2 * Kod + 17) ≤ W) :
    IRS P W c₀ (parDo od) c (2 * Kod + 17) (fun c' => Inv (O ∪ parS ci i) c' ∧
      (∀ q, ER q → c'.nreg q = ci.nreg q) ∧ AuxKeep ci c') := by
  have hK := E.hK.fix hI
  have esC : c.nreg sC = ci.nreg sC := he _ (by unfold ER; simp)
  have eaB : c.nreg aB = ci.nreg aB := he _ (by unfold ER; simp)
  refine IRS.mono (K := 8 + (1 + (2 * Kod + 4) + 2) + 2) (IRS.ite ?_ ?_) (⋄)
    (fun _ h => h)
  swap
  · intro hlt
    Ξ' hi, esC at hlt
    have hS : parS ci i = ∅ := by ext j; simp [parS]; omega
    exact IRS.skip hI ⟨by rw [hS, Set.union_empty]; exact hinv, he, ha⟩
  intro hlt
  Ξ' hi, esC at hlt
  have hadr : ci.nreg aB + 5 * i + 4 < ci.nreg aB + 5 * ci.nreg sC := ⋄
  refine IRS.seq (K₁ := parBody.length) (IRS.block parBody hI
    (parBody_ok _ _ hK.2.2.2.1 (by rw [eaB, hi]; omega))) ?_
  rintro c₁ hI₁ - hA1 hc1
  have r1 : c₁.nreg = regB c.nmem parBody c.nreg := Ρ hc1
  have m1 : c₁.nmem = c.nmem := Ρ hc1
  have vK : c₁.nreg uK = parOf ci i := by
    rw [r1, parBody_val _ _ hK.2.2.2.1, eaB, hi, ha _ (⋄) hadr]; rfl
  have inv1 : Inv O c₁ := by rw [hc1]; exact inv_blk hst parBody_lr hinv
  have he1 : ∀ q, ER q → c₁.nreg q = c.nreg q := fun q h => by
    rw [r1]; exact er_blk parBody_lr h
  have ha1 : AuxKeep c c₁ := fun x _ _ => Ρ m1
  have nA : ALLOC ≠ uA ∧ ALLOC ≠ uK := by unfold ALLOC uA uK sw; omega
  have eA1 : c₁.nreg ALLOC = c.nreg ALLOC := by rw [r1]; exact parBody_other _ _ nA.1 nA.2
  have hK1 := E.hK.fix hI₁
  have hl : parBody.length = 8 := rfl
  refine IRS.ite ?_ ?_
  swap
  · intro hn
    Ξ' hK1.1, vK at hn
    have hS : parS ci i = ∅ := by ext j; simp [parS]; omega
    obtain ⟨he', ha'⟩ := keep_chain he ha he1 ha1
    exact IRS.skip hI₁ ⟨by rw [hS, Set.union_empty]; exact inv1, he', ha'⟩
  intro hp
  Ξ' hK1.1, vK at hp
  refine IRS.seq (K₁ := 1) (IRS.block uDec hI₁ ⟨iscr_sw (by unfold uK sw; omega)
    (by unfold uK sw; omega), trivial⟩) ?_
  rintro c₂ hI₂ - hA2 hc2
  have r2 : c₂.nreg = regB c₁.nmem uDec c₁.nreg := Ρ hc2
  have m2 : c₂.nmem = c₁.nmem := Ρ hc2
  have vK2 : c₂.nreg uK = parOf ci i - 1 := by
    rw [r2]; simp [uDec, regB, regI, upd_same]; Ξ vK, hK1.2.1
  have inv2 : Inv O c₂ := by rw [hc2]; exact inv_blk hst uDec_lr inv1
  have he2 : ∀ q, ER q → c₂.nreg q = c₁.nreg q := fun q h => by
    rw [r2]; exact er_blk uDec_lr h
  have eA2 : c₂.nreg ALLOC = c₁.nreg ALLOC := by
    rw [r2]; simp only [uDec, regB, regI]; exact upd_other _ _ _ (by unfold ALLOC uK sw; omega)
  have hkn : parOf ci i - 1 < N₂.nChords := by have := hpar i hlt; omega
  refine (odPair_irs E hod hst hI₂ inv2 vK2 hkn (⋄)).mono le_rfl ?_
  rintro c' ⟨inv', he', ha'⟩
  have hS : parS ci i = pairS (parOf ci i - 1) := by
    ext j; ϴ parS, pairS, mem_ofPred_eq
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · intro h; exact ⟨hlt, hp, h⟩
  obtain ⟨k1e, k1a⟩ := keep_chain he ha he1 ha1
  obtain ⟨k2e, k2a⟩ := keep_chain k1e k1a he2 (fun x _ _ => Ρ m2)
  obtain ⟨k3e, k3a⟩ := keep_chain k2e k2a (fun q h => he' q (Or.inl h)) ha'
  exact ⟨by rw [hS]; exact inv', k3e, k3a⟩

/-- The parent of the stop `sP`. -/
def pStep0 (od : Stmt) : Stmt := .seq (block [.copyN uI sP]) (parDo od)

/-- The parent of the stop `sP + 1` (if `sP < sC`). -/
def pStep1 (od : Stmt) : Stmt :=
  .ifLtN sP sC (.seq (block [.addN uI sP K1]) (parDo od)) .skip

theorem pStep0_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} (hpar : ∀ i, i < ci.nreg sC → parOf ci i ≤ N₂.nChords)
    (haux : ci.nreg aB + 5 * ci.nreg sC ≤ ci.nreg ALLOC) (hA : ci.nreg ALLOC ≤ W) :
    StepOK P W c₀ ci Inv (pStep0 od) (parS ci (ci.nreg sP)) (1 + (2 * Kod + 17)) := by
  intro O c hI he ha hinv hroom
  have hlr : ∀ i ∈ [Instr.copyN uI sP], LR (dstI i) := ⊚ dstI, LR, uI, oK, oS, sw
  refine IRS.seq (IRS.block [.copyN uI sP] hI ⟨iscr_sw (by unfold uI sw; omega)
    (by unfold uI sw; omega), trivial⟩) ?_
  rintro c₁ hI₁ - hA1 hc1
  have r1 : c₁.nreg = regB c.nmem [.copyN uI sP] c.nreg := Ρ hc1
  have m1 : c₁.nmem = c.nmem := Ρ hc1
  have vI : c₁.nreg uI = ci.nreg sP := by
    rw [r1]; simp [regB, regI, upd_same]; exact he _ (by unfold ER; simp)
  have inv1 : Inv O c₁ := by rw [hc1]; exact inv_blk hst hlr hinv
  obtain ⟨he1, ha1⟩ := keep_chain he ha (fun q h => by rw [r1]; exact er_blk hlr h)
    (fun x _ _ => Ρ m1)
  exact parDo_ok E hod hst hpar haux hA hI₁ he1 ha1 inv1 vI (⋄)

theorem pStep1_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} (hpar : ∀ i, i < ci.nreg sC → parOf ci i ≤ N₂.nChords)
    (haux : ci.nreg aB + 5 * ci.nreg sC ≤ ci.nreg ALLOC) (hA : ci.nreg ALLOC ≤ W) :
    StepOK P W c₀ ci Inv (pStep1 od) (parS ci (ci.nreg sP + 1)) (1 + (2 * Kod + 17) + 2) := by
  intro O c hI he ha hinv hroom
  have eP : c.nreg sP = ci.nreg sP := he _ (by unfold ER; simp)
  have eC : c.nreg sC = ci.nreg sC := he _ (by unfold ER; simp)
  refine IRS.ite ?_ ?_
  swap
  · intro hn
    Ξ' eP, eC at hn
    have hS : parS ci (ci.nreg sP + 1) = ∅ := by ext j; simp [parS]; omega
    exact IRS.skip hI ⟨by rw [hS, Set.union_empty]; exact hinv, he, ha⟩
  intro hlt
  have hK := E.hK.fix hI
  have hlr : ∀ i ∈ [Instr.addN uI sP K1], LR (dstI i) := ⊚ dstI, LR, uI, oK, oS, sw
  refine IRS.seq (IRS.block [.addN uI sP K1] hI ⟨⟨iscr_sw (by unfold uI sw; omega)
    (by unfold uI sw; omega), by rw [hK.2.1]; have := hI.hw.1 sC; omega⟩, trivial⟩) ?_
  rintro c₁ hI₁ - hA1 hc1
  have r1 : c₁.nreg = regB c.nmem [.addN uI sP K1] c.nreg := Ρ hc1
  have m1 : c₁.nmem = c.nmem := Ρ hc1
  have vI : c₁.nreg uI = ci.nreg sP + 1 := by
    rw [r1]; simp [regB, regI, upd_same]; Ξ eP, hK.2.1
  have inv1 : Inv O c₁ := by rw [hc1]; exact inv_blk hst hlr hinv
  obtain ⟨he1, ha1⟩ := keep_chain he ha (fun q h => by rw [r1]; exact er_blk hlr h)
    (fun x _ _ => Ρ m1)
  exact parDo_ok E hod hst hpar haux hA hI₁ he1 ha1 inv1 vI (⋄)

/-! ## The enumeration -/

/-- **The origin enumeration of one iteration.** -/
def orgs (od : Stmt) : Stmt :=
  .seq (rStep K0 kN kL od) (.seq (rStep K1 kN (kL + 1) od) (.seq (rStep K2 kN (kL + 2) od)
    (.seq (rStep K3 kN (kL + 3) od) (.seq (rStep K0 gN gR od) (.seq (rStep K1 gN (gR + 1) od)
      (.seq (pStep0 od) (pStep1 od)))))))

/-- The queries of the steps are those of `iterO`. -/
theorem iter_eq (N : NF) (c : Config) :
    {j | 0 < c.nreg kN ∧ j ∈ regO N (c.nreg kL)} ∪
      ({j | 1 < c.nreg kN ∧ j ∈ regO N (c.nreg (kL + 1))} ∪
      ({j | 2 < c.nreg kN ∧ j ∈ regO N (c.nreg (kL + 2))} ∪
      ({j | 3 < c.nreg kN ∧ j ∈ regO N (c.nreg (kL + 3))} ∪
      ({j | 0 < c.nreg gN ∧ j ∈ regO N (c.nreg gR)} ∪
      ({j | 1 < c.nreg gN ∧ j ∈ regO N (c.nreg (gR + 1))} ∪
      (parS c (c.nreg sP) ∪ parS c (c.nreg sP + 1))))))) = iterO N c := by
  ext j
  ϴ iterO, parO, parS, mem_union, mem_ofPred_eq
  constructor
  · rintro (⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h1, h2, hj⟩ |
      ⟨h1, h2, hj⟩)
    · exact Or.inl (Or.inl ⟨0, ⋄, by rw [Nat.add_zero]; exact hj⟩)
    · exact Or.inl (Or.inl ⟨1, ⋄, hj⟩)
    · exact Or.inl (Or.inl ⟨2, ⋄, hj⟩)
    · exact Or.inl (Or.inl ⟨3, ⋄, hj⟩)
    · exact Or.inl (Or.inr ⟨0, ⋄, by rw [Nat.add_zero]; exact hj⟩)
    · exact Or.inl (Or.inr ⟨1, ⋄, hj⟩)
    · exact Or.inr ⟨_, Or.inl rfl, h1, h2, hj⟩
    · exact Or.inr ⟨_, Or.inr rfl, h1, h2, hj⟩
  · rintro ((⟨i, hi, hj⟩ | ⟨i, hi, hj⟩) | ⟨i, hi | hi, h1, h2, hj⟩)
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
      · Ξ' Nat.add_zero at hj; exact Or.inl ⟨⋄, hj⟩
      · exact Or.inr (Or.inl ⟨⋄, hj⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⋄, hj⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⋄, hj⟩)))
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · Ξ' Nat.add_zero at hj
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⋄, hj⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⋄, hj⟩)))))
    · subst hi
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, hj⟩))))))
    · subst hi
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, hj⟩))))))

theorem er_of {r : ℕ} (h : r = kN ∨ (kL ≤ r ∧ r < kL + 4) ∨ r = gN ∨ r = gR ∨ r = gR + 1) :
    ER r := by
  unfold ER; rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))


/-- **Task E: the origin enumeration.** -/
theorem orgsTask : OrgsTask := by
  refine ⟨orgs, 200, ?_⟩
  intro sh Bs F X Ok P W c₀ J N₁ N₂ E od Kod Inv hod hst O c hI hinv hkL hgR hpar haux hroom
  have hod' := hod
  have hst' : InvStab Inv := hst
  have hA : c.nreg ALLOC ≤ W := hI.hw.1 ALLOC
  have kv : ∀ c', IInv W c₀ c' → c'.nreg K0 = 0 ∧ c'.nreg K1 = 1 ∧ c'.nreg K2 = 2 ∧
      c'.nreg K3 = 3 := fun c' h => by
    obtain ⟨a, b, -, -, -, f, g⟩ := E.hK.fix h; exact ⟨a, b, f, g⟩
  have h := (rStep_ok E hod' hst' (ci := c) (ka := K0) (cnt := kN) (src := kL) (i := 0)
      (fun c' h => (kv c' h).1) (er_of (Or.inl rfl)) (er_of (Or.inr (Or.inl ⟨le_rfl, by
        unfold kL sw; omega⟩))) (fun h => by simpa using hkL 0 (⋄))).seq
    ((rStep_ok E hod' hst' (ci := c) (ka := K1) (cnt := kN) (src := kL + 1) (i := 1)
      (fun c' h => (kv c' h).2.1) (er_of (Or.inl rfl)) (er_of (Or.inr (Or.inl ⟨⋄, by
        omega⟩))) (fun h => hkL 1 (⋄))).seq
    ((rStep_ok E hod' hst' (ci := c) (ka := K2) (cnt := kN) (src := kL + 2) (i := 2)
      (fun c' h => (kv c' h).2.2.1) (er_of (Or.inl rfl)) (er_of (Or.inr (Or.inl ⟨⋄, by
        omega⟩))) (fun h => hkL 2 (⋄))).seq
    ((rStep_ok E hod' hst' (ci := c) (ka := K3) (cnt := kN) (src := kL + 3) (i := 3)
      (fun c' h => (kv c' h).2.2.2) (er_of (Or.inl rfl)) (er_of (Or.inr (Or.inl ⟨⋄, by
        omega⟩))) (fun h => hkL 3 (⋄))).seq
    ((rStep_ok E hod' hst' (ci := c) (ka := K0) (cnt := gN) (src := gR) (i := 0)
      (fun c' h => (kv c' h).1) (er_of (Or.inr (Or.inr (Or.inl rfl))))
      (er_of (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (fun h => by simpa using hgR 0 (⋄))).seq
    ((rStep_ok E hod' hst' (ci := c) (ka := K1) (cnt := gN) (src := gR + 1) (i := 1)
      (fun c' h => (kv c' h).2.1) (er_of (Or.inr (Or.inr (Or.inl rfl))))
      (er_of (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (fun h => hgR 1 (⋄))).seq
    ((pStep0_ok E hod' hst' hpar haux hA).seq (pStep1_ok E hod' hst' hpar haux hA)))))))
  Ξ' iter_eq at h
  set D := c₀.nreg (sw 6) with hD
  have e1 : (12 * D + 8) * (Kod + 200) + 200 = 12 * (D * Kod) + 2400 * D + 8 * Kod + 1800 := by
    ring
  have e2 : regK Kod D = 2 * (D * Kod) + 10 * D + 17 := by unfold regK; ring
  refine (h O c hI (fun _ _ => rfl) (fun _ _ _ => rfl) hinv ?_).mono ?_ (fun c' h' => h'.1)
  · rw [e2]; Ξ' e1 at hroom; omega
  · rw [e2, e1]; omega

end

end SweepEv

end Chazelle.Core
