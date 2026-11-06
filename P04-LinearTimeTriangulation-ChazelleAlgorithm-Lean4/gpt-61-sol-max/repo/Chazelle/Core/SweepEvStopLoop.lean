module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopTasks2
public import Chazelle.Core.SweepEvStopTasks
public import Chazelle.Core.SweepEvStopL

/-!
# The sweep (WP-D), stage 2: the loop over the stop origins and the assembly of `StopTask`

`stopTask_of (hO : OrgTask) (hS : SortTask) : StopTask`: the model descriptor of `C₂`
(`md2Init`), the raw array (`11 (4 K₂ + 8)` words, `gRB`, `gRC := 0`), the per-origin step for the
codes `(0, 0, b)`, `(2, 0, b)` and `(1, k, b)` (`k < K₂`, `b ≤ 1`), the sort, and `StopOut` from
`stopsOK_of'` and `stop_complete`.  Loop registers `sw 4200 …`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers of the loop -/

def slK : ℕ := sw 4200
def slN : ℕ := sw 4201
def slV : ℕ := sw 4202

/-- `n` increments of the allocator. -/
def slInc : ℕ → Stmt
  | 0 => .skip
  | n + 1 => .seq (.instr (.addN ALLOC ALLOC K1)) (slInc n)

theorem slInc_irs (hK : Consts c₀) : ∀ (n : ℕ) {c : Config}, IInv W c₀ c →
    c.nreg ALLOC + n ≤ W →
    IRS P W c₀ (slInc n) c n (fun c' => c'.nreg ALLOC = c.nreg ALLOC + n ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem)
  | 0, c, hI, _ => IRS.skip hI ⟨rfl, fun _ _ => rfl, rfl⟩
  | n + 1, c, hI, hroom => by
    have k1 : c.nreg K1 = 1 := (hK.fix hI).2.1
    have ex := Exec.addN (P := P) hI.hw ALLOC ALLOC K1 (by omega)
    have h1 : IRS P W c₀ (.instr (.addN ALLOC ALLOC K1)) c 1 (fun c' =>
        c' = { c with nreg := upd c.nreg ALLOC (c.nreg ALLOC + c.nreg K1) }) := by
      refine IRS.ofExec hI ex le_rfl (fun r _ hr => ?_) rfl (fun _ _ => rfl) rfl rfl
        (by simp_all) (by simp_all) rfl
      simp_all
    refine (IRS.seq (K₂ := n) h1 ?_).mono (by omega) (fun _ h => h)
    rintro c₁ hI₁ - - rfl
    have hA : ({ c with nreg := upd c.nreg ALLOC (c.nreg ALLOC + c.nreg K1) } : Config).nreg ALLOC =
        c.nreg ALLOC + 1 := by simp_all
    refine (slInc_irs hK n hI₁ (by omega)).mono le_rfl ?_
    simp_all +arith


/-- The raw records only read their eleven words. -/
theorem slRawV_congr {J : Merge.Junction} {N : NF} {m m' : ℕ → ℕ} {RB i : ℕ}
    (h : ∀ j, j < 11 → m' (RB + 11 * i + j) = m (RB + 11 * i + j)) (hv : RawV P J N m RB i) :
    RawV P J N m' RB i := by
  have e1 : rawRec m' RB i = rawRec m RB i := by
    unfold rawRec
    rw [show RB + 11 * i = RB + 11 * i + 0 by ring, h 0 (by norm_num), h 1 (by norm_num),
      h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num)]
  simp_all [rawDc, rawAux, RawV]

/-- **The invariant of the origin loop** (`M1` the configuration after `md2Init`, the raw array
at `A0 = M1.ALLOC`, `u` codes done, the set `D` of done codes). -/
structure SlpInv (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c M1 : Config) (u : ℕ)
    (D : ℕ → ℕ → ℕ → Prop) (c' : Config) : Prop where
  rb : c'.nreg gRB = M1.nreg ALLOC
  room : M1.nreg ALLOC + 11 * (4 * N₂.nChords + 8) ≤ c'.nreg ALLOC
  cnt : c'.nreg gRC ≤ 2 * u
  valid : ∀ i, i < c'.nreg gRC → RawV P J N₂ c'.nmem (M1.nreg ALLOC) i
  compl : ∀ kind k b, D kind k b → OrgD P J N₂ kind k b → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W (stopSet J (Qof P) N₂ kind k b) p t →
    (Lst J : ℝ) ≤ oW J (p + t) → ∃ i, i < c'.nreg gRC ∧
      (rawRec c'.nmem (M1.nreg ALLOC) i).1 = p ∧
      rPar P J (rawRec c'.nmem (M1.nreg ALLOC) i) = t ∧
      rSet P J N₂ (rawRec c'.nmem (M1.nreg ALLOC) i) = stopSet J (Qof P) N₂ kind k b
  memM : ∀ a, a < M1.nreg ALLOC → c'.nmem a = M1.nmem a
  regM : c'.nreg gMD2 = M1.nreg gMD2 ∧ c'.nreg gCD2 = M1.nreg gCD2
  regs : ∀ r, bandOf r ∉ oracleBands → ¬ S2R r → r ≠ ALLOC → c'.nreg r = c.nreg r

theorem slpOrgR_S2R {r : ℕ} (h : SOrgR r) : S2R r := by
  omega_nf

/-- The model context of `C₂` along the invariant. -/
theorem SlpInv.ctx {J : Merge.Junction} {N₂ : NF} {c M1 c' : Config} {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} (hS : SlpInv P J N₂ c M1 u D c')
    (hctx : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) M1)
    (hIM : IInv W c₀ M1) (hI' : IInv W c₀ c') :
    MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c' := by
  have hA1 : M1.nreg ALLOC ≤ c'.nreg ALLOC := by ram_grind
  refine hctx.transport (fun r hr => ?_) (fun a ha => hS.memM a ha) hA1
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · ram_grind
  · ram_grind
  · exact (hI'.hin _ (by omega_nf)).trans (hIM.hin _ (by omega_nf)).symm
  · exact (hI'.hin _ (by omega_nf)).trans
      (hIM.hin _ (by omega_nf)).symm
  · exact (hI'.hin _ (by omega_nf)).trans
      (hIM.hin _ (by omega_nf)).symm

set_option maxHeartbeats 4000000 in
/-- **One per-origin step** keeps the invariant and adds its code. -/
theorem slOrg_step {J : Merge.Junction} {N₂ : NF} {M1 c' c'' : Config} {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} (hS : SlpInv P J N₂ c M1 u D c') (hu : u + 1 ≤ 2 * N₂.nChords + 4)
    (hO : OrgOut P J N₂ (c'.nreg oKd) (c'.nreg oKk) (c'.nreg oB) c' c'') :
    SlpInv P J N₂ c M1 (u + 1)
      (fun kind k b => D kind k b ∨ (kind = c'.nreg oKd ∧ k = c'.nreg oKk ∧ b = c'.nreg oB)) c'' ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c''.nreg r = c'.nreg r) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hO
  have hcnt := hS.cnt
  rw [hS.rb] at o3 o4 o5
  have keepOld : ∀ i, i < c'.nreg gRC → ∀ j, j < 11 →
      c''.nmem (M1.nreg ALLOC + 11 * i + j) = c'.nmem (M1.nreg ALLOC + 11 * i + j) :=
    fun i hi j hj => o5 _ (by have := hS.room; omega) (Or.inl (by nlinarith))
  have hR : ∀ r, 240000 ≤ r → r < 250000 → ¬ SOrgR r → c''.nreg r = c'.nreg r := fun r h1 h2 h3 =>
    o7 r (not_oracle_sw h1 h2) h3 (by omega_nf)
  have rB : c''.nreg gRB = c'.nreg gRB := hR _ (by omega_nf) (by omega_nf)
    (by omega_nf)
  have rM : c''.nreg gMD2 = c'.nreg gMD2 := hR _ (by omega_nf)
    (by omega_nf) (by omega_nf)
  have rC : c''.nreg gCD2 = c'.nreg gCD2 := hR _ (by omega_nf)
    (by omega_nf) (by omega_nf)
  refine ⟨⟨by rw [rB, hS.rb], by have := hS.room; omega, by omega,
    fun i hi => ?_, fun kind k b hD hOD p t hA hL => ?_, fun a ha => ?_,
    ⟨by rw [rM, hS.regM.1], by rw [rC, hS.regM.2]⟩, fun r h0 h1 h2 => ?_⟩, o7⟩
  · by_cases hi' : i < c'.nreg gRC
    · exact slRawV_congr (keepOld i hi') (hS.valid i hi')
    grind
  · rcases hD with hD | ⟨rfl, rfl, rfl⟩
    · obtain ⟨i, hi, e1, e2, e3⟩ := hS.compl kind k b hD hOD p t hA hL
      have hrr : rawRec c''.nmem (M1.nreg ALLOC) i = rawRec c'.nmem (M1.nreg ALLOC) i := by
        unfold rawRec
        rw [show M1.nreg ALLOC + 11 * i = M1.nreg ALLOC + 11 * i + 0 by ring,
          keepOld i hi 0 (by norm_num), keepOld i hi 1 (by norm_num),
          keepOld i hi 3 (by norm_num), keepOld i hi 4 (by norm_num), keepOld i hi 5 (by norm_num)]
      grind
    grind
  · rw [o5 a (by have := hS.room; omega) (Or.inl (by omega)), hS.memM a ha]
  · rw [o7 r h0 (fun h => h1 (slpOrgR_S2R h)) h2, hS.regs r h0 h1 h2]

/-- The invariant survives changes of the code and loop registers `sw 4010 … sw 4999`. -/
theorem SlpInv.regChange {J : Merge.Junction} {N₂ : NF} {c M1 c' c'' : Config} {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} (h : SlpInv P J N₂ c M1 u D c')
    (hr : ∀ r, ¬ (sw 4010 ≤ r ∧ r < sw 5000) → c''.nreg r = c'.nreg r)
    (hm : c''.nmem = c'.nmem) : SlpInv P J N₂ c M1 u D c'' := by
  grind [Chazelle.Core.SweepEv.SlpInv, ALLOC, sw, gRB, gRC, eA, gMD2, gCD2, S2R]

/-- Set the code registers and run the per-origin step. -/
def slCode (o : Stmt) (kd : ℕ) (ins : Instr) (b : ℕ) : Stmt :=
  .seq (block [.constN oKd kd, ins, .constN oB b]) o

set_option maxHeartbeats 4000000 in
theorem slCode_irs {J : Merge.Junction} {N₂ : NF} {c₁ M1 : Config} {o : Stmt} {Ko : ℕ → ℕ} {u : ℕ}
    {D : ℕ → ℕ → ℕ → Prop} {kd b kv : ℕ} {ins : Instr}
    (hctx : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) M1)
    (hO : ∀ c', IInv W c₀ c' → MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c' →
      c'.nreg oKd ≤ 2 → c'.nreg oB ≤ 1 → (c'.nreg oKd = 1 → c'.nreg oKk < N₂.nChords) →
      c₀.nreg ALLOC ≤ c'.nreg gRB →
      c'.nreg gRB + 11 * (c'.nreg gRC + 2) ≤ c'.nreg ALLOC → c'.nreg ALLOC + Ko (c'.nreg oKd) ≤ W →
      IRS P W c₀ o c' (Ko (c'.nreg oKd)) (OrgOut P J N₂ (c'.nreg oKd) (c'.nreg oKk) (c'.nreg oB) c'))
    (hA0 : Consts c₀) (hIM : IInv W c₀ M1) (hI : IInv W c₀ c) (hS : SlpInv P J N₂ c₁ M1 u D c)
    (hins : (ins = .constN oKk 0 ∧ kv = 0) ∨ (ins = .copyN oKk slK ∧ kv = c.nreg slK))
    (hkd : kd ≤ 2) (hb : b ≤ 1) (hk : kd = 1 → kv < N₂.nChords)
    (hu : u + 1 ≤ 2 * N₂.nChords + 4) (hroom : c.nreg ALLOC + (3 + Ko kd) ≤ W) :
    IRS P W c₀ (slCode o kd ins b) c (3 + Ko kd) (fun c' => SlpInv P J N₂ c₁ M1 (u + 1)
      (fun kind k b' => D kind k b' ∨ (kind = kd ∧ k = kv ∧ b' = b)) c' ∧
      c'.nreg slK = c.nreg slK ∧ c'.nreg slN = c.nreg slN ∧ c'.nreg slV = c.nreg slV) := by
  
  have ok : okB W c.nmem [.constN oKd kd, ins, .constN oB b] c.nreg := by
    rcases hins with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨⟨iscr_sw (by omega_nf) (by omega_nf), by omega⟩,
        ⟨iscr_sw (by omega_nf) (by omega_nf), by omega⟩,
        ⟨iscr_sw (by omega_nf) (by omega_nf), by omega⟩, trivial⟩
    · exact ⟨⟨iscr_sw (by omega_nf) (by omega_nf), by omega⟩,
        iscr_sw (by omega_nf) (by omega_nf),
        ⟨iscr_sw (by omega_nf) (by omega_nf), by omega⟩, trivial⟩
  refine (IRS.seq (K₂ := Ko kd) (IRS.block _ hI ok) ?_).mono (by simp) (fun _ h => h)
  rintro c₂ hI₂ - - hc2
  have vals : c₂.nreg oKd = kd ∧ c₂.nreg oKk = kv ∧ c₂.nreg oB = b ∧
      (∀ r, r ≠ oKd → r ≠ oKk → r ≠ oB → c₂.nreg r = c.nreg r) ∧ c₂.nmem = c.nmem := by
    subst hc2
    rcases hins with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp only [regB, regI, oKd, oKk, oB, slK, sw, Nat.reduceAdd]
      simp_all
  obtain ⟨v1, v2, v3, v4, v5⟩ := vals
  have hS2 : SlpInv P J N₂ c₁ M1 u D c₂ := hS.regChange (fun r hr => v4 r
    (fun h => hr (by ram_grind)) (fun h => hr (by grind [oKk, sw]))
    (fun h => hr (by grind [oB, sw]))) v5
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := v4 _ (by omega_nf)
    (by omega_nf) (by omega_nf)
  have hO2 := hO c₂ hI₂ (hS2.ctx hctx hIM hI₂) (by omega) (by omega)
    (by omega) (by rw [hS2.rb]; exact hIM.hA)
    (by rw [hS2.rb]; have := hS2.room; have := hS2.cnt; omega)
    (by grind)
  refine hO2.mono (le_of_eq (by rw [v1])) ?_
  intro c' hc'
  obtain ⟨h1, h2⟩ := slOrg_step hS2 hu hc'
  rw [v1, v2, v3] at h1
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h2 _ (not_oracle_sw (by omega_nf) (by omega_nf))
      (by omega_nf) (by omega_nf),
      v4 _ (by omega_nf) (by omega_nf) (by omega_nf)]
  · rw [h2 _ (not_oracle_sw (by omega_nf) (by omega_nf))
      (by omega_nf) (by omega_nf),
      v4 _ (by omega_nf) (by omega_nf) (by omega_nf)]
  · rw [h2 _ (not_oracle_sw (by omega_nf) (by omega_nf))
      (by omega_nf) (by omega_nf),
      v4 _ (by omega_nf) (by omega_nf) (by omega_nf)]


/-- The allocation of the raw array: `44` words per round, `slV` rounds. -/
def slAlloc : Stmt := .whileLtN slK slV (.seq (slInc 44) (block [.addN slK slK K1]))

set_option maxHeartbeats 4000000 in
theorem slAlloc_irs (hK : Consts c₀) (hI : IInv W c₀ c) (h0 : c.nreg slK = 0)
    (hroom : c.nreg ALLOC + (47 * c.nreg slV + 2) ≤ W) :
    IRS P W c₀ slAlloc c (47 * c.nreg slV + 2) (fun c' =>
      c'.nreg ALLOC = c.nreg ALLOC + 44 * c.nreg slV ∧ c'.nreg slK = c.nreg slV ∧
      (∀ r, r ≠ slK → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  set V := c.nreg slV
  have hVW : V ≤ W := by omega
  refine (IRS.while (Kb := 45) (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 44 * c'.nreg slK ∧
      c'.nreg slK ≤ V ∧ (∀ r, r ≠ slK → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem)
      (fun c' => V - c'.nreg slK) ?_ ?_ hI ⟨by omega, by omega, fun _ _ _ => rfl, rfl⟩
      (by omega)).mono (by omega) ?_
  · ram_grind
  · rintro c' hI' ⟨a1, a2, a3, a4⟩ ht hroom'
    have hV' : c'.nreg slV = V := a3 slV (by omega_nf) (by omega_nf)
    rw [hV'] at ht
    refine IRS.seq (K₂ := 1) (slInc_irs hK 44 hI' (by omega)) ?_
    rintro c₁ hI₁ - - ⟨b1, b2, b3⟩
    have k1 : c₁.nreg K1 = 1 := (hK.fix hI₁).2.1
    have hk1 : c₁.nreg slK = c'.nreg slK := b2 _ (by omega_nf)
    refine (IRS.block [.addN slK slK K1] hI₁ ⟨⟨iscr_sw (by omega_nf)
      (by omega_nf), by omega⟩, trivial⟩).mono le_rfl ?_
    rintro c'' rfl
    have v : ∀ r, r ≠ slK → regB c₁.nmem [.addN slK slK K1] c₁.nreg r = c₁.nreg r := by
      simp_all [regB, regI]
    have vk : regB c₁.nmem [.addN slK slK K1] c₁.nreg slK = c'.nreg slK + 1 := by
      simp_all [regB, regI, upd_same]
    grind
  grind


/-- The codes done after the shared and top codes and the wall codes of the chords `< k₀`. -/
def slD (k₀ kind k b : ℕ) : Prop := b ≤ 1 ∧ (((kind = 0 ∨ kind = 2) ∧ k = 0) ∨ (kind = 1 ∧ k < k₀))

theorem SlpInv.monoD {J : Merge.Junction} {N₂ : NF} {c M1 c' : Config} {u u' : ℕ}
    {D D' : ℕ → ℕ → ℕ → Prop} (h : SlpInv P J N₂ c M1 u D c')
    (hD : ∀ kind k b, D' kind k b → D kind k b) (hu : u ≤ u') : SlpInv P J N₂ c M1 u' D' c' :=
  by ram_grind

/-- The loop over the chords of `N₂` (both directions). -/
def slKLoop (o : Stmt) : Stmt :=
  .whileLtN slK slN (.seq (slCode o 1 (.copyN oKk slK) 0)
    (.seq (slCode o 1 (.copyN oKk slK) 1) (block [.addN slK slK K1])))

set_option maxHeartbeats 4000000 in
theorem slKLoop_irs {J : Merge.Junction} {N₂ : NF} {c₁ M1 : Config} {o : Stmt} {Ko : ℕ → ℕ}
    (hctx : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) M1)
    (hO : ∀ c', IInv W c₀ c' → MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c' →
      c'.nreg oKd ≤ 2 → c'.nreg oB ≤ 1 → (c'.nreg oKd = 1 → c'.nreg oKk < N₂.nChords) →
      c₀.nreg ALLOC ≤ c'.nreg gRB →
      c'.nreg gRB + 11 * (c'.nreg gRC + 2) ≤ c'.nreg ALLOC → c'.nreg ALLOC + Ko (c'.nreg oKd) ≤ W →
      IRS P W c₀ o c' (Ko (c'.nreg oKd)) (OrgOut P J N₂ (c'.nreg oKd) (c'.nreg oKk) (c'.nreg oB) c'))
    (hK : Consts c₀) (hIM : IInv W c₀ M1) (hI : IInv W c₀ c)
    (hS : SlpInv P J N₂ c₁ M1 4 (slD 0) c) (h0 : c.nreg slK = 0) (hN : c.nreg slN = N₂.nChords)
    (hroom : c.nreg ALLOC + ((7 + 2 * Ko 1 + 2) * N₂.nChords + 2) ≤ W) :
    IRS P W c₀ (slKLoop o) c ((7 + 2 * Ko 1 + 2) * N₂.nChords + 2) (fun c' =>
      SlpInv P J N₂ c₁ M1 (4 + 2 * N₂.nChords) (slD N₂.nChords) c') := by
  have hKW : N₂.nChords ≤ W := by nlinarith
  refine (IRS.while (Kb := 7 + 2 * Ko 1) (fun c' => SlpInv P J N₂ c₁ M1 (4 + 2 * c'.nreg slK)
      (slD (c'.nreg slK)) c' ∧ c'.nreg slN = N₂.nChords ∧ c'.nreg slK ≤ N₂.nChords)
      (fun c' => N₂.nChords - c'.nreg slK) ?_ ?_ hI ⟨by simp_all, hN, by omega⟩
      (by grind)).mono (by simp_all) ?_
  · omega
  · rintro c' hI' ⟨hS', hN', hk'⟩ ht hroom'
    rw [hN'] at ht
    set k := c'.nreg slK with hk_def
    refine (IRS.seq (K₂ := 4 + Ko 1) (slCode_irs (kd := 1) (b := 0) hctx hO hK hIM hI' hS'
      (Or.inr ⟨rfl, rfl⟩) (by norm_num) (by norm_num) (fun _ => ht) (by omega) (by omega)) ?_).mono
      (by omega) (fun _ h => h)
    rintro c₂ hI₂ - hA₂' ⟨hS₂, k2, n2, -⟩
    refine (IRS.seq (K₂ := 1) (slCode_irs (kd := 1) (b := 1) hctx hO hK hIM hI₂ hS₂
      (Or.inr ⟨rfl, rfl⟩) (by norm_num) (by norm_num) (fun _ => by omega)
      (by omega) (by omega)) ?_).mono (by omega) (fun _ h => h)
    rintro c₃ hI₃ - - ⟨hS₃, k3, n3, -⟩
    have k1 : c₃.nreg K1 = 1 := (hK.fix hI₃).2.1
    refine (IRS.block [.addN slK slK K1] hI₃ ⟨⟨iscr_sw (by omega_nf)
      (by omega_nf), by omega⟩, trivial⟩).mono le_rfl ?_
    rintro c'' rfl
    have v : ∀ r, r ≠ slK → regB c₃.nmem [.addN slK slK K1] c₃.nreg r = c₃.nreg r := by
      simp_all [regB, regI] <;> omega_nf
    have vk : regB c₃.nmem [.addN slK slK K1] c₃.nreg slK = k + 1 := by
      simp_all [regB, regI, upd_same] <;> omega_nf
    have hS₄ := hS₃.regChange (c'' := { c₃ with nreg := regB c₃.nmem [.addN slK slK K1] c₃.nreg })
      (fun r hr => v r (fun h => hr (by grind [slK, sw]))) rfl
    refine ⟨⟨?_, by grind,
      by grind⟩, by grind⟩
    dsimp only at hS₄ ⊢
    rw [vk]
    refine hS₄.monoD ?_ (by omega)
    ram_grind
  grind


theorem slp_clog_le {K L : ℕ} (hL : L = Nat.clog 2 K) (_hK : 1 ≤ K) {x : ℕ} (hx : x ≤ 16 * K) :
    Nat.clog 2 x ≤ L + 4 := by
  have h1 : K ≤ 2 ^ L := by rw [hL]; exact Nat.le_pow_clog (by norm_num) K
  have h2 : x ≤ 2 ^ (L + 4) := by grind
  exact (Nat.clog_le_of_le_pow h2)

theorem slp_cost (κo κs K₁ K₂ F T L : ℕ) (hL : L = Nat.clog 2 (K₁ + K₂ + 1)) (hT : T ≤ L + 3) :
    25 + (5 + ((47 * (K₂ + 2) + 2) + (1 + ((3 + κo * (K₁ + K₂ + 1) * (F + T + 1)) +
      ((3 + κo * (K₁ + K₂ + 1) * (F + T + 1)) + ((3 + κo * (K₁ + K₂ + 1) * (F + T + 1)) +
      ((3 + κo * (K₁ + K₂ + 1) * (F + T + 1)) + (((7 + 2 * (κo * 1 * (F + T + 1)) + 2) * K₂ + 2) +
      κs * (4 * K₂ + 8 + 1) * (Nat.clog 2 (4 * K₂ + 8 + 1) + 1))))))))) ≤
    (24 * κo + 45 * κs + 400) * (K₁ + K₂ + 1) * (F + L + 1) := by
  have hc : Nat.clog 2 (4 * K₂ + 8 + 1) ≤ L + 4 := slp_clog_le hL (by omega) (by omega)
  set Kc := K₁ + K₂ + 1 with hKc
  set Y := F + L + 1 with hY
  have hX : F + T + 1 ≤ 4 * Y := by omega
  have hY1 : 1 ≤ Y := by omega
  
  have e1 : κo * Kc * (F + T + 1) ≤ κo * Kc * (4 * Y) := Nat.mul_le_mul_left _ hX
  
  have e3 : κs * (4 * K₂ + 8 + 1) * (Nat.clog 2 (4 * K₂ + 8 + 1) + 1) ≤ κs * (9 * Kc) * (5 * Y) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  grind


/-- The setup of the raw array. -/
def slSetup : List Instr :=
  [.copyN gRB ALLOC, .constN gRC 0, .loadN slN (sw 4), .addN slV slN K2, .constN slK 0]

/-- **Stage 2**: the model descriptor of `C₂`, the raw array, the codes, the sort. -/
def slpStopP (o srt : Stmt) : Stmt :=
  .seq md2Init (.seq (block slSetup) (.seq slAlloc (.seq (block [.constN slK 0])
    (.seq (slCode o 0 (.constN oKk 0) 0) (.seq (slCode o 0 (.constN oKk 0) 1)
    (.seq (slCode o 2 (.constN oKk 0) 0) (.seq (slCode o 2 (.constN oKk 0) 1)
    (.seq (slKLoop o) srt))))))))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **`StopTask` from the per-origin step and the sort.** -/
theorem stopTask_of (hO : OrgTask) (hS : SortTask) : StopTask := by
  obtain ⟨org, κo, hOrg⟩ := hO
  obtain ⟨srt, κs, hSrt⟩ := hS
  refine ⟨fun sh => slpStopP (org sh) srt, fun D => 24 * κo D + 45 * κs + 400, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hroom
  set Kc := N₁.nChords + N₂.nChords + 1 with hKc
  set XX := F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1 with hXX
  set Ko : ℕ → ℕ := fun kd => κo (c₀.nreg (sw 6)) * (if kd = 1 then 1 else Kc) * XX with hKo
  have hOc : ∀ c', IInv W c₀ c' → MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c' →
      c'.nreg oKd ≤ 2 → c'.nreg oB ≤ 1 → (c'.nreg oKd = 1 → c'.nreg oKk < N₂.nChords) →
      c₀.nreg ALLOC ≤ c'.nreg gRB →
      c'.nreg gRB + 11 * (c'.nreg gRC + 2) ≤ c'.nreg ALLOC → c'.nreg ALLOC + Ko (c'.nreg oKd) ≤ W →
      IRS P W c₀ (org sh) c' (Ko (c'.nreg oKd))
        (OrgOut P J N₂ (c'.nreg oKd) (c'.nreg oKk) (c'.nreg oB) c') :=
    fun c' h1 h2 h3 h4 h5 h6 h6' h7 => hOrg sh Bs F X Ok P W c₀ c' J N₁ N₂ E h1 h2 h3 h4 h5 h6 h6' h7
  have hK := E.hK
  have hcost := slp_cost (κo (c₀.nreg (sw 6))) κs N₁.nChords N₂.nChords (F (c₀.nreg (sw 5)))
    (c₀.nreg TLR) _ rfl E.hTLR
  set K₂ := N₂.nChords with hK₂d
  set R9 := κs * (4 * K₂ + 8 + 1) * (Nat.clog 2 (4 * K₂ + 8 + 1) + 1) with hR9
  set R8 := ((7 + 2 * Ko 1 + 2) * K₂ + 2) + R9 with hR8
  set R7 := (3 + Ko 2) + R8 with hR7
  set R6 := (3 + Ko 2) + R7 with hR6
  set R5 := (3 + Ko 0) + R6 with hR5
  set R4 := (3 + Ko 0) + R5 with hR4
  set R3 := 1 + R4 with hR3
  set R2 := (47 * (K₂ + 2) + 2) + R3 with hR2
  set R1 := 5 + R2 with hR1
  have hKo0 : Ko 0 = κo (c₀.nreg (sw 6)) * Kc * XX := by simp [hKo]
  have hKo2 : Ko 2 = κo (c₀.nreg (sw 6)) * Kc * XX := by simp [hKo]
  have hKo1 : Ko 1 = κo (c₀.nreg (sw 6)) * 1 * XX := by simp [hKo]
  have hT : 25 + R1 ≤ (24 * κo (c₀.nreg (sw 6)) + 45 * κs + 400) * Kc *
      (F (c₀.nreg (sw 5)) + Nat.clog 2 Kc + 1) := by
    simp only [hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hKo0, hKo2, hKo1]; exact hcost
  have hroom' : c.nreg ALLOC + (25 + R1) ≤ W := by
    dsimp only at hroom; exact le_trans (Nat.add_le_add_left hT _) hroom
  refine (IRS.seq (K₂ := R1) (md2Init_irs E hI (by omega)) ?_).mono hT (fun _ h => h)
  have hRge : 47 * (K₂ + 2) + 8 ≤ R1 := by rw [hR1, hR2, hR3]; omega
  rintro c₁ hI₁ hA₁ hA₁' ⟨hctx₁, r1, a1, m1⟩
  -- the setup
  have hKc1 := hK.fix hI₁
  have hNW : NFWithin c₁.nmem (c₁.nreg (sw 4)) (c₀.nreg ALLOC) N₂ := by
    rw [hI₁.hin _ (by omega_nf)]
    exact E.hNW₂.transport fun b hb => hI₁.hm b hb
  have hK2m : c₁.nmem (c₁.nreg (sw 4)) = K₂ := hNW.holds.1
  have k2c : c₁.nreg K2 = 2 := hKc1.2.2.2.2.2.1
  have okS : okB W c₁.nmem slSetup c₁.nreg := by
    simp only [slSetup, okB, okI, regI, gRB, gRC, slN, slV, slK, K2, ALLOC, sw, Nat.reduceAdd]
      at hK2m k2c ⊢
    simp only [upd, Nat.reduceEqDiff, ite_true, ite_false, hK2m, k2c]
    refine ⟨iscr_sw (by norm_num) (by norm_num), ⟨iscr_sw (by norm_num) (by norm_num), by omega⟩,
      iscr_sw (by norm_num) (by norm_num), ⟨iscr_sw (by norm_num) (by norm_num), ?_⟩,
      ⟨iscr_sw (by norm_num) (by norm_num), by omega⟩, trivial⟩
    have := hI₁.hw; omega
  refine IRS.seq (K₂ := R2) (IRS.block _ hI₁ okS) ?_
  rintro M1 hIM hAMa hAMb hM1
  have vals : M1.nreg gRB = c₁.nreg ALLOC ∧ M1.nreg gRC = 0 ∧ M1.nreg slN = K₂ ∧
      M1.nreg slV = K₂ + 2 ∧ M1.nreg slK = 0 ∧
      (∀ r, r ≠ gRB → r ≠ gRC → r ≠ slN → r ≠ slV → r ≠ slK → M1.nreg r = c₁.nreg r) ∧
      M1.nmem = c₁.nmem := by
    subst hM1
    simp only [slSetup, gRB, gRC, slN, slV, slK, K2, ALLOC, sw, Nat.reduceAdd] at hK2m k2c ⊢
    simp only [regB, regI, upd, Nat.reduceEqDiff, ite_true, ite_false, hK2m, k2c]
    refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h1 h2 h3 h4 h5 => ?_, trivial⟩
    simp only [h1, h2, h3, h4, h5, ite_false]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := vals
  have hAM : M1.nreg ALLOC = c₁.nreg ALLOC := v6 _ (by omega_nf)
    (by omega_nf) (by omega_nf) (by omega_nf)
    (by omega_nf)
  have hctxM : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) M1 := by
    refine hctx₁.transport (fun r hr => ?_) (fun a _ => by rw [v7]) (by rw [hAM])
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact v6 _ (by omega_nf)
        (by omega_nf)
        (by omega_nf)
        (by omega_nf)
        (by omega_nf)
  -- the raw array
  refine IRS.seq (K₂ := R3) (slAlloc_irs hK hIM v5 (by rw [v4]; omega)) ?_ |>.mono
    (by rw [v4, hR2]) (fun _ h => h)
  rintro c₃ hI₃ hA3a hA3b ⟨a3, k3, r3, m3⟩
  refine IRS.seq (K₂ := R4) (IRS.block [.constN slK 0] hI₃
    ⟨⟨iscr_sw (by omega_nf) (by omega_nf), Nat.zero_le _⟩, trivial⟩) ?_
  rintro c₄ hI₄ hA4a hA4b hc4
  have v4' : ∀ r, r ≠ slK → c₄.nreg r = c₃.nreg r := fun r hr => by
    rw [hc4]; simp only [regB, regI]; exact upd_other _ _ _ hr
  have k4 : c₄.nreg slK = 0 := by rw [hc4]; simp only [regB, regI, upd_same]
  have m4 : c₄.nmem = c₃.nmem := by rw [hc4]
  have r4 : ∀ r, r ≠ slK → r ≠ ALLOC → c₄.nreg r = M1.nreg r := fun r h1 h2 => by
    rw [v4' r h1, r3 r h1 h2]
  have hA4 : c₄.nreg ALLOC = M1.nreg ALLOC + 44 * (K₂ + 2) := by
    rw [v4' _ (by omega_nf), a3, v4]
  have hS4 : SlpInv P J N₂ c M1 0 (fun _ _ _ => False) c₄ := by
    refine ⟨by rw [r4 _ (by omega_nf) (by omega_nf), v1, hAM],
      by rw [hA4]; omega, by rw [r4 _ (by omega_nf) (by omega_nf),
      v2], fun i hi => ?_, fun _ _ _ h => h.elim, fun a _ => by rw [m4, m3],
      ⟨r4 _ (by omega_nf) (by omega_nf),
        r4 _ (by omega_nf) (by omega_nf)⟩,
      fun r h0 h1 h2 => ?_⟩
    · rw [r4 _ (by omega_nf) (by omega_nf), v2] at hi; omega
    · have hS2R : ∀ x, sw 3000 ≤ x → x < sw 6000 → S2R x := fun x a b => Or.inr (Or.inr ⟨a, b⟩)
      rw [r4 r (fun h => h1 (hS2R _ (by subst h; omega_nf) (by subst h; omega_nf))) h2,
        v6 r (fun h => h1 (hS2R _ (by subst h; omega_nf) (by subst h; omega_nf)))
          (fun h => h1 (hS2R _ (by subst h; omega_nf) (by subst h; omega_nf)))
          (fun h => h1 (hS2R _ (by subst h; omega_nf) (by subst h; omega_nf)))
          (fun h => h1 (hS2R _ (by subst h; omega_nf) (by subst h; omega_nf)))
          (fun h => h1 (hS2R _ (by subst h; omega_nf) (by subst h; omega_nf)))]
      exact r1 r (fun h => h1 (by
        unfold MD2W gMD2 gCD2 gTP gTV at h
        rcases h with rfl | rfl | rfl | rfl <;> omega_nf)) h2
  have hK4 : c₄.nreg slK = 0 := k4
  have hN4 : c₄.nreg slN = K₂ := by
    rw [v4' _ (by omega_nf), r3 _ (by omega_nf)
      (by omega_nf), v3]
  -- the shared and top codes
  refine IRS.seq (K₂ := R5) (slCode_irs (kd := 0) (b := 0) hctxM hOc hK hIM hI₄ hS4
    (Or.inl ⟨rfl, rfl⟩) (by norm_num) (by norm_num) (fun h => absurd h (by norm_num)) (by omega)
    (by omega)) ?_
  rintro c₅ hI₅ hA5a hA5b ⟨hS5, k5, n5, -⟩
  refine IRS.seq (K₂ := R6) (slCode_irs (kd := 0) (b := 1) hctxM hOc hK hIM hI₅ hS5
    (Or.inl ⟨rfl, rfl⟩) (by norm_num) (by norm_num) (fun h => absurd h (by norm_num)) (by omega)
    (by omega)) ?_
  rintro c₆ hI₆ hA6a hA6b ⟨hS6, k6, n6, -⟩
  refine IRS.seq (K₂ := R7) (slCode_irs (kd := 2) (b := 0) hctxM hOc hK hIM hI₆ hS6
    (Or.inl ⟨rfl, rfl⟩) (by norm_num) (by norm_num) (fun h => absurd h (by norm_num)) (by omega)
    (by omega)) ?_
  rintro c₇ hI₇ hA7a hA7b ⟨hS7, k7, n7, -⟩
  refine IRS.seq (K₂ := R8) (slCode_irs (kd := 2) (b := 1) hctxM hOc hK hIM hI₇ hS7
    (Or.inl ⟨rfl, rfl⟩) (by norm_num) (by norm_num) (fun h => absurd h (by norm_num)) (by omega)
    (by omega)) ?_
  rintro c₈ hI₈ hA8a hA8b ⟨hS8, k8, n8, -⟩
  have hS8' : SlpInv P J N₂ c M1 4 (slD 0) c₈ := by
    refine hS8.monoD ?_ le_rfl
    rintro kind k b ⟨hb, ⟨h0k, rfl⟩ | ⟨-, hk⟩⟩
    · rcases h0k with rfl | rfl <;> omega <;>
        simp
    · omega
  -- the wall codes
  refine IRS.seq (K₂ := R9) (slKLoop_irs hctxM hOc hK hIM hI₈ hS8'
    (by rw [k8, k7, k6, k5, hK4]) (by rw [n8, n7, n6, n5, hN4]) (by
      have h1 : (7 + 2 * Ko 1 + 2) * N₂.nChords + 2 ≤ R8 := by
        rw [hR8]; exact Nat.le_add_right _ _
      omega)) ?_
  rintro c₉ hI₉ hA₉ hA₉' hS9
  -- the sort
  have hcnt9 : c₉.nreg gRC ≤ 4 * K₂ + 8 := by have := hS9.cnt; omega
  have hsc : κs * (c₉.nreg gRC + 1) * (Nat.clog 2 (c₉.nreg gRC + 1) + 1) ≤ R9 := by
    rw [hR9]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      (by have := Nat.clog_mono_right 2 (show c₉.nreg gRC + 1 ≤ 4 * K₂ + 8 + 1 by omega); omega)
  refine (hSrt sh Bs F X Ok P W c₀ c₉ J N₁ N₂ E hI₉ (fun i hi => ?_)
    (by rw [hS9.rb]; have := hS9.room; omega) (by omega)).mono hsc ?_
  · obtain ⟨hok, hpw, -⟩ := hS9.valid i hi
    rw [hS9.rb]
    exact ⟨hpw, hok.2.2.2.2.1⟩
  rintro c' ⟨O, hO1, hO2, hO3, hO4, hO5, hO6, hO7, hO8, hO9, hO10, hO11, hO12⟩
  rw [hS9.rb] at hO2 hO3 hO5 hO6
  have hval : ∀ i ∈ O, RawV P J N₂ c₉.nmem (M1.nreg ALLOC) i := fun i hi => hS9.valid i (hO1 i hi)
  have hnd : O.Nodup := hO2.imp fun {a b} h hab => by
    subst hab; unfold KLt at h; rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
  have hlen : O.length ≤ 4 * K₂ + 8 := by
    have h1 : O.toFinset ⊆ Finset.range (c₉.nreg gRC) := fun x hx =>
      Finset.mem_range.2 (hO1 x (List.mem_toFinset.1 hx))
    have h2 := Finset.card_le_card h1
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at h2
    omega
  have hget : ∀ i (hi : i < O.length) (f : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ),
      (O.map f).getD i (0, 0, 0, 0, 0) = f (O[i]'hi) := fun i hi f => by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  have hMc : ∀ a, a < c.nreg ALLOC → M1.nmem a = c.nmem a := fun a ha => by
    rw [v7, m1 a ha]
  refine ⟨O.map (rawRec c₉.nmem (M1.nreg ALLOC)), O.map (rawAux c₉.nmem (M1.nreg ALLOC)), by simp [hO4], by simp, hO5, hO6, ?_, ?_, ?_,
    by simpa using hlen, by omega, by simpa using hO8, by omega, by simpa using hO10,
    fun a ha => ?_, fun r h0 h1 h2 => ?_⟩
  · -- the stops
    refine stopsOK_of' (RS := List.range (c₉.nreg gRC)) (rec := rawRec c₉.nmem (M1.nreg ALLOC)) (dc := rawDc c₉.nmem (M1.nreg ALLOC))
      E.hP E.hNF₂ (fun x hx => (hS9.valid x (List.mem_range.1 hx)).1) ?_
      (fun y hy => List.mem_range.2 (hO1 y hy)) hO2
      (fun x hx => by
        obtain ⟨j, hj, hk⟩ := hO3 x (List.mem_range.1 hx)
        exact ⟨j, hj, hk⟩)
    intro e he hsc p t hA hL
    obtain ⟨kind, k, b, hst, hfree, rfl⟩ := stop_complete E.hP E.hNF₂ hsc
    obtain ⟨hk2, hb1, hk1, htop⟩ := hst
    by_cases h1 : kind = 1
    · subst h1
      obtain ⟨i, hi, e1, e2, e3⟩ := hS9.compl 1 k b ⟨hb1, Or.inr ⟨rfl, (hk1 rfl).1⟩⟩
        ⟨⟨hk2, hb1, hk1, htop⟩, hfree⟩ p t hA hL
      exact ⟨i, List.mem_range.2 hi, e1, e2, e3⟩
    · have hso : stOrig J (Qof P) N₂ kind 0 b = stOrig J (Qof P) N₂ kind k b := by
        simp [stOrig, h1]
      have hss : stopSet J (Qof P) N₂ kind 0 b = stopSet J (Qof P) N₂ kind k b := by
        simp [stopSet, h1]
      obtain ⟨i, hi, e1, e2, e3⟩ := hS9.compl kind 0 b
        ⟨hb1, Or.inl ⟨by omega, rfl⟩⟩
        ⟨⟨hk2, hb1, fun h => absurd h h1, htop⟩, by rw [hso]; exact hfree⟩ p t
        (by rw [hss]; exact hA) hL
      exact ⟨i, List.mem_range.2 hi, e1, e2, by rw [e3, hss]⟩
  · -- the word facts
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hok, hpw, -⟩ := hval i hi
    obtain ⟨⟨hk2, hb1, hk1, -⟩, -⟩ := hok
    exact ⟨hpw, hk2, hb1, fun h => (hk1 h).1⟩
  · -- the auxiliary data
    intro i hi
    simp only [List.length_map] at hi
    rw [hget i hi, hget i hi]
    exact (hval _ (List.getElem_mem hi)).2.2
  · rw [hO11 a (by omega), hS9.memM a (by omega), hMc a ha]
  · rw [hO12 r h0 (fun h => h1 ?_) h2, hS9.regs r h0 h1 h2]
    unfold SoR at h; unfold S2R
    rcases h with h | h | h | h
    · exact Or.inl h
    · omega
    · right; right; unfold sw at *; omega
    · right; right; unfold sw at *; omega

end

end SweepEv

end Chazelle.Core
