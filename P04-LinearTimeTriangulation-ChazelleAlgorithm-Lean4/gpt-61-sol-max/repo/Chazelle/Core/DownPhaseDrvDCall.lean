module

public import Chazelle.Core.DownPhaseDrvDGlue
public import Chazelle.Core.DownPhaseDrvRObl
public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase restoration rounds (D8), part 7: the region loop, data and straight-line pieces

The fixed data of the region loop of a round (`REnv`): the current chord list `L` and event
list `E` (normal form `N = buildNF I Q L E` at `H`, interior model `I`), the region
correspondence `reg`, the base `A₀` below which the memory is the initial one `m₀` (context and
descriptor), the round base `B₀` (new triples at `B₀`, buckets at `BK = B₀ + 3 R`), the
splitting step `sF` and its costs.  `RGood` collects the facts at the start of the loop, `RegI`
is the loop invariant (after the regions `< r`: the high regions paired with sound chords
`newL`, their triples at `B₀`, the buckets of their ends at `BK`).

Straight-line pieces: `argS_exec`, `appT_exec`, `stB_exec`.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam

@[expose] public section

/-- **The fixed data of the region loop of a round.** -/
structure REnv where
  P : Polygon
  W : ℕ
  L : List (ℕ × ℕ × ℕ)
  E : List ℕ
  reg : ℕ → Set Point
  A₀ : ℕ
  m₀ : ℕ → ℕ
  B₀ : ℕ
  MD : ℕ
  H : ℕ
  γ : ℕ
  d0 : ℕ
  ctx : ℕ
  sF : Stmt
  κf : ℕ → ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx

namespace REnv

variable (E : REnv)

/-- The geometry polygon. -/
noncomputable abbrev Q : Polygon := Qof E.P

/-- The interior model. -/
noncomputable abbrev M : Model := interiorModel E.Q

/-- The current normal form. -/
noncomputable abbrev N : NF := BuildNF.buildNF E.M E.Q E.L E.E

/-- The number of regions. -/
def R : ℕ := E.L.length + 1

/-- The number of arcs. -/
noncomputable def A : ℕ := E.N.arcs.length

/-- The bucket base. -/
def BK : ℕ := E.B₀ + 3 * E.R

/-- The body bound of the region loop. -/
def Bf : ℕ := Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ + 2 * ((scanK + 2) * (E.d0 + 1)) + 60

end REnv

/-- The registers of `bDownDrv` the region loop keeps. -/
def FixR (q : ℕ) : Prop :=
  (210000 ≤ q ∧ q < 216020) ∨ (216023 ≤ q ∧ q < 216030) ∨ (216060 ≤ q ∧ q < 220000)

/-- **The facts at the start of the region loop.** -/
structure RGood (E : REnv) (c₀ : Config) : Prop where
  hF : Restore.FindOK E.sF E.κf E.F E.G E.Hc E.X DrvR.OkInt DrvR.ioBandsD
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, (∀ a, a < E.A₀ → m a = E.m₀ a) → E.γ ≤ E.X.cap E.P m E.ctx
  hA₀ : E.A₀ ≤ E.B₀
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD E.Q E.M
  hok : ChordTriplesOK E.M E.Q E.L
  hperm : E.E.Perm (List.range (2 * E.L.length))
  hsort : E.E.Pairwise (BuildNF.codeLe E.M E.Q E.L)
  hregs : Restore.NFRegs E.M E.Q E.N E.reg
  hdeg : E.M.DegLe (E.N.F E.M E.Q) E.d0
  hsg : E.M.Semigranular (E.N.F E.M E.Q) E.γ
  hNW : NFWithin c₀.nmem E.H E.B₀ E.N
  hlow : ∀ a, a < E.A₀ → c₀.nmem a = E.m₀ a
  wb : WordsBounded E.W c₀
  r001 : c₀.nreg 210001 = E.MD
  r00 : c₀.nreg 216000 = E.d0
  r01 : c₀.nreg 216001 = E.γ
  r02 : c₀.nreg 216002 = 1
  r03 : c₀.nreg 216003 = 0
  r04 : c₀.nreg 216004 = 4
  r05 : c₀.nreg 216005 = 2
  r06 : c₀.nreg 216006 = 5
  r12 : c₀.nreg 216012 = E.H
  r13 : c₀.nreg 216013 = E.R
  r14 : c₀.nreg 216014 = c₀.nmem (E.H + 4)
  r15 : c₀.nreg 216015 = c₀.nmem (E.H + 5)
  r16 : c₀.nreg 216016 = c₀.nmem (E.H + 7)
  r17 : c₀.nreg 216017 = E.A
  r18 : c₀.nreg 216018 = E.B₀
  r19 : c₀.nreg 216019 = E.BK
  r20 : c₀.nreg 216020 = 0
  r21 : c₀.nreg 216021 = E.B₀
  r22 : c₀.nreg 216022 = E.BK
  r30 : c₀.nreg 216030 = 0
  r31 : c₀.nreg 216031 = c₀.nmem (E.H + 5) + 2
  rctx : c₀.nreg 230001 = E.ctx
  alloc : E.BK + 2 * E.R ≤ c₀.nreg ALLOC
  room : c₀.nreg ALLOC + (E.Bf + 2) * E.R + 2 ≤ E.W

/-- **The region-loop invariant.** -/
structure RegI (E : REnv) (c₀ : Config) (newL : List (ℕ × (ℕ × ℕ × ℕ))) (c : Config) :
    Prop where
  wb : WordsBounded E.W c
  r_le : c.nreg 216030 ≤ E.R
  ptr : c.nreg 216031 = c₀.nmem (E.H + 5) + 2 + 5 * c.nreg 216030
  hfst : newL.map Prod.fst = Restore.highList E.N 4 (c.nreg 216030)
  hgood : ∀ p ∈ newL, Restore.FoundOK E.M E.Q E.N E.reg p.1 p.2
  hbk : BktOK E.M E.Q E.N newL (fun q => c.nmem (E.BK + q))
  cnt : c.nreg 216020 = newL.length
  dst : c.nreg 216021 = E.B₀ + 3 * newL.length
  dstB : c.nreg 216022 = E.BK + 2 * newL.length
  list : ChordListAt c.nmem E.B₀ (newL.map Prod.snd)
  low : ∀ a, a < E.B₀ → c.nmem a = c₀.nmem a
  regs : ∀ q, FixR q → c.nreg q = c₀.nreg q
  rctx : c.nreg 230001 = E.ctx
  alloc : c₀.nreg ALLOC ≤ c.nreg ALLOC
  room : c.nreg ALLOC + (E.Bf + 2) * (E.R - c.nreg 216030) ≤ c₀.nreg ALLOC + (E.Bf + 2) * E.R

/-! ## Straight-line pieces -/

section exec

variable {P : Polygon} {W : ℕ}

theorem argS_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W argS c c' k ∧ k = 7 ∧
      c'.nreg 81000 = c.nreg 210001 ∧ c'.nreg 81001 = c.nreg 216012 ∧
      c'.nreg 81002 = c.nreg 216030 ∧ c'.nreg 81003 = c.nreg 216001 ∧
      c'.nreg 81004 = c.nreg 230001 ∧ c'.nreg 81005 = c.nreg 216000 ∧
      c'.nreg 81006 = c.nreg 216004 ∧
      FrameB (fun r => decide (81000 ≤ r ∧ r ≤ 81006)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W argS c c' k ∧ k = 7 ∧
      (c'.nreg 81000 = c.nreg 210001 ∧ c'.nreg 81001 = c.nreg 216012 ∧
      c'.nreg 81002 = c.nreg 216030 ∧ c'.nreg 81003 = c.nreg 216001 ∧
      c'.nreg 81004 = c.nreg 230001 ∧ c'.nreg 81005 = c.nreg 216000 ∧
      c'.nreg 81006 = c.nreg 216004) := by
    unfold argS
    exec_block
    simp_all
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2, exec_frameB ex (by decide)⟩

/-- The registers `appT` writes. -/
def BappT (r : ℕ) : Bool :=
  decide (r = 216020) || decide (r = 216021) || decide (r = 216033) || decide (r = 216034) ||
    decide (216040 ≤ r ∧ r ≤ 216043) || decide (r = 40000)

theorem wrM_appT : wrM BappT appT = true := by decide

set_option maxHeartbeats 2000000 in
/-- Appending the triple and the region data of the scans. -/
theorem appT_exec (c : Config) (hw : WordsBounded W c) {d n p LB : ℕ}
    (h21 : c.nreg 216021 = d) (h20 : c.nreg 216020 = n) (h02 : c.nreg 216002 = 1)
    (h05 : c.nreg 216005 = 2) (h31 : c.nreg 216031 = p) (h16 : c.nreg 216016 = LB)
    (hd : d + 3 ≤ W) (hn : n + 1 ≤ W) (hp : 2 ≤ p) (hLB : LB + c.nmem (p - 1) ≤ W)
    (hh : c.nreg 81008 + 1 ≤ W) (hsep : p < d) :
    ∃ c' k, Exec P W appT c c' k ∧ k = 15 ∧
      c'.nmem = upd (upd (upd c.nmem d (c.nreg 81008)) (d + 1) (c.nreg 81009)) (d + 2)
        (c.nreg 81010) ∧
      c'.nreg 216021 = d + 3 ∧ c'.nreg 216020 = n + 1 ∧
      c'.nreg 216042 = c.nmem (p - 2) ∧ c'.nreg 216043 = LB + c.nmem (p - 1) ∧
      c'.nreg 216041 = c.nreg 81008 + 1 ∧ c'.nreg 40000 = c.nreg 210001 ∧
      c'.nreg 216040 = c.nreg 81009 ∧ FrameM BappT c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W appT c c' k ∧ k = 15 ∧
      (c'.nmem = upd (upd (upd c.nmem d (c.nreg 81008)) (d + 1) (c.nreg 81009)) (d + 2)
        (c.nreg 81010) ∧
      c'.nreg 216021 = d + 3 ∧ c'.nreg 216020 = n + 1 ∧
      c'.nreg 216042 = c.nmem (p - 2) ∧ c'.nreg 216043 = LB + c.nmem (p - 1) ∧
      c'.nreg 216041 = c.nreg 81008 + 1 ∧ c'.nreg 40000 = c.nreg 210001 ∧
      c'.nreg 216040 = c.nreg 81009) := by
    unfold appT
    exec_block
    all_goals try (config_simp; omega)
    · config_simp
      simp only [h21, h02, h05, h31, h16, Machine.upd_apply]
      split_ifs <;> first | omega | (rw [show p - 2 + 1 = p - 1 by omega]; exact hLB)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals config_simp
    all_goals try simp only [h21, h20, h02, h05, h31, h16]
    all_goals try simp only [Machine.upd_apply]
    all_goals try split_ifs
    all_goals first | omega | rfl | (congr 2; omega)
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2, exec_frameM ex wrM_appT⟩

theorem wrM_stB : wrM (fun r => decide (r = 216022)) stB = true := by decide

/-- Storing a bucket. -/
theorem stB_exec (c : Config) (hw : WordsBounded W c) {d : ℕ} (h22 : c.nreg 216022 = d)
    (h02 : c.nreg 216002 = 1) (hd : d + 1 ≤ W) :
    ∃ c' k, Exec P W stB c c' k ∧ k = 2 ∧ c'.nmem = upd c.nmem d (c.nreg 216053) ∧
      c'.nreg 216022 = d + 1 ∧ FrameM (fun r => decide (r = 216022)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W stB c c' k ∧ k = 2 ∧
      (c'.nmem = upd c.nmem d (c.nreg 216053) ∧ c'.nreg 216022 = d + 1) := by
    unfold stB
    exec_block
    all_goals simp_all
  exact ⟨c', k, ex, hk, q.1, q.2, exec_frameM ex wrM_stB⟩

end exec

end

end DrvD

end Chazelle.Core
