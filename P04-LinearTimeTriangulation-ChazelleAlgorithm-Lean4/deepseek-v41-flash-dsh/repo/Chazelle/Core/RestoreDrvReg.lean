module

public import Chazelle.Core.RestoreDrvCopy

/-!
# WP-E, part 8: the restoration driver — the region loop

`regS sF` visits the regions `r = 0 … R - 1` of the current normal form; for every region with
more than `D` exit chords (the length of its chord list, `Gran.deg_region`) it calls the splitting
step `sF` (`FindOK`) and appends the returned chord triple to the list at `LB`.  By completeness
of `sF` (the full augmented maps have degree `≤ D`) every such region receives a chord.

`reg_exec`: after the loop the list at `LB` is `oldL N ++ newL.map Prod.snd`, where `newL` pairs
the high regions (in increasing order) with their chords, each sound (`FoundOK`).
-/

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs
open Chazelle.Chain (regionsIn)

@[expose] public section

/-- The chord triples of a normal form, in order. -/
def oldL (N : NF) : List (ℕ × ℕ × ℕ) := N.chords.map fun x => (x.h, x.lp, x.rp)

/-- The degree of region `r` as stored. -/
def degOf (N : NF) (r : ℕ) : ℕ := (N.region r).chords.length

/-- The regions below `r` with more than `D` exit chords. -/
def highList (N : NF) (D r : ℕ) : List ℕ := (List.range r).filter fun r' => D < degOf N r'

theorem highList_succ (N : NF) (D r : ℕ) :
    highList N D (r + 1) = highList N D r ++ (if D < degOf N r then [r] else []) := by
  unfold highList
  Ξ List.range_succ, List.filter_append
  congr 1
  by_cases h : D < degOf N r <;> Θ h

theorem highList_length_le (N : NF) (D r : ℕ) : (highList N D r).length ≤ r := by
  unfold highList
  exact (List.length_filter_le _ _).trans (✓)

/-- A chord triple found for region `r`: attached, at a vertex height, admissible, splitting the
region well. -/
def FoundOK (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) (r : ℕ)
    (t : ℕ × ℕ × ℕ) : Prop :=
  (recOf t).Attached M Q ∧ t.1 < Q.n ∧ (recOf t).toSet M Q ∈ M.Adm ∧
    SplitsWell M (N.F M Q) (reg r) ((recOf t).toSet M Q)

/-- The memory context has a local capacity. -/
abbrev CapLocal (X : MemCtx) : Prop := X.CapLocal

/-- The cost of one call of the splitting step. -/
def costF (κf F G Hc : ℕ → ℕ) (dcap γ : ℕ) : ℕ :=
  κf dcap * F γ * G γ * (Hc γ + Nat.clog 2 γ + 1)

/-- The fixed data of the region loop. -/
structure RegEnv where
  P : Polygon
  W : ℕ
  M : Model
  N : NF
  reg : ℕ → Set Point
  A₀ : ℕ
  m₀ : ℕ → ℕ
  LB : ℕ
  H : ℕ
  MD : ℕ
  D : ℕ
  γ : ℕ
  ctx : ℕ
  dcap : ℕ
  sF : Stmt
  κf : ℕ → ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx
  Ok : Polygon → Model → Prop

namespace RegEnv

variable (E : RegEnv)

/-- The number of chords. -/
def K : ℕ := E.N.nChords

/-- The number of regions. -/
def R : ℕ := E.N.nRegions

/-- The chord family. -/
def S : Set (Set Point) := E.N.F E.M (Qof E.P)

/-- The body bound of the region loop. -/
def Bf : ℕ := costF E.κf E.F E.G E.Hc E.dcap E.γ + 20

end RegEnv

/-- **Host regularity of a descriptor** survives a change of the memory at or above the bound of
a well-formed descriptor (G10/G11). -/
theorem hregKeep {P : Polygon} {m m' : ℕ → ℕ} {D E : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D (Qof P) M)
    (h : m D = 0 → ∀ H C, ChainDescAt m (D + 1) (Qof P) H C → HostRegular (Qof P).n H)
    (he : ∀ a, a < E → m' a = m a) :
    m' D = 0 → ∀ H C, ChainDescAt m' (D + 1) (Qof P) H C → HostRegular (Qof P).n H := by
  intro h0 H C hC
  have hD := hwf.1
  have h0' : m D = 0 := by rw [← he D (⋄)]; exact h0
  rcases hMD with ⟨-, H₀, C₀, hC₀, -⟩ | ⟨h1, -, -⟩
  · obtain ⟨-, -, hEb, -⟩ := (hwf.2 h0').2 H₀ C₀ hC₀
    have hH : HostAt m' (m (D + 1)) H₀ := Gran.hostAt_agree' hC₀.1 hEb he
    have e1 : m' (D + 1) = m (D + 1) := he _ (⋄)
    have : H = H₀ := NFLoc.hostAt_unique (by rw [← e1]; exact hC.1) hH
    subst this
    exact h h0' H C₀ hC₀
  · Ξ' h0' at h1; exact absurd h1 (⊛)

/-- A chain descriptor's polygon stays simple when the memory changes above its bound. -/
theorem simpKeep {P : Polygon} {m m' : ℕ → ℕ} {D E : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D (Qof P) M)
    (h : m D = 0 → ∀ H C, ChainDescAt m (D + 1) (Qof P) H C → C.P.Simple)
    (he : ∀ a, a < E → m' a = m a) :
    m' D = 0 → ∀ H C, ChainDescAt m' (D + 1) (Qof P) H C → C.P.Simple := by
  intro h0 H C hC
  have hD := hwf.1
  have h0' : m D = 0 := by rw [← he D (⋄)]; exact h0
  rcases hMD with ⟨-, H₀, C₀, hC₀, -⟩ | ⟨h1, -, -⟩
  · obtain ⟨-, -, hEb, -⟩ := (hwf.2 h0').2 H₀ C₀ hC₀
    have hH : HostAt m' (m (D + 1)) H₀ := Gran.hostAt_agree' hC₀.1 hEb he
    have e1 : m' (D + 1) = m (D + 1) := he _ (⋄)
    have hHH : H = H₀ := NFLoc.hostAt_unique (by rw [← e1]; exact hC.1) hH
    have hPP : C.P = C₀.P := Ρ hC.2.1, hC₀.2.1, hHH
    rw [hPP]; exact h h0' H₀ C₀ hC₀
  · Ξ' h0' at h1; exact absurd h1 (⊛)

/-- The facts about the region-loop data and the configuration `c₀` at the start of the loop. -/
structure RegGood (E : RegEnv) (c₀ : Config) : Prop where
  hF : FindOK E.sF E.κf E.F E.G E.Hc E.X E.Ok oracleBands
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, (∀ a, a < E.A₀ → m a = E.m₀ a) → E.γ ≤ E.X.cap E.P m E.ctx
  hA₀ : E.A₀ ≤ E.LB
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD (Qof E.P) E.M
  hreg : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H C →
    HostRegular (Qof E.P).n H
  hsimp : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H C → C.P.Simple
  hGM : GoodModel E.M
  hOk : E.Ok E.P E.M
  hfull : E.M.FullDegLe (Qof E.P) E.D
  hNW : NFWithin c₀.nmem E.H E.LB E.N
  hNF : IsNF E.M (Qof E.P) E.N
  hregs : NFRegs E.M (Qof E.P) E.N E.reg
  hdeg : E.M.DegLe E.S E.dcap
  hsg : E.M.Semigranular E.S E.γ
  hlow : ∀ a, a < E.A₀ → c₀.nmem a = E.m₀ a
  wb : WordsBounded E.W c₀
  r00 : c₀.nreg 80000 = E.MD
  r03 : c₀.nreg 80003 = E.D
  r04 : c₀.nreg 80004 = E.γ
  r06 : c₀.nreg 80006 = E.ctx
  r12 : c₀.nreg 80012 = E.H
  r14 : c₀.nreg 80014 = E.R
  r19 : c₀.nreg 80019 = E.dcap
  r20 : c₀.nreg 80020 = 1
  r23 : c₀.nreg 80023 = 5
  r24 : c₀.nreg 80024 = 0
  r40 : c₀.nreg 80040 = 0
  r41 : c₀.nreg 80041 = c₀.nmem (E.H + 5) + 2
  r18 : c₀.nreg 80018 = E.K
  r43 : c₀.nreg 80043 = E.LB + 3 * E.K
  alloc : E.LB + 3 * (E.K + E.R) ≤ c₀.nreg ALLOC
  list : ChordListAt c₀.nmem E.LB (oldL E.N)
  room : c₀.nreg ALLOC + (E.Bf + 2) * E.R + 2 ≤ E.W

/-- The region-loop invariant. -/
structure RegI (E : RegEnv) (c₀ : Config) (newL : List (ℕ × (ℕ × ℕ × ℕ))) (c : Config) :
    Prop where
  wb : WordsBounded E.W c
  r_le : c.nreg 80040 ≤ E.R
  ptr : c.nreg 80041 = c₀.nmem (E.H + 5) + 2 + 5 * c.nreg 80040
  hfst : newL.map Prod.fst = highList E.N E.D (c.nreg 80040)
  hgood : ∀ p ∈ newL, FoundOK E.M (Qof E.P) E.N E.reg p.1 p.2
  cnt : c.nreg 80018 = E.K + newL.length
  dst : c.nreg 80043 = E.LB + 3 * (E.K + newL.length)
  list : ChordListAt c.nmem E.LB (oldL E.N ++ newL.map Prod.snd)
  low : ∀ a, a < E.LB → c.nmem a = c₀.nmem a
  regs : ∀ q, 80000 ≤ q → q < 81000 → q ≠ 80040 → q ≠ 80041 → q ≠ 80042 → q ≠ 80018 →
    q ≠ 80043 → c.nreg q = c₀.nreg q
  alloc : c₀.nreg ALLOC ≤ c.nreg ALLOC
  room : c.nreg ALLOC + (E.Bf + 2) * (E.R - c.nreg 80040) ≤ c₀.nreg ALLOC + (E.Bf + 2) * E.R

/-! ## Straight-line pieces -/

theorem load42_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W (block [.loadN 80042 80041]) c c' k ∧ k = 1 ∧
      c'.nreg 80042 = c.nmem (c.nreg 80041) ∧ (∀ r, r ≠ 80042 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other]

theorem argS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W argS c c' k ∧ k = 7 ∧
      c'.nreg 81000 = c.nreg 80000 ∧ c'.nreg 81001 = c.nreg 80012 ∧
      c'.nreg 81002 = c.nreg 80040 ∧ c'.nreg 81003 = c.nreg 80004 ∧
      c'.nreg 81004 = c.nreg 80006 ∧ c'.nreg 81005 = c.nreg 80019 ∧
      c'.nreg 81006 = c.nreg 80003 ∧
      (∀ r, (r < 81000 ∨ 81007 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold argS
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

theorem appS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {d : ℕ}
    (h43 : c.nreg 80043 = d) (h20 : c.nreg 80020 = 1) (hd : d + 3 ≤ W)
    (hn : c.nreg 80018 + 1 ≤ W) :
    ∃ c' k, Exec P W appS c c' k ∧ k = 7 ∧ c'.nreg 80043 = d + 3 ∧
      c'.nreg 80018 = c.nreg 80018 + 1 ∧
      c'.nmem = upd (upd (upd c.nmem d (c.nreg 81008)) (d + 1) (c.nreg 81009)) (d + 2)
        (c.nreg 81010) ∧
      (∀ r, r ≠ 80043 → r ≠ 80018 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold appS
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h43, h20]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl⟩ <;>
    simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h43, h20]

theorem tail_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h1 : c.nreg 80041 + c.nreg 80023 ≤ W) (h2 : c.nreg 80040 + c.nreg 80020 ≤ W) :
    ∃ c' k, Exec P W (block [.addN 80041 80041 80023, .addN 80040 80040 80020]) c c' k ∧
      k = 2 ∧ c'.nreg 80041 = c.nreg 80041 + c.nreg 80023 ∧
      c'.nreg 80040 = c.nreg 80040 + c.nreg 80020 ∧
      (∀ r, r ≠ 80041 → r ≠ 80040 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  · exact h1
  · simp (disch := omega) only [Machine.upd_other]; exact h2
  · refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

/-! ## The call of the splitting step -/

/-- The memory of the loop agrees with the initial memory below `A₀`. -/
theorem RegI.agree {E : RegEnv} {c₀ c : Config} {newL : List (ℕ × (ℕ × ℕ × ℕ))}
    (hE : RegGood E c₀) (hI : RegI E c₀ newL c) : ∀ a, a < E.A₀ → c.nmem a = E.m₀ a :=
  fun a ha => (hI.low a (lt_of_lt_of_le ha hE.hA₀)).trans (hE.hlow a ha)

theorem RegI.nfWithin {E : RegEnv} {c₀ c : Config} {newL : List (ℕ × (ℕ × ℕ × ℕ))}
    (hE : RegGood E c₀) (hI : RegI E c₀ newL c) {A : ℕ} (hA : E.LB ≤ A) :
    NFWithin c.nmem E.H A E.N :=
  (hE.hNW.transport hI.low).mono hA

theorem RegGood.lb_le {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀) :
    E.LB ≤ c₀.nreg ALLOC := by have := hE.alloc; omega

/-- The degree word of region `r`. -/
theorem RegI.deg_word {E : RegEnv} {c₀ c : Config} {newL : List (ℕ × (ℕ × ℕ × ℕ))}
    (hE : RegGood E c₀) (hI : RegI E c₀ newL c) (hr : c.nreg 80040 < E.R) :
    c.nmem (c.nreg 80041) = degOf E.N (c.nreg 80040) := by
  have hNWc : NFWithin c.nmem E.H E.LB E.N := hI.nfWithin hE le_rfl
  have hareas := Gran.nf_areas hNWc
  have h5 : c.nmem (E.H + 5) = c₀.nmem (E.H + 5) := hI.low _ (⋄)
  have hreg := (hNWc.nfAt.2.2.2.2.2.2.2.1 (c.nreg 80040) hr).2.1
  Ξ hI.ptr, ← h5
  unfold degOf
  Ξ ← hreg
  congr 1
  ring

set_option maxHeartbeats 4000000 in
/-- **One call of the splitting step** on a region with more than `D` exit chords: a sound chord
is appended to the list. -/
theorem call_step {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀)
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 80040 < E.R) (hhigh : E.D < degOf E.N (c.nreg 80040)) :
    ∃ c' k t, Exec E.P E.W (callS E.sF) c c' k ∧ k ≤ costF E.κf E.F E.G E.Hc E.dcap E.γ + 16 ∧
      RF dBands E.A₀ c c' k ∧ WordsBounded E.W c' ∧
      FoundOK E.M (Qof E.P) E.N E.reg (c.nreg 80040) t ∧
      c'.nreg 80018 = c.nreg 80018 + 1 ∧ c'.nreg 80043 = c.nreg 80043 + 3 ∧
      ChordListAt c'.nmem E.LB (oldL E.N ++ newL.map Prod.snd ++ [t]) ∧
      (∀ a, a < E.LB → c'.nmem a = c.nmem a) ∧
      (∀ q, 80000 ≤ q → q < 81000 → q ≠ 80018 → q ≠ 80043 → c'.nreg q = c.nreg q) := by
  obtain ⟨hF, hG, hWh, hX, hcap, hA₀, hwf, hMD, hreg, hsimp, hGM, hOk, hfull, hNW, hNF, hregs, hdeg, hsg,
    hlow, wb₀, r00, r03, r04, r06, r12, r14, r19, r20, r23, r24, r40, r41, r18, r43, halloc,
    hlist₀, hroom₀⟩ := hE
  have hE' : RegGood E c₀ := ⟨hF, hG, hWh, hX, hcap, hA₀, hwf, hMD, hreg, hsimp, hGM, hOk, hfull, hNW, hNF,
    hregs, hdeg, hsg, hlow, wb₀, r00, r03, r04, r06, r12, r14, r19, r20, r23, r24, r40, r41, r18,
    r43, halloc, hlist₀, hroom₀⟩
  set r := c.nreg 80040 with hrdef
  have reg8 : ∀ q, 80000 ≤ q → q < 81000 → q ≠ 80040 → q ≠ 80041 → q ≠ 80042 → q ≠ 80018 →
      q ≠ 80043 → c.nreg q = c₀.nreg q := hI.regs
  have c00 : c.nreg 80000 = E.MD := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r00]
  have c03 : c.nreg 80003 = E.D := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r03]
  have c04 : c.nreg 80004 = E.γ := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r04]
  have c06 : c.nreg 80006 = E.ctx := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r06]
  have c12 : c.nreg 80012 = E.H := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r12]
  have c19 : c.nreg 80019 = E.dcap := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r19]
  have c20 : c.nreg 80020 = 1 := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r20]
  have c24 : c.nreg 80024 = 0 := by
    rw [reg8 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r24]
  have hagree := hI.agree hE'
  have hA0c : E.A₀ ≤ c.nreg ALLOC := by have := hI.alloc; have := hE'.lb_le; omega
  have hLBc : E.LB ≤ c.nreg ALLOC := by have := hI.alloc; have := hE'.lb_le; omega
  -- arguments
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, a3, a4, a5, a6, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    argS_exec (P := E.P) c hI.wb
  have w₁ := e₁.wb_right
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := R₁ _ (by left; decide)
  have hag₁ : ∀ a, a < E.A₀ → c₁.nmem a = E.m₀ a := fun a ha => by rw [m₁, hagree a ha]
  obtain ⟨hMD₁, hwf₁⟩ := Gran.desc_agree' hwf hMD hag₁
  have hNW₁ : NFWithin c₁.nmem E.H (c₁.nreg ALLOC) E.N := by
    rw [m₁, A₁]; exact hI.nfWithin hE' hLBc
  have hR : E.R = E.N.nRegions := rfl
  -- the precondition of the splitting step
  have pre : GoodEnv E.P ∧ hostWords E.P.n ≤ E.W ∧
      E.X.holds E.P c₁.nmem (c₁.nreg 81004) (c₁.nreg ALLOC) ∧
      c₁.nreg 81003 ≤ E.X.cap E.P c₁.nmem (c₁.nreg 81004) ∧
      ModelDescWF E.P (c₁.nreg ALLOC) c₁.nmem (c₁.nreg 81000) ∧
      (c₁.nmem (c₁.nreg 81000) = 0 → ∀ H C, ChainDescAt c₁.nmem (c₁.nreg 81000 + 1) (Qof E.P) H C →
        HostRegular (Qof E.P).n H) ∧
      (c₁.nmem (c₁.nreg 81000) = 0 → ∀ H C, ChainDescAt c₁.nmem (c₁.nreg 81000 + 1) (Qof E.P) H C →
        C.P.Simple) ∧
      ∃ M N, ModelDescAt c₁.nmem (c₁.nreg 81000) (Qof E.P) M ∧ GoodModel M ∧ E.Ok E.P M ∧
        NFWithin c₁.nmem (c₁.nreg 81001) (c₁.nreg ALLOC) N ∧ IsNF M (Qof E.P) N ∧
        M.DegLe (N.F M (Qof E.P)) (c₁.nreg 81005) ∧
        M.Semigranular (N.F M (Qof E.P)) (c₁.nreg 81003) ∧ c₁.nreg 81002 < N.nRegions := by
    rw [a0, a1, a2, a3, a4, a5, c00, c12, c04, c06, c19]
    refine ⟨hG, hWh, ?_, hcap _ hag₁, hwf₁.mono (by rw [A₁]; exact hA0c),
      hregKeep hwf hMD hreg hag₁, simpKeep hwf hMD hsimp hag₁, E.M, E.N, hMD₁, hGM,
      hOk, hNW₁, hNF, hdeg, hsg, by rw [← hR]; exact hr⟩
    exact E.X.mono _ _ _ _ _ (by rw [A₁]; exact hA0c)
      (E.X.local_ _ _ _ _ _ (fun a ha => (hag₁ a ha).symm) hX)
  have hcostle : costF E.κf E.F E.G E.Hc E.dcap E.γ + 20 = E.Bf := rfl
  have hroomF : c₁.nreg ALLOC + E.κf (c₁.nreg 81005) * E.F (c₁.nreg 81003) *
      E.G (c₁.nreg 81003) * (E.Hc (c₁.nreg 81003) + Nat.clog 2 (c₁.nreg 81003) + 1) ≤ E.W := by
    rw [a5, a3, c19, c04, A₁]
    have h1 := hI.room
    have h2 : (E.Bf + 2) * 1 ≤ (E.Bf + 2) * (E.R - r) := Nat.mul_le_mul_left _ (by omega)
    unfold costF at hcostle
    have := hroom₀
    nlinarith
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨P₂8, P₂fl, P₂⟩, F₂⟩ := hF E.P E.W c₁ w₁ pre hroomF
  beta_reduce at hk₂
  rw [a5, a3, c19, c04] at hk₂
  have w₂ := e₂.wb_right
  -- the flag is `1` and the chord is sound
  have hNAt₁ : NFAt c₁.nmem (c₁.nreg 81001) E.N := by rw [a1, c12]; exact hNW₁.nfAt
  have hMD₁' : ModelDescAt c₁.nmem (c₁.nreg 81000) (Qof E.P) E.M := by rw [a0, c00]; exact hMD₁
  obtain ⟨hsnd, hcpl⟩ := P₂ E.M E.N E.reg hMD₁' hNAt₁ hNF hregs
  obtain ⟨hRC, -, -, hRO⟩ := hregs
  have hdegr : E.M.deg (E.N.F E.M (Qof E.P)) (E.reg r) = degOf E.N r :=
    Gran.deg_region hNF hRC hRO (by rw [← hR]; exact hr)
  have hflag : c₂.nreg 81007 = 1 := hcpl (by rw [a6, c03]; exact hfull)
    (by rw [a6, c03, a2, hdegr]; exact hhigh)
  obtain ⟨s1, s2, s3, s4⟩ := hsnd hflag
  rw [a2] at s4
  set t : ℕ × ℕ × ℕ := (c₂.nreg 81008, c₂.nreg 81009, c₂.nreg 81010) with htdef
  have hgood : FoundOK E.M (Qof E.P) E.N E.reg r t := ⟨s1, s2, s3, s4⟩
  -- append
  have d43 : c₂.nreg 80043 = E.LB + 3 * (E.K + newL.length) := by
    rw [P₂8 _ (band8 (by omega) (by omega)) (by omega), R₁ _ (by left; decide), hI.dst]
  have d20 : c₂.nreg 80020 = 1 := by
    rw [P₂8 _ (band8 (by omega) (by omega)) (by omega), R₁ _ (by left; decide), c20]
  have d18 : c₂.nreg 80018 = E.K + newL.length := by
    rw [P₂8 _ (band8 (by omega) (by omega)) (by omega), R₁ _ (by left; decide), hI.cnt]
  have hlen : newL.length ≤ r := by
    have := congrArg List.length hI.hfst
    rw [List.length_map] at this
    rw [this]; exact highList_length_le _ _ _
  have hA₂ : c₁.nreg ALLOC ≤ c₂.nreg ALLOC := F₂.2.2.2.2.2.1
  have hdA : E.LB + 3 * (E.K + newL.length) + 3 ≤ c₁.nreg ALLOC := by
    rw [A₁]; have := hI.alloc; omega
  have hWW : c₂.nreg ALLOC ≤ E.W := w₂.1 _
  obtain ⟨c₃, k₃, e₃, hk₃, t43, t18, m₃, R₃, rr₃, rm₃, o₃⟩ := appS_exec (P := E.P) c₂ w₂ d43 d20
    (by omega) (by have := w₂.1 80018; omega)
  have f24 : c₂.nreg 80024 = 0 := by
    rw [P₂8 _ (band8 (by omega) (by omega)) (by omega), R₁ _ (Or.inl (by decide)), c24]
  have e₂₃ : Exec E.P E.W (.ifLtN 80024 81007 appS .skip) c₂ c₃ (k₃ + 1) :=
    .ifLtN_true (by rw [f24, hflag]; omega) e₃
  -- memory facts
  have hm₂low : ∀ a, a < c₁.nreg ALLOC → c₂.nmem a = c₁.nmem a := F₂.2.2.1
  have hmem : ∀ a, a < E.LB + 3 * (E.K + newL.length) → c₃.nmem a = c.nmem a := by
    intro a ha
    rw [m₃, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), hm₂low a (by omega), m₁]
  refine ⟨c₃, k₁ + (k₂ + (k₃ + 1)), t, .seq e₁ (.seq e₂ e₂₃), ?_, ?_, e₃.wb_right, hgood,
    ?_, ?_, ?_, fun a ha => hmem a (by omega), fun q q1 q2 q3 q4 => ?_⟩
  · unfold costF; omega
  · -- the frame
    have RF₁ : RF dBands E.A₀ c c₁ k₁ := rf_of_regs (fun q hq => R₁ q (by
      rcases hq with hq | hq <;> [left; right] <;> omega)) rr₁ m₁ rm₁ o₁
    have RF₂ : RF dBands E.A₀ c₁ c₂ k₂ := RF.of_frame F₂ (by rw [A₁]; exact hA0c)
    have RF₃ : RF dBands E.A₀ c₂ c₃ (k₃ + 1) := by
      have hA₃ : c₃.nreg ALLOC = c₂.nreg ALLOC := R₃ _ (by decide) (by decide)
      have b43 : bandOf 80043 ∈ dBands := by rw [band8 (by norm_num) (by norm_num)]; exact mem_dBands_8
      have b18 : bandOf 80018 ∈ dBands := by rw [band8 (by norm_num) (by norm_num)]; exact mem_dBands_8
      refine ⟨fun q hq _ => R₃ q (fun h => hq (h ▸ b43)) (fun h => hq (h ▸ b18)),
        fun q _ => by rw [rr₃], fun a ha => ?_, fun a _ => by rw [rm₃], o₃, by omega, by omega⟩
      · have : a < E.LB := lt_of_lt_of_le ha hA₀
        rw [m₃, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
          Machine.upd_other _ _ _ (by omega)]
    exact (RF₁.trans (RF₂.trans RF₃))
  · rw [t18, d18, hI.cnt]
  · rw [t43, hI.dst]
  · -- the list
    have hl := hI.list
    have hlen' : (oldL E.N ++ newL.map Prod.snd).length = E.K + newL.length := by
      simp [oldL, RegEnv.K, NF.nChords]
    refine Gran.ChordListAt.snoc hl (fun a a1 a2 => ?_) ?_ ?_ ?_
    · rw [hlen'] at a2; exact hmem a a2
    · rw [hlen', m₃, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_same]
    · rw [hlen', m₃, Machine.upd_other _ _ _ (by omega), Machine.upd_same]
    · rw [hlen', m₃, Machine.upd_same]
  · rw [R₃ q q4 q3, P₂8 q (band8 q1 (by omega)) q2, R₁ q (by left; exact q2)]

/-! ## One region, and the loop -/


/-- **One step of the region loop.** -/
theorem regBody_step {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀)
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 80040 < E.R) :
    ∃ c' k newL', Exec E.P E.W (regBody E.sF) c c' k ∧ RegI E c₀ newL' c' ∧
      RF dBands E.A₀ c c' k ∧ k ≤ E.Bf ∧ c'.nreg 80040 = c.nreg 80040 + 1 := by
  have reg8 := hI.regs
  have c03 : c.nreg 80003 = E.D := by
    rw [reg8 _ (⋄) (⋄) (⋄) (⋄) (⋄) (⋄) (⋄),
      hE.r03]
  have c20 : c.nreg 80020 = 1 := by
    rw [reg8 _ (⋄) (⋄) (⋄) (⋄) (⋄) (⋄) (⋄),
      hE.r20]
  have c23 : c.nreg 80023 = 5 := by
    rw [reg8 _ (⋄) (⋄) (⋄) (⋄) (⋄) (⋄) (⋄),
      hE.r23]
  have hdw := hI.deg_word hE hr
  obtain ⟨r, hrdef⟩ : ∃ r, c.nreg 80040 = r := ⟨_, rfl⟩
  Ξ' hrdef at hr hdw
  obtain ⟨c₁, k₁, e₁, hk₁, l42, R₁, rr₁, m₁, rm₁, o₁⟩ := load42_exec (P := E.P) c hI.wb
  Ξ' hdw at l42
  have w₁ := e₁.wb_right
  have hroom₁ : c₁.nreg ALLOC + (E.Bf + 2) * (E.R - c₁.nreg 80040) ≤
      c₀.nreg ALLOC + (E.Bf + 2) * E.R := by
    rw [R₁ _ (⌖), R₁ _ (⌖)]; exact hI.room
  have hI₁ : RegI E c₀ newL c₁ := ⟨w₁, by rw [R₁ _ (⌖)]; exact hI.r_le,
    by rw [R₁ _ (⌖), R₁ _ (⌖)]; exact hI.ptr,
    by rw [R₁ _ (⌖)]; exact hI.hfst, hI.hgood, by rw [R₁ _ (⌖)]; exact hI.cnt,
    by rw [R₁ _ (⌖)]; exact hI.dst, by rw [m₁]; exact hI.list,
    fun a ha => by rw [m₁]; exact hI.low a ha,
    fun q q1 q2 q3 q4 q5 q6 q7 => by rw [R₁ q q5]; exact hI.regs q q1 q2 q3 q4 q5 q6 q7,
    by rw [R₁ _ (⌖)]; exact hI.alloc, hroom₁⟩
  have RF₁ : RF dBands E.A₀ c c₁ k₁ := rf_of_regs (fun q hq => R₁ q (⋄)) rr₁ m₁ rm₁ o₁
  have r1 : c₁.nreg 80040 = r := Ρ R₁ _ (⌖), hrdef
  -- the conditional call
  obtain ⟨c₂, k₂, newL', e₂, hk₂, RF₂, w₂, hfst₂, hgood₂, cnt₂, dst₂, list₂, low₂, reg₂⟩ :
      ∃ (c₂ : Config) (k₂ : ℕ) (newL' : List (ℕ × (ℕ × ℕ × ℕ))),
      Exec E.P E.W (.ifLtN 80003 80042 (callS E.sF) .skip) c₁ c₂ k₂ ∧
      k₂ ≤ costF E.κf E.F E.G E.Hc E.dcap E.γ + 17 ∧ RF dBands E.A₀ c₁ c₂ k₂ ∧
      WordsBounded E.W c₂ ∧ newL'.map Prod.fst = highList E.N E.D (r + 1) ∧
      (∀ p ∈ newL', FoundOK E.M (Qof E.P) E.N E.reg p.1 p.2) ∧
      c₂.nreg 80018 = E.K + newL'.length ∧ c₂.nreg 80043 = E.LB + 3 * (E.K + newL'.length) ∧
      ChordListAt c₂.nmem E.LB (oldL E.N ++ newL'.map Prod.snd) ∧
      (∀ a, a < E.LB → c₂.nmem a = c₁.nmem a) ∧
      (∀ q, 80000 ≤ q → q < 81000 → q ≠ 80018 → q ≠ 80043 → c₂.nreg q = c₁.nreg q) := by
    by_cases hhigh : E.D < degOf E.N r
    · obtain ⟨c₂, k₂, t, e₂, hk₂, RF₂, w₂, hgood, t18, t43, tlist, tlow, treg⟩ :=
        call_step hE hI₁ (by rw [r1]; exact hr) (by rw [r1]; exact hhigh)
      Ξ' r1 at hgood
      refine ⟨c₂, k₂ + 1, newL ++ [(r, t)],
        .ifLtN_true (by rw [R₁ _ (⌖), c03, l42]; exact hhigh) e₂, ⋄,
        RF₂.mono subset_rfl (⋄), w₂, ?_, ?_, ?_, ?_, ?_, tlow, treg⟩
      · rw [List.map_append, hI.hfst, hrdef, highList_succ, ite_eq_left hhigh]; rfl
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hI.hgood p hp
        · ϴ' List.mem_singleton at hp; subst hp; exact hgood
      · rw [t18, hI₁.cnt, List.length_append, List.length_singleton]; ring
      · rw [t43, hI₁.dst, List.length_append, List.length_singleton]; ring
      · rw [List.map_append, ← List.append_assoc]; exact tlist
    · refine ⟨c₁, 2, newL, .ifLtN_false (by rw [R₁ _ (⌖), c03, l42]; exact hhigh)
        (.skip w₁), ⋄, RF.refl _ _, w₁, ?_, hI.hgood, hI₁.cnt, hI₁.dst, hI₁.list,
        fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
      Ξ hI.hfst, hrdef, highList_succ, ite_eq_right hhigh, List.append_nil
  -- the tail
  have k40 : c₂.nreg 80040 = r := Ρ reg₂ _ (⋄) (⋄) (⋄) (⋄), r1
  have k41 : c₂.nreg 80041 = c₀.nmem (E.H + 5) + 2 + 5 * r := by
    Ξ reg₂ _ (⋄) (⋄) (⋄) (⋄), hI₁.ptr, r1
  have k20 : c₂.nreg 80020 = 1 := by
    rw [reg₂ _ (⋄) (⋄) (⋄) (⋄),
      hI₁.regs _ (⋄) (⋄) (⋄) (⋄) (⋄) (⋄) (⋄),
      hE.r20]
  have k23 : c₂.nreg 80023 = 5 := by
    rw [reg₂ _ (⋄) (⋄) (⋄) (⋄),
      hI₁.regs _ (⋄) (⋄) (⋄) (⋄) (⋄) (⋄) (⋄),
      hE.r23]
  -- the pointer stays below the allocator
  have hNWc : NFWithin c.nmem E.H E.LB E.N := hI.nfWithin hE le_rfl
  have hareas := (Gran.nf_areas hNWc).2.2.1 r hr
  have h5 : c.nmem (E.H + 5) = c₀.nmem (E.H + 5) := hI.low _ (by
    have := (Gran.nf_areas hNWc).1; omega)
  Ξ' h5 at hareas
  have hLBW : E.LB ≤ E.W := le_trans (hE.lb_le) (hE.wb.1 ALLOC)
  have hRW : E.R + 1 ≤ E.W := by
    have := hE.room
    have : E.R ≤ (E.Bf + 2) * E.R := Nat.le_mul_of_pos_left _ (⋄)
    omega
  have hLB3 : E.LB + 3 ≤ E.W := by
    have := hE.alloc; have := hE.wb.1 ALLOC; omega
  obtain ⟨c₃, k₃, e₃, hk₃, t41, t40, R₃, rr₃, m₃, rm₃, o₃⟩ := tail_exec (P := E.P) c₂ w₂
    (by rw [k41, k23]; omega) (by rw [k40, k20]; omega)
  Ξ' k41, k23 at t41
  Ξ' k40, k20 at t40
  have RF₃ : RF dBands E.A₀ c₂ c₃ k₃ := rf_of_regs (fun q hq => R₃ q (⋄) (⋄))
    rr₃ m₃ rm₃ o₃
  have RFall : RF dBands E.A₀ c c₃ (k₁ + (k₂ + k₃)) := RF₁.trans (RF₂.trans RF₃)
  have hBf : costF E.κf E.F E.G E.Hc E.dcap E.γ + 20 = E.Bf := rfl
  refine ⟨c₃, k₁ + (k₂ + k₃), newL', .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, ⋄,
    by rw [t41, t40]; ring, by rw [t40]; exact hfst₂, hgood₂,
    by rw [R₃ _ (⌖) (⌖)]; exact cnt₂,
    by rw [R₃ _ (⌖) (⌖)]; exact dst₂, by rw [m₃]; exact list₂,
    fun a ha => by rw [m₃, low₂ a ha, m₁]; exact hI.low a ha,
    fun q q1 q2 q3 q4 q5 q6 q7 => ?_, ?_, ?_⟩, RFall, ⋄, Ρ t40, hrdef⟩
  · rw [R₃ q q4 q3, reg₂ q q1 q2 q6 q7]; exact hI₁.regs q q1 q2 q3 q4 q5 q6 q7
  · exact le_trans hI.alloc RFall.2.2.2.2.2.1
  · have h1 := hI.room
    have h2 := RFall.2.2.2.2.2.2
    Ξ t40
    Ξ' hrdef at h1
    have h3 : (E.Bf + 2) * (E.R - r) = (E.Bf + 2) * (E.R - (r + 1)) + (E.Bf + 2) := by
      Ξ show E.R - r = (E.R - (r + 1)) + 1 by omega, Nat.mul_add, Nat.mul_one
    omega

/-- **The region loop.** -/
theorem reg_exec {E : RegEnv} {c₀ : Config} (hE : RegGood E c₀) :
    ∃ c' k newL, Exec E.P E.W (regS E.sF) c₀ c' k ∧ RegI E c₀ newL c' ∧
      c'.nreg 80040 = E.R ∧ RF dBands E.A₀ c₀ c' k ∧ k ≤ (E.Bf + 2) * E.R + 2 := by
  have I0 : RegI E c₀ [] c₀ := ⟨hE.wb, by rw [hE.r40]; omega, by rw [hE.r40, hE.r41],
    by rw [hE.r40]; rfl, fun p hp => by simp at hp, by rw [hE.r18]; simp,
    by rw [hE.r43]; simp, by simpa using hE.list, fun _ _ => rfl,
    fun _ _ _ _ _ _ _ _ => rfl, le_rfl, by rw [hE.r40]; simp⟩
  obtain ⟨c', k, e, ⟨newL, I'⟩, hx, RFl, hk⟩ := whileLtN_frame (P := E.P) (W := E.W)
    (a := 80040) (b := 80014) (body := regBody E.sF) (B := dBands) (A₀ := E.A₀)
    (fun c => ∃ newL, RegI E c₀ newL c) (fun c => E.R - c.nreg 80040) E.Bf
    (fun c ⟨_, h⟩ => h.wb)
    (fun c ⟨newL, I⟩ ht => by
      have t : c.nreg 80040 < E.R := by
        rw [I.regs 80014 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega), hE.r14] at ht
        exact ht
      obtain ⟨c', k, newL', e, I', RF', hk, h40⟩ := regBody_step hE I t
      exact ⟨c', k, e, ⟨newL', I'⟩, RF', hk, by omega⟩) ⟨[], I0⟩
  have hR' : c'.nreg 80040 = E.R := by
    rw [I'.regs 80014 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hE.r14] at hx
    have := I'.r_le; omega
  refine ⟨c', k, newL, e, I', hR', RFl, ?_⟩
  rw [hE.r40] at hk
  simpa using hk

end

end Restore

end Chazelle.Core
