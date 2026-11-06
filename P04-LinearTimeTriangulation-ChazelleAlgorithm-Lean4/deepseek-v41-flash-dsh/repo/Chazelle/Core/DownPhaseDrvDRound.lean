module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvDReg
public import Chazelle.Core.DownPhaseDrvRSplG
public import Chazelle.Core.DownPhaseDrvRRoundSpec

/-!
# Down-phase restoration rounds (D8), part 11: the data of the rounds, straight-line pieces

`DEnv`: the fixed data of the rounds (the base `A₀` below which the memory is the initial one,
the descriptor, `d₀`, `γ`, the context, the splitting step `sF`, the sorted build `sB` and
their costs, the initial family `S₀` and count `K₀`, the initial registers `r₀`); `DGood` its
facts; `RInv E t c`: the state after `t` rounds (`DrvR.StateAt` with a family `⊇ S₀`, degree
`≤ max 4 (d₀ - t)`, `γ`-semigranular, at most `2^t (K₀ + 1) - 1` chords).

Straight-line pieces of a round: `hdS_exec`, `resS_exec`, `midS_exec`, `splArgs_exec`.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

/-- **The fixed data of the rounds.** -/
structure DEnv where
  P : Polygon
  W : ℕ
  A₀ : ℕ
  m₀ : ℕ → ℕ
  r₀ : ℕ → ℕ
  MD : ℕ
  γ : ℕ
  d0 : ℕ
  ctx : ℕ
  sF : Stmt
  sB : Stmt
  κf : ℕ → ℕ
  κB : ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx
  S₀ : Set (Set Point)
  K₀ : ℕ

namespace DEnv

variable (E : DEnv)

/-- The geometry polygon. -/
noncomputable abbrev Q : Polygon := Qof E.P

/-- The interior model. -/
noncomputable abbrev M : Model := interiorModel E.Q

/-- A bound on the number of regions during the rounds. -/
def Kc : ℕ := 2 ^ E.d0 * (E.K₀ + 1)

/-- The body bound of the region loop. -/
def Bf : ℕ := Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ + 2 * ((scanK + 2) * (E.d0 + 1)) + 60

/-- The bound of one round. -/
def Br : ℕ := 40 + (E.Bf + 10) * E.Kc + 8 * DrvR.κSpl E.κB * E.Kc

end DEnv

/-- The registers of `bDownDrv` the rounds keep (the post of `RoundsSpec`). -/
def KeepR (q : ℕ) : Prop :=
  q = 210000 ∨ q = 210001 ∨ (211000 ≤ q ∧ q < 216000) ∨ (217000 ≤ q ∧ q < 220000)

/-- **The facts of the rounds' data.** -/
structure DGood (E : DEnv) : Prop where
  hF : Restore.FindOK E.sF E.κf E.F E.G E.Hc E.X DrvR.OkInt DrvR.ioBandsD
  hB : DrvR.SortedMeets E.sB E.κB
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, (∀ a, a < E.A₀ → m a = E.m₀ a) → E.γ ≤ E.X.cap E.P m E.ctx
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD E.Q E.M
  hd0 : 4 ≤ E.d0

/-- **The state after `t` rounds.** -/
structure RInv (E : DEnv) (t : ℕ) (c : Config) : Prop where
  wb : WordsBounded E.W c
  r001 : c.nreg 210001 = E.MD
  r00 : c.nreg 216000 = E.d0
  r01 : c.nreg 216001 = E.γ
  r02 : c.nreg 216002 = 1
  r03 : c.nreg 216003 = 0
  r04 : c.nreg 216004 = 4
  r05 : c.nreg 216005 = 2
  r06 : c.nreg 216006 = 5
  r10 : c.nreg 216010 = t
  rctx : c.nreg 230001 = E.ctx
  keep : ∀ q, KeepR q → c.nreg q = E.r₀ q
  state : ∃ (L : List (ℕ × ℕ × ℕ)) (Ev : List ℕ), DrvR.StateAt E.P c L Ev ∧
    E.S₀ ⊆ (BuildNF.buildNF E.M E.Q L Ev).F E.M E.Q ∧
    E.M.DegLe ((BuildNF.buildNF E.M E.Q L Ev).F E.M E.Q) (max 4 (E.d0 - t)) ∧
    E.M.Semigranular ((BuildNF.buildNF E.M E.Q L Ev).F E.M E.Q) E.γ ∧
    L.length + 1 ≤ 2 ^ t * (E.K₀ + 1)
  low : ∀ a, a < E.A₀ → c.nmem a = E.m₀ a
  alloc : E.A₀ ≤ c.nreg ALLOC
  t_le : t ≤ E.d0
  room : c.nreg ALLOC + (E.d0 - t) * (E.Br + 2) + 3 ≤ E.W

/-! ## Straight-line pieces -/

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- The header of the current normal form. -/
theorem hdS_exec (c : Config) (hw : WordsBounded W c) {H : ℕ} (h05 : c.nreg 210005 = H)
    (h02 : c.nreg 216002 = 1) (h0205 : c.nreg 216005 = 2) (hH : H + 7 ≤ W) :
    ∃ c' k, Exec P W hdS c c' k ∧ k = 15 ∧ c'.nreg 216012 = H ∧
      c'.nreg 216017 = c.nmem (H + 1) ∧ c'.nreg 216013 = c.nmem (H + 2) ∧
      c'.nreg 216014 = c.nmem (H + 4) ∧ c'.nreg 216015 = c.nmem (H + 5) ∧
      c'.nreg 216016 = c.nmem (H + 7) ∧ c'.nreg 216018 = c.nreg ALLOC ∧
      c'.nreg 216021 = c.nreg ALLOC ∧ c'.nreg 216020 = 0 ∧ c'.nreg 216023 = 0 ∧
      FrameB (fun r => decide (216012 ≤ r ∧ r ≤ 216033)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W hdS c c' k ∧ k = 15 ∧
      (c'.nreg 216012 = H ∧
      c'.nreg 216017 = c.nmem (H + 1) ∧ c'.nreg 216013 = c.nmem (H + 2) ∧
      c'.nreg 216014 = c.nmem (H + 4) ∧ c'.nreg 216015 = c.nmem (H + 5) ∧
      c'.nreg 216016 = c.nmem (H + 7) ∧ c'.nreg 216018 = c.nreg ALLOC ∧
      c'.nreg 216021 = c.nreg ALLOC ∧ c'.nreg 216020 = 0 ∧ c'.nreg 216023 = 0) := by
    unfold hdS
    exec_block
    all_goals try (config_simp; (try simp only [h05, h02, h0205]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals config_simp
    all_goals try simp only [h05, h02, h0205]
    all_goals try rfl
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2,
    exec_frameB ex (⌖)⟩

/-- The registers of the reservation. -/
def Bres (r : ℕ) : Bool := decide (r = 216023) || decide (r = 9999)

/-- **The reservation** of `5 R` words. -/
theorem resS_exec {c : Config} (hw : WordsBounded W c) {R : ℕ} (h13 : c.nreg 216013 = R)
    (h23 : c.nreg 216023 = 0) (h02 : c.nreg 216002 = 1) (hW : c.nreg ALLOC + 5 * R + 1 ≤ W)
    (A₀ : ℕ) :
    ∃ c' k, Exec P W resS c c' k ∧ k ≤ 8 * R + 2 ∧ c'.nreg ALLOC = c.nreg ALLOC + 5 * R ∧
      c'.nreg 216023 = R ∧ FrameB Bres c c' ∧ Restore.RF DrvR.drvBands A₀ c c' k := by
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 216023 = j ∧
    e.nreg 216013 = R ∧ e.nreg 216002 = 1 ∧ e.nreg ALLOC = c.nreg ALLOC + 5 * j ∧
    FrameB Bres c e ∧ j ≤ R
  have key : ∀ j e, j < R → Inv j e → ∃ e' k, Exec P W resBody e e' k ∧ Inv (j + 1) e' ∧
      Restore.RF DrvR.drvBands A₀ e e' k ∧ k = 6 := by
    intro j e hj ⟨hw, h1, h2, h3, h4, hf, _⟩
    have h4' : e.nreg 9999 = c.nreg ALLOC + 5 * j := h4
    obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W resBody e e' k ∧ k = 6 ∧
        (e'.nreg 216023 = j + 1 ∧ e'.nreg 9999 = c.nreg ALLOC + 5 * (j + 1)) := by
      unfold resBody
      exec_block
      all_goals try (config_simp; (try simp only [h1, h3, h4']); omega)
      refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp only [h1, h3, h4']; omega
    have hf' : FrameB Bres e e' := exec_frameB ex (by decide)
    have hA' : e'.nreg ALLOC = e.nreg ALLOC + 5 := by
      show e'.nreg 9999 = e.nreg 9999 + 5
      rw [q.2, h4']; ring
    have hnot : ∀ r, bandOf r ∉ DrvR.drvBands → r ≠ ALLOC → Bres r = false := fun r hr hra => by
      simp only [Bres, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨fun h => hr (by rw [h]; exact mem_drvBands (by norm_num) (by norm_num)), hra⟩
    refine ⟨e', k, ex, ⟨ex.wb_right, q.1, (hf'.1 _ (by decide)).trans h2,
      (hf'.1 _ (by decide)).trans h3, by show e'.nreg 9999 = _; rw [q.2], hf.trans hf', hj⟩,
      ⟨fun r hr hra => hf'.1 r (hnot r hr hra), fun r _ =>
        WalkKey.exec_rframe ex (B := fun _ => false) (by decide) r rfl, fun a _ => by rw [hf'.2.2.1],
        fun a _ => by rw [hf'.2.2.2.1], hf'.2.2.2.2, by omega, by omega⟩, hk⟩
  have I0 : Inv 0 c := ⟨hw, h23, h13, h02, by simp, FrameB.refl _ _, Nat.zero_le _⟩
  obtain ⟨c', k, ex, ⟨j, w', h1, h2, -, h4, hf, hjle⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := P)
    (W := W) (a := 216023) (b := 216013) (body := resBody) (B := DrvR.drvBands) (A₀ := A₀)
    (fun e => ∃ j, Inv j e) (fun e => R - e.nreg 216023) 6 (fun e ⟨_, h⟩ => h.1)
    (fun e ⟨j, hI⟩ ht => by
      obtain ⟨hw, h1, h2, -⟩ := id hI
      rw [h1, h2] at ht
      obtain ⟨e', k, ex, hI', RF', hk⟩ := key j e ht hI
      exact ⟨e', k, ex, ⟨j + 1, hI'⟩, RF', by omega, by rw [h1, hI'.2.1]; omega⟩) ⟨0, I0⟩
  have hjR : j = R := by rw [h1, h2] at hx; omega
  subst hjR
  refine ⟨c', k, ex, ?_, h4, h1, hf, RFl⟩
  rw [h23] at hk
  simpa using hk

set_option maxHeartbeats 1000000 in
/-- The bucket base and the region loop set-up. -/
theorem midS_exec (c : Config) (hw : WordsBounded W c) {R B RB : ℕ} (h13 : c.nreg 216013 = R)
    (h18 : c.nreg 216018 = B) (h15 : c.nreg 216015 = RB) (h05 : c.nreg 216005 = 2)
    (hW : B + 3 * R ≤ W) (hRB : RB + 2 ≤ W) :
    ∃ c' k, Exec P W midS c c' k ∧ k = 6 ∧ c'.nreg 216019 = B + 3 * R ∧
      c'.nreg 216022 = B + 3 * R ∧ c'.nreg 216030 = 0 ∧ c'.nreg 216031 = RB + 2 ∧
      FrameB (fun r => decide (r = 216019 ∨ r = 216022 ∨ r = 216030 ∨ r = 216031 ∨
        r = 216033)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W midS c c' k ∧ k = 6 ∧
      (c'.nreg 216019 = B + 3 * R ∧ c'.nreg 216022 = B + 3 * R ∧ c'.nreg 216030 = 0 ∧
        c'.nreg 216031 = RB + 2) := by
    unfold midS
    exec_block
    all_goals try (config_simp; (try simp only [h13, h18, h15, h05]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h13, h18, h15, h05]) <;> omega
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2, exec_frameB ex (⌖)⟩

set_option maxHeartbeats 1000000 in
/-- The arguments of the splice. -/
theorem splArgs_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W splArgs c c' k ∧ k = 5 ∧ c'.nreg 210020 = c.nreg 216018 ∧
      c'.nreg 210021 = c.nreg 216020 ∧ c'.nreg 210022 = c.nreg 216019 ∧
      c'.nreg 210023 = c.nreg 216017 ∧ c'.nreg 210024 = c.nreg 216005 ∧
      FrameB (fun r => decide (210020 ≤ r ∧ r ≤ 210024)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W splArgs c c' k ∧ k = 5 ∧
      (c'.nreg 210020 = c.nreg 216018 ∧
      c'.nreg 210021 = c.nreg 216020 ∧ c'.nreg 210022 = c.nreg 216019 ∧
      c'.nreg 210023 = c.nreg 216017 ∧ c'.nreg 210024 = c.nreg 216005) := by
    unfold splArgs
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, exec_frameB ex (⌖)⟩

/-- The round counter. -/
theorem incr_exec (c : Config) (hw : WordsBounded W c) {t : ℕ} (h10 : c.nreg 216010 = t)
    (h02 : c.nreg 216002 = 1) (ht : t + 1 ≤ W) :
    ∃ c' k, Exec P W (block [.addN 216010 216010 216002]) c c' k ∧ k = 1 ∧
      c'.nreg 216010 = t + 1 ∧ FrameB (fun r => decide (r = 216010)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W (block [.addN 216010 216010 216002]) c c' k ∧
      k = 1 ∧ c'.nreg 216010 = t + 1 := by
    exec_block
    · rw [h10, h02]; exact ht
    · refine ⟨rfl, ?_⟩; config_simp; rw [h10, h02]
  exact ⟨c', k, ex, hk, q, exec_frameB ex (⌖)⟩

end exec

end

end DrvD

end Chazelle.Core
