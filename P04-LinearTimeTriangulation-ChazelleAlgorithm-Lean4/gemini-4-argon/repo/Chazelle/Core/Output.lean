module

public import Chazelle.Core.OutputRam

/-!
# WP-N: the output phase

`Output.prog`: the orientation of the walk, the constants, the reads of the normal-form header,
then the region loop (`OutputRam.lean`).  `outputSpecH : OutputSpecH` proves the output phase for
normal forms whose chord records have their height vertex below `n`.

**Spec gap (reported).**  `OutputSpec` itself is `OutputSpecH` without the hypothesis
`∀ k < N.nChords, (N.chord k).h < P.n`: `IsNF` does not bound the height vertex of a chord record,
and a record with `h ≥ n` (then `vtx h = (0, 0)`) describes a chord at height `0` without naming
its vertex, which the machine cannot recover from `P` (the height `0` of `Q` is not a comparison
between symbolic points).  Adding `(N.chord k).h < Q.n` to `IsNF` (or to the down phase's
postcondition and the output phase's precondition) closes the gap; every chord record produced
from symbolic points satisfies it.
-/

namespace Chazelle.Core

namespace Output

open Machine Machine.Stmt Programs
open OutWalk OutTrap OutNF

@[expose] public section

/-! ## The program -/

/-- Constants: `n`, `1`, `0`, `2`, `3`, `4`, `5`, `7`, `n - 1`, `n - 2`, and the real `0`. -/
def initS : Stmt :=
  block [.inputSize 220000, .constN 220001 1, .constN 220002 0, .constN 220019 2,
    .constN 220020 3, .constN 220011 4, .constN 220012 5, .constN 220021 7,
    .subN 220017 220000 220001, .subN 220018 220017 220001, .constR 220000 0]

/-- The reversal flag: `1` iff the orientation (real register `100`) is negative. -/
def revS : Stmt := .ifLtR 100 220000 (.instr (.constN 220003 1)) (.instr (.constN 220003 0))

/-- The header of the normal form (handle in `coreReg 3`), the table base `T₀ = ALLOC`, the loop
registers and the hand-off registers. -/
def readS : Stmt :=
  block [.copyN 220004 230003, .addN 220117 220004 220019, .loadN 220005 220117,
    .addN 220117 220004 220020, .loadN 220006 220117, .addN 220117 220004 220012,
    .loadN 220007 220117, .addN 220117 220004 220021, .loadN 220008 220117,
    .copyN 220009 9999, .constN 220010 0, .copyN 220013 220007, .copyN 220016 220009,
    .copyN 9990 220009, .copyN 9991 220005, .copyN 9992 220009, .constN 9993 0]

/-- The preparation. -/
def prepS : Stmt := .seq initS (.seq revS readS)

/-- **The output program.** -/
def prog : Stmt := .seq Final.orientStmt (.seq prepS regionLoop)

section prep

variable {P : Polygon} {W : ℕ}

/-- Spec of the preparation: constants, the reversal flag from the orientation, the header of the normal form, the table base and the hand-off registers; cost `≤ 40`. -/
theorem prepS_spec {c : Config} (hc : WordsBounded W c) {σ : ℝ} {B T0 : ℕ}
    (hσ : c.rreg 100 = σ) (hB : c.nreg 230003 = B) (hT0 : c.nreg 9999 = T0) (hb : B + 7 ≤ W)
    (hn : P.n + 7 ≤ W) :
    ∃ c' k, Exec P W prepS c c' k ∧ k ≤ 40 ∧ ArithRegs c' (decide (σ < 0)) P.n ∧
      c'.nreg 220005 = c.nmem (B + 2) ∧ c'.nreg 220006 = c.nmem (B + 3) ∧
      c'.nreg 220007 = c.nmem (B + 5) ∧ c'.nreg 220008 = c.nmem (B + 7) ∧
      c'.nreg 220009 = T0 ∧ c'.nreg 220011 = 4 ∧ c'.nreg 220012 = 5 ∧ c'.nreg 220019 = 2 ∧
      c'.nreg 220020 = 3 ∧ c'.nreg 220010 = 0 ∧ c'.nreg 220013 = c.nmem (B + 5) ∧
      c'.nreg 220016 = T0 ∧ c'.nreg 9990 = T0 ∧ c'.nreg 9991 = c.nmem (B + 2) ∧
      c'.nreg 9992 = T0 ∧ c'.nreg 9993 = 0 ∧ c'.nreg 9999 = T0 ∧
      (∀ r, 240000 ≤ r → c'.nreg r = c.nreg r) ∧ (∀ r, 240000 ≤ r → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold prepS
  refine spec_seq ?_
  unfold initS
  exec_block
  all_goals try omega
  refine Final.spec_name fun c1 hc1 => ?_
  have hw1 : WordsBounded W c1 := by rw [hc1]; assumption
  have r1 : c1.rreg 100 = σ := by rw [hc1]; config_simp; exact hσ
  have r0 : c1.rreg 220000 = 0 := by rw [hc1]; config_simp; simp
  have hA1 : ∀ bb : Bool, c1.nreg 220000 = P.n ∧ c1.nreg 220001 = 1 ∧ c1.nreg 220002 = 0 ∧
      c1.nreg 220017 = P.n - 1 ∧ c1.nreg 220018 = P.n - 2 ∧ c1.nreg 220019 = 2 ∧
      c1.nreg 220020 = 3 ∧ c1.nreg 220011 = 4 ∧ c1.nreg 220012 = 5 ∧ c1.nreg 220021 = 7 ∧
      c1.nreg 230003 = B ∧ c1.nreg 9999 = T0 := fun _ => by
    rw [hc1]; config_simp
    exact ⟨by omega, hB, hT0⟩
  obtain ⟨b0, b1, b2, b17, b18, b19, b20, b11, b12, b21, b3, b9999⟩ := hA1 true
  have fr1 : ∀ r, 240000 ≤ r → c1.nreg r = c.nreg r := fun r hr => by
    rw [hc1]; simp (disch := omega) only [Machine.upd_other]
  have rr1 : ∀ r, 240000 ≤ r → c1.rreg r = c.rreg r := fun r hr => by
    rw [hc1]; simp (disch := omega) only [Machine.upd_other]
  have m1 : c1.nmem = c.nmem := by rw [hc1]
  have rm1 : c1.rmem = c.rmem := by rw [hc1]
  have o1 : c1.output = c.output := by rw [hc1]
  -- the reversal flag
  have hrev : ∃ c2 k2, Exec P W revS c1 c2 k2 ∧ k2 ≤ 3 ∧
      c2 = { c1 with nreg := upd c1.nreg 220003 (decide (σ < 0)).toNat } := by
    unfold revS
    by_cases hneg : σ < 0
    · refine spec_ifLtR_true (by rwa [r1, r0])
        (spec_instr (Exec.constN hw1 220003 1 (by omega)) fun _ => ?_)
      exact ⟨by omega, by simp [hneg]⟩
    · refine spec_ifLtR_false (by rwa [r1, r0])
        (spec_instr (Exec.constN hw1 220003 0 (by omega)) fun _ => ?_)
      exact ⟨by omega, by simp [hneg]⟩
  obtain ⟨c2, k2, e2, hk2, rfl⟩ := hrev
  refine spec_seq ⟨_, k2, e2, ?_⟩
  unfold readS
  have hw2 := e2.wb_right
  exec_block
  all_goals try (config_simp; simp only [b3, b19, b20, b12, b21]; omega)
  all_goals try omega
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  all_goals try (config_simp; simp only [b0, b1, b2, b17, b18, b19, b20, b11, b12, b21, b3, b9999, m1]; done)
  all_goals try (config_simp; done)
  · rw [← fr1 r hr]; simp (disch := omega) only [Machine.upd_other]
  · rw [← rr1 r hr]
  all_goals first | exact m1 | exact rm1 | exact o1

end prep

end

end Output

end Chazelle.Core

namespace Chazelle.Core

@[expose] public section

open Machine Machine.Stmt Programs
open OutWalk OutTrap OutNF Output

/-- **WP-N with the height hypothesis**: `OutputSpec` with the extra precondition that the chord
records of the normal form name their height vertex (`h < n`); see the module docstring. -/
def OutputSpecH : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s outBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧ c.output = [] ∧
      ∃ N, Robust (c.nreg ALLOC) c.nmem (fun m => NFAt m (c.nreg (coreReg 3)) N) ∧
        IsNF (interiorModel (Qof P)) (Qof P) N ∧
        N.F (interiorModel (Qof P)) (Qof P) = (interiorModel (Qof P)).Full ∧
        ∀ k, k < N.nChords → (N.chord k).h < P.n)
    (fun P _ c' => TablesReady (Qof P) c')
    (fun P _ => κ * (P.n + 1))

/-- The reversal flag computed from the orientation. -/
theorem decide_orient_neg (Q : Polygon) : decide (Mountain.orient Q < 0) = revOf Q := by
  classical
  unfold Mountain.orient revOf
  by_cases h : Mountain.LeftInside Q <;> simp [h]

/-- Entry `i` of the table of records of the regions. -/
theorem getD_trapTable {nR : ℕ} {f : ℕ → Final.TrapRec} {i : ℕ} (hi : i < nR) :
    ((List.range nR).map f).getD i ⟨0, 0, 0, 0⟩ = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

/-- A register outside the output bands is at least `240000`. -/
theorem ge_of_band {r : ℕ} (h : bandOf r ∉ outBands) : 240000 ≤ r := by
  have h' : ¬ r / 10000 < 25 := fun h' => h (Finset.mem_range.2 h')
  omega

/-- **WP-N (proved, with the height hypothesis)**: the output program meets `OutputSpecH` with
the constant `κ = 700`. -/
theorem outputSpecH : OutputSpecH := by
  refine ⟨Output.prog, 700, ?_⟩
  intro P W c hw ⟨hge, hn3, hout, N, hRob, hNF, hfull, hhlt⟩ hroom
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hge.1
  have hgs := goodShear_epsOf hge.2
  have hdh : DistinctHeights (Qof P) := hgs.2.1
  have hPQ : ShearRel P (Qof P) := shearRel_Qof hge.2
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn3' : 3 ≤ P.n := hge.1.1
  obtain ⟨reg, hcorr, hsides, -, hregs, -⟩ := hNF.2.2.2
  have H : RegCtx (Qof P) N reg :=
    ⟨hQ, hdh, hNF, hfull, fun k hk => hQn ▸ hhlt k hk, hcorr, hsides, hregs⟩
  have hT := table_ok H
  have hnR : N.nRegions ≤ 2 * P.n + 1 := by
    have := hT.length_le hQ
    rwa [List.length_map, List.length_range, hQn] at this
  have hAL : ALLOC = 9999 := rfl
  have hc3 : coreReg 3 = 230003 := rfl
  rw [hAL] at hroom hRob
  rw [hc3] at hRob
  simp only at hroom
  set B := c.nreg 230003
  set T0 := c.nreg 9999
  have hRd := nfReads_of_robust hRob
  have hB2 := hRd.nr
  -- stage 1: the orientation
  obtain ⟨c1, k1, e1, hk1, hσ, fn1, fr1, m1, rm1, o1⟩ :=
    Final.orientStmt_exec (W := W) hPQ hQ c hw (by omega)
  -- stage 2: the preparation
  obtain ⟨c2, k2, e2, hk2, hA2, v5, v6, v7, v8, v9, v11, v12, v19, v20, v10, v13, v16, v9990, v9991,
    v9992, v9993, v9999, fn2, fr2, m2, rm2, o2⟩ := prepS_spec (P := P) e1.wb_right hσ
      (by rw [fn1 _ (by omega)]) (by rw [fn1 _ (by omega)]) (by omega) (by omega)
  rw [decide_orient_neg] at hA2
  rw [m1] at v5 v6 v7 v8 v13 v9991
  -- stage 3: the regions
  have hent : ∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      (N.region r).chords.getD t 0 < N.nChords := fun r hr t ht => by
    have hmem : (N.region r).chords.getD t 0 ∈ (N.region r).chords := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      exact List.getElem_mem ht
    exact (((hregs r hr).1 _).1 hmem).1
  have hrec : ∀ k, k < N.nChords →
      (N.chord k).h < P.n ∧ (N.chord k).lp < P.n ∧ (N.chord k).rp < P.n := fun k hk => by
    obtain ⟨hl, hr, -⟩ := rec_attach hNF hk
    exact ⟨hhlt k hk, hQn ▸ hl, hQn ▸ hr⟩
  have hC : RegConsts c2 (revOf (Qof P)) P.n N.nRegions (c.nmem (B + 3)) (c.nmem (B + 7)) T0 :=
    ⟨hA2, by rw [v5, hB2.1], v6, v8, v9, v11, v12, v19, v20⟩
  have hI0 : RegInv W (revOf (Qof P)) P.n N T0 (c.nmem (B + 5)) c.nmem c2 c2 :=
    ⟨e2.wb_right, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, by rw [v10]; exact Nat.zero_le _,
      by rw [v13, v10]; ring, by rw [v16, v10]; ring, by rw [v9999, v10]; ring,
      fun a _ => by rw [m2, m1], fun s hs => by rw [v10] at hs; exact absurd hs (Nat.not_lt_zero _)⟩
  obtain ⟨c3, k3, e3, hI3, h10, hk3, hΨ⟩ := regionLoop_spec (P := P) hC hRd rfl rfl rfl
    (fun r hr => chords_length_le H hr) hent hrec (by omega) (by omega) (by omega) hI0 v10
  obtain ⟨hw3, hfr3, hrr3, hrm3, ho3, -, -, -, hal3, hmem3, hrecs3⟩ := hI3
  have eall : Exec P W Output.prog c c3 (k1 + (k2 + k3)) := e1.seq (e2.seq e3)
  refine ⟨c3, _, eall, ?_, ?_, ?_⟩
  · -- cost
    have : 332 * N.nRegions ≤ 332 * (2 * P.n + 1) := Nat.mul_le_mul_left _ hnR
    nlinarith
  · -- the tables
    refine ⟨_, [], hT, vtxChordTable_nil hQ hdh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show c3.nreg 9991 = _
      rw [hfr3 _ (by unfold regFree; omega), v9991, hB2.1, List.length_map, List.length_range]
    · show TrapTableAt c3.nmem (c3.nreg 9990) _
      rw [hfr3 _ (by unfold regFree; omega), v9990]
      intro i hi
      rw [List.length_map, List.length_range] at hi
      rw [getD_trapTable hi, hQn]
      obtain ⟨t1, t2, t3, t4⟩ := hrecs3 i (by rwa [h10])
      exact ⟨t1, t2, t3, t4⟩
    · show c3.nreg 9993 = _
      rw [hfr3 _ (by unfold regFree; omega), v9993]; rfl
    · intro i hi; exact absurd hi (Nat.not_lt_zero _)
    · show c3.nreg 9990 + _ ≤ c3.nreg 9999
      rw [hfr3 _ (by unfold regFree; omega), v9990, hal3, h10, List.length_map, List.length_range]
    · show c3.nreg 9992 + 3 * 0 ≤ c3.nreg 9999
      rw [hfr3 _ (by unfold regFree; omega), v9992, hal3]; omega
    · rw [ho3, o2, o1, hout]
  · -- the frame
    refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a _ => ?_, ?_, ?_, ?_⟩
    · have hr' : 240000 ≤ r := ge_of_band hr
      rw [hfr3 _ (by unfold regFree; omega), fn2 _ hr', fn1 _ (by omega)]
    · have hr' : 240000 ≤ r := ge_of_band hr
      rw [hrr3 _ (by unfold regFree; omega), fr2 _ hr', fr1 _ (by omega) (by omega)]
    · exact hmem3 a ha
    · rw [hrm3, rm2, rm1]
    · rw [ho3, o2, o1]
    · rw [hAL, hal3]; omega
    · rw [hAL]; rw [v9999] at hΨ; omega

/-! ## Composition with the strengthened down phase -/

/-- `DownPhaseSpec` whose normal form also names the height vertex of each chord record. -/
def DownPhaseSpecH (X : MemCtx) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s phaseBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧
      Robust (c.nreg ALLOC) c.nmem (fun m => SetupAt m (c.nreg (coreReg 0)) P.n (c.nreg ALLOC)) ∧
      X.holds P c.nmem (c.nreg (coreReg 1)) (c.nreg ALLOC) ∧
      P.n - 1 ≤ X.cap P c.nmem (c.nreg (coreReg 1)) ∧
      ∃ C N, TopChain P C ∧ Robust (c.nreg ALLOC) c.nmem (fun m => NFAt m (c.nreg (coreReg 2)) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (topGran P.n) 4)
    (fun P _ c' => ∃ N, Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (c'.nreg (coreReg 3)) N) ∧
      IsNF (interiorModel (Qof P)) (Qof P) N ∧
      N.F (interiorModel (Qof P)) (Qof P) = (interiorModel (Qof P)).Full ∧
      ∀ k, k < N.nChords → (N.chord k).h < P.n)
    (fun P _ => κ * (P.n + 1))

/-- **The core stage from the phases, with the height hypothesis** (the proof of
`core_of_phases`, with `DownPhaseSpecH` and `OutputSpecH`). -/
theorem core_of_phasesH (hS : SetupSpec) (hUD : ∃ X : MemCtx, UpPhaseSpec X ∧ DownPhaseSpecH X)
    (hO : OutputSpecH) (hgood : GoodShearExistsSpec) (hsh : ShearInvarianceSpec) :
    CoreStageSpec := by
  obtain ⟨⟨sS, κS, hS⟩, ⟨X, ⟨sU, κU, hU⟩, ⟨sD, κD, hD⟩⟩, ⟨sO, κO, hO⟩⟩ := And.intro hS
    (And.intro hUD hO)
  refine ⟨.seq sS (.seq sU (.seq sD sO)), κS + κU + κD + κO, κS + κU + κD + κO + 3, ?_⟩
  intro P hP W hW
  have hge : GoodEnv P := ⟨hP, hgood P hP⟩
  obtain ⟨bS, hbS⟩ : ∃ b, b = κS * (P.n + 1) := ⟨_, rfl⟩
  obtain ⟨bU, hbU⟩ : ∃ b, b = κU * (P.n + 1) := ⟨_, rfl⟩
  obtain ⟨bD, hbD⟩ : ∃ b, b = κD * (P.n + 1) := ⟨_, rfl⟩
  obtain ⟨bO, hbO⟩ : ∃ b, b = κO * (P.n + 1) := ⟨_, rfl⟩
  have hsum : (κS + κU + κD + κO + 3) * (P.n + 1) = bS + bU + bD + bO + 3 * (P.n + 1) := by
    subst hbS hbU hbD hbO; ring
  have hC : (κS + κU + κD + κO) * (P.n + 1) = bS + bU + bD + bO := by
    subst hbS hbU hbD hbO; ring
  rw [hsum] at hW
  have hn3 : P.n + 3 ≤ W := by omega
  have hw0 : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have ha0 : initConfig.nreg ALLOC = 0 := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, hq₁, hf₁⟩ := hS P W initConfig hw0 ⟨hge, hn3⟩
    (show initConfig.nreg ALLOC + κS * (P.n + 1) ≤ W by rw [ha0, ← hbS]; omega)
  replace hk₁ : k₁ ≤ bS := by rwa [hbS]
  have ha₁ : c₁.nreg ALLOC ≤ k₁ := by have := hf₁.2.2.2.2.2.2; rw [ha0] at this; omega
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨hkeep₂, hX₂, hcap₂, C, N, hC₂, hN₂, hcan₂⟩, hf₂⟩ :=
    hU P W c₁ e₁.wb_right ⟨hge, hn3, hq₁⟩
      (show c₁.nreg ALLOC + κU * (P.n + 1) ≤ W by rw [← hbU]; omega)
  replace hk₂ : k₂ ≤ bU := by rwa [hbU]
  have ha₂ : c₂.nreg ALLOC ≤ c₁.nreg ALLOC + k₂ := hf₂.2.2.2.2.2.2
  have hset₂ : Robust (c₂.nreg ALLOC) c₂.nmem
      (fun m => SetupAt m (c₂.nreg (coreReg 0)) P.n (c₂.nreg ALLOC)) := by
    have h0 : c₂.nreg (coreReg 0) = c₁.nreg (coreReg 0) := hkeep₂ 0 (by simp)
    rw [h0]
    intro m hm
    have hq := (hq₁.frame hf₂) m hm
    exact ⟨hq.1, hq.2.1, hq.2.2.1, le_trans hq.2.2.2 hf₂.2.2.2.2.2.1⟩
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨N', hN₃, hnf₃, hfull₃, hh₃⟩, hf₃⟩ :=
    hD P W c₂ e₂.wb_right ⟨hge, hn3, hset₂, hX₂, hcap₂, C, N, hC₂, hN₂, hcan₂⟩
      (show c₂.nreg ALLOC + κD * (P.n + 1) ≤ W by rw [← hbD]; omega)
  replace hk₃ : k₃ ≤ bD := by rwa [hbD]
  have ha₃ : c₃.nreg ALLOC ≤ c₂.nreg ALLOC + k₃ := hf₃.2.2.2.2.2.2
  have hout₃ : c₃.output = [] := by
    rw [hf₃.2.2.2.2.1, hf₂.2.2.2.2.1, hf₁.2.2.2.2.1]; rfl
  obtain ⟨c₄, k₄, e₄, hk₄, hq₄, hf₄⟩ :=
    hO P W c₃ e₃.wb_right ⟨hge, hn3, hout₃, N', hN₃, hnf₃, hfull₃, hh₃⟩
      (show c₃.nreg ALLOC + κO * (P.n + 1) ≤ W by rw [← hbO]; omega)
  replace hk₄ : k₄ ≤ bO := by rwa [hbO]
  have ha₄ : c₄.nreg ALLOC ≤ c₃.nreg ALLOC + k₄ := hf₄.2.2.2.2.2.2
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ?_,
    Qof P, shearRel_Qof (hgood P hP), (hsh (epsOf P) P).1 hP, hq₄⟩
  · rw [hC]; omega
  · rw [hC]; omega

end

end Chazelle.Core

namespace Chazelle.Core

end Chazelle.Core
