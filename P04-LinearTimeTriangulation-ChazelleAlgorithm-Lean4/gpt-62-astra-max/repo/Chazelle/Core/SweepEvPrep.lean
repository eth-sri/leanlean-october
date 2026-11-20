module

public import Chazelle.Core.SweepEvTasks3

/-!
# The sweep (WP-D), stage 3: the preparation (task P)

`prep`: from a configuration whose allocator is the table base `cTB`, zero the `6 K₂` words of the
endpoint table (in particular the flags at `cTB + 3 j`, `j < 2 K₂`), raising the allocator past
the table one word at a time; then set the log base `lB` to the allocator, `lC = 0`, and raise the
allocator by `7 · 16 (K₁ + K₂ + 1)` words (one word per step, like `put4`).

`prepTask : PrepTask` (cost `400 (K₁ + K₂ + 1)`).  Scratch registers `sw 2480 … 2490` (`PR`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## Registers and program -/

/-- The chord counts `K₂`, `K₁`, the table end, the sum `K₁ + K₂ + 1` and its multiples, the log
end. -/
def pK2 : ℕ := sw 2480
def pK1 : ℕ := sw 2481
def pT : ℕ := sw 2482
def pS : ℕ := sw 2483
def p2 : ℕ := sw 2484
def p4 : ℕ := sw 2485
def p8 : ℕ := sw 2486
def p16 : ℕ := sw 2487
def p32 : ℕ := sw 2488
def p64 : ℕ := sw 2489
def pU : ℕ := sw 2490

/-- The head: read `K₂`, `K₁`; the table end `pT = ALLOC + 6 K₂`. -/
def prepHead : List Instr :=
  [.loadN pK2 (sw 4), .loadN pK1 (sw 3), .copyN pT ALLOC, .addN pT pT pK2, .addN pT pT pK2,
    .addN pT pT pK2, .addN pT pT pK2, .addN pT pT pK2, .addN pT pT pK2]

/-- Zero the table, one word per iteration. -/
def zeroLoop : Stmt :=
  .whileLtN ALLOC pT (.seq (.instr (.storeN ALLOC K0)) (.instr (.addN ALLOC ALLOC K1)))

/-- The middle: `lB`, `lC`, and the log end `pU = ALLOC + 112 (K₁ + K₂ + 1)`. -/
def prepMid : List Instr :=
  [.copyN lB ALLOC, .copyN lC K0, .addN pS pK1 pK2, .addN pS pS K1, .addN p2 pS pS,
    .addN p4 p2 p2, .addN p8 p4 p4, .addN p16 p8 p8, .addN p32 p16 p16, .addN p64 p32 p32,
    .copyN pU ALLOC, .addN pU pU p16, .addN pU pU p32, .addN pU pU p64]

/-- Raise the allocator to `pU`, one word per iteration. -/
def allocLoop : Stmt := .whileLtN ALLOC pU (.instr (.addN ALLOC ALLOC K1))

/-- **The preparation.** -/
def prep : Stmt := .seq (block prepHead) (.seq zeroLoop (.seq (block prepMid) allocLoop))

/-! ## Steps -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- One word of allocation. -/
theorem allocOne_irs (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1) (hroom : c.nreg ALLOC + 1 ≤ W) :
    IRS P W c₀ (.instr (.addN ALLOC ALLOC K1)) c 1
      (fun c' => c' = { c with nreg := upd c.nreg ALLOC (c.nreg ALLOC + 1) }) := by
  have ex := Exec.addN (P := P) hI.hw ALLOC ALLOC K1 (by rw [hK1]; exact hroom)
  rw [hK1] at ex
  exact IRS.ofExec hI ex le_rfl (fun r _ hr => upd_other _ _ _ hr) rfl (fun _ _ => rfl) rfl rfl
    (by simp) (by simp) rfl

/-- The zeroing loop. -/
theorem zeroLoop_irs (hI : IInv W c₀ c) (hK : Consts c) {T : ℕ} (hT : c.nreg pT = T)
    (hAT : c.nreg ALLOC ≤ T) (hroom : c.nreg ALLOC + 4 * (T - c.nreg ALLOC) ≤ W) :
    IRS P W c₀ zeroLoop c (4 * (T - c.nreg ALLOC) + 2) (fun c' =>
      c'.nreg ALLOC = T ∧ (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ x, c.nreg ALLOC ≤ x → x < T → c'.nmem x = 0) ∧
      (∀ x, x < c.nreg ALLOC → c'.nmem x = c.nmem x)) := by
  set A := c.nreg ALLOC with hA
  have k0 : c.nreg K0 = 0 := hK.1
  have k1 : c.nreg K1 = 1 := hK.2.1
  have nT : pT ≠ ALLOC := by unfold pT ALLOC sw; omega
  have n0 : K0 ≠ ALLOC := by unfold K0 ALLOC sw; omega
  have n1 : K1 ≠ ALLOC := by unfold K1 ALLOC sw; omega
  let I : Config → Prop := fun c' => A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ T ∧
    (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ x, A ≤ x → x < c'.nreg ALLOC → c'.nmem x = 0) ∧
    (∀ x, x < A → c'.nmem x = c.nmem x)
  have hpT : ∀ c', I c' → c'.nreg pT = T := fun c' hc => (hc.2.2.1 _ nT).trans hT
  have h := IRS.while (P := P) (c₀ := c₀) (a := ALLOC) (b := pT)
    (body := .seq (.instr (.storeN ALLOC K0)) (.instr (.addN ALLOC ALLOC K1))) I
    (fun c' => T - c'.nreg ALLOC) 2
    (fun c' hc hlt => by rw [hpT c' hc] at hlt; omega) ?_ hI
    ⟨le_rfl, hAT, fun _ _ => rfl, fun x h1 h2 => by omega, fun _ _ => rfl⟩ (by omega)
  · refine (h.mono (by omega) ?_)
    rintro c' ⟨hc, h6⟩
    rw [hpT c' hc] at h6
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    have e : c'.nreg ALLOC = T := by omega
    exact ⟨e, h3, fun x hx1 hx2 => h4 x hx1 (by omega), h5⟩
  · intro c' hI' hc hlt hroom'
    rw [hpT c' hc] at hlt
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    refine IRS.seq (K₁ := 1) (K₂ := 1) (IRS.store hI' hI'.hA) ?_
    rintro c₁ hI₁ - - rfl
    refine (allocOne_irs hI₁ (by simp only; rw [h3 _ n1, k1]) (by simp only; omega)).mono le_rfl ?_
    rintro c'' rfl
    simp only [I, upd_same]
    refine ⟨⟨by omega, by omega, fun r hr => ?_, fun x hx1 hx2 => ?_, fun x hx => ?_⟩, by omega⟩
    · rw [upd_other _ _ _ hr, h3 r hr]
    · rw [h3 _ n0, k0]
      by_cases hx : x = c'.nreg ALLOC
      · rw [hx, upd_same]
      · rw [upd_other _ _ _ hx]; exact h4 x hx1 (by omega)
    · rw [upd_other _ _ _ (by omega)]; exact h5 x hx

/-- The allocation loop. -/
theorem allocLoop_irs (hI : IInv W c₀ c) (hK : Consts c) {U : ℕ} (hU : c.nreg pU = U)
    (hAU : c.nreg ALLOC ≤ U) (hroom : c.nreg ALLOC + 3 * (U - c.nreg ALLOC) ≤ W) :
    IRS P W c₀ allocLoop c (3 * (U - c.nreg ALLOC) + 2) (fun c' =>
      c'.nreg ALLOC = U ∧ (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  set A := c.nreg ALLOC with hA
  have k1 : c.nreg K1 = 1 := hK.2.1
  have nU : pU ≠ ALLOC := by unfold pU ALLOC sw; omega
  have n1 : K1 ≠ ALLOC := by unfold K1 ALLOC sw; omega
  let I : Config → Prop := fun c' => A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ U ∧
    (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem
  have hpU : ∀ c', I c' → c'.nreg pU = U := fun c' hc => (hc.2.2.1 _ nU).trans hU
  have h := IRS.while (P := P) (c₀ := c₀) (a := ALLOC) (b := pU)
    (body := .instr (.addN ALLOC ALLOC K1)) I (fun c' => U - c'.nreg ALLOC) 1
    (fun c' hc hlt => by rw [hpU c' hc] at hlt; omega) ?_ hI
    ⟨le_rfl, hAU, fun _ _ => rfl, rfl⟩ (by omega)
  · refine (h.mono (by omega) ?_)
    rintro c' ⟨hc, h6⟩
    rw [hpU c' hc] at h6
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨by omega, h3, h4⟩
  · intro c' hI' hc hlt hroom'
    rw [hpU c' hc] at hlt
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine (allocOne_irs hI' (by rw [h3 _ n1, k1]) (by omega)).mono le_rfl ?_
    rintro c'' rfl
    simp only [I, upd_same]
    refine ⟨⟨by omega, by omega, fun r hr => ?_, h4⟩, by omega⟩
    rw [upd_other _ _ _ hr, h3 r hr]

/-- The head. -/
theorem prepHead_irs (hI : IInv W c₀ c) {K₁ K₂ : ℕ} (h2 : c.nmem (c.nreg (sw 4)) = K₂)
    (h1 : c.nmem (c.nreg (sw 3)) = K₁) (hroom : c.nreg ALLOC + 6 * K₂ ≤ W) :
    IRS P W c₀ (block prepHead) c 9 (fun c' => c'.nreg pK2 = K₂ ∧ c'.nreg pK1 = K₁ ∧
      c'.nreg pT = c.nreg ALLOC + 6 * K₂ ∧
      (∀ r, r ≠ pK2 → r ≠ pK1 → r ≠ pT → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  simp only [sw, ALLOC] at h1 h2 hroom
  refine (IRS.block prepHead hI ?_).mono le_rfl ?_
  · simp [prepHead, okB, okI, regI, upd, pK2, pK1, pT, sw, ALLOC, IScr, h2]
    omega
  · rintro c' rfl
    simp [prepHead, regB, regI, upd, pK2, pK1, pT, sw, ALLOC, h1, h2]
    refine ⟨by omega, ?_⟩
    intro r ha hb hc
    simp [ha, hb, hc]

/-- The middle block. -/
theorem prepMid_irs (hI : IInv W c₀ c) (hK : Consts c) {K₁ K₂ : ℕ} (h1 : c.nreg pK1 = K₁)
    (h2 : c.nreg pK2 = K₂) (hroom : c.nreg ALLOC + 112 * (K₁ + K₂ + 1) ≤ W) :
    IRS P W c₀ (block prepMid) c 14 (fun c' => c'.nreg lB = c.nreg ALLOC ∧ c'.nreg lC = 0 ∧
      c'.nreg pU = c.nreg ALLOC + 112 * (K₁ + K₂ + 1) ∧
      (∀ r, r ≠ lB → r ≠ lC → (r < pS ∨ pU < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have k0 : c.nreg K0 = 0 := hK.1
  have k1 : c.nreg K1 = 1 := hK.2.1
  simp only [K0, K1, sw, ALLOC, pK1, pK2] at h1 h2 hroom k0 k1
  refine (IRS.block prepMid hI ?_).mono le_rfl ?_
  · simp [prepMid, okB, okI, regI, upd, pK2, pK1, pS, p2, p4, p8, p16, p32, p64, pU, lB, lC, sw,
      ALLOC, IScr, K0, K1, h1, h2, k1]
    omega
  · rintro c' rfl
    simp [prepMid, regB, regI, upd, pK2, pK1, pS, p2, p4, p8, p16, p32, p64, pU, lB, lC, sw,
      ALLOC, K0, K1, h1, h2, k0, k1]
    refine ⟨by omega, ?_⟩
    intro r ha hb hc
    split_ifs <;> first | rfl | omega

theorem nw₁' {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    {J : Merge.Junction} {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂)
    (hI : IInv W c₀ c) : NFWithin c.nmem (c.nreg (sw 3)) (c.nreg ALLOC) N₁ := by
  rw [hI.hin _ (by unfold IFix sw; omega)]
  exact (E.hNW₁.transport (fun a ha => hI.hm a ha)).mono hI.hA

/-- **Task P: the preparation.** -/
theorem prepTask : PrepTask := by
  refine ⟨prep, 400, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hAc hroom
  have hK : Consts c := E.hK.fix hI
  have h2 : c.nmem (c.nreg (sw 4)) = N₂.nChords := (E.nw₂' hI).nfAt.1
  have h1 : c.nmem (c.nreg (sw 3)) = N₁.nChords := (nw₁' E hI).nfAt.1
  set K₁ := N₁.nChords with hK₁
  set K₂ := N₂.nChords with hK₂
  set t := K₁ + K₂ + 1 with ht
  set A := c.nreg ALLOC with hA
  have hTB : c.nreg cTB = A := hAc.symm
  refine IRS.mono (K := 9 + ((4 * (A + 6 * K₂ - A) + 2) + (14 + (3 * (A + 6 * K₂ + 112 * t -
    (A + 6 * K₂)) + 2)))) ?_ (by omega) (fun _ h => h)
  refine IRS.seq (prepHead_irs hI h2 h1 (by omega)) ?_
  rintro c₁ hI₁ - - ⟨a2, a1, aT, afr, am⟩
  have nA : ∀ r, r = ALLOC → r ≠ pK2 ∧ r ≠ pK1 ∧ r ≠ pT := by
    rintro r rfl; unfold ALLOC pK2 pK1 pT sw; omega
  have e1A : c₁.nreg ALLOC = A := afr _ (nA _ rfl).1 (nA _ rfl).2.1 (nA _ rfl).2.2
  have hK₁' : Consts c₁ := E.hK.fix hI₁
  refine IRS.seq ((zeroLoop_irs hI₁ hK₁' aT (by omega) (by omega)).mono
    (K' := 4 * (A + 6 * K₂ - A) + 2) (by omega) (fun _ h => h)) ?_
  rintro c₂ hI₂ - - ⟨z1, z2, z3, z4⟩
  rw [e1A] at z3 z4
  have hK₂' : Consts c₂ := E.hK.fix hI₂
  have nk1 : pK1 ≠ ALLOC := by unfold pK1 ALLOC sw; omega
  have nk2 : pK2 ≠ ALLOC := by unfold pK2 ALLOC sw; omega
  refine IRS.seq (prepMid_irs hI₂ hK₂' (by rw [z2 _ nk1, a1]) (by rw [z2 _ nk2, a2])
    (by rw [z1]; omega)) ?_
  rintro c₃ hI₃ - - ⟨m1, m2, m3, m4, m5⟩
  rw [z1] at m1 m3
  have e3A : c₃.nreg ALLOC = A + 6 * K₂ := by
    rw [m4 _ (by unfold lB ALLOC sw; omega) (by unfold lC ALLOC sw; omega)
      (by left; unfold pS ALLOC sw; omega), z1]
  refine (allocLoop_irs hI₃ (E.hK.fix hI₃) m3 (by omega) (by omega)).mono (by omega) ?_
  rintro c' ⟨f1, f2, f3⟩
  have nlB : lB ≠ ALLOC := by unfold lB ALLOC sw; omega
  have nlC : lC ≠ ALLOC := by unfold lC ALLOC sw; omega
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, fun x hx => ?_, fun r hr hpr hra => ?_⟩
  · rw [f3, m5, hTB]; exact z3 _ (by omega) (by omega)
  · rw [f2 _ nlB, m1, hTB]
  · rw [f2 _ nlC, m2]
  · rw [f2 _ nlB, m1, f1]; omega
  · rw [f3, m5, z4 x hx, am]
  · unfold PR at hpr
    push Not at hpr
    rw [f2 r hra, m4 r hpr.1 hpr.2.1 (by unfold pS pU sw at *; omega), z2 r hra,
      afr r (by unfold pK2 sw at *; omega) (by unfold pK1 sw at *; omega)
        (by unfold pT sw at *; omega)]

end

end SweepEv

end Chazelle.Core
