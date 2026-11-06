module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFBuildZero
public import Chazelle.Core.NFBuildPhaseA
public import Chazelle.Core.NFBuildSpec

/-!
# WP-C (BuildNF), RAM part 26: the procedure and `BuildNFSpec`

`buildStmt`: for `K > 0`, phase A (records, sort of the event codes by `codeLe`) then phase B
(main pass, regions, layout); for `K = 0`, `zeroCase`.

* `buildNFRam : BuildNF.BuildNFRamSpec`;
* **`Chazelle.Core.buildNF : BuildNFSpec`** (with `BuildNF.buildNFSpec_of_ram`).
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK NFLoc SortL
open BuildNF (codeLe)

@[expose] public section

/-- **The procedure of `BuildNFSpec`.** -/
def buildStmt : Stmt :=
  .seq (.instr (.constN 43250 0)) (.ifLtN 43250 40002 (.seq phaseA phaseB) zeroCase)

/-- The constant of the cost bound. -/
def κBuild : ℕ := 70000

theorem clog_two_mul_le (K : ℕ) : Nat.clog 2 (2 * K) ≤ Nat.clog 2 K + 1 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.le_pow_clog (by norm_num : 1 < 2) K
  omega

theorem sortCost_le (K : ℕ) :
    SortR.sortCost 11010 (2 * K) ≤ 44160 * (K * (Nat.clog 2 K + 1) + 1) := by
  unfold SortR.sortCost
  have h1 := clog_two_mul_le K
  have h2 : 2 * K * (Nat.clog 2 (2 * K) + 1) ≤ 2 * K * (Nat.clog 2 K + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  grind

theorem seg_getD {m : ℕ → ℕ} {a n : ℕ} {E : List ℕ} (h : seg m a n = E) {j : ℕ} (hj : j < n) :
    m (a + j) = E.getD j 0 := by
  core_grind

/-! ## Separate write sets with natural stores -/

/-- The instruction writes a natural register in `BN` (or natural memory) or a real one in
`BR`. -/
def wrOKM2 (BN BR : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | .inputSize r | .constN r _ | .copyN r _ | .addN r _ _ | .subN r _ _ | .loadN r _ => BN r
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => BR r
  | .loadR r _ | .readX r _ | .readY r _ => BR r
  | _ => false

/-- Every instruction satisfies `wrOKM2 BN BR`. -/
def wrM2 (BN BR : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOKM2 BN BR i
  | .seq s t => wrM2 BN BR s && wrM2 BN BR t
  | .ifLtN _ _ t e => wrM2 BN BR t && wrM2 BN BR e
  | .ifLtR _ _ t e => wrM2 BN BR t && wrM2 BN BR e
  | .whileLtN _ _ b => wrM2 BN BR b
  | .whileLtR _ _ b => wrM2 BN BR b

/-- **The real registers outside `BR` are unchanged.** -/
theorem exec_frameM2 {P : Polygon} {W : ℕ} {BN BR : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrM2 BN BR s = true) :
    ∀ r, BR r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => simp_all
  | @instr ins c c' _ he _ _ =>
    simp only [wrM2] at hs
    cases ins <;> simp only [wrOKM2, Bool.false_eq_true] at hs <;>
      simp only [Instr.effect, Option.some.injEq] at he <;>
      (try split at he) <;> simp_all <;> subst he <;>
      intro j hj <;>
      aesop (add simp [upd]) (add safe (by omega))
  | seq _ _ ih₁ ih₂ =>
    simp_all [wrM2, Bool.and_eq_true] <;> omega_nf
  | ifLtN_true _ _ ih =>
    simp_all [wrM2, Bool.and_eq_true] <;> omega_nf
  | ifLtN_false _ _ ih =>
    simp_all [wrM2, Bool.and_eq_true] <;> omega_nf
  | ifLtR_true _ _ ih =>
    simp_all [wrM2, Bool.and_eq_true] <;> omega_nf
  | ifLtR_false _ _ ih =>
    simp_all [wrM2, Bool.and_eq_true] <;> omega_nf
  | whileLtN_false _ _ => simp_all
  | whileLtN_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans (ih₁ hs r hr)
  | whileLtR_false _ _ => simp_all
  | whileLtR_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans (ih₁ hs r hr)

theorem wrM2_of_wrM {B BN BR : ℕ → Bool} (hN : ∀ r, B r = true → BN r = true)
    (hR : ∀ r, B r = true → BR r = true) {s : Stmt} (h : wrM B s = true) :
    wrM2 BN BR s = true := by
  induction s with
  | skip => rfl
  | instr i =>
    simp only [wrM] at h; simp only [wrM2]
    cases i <;> simp only [wrOKM, wrOK] at h <;> simp only [wrOKM2] <;>
      first | exact hN _ h | exact hR _ h | exact h
  | seq s t ihs iht =>
    simp_all [wrM, Bool.and_eq_true, wrM2, Bool.and_self] <;> omega_nf
  | ifLtN a b s t ihs iht =>
    simp_all [wrM, Bool.and_eq_true, wrM2, Bool.and_self] <;> omega_nf
  | ifLtR a b s t ihs iht =>
    simp_all [wrM, Bool.and_eq_true, wrM2, Bool.and_self] <;> omega_nf
  | whileLtN a b s ih => simp_all [wrM, wrM2] 
  | whileLtR a b s ih => simp_all [wrM, wrM2] 

theorem wrM2_phaseB : wrM2 BphaseB BRb phaseB = true := by
  have h1 : wrM2 BphaseB BRb setupB = true := by decide
  have h2 : wrM2 BphaseB BRb lohiS = true := by decide
  have h3 : wrM2 BphaseB BRb passLoop = true := by
    refine wrM2_of_wrM (B := Bpass) (fun r hr => ?_) (fun r hr => ?_) ?_
    · cases hb : Bpass r
      · simp_all
      · by_contra hc
        simp only [BphaseB, decide_eq_true_eq, not_or, not_and, not_lt] at hc
        have : Bpass r = false := Bpass_false (by omega)
        simp_all
    · cases hb : Bpass r
      · simp_all
      · by_contra hc
        have hc' : ¬ (r / 10000 = 1 ∨ r / 10000 = 4) := fun h' => hc (by
          unfold BRb bandOf bSign bBuild; simp_all)
        have : Bpass r = false := Bpass_false (by omega)
        simp_all
    · simp only [passLoop, wrM]; exact wr_passBody
  have h4 : wrM2 BphaseB BRb regPhase = true := wrM2_of_wrM (B := BregPhase)
    (fun r hr => by
      simp only [BregPhase, Bool.or_eq_true, decide_eq_true_eq] at hr
      simp only [BphaseB, decide_eq_true_eq]; omega)
    (fun r hr => by
      simp only [BregPhase, Bool.or_eq_true, decide_eq_true_eq] at hr
      unfold BRb bandOf bSign bBuild; grind) wr_regPhase
  simp_all [phaseB, phaseB1, wrM2, Bool.and_self] 

theorem wrM2_zeroCase : wrM2 BphaseB BRb zeroCase = true := by decide

section
variable {r : ℕ} (hr : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ))
include hr
theorem BphaseB_false
    (hra : r ≠ ALLOC) : BphaseB r = false := by
  simp_all [Finset.mem_insert, Finset.mem_singleton, bandOf, bBuild, bSort, bSign, ALLOC, BphaseB, decide_eq_false_iff_not] <;> omega_nf

theorem BRb_false :
    BRb r = false := by
  simp_all [Finset.mem_insert, Finset.mem_singleton, bandOf, bBuild, bSort, bSign, BRb, decide_eq_false_iff_not] 


end

/-- A register frame of phase B gives the frame of the specification. -/
theorem frame_of_frameM {c c' : Config} {k : ℕ} (F : FrameM BphaseB c c')
    (hR : ∀ r, BRb r = false → c'.rreg r = c.rreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (h1 : c.nreg ALLOC ≤ c'.nreg ALLOC) (h2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) :
    Frame {bBuild, bSort, bSign} c c' k :=
  ⟨fun r hr hra => F.1 r (BphaseB_false hr hra), fun r hr => hR r (BRb_false hr),
    hm, fun a _ => by rw [F.2.2.1], F.2.2.2, h1, h2⟩

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The RAM part of `BuildNFSpec`.** -/
theorem buildNFRam : BuildNF.BuildNFRamSpec := by
  unfold BuildNF.BuildNFRamSpec
  refine ⟨buildStmt, κBuild, ?_⟩
  intro P W c hw hpre hcost
  obtain ⟨hG, hWn, hwf, M, L, hM, hgood, hlen, hBL, hCL, hok⟩ := hpre
  simp only [rd, bandReg, bBuild] at hwf hM hlen hBL hCL ⊢
  norm_num at hwf hM hlen hBL hCL ⊢
  set K := L.length with hKdef
  set A₀ := c.nreg ALLOC with hA₀
  have hA : c.nreg 9999 = A₀ := rfl
  have hX : 1 ≤ K * (Nat.clog 2 K + 1) + 1 := by omega
  have hKX : K ≤ K * (Nat.clog 2 K + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hcost' : A₀ + κBuild * (K * (Nat.clog 2 K + 1) + 1) ≤ W := by
    simp_all [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd] 
  have hsc := sortCost_le K
  unfold κBuild at hcost'
  -- the first instruction
  have x₀ := Exec.constN (P := P) hw 43250 0 (Nat.zero_le _)
  set c₀ : Config := { c with nreg := upd c.nreg 43250 0 } with hc₀
  have w₀ := x₀.wb_right
  have g₀ : ∀ r, r ≠ 43250 → c₀.nreg r = c.nreg r := fun r hr => by ram_simp
  by_cases hK : 0 < K
  · -- phase A
    have t₀ : c₀.nreg 43250 < c₀.nreg 40002 := by
      ram_simp
    obtain ⟨c₁, k₁, x₁, hk₁, w₁, F₁, d1, d2, d3, d4, d5, d6, d7, hrec, e1, e2, E, hE, hperm,
      hsort⟩ := phaseA_exec (P := P) hG hWn c₀ w₀ (M := M) (L := L) (D := c.nreg 40000)
        (B := c.nreg 40001) hwf hM hok hCL hBL (g₀ _ (by norm_num)) (g₀ _ (by norm_num))
        (by ram_simp)
        (by ram_grind)
    have hc0A : c₀.nreg ALLOC = A₀ := g₀ 9999 (by norm_num)
    rw [hc0A] at d2 hrec e1
    have hm₀ : c₀.nmem = c.nmem := by rw [hc₀]
    set SE := c₁.nreg 30005 with hSEdef
    set H := c₁.nreg 9999 with hHdef
    have e2' : SE + 2 * K ≤ H := e2
    have hElen : E.length = 2 * K := by rw [hperm.length_eq, List.length_range]
    have hlow₁ : ∀ a, a < A₀ → c₁.nmem a = c.nmem a := fun a ha => by
      rw [F₁.2.2.1 a (by omega), hm₀]
    have hAH : A₀ ≤ H := by omega
    have hHk : H ≤ A₀ + k₁ := by have := F₁.2.2.2.2.2.2; rw [hc0A] at this; exact this
    obtain ⟨hM₁, hwf₁⟩ := desc_agree hwf hM hlow₁
    have hI : BuildNF.Input M (Qof P) L E :=
      ⟨walkAx_of_goodModel hgood, hok, hperm,
        BuildNF.sorted_of_codeLe (walkAx_of_goodModel hgood) hok hperm hsort⟩
    have hCL₁ : ChordListAt c₁.nmem (c.nreg 40001) L := fun i hi => by
      obtain ⟨a1, a2, a3⟩ := hCL i hi
      grind
    obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, F₂, h40003, h9999, hlow, hNF⟩ := phaseB_exec (P := P) hG
      hWn c₁ w₁ (M := M) (L := L) (E := E) (D := c.nreg 40000) (T := A₀) (SE := SE)
      (B := c.nreg 40001) (H := H) hI hK d1 d2 d3 d4 d5 d6 d7 rfl rfl
      (modelDescWF_mono hwf₁ hAH) hM₁ hrec (by omega) hCL₁ (by omega)
      (fun j hj => seg_getD hE (by omega)) (by omega)
      (by grind [sizeB, costA])
    have X : Exec P W buildStmt c c₂ (1 + (k₁ + k₂ + 1)) :=
      .seq x₀ (.ifLtN_true t₀ (.seq x₁ x₂))
    refine ⟨c₂, _, X, ?_, fun M' L' hM' hlen' hL' => ?_, ?_⟩
    · rw [hlen]; unfold costA at hk₁; unfold κBuild; nlinarith
    · obtain rfl := NFLoc.modelDesc_unique hM hM'
      obtain rfl := BuildNF.chordListAt_unique hCL hL' (hlen.symm.trans hlen')
      exact ⟨E, hperm, hsort, by omega, by ram_grind⟩
    · refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
      · rw [F₂.1 r (BphaseB_false hr hra), F₁.1 r hr hra, g₀ r (by
          grind [bandOf, bSort, bSign])]
      · rw [exec_frameM2 x₂ wrM2_phaseB r (BRb_false hr), F₁.2.1 r hr]
      · grind
      · rw [F₂.2.2.1, F₁.2.2.2.1 a (by omega)]
      · rw [F₂.2.2.2, F₁.2.2.2.2.1]
      · omega_nf
      · omega_nf
  · -- `K = 0`
    have hK0 : K = 0 := by omega
    have t₀ : ¬ c₀.nreg 43250 < c₀.nreg 40002 := by
      ram_simp
    obtain ⟨c', k, x, hk, hk', w', F', h40003, h9999, hlow, hNF⟩ := zeroCase_exec (P := P) hWn c₀
      w₀ (M := M) (L := L) (E := []) (D := c.nreg 40000) (H := A₀) hK0
      (g₀ _ (by norm_num)) (by ram_simp) hwf hM (by nlinarith)
    have X : Exec P W buildStmt c c' (1 + (k + 2)) := .seq x₀ (.ifLtN_false t₀ x)
    refine ⟨c', _, X, by omega_nf, fun M' L' hM' hlen' hL' => ?_, ?_⟩
    · obtain rfl := NFLoc.modelDesc_unique hM hM'
      obtain rfl := BuildNF.chordListAt_unique hCL hL' (hlen.symm.trans hlen')
      refine ⟨[], by grind, List.Pairwise.nil, by rw [h40003], ?_⟩
      rw [h40003]; exact hNF
    · have F₀ : FrameM BphaseB c c₀ := exec_frameM x₀ (by decide)
      have R' : ∀ r, BRb r = false → c'.rreg r = c.rreg r := fun r hr =>
        (exec_frameM2 x wrM2_zeroCase r hr).trans (by rw [hc₀])
      refine frame_of_frameM (F₀.trans F') R' (fun a ha => by ram_simp) ?_ ?_
      · omega_nf
      · omega_nf

end exec

end

end BuildRam

end Chazelle.Core

namespace Chazelle.Core

@[expose] public section

/-- **WP-C: `BuildNFSpec`.** -/
theorem buildNF : BuildNFSpec := BuildNF.buildNFSpec_of_ram BuildRam.buildNFRam

end

end Chazelle.Core
