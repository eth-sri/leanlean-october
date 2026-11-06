module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRTailSpec
public import Chazelle.Core.DownPhaseDrvRLvC
public import Chazelle.Core.DownPhaseDrvRCostSpec
public import Chazelle.Core.DownPhaseDrvBSize
public import Chazelle.Core.DownPhaseMathRec
public import Chazelle.Core.RestoreTKey
public import Chazelle.Core.Setup

/-!
# Down-phase driver: one level from its parts (`LevelSpec`)

`levelSpec_of_loop`: the program `lvPar ; lvLoop sH sR sX ; sT` meets `DrvR.LevelSpec (gradeCtx O)
DrvR.lvCnt n₀` (`n₀` from `LvCostSpec` (a)) given the region loop's contract `LoopOK` (the
statement of `DrvR.lvLoop_exec`), the tail `LvTailSpec O` and the level cost `LvCostSpec`:

1. `lvPar_exec` (parameters, region table);
2. the context `LvCtx` at the configuration after `lvPar` (`ctx_of`): the region correspondence
   from `IsNF` of the build (`DownMath.isNF_build`), `L ≠ []` (`DrvB.n_le_of_empty` and the
   threshold), the bounds `big`, `big2` (the threshold), the `LeftInside` bit from the interior
   model descriptor;
3. the loop invariant at `j = 0` (`lvInv_zero`);
4. the loop, the tail, the frame and the cost (`lv_cost`).
-/

namespace Chazelle.Core

namespace DrvLS

open Machine Machine.Stmt Programs
open BuildNF (codeLe)
open SortL (seg)
open DrvR

@[expose] public section

/-- The step bound of one region (the `Kb` of `lvLoop_exec`). -/
noncomputable def lvKb (κH κR κX lam : ℕ) : ℕ :=
  30 + κH + κR * (lemma41Nat (nextLvl lam) + 1) + κX * (lvNch (nextLvl lam) + 1) +
    lvNch (nextLvl lam)

/-- **The contract of the region loop** (the statement of `DrvR.lvLoop_exec`). -/
def LoopOK (O : OracleIface) (sH sR sX : Stmt) (κH κR κX : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c₁ c : Config) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
    (reg : ℕ → Set Point) (lam Kb : ℕ),
    LvCtx O P W c₁ L E reg lam →
    30 + κH + κR * (lemma41Nat (nextLvl lam) + 1) + κX * (lvNch (nextLvl lam) + 1) +
      lvNch (nextLvl lam) ≤ Kb →
    c₁.nreg ALLOC + (L.length + 1) * Kb ≤ W →
    LvInv O P W c₁ L E reg Kb 0 c →
    ∃ c' k, Exec P W (lvLoop sH sR sX) c c' k ∧ LvInv O P W c₁ L E reg Kb (L.length + 1) c' ∧
      k ≤ (Kb + 2) * (L.length + 1) + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

theorem nextLvl_ge {lam : ℕ} (h : 16 ≤ lam) : 15 ≤ nextLvl lam := by
  unfold nextLvl
  have := ceilBeta_mono h
  have e : Cost.ceilBeta 16 = 4 := Ρ Setup.ceilBeta_eq
  omega

/-- The arithmetic of the cost of one level. -/
theorem lv_cost (K X κH κR κX κc κT N Kb : ℕ) (hX : 1 ≤ X) (hN : N ≤ κc * X)
    (hKb : Kb = 30 + κH + κR * X + κX * (N + 1) + N) :
    9 * (K + 1) + 48 + (Kb + 2) * (K + 1) + κT * (K + 1) * X ≤
      (89 + κH + κR + κX + κX * κc + κc + κT) * ((K + 1) * X) := by
  have h1 : Kb + 2 ≤ (32 + κH + κR + κX + κX * κc + κc) * X := by
    Ξ hKb
    have a1 : κH ≤ κH * X := Nat.le_mul_of_pos_right _ hX
    have a2 : κX * (N + 1) ≤ κX * κc * X + κX * X := by
      have : κX * (N + 1) ≤ κX * (κc * X + X) := Nat.mul_le_mul_left _ (⋄)
      calc κX * (N + 1) ≤ κX * (κc * X + X) := this
        _ = κX * κc * X + κX * X := ⋆
    have e : (32 + κH + κR + κX + κX * κc + κc) * X =
        32 * X + κH * X + κR * X + κX * X + κX * κc * X + κc * X := ⋆
    Ξ e
    generalize κH * X = a at *
    generalize κR * X = b at *
    generalize κX * κc * X = d at *
    generalize κX * X = f at *
    generalize κc * X = g at *
    generalize κX * (N + 1) = h at *
    omega
  have h2 : (Kb + 2) * (K + 1) ≤ (32 + κH + κR + κX + κX * κc + κc) * ((K + 1) * X) := by
    calc (Kb + 2) * (K + 1) ≤ (32 + κH + κR + κX + κX * κc + κc) * X * (K + 1) :=
          Nat.mul_le_mul_right _ h1
      _ = _ := ⋆
  have h3 : 9 * (K + 1) + 48 ≤ 57 * ((K + 1) * X) := by
    have : K + 1 ≤ (K + 1) * X := Nat.le_mul_of_pos_right _ hX
    omega
  have e : (89 + κH + κR + κX + κX * κc + κc + κT) * ((K + 1) * X) =
      57 * ((K + 1) * X) + (32 + κH + κR + κX + κX * κc + κc) * ((K + 1) * X) +
        κT * (K + 1) * X := ⋆
  Ξ e
  generalize (32 + κH + κR + κX + κX * κc + κc) * ((K + 1) * X) = u at *
  generalize κT * (K + 1) * X = v at *
  generalize (Kb + 2) * (K + 1) = w at *
  generalize (K + 1) * X = y at *
  omega

theorem rd21 (c : Config) (i : ℕ) : rd c bDownDrv i = c.nreg (210000 + i) := rfl

/-- `L ≠ []` above the threshold. -/
theorem ne_nil_of_big {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {lam : ℕ}
    (hG : GoodEnv P) (hperm : E.Perm (List.range (2 * L.length)))
    (hwt : (interiorModel (Qof P)).Semigranular
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P))
      (2 ^ (Cost.ceilBeta lam + 12)))
    (hlp : lam ≤ topGrade P.n)
    (hbig : 2 ^ (Cost.ceilBeta (topGrade P.n) + 13) + 200 ≤ P.n) : L ≠ [] := by
  intro hL
  subst hL
  have hE : E = [] := by simpa using hperm
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have h := DrvB.n_le_of_empty hQ hE hwt
  have hn : (Qof P).n = P.n := shear_n _ _
  Ξ' hn at h
  have h1 : 2 ^ (Cost.ceilBeta lam + 12) ≤ 2 ^ (Cost.ceilBeta (topGrade P.n) + 12) :=
    Nat.pow_le_pow_right (⊛) (by have := ceilBeta_mono hlp; omega)
  have h2 : 2 ^ (Cost.ceilBeta (topGrade P.n) + 13) = 2 * 2 ^ (Cost.ceilBeta (topGrade P.n) + 12) := by
    rw [pow_succ]; ring
  omega

/-- The bounds `big`, `big2` of the context above the threshold. -/
theorem big_of {n lam : ℕ} (h16 : 16 ≤ lam) (hlp : lam ≤ topGrade n)
    (hbig : 2 ^ (Cost.ceilBeta (topGrade n) + 13) + 200 ≤ n) :
    3 * 2 ^ (Cost.ceilBeta (nextLvl lam) + 10) + 129 ≤ n - 1 ∧
      2 ^ (Cost.ceilBeta (nextLvl lam) + 12) ≤ n - 1 := by
  have hμ := nextLvl_lt h16
  have hc : Cost.ceilBeta (nextLvl lam) ≤ Cost.ceilBeta (topGrade n) :=
    ceilBeta_mono (⋄)
  have h1 : 2 ^ (Cost.ceilBeta (nextLvl lam) + 12) ≤ 2 ^ (Cost.ceilBeta (topGrade n) + 12) :=
    Nat.pow_le_pow_right (⊛) (⋄)
  have h2 : 2 ^ (Cost.ceilBeta (topGrade n) + 13) = 2 * 2 ^ (Cost.ceilBeta (topGrade n) + 12) := by
    rw [pow_succ]; ring
  have h3 : 2 ^ (Cost.ceilBeta (nextLvl lam) + 12) = 4 * 2 ^ (Cost.ceilBeta (nextLvl lam) + 10) := by
    rw [show Cost.ceilBeta (nextLvl lam) + 12 = Cost.ceilBeta (nextLvl lam) + 10 + 2 by omega,
      pow_add]; ring
  omega

/-- The `LeftInside` bit of the interior model descriptor. -/
theorem li_of_desc {m : ℕ → ℕ} {B : ℕ} {Q : Polygon}
    (h : ModelDescAt m B Q (interiorModel Q)) : m (B + 1) = 1 ↔ Mountain.LeftInside Q := by
  rcases h with ⟨-, H, C, -, hM⟩ | ⟨-, hli, -⟩
  · exact absurd hM.symm (Restore.chainModel_ne_interior C Q)
  · exact hli

/-- The constant of a level. -/
def κLv (κH κR κX κc κT : ℕ) : ℕ := 89 + κH + κR + κX + κX * κc + κc + κT


/-- **One level from its parts**, given the region loop's contract. -/
theorem levelSpec_of_loop {O : OracleIface} {sH sR sX : Stmt} {κH κR κX : ℕ}
    (hloop : LoopOK O sH sR sX κH κR κX) (hT : LvTailSpec O) (hC : LvCostSpec) :
    ∃ n₀, LevelSpec (gradeCtx O) lvCnt n₀ := by
  obtain ⟨⟨n₀, hn₀⟩, hb⟩ := hC
  obtain ⟨κc, hκc⟩ := hb 0
  obtain ⟨sT, κT, hTm⟩ := hT
  refine ⟨n₀, .seq lvPar (.seq (lvLoop sH sR sX) sT), κLv κH κR κX κc κT,
    fun P W c hw hpre hroom => ?_⟩
  obtain ⟨hE, hn, h16, hlp, hInv⟩ := hpre
  beta_reduce at hroom ⊢
  obtain ⟨hG, hW3, hWh, hS, hXh, hcap⟩ := hE
  obtain ⟨lam, hlam⟩ : ∃ lam, c.nreg 210000 = lam := ⟨_, rfl⟩
  simp only [rd21, Nat.reduceAdd] at h16 hlp hInv hroom
  rw [hlam] at h16 hlp hInv hroom
  obtain ⟨hD, hDa, L, E, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hN, hdeg, hwt, hcnt⟩ := hInv
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  obtain ⟨-, -, -, reg, g1, g2, g3, g4, -⟩ := DownMath.isNF_build hQ hok hperm hsort
  set X := lemma41Nat (nextLvl lam) + 1 with hX
  set K := L.length with hKdef
  have hX1 : 1 ≤ X := by omega
  have hμ15 := nextLvl_ge h16
  have hNc : lvNch (nextLvl lam) ≤ κc * X := (hκc _ hμ15).1
  set Kb := lvKb κH κR κX lam with hKb
  have hcost := lv_cost K X κH κR κX κc κT (lvNch (nextLvl lam)) Kb hX1 hNc rfl
  have hκ : κLv κH κR κX κc κT = 89 + κH + κR + κX + κX * κc + κc + κT := rfl
  rw [← hκ] at hcost
  have hK' : c.nreg 210003 = K := hK
  replace hroom : c.nreg ALLOC + κLv κH κR κX κc κT * ((K + 1) * X) ≤ W := by
    rw [hK'] at hroom; exact hroom
  have hW11 : 11 ≤ W := by unfold hostWords at hWh; omega
  -- 1. the parameters
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a06, a07, b08, b08', a14, a15, a16, a17, d09,
    d11, d99, d10, d12, d13, w₁, hreg, hmm, F₁⟩ := lvPar_exec (P := P) c hw (S := c.nreg 230000)
      (n := P.n) rfl hlam (MD := c.nreg 210001) rfl (K := K) hK' hS.holds h16 hlp hD
      (by generalize κLv κH κR κX κc κT * ((K + 1) * X) = u at hcost hroom
          generalize (Kb + 2) * (K + 1) = v at hcost
          generalize κT * (K + 1) * X = w at hcost
          omega) hW11
  have keep : ∀ q, 210000 ≤ q → q ≤ 210005 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    hreg q (by omega) (by omega) (by omega) (by unfold ALLOC; omega)
  have k230 : ∀ q, 230000 ≤ q → q ≤ 230001 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    hreg q (by omega) (by omega) (by omega) (by unfold ALLOC; omega)
  have hc0 : c₁.nreg (coreReg 0) = c.nreg (coreReg 0) := k230 230000 le_rfl (by norm_num)
  have hc1 : c₁.nreg (coreReg 1) = c.nreg (coreReg 1) := k230 230001 (by norm_num) le_rfl
  -- 2. the context
  have ctx : LvCtx O P W c₁ L E reg lam := by
    refine ⟨hG, hW3, hWh, ?_, ?_, ?_, h16, hlp, ne_nil_of_big hG hperm hwt hlp (hn₀ _ hn), hok,
      hperm, hsort, hdeg, hwt, ⟨g1, g2, g3, g4⟩, ?_, by rw [keep _ le_rfl (by norm_num), hlam],
      a02, a04, a06, a07, b08, ?_, ?_, a14, (big_of h16 hlp (hn₀ _ hn)).1,
      (big_of h16 hlp (hn₀ _ hn)).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [d09, hmm, hc0]; exact hS
    · rw [d09, hmm, hc1]; exact hXh
    · rw [hmm, hc1]; exact hcap
    · rw [d09, hmm, keep _ (by norm_num) le_rfl]; exact hN
    · rw [b08']; exact li_of_desc hDa.holds
    · rw [d09, d99]
    · rw [d09, hmm, keep _ (by norm_num) (by norm_num)]; exact hDa
    · rw [d09, keep _ (by norm_num) (by norm_num)]; exact hD
    · rw [keep _ (by norm_num) (by norm_num)]; exact hK
    · rw [d09, keep _ (by norm_num) (by norm_num)]; exact hLb
    · rw [d09, hmm, keep _ (by norm_num) (by norm_num)]; exact hLa
    · rw [d09, keep _ (by norm_num) (by norm_num)]; exact hEb
    · rw [d09, hmm, keep _ (by norm_num) (by norm_num)]; exact hEa
  -- 3. the loop invariant at the start
  have hn3 := hQ.1
  have inv0 : LvInv O P W c₁ L E reg Kb 0 c₁ := by
    refine ⟨w₁, d10, by rw [d11], fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, by simp,
      fun _ => ⟨Qof P, 0, 1, le_rfl, by omega⟩,
      fun _ => BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E, fun _ => 0, fun _ => [],
      by rw [d12]; simp, fun r hr => absurd hr (Nat.not_lt_zero r), Or.inl d13,
      fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  -- 4. the loop
  have hA₁ := d99
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hA₂⟩ := hloop P W c₁ c₁ L E reg lam Kb ctx le_rfl
    (by rw [hA₁]
        have hkb : (K + 1) * Kb ≤ (Kb + 2) * (K + 1) := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
        generalize κLv κH κR κX κc κT * ((K + 1) * X) = u at hcost hroom
        generalize (Kb + 2) * (K + 1) = v at hcost hkb
        generalize κT * (K + 1) * X = w at hcost
        generalize (K + 1) * Kb = z at hkb ⊢
        omega) inv0
  -- 5. the tail
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, h00, hInv₃⟩ := hTm Kb P W c₁ c₂ L E reg lam ctx hcnt I₂
    (by generalize κLv κH κR κX κc κT * ((K + 1) * X) = u at hcost hroom
        generalize (Kb + 2) * (K + 1) = v at hcost hk₂
        generalize κT * (K + 1) * X = w at hcost ⊢
        omega)
  obtain ⟨-, -, -, -, m₂, rm₂, r₂, rr₂, o₂, a₂, -, -⟩ := I₂
  have ex : Exec P W (.seq lvPar (.seq (lvLoop sH sR sX) sT)) c c₃ (k₁ + (k₂ + k₃)) :=
    .seq e₁ (.seq e₂ e₃)
  have b21 : bDownDrv ∈ drvBands := bDownDrv_mem_drvBands
  refine ⟨c₃, _, ex, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- the cost
    simp only [rd21, Nat.reduceAdd]
    rw [hlam, hK']
    generalize κLv κH κR κX κc κT * ((K + 1) * X) = u at hcost hroom ⊢
    generalize (Kb + 2) * (K + 1) = v at hcost hk₂
    generalize κT * (K + 1) * X = w at hcost hk₃
    omega
  · simp only [rd21, Nat.reduceAdd]; rw [h00, hlam]
  · simp only [rd21, Nat.reduceAdd]; rw [hlam]; exact hInv₃
  · -- the frame
    have hA9 := d09
    refine ⟨fun r hr hrA => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
    · rw [F₃.1 r hr hrA, r₂ r hr hrA, F₁.1 r (fun h => hr (by
        simp only [Finset.mem_singleton] at h; rw [h]; exact b21)) hrA]
    · rw [F₃.2.1 r hr, rr₂ r hr, F₁.2.1 r (fun h => hr (by
        simp only [Finset.mem_singleton] at h; rw [h]; exact b21))]
    · rw [F₃.2.2.1 a (by omega), m₂ a (by omega), hmm]
    · rw [F₃.2.2.2.1 a (by omega), rm₂ a (by omega), F₁.2.2.2.1 a ha]
    · rw [F₃.2.2.2.2.1, o₂, F₁.2.2.2.2.1]
    · have := F₃.2.2.2.2.2.1; omega
    · have := F₃.2.2.2.2.2.2; have := F₁.2.2.2.2.2.2; omega


end

end DrvLS

end Chazelle.Core
