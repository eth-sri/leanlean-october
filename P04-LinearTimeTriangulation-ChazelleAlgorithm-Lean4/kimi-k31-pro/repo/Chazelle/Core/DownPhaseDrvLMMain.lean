module

public import Chazelle.Core.DownPhaseDrvLMFam
public import Chazelle.Rwx

/-!
# Down-phase level math (D7): `levelMathSpec`

**`levelMathSpec : DrvR.LevelMathSpec`**, the math of one level:

1. the hosts (`host_facts`, weight bound `2^(⌈βλ⌉+12) = 2 · 2^μ`);
2. the size of the kept lists (`lx_size`, Lemma 2.3, `#pts ≤ 10 · 2^μ + 8`);
3. the splice precondition (`LvlCtx.ok`, `keyBkt_le`, `codeLe_of_keyBkt`, `bcnt_le_four`);
4. the family after the splice (`LvlCtx.step`, `LvlCtx.down`, `LvlCtx.count`).
-/

namespace Chazelle.Core

namespace DrvLM

@[expose] public section

open DrvR (regHost keyBkt)
open DownStep (stepFam)

/-- `2^(⌈βλ⌉+12) = 2 · 2^μ`. -/
theorem pow_lvl (lam : ℕ) : 2 ^ (Cost.ceilBeta lam + 12) = 2 * 2 ^ DrvR.nextLvl lam := by
  unfold DrvR.nextLvl
  rw [show Cost.ceilBeta lam + 12 = Cost.ceilBeta lam + 11 + 1 by omega, pow_succ]
  ring

/-- **The math of one level (D7).** -/
theorem levelMathSpec : DrvR.LevelMathSpec := by
  classical
  intro P L E reg lam hG hLne hL hperm hsort hdeg hwt hregs
  have hQ  := (shearInvariance (epsOf P) P).1 hG.1
  have hdh  := (goodShear_epsOf hG.2).2.1
  have hK : 0 < L.length := List.length_pos_iff_exists_mem.2 (List.exists_mem_of_ne_nil _ hLne)
  have B : DrvB.BaseCtx (Qof P) L E reg (decide (Mountain.LeftInside (Qof P))) :=
    ⟨hQ, hdh, hL, hperm, hsort, hK, hregs, decide_eq_true_iff⟩
  have hS : (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P))
      (Qof P) = Gran.lset (interiorModel (Qof P)) (Qof P) L :=
    Gran.F_of_map (BuildNF.isNF_goodModel (Or.inr ⟨Qof P, hQ, rfl⟩) hL hperm hsort).2.1
  have hγ := pow_lvl lam
  refine ⟨fun r hr => ?_, ?_⟩
  · -- 1. the hosts
    obtain ⟨h1, h2, h3, h4⟩ := host_facts B hr hdeg hwt
    exact ⟨h1, fun a ℓ h => by have := h2 a ℓ h; omega, h3, by omega⟩
  intro γ₀ M C NR γR Lx hγ₀ hreg
  -- the host facts of the regions
  have hH : ∀ r, r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
      (C r).P.Simple ∧ DownDrv.ExtractOK (Qof P) (Gran.lset (interiorModel (Qof P)) (Qof P) L)
        (reg r) (C r) := by
    intro r hr
    obtain ⟨hP, hs, hm, -⟩ := hreg r hr
    have h := DownMath.hostR1Spec P L E reg r hG hLne hL hperm hsort hdeg hregs hr
    obtain ⟨-, -, hsimp, -, -, -, hex⟩ := h
    refine ⟨by rwx [hP], ?_⟩
    have := hex (C r) hP hs hm
    rw [hS] at this
    exact this
  -- the abstract level
  have X : LvlCtx (Qof P) L (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions reg C
      (fun r => (NR r).F (chainModel (C r)) (Qof P)) Lx DrvR.regCap
      (2 ^ (Cost.ceilBeta (DrvR.nextLvl lam) + 12)) := by
    refine ⟨hQ, hL, by rwx [← hS], fun r hr => by rw [← hS]; exact hregs.1.1 r hr,
      hregs.1.2.1, fun U hU => hregs.1.2.2 U (by rwx [hS]), fun r hr => (hH r hr).2,
      fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
    · obtain ⟨-, -, -, hcan, -, hhi, -⟩ := hreg r hr
      exact ⟨hcan.1.1, hcan.2.1, fun U hU => (hcan.2.2.1.1 U hU).trans (by omega)⟩
    · obtain ⟨-, -, -, -, -, -, hkept, -⟩ := hreg r hr
      exact hkept
    · obtain ⟨-, -, -, -, -, -, -, hnd, -⟩ := hreg r hr
      exact hnd
    · obtain ⟨-, -, -, -, -, -, -, -, hatt, -⟩ := hreg r hr
      exact hatt
  -- the sizes
  have hsize : ∀ r, r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
      (Lx r).length * (γ₀ + 1) ≤ 140 * (DrvR.regCap + 2) * (2 * (C r).m + 1) := by
    intro r hr
    obtain ⟨-, -, -, hcan, hlo, -, hkept, hnd, -⟩ := hreg r hr
    exact lx_size (hH r hr).1 ⟨hcan.1.1, hcan.2.1, hcan.2.2.1⟩ hlo hkept hnd
  have hm : ∀ r, r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
      (C r).m + 1 = ((regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) r).pts (Qof P).n).length := by
    intro r hr
    obtain ⟨hP, -, hm, -⟩ := hreg r hr
    rw [hm, hP]
    simp [Host.poly, Polygon.n]
  refine ⟨fun r hr => ?_, X.ok, fun q _ => keyBkt_le _ _ _,
    fun q q' hq hq' h => codeLe_of_keyBkt _ _ hq hq' h, fun b => ?_, fun E' hperm' hsort' => ?_⟩
  · -- 3. the size of the kept lists
    have h1 := hsize r hr
    have h2 := hm r hr
    have h4 := (host_facts B hr hdeg hwt).2.2.2
    calc (Lx r).length * (γ₀ + 1) ≤ 140 * (DrvR.regCap + 2) * (2 * (C r).m + 1) := h1
      _ ≤ 140 * (DrvR.regCap + 2) * (20 * 2 ^ DrvR.nextLvl lam + 17) :=
        Nat.mul_le_mul_left _ (by omega)
  · -- the buckets
    exact bcnt_le_four hK hperm hsort hregs
      (fun r hr => (hreg r hr).2.2.2.2.2.2.2.2.2.2)
      (fun r hr => (hreg r hr).2.2.2.2.2.2.2.2.2.1) b
  · -- 4. the family after the splice
    have hF' : (BuildNF.buildNF (interiorModel (Qof P)) (Qof P)
        (L ++ (List.range (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions).flatMap
          Lx) E').F (interiorModel (Qof P)) (Qof P) =
        stepFam (Qof P) (Gran.lset (interiorModel (Qof P)) (Qof P) L)
          (fun U => (NR (rOf (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions reg
            U)).F (chainModel (C (rOf (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions
              reg U))) (Qof P)) := by
      rw [Gran.F_of_map (BuildNF.isNF_goodModel (Or.inr ⟨Qof P, hQ, rfl⟩) X.ok hperm' hsort').2.1,
        X.step]
    rw [hF', hS]
    refine ⟨Set.subset_union_left, X.down.2.1, X.down.2.2, X.count (fun r hr => ?_)⟩
    have h1 := hsize r hr
    have h2 := hm r hr
    rw [pts_length B hr, hS] at h2
    rw [← h2]
    calc (Lx r).length * (γ₀ + 1) ≤ 140 * (DrvR.regCap + 2) * (2 * (C r).m + 1) := h1
      _ ≤ 140 * (DrvR.regCap + 2) * (2 * ((C r).m + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 280 * (DrvR.regCap + 2) * ((C r).m + 1) := by ring

end

end DrvLM

end Chazelle.Core
