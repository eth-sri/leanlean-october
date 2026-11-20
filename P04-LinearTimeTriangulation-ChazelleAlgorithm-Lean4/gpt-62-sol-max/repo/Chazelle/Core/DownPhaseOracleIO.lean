module

public import Chazelle.Core.DownPhaseOracleCuH
public import Chazelle.Core.DownPhaseDrvRObl

/-!
# WP-M (E7-B): the interior oracles from the oracles of `ShootCutSpec`

**`interiorOracles_of : ShootCutSpec O → DrvR.IntOraclesSpec O`**: the interior shooter `shI sh`
and the interior cutter `cuI cu` built from the chain-model oracles `sh`, `cu` of `ShootCutSpec O`
(`interiorShooter_of`, `interiorCutter_of`) serve the interior model of `Qof P` on `gradeCtx O`,
writing `insert bUp oracleBands`, with the cost shape of `ShootCutSpec O` and the constant
`κ' = 172 κ + 23000` (finding E7-B, the obligation of the driver in
`DownPhaseDrvRObl.lean`).

* `shooterOK_weaken`, `cutterOK_weaken`: the oracle specifications are antitone in the model
  predicate (it occurs only in the precondition) and monotone in the cost.
-/

namespace Chazelle.Core

namespace IOrc

open Machine

@[expose] public section

/-- **A shooter serves fewer models at a larger cost.** -/
theorem shooterOK_weaken {sh : Stmt} {B : Finset ℕ} {F F' : ℕ → ℕ} {X : MemCtx}
    {Ok Ok' : Polygon → Model → Prop} (h : ShooterOK sh B F X Ok)
    (hOk : ∀ P M, Ok' P M → Ok P M) (hF : ∀ γ, F γ ≤ F' γ) : ShooterOK sh B F' X Ok' := by
  intro P W c hw hpre hcost
  obtain ⟨hG, hHW, hX, hcap, hwf, hreg, M, hMD, hOk', rest⟩ := hpre
  beta_reduce at hcost
  obtain ⟨c', k, e, hk, hpost, F₁⟩ := h P W c hw
    ⟨hG, hHW, hX, hcap, hwf, hreg, M, hMD, hOk P M hOk', rest⟩
    (by beta_reduce; exact le_trans (Nat.add_le_add_left (hF _) _) hcost)
  refine ⟨c', k, e, ?_, hpost, F₁⟩
  beta_reduce at hk ⊢
  exact hk.trans (hF _)

/-- **A cutter serves fewer models at a larger cost and piece bound.** -/
theorem cutterOK_weaken {cu : Stmt} {B : Finset ℕ} {G G' H : ℕ → ℕ} {X : MemCtx}
    {Ok Ok' : Polygon → Model → Prop} (h : CutterOK cu B G H X Ok)
    (hOk : ∀ P M, Ok' P M → Ok P M) (hG : ∀ γ, G γ ≤ G' γ) : CutterOK cu B G' H X Ok' := by
  intro P W c hw hpre hcost
  obtain ⟨hGE, hHW, hX, hcap, hwf, M, hMD, hOk', rest⟩ := hpre
  beta_reduce at hcost
  obtain ⟨c', k, e, hk, hpost, F₁⟩ := h P W c hw
    ⟨hGE, hHW, hX, hcap, hwf, M, hMD, hOk P M hOk', rest⟩
    (by beta_reduce; exact le_trans (Nat.add_le_add_left (hG _) _) hcost)
  refine ⟨c', k, e, ?_, fun M' hM' => ?_, F₁⟩
  · beta_reduce at hk ⊢
    exact hk.trans (hG _)
  · obtain ⟨p1, p2, p3, prest⟩ := hpost M' hM'
    exact ⟨p1, p2, p3.trans (hG _), prest⟩

theorem one_le_rpowCeil' (γ : ℕ) : 1 ≤ rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) := by
  have h1 : 1 ≤ cutGran γ := by
    unfold cutGran gradeGran
    have := Nat.one_le_two_pow (n := Cost.ceilBeta (Nat.clog 2 γ))
    omega
  have h2 : 1 ≤ cutGran γ * (γ + 1) ^ 2 := Nat.mul_le_mul h1 (Nat.one_le_pow _ _ (by omega))
  unfold rpowCeil
  apply Nat.one_le_iff_ne_zero.2
  intro h0
  rw [Nat.ceil_eq_zero] at h0
  have : (0 : ℝ) < ((cutGran γ * (γ + 1) ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
    apply Real.rpow_pos_of_pos; exact_mod_cast h2
  linarith

theorem shCost_ge (κ γ : ℕ) :
    FI (fun γ => κ * (Nat.clog 2 γ + 1) * rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) + κ) γ ≤
      DrvR.shCost (172 * κ + 23000) γ := by
  unfold FI DrvR.shCost
  beta_reduce
  have hR := one_le_rpowCeil' γ
  set R := rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3)
  set a := Nat.clog 2 γ + 1
  have ha : 1 ≤ a := by omega
  have h1 : a ≤ a * R := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : 0 ≤ κ * a * R := Nat.zero_le _
  nlinarith

theorem cuCost_ge (κ γ : ℕ) :
    GI (fun γ => κ * (Nat.clog 2 γ + 1)) γ ≤ DrvR.cuCost (172 * κ + 23000) γ := by
  unfold GI DrvR.cuCost
  beta_reduce
  set a := Nat.clog 2 γ + 1
  have ha : 1 ≤ a := by omega
  nlinarith

/-- **The interior oracles** (finding E7-B): from the oracles of `ShootCutSpec O`, a shooter and a
cutter serving the interior model of `Qof P` on `gradeCtx O`, writing `insert bUp oracleBands`,
with the cost shape of `ShootCutSpec O`. -/
theorem interiorOracles_of {O : OracleIface} (hSC : ShootCutSpec O) : DrvR.IntOraclesSpec O := by
  obtain ⟨sh, cu, κ, hsh, hcu⟩ := hSC
  refine ⟨shI sh, cuI cu, 172 * κ + 23000, ?_, ?_⟩
  · exact shooterOK_weaken (interiorShooter_of hsh) (fun P M h => Or.inr h) (shCost_ge κ)
  · exact cutterOK_weaken (interiorCutter_of hcu) (fun P M h => Or.inr h) (cuCost_ge κ)

end

end IOrc

end Chazelle.Core
