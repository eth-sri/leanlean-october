/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthStableTemplate
public import VaughtConjecture.Knight.GrowthCarrierEvaluation
public import VaughtConjecture.Knight.StableActualLabelling
public import VaughtConjecture.Knight.GrowthStableSelectedInput
public import VaughtConjecture.Knight.AnchorStable

@[expose] public section

namespace VaughtConjecture.Knight.NonHollowGrowthReceiving

open TypeTower StageType KnightRealization Value ExtOrd

noncomputable section

universe w

variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- Stable receiving over a positive root, with no supplied calibration,
template, admission or physical-correctness hypothesis. -/
theorem receives_positive (hM : W.IsModel) (hh : ¬ W.IsHollow)
    (hg : W.HasTopGradeGrowth) {n : ℕ} (hn : 0 < n)
    (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.nextBlock.1 (n + 1)) (hq : IsCoface (stableLiftType hM t p hp) q)
    (γ : Ordinal.{0}) (hγ : γ < α.nextBlock.1) :
    ∃ (y : M) (hy : y ∉ Set.range t) (s : S α.1 (n + 1)),
      W.eval (snoc t y hy) = some s ∧ ∃ he : q.scheme = s.scheme,
        (∀ d, q.label d ≠ ⊤ →
          W.stableValue (snoc t y hy) s (SemScheme.castCell he d) = q.label d) ∧
        (∀ d, q.label d = ⊤ →
          ofOrd γ < W.stableValue (snoc t y hy) s (SemScheme.castCell he d)) := by
  have ha : W.HasInfinityAnchor := Classical.not_not.mp hh
  obtain ⟨k, a, p₀, ha₀, d₀, i, hd₀, hstable⟩ :=
    (hasInfinityAnchor_iff_exists_finite_stable hM).mp ha
  obtain ⟨J, u, C, hC, f, hfu, _, hvP, hP, hvC, hF, X, _, hsmall,
    _, _, ⟨T⟩, hclass, _, hread⟩ :=
    GrowthStableTemplate.exists_input hM hg ha₀ d₀ hd₀ hstable hn hp q hq γ hγ
  have hin : InClass X.ZA C.label := by
    intro d
    rw [hclass]
    rfl
  obtain ⟨y, _, hyRoot, s, hev, he, hc⟩ :=
    GrowthCarrierEvaluation.exists_correct_donor C q.scheme p.scheme f
      hvC hvP hF hP X T hsmall (stableActualLabelling hM.consistent hM.covering) hM hC
      (fun d => (GrowthStableSelectedInput.private_bottom hM hC d.1).trans (hin d))
  change X.req.Correct (X.req.sec (W.stableValue u C))
    (fun d => W.stableValue (snoc (f.trans u) y hyRoot) s (SemScheme.castCell he.symm d)) at hc
  rw [← hfu]
  exact ⟨y, hyRoot, s, hev, he.symm, hread _ hc⟩

end

end VaughtConjecture.Knight.NonHollowGrowthReceiving
