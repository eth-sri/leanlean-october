module

public import NearlyMinimax.HighSourceRawDecomposition
public import RoughRegime.Macro
public import NearlyMinimax.OrdinaryFineAliasSpatialEnergy
public import RoughRegime.Notation

𝗍

/-! Exact identification of every genuine ordinary fine signed packet
with the spatial all-count alias action used by the energy bounds. -/
𝚫
𝚪
𝚨
𝚩
𝚱

theorem higherBandFirstAction_fine_eq_aliasRawAction
    ad bd lam L T (ha : 𝖼) (hab : 𝖽) (hlam : 𝖺)
    (hL : 0 < L) (hT : 𝖹) r M D q (hr : 𝘠₁)
    (hD : 𝗮) (hnD : 𝖠₁) C a V η
    U (hU : ∀ i j, |𝗒₂| ≤ 2)
    (p g w : 𝙔) (hp : 𝖳)
    (c : 𝙮 → ℝ) y :
    higherBandFirstAction ad bd lam L T r M D q C true U p c
      (fun v => 𝖨 𝙬 v y) =
      ordinaryFineAliasRawAction ad bd lam L T M r q C a V η U p g w c y := by
  rw [higherBandFirstAction_actual_count_expansion ad bd lam L T ha hab hlam hL hT
    r M D q hr hD hnD C true U hU p hp c]
  rfl
