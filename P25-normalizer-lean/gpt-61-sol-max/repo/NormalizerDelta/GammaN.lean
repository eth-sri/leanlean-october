module

public import NormalizerDelta.GammaConj

@[expose] public section

/-!
# §G: Nor(±Γ(N)) = Nor(Γ(N)) = SL₂(ℤ); the S₇ example at level 49

* For Δ = {d ≡ ±1 mod M} at level M², M ∣ ε_Δ, so h_Δ = M and n_Δ = 1 (`hDelta_deltaPm_sq`).
* Nor(±Γ(M)) = D Nor(Γ_Δ(M²)) D⁻¹ (`conj_GammaDelta_sq'`, `Subgroup.map_equiv_normalizer_eq`), and by
  `newman_delta'` every element of Nor(Γ_Δ(M²)) is ±[[a, b/M], [Mc, d]] (e ∣ n_Δ = 1), whose D-conjugate
  ±[[a, b], [c, d]] is integral.
* Nor(Γ(N)) ≤ Nor(±Γ(N)) since −1 is central; SL₂(ℤ) normalizes both since Γ(N) is normal.
* S₇ = D⁻¹ T D normalizes Γ_Δ(49) because T normalizes ±Γ(7); S₇ ∉ Nor(Γ₀(49)) by the frozen T2
  (h(49) = 1 would force 7 b = ±1).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem ofZ_neg (γ : SL(2, ℤ)) : ofZ (-γ) = -ofZ γ := by
  ext i j; simp [SpecialLinearGroup.coe_neg]

/-! ### h_Δ for Δ = ±1 mod M at level M² -/

/-! ### Nor(±Γ(N)) and Nor(Γ(N)) -/

/-! ### S₇ at level 49 -/

end

end NormalizerLean
