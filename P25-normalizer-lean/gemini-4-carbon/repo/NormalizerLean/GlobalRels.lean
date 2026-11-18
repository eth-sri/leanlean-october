module

public import NormalizerLean.LocalRels

@[expose] public section

/-!
# The global relations hold: `globalRels_mem_Gamma0`

* the local relators hold in Γ₀(N), by the embedding argument (12) of [BA]: words in w_{m_p}, S_{h(m_p)}
  have the shape μ·[[a, b], [Nc, d]] with a, b, c, d, μ² ∈ ℤ[1/p], and such an element of Γ₀(m_p) lies
  in Γ₀(N);
* [w_p, w_q] ∈ Γ₀(N), since w_p w_q and w_q w_p are both Atkin–Lehner elements for m_p m_q;
* [s_p, s_q] = 1;
* w_p s_q w_p⁻¹ s_q^{-m_p} ∈ Γ₀(N), which is (15) of [BA].
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### ℤ[1/p] -/

/-! ### The embedding invariant -/

/-! ### The generators have the invariant shape -/

/-! ### Atkin–Lehner elements at a smaller level, and products -/

/-! ### Translations commute; (15) -/

/-! ### Assembly -/

theorem mPart_ne_zero {N p : ℕ} (hp : p.Prime) : mPart N p ≠ 0 :=
  pow_ne_zero _ hp.ne_zero

end

end NormalizerLean
