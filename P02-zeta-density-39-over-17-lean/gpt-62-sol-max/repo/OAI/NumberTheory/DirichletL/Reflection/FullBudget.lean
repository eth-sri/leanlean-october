module
public import OAI.NumberTheory.DirichletL.Reflection.OriginalFull
public import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps

@[expose] public section

namespace OAI.SevenEighths.InverseReflectedPhase

/-- Combine the main energy and a uniformly paid squared tail, taking the
larger of their two height degrees. -/
theorem merge_sector_tail {S M T cusp R P Z L p q : ℝ} {d e : ℕ}
    (hM : 0≤M) (hZ : 1≤Z) (hL : 1≤L) (hp : p≤q)
    (hT : R*P^2≤cusp^4*Z^p)
    (hS : S≤M*L^d*Z^q+2*R*(P*T*L^e)^2) :
    S≤(M+2*T^2*cusp^4+1)*L^(max d (e*2))*Z^q := by
  let D := max d (e*2)
  have hLp : L^(e*2) ≤ L^D := pow_le_pow_right₀ hL (le_max_right _ _)
  have hLm : L^d ≤ L^D := pow_le_pow_right₀ hL (le_max_left _ _)
  have hZp : Z^p ≤ Z^q := Real.rpow_le_rpow_of_exponent_le hZ hp
  apply hS.trans
  have ht : 2*R*(P*T*L^e)^2 ≤ (2*T^2*cusp^4)*L^D*Z^q := calc
    _ = (2*T^2*L^(e*2))*(R*P^2) := by rw [pow_mul]; ring
    _ ≤ (2*T^2*L^(e*2))*(cusp^4*Z^p) := mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2*T^2*L^D)*(cusp^4*Z^q) := by gcongr
    _ = _ := by ring
  have hm : M*L^d*Z^q ≤ M*L^D*Z^q := by gcongr
  have hb : 0≤L^D*Z^q := by positivity
  exact (add_le_add hm ht).trans (by nlinarith only [hb])

end OAI.SevenEighths.InverseReflectedPhase
