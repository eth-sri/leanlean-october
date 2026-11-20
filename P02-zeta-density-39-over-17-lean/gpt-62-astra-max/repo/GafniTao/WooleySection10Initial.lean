module
public import GafniTao.WooleyExponent
public import GafniTao.WooleySourceSections68

@[expose] public section

/-!
# The initial normalized lower bound in Wooley Section 10

This file converts an actual counterexample below the critical exponent into
the lower bound for the first normalized mixed mean.  The positivity of the
normalizing conditioned mean is derived from source equation (3.10); it is
not imposed as an extra hypothesis.
-/

namespace GafniTao

noncomputable section

/-- The exact real-power rearrangement used between (6.3), Lemma 6.3, and
the initial inequality in (10.6). -/
theorem wooley_initial_normalization_algebra
    {p H theta s : ℕ} {Lambda epsilon C U K Z : ℝ}
    (hp : 1 ≤ p) (hC : 0 < C) (hZ : 0 < Z)
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z ≤ U)
    (hupper : U ≤ C * (p ^ theta : ℝ) ^ s * K) :
    C⁻¹ * (p : ℝ) ^ (-((H : ℝ) * epsilon) - (s : ℝ) * theta) ≤
      K / ((p : ℝ) ^ (Lambda * (H : ℝ)) * Z) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hden : 0 < (p : ℝ) ^ (Lambda * (H : ℝ)) * Z :=
    mul_pos (Real.rpow_pos_of_pos hpR _) hZ
  rw [le_div_iff₀ hden]
  have hscale : 0 < C * (p ^ theta : ℝ) ^ s := by positivity
  have hpowTheta : (p ^ theta : ℝ) ^ s =
      (p : ℝ) ^ ((s : ℝ) * theta) := by
    calc
      (p ^ theta : ℝ) ^ s = ((p : ℝ) ^ theta) ^ s := by norm_num
      _ = (p : ℝ) ^ (theta * s) := by rw [pow_mul]
      _ = (p : ℝ) ^ (((theta * s : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (p : ℝ) ^ ((s : ℝ) * theta) := by
        congr 1
        push_cast
        ring
  have hrearrange :
      C⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
          ((p : ℝ) ^ (Lambda * (H : ℝ)) * Z) =
        (C * (p ^ theta : ℝ) ^ s)⁻¹ *
          ((p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z) := by
    rw [hpowTheta, mul_inv, ← Real.rpow_neg hpR.le]
    have hpowers :
        (p : ℝ) ^ (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
            (p : ℝ) ^ (Lambda * (H : ℝ)) =
          (p : ℝ) ^ (-((s : ℝ) * theta)) *
            (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) := by
      rw [← Real.rpow_add hpR, ← Real.rpow_add hpR]
      congr 1
      ring
    calc
      C⁻¹ * (p : ℝ) ^
            (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
            ((p : ℝ) ^ (Lambda * (H : ℝ)) * Z) =
          C⁻¹ *
            ((p : ℝ) ^
              (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
             (p : ℝ) ^ (Lambda * (H : ℝ))) * Z := by ring
      _ = C⁻¹ *
            ((p : ℝ) ^ (-((s : ℝ) * theta)) *
             (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon))) * Z := by
          rw [hpowers]
      _ = C⁻¹ * (p : ℝ) ^ (-((s : ℝ) * theta)) *
            ((p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z) := by
          ring
  rw [hrearrange]
  calc
    (C * (p ^ theta : ℝ) ^ s)⁻¹ *
        ((p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z) ≤
      (C * (p ^ theta : ℝ) ^ s)⁻¹ * U :=
        mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hscale.le)
    _ ≤ (C * (p ^ theta : ℝ) ^ s)⁻¹ *
        (C * (p ^ theta : ℝ) ^ s * K) :=
          mul_le_mul_of_nonneg_left hupper (inv_nonneg.mpr hscale.le)
    _ = K := by field_simp

end

end GafniTao
