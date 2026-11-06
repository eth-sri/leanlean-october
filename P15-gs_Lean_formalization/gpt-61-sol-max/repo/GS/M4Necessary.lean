
import GS.M4Obstruction



/-!
# Necessity of the four-factor determinant obstruction

-/

namespace GS.M4

variable (a b e f : Fin 3 → ℝ)

def canonicalDetTable  : Mat 3 :=
  !![b 0*b 1*f 1*f 0, a 0*a 1*e 2*f 0, a 1*b 0*e 1*f 2;
     a 2*b 0*e 0*e 1, b 2*b 0*f 0*f 2, b 2*a 0*e 1*e 2;
     b 2*a 1*f 0*e 1, a 1*a 2*f 2*e 0, b 1*b 2*f 2*f 1]


theorem canonical_obstruction 
    (hW : ∀ i, (a i)^2+(b i)^2=1) (hY : ∀ i, (e i)^2+(f i)^2=1)
    (hden : canonicalDetTable a b e f 2 1 * canonicalDetTable a b e f 1 0 *
      canonicalDetTable a b e f 1 1 ≠ 0) :
    let d := canonicalDetTable a b e f
    (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1 := by
  let d := canonicalDetTable a b e f
  simp only [mul_ne_zero_iff] at hden
  rcases hden with ⟨⟨h32,h21⟩,h22⟩
  have r1 : d 0 2*d 1 0/d 2 1 = (b 0)^2*(e 1)^2 := by
    apply (div_eq_iff h32).mpr
    simp [d,canonicalDetTable]
    ring
  have r2 : d 0 2*d 2 1/d 1 0 = (a 1)^2*(f 2)^2 := by
    apply (div_eq_iff h21).mpr
    simp [d,canonicalDetTable]
    ring
  have r3 : d 0 0*d 2 2/d 1 1 = (b 1)^2*(f 1)^2 := by
    apply (div_eq_iff h22).mpr
    simp [d,canonicalDetTable]
    ring
  have hb : (b 0)^2 ≤ 1 := by grind [sq_nonneg]
  have hf : (f 2)^2 ≤ 1 := by grind [sq_nonneg]
  change (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1
  rw [r1,r2,r3]
  have h₁ : (b 1)^2 ≤ 1-(a 1)^2*(f 2)^2 := by
    nlinarith [hW 1,mul_nonneg (sq_nonneg (a 1)) (sub_nonneg.mpr hf)]
  have h₂ : (f 1)^2 ≤ 1-(b 0)^2*(e 1)^2 := by
    nlinarith [hY 1,mul_nonneg (sq_nonneg (e 1)) (sub_nonneg.mpr hb)]
  simpa only [mul_comm] using
    mul_le_mul h₂ h₁ (sq_nonneg (b 1)) ((sq_nonneg (f 1)).trans h₂)


end GS.M4
