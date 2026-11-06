module

public import OAI.NumberTheory.DirichletL.Moments.OriginalRadialTail
public import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentNaturalRadialCutoff
local notation "O" => HeckeFamily.O

lemma reciprocal_cutoff_bound (Z xi:ℝ) (order:ℕ) (hZ:0<Z) :
    ((1+Z^xi)^order)⁻¹≤Z^(-xi*(order:ℝ)) := by
  have hp : (Z^xi)^order≤(1+Z^xi)^order:=
    pow_le_pow_left₀ (by positivity) (by linarith) order
  have hh:=inv_anti₀ (by positivity) hp
  have he : (Z^xi)^order=Z^(xi*(order:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  apply hh.trans_eq
  rw [he,←Real.rpow_neg hZ.le]
  simp

end SevenEighths.CenteredMomentNaturalRadialCutoff

end

end OAI
