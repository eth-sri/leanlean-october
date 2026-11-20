module

public import OAI.NumberTheory.DirichletL.Reflection.LowWidth

@[expose] public section

namespace OAI.SevenEighths.InverseReflectedPhase
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths
local notation "Eis" => ActualEisensteinCubic.O

/-- Common norm bounds, dyadic widths and exponent losses in the low reflected window.
`rowScale` and `slotScale` account for the scaling of the dyadic endpoints. -/
structure LowReflectionBudget (I Q : Ideal Eis) (Z₀ η ε δ Lscale : ℝ)
    (rowScale slotScale : ℝ → ℝ) where
  Z : ℝ
  O₀ : ℝ
  H : ℝ
  za : ℝ
  Nstar : ℝ
  d : ℝ
  ell0 : ℝ
  shift : ℝ
  π : ℝ
  Ck : ℝ
  CO : ℝ
  CH : ℝ
  X : ℝ
  QK : ℝ
  QP : ℝ
  Lrow : ℝ
  Lslot : ℝ
  scale_ge : Z₀≤Z
  Ck_pos : 0<Ck
  CO_pos : 0<CO
  CH_pos : 0<CH
  X_pos : 0<X
  QK_pos : 0<QK
  QP_pos : 0<QP
  row_norm : (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)
  powerful_norm : Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ)
  residual_norm : Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ)
  residual_error : Real.log (CH*Ck*CO)/Real.log Z≤η
  powerful_width : normWidth Z (rowPowerfulPart I)≤O₀+η
  mask_width : normWidth Z Q≤η
  d_nonneg : 0≤d
  d_le : d≤1/6
  length_le : ell0≤1/6-d+η
  powerful_nonneg : 0≤O₀
  slot_le : za≤ell0+η
  shift_le : |shift|≤η
  shifted_width : Nstar=1+ell0+shift
  row_log : H=Real.logb Z (rowScale QK)
  slot_log : za=Real.logb Z (slotScale QP)
  source_log : Nstar=Real.logb Z X
  delta_nonneg : 0≤δ
  delta_le : δ≤η
  row_cap : rowScale QK≤Z^Lrow
  slot_cap : slotScale QP≤Z^Lslot
  fixed_error : Real.logb Z 16≤η
  loss_budget : ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π

/-- Reuse the same budget after decreasing the lower threshold on the main scale. -/
def LowReflectionBudget.lowerThreshold {I Q : Ideal Eis} {Z₀ Z₁ η ε δ Lscale : ℝ}
    {rowScale slotScale : ℝ → ℝ} (B : LowReflectionBudget I Q Z₀ η ε δ Lscale rowScale slotScale)
    (h : Z₁ ≤ Z₀) : LowReflectionBudget I Q Z₁ η ε δ Lscale rowScale slotScale :=
  { B with scale_ge := h.trans B.scale_ge }

end OAI.SevenEighths.InverseReflectedPhase
