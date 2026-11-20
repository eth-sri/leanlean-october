module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
public import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.SectorData

@[expose] public section

namespace OAI.SevenEighths.InverseReflectedPhase

open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
open InverseTerminalWidths InverseMoment
local notation "Eis" => ActualEisensteinCubic.O

/-- The common scale, width, and loss conditions for the original reflection window. -/
structure OriginalReflectionBudget (I F B R : Ideal Eis) (Z₀ η ε δ Lscale : ℝ) where
  Z : ℝ
  F₀ : ℝ
  N : ℝ
  V : ℝ
  M : ℝ
  z₀ : ℝ
  margin : ℝ
  cstar : ℝ
  O₀ : ℝ
  H : ℝ
  za : ℝ
  Nstar : ℝ
  hhat : ℝ
  d : ℝ
  π : ℝ
  Ck : ℝ
  CO : ℝ
  CH : ℝ
  Cf : ℝ
  X : ℝ
  QK : ℝ
  QP : ℝ
  Lrow : ℝ
  Lslot : ℝ
  scale_ge : Z₀≤Z
  Ck_pos : 0<Ck
  CO_pos : 0<CO
  CH_pos : 0<CH
  Cf_pos : 0<Cf
  X_pos : 0<X
  QK_pos : 0<QK
  QP_pos : 0<QP
  row_upper : (Ideal.absNorm I:ℝ)≤Ck*Z^M
  powerful_lower : Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ)
  residual_lower : Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ)
  factor_upper : (Ideal.absNorm F:ℝ)≤Cf*Z^V
  residual_error : Real.log (CH*Ck*CO)/Real.log Z≤η
  width_error : Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η
  margins : CanonicalMargins F₀ M (normWidth Z R) z₀ margin
  total_width : F₀=N+V
  shifted_width : Nstar=N-3*hhat
  factor_width : V≤d
  shift_le : hhat≤d+η
  row_log : H=Real.logb Z QK
  slot_log : za=Real.logb Z (QP/2)
  source_log : Nstar=Real.logb Z X
  row_nonneg : 0≤M
  powerful_nonneg : 0≤O₀
  slot_nonneg : 0≤za
  slot_le : za≤z₀
  saving_pos : 0<cstar
  margin_le : cstar/2≤margin
  perturbation_le : d≤cstar/200
  eta_le : η≤cstar/1000
  delta_le : δ+η≤cstar/1000
  overhead_le : π≤cstar/1000
  row_cap : QK≤Z^Lrow
  slot_cap : (QP/2)≤Z^Lslot
  fixed_error : Real.logb Z 16≤η
  loss_budget : ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π

/-- Pass to an estimate with a smaller lower threshold on the base scale. -/
def OriginalReflectionBudget.lowerThreshold {I F B R : Ideal Eis} {Z₀ Z₁ η ε δ Lscale : ℝ}
    (rb : OriginalReflectionBudget I F B R Z₀ η ε δ Lscale) (h : Z₁ ≤ Z₀) :
    OriginalReflectionBudget I F B R Z₁ η ε δ Lscale :=
  { rb with scale_ge := h.trans rb.scale_ge }

/-- In the global estimate the three dyadic scales must also lie in the fixed power cap. -/
structure CappedReflectionBudget (I F B R : Ideal Eis) (Z₀ η ε δ Lscale Lcap saving : ℝ)
    extends OriginalReflectionBudget I F B R Z₀ η ε δ Lscale where
  source_cap : X⁻¹≤Z^Lcap
  row_scale_cap : QK≤Z^Lcap
  slot_scale_cap : QP≤Z^Lcap
  target_lower : -saving≤F₀-3*cstar/16-O₀/2


end OAI.SevenEighths.InverseReflectedPhase
