module
public import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths
public import OAI.NumberTheory.DirichletL.GaussSum.PowerfulParts
public import OAI.NumberTheory.DirichletL.CubicSieve.Ideal

@[expose] public section

namespace OAI.SevenEighths.InverseReflectedPhase
open CompletedGauss InverseTerminalWidths InverseMoment
local notation "Eis" => ActualEisensteinCubic.O

/-- Norm and scale conditions in the low reflected sector. -/
abbrev WithLowWidths
    (I Q : Ideal Eis) (Z₀ Z O₀ H za Nstar d ell0 shift Ck CO CH X QK QP η K P : ℝ) (T : Prop) : Prop :=
  Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
  (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
  Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
  Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
  Real.log (CH*Ck*CO)/Real.log Z≤η →
  normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
  0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
  Nstar=1+ell0+shift → H=Real.logb Z K → za=Real.logb Z P → Nstar=Real.logb Z X → T

/-- Norm and margin conditions for the original reflected sector. -/
abbrev WithOriginalWidths
    (I F B R : Ideal Eis) (Z₀ Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ η π
      Ck CO CH Cf X QK QP K P : ℝ) (T : Prop) : Prop :=
  Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
  (Ideal.absNorm I:ℝ)≤Ck*Z^M →
  Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
  Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
  (Ideal.absNorm F:ℝ)≤Cf*Z^V →
  Real.log (CH*Ck*CO)/Real.log Z≤η →
  Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
  CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
  Nstar=N-3*hhat → V≤d → hhat≤d+η →
  H=Real.logb Z K → za=Real.logb Z P → Nstar=Real.logb Z X →
  0≤M → 0≤O₀ → 0≤za → za≤z₀ →
  0<cstar → cstar/2≤margin → d≤cstar/200 →
  η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 → T

/-- The logarithmic allowance for the row and column windows. -/
abbrev WithRetainedSlotBudget
    (Z QK QP Lrow Lslot δ Lscale η ε π : ℝ) (T : Prop) : Prop :=
  QK≤Z^Lrow → QP≤Z^Lslot →
  Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π → T

/-- Dyadic norm ranges and bounded coefficients for a sector. -/
abbrev WithSectorWeights
    (rows Pset : Finset (Ideal Eis)) (QK QP : ℝ) (r aw : Ideal Eis → ℂ) (T : Prop) : Prop :=
  1≤QK → 2≤QP →
  (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
  (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
  (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) → T

end OAI.SevenEighths.InverseReflectedPhase
