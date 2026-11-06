module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberIntegrability
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.Analyticity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

def localPeriod (T : Realization R Q) (v : R.A.UnitQuotient) (s : ℂ)
    (g : Group R) : ℂ := upper R Q.dq (T.cleared v s) g / s

theorem localPeriod_meromorphic (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) : MeromorphicOn (fun s => localPeriod T v s g)
      (Metric.ball (0 : ℂ) T.radius) :=
  (upper_cleared_analyticOnNhd T v g).meromorphicOn.div analyticOnNhd_id.meromorphicOn

theorem localPeriod_clears (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (hs0 : s ≠ 0) (g : Group R) :
    Integrable (fun q => T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) Q.dq ∧
    upper R Q.dq (T.cleared v s) g = s * localPeriod T v s g := by
  refine ⟨cleared_integrable T v s hs g, ?_⟩
  dsimp [localPeriod]
  field_simp

end DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod

end
