module

public import DedekindZetaZeroFree.Theta.Unfolding.RationalOrbitFrequencyEquivalence
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.QuotientDescent

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

def thetaFiber {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) (q : KPAdditiveQuotient F) : ℂ :=
  T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out q) * g)

theorem thetaFiber_mk {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) (x : KPAdeles F) :
    thetaFiber R T v g (QuotientAddGroup.mk x) =
      T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) :=
  CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_mk T v 0
    (Metric.mem_ball_self T.radius_pos) x g

theorem thetaFiber_zero {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) : thetaFiber R T v g 0 = T.theta v g := by
  have hn : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
  simpa only [QuotientAddGroup.mk_zero, hn, one_mul] using thetaFiber_mk R T v g 0

theorem thetaFiber_continuous {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) : Continuous (thetaFiber R T v g) :=
  CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_continuous T v 0
    (Metric.mem_ball_self T.radius_pos) g

theorem rationalCharacter_out (a : F) (q : KPAdditiveQuotient F) :
    (adelicRationalFrequencyQuotientCharacter F a q : ℂ) =
      (adelicTraceCharacter F (algebraMap F (KPAdeles F) a * Quotient.out q) : ℂ) := by
  simpa using
    congrArg (fun z : Circle => (z : ℂ)) (adelicRationalFrequencyQuotientCharacter_mk F a (Quotient.out q))

def rationalPeriod {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : F) (g : Group R) : ℂ :=
  ∫ q, thetaFiber R T v g q *
    star (adelicRationalFrequencyQuotientCharacter F a q : ℂ) ∂Q.dq

theorem orbitFrequencyValue_eq_rationalPeriod {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient)
    (i : ThetaExpansion.SignedExpansion.OrbitIndex R) (g : Group R) :
    orbitFrequencyValue R Q T v i g = rationalPeriod R T v (orbitFrequency R i : F) g := by
  unfold orbitFrequencyValue orbitFrequencyIntegrand rationalPeriod
  simp only [rationalCharacter_out, thetaFiber, orbitFrequency]

theorem rationalPeriod_zero {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) :
    rationalPeriod R T v 0 g = upper R Q.dq (T.theta v) g := by
  unfold rationalPeriod upper thetaFiber
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by simp [rationalCharacter_out])

theorem thetaFiber_joint_continuous {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) :
    Continuous (fun p : Group R × KPAdditiveQuotient F => thetaFiber R T v p.1 p.2) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply ((IsOpenQuotientMap.id).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk
      )).continuous_comp_iff.mp
  simpa only [Function.comp_def, Prod.map, id_eq, thetaFiber_mk, Pi.mul_apply,
    Realization.theta] using
    (T.smooth v 0 (Metric.mem_ball_self T.radius_pos)).1.comp
      (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
        F R.A.zeta12 R.A.primitive_zeta12).comp
          (continuous_snd : Continuous (Prod.snd : Group R × KPAdeles F → KPAdeles F))).mul
        continuous_fst)

theorem rationalPeriod_continuous {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (a : F) : Continuous (rationalPeriod R T v a) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  letI : IsFiniteMeasureOnCompacts Q.dq := ⟨fun K _ => measure_lt_top Q.dq K⟩
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support isCompact_univ
  · exact ((thetaFiber_joint_continuous R T v).mul
      ((continuous_subtype_val.comp (continuous_adelicRationalFrequencyQuotientCharacter F a)).star.comp continuous_snd)).continuousOn
  · intro p x hp hx
    exact False.elim (hx (Set.mem_univ x))

theorem orbitFrequencyValue_continuous {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (i : ThetaExpansion.SignedExpansion.OrbitIndex R) :
    Continuous (orbitFrequencyValue R Q T v i) := by
  rw [(funext (orbitFrequencyValue_eq_rationalPeriod R T v i))]
  exact rationalPeriod_continuous R T v (orbitFrequency R i : F)

end DedekindZetaZeroFree.OrbitExpansion

end
