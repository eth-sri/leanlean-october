module

public import DedekindZetaZeroFree.Eisenstein.Induction.AdelicSectionDescent
public import DedekindZetaZeroFree.Metaplectic.Torus.LocalNorms

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusEvaluation
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)















































 theorem norm_mul (q : HeightOneSpectrum (𝓞 F))
    (x t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate (x*t))) (1/6 : ℝ) : ℂ) =
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate x)) (1/6 : ℝ) : ℂ) *
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate t)) (1/6 : ℝ) : ℂ) := by
  rw [map_mul]
  simp only [KPGlobalCenterRationalCharacter.localAbs, Units.val_mul, nnnorm_mul, NNReal.coe_mul]
  exact (congrArg (fun z : ℝ => (z : ℂ)) (Real.mul_rpow
    (NNReal.coe_nonneg ‖((C.canonical q).borel.coordinate x : q.adicCompletion F)‖₊)
    (NNReal.coe_nonneg ‖((C.canonical q).borel.coordinate t : q.adicCompletion F)‖₊))).trans
      (Complex.ofReal_mul _ _)

 theorem untwisted_tau (q : HeightOneSpectrum (𝓞 F))
    (v : LocalFiber F ζ hζ P C q) (x t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    localUntwistedEvaluation F ζ hζ P C q (localTau F ζ hζ P C q t v) x =
    localUntwistedEvaluation F ζ hζ P C q v (x*t) *
      (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate t)) (1/6 : ℝ) : ℂ) := by
  unfold localUntwistedEvaluation
  change v.val (x*t) / _ = _
  rw [norm_mul F ζ hζ P C]
  have hx : (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
    ((C.canonical q).borel.coordinate x)) (1/6 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F _ _) _).ne'
  have ht : (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
    ((C.canonical q).borel.coordinate t)) (1/6 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F _ _) _).ne'
  field_simp























 theorem phase_mul (x u : RestrictedCover F ζ hζ) :
    (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ ((x*u) (Sum.inl w)).epsilon : ℂ)) =
    (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (x (Sum.inl w)).epsilon : ℂ)) *
    (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (u (Sum.inl w)).epsilon : ℂ)) := by
  have hm w : ((x*u) (Sum.inl w)).epsilon = (x (Sum.inl w)).epsilon * (u (Sum.inl w)).epsilon := by
    change (x (Sum.inl w) * u (Sum.inl w)).epsilon = _
    rw [KPLocalCover.mul_epsilon, KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  simp_rw [hm, map_mul, Units.val_mul]
  exact Finset.prod_mul_distrib

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusEvaluation

end
