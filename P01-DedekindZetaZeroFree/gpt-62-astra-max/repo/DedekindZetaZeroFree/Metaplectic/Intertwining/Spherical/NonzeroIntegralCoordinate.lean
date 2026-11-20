module

public import DedekindZetaZeroFree.Eisenstein.Induction.UnramifiedCompactFixedSections
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.CubicUnitShells

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
    (S : RawFiniteInducingData F ζ hζ q)

private alias signed_weyl_mem_actual_compact := CubicUnitShells.shell_weyl_mem
 theorem spherical_integrand_on_integer_ring
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (x : (valuation (LocalField F q)).integer) :
    f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd (x : LocalField F q)) : ActualCover F ζ hζ q)) = f.val 1 := by
  let k := ((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
    (KPGoodCompactSplitting.kStar F ζ hζ q ht))
  have hn : (S.borel.upperRoot (Multiplicative.ofAdd x) :
      ActualCover F ζ hζ q) ∈ k.range := by
    refine ⟨KPStandardLocalRootLifts.integralN F q x, ?_⟩
    rw [(S.openCell P).upper_eq]
    change _ = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) x)
    rw [KPStandardLocalRootLifts.N_eq_compact F ζ hζ q ht x]
    rfl
  obtain ⟨a, ha⟩ := k.range.mul_mem (k.range.inv_mem (signed_weyl_mem_actual_compact F ζ hζ q S ht)) hn
  have hf := congrArg (fun z : sectionSpace S.borel P .plus 0 => z.val 1) (hfixed a)
  change f.val (1 * k a) = f.val 1 at hf
  simpa only [one_mul, ha] using hf

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
