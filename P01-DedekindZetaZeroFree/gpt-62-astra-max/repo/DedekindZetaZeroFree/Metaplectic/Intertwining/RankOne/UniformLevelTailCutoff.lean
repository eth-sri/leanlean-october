module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailInducingActionAndCubeClasses

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actual_level_tail_uniform (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) :
    ∀ᶠ v : LocalField F q in nhds 0, ∀ (s : ℂ)
      (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
      (k : S.iwasawa.compact.toOpenSubgroup) (hv : v ≠ 0),
      ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)
        (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))).val
        (kernelW (LocalField F q) S.borel ε *
          (S.borel.upperRoot (Multiplicative.ofAdd (-(v⁻¹))) : ActualCover F ζ hζ q) * k)) =
      (ordinaryIota F ζ hζ (actualTailPhase F ζ hζ q (Units.mk0 v hv)) : ℂ) •
        actualRootAction F ζ hζ q S P ε s (Units.mk0 v hv) (φ.val.val k) := by
  filter_upwards [(lowerRootCoordinate_uniform_cutoff (LocalField F q) S.borel S.iwasawa J)] with v hvJ
  intro s φ k hv
  let f := compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)
    φ
  let j : J.toOpenSubgroup := ⟨(k : ActualCover F ζ hζ q)⁻¹ *
    actualLowerRoot F ζ hζ q v * k, by
      rw [actualLowerRoot_eq F ζ hζ q S P]
      exact hvJ k⟩
  have he : f.val (actualLowerRoot F ζ hζ q v * k) = f.val k := by
    simpa [principalSeries, vectorRightTranslation, j, mul_assoc] using (congrFun (congrArg Subtype.val (((compact_level_identification S.borel P S.iwasawa (sourceSign ε) J hJ
      (sourceParameter ε s) _).mp φ.property) j)) k)
  have hk : f.val k = φ.val.val k := by
    exact congrFun (congrArg Subtype.val ((compactTrivialization S.borel P S.iwasawa (sourceSign ε)
      (sourceParameter ε s)).symm_apply_apply φ.val)) k
  simpa only [Units.val_mk0, Units.val_inv_eq_inv_val, he, hk] using (actual_tail_inducing F ζ hζ q S P ε s f (Units.mk0 v hv) k)

end DedekindZetaZeroFree.KPRankOneShellRepair

end
