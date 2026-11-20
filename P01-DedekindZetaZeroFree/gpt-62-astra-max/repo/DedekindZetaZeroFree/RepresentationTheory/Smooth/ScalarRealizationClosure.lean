module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.AdditivePeriodization
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology InnerProductSpace ComplexOrder
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rawSmoothCarrier : Set (KPMsFixedHaarDisintegration.X F ζ hζ → ℂ) :=
  {f | KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f ∧
    (∀ ε x, f (KPSmoothActualFlowData.rightTranslate F ζ hζ
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) x) =
        (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) * f x) ∧
    ∃ U : KPMsRationalCompactCrossPairing.Level F ζ hζ,
      ∀ (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) x,
        f (KPSmoothActualFlowData.rightTranslate F ζ hζ u.val x) = f x}

theorem rawSmoothCarrier_closed :
    (0 : KPMsFixedHaarDisintegration.X F ζ hζ → ℂ) ∈ rawSmoothCarrier F ζ hζ := by
  have hfinite : ActualFiniteFactor.finiteSubgroup F ζ hζ =
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
    congr 1
    ext x
    simp [PGLComplex.AdelicSlicesRaw.finiteSubgroup,
      PGLComplex.AdelicSlicesRaw.finiteTuples,
      KPGlobalTorusFunctionData.finitePart, Subgroup.mem_iInf]
  have hlevel : Nonempty (KPMsRationalCompactCrossPairing.Level F ζ hζ) := by
    obtain ⟨J, _⟩ := ActualFiniteFactor.productLevels_cofinal F ζ hζ
      Set.univ (Filter.univ_mem)
    have h : Nonempty (CompactOpenLevel (ActualFiniteFactor.finiteSubgroup F ζ hζ)) :=
      ⟨⟨(ActualFiniteFactor.productLevel F ζ hζ J).subgroup,
        (ActualFiniteFactor.productLevel F ζ hζ J).compact⟩⟩
    rw [hfinite] at h
    exact h
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨⟨continuous_const, fun _ => contDiff_const⟩, ?_, ?_⟩
  · intro ε x
    simp
  · obtain ⟨U⟩ := hlevel
    exact ⟨U, fun _ _ => rfl⟩
end DedekindZetaZeroFree.KPGlobalResidualKernel

end
