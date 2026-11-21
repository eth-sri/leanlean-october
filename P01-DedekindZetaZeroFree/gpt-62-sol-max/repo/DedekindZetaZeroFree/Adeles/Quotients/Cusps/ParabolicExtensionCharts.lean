module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.EquivariantAffineUnitCharts
public import DedekindZetaZeroFree.Adeles.Lattices.Cusps.ParabolicExtension

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPCuspMonodromy

theorem finite_adelic_cusp_charts
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hcompact : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hopen : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    let Γ := KPFiniteComponents.arithmeticStabilizer F U g
    let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
    ∃ (D : KPCuspCharts.ParabolicData F S),
      Nonempty (KPCuspCharts.ChartOutput F hF S D) := by
  obtain ⟨D, hdisc, hlattice⟩ :=
    KPCuspFiniteArithmetic.finite_adelic_parabolic_extension_lattice
      F hF U hcompact hopen g q σ hσ
  exact ⟨D, KPCuspCharts.chartOutput_nonempty F hF _ D hdisc hlattice⟩

end DedekindZetaZeroFree.KPCuspMonodromy

end

end
