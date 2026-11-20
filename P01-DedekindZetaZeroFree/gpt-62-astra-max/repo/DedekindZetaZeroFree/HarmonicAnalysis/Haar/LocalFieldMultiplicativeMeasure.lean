module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TruncatedCubicUnitIndices

@[expose] public section

namespace DedekindZetaZeroFree.KPCubicHaarTransport
noncomputable section
open MeasureTheory ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def abs (x : K) : ℝ := by
  classical
  exact if x = 0 then 0 else
    (KPCubicUnitIndices.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x))

def haar [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) : Measure Kˣ :=
  Measure.comap (fun x : Kˣ => (x : K))
    (dx.withDensity (fun x => ENNReal.ofReal ((abs K x)⁻¹)))

end
end DedekindZetaZeroFree.KPCubicHaarTransport
