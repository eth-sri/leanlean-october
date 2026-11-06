module
public import OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowDeletedGeometry
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyDeletedRobustGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyLiveClippingDefect
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi e:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(he:0≤e)(hreserve:xi+11*e/7≤ s.width/14)
    (hlarge:5*s.width/6-e≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z ^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z ^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z ^short)+length Z (Z ^along)+z≤5*s.width/6 ∧
        length Z (Z ^short)+length Z (Z ^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z ^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z ^short)+6*κ*z≤ s.width)):= by
  have hbase : 0 < Z := zero_lt_one.trans hZ
  pm_8428 s.width xi s.width_nonneg hxi
  have hy₁ : 1 ≤ comparisonFirst Z s.width :=
    Real.one_le_rpow hZ.le (by linarith [s.width_nonneg])
  pm_6135 hy₂ s.width
  have hf : Real.logb Z (comparisonFirst Z s.width) = s.width/4 :=
    Real.logb_rpow hbase hZ.ne'
  have hl : Real.logb Z (comparisonSecond Z s.width X₁ X₂) = Real.logb Z (X₁*X₂)-s.width/4 := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂, Real.logb_rpow hbase hZ.ne']
  have hd₁ := divisor_reflection_range s hZ Mcap _ hwidth hy₁ D₁ hD₁
  have hd₂ := divisor_reflection_range s hZ Mcap _ hwidth hy₂ D₂ hD₂
  dsimp only at hd₁ hd₂
  rw [hf] at hd₁
  rw [hl] at hd₂
  have hn₁ := (divisor_norm s D₁ hD₁).1
  have hn₂ := (divisor_norm s D₂ hD₂).1
  pm_733 hlog₁ Real.logb_nonneg hZ hn₁ hlog₂ hn₂
  have hMcap : 0 ≤ Mcap := s.width_nonneg.trans hwidth
  have hLc : 0 ≤ L := by linarith
  have hslot : 0 ≤ (6*κ-1)*ell := mul_nonneg (by linarith) hell
  dsimp only
  refine ⟨hd₁.2.2, hd₂.2.2, by linarith, by linarith [s.width_nonneg],
    by linarith, hd₂.2.1, max_le hLc (by linarith [hd₂.1]), ?_⟩
  pm_7894 hp₁ D₁ hD₁
  pm_7894 hp₂ D₂ hD₂
  let along := Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
  have halong : Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏ P ∈ D₂, P).absNorm : ℝ)) = along := by
    rw [← hd₂.2.2]
    exact Real.logb_rpow hbase hZ.ne'
  rcases robust_deleted_reference_cases Z s.width X₁ X₂ ell z κ xi e (max 0 (s.width-along+xi))
    hZ s.width_nonneg hX₁ hX₂ hell hz hze hκ hxi he hreserve hlarge hcap D₁ D₂ hp₁ hp₂
    (by rw [halong]) with hc | hc
  · exact Or.inl (by simpa only [hd₁.2.2, hd₂.2.2] using hc)
  · apply Or.inr
    have hh := robust_reflected_low_admissible s.width xi e _ (max 0 (s.width-along+xi)) z κ
      he hreserve hc.2.1 hc.2.2
    simpa only [hd₁.2.2] using hh

end SevenEighths.CenteredMomentEnergyDeletedRobustGeometry

end

end OAI
