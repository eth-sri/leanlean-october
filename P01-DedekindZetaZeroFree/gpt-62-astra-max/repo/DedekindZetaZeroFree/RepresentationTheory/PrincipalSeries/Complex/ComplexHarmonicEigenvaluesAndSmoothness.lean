module
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryPairing

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerSmoothness
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerChartEstimates
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypeMultiplicity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerHarmonicIntegrals

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory

theorem positive_intertwiner_infinityCoordinate_contDiff (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)) := by
  have hweyl (y : ℂ) : weyl * upperUnipotent y * weyl = lowerUnipotent y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  have hchart :
      infinityCoordinate (fun g : ComplexGL2 =>
        ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) =
      openCoordinate (fun g : ComplexGL2 =>
        ∫ x : ℂ, rightTranslate positiveParameter weyl f
          (weyl * upperUnipotent x * g) ∂characterHaar β) := by
    funext y
    change (∫ x : ℂ, f (weyl * upperUnipotent x * lowerUnipotent y)
        ∂characterHaar β) =
      ∫ x : ℂ, f ((weyl * upperUnipotent x * (weyl * upperUnipotent y)) * weyl)
        ∂characterHaar β
    simp only [mul_assoc, hweyl]
  rw [hchart]
  solve_by_elim [positive_intertwiner_openCoordinate_contDiff]

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped NNReal

private theorem weyl_upper_weyl (u : ℂ) :
    weyl * upperUnipotent u * weyl = lowerUnipotent u := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem lower_weyl (u : ℂ) :
    lowerUnipotent u * weyl = weyl * upperUnipotent u := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem weyl_translate_chartSeminorm (s : ℝ) (n : ℕ)
    (f : PrincipalSeries s) :
    chartSeminorm s n (rightTranslate s weyl f) = chartSeminorm s n f := by
  have hO : openCoordinate (rightTranslate s weyl f) = infinityCoordinate f := by
    funext u
    change f (weyl * upperUnipotent u * weyl) = f (lowerUnipotent u)
    rw [weyl_upper_weyl]
  have hI : infinityCoordinate (rightTranslate s weyl f) = openCoordinate f := by
    funext u
    change f (lowerUnipotent u * weyl) = f (weyl * upperUnipotent u)
    rw [lower_weyl]
  change chartSeminormValue s n (rightTranslate s weyl f) = chartSeminormValue s n f
  simp only [chartSeminormValue, hO, hI, max_comm]

theorem positive_intertwiner_infinity_chart_bounds (β : ℂˣ)
    (T : PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀ (f : PrincipalSeries positiveParameter) (g : ComplexGL2),
      T f g = ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) :
    ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      ∀ (f : PrincipalSeries positiveParameter) (u : ℂ),
        u ∈ Metric.closedBall (0 : ℂ) 1 →
          ‖iteratedFDeriv ℝ n (infinityCoordinate (T f)) u‖ ≤
            (C • orders.sup (chartSeminorm positiveParameter)) f := by
  intro n
  obtain ⟨orders, C, hbound⟩ := positive_intertwiner_open_chart_bounds β T hT n
  refine ⟨orders, C, ?_⟩
  intro f u hu
  have hcharts : infinityCoordinate (T f) =
      openCoordinate (T (rightTranslate positiveParameter weyl f)) := by
    funext v
    change T f (lowerUnipotent v) =
      T (rightTranslate positiveParameter weyl f) (weyl * upperUnipotent v)
    rw [hT, hT]
    apply integral_congr_ae
    filter_upwards [] with x
    change f (weyl * upperUnipotent x * lowerUnipotent v) =
      f ((weyl * upperUnipotent x * (weyl * upperUnipotent v)) * weyl)
    rw [mul_assoc (weyl * upperUnipotent x) (weyl * upperUnipotent v) weyl,
      weyl_upper_weyl]
  have hsup : orders.sup (chartSeminorm positiveParameter)
      (rightTranslate positiveParameter weyl f) =
      orders.sup (chartSeminorm positiveParameter) f := by
    classical
    clear hbound
    induction orders using Finset.induction_on with
    | empty => simp
    | @insert a orders ha ih =>
      simp only [Finset.sup_insert, Seminorm.sup_apply, weyl_translate_chartSeminorm, ih]
  rw [hcharts]
  have h := hbound (rightTranslate positiveParameter weyl f) u hu
  simpa only [Seminorm.smul_apply, hsup] using h

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxPrincipalSeriesCharts
open scoped NNReal

private theorem sSup_closedBall_le {F : ℂ → ℝ} {M : ℝ}
    (h : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, F x ≤ M) :
    sSup (F '' Metric.closedBall (0 : ℂ) 1) ≤ M := by
  refine csSup_le ⟨F 0, 0, Metric.mem_closedBall_self (by norm_num), rfl⟩ ?_
  rintro y ⟨x, hx, rfl⟩
  exact h x hx

theorem linearMap_isBounded_of_two_chart_derivative_bounds (s t : ℝ)
    (T : PrincipalSeries s →ₗ[ℂ] PrincipalSeries t)
    (hopen : ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      ∀ (f : PrincipalSeries s) (x : ℂ),
        x ∈ Metric.closedBall (0 : ℂ) 1 →
          ‖iteratedFDeriv ℝ n (openCoordinate (T f)) x‖ ≤
            (C • orders.sup (chartSeminorm s)) f)
    (hinfinity : ∀ n : ℕ, ∃ (orders : Finset ℕ) (C : ℝ≥0),
      ∀ (f : PrincipalSeries s) (u : ℂ),
        u ∈ Metric.closedBall (0 : ℂ) 1 →
          ‖iteratedFDeriv ℝ n (infinityCoordinate (T f)) u‖ ≤
            (C • orders.sup (chartSeminorm s)) f) :
    Seminorm.IsBounded (chartSeminorm s) (chartSeminorm t) T := by
  rw [Seminorm.IsBounded]
  intro n
  obtain ⟨ordersO, CO, hO⟩ := hopen n
  obtain ⟨ordersI, CI, hI⟩ := hinfinity n
  refine ⟨ordersO ∪ ordersI, max CO CI, ?_⟩
  rw [Seminorm.le_def]
  intro f
  set S : ℝ := ((ordersO ∪ ordersI).sup (chartSeminorm s)) f with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact apply_nonneg _ _
  have hsupO : (ordersO.sup (chartSeminorm s)) f ≤ S := by
    rw [hS]
    exact (Seminorm.le_def.mp (Finset.sup_mono
      Finset.subset_union_left)) f
  have hsupI : (ordersI.sup (chartSeminorm s)) f ≤ S := by
    rw [hS]
    exact (Seminorm.le_def.mp (Finset.sup_mono
      Finset.subset_union_right)) f
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (openCoordinate (T f)) x‖ ≤ (max CO CI : ℝ) * S := by
    intro x hx
    have h1 := hO f x hx
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans ?_
    calc _
        ≤ (CO : ℝ) * S := mul_le_mul_of_nonneg_left hsupO (by positivity)
      _ ≤ (max CO CI : ℝ) * S := mul_le_mul_of_nonneg_right (by
        exact_mod_cast le_max_left CO CI) hSnn
  have hbound' : ∀ x ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ n (infinityCoordinate (T f)) x‖ ≤ (max CO CI : ℝ) * S := by
    intro x hx
    have h1 := hI f x hx
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans ?_
    calc _
        ≤ (CI : ℝ) * S := mul_le_mul_of_nonneg_left hsupI (by positivity)
      _ ≤ (max CO CI : ℝ) * S := mul_le_mul_of_nonneg_right (by
        exact_mod_cast le_max_right CO CI) hSnn
  rw [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  change chartSeminormValue t n (T f) ≤ (max CO CI : ℝ) * S
  rw [chartSeminormValue]
  exact max_le (sSup_closedBall_le
    hbound) (sSup_closedBall_le
    hbound')

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators Matrix

private lemma complex_integral_mul (F : ℂ → ℂ) (c : ℂ) (hc : c ≠ 0) :
    (∫ x : ℂ, F (c * x)) = (‖c‖ ^ 2)⁻¹ • ∫ x : ℂ, F x := by
  let u : Circle := ⟨c / (‖c‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [norm_div, Complex.norm_real, abs_of_nonneg, hc]⟩
  have hcx (x : ℂ) : c * x = ‖c‖ • (rotation u x) := by
    change c * x = (‖c‖ : ℂ) * ((c / (‖c‖ : ℂ)) * x)
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)]
  simp_rw [hcx]
  rw [MeasureTheory.integral_comp (rotation u) (fun y => F (‖c‖ • y))]
  simpa only [Complex.finrank_real_complex] using
    Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ) F ‖c‖
      (hR := norm_nonneg _)

lemma character_integral_mul (β : ℂˣ) (F : ℂ → ℂ) (c : ℂ) (hc : c ≠ 0) :
    (∫ x : ℂ, F (c * x) ∂characterHaar β) =
      (‖c‖ ^ 2)⁻¹ • ∫ x : ℂ, F x ∂characterHaar β := by
  unfold characterHaar
  rw [integral_smul_measure, integral_smul_measure]
  change _ • (∫ x : ℂ, F (c * x)) = (‖c‖ ^ 2)⁻¹ • _ • (∫ x : ℂ, F x)
  rw [complex_integral_mul F c hc, smul_comm]
private alias positive_intertwiner_triangular_identity := DedekindZetaZeroFree.CurrentComplexBoundary.BoundaryPairing.weyl_upper
private lemma positive_intertwiner_weight (a d : ℂˣ) :
    inductionWeight positiveParameter d a * (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ =
      inductionWeight negativeParameter a d := by
  have hpos :=
    pow_pos (norm_pos_iff.mpr (div_ne_zero d.ne_zero a.ne_zero)) 2
  have hinv : ‖(a : ℂ) / (d : ℂ)‖ ^ 2 = (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ := by
    rw [← inv_div, norm_inv, inv_pow]
  simp only [inductionWeight, complexAbs, positiveParameter, negativeParameter, hinv]
  simp only [Real.rpow_eq_pow]
  have hneg : (‖(d : ℂ) / (a : ℂ)‖ ^ 2)⁻¹ =
      (‖(d : ℂ) / (a : ℂ)‖ ^ 2) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_one]
  rw [← Real.rpow_neg_eq_inv_rpow]
  conv_lhs => arg 2; rw [hneg]
  rw [← Real.rpow_add hpos]
  congr 1
  norm_num

lemma positive_intertwiner_covariance (β : ℂˣ) (f : PrincipalSeries positiveParameter) :
    HasCovariance negativeParameter (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) := by
  intro a d b g
  letI := characterHaar_isAddHaarMeasure β
  have hf := f.property.1
  change HasCovariance positiveParameter f at hf
  simp_rw [← mul_assoc, positive_intertwiner_triangular_identity, mul_assoc,
    hf d a 0]
  rw [integral_const_mul]
  have heq (x : ℂ) : (b + x * (d : ℂ)) / (a : ℂ) =
      (d : ℂ) / (a : ℂ) * x + b / (a : ℂ) := by ring
  simp_rw [heq, ← mul_assoc]
  rw [character_integral_mul β (fun x => f (weyl * upperUnipotent (x + b / (a : ℂ)) * g))
    ((d : ℂ) / (a : ℂ)) (div_ne_zero d.ne_zero a.ne_zero)]
  rw [integral_add_right_eq_self (fun x => f (weyl * upperUnipotent x * g)) (b / (a : ℂ)),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, positive_intertwiner_weight]

theorem positive_intertwiner_section (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β) ∈
      principalSeriesSubmodule negativeParameter := ⟨positive_intertwiner_covariance β f,
    positive_intertwiner_openCoordinate_contDiff β f,
    positive_intertwiner_infinityCoordinate_contDiff β f⟩

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators NNReal

variable (β : ℂˣ) (T : PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀ (f : PrincipalSeries positiveParameter) (g : ComplexGL2), T f g = ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)

include hT in
theorem positive_intertwiner_seminorm_bounds :
    Seminorm.IsBounded (chartSeminorm positiveParameter)
      (chartSeminorm negativeParameter) T := linearMap_isBounded_of_two_chart_derivative_bounds
    positiveParameter negativeParameter T
    (positive_intertwiner_open_chart_bounds β T hT)
    (positive_intertwiner_infinity_chart_bounds β T hT)

include hT in
theorem positive_intertwiner_continuous :
    Continuous T := by
  exact WithSeminorms.continuous_of_isBounded (⟨rfl⟩) (⟨rfl⟩) T
    (positive_intertwiner_seminorm_bounds β T hT)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section

namespace DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

noncomputable def compactSphereCoordinate (k : ComplexSU2) : Fin 3 → ℂ :=
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  ![(2 * (m 1 0 * star (m 1 1)).re : ℝ),
    (2 * (m 1 0 * star (m 1 1)).im : ℝ),
    (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ)]

noncomputable def polynomialLaplacian :
    MvPolynomial (Fin 3) ℂ →ₗ[ℂ] MvPolynomial (Fin 3) ℂ :=
  ∑ i : Fin 3, (MvPolynomial.pderiv i).toLinearMap.comp
    (MvPolynomial.pderiv i).toLinearMap

noncomputable def harmonicPolynomials (ℓ : ℕ) : Submodule ℂ (MvPolynomial (Fin 3) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ ⊓ polynomialLaplacian.ker

noncomputable def compactRestriction (s : ℝ) : PrincipalSeries s →ₗ[ℂ] (ComplexSU2 → ℂ) where
  toFun f k := f (complexSU2Embedding k)
  map_add' f h := rfl
  map_smul' c f := rfl

noncomputable def polynomialCompactRestriction :
    MvPolynomial (Fin 3) ℂ →ₗ[ℂ] (ComplexSU2 → ℂ) where
  toFun p k := MvPolynomial.eval (compactSphereCoordinate k) p
  map_add' p q := by ext k; simp
  map_smul' c p := by ext k; simp

section

variable (s : ℝ)

noncomputable def harmonicKType (ℓ : ℕ) : Submodule ℂ (PrincipalSeries s) :=
  ((harmonicPolynomials ℓ).map polynomialCompactRestriction).comap (compactRestriction s)

def IsKInvariant (U : Submodule ℂ (PrincipalSeries s)) : Prop :=
  ∀ (k : compactSubgroup) (f : PrincipalSeries s), f ∈ U → pi s k f ∈ U

def KEquivalent (U V : Submodule ℂ (PrincipalSeries s)) : Prop :=
  ∃ e : U ≃ₗ[ℂ] V, ∀ (k : compactSubgroup) (u v : U),
    (v : PrincipalSeries s) = pi s k u →
      (e v : PrincipalSeries s) = pi s k (e u)

theorem harmonicKType_multiplicity_one (ℓ : ℕ) :
    IsKInvariant s (harmonicKType s ℓ) ∧
    Module.finrank ℂ (harmonicKType s ℓ) = 2 * ℓ + 1 ∧
    (∀ U : Submodule ℂ (PrincipalSeries s), U ≤ harmonicKType s ℓ →
      IsKInvariant s U → U = ⊥ ∨ U = harmonicKType s ℓ) ∧
    (∀ U : Submodule ℂ (PrincipalSeries s), IsKInvariant s U →
      KEquivalent s U (harmonicKType s ℓ) → U = harmonicKType s ℓ) := by
  have hs := KPCplxHarmonicIntertwinerSpectrum.harmonicKType_structure s ℓ
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  intro U hU he
  exact KPCplxHarmonicIntertwinerSpectrum.harmonicKType_unique_copy s ℓ U hU he

end

section

variable (β : ℂˣ)

noncomputable def intertwinerIntegral (f : PrincipalSeries positiveParameter)
    (g : ComplexGL2) : ℂ :=
  ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β

theorem intertwinerIntegral_exists (f : PrincipalSeries positiveParameter) :
    (∀ g : ComplexGL2, Integrable
      (fun x : ℂ => f (weyl * upperUnipotent x * g)) (characterHaar β)) ∧
    intertwinerIntegral β f ∈ principalSeriesSubmodule negativeParameter := ⟨fun g => KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_integrable β f g,
    KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_section β f⟩

noncomputable def intertwinerLinearMap :
    PrincipalSeries positiveParameter →ₗ[ℂ] PrincipalSeries negativeParameter where
  toFun f := ⟨intertwinerIntegral β f, (intertwinerIntegral_exists β f).2⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    exact integral_add ((intertwinerIntegral_exists β f).1 g)
      ((intertwinerIntegral_exists β h).1 g)
  map_smul' c f := by
    apply Subtype.ext
    funext g
    exact integral_smul c (fun x : ℂ => f (weyl * upperUnipotent x * g))

theorem intertwinerLinearMap_continuous :
    Continuous (intertwinerLinearMap β) := KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_continuous β
    (intertwinerLinearMap β) (fun _ _ => rfl)

noncomputable def standardIntertwiner :
    PrincipalSeries positiveParameter →L[ℂ] PrincipalSeries negativeParameter :=
  ⟨intertwinerLinearMap β, intertwinerLinearMap_continuous β⟩

theorem standardIntertwiner_apply (f : PrincipalSeries positiveParameter)
    (g : ComplexGL2) :
    standardIntertwiner β f g =
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β := rfl

theorem standardIntertwiner_equivariant (g : ComplexPGL2)
    (f : PrincipalSeries positiveParameter) :
    standardIntertwiner β (pi positiveParameter g f) =
      pi negativeParameter g (standardIntertwiner β f) := by
  induction g using Quotient.inductionOn with
  | h g =>
    change standardIntertwiner β (pi positiveParameter (Matrix.ProjGenLinGroup.mk g) f) =
      pi negativeParameter (Matrix.ProjGenLinGroup.mk g) (standardIntertwiner β f)
    rw [pi_mk, pi_mk]
    apply Subtype.ext
    funext h
    change (∫ x : ℂ, f ((weyl * upperUnipotent x * h) * g) ∂characterHaar β) =
      ∫ x : ℂ, f (weyl * upperUnipotent x * (h * g)) ∂characterHaar β
    simp only [mul_assoc]

noncomputable def eigenvalue (ℓ : ℕ) : ℝ :=
  (3 * characterScale β / 2) *
    ∏ j ∈ Finset.Icc 1 ℓ, (((j : ℝ) - 1 / 3) / ((j : ℝ) + 1 / 3))

end

alias su2_matrix := DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.su2_matrix
noncomputable def openSU2 (x : ℂ) : ComplexSU2 := by
  let r := Real.sqrt (1 + Complex.normSq x)
  have hn := Complex.normSq_nonneg x
  have hr : r ^ 2 = 1 + Complex.normSq x := Real.sq_sqrt (by linarith)
  refine ⟨!![(star x) / r, -(1 / r); 1 / r, x / r], ?_⟩
  convert su2_matrix (1 / (r : ℂ)) (x / (r : ℂ)) ?_ using 1
  · simp [map_div₀]
  · simp only [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
    rw [← pow_two, hr]
    field_simp [show 1 + Complex.normSq x ≠ 0 by linarith]

private lemma openSU2_factor (x : ℂ) :
    ∃ (a d : ℂˣ) (b : ℂ), weyl * upperUnipotent x =
      upperTriangular a d b * complexSU2Embedding (openSU2 x) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicHighestWeightCyclicity.openSU2_factor <;> assumption

theorem compactRestriction_injective (s : ℝ) : Function.Injective (compactRestriction s) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.compactRestriction_injective <;> assumption
private alias spherical_compact := DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicHighestWeightCyclicity.spherical_compact

alias ComplexHarmonicEigenvaluesAndSmoothness.spherical_compact := spherical_compact

lemma inductionWeight_product (s u : ℝ) (a d : ℂˣ) :
    inductionWeight s a d * inductionWeight u a d = inductionWeight (s + u + 1 / 2) a d := by
  unfold inductionWeight
  rw [show 1 / 2 + (s + u + 1 / 2) = (1 / 2 + s) + (1 / 2 + u) by ring]
  refine (Real.rpow_add ?_ (1 / 2 + s) (1 / 2 + u)).symm
  unfold complexAbs
  exact pow_pos (norm_pos_iff.mpr (div_ne_zero a.ne_zero d.ne_zero)) _

section

variable (s t : ℝ)

noncomputable def changeParameter (f : PrincipalSeries s) : PrincipalSeries t := by
  let h := sphericalSection (t - s - 1 / 2)
  refine ⟨fun g => f g * h g, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a d b g
    dsimp only
    rw [f.property.1, h.property.1]
    have hw := inductionWeight_product s (t - s - 1 / 2) a d
    have he : s + (t - s - 1 / 2) + 1 / 2 = t := by ring
    rw [he] at hw
    push_cast
    rw [← hw]
    push_cast
    ring
  · exact f.property.2.1.mul h.property.2.1
  · exact f.property.2.2.mul h.property.2.2

private lemma changeParameter_restriction (f : PrincipalSeries s) :
    compactRestriction t (changeParameter s t f) = compactRestriction s f := by
  ext k
  change f (complexSU2Embedding k) * sphericalSection _ (complexSU2Embedding k) = _
  rw [spherical_compact, mul_one]
  rfl

theorem harmonicKType_compact_identification (ℓ : ℕ) :
    Function.Injective (compactRestriction s) ∧
    (harmonicKType s ℓ).map (compactRestriction s) =
      (harmonicKType t ℓ).map (compactRestriction t) := by
  refine ⟨compactRestriction_injective s, ?_⟩
  apply le_antisymm
  · rintro u ⟨f, hf, rfl⟩
    refine ⟨changeParameter s t f, ?_, changeParameter_restriction s t f⟩
    change compactRestriction t (changeParameter s t f) ∈ (harmonicPolynomials ℓ).map polynomialCompactRestriction
    rw [changeParameter_restriction]
    exact hf
  · rintro u ⟨f, hf, rfl⟩
    refine ⟨changeParameter t s f, ?_, changeParameter_restriction t s f⟩
    change compactRestriction s (changeParameter t s f) ∈ (harmonicPolynomials ℓ).map polynomialCompactRestriction
    rw [changeParameter_restriction]
    exact hf

end

theorem standardIntertwiner_harmonic_eigenvalue (β : ℂˣ) (ℓ : ℕ)
    (f : PrincipalSeries positiveParameter) (hf : f ∈ harmonicKType positiveParameter ℓ) :
    standardIntertwiner β f ∈ harmonicKType negativeParameter ℓ ∧
    compactRestriction negativeParameter (standardIntertwiner β f) =
      (eigenvalue β ℓ : ℂ) • compactRestriction positiveParameter f := by
  have hcompact := hf
  obtain ⟨p, hp, hpf⟩ := hcompact
  have hscalar : compactRestriction negativeParameter (standardIntertwiner β f) =
      (eigenvalue β ℓ : ℂ) • compactRestriction positiveParameter f := by
    ext k
    change (∫ x : ℂ, f (weyl * upperUnipotent x * complexSU2Embedding k) ∂characterHaar β) =
      (eigenvalue β ℓ : ℂ) * f (complexSU2Embedding k)
    have hfk : ∀ k : ComplexSU2, f (complexSU2Embedding k) =
        MvPolynomial.eval (compactSphereCoordinate k) p :=
      fun k => (congrFun hpf k).symm
    rw [hfk k]
    exact KPCplxHarmonicIntertwinerSpectrum.positive_intertwiner_harmonic_integral
      β ℓ p hp f hfk k
  refine ⟨?_, hscalar⟩
  change compactRestriction negativeParameter (standardIntertwiner β f) ∈
    (harmonicPolynomials ℓ).map polynomialCompactRestriction
  rw [hscalar]
  exact Submodule.smul_mem _ _ hf

private alias characterScale_pos' := DedekindZetaZeroFree.KPCplxCharacterHaar.characterScale_pos

private lemma eigenvalue_pos (β : ℂˣ) (ℓ : ℕ) : 0 < eigenvalue β ℓ := by
  have hc := characterScale_pos' β
  rw [eigenvalue]
  apply mul_pos
  · positivity
  · apply Finset.prod_pos
    intro j hj
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    apply div_pos <;> linarith

theorem eigenvalue_zero (β : ℂˣ) :
    eigenvalue β 0 = 3 * characterScale β / 2 ∧ 0 < eigenvalue β 0 := by
  constructor
  · rw [eigenvalue]; simp
  · exact eigenvalue_pos β 0

theorem eigenvalue_ne_zero (β : ℂˣ) (ℓ : ℕ) : eigenvalue β ℓ ≠ 0 :=
  ne_of_gt (eigenvalue_pos β ℓ)

private lemma one_harmonic : (1 : MvPolynomial (Fin 3) ℂ) ∈ harmonicPolynomials 0 := by
  constructor
  · exact MvPolynomial.isHomogeneous_one (Fin 3) ℂ
  · simp [LinearMap.mem_ker, polynomialLaplacian, LinearMap.sum_apply,
      LinearMap.comp_apply]

theorem standardIntertwiner_spherical (β : ℂˣ) :
    standardIntertwiner β (sphericalSection positiveParameter) =
      (3 * characterScale β / 2 : ℂ) • sphericalSection negativeParameter := by
  apply (harmonicKType_compact_identification negativeParameter negativeParameter 0).1
  rw [map_smul]
  have he := (standardIntertwiner_harmonic_eigenvalue β 0
    (sphericalSection positiveParameter) (by
      refine ⟨1, one_harmonic, ?_⟩
      ext k
      change MvPolynomial.eval (compactSphereCoordinate k) 1 =
        sphericalSection positiveParameter (complexSU2Embedding k)
      rw [spherical_compact]; simp)).2
  rw [(eigenvalue_zero β).1] at he
  rw [he]
  congr 1
  · push_cast; rfl
  · funext k
    exact (spherical_compact positiveParameter k).trans (spherical_compact negativeParameter k).symm

end DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

end

section

namespace DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

theorem harmonicKType_zero_scalar (s : ℝ) (f : PrincipalSeries s) (hf : f ∈ harmonicKType s 0) :
    f = (f 1) • sphericalSection s := by
  obtain ⟨p, hp, he⟩ := hf
  have hc : p = MvPolynomial.C (p.coeff 0) := by
    rw [← MvPolynomial.homogeneousComponent_zero p]
    exact (MvPolynomial.homogeneousComponent_eq_self hp.1).symm
  apply compactRestriction_injective s
  ext k
  have hek := congrFun he k
  change MvPolynomial.eval (compactSphereCoordinate k) p = f (complexSU2Embedding k) at hek
  rw [hc, MvPolynomial.eval_C] at hek
  have hek1 := congrFun he 1
  change MvPolynomial.eval (compactSphereCoordinate 1) p = f (complexSU2Embedding 1) at hek1
  rw [hc, MvPolynomial.eval_C, map_one] at hek1
  change f (complexSU2Embedding k) = f 1 * sphericalSection s (complexSU2Embedding k)
  rw [← hek, ← hek1]
  rw [spherical_compact, mul_one]

theorem harmonicKType_zero_eq_span (s : ℝ) :
    harmonicKType s 0 = Submodule.span ℂ {sphericalSection s} := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.harmonicKType_zero_eq_span <;> assumption

end DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

end
