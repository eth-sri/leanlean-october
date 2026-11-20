module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexIntertwinerImageAndHarmonicExtraction

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxUpperRootSeminormDifferentiation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open Filter Topology
open scoped Matrix.Norms.Elementwise

section

variable (β : ℂˣ) (e : Theta β) (v : ℂ)

theorem upperRoot_open_joint_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ =>
      orbitOpenCoordinate negativeParameter (e : PrincipalSeries negativeParameter)
        ((upperUnipotent ((p.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ), p.2)) := by
  apply contDiffOn_univ.mp
  apply (image_smooth β e).1.comp _ _
  · apply ContDiff.contDiffOn
    apply ContDiff.prodMk _ contDiff_snd
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ × ℂ => (fun i j => (upperUnipotent ((x.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ) i j))
    rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent]
    all_goals try exact contDiff_const
    exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const
  · intro p hp
    exact Matrix.GeneralLinearGroup.det_ne_zero _

theorem upperRoot_infinity_joint_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℂ =>
      orbitInfinityCoordinate negativeParameter (e : PrincipalSeries negativeParameter)
        ((upperUnipotent ((p.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ), p.2)) := by
  apply contDiffOn_univ.mp
  apply (image_smooth β e).2.comp _ _
  · apply ContDiff.contDiffOn
    apply ContDiff.prodMk _ contDiff_snd
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ × ℂ => (fun i j => (upperUnipotent ((x.1 : ℂ) * v) : Matrix (Fin 2) (Fin 2) ℂ) i j))
    rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent]
    all_goals try exact contDiff_const
    exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const
  · intro p hp
    exact Matrix.GeneralLinearGroup.det_ne_zero _

end

alias joint_spatial_jets := DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.HarmonicRaising.joint_spatial_jets

namespace SmoothQuotient
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
section

variable (F : ℝ × E → V)

noncomputable def partialT (p : ℝ × E) : V :=
  fderiv ℝ (fun t => F (t,p.2)) p.1 1
lemma partialT_smooth (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (partialT F) := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.partialT_smooth <;> assumption
lemma partialT_deriv (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : E) :
    HasDerivAt (fun s => F (s,x)) (partialT F (t,x)) t := ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt
noncomputable def extSlope (p : ℝ × E) : V :=
  ∫ s : ℝ in 0..1, partialT F (s * p.1, p.2)
lemma extSlope_continuous (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (extSlope F) := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.extSlope_continuous <;> assumption
lemma extSlope_zero (x : E) :
    extSlope F (0,x) = partialT F (0,x) := by
  simp [extSlope, intervalIntegral.integral_const]
lemma extSlope_ne (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (ht : t ≠ 0) (x : E) :
    extSlope F (t,x) = t⁻¹ • (F (t,x) - F (0,x)) := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.extSlope_ne <;> assumption
lemma slope_locally_uniform (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [WeaklyLocallyCompactSpace E] :
    TendstoLocallyUniformlyOn (fun t x => t⁻¹ • (F (t,x) - F (0,x)))
      (fun x => partialT F (0,x)) (𝓝[≠] (0:ℝ)) Set.univ := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.slope_locally_uniform <;> assumption

end
alias slice_smooth := DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.slice_smooth

variable (F : ℝ × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F) [WeaklyLocallyCompactSpace E] (n : ℕ)

include hF in
lemma jets_partialT :
    iteratedFDeriv ℝ n (fun x => partialT F (0,x)) =
      (fun x => partialT (fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) (0,x)) := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.jets_partialT <;> assumption
include hF in
lemma quotient_jets_uniform (S : Set E) (hS : IsCompact S) :
    TendstoUniformlyOn (fun t x => iteratedFDeriv ℝ n
      (fun x => t⁻¹ • (F (t,x) - F (0,x))) x)
      (iteratedFDeriv ℝ n (fun x => partialT F (0,x))) (𝓝[≠] (0:ℝ)) S := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.quotient_jets_uniform <;> assumption

include hF in
lemma sup_jet_error_tendsto (S : Set E) (hS : IsCompact S) (hne : S.Nonempty) :
    Tendsto (fun t => sSup ((fun x => ‖iteratedFDeriv ℝ n
      (fun x => t⁻¹ • (F (t,x) - F (0,x)) - partialT F (0,x)) x‖) '' S))
      (𝓝[≠] (0:ℝ)) (𝓝 (0:ℝ)) := by apply @DedekindZetaZeroFree.KPCplxHarmonicPropagation.RaisingTopology.SmoothQuotient.sup_jet_error_tendsto <;> assumption
end SmoothQuotient

private lemma matrixFunction_gl (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by apply @DedekindZetaZeroFree.KPCplxPrincipalSeriesMatrixSmooth.matrixFunction_coe <;> assumption
private lemma upper_zero : upperUnipotent 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent]
section

variable (s : ℝ) (f : PrincipalSeries s) (v : ℂ) (t : ℝ) (x : ℂ)

private lemma orbit_open_eq :
    orbitOpenCoordinate s f ((upperUnipotent ((t:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),x) =
    f ((weyl * upperUnipotent x) * upperUnipotent ((t:ℂ)*v)) := by
  unfold orbitOpenCoordinate
  change matrixFunction f (((weyl * upperUnipotent x) * upperUnipotent ((t:ℂ)*v) : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) = _
  exact matrixFunction_gl _ _
private lemma orbit_infinity_eq :
    orbitInfinityCoordinate s f ((upperUnipotent ((t:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),x) =
    f (lowerUnipotent x * upperUnipotent ((t:ℂ)*v)) := by
  unfold orbitInfinityCoordinate
  change matrixFunction f ((lowerUnipotent x * upperUnipotent ((t:ℂ)*v) : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) = _
  exact matrixFunction_gl _ _

end

theorem upperRoot_differenceQuotient_chartSeminorm_of_pointwise
    (β : ℂˣ) (e : Theta β) (v : ℂ)
    (D : PrincipalSeries negativeParameter)
    (hD : ∀ g : ComplexGL2,
      HasDerivAt (fun t : ℝ => (e : PrincipalSeries negativeParameter)
        (g * upperUnipotent ((t : ℂ) * v))) (D g) 0)
    (n : ℕ) :
    Tendsto (fun t : ℝ => chartSeminorm negativeParameter n
      ((((t⁻¹ : ℂ) •
        (imageAction β (Matrix.ProjGenLinGroup.mk
          (upperUnipotent ((t : ℂ) * v))) e - e) : Theta β) :
          PrincipalSeries negativeParameter) - D))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let F : ℝ × ℂ → ℂ := fun p => orbitOpenCoordinate negativeParameter
    (e : PrincipalSeries negativeParameter) ((upperUnipotent ((p.1:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),p.2)
  let H : ℝ × ℂ → ℂ := fun p => orbitInfinityCoordinate negativeParameter
    (e : PrincipalSeries negativeParameter) ((upperUnipotent ((p.1:ℂ)*v) : Matrix (Fin 2) (Fin 2) ℂ),p.2)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := upperRoot_open_joint_contDiff β e v
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := upperRoot_infinity_joint_contDiff β e v
  have hFD (x : ℂ) : SmoothQuotient.partialT F (0,x) = openCoordinate D x := by
    have hd := hD (weyl * upperUnipotent x)
    have heq : (fun t : ℝ => F (t,x)) = (fun t : ℝ =>
      (e : PrincipalSeries negativeParameter) ((weyl * upperUnipotent x) * upperUnipotent ((t:ℂ)*v))) := by
      funext t; exact orbit_open_eq _ _ _ _ _
    rw [← heq] at hd
    exact hd.deriv
  have hHD (x : ℂ) : SmoothQuotient.partialT H (0,x) = infinityCoordinate D x := by
    have hd := hD (lowerUnipotent x)
    have heq : (fun t : ℝ => H (t,x)) = (fun t : ℝ =>
      (e : PrincipalSeries negativeParameter) (lowerUnipotent x * upperUnipotent ((t:ℂ)*v))) := by
      funext t; exact orbit_infinity_eq _ _ _ _ _
    rw [← heq] at hd
    exact hd.deriv
  let S := Metric.closedBall (0:ℂ) 1
  have hS : IsCompact S := isCompact_closedBall _ _
  have hne : S.Nonempty := ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  have hf := SmoothQuotient.sup_jet_error_tendsto F hF n S hS hne
  have hh := SmoothQuotient.sup_jet_error_tendsto H hH n S hS hne
  have hmax := hf.max hh
  simp only [max_self] at hmax
  convert hmax using 1
  funext t
  change chartSeminormValue negativeParameter n _ = _
  unfold chartSeminormValue
  congr 2
  · congr 1
    funext x
    congr 2
    funext y
    rw [hFD]
    change (t⁻¹:ℂ) * ((e : PrincipalSeries negativeParameter)
      ((weyl * upperUnipotent y) * upperUnipotent ((t:ℂ)*v)) - (e : PrincipalSeries negativeParameter) (weyl * upperUnipotent y)) - D (weyl * upperUnipotent y) = _
    simp [openCoordinate, F, orbit_open_eq, upper_zero, Complex.real_smul]
  · congr 1
    funext x
    congr 2
    funext y
    rw [hHD]
    change (t⁻¹:ℂ) * ((e : PrincipalSeries negativeParameter)
      (lowerUnipotent y * upperUnipotent ((t:ℂ)*v)) - (e : PrincipalSeries negativeParameter) (lowerUnipotent y)) - D (lowerUnipotent y) = _
    simp [infinityCoordinate, H, orbit_infinity_eq, upper_zero, Complex.real_smul]

end DedekindZetaZeroFree.KPCplxUpperRootSeminormDifferentiation
