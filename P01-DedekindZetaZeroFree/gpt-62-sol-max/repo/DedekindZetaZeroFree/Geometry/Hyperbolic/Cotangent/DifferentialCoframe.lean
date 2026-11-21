module

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.LogarithmicCoframe

@[expose] public section

noncomputable section
open scoped Classical BigOperators ContDiff

namespace DedekindZetaZeroFree.CotangentLogCoframe

open HyperbolicChart

private theorem sum_real_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℝ) :
    ∑ i, (L (b i)) ^ 2 = ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L‖ ^ 2 := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    b.sum_sq_inner_left ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L)

theorem sum_complex_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b c : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℂ) :
    ∑ i, ‖L (b i)‖ ^ 2 = ∑ i, ‖L (c i)‖ ^ 2 := by
  have hRe := (sum_real_basis b (Complex.reCLM.comp L)).trans
    (sum_real_basis c (Complex.reCLM.comp L)).symm
  have hIm := (sum_real_basis b (Complex.imCLM.comp L)).trans
    (sum_real_basis c (Complex.imCLM.comp L)).symm
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hRe hIm
  simp only [Complex.sq_norm, Complex.normSq_apply, Finset.sum_add_distrib]
  simpa only [pow_two] using congrArg₂ (· + ·) hRe hIm

theorem differential_frame (d : ℕ) (f : HyperbolicChart.Space d → ℂ) (x : HyperbolicChart.Space d) (k : Fin d × Fin 3) :
    (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) k =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ k)) := by
  rcases k with ⟨i, k⟩
  fin_cases k
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))) =
        HyperbolicChart.coordinateVector d i 2 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (0 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative]
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector d i 0 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (1 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector d i 1 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (2 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]

theorem differential_frame_sum (d : ℕ) (f : HyperbolicChart.Space d → ℂ) (x : HyperbolicChart.Space d) (v : RealCoefficients d) :
    fderiv ℝ f x (CotangentLogCoframe.H d x v) =
      ∑ k, (v k : ℂ) *
        (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) k := by
  conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun _ ℝ) v]
  simp only [EuclideanSpace.basisFun_repr, map_sum, map_smul, differential_frame,
    RCLike.real_smul_eq_coe_mul]
  rfl

theorem differential_norm_isometry (d : ℕ)
    (ψ : HyperbolicChart.Space d → HyperbolicChart.Space d)
    (x : HyperbolicChart.Space d)
    (hψ : DifferentiableAt ℝ ψ x)
    (hm : ∀ v w, HyperbolicChart.metric d (ψ x)
      (fderiv ℝ ψ x v) (fderiv ℝ ψ x w) = HyperbolicChart.metric d x v w)
    (f : HyperbolicChart.Space d → ℂ) (hf : DifferentiableAt ℝ f (ψ x)) :
    (∑ i, ∑ k, ‖HyperbolicChart.differential d (f ∘ ψ) x i k‖ ^ 2) =
    ∑ i, ∑ k, ‖HyperbolicChart.differential d f (ψ x) i k‖ ^ 2 := by
  let Q : EuclideanSpace ℝ (Fin d × Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    (CotangentLogCoframe.C d (ψ x)).toContinuousLinearMap.comp
      ((fderiv ℝ ψ x).comp (CotangentLogCoframe.H d x).toContinuousLinearMap)
  have hQ : ∀ v w, inner ℝ (Q v) (Q w) = inner ℝ v w := by
    intro v w
    change inner ℝ (CotangentLogCoframe.C d (ψ x)
      (fderiv ℝ ψ x (CotangentLogCoframe.H d x v)))
      (CotangentLogCoframe.C d (ψ x) (fderiv ℝ ψ x (CotangentLogCoframe.H d x w))) = _
    rw [CotangentLogCoframe.inner_C, hm, ← CotangentLogCoframe.inner_C]
    simp [CotangentLogCoframe.H]
  let q₀ : EuclideanSpace ℝ (Fin d × Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    ⟨Q.toLinearMap, (LinearMap.norm_map_iff_inner_map_map Q).2 hQ⟩
  let q := LinearIsometryEquiv.ofSurjective q₀
    (LinearMap.surjective_of_injective (f := q₀.toLinearMap) q₀.injective)
  let L := (fderiv ℝ f (ψ x)).comp (CotangentLogCoframe.H d (ψ x)).toContinuousLinearMap
  have hh : ∀ v, fderiv ℝ ψ x (CotangentLogCoframe.H d x v) =
      CotangentLogCoframe.H d (ψ x) (q v) := by
    intro v
    apply (CotangentLogCoframe.C d (ψ x)).injective
    simp only [CotangentLogCoframe.H, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hsum := sum_complex_basis ((EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).map q)
    (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ) L
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hsum
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [← CotangentLogCoframe.j_apply d (HyperbolicChart.differential d (f ∘ ψ) x) i k,
      differential_frame, fderiv_comp x hf hψ]
    simp only [ContinuousLinearMap.comp_apply, hh, OrthonormalBasis.map_apply, L]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [← CotangentLogCoframe.j_apply d (HyperbolicChart.differential d f (ψ x)) i k,
      differential_frame]
    rfl

end DedekindZetaZeroFree.CotangentLogCoframe

namespace DedekindZetaZeroFree.HyperbolicChart

private theorem derivative_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem differential_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i,2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using derivative_smoothAt d g x hg i 2
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 0)
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 1)

end DedekindZetaZeroFree.HyperbolicChart
