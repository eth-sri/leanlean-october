module

public import RequestProject.TraceH1
public import RequestProject.LpBoundedMultiplier

/-!
# Multiplication in the actual weak-gradient H¹ space

A globally smooth coefficient with bounded value and first derivatives defines
a genuine bounded H¹ multiplication operator. The product rule is proved by
testing the original weak gradient against the compact product aφ. Smooth
compact coefficients supply the bounds, so this applies to actual cutoff
coordinate functions without an assumed weak product rule.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {γ : ℝ → ℂ}

/-- Bounds on an actual smooth coefficient and its two real derivatives. -/
structure SmoothH1Coefficient where
  toFun : ℂ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  value_bound : ∀ z, ‖toFun z‖ ≤ bound
  derivative_bound : ∀ (i : Fin 2) z, ‖fderiv ℝ toFun z (coordDir i)‖ ≤ bound


instance : CoeFun SmoothH1Coefficient fun _ => ℂ → ℂ := ⟨SmoothH1Coefficient.toFun⟩

/-- Smooth compact coefficients have actual global value and derivative bounds. -/
theorem smoothTraceTests_exists_h1Coefficient_bound (a : smoothTraceTests) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ z, ‖a z‖ ≤ B) ∧
      ∀ i z, ‖fderiv ℝ a z (coordDir i)‖ ≤ B := by
  obtain ⟨B, hB⟩ := a.2.2.1.exists_bound_of_continuous a.2.1.continuous
  obtain ⟨B₀, hB₀⟩ := (a.2.dirD (coordDir 0)).2.1.exists_bound_of_continuous
    (a.2.dirD (coordDir 0)).1.continuous
  obtain ⟨B₁, hB₁⟩ := (a.2.dirD (coordDir 1)).2.1.exists_bound_of_continuous
    (a.2.dirD (coordDir 1)).1.continuous
  refine ⟨max 0 (max B (max B₀ B₁)), le_max_left _ _, ?_, ?_⟩
  · intro z
    exact (hB z).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro i z
    fin_cases i
    · exact (hB₀ z).trans ((le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    · exact (hB₁ z).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

/-- An actual compact smooth function as a bounded H¹ coefficient. -/
def smoothTraceTestsH1Coefficient (a : smoothTraceTests) : SmoothH1Coefficient where
  toFun := a
  smooth := a.2.1
  bound := Classical.choose (smoothTraceTests_exists_h1Coefficient_bound a)
  bound_nonneg := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).1
  value_bound := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.1
  derivative_bound := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.2


theorem coefficient_derivative_continuous (a : SmoothH1Coefficient) i :
    Continuous (fun z => fderiv ℝ a z (coordDir i)) :=
  ((a.smooth.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiff_const).continuous

def h1SmoothCoefficientL2 Ω (a : SmoothH1Coefficient) : L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier a a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound)

def h1SmoothCoefficientDerivativeL2 Ω (a : SmoothH1Coefficient) (i : Fin 2) :
    L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (fun z => fderiv ℝ a z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i))

theorem h1SmoothCoefficientL2_ae Ω a u :
    (h1SmoothCoefficientL2 Ω a u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => a z * u z :=
  lpBoundedMultiplier_ae (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound) u

theorem h1SmoothCoefficientDerivativeL2_ae Ω a
    (i : Fin 2) u :
    (h1SmoothCoefficientDerivativeL2 Ω a i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i) * u z :=
  lpBoundedMultiplier_ae (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i))
    (coefficient_derivative_continuous a i).aestronglyMeasurable
    (Eventually.of_forall (a.derivative_bound i)) u

theorem norm_h1SmoothCoefficientL2_apply_le Ω a
    u : ‖h1SmoothCoefficientL2 Ω a u‖ ≤ a.bound * ‖u‖ :=
  norm_lpBoundedMulLin_le (a : ℂ → ℂ) a.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall a.value_bound) u

theorem coefficient_test_mul  (a : SmoothH1Coefficient)
     (hφ : TestFunction Ω φ) : TestFunction Ω (fun z => a z * φ z) :=
  ⟨a.smooth.mul hφ.1, hφ.2.1.mul_left, tsupport_mul_subset_right.trans hφ.2.2⟩

/-- The genuine weak product rule, with both derivative terms in actual L². -/
theorem isWeakGradient_h1SmoothCoefficientL2  a
    {u : L2 Ω}  (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (h1SmoothCoefficientL2 Ω a u)
      (fun i => h1SmoothCoefficientL2 Ω a (g i) +
        h1SmoothCoefficientDerivativeL2 Ω a i u) := by
  intro φ hφ i
  have hweak := hu (fun z => a z * φ z) (coefficient_test_mul a hφ) i
  have hid : Integrable (fun z => h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z)
      (volume.restrict Ω) :=
    (Lp.memLp (h1SmoothCoefficientDerivativeL2 Ω a i u)).integrable_mul hφ.memLp
  rw [show (∫ z in Ω, u z * fderiv ℝ (fun w => a w * φ w) z (coordDir i)) = (∫ z in Ω, h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z) + ∫ z in Ω, h1SmoothCoefficientL2 Ω a u z * fderiv ℝ φ z (coordDir i) by
    calc
      _ = ∫ z in Ω, h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z +
          h1SmoothCoefficientL2 Ω a u z * fderiv ℝ φ z (coordDir i) := by
        apply integral_congr_ae
        filter_upwards [h1SmoothCoefficientL2_ae Ω a u,
          h1SmoothCoefficientDerivativeL2_ae Ω a i u] with z hz hdz
        rw [(show fderiv ℝ (fun w => a w * φ w) z (coordDir i) = fderiv ℝ (a : ℂ → ℂ) z (coordDir i) * φ z + a z * fderiv ℝ φ z (coordDir i) by
          rw [fderiv_fun_mul (a.smooth.differentiable (by simp) z)
            (hφ.1.differentiable (by simp) z)]
          simp
          ring), hz, hdz]
        ring
      _ = _ := integral_add hid ((Lp.memLp (h1SmoothCoefficientL2 Ω a u)).integrable_mul (hφ.memLp_fderiv (coordDir i))), show (∫ z in Ω, (g i) z * (a z * φ z)) = ∫ z in Ω, h1SmoothCoefficientL2 Ω a (g i) z * φ z by
    apply integral_congr_ae
    filter_upwards [h1SmoothCoefficientL2_ae Ω a (g i)] with z hz
    rw [hz]
    ring] at hweak
  rw [show (∫ z in Ω, (h1SmoothCoefficientL2 Ω a (g i) + h1SmoothCoefficientDerivativeL2 Ω a i u : L2 Ω) z * φ z) = (∫ z in Ω, h1SmoothCoefficientL2 Ω a (g i) z * φ z) + ∫ z in Ω, h1SmoothCoefficientDerivativeL2 Ω a i u z * φ z by
    calc
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (h1SmoothCoefficientL2 Ω a (g i))
          (h1SmoothCoefficientDerivativeL2 Ω a i u)] with z hz
        rw [hz]
        simp [add_mul]
      _ = _ := integral_add ((Lp.memLp (h1SmoothCoefficientL2 Ω a (g i))).integrable_mul hφ.memLp) hid]
  linear_combination hweak

theorem smooth_coefficient_h1_ext  
    (hv : h1Value Ω u = h1Value Ω v)
    (hg : ∀ i : Fin 2, h1Gradient Ω i u = h1Gradient Ω i v) : u = v := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

def smoothCoefficientH1Vector Ω (a : SmoothH1Coefficient)
    (u : NeumannH1 Ω) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u))

theorem smoothCoefficientH1Vector_value Ω a
    u :
    h1Value Ω (smoothCoefficientH1Vector Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  h1Value_h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u))

theorem smoothCoefficientH1Vector_gradient Ω a
    u i :
    h1Gradient Ω i (smoothCoefficientH1Vector Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  h1Gradient_h1Vector (isWeakGradient_h1SmoothCoefficientL2 a (h1Value_weakGradient Ω u)) i

def smoothCoefficientH1Lin (Ω : Set ℂ) (a : SmoothH1Coefficient) :
    NeumannH1 Ω →ₗ[ℂ] NeumannH1 Ω where
  toFun := smoothCoefficientH1Vector Ω a
  map_add' u v := by
    apply smooth_coefficient_h1_ext
    · simp [smoothCoefficientH1Vector_value]
    · intro i
      simp [smoothCoefficientH1Vector_gradient]
      abel
  map_smul' c u := by
    apply smooth_coefficient_h1_ext
    · simp [smoothCoefficientH1Vector_value]
    · intro i
      simp [smoothCoefficientH1Vector_gradient]

private theorem smoothCoefficientH1Lin_value Ω a
    u :
    h1Value Ω (smoothCoefficientH1Lin Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  smoothCoefficientH1Vector_value Ω a u

private theorem smoothCoefficientH1Lin_gradient Ω a
    u i :
    h1Gradient Ω i (smoothCoefficientH1Lin Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  smoothCoefficientH1Vector_gradient Ω a u i

private theorem smooth_real_component_bounds {r a b c : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : r ^ 2 = a ^ 2 + (b ^ 2 + c ^ 2)) :
    a ≤ r ∧ b ≤ r ∧ c ≤ r := by
  constructor
  · apply (sq_le_sq₀ ha hr).mp
    nlinarith [sq_nonneg b, sq_nonneg c]
  constructor
  · apply (sq_le_sq₀ hb hr).mp
    nlinarith [sq_nonneg a, sq_nonneg c]
  · apply (sq_le_sq₀ hc hr).mp
    nlinarith [sq_nonneg a, sq_nonneg b]

private theorem smooth_real_three_component_norm_le 
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hs : r ^ 2 = a ^ 2 + (b ^ 2 + c ^ 2))
    (hva : a ≤ A) (hvb : b ≤ A) (hvc : c ≤ A) :
    r ≤ Real.sqrt 3 * A := by
  apply (sq_le_sq₀ hr (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith

private theorem smooth_coefficient_norm_le_of_components 
    u  (hA : 0 ≤ A)
    (hv : ‖h1Value Ω u‖ ≤ A) (hg : ∀ i : Fin 2, ‖h1Gradient Ω i u‖ ≤ A) :
    ‖u‖ ≤ Real.sqrt 3 * A := by
  have hs := h1_norm_sq Ω u
  rw [Fin.sum_univ_two] at hs
  exact smooth_real_three_component_norm_le (norm_nonneg u) (norm_nonneg (h1Value Ω u))
    (norm_nonneg (h1Gradient Ω 0 u)) (norm_nonneg (h1Gradient Ω 1 u)) hA hs hv (hg 0) (hg 1)

theorem smoothCoefficientH1Lin_norm_le Ω a
    u :
    ‖smoothCoefficientH1Lin Ω a u‖ ≤ 2 * Real.sqrt 3 * a.bound * ‖u‖ := by
  have hc : ‖h1Value Ω u‖ ≤ ‖u‖ ∧ ∀ i : Fin 2, ‖h1Gradient Ω i u‖ ≤ ‖u‖ := by
    have hs := h1_norm_sq Ω u
    rw [Fin.sum_univ_two] at hs
    have hc := smooth_real_component_bounds (norm_nonneg u) (norm_nonneg (h1Value Ω u))
      (norm_nonneg (h1Gradient Ω 0 u)) (norm_nonneg (h1Gradient Ω 1 u)) hs
    refine ⟨hc.1, ?_⟩
    intro i
    fin_cases i
    · exact hc.2.1
    · exact hc.2.2
  have hg i :
      ‖h1Gradient Ω i (smoothCoefficientH1Lin Ω a u)‖ ≤ 2 * a.bound * ‖u‖ := by
    rw [smoothCoefficientH1Lin_gradient]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ :=
        add_le_add (norm_h1SmoothCoefficientL2_apply_le Ω a _)
          (norm_lpBoundedMulLin_le (fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i)) (coefficient_derivative_continuous a i).aestronglyMeasurable (Eventually.of_forall (a.derivative_bound i)) _)
      _ ≤ _ :=
        add_le_add (mul_le_mul_of_nonneg_left (hc.2 i) a.bound_nonneg)
          (mul_le_mul_of_nonneg_left hc.1 a.bound_nonneg)
      _ = _ := by ring
  convert (smooth_coefficient_norm_le_of_components (smoothCoefficientH1Lin Ω a u) (mul_nonneg (mul_nonneg (by norm_num) a.bound_nonneg) (norm_nonneg u)) (by
    rw [smoothCoefficientH1Lin_value]
    exact (norm_h1SmoothCoefficientL2_apply_le Ω a _).trans
      ((mul_le_mul_of_nonneg_left hc.1 a.bound_nonneg).trans
        (by nlinarith [norm_nonneg u, a.bound_nonneg]))) hg) using 1; ring

/-- Actual bounded multiplication in H¹, with no regularity premise on the input. -/
def neumannH1SmoothMultiplier Ω (a : SmoothH1Coefficient) :
    NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  (smoothCoefficientH1Lin Ω a).mkContinuous (2 * Real.sqrt 3 * a.bound)
    (smoothCoefficientH1Lin_norm_le Ω a)

theorem h1Value_neumannH1SmoothMultiplier Ω a
    u :
    h1Value Ω (neumannH1SmoothMultiplier Ω a u) = h1SmoothCoefficientL2 Ω a (h1Value Ω u) :=
  smoothCoefficientH1Vector_value Ω a u

theorem h1Gradient_neumannH1SmoothMultiplier Ω a
    u i :
    h1Gradient Ω i (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
        h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  smoothCoefficientH1Vector_gradient Ω a u i

def smoothCoefficientTestProduct (a : SmoothH1Coefficient) (f : smoothTraceTests) :
    smoothTraceTests :=
  ⟨fun z => a z * f z, coefficient_test_mul a f.property⟩


/-- The completed product agrees with the actual compact smooth product. -/
def h1SmoothBoundaryMultiplier  
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ)))

theorem h1SmoothBoundaryMultiplier_ae  
    (hγ : IsBoundaryParam Ω γ) a g :
    (h1SmoothBoundaryMultiplier hγ a g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] fun θ => a (γ θ) * g θ :=
  lpBoundedMultiplier_ae (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ))) g

/-- The physical trace product rule for every actual H¹ vector follows from
the dense smooth restrictions and the two already bounded product operators. -/
theorem h1BoundaryTrace_neumannH1SmoothMultiplier {Ω : Set ℂ}
    hb hL 
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) u :
    h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ u) := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a v) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ v)) u ?_ ?_
  · exact isClosed_eq ((h1BoundaryTrace hb hL hγ).continuous.comp
      (neumannH1SmoothMultiplier Ω a).continuous)
      ((h1SmoothBoundaryMultiplier hγ a).continuous.comp (h1BoundaryTrace hb hL hγ).continuous)
  · intro f
    change h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f)) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f))
    have h_inl a f : neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f) = smoothTraceH1 Ω (smoothCoefficientTestProduct a f) := by
      apply h1Value_injective hL.1.1
      simp [h1Value_neumannH1SmoothMultiplier]
      apply Lp.ext
      filter_upwards [h1SmoothCoefficientL2_ae Ω a (h1Value Ω (smoothTraceH1 Ω f)),
        (smoothTraceTests_memLp Ω f).coeFn_toLp,
        (smoothTraceTests_memLp Ω (smoothCoefficientTestProduct a f)).coeFn_toLp]
        with z hm hf hp
      simp at hm
      rw [hm, hf, hp]
      rfl
    rw [h_inl]
    apply Lp.ext
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ (smoothCoefficientTestProduct a f),
      h1SmoothBoundaryMultiplier_ae hγ a (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f)),
      h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hp hm hf
    rw [hp, hm, hf]
    rfl

end PolyaNeumann

end
