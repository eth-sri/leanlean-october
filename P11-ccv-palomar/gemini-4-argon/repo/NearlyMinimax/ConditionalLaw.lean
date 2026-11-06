module

public import NearlyMinimax.Model

@[expose] public section

/-! Actual finite-product conditional sampling laws for the original model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace NearlyMinimax


variable {ι α β : Type*}
/-- The indexed product of Markov kernels, evaluated coordinate by coordinate. -/
def finiteProductKernel  [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    Kernel (ι → α) (ι → β) where
  toFun x := Measure.pi (fun i => κ i (x i))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    induction s, hs using MeasurableSpace.induction_on_inter
        generateFrom_pi.symm isPiSystem_pi with
    | empty => simp only [measure_empty]; exact measurable_const
    | basic s hs =>
        obtain ⟨t, ht, rfl⟩ := hs
        simp_rw [Measure.pi_pi]
        exact Finset.measurable_prod Finset.univ
          (fun i _ => (Kernel.measurable_coe (κ i) (ht i (mem_univ i))).comp
            (measurable_pi_apply i))
    | compl s hs ih =>
        simp_rw [measure_compl hs (measure_ne_top _ _), measure_univ]
        exact measurable_const.sub ih
    | iUnion f hd hf ih =>
        simp_rw [measure_iUnion hd hf]
        exact Measurable.tsum ih
    | x_4 => infer_instance

instance finiteProductKernel_markov {ι α β : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (finiteProductKernel κ) :=
  ⟨fun x => inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun i => κ i (x i))))⟩

theorem finiteProductKernel_apply  [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] (x : ι → α) :
    finiteProductKernel κ x = Measure.pi (fun i => κ i (x i)) := rfl

/-- Reassemble separate design and error vectors into coordinate pairs. -/
def pairVectors  (z : (ι → α) × (ι → β)) : ι → α × β :=
  fun i => (z.1 i, z.2 i)

theorem pairVectors_measurable 
    [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (pairVectors (ι := ι) (α := α) (β := β)) :=
  Measurable.of_eval (fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

/-- The product of one-coordinate joint laws is the design-vector law followed
by the independent coordinate conditional laws. No conditional independence is assumed. -/
theorem pi_compProd_eq_map_pairVectors  [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (μ ) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ι → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    Measure.pi (fun i => (μ i).compProd (κ i)) =
      ((Measure.pi μ).compProd (finiteProductKernel κ)).map pairVectors := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply pairVectors_measurable (MeasurableSet.univ_pi hs),
    Measure.compProd_apply (pairVectors_measurable (MeasurableSet.univ_pi hs))]
  have hsection (x : ι → α) :
      Prod.mk x ⁻¹' (pairVectors ⁻¹' Set.univ.pi s) =
        Set.univ.pi (fun i => Prod.mk (x i) ⁻¹' s i) := by
    ext u
    simp [pairVectors, Set.mem_pi]
  simp_rw [hsection, finiteProductKernel_apply, Measure.pi_pi]
  have h_lintegral_coordinate_product (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) : (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ a, f i a ∂μ i := by
    have h := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
      (fun (i : ι) (x : ι → α) => f i (x i))
      (iIndepFun_pi (μ := μ) (X := f) (fun i => (hf i).aemeasurable))
      (fun i => (hf i).comp (measurable_pi_apply i))
    rw [h]
    apply Finset.prod_congr rfl
    intro i _
    exact lintegral_map' (hf i).aemeasurable (measurable_pi_apply i).aemeasurable |>.symm.trans
      (by rw [(measurePreserving_eval μ i).map_eq])
  rw [h_lintegral_coordinate_product (fun i a => κ i a (Prod.mk a ⁻¹' s i)) (fun i => Kernel.measurable_kernel_prodMk_left (hs i))]
  simp_rw [Measure.compProd_apply (hs _)]

def designVectorLaw  (θ : RegressionParameter d) (n ) :
    Measure (Fin n → Covariate d) := Measure.pi (fun _ => designLaw θ)

def conditionalErrorLaw  (θ : RegressionParameter d)
    (x : Fin n → Covariate d) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => θ.errors (x i))

def conditionalErrorKernel  (θ : RegressionParameter d) (n : ℕ) :
    Kernel (Fin n → Covariate d) (Fin n → ℝ) :=
  finiteProductKernel (fun _ => θ.errors)

instance conditionalErrorKernel_markov {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    IsMarkovKernel (conditionalErrorKernel θ n) := by
  unfold conditionalErrorKernel
  infer_instance

instance conditionalErrorLaw_probability {d n : ℕ} (θ : RegressionParameter d)
    (x : Fin n → Covariate d) : IsProbabilityMeasure (conditionalErrorLaw θ x) := by
  unfold conditionalErrorLaw
  infer_instance

/-- Reconstruct observations from the design and error vectors. -/
def samplesFromDesignErrors  (θ : RegressionParameter d)
    (z : (Fin n → Covariate d) × (Fin n → ℝ)) : Fin n → Observation d :=
  fun i => (z.1 i, θ.regression (z.1 i) + z.2 i)

theorem samplesFromDesignErrors_measurable  (θ : RegressionParameter d)
    (hf : Measurable θ.regression) : Measurable (samplesFromDesignErrors (n := n) θ) :=
  Measurable.of_eval (fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((hf.comp ((measurable_pi_apply i).comp measurable_fst)).add
        ((measurable_pi_apply i).comp measurable_snd)))

/-- An equality of the actual original sample measure, not an assumed conditional law. -/
theorem sampleLaw_eq_conditional_map  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (n ) :
    sampleLaw θ n =
      ((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)).map
        (samplesFromDesignErrors θ) := by
  let := designLaw_isProbability C θ hθ
  have hm : Measurable (fun z : Covariate d × ℝ =>
      (z.1, θ.regression z.1 + z.2)) :=
    measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)
  have hp := pi_compProd_eq_map_pairVectors (ι := Fin n)
    (fun _ => designLaw θ) (fun _ => θ.errors)
  have hv : Measurable (fun z : Fin n → Covariate d × ℝ =>
      fun i => ((z i).1, θ.regression (z i).1 + (z i).2)) :=
    Measurable.of_eval (fun i => hm.comp (measurable_pi_apply i))
  unfold sampleLaw observationLaw
  rw [← Measure.pi_map_pi (fun _ => hm.aemeasurable), hp, Measure.map_map hv pairVectors_measurable]
  rfl

/-- Bochner Fubini for every integrable vector-valued observation function. -/
theorem sampleLaw_integral_conditioning  
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C θ) (hθ : Admissible C θ)
    (g : (Fin n → Observation d) → E) (hg : Integrable g (sampleLaw θ n)) :
    (∫ z, g z ∂sampleLaw θ n) =
      ∫ x, ∫ u, g (samplesFromDesignErrors θ (x, u))
        ∂conditionalErrorLaw θ x ∂designVectorLaw θ n := by
  let := designLaw_isProbability C θ hθ
  let : IsProbabilityMeasure (designVectorLaw θ n) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ => designLaw θ)))
  have hm := samplesFromDesignErrors_measurable (n := n) θ hθ.2.1
  have hmap : Integrable g
      (((designVectorLaw θ n).compProd (conditionalErrorKernel θ n)).map
        (samplesFromDesignErrors θ)) := by
    rwa [← sampleLaw_eq_conditional_map C θ hθ]
  rw [sampleLaw_eq_conditional_map C θ hθ,
    integral_map hm.aemeasurable hmap.aestronglyMeasurable,
    Measure.integral_compProd (by simpa only [Function.comp_def] using hmap.comp_measurable hm)]
  rfl

theorem conditionalErrorLaw_integral_coordinate  (θ : RegressionParameter d)
    (x : Fin n → Covariate d) (i : Fin n) (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ u, g (u i) ∂conditionalErrorLaw θ x) = ∫ a, g a ∂θ.errors (x i) := by
  have h := integral_map (μ := Measure.pi (fun j => θ.errors (x j)))
    (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable
  rw [(measurePreserving_eval (fun j => θ.errors (x j)) i).map_eq] at h
  exact h.symm

/-- The design law is supported on the actual cube, even before admissibility. -/
theorem designLaw_cube_ae  (θ : RegressionParameter d) :
    ∀ᵐ x ∂designLaw θ, x ∈ unitCube d := by
  have heq : unitCube d = Set.univ.pi (fun _ => Set.Icc 0 1) := by
    ext x
    simp only [unitCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      true_imp_iff, Set.mem_Icc]
  exact (ae_restrict_mem (by rw [heq]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc))).filter_mono (withDensity_absolutelyContinuous (cubeVolume d)
    (fun x => ENNReal.ofReal (θ.density x))).ae_le

end NearlyMinimax
