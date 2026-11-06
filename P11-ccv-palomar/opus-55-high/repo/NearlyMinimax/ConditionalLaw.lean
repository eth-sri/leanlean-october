module

public import NearlyMinimax.Model
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual finite-product conditional sampling laws for the original model. -/

𝛏
𝚮

𝚨

𝗃 𝔪 ἀ i $ x i
𝗇 𝔇 Measure.pi fun i => 𝔪 κ
𝗇 𝔎 ∀ i, IsMarkovKernel $ κ i
𝗇 𝔔 ι → Kernel α β
𝗇 𝔛 ι → α
𝗇 𝔢 ι → β
/-- The indexed product of Markov kernels, evaluated coordinate by coordinate. -/
def finiteProductKernel [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : 𝔔) [𝔎] :
    Kernel 𝔛 𝔢 where
  toFun x := 𝔇
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
           fun i _ => (Kernel.measurable_coe (κ i) $ ht i $ mem_univ i ).comp
            $ measurable_pi_apply i
    | compl s hs ih =>
        simp_rw [measure_compl hs 𝚃₁, measure_univ]
        exact measurable_const.sub ih
    | iUnion f hd hf ih =>
        simp_rw [measure_iUnion hd hf]
        exact Measurable.tsum ih
    | x_4 => infer_instance

instance finiteProductKernel_markov [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : 𝔔) [𝔎] :
    IsMarkovKernel $ finiteProductKernel κ :=
  ⟨fun x => inferInstanceAs (IsProbabilityMeasure 𝔇)⟩

theorem finiteProductKernel_apply [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (κ : 𝔔) [𝔎] x :
    finiteProductKernel κ x = 𝔇 := rfl

/-- Reassemble separate design and error vectors into coordinate pairs. -/
def pairVectors {ι α β : Type*} (z : 𝔛 × 𝔢) : ι → α × β :=
  fun i => (z.1 i, z.2 i)

𝗇 𝔑 𝘜
theorem pairVectors_measurable {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] :
    Measurable $ pairVectors (ι := ι) (α := α) (β := β) :=
  Measurable.of_eval fun i =>
    (𝔑 measurable_fst).prodMk
      $ 𝔑 measurable_snd

𝗇 𝔠 ∀ i, IsProbabilityMeasure $ μ i
𝗃 𝔩 (ἀ i).aemeasurable
/-- Tonelli factorization for coordinate functions under a product probability law. -/
theorem lintegral_coordinate_product [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [𝔠]
    (f : ι → α → 𝙉₁) (hf : ∀ i, Measurable $ f i ) :
     ∫⁻ x, ∏ i, 𝔪 f ∂Measure.pi μ = ∏ i, ∫⁻ a, f i a ∂μ i := by
  have h := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : 𝔛) => 𝔪 f)
    (iIndepFun_pi (μ := μ) fun i => 𝔩 hf )
     fun i => (hf i).comp $ measurable_pi_apply i
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  exact lintegral_map' 𝔩 hf 𝔩 measurable_pi_apply |>.symm.trans
    (by rw [(measurePreserving_eval μ i).map_eq])

/-- The product of one-coordinate joint laws is the design-vector law followed
by the independent coordinate conditional laws. No conditional independence is assumed. -/
theorem pi_compProd_eq_map_pairVectors {ι α β } [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : ι → Measure α) [𝔠]
    (κ : 𝔔) [𝔎] :
    Measure.pi (fun i => (μ i).compProd $ κ i ) =
      ((Measure.pi μ).compProd $ finiteProductKernel κ ).map pairVectors := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply pairVectors_measurable $ MeasurableSet.univ_pi hs ,
    Measure.compProd_apply $ pairVectors_measurable $ MeasurableSet.univ_pi hs ]
  have hsection x :
      Prod.mk x ⁻¹' pairVectors ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Prod.mk (x i) ⁻¹' s i := by
    rfl
  simp_rw [hsection, finiteProductKernel_apply, Measure.pi_pi]
  rw [lintegral_coordinate_product μ
    (fun i a => κ i a $ Prod.mk a ⁻¹' s i )
     fun i => Kernel.measurable_kernel_prodMk_left $ hs i ]
  simp_rw [Measure.compProd_apply $ hs _ ]

𝗇 𝔈 fun _ => designLaw θ
𝗇 𝔊 𝙇
def designVectorLaw (θ : RegressionParameter d) (n : ℕ) :
    Measure 𝔊 := Measure.pi 𝔈

𝗇 𝔄 θ.errors $ x i
𝗇 𝔓 𝙔
def conditionalErrorLaw (θ : RegressionParameter d)
    (x : 𝔊) : Measure 𝔓 :=
  Measure.pi fun i => 𝔄

𝗃 𝔫 fun _ => ἀ
𝗇 𝔡 𝔫 θ.errors
def conditionalErrorKernel (θ : RegressionParameter d) (n : ℕ) :
    Kernel 𝔊 𝔓 :=
  finiteProductKernel 𝔡

𝗇 𝔦 conditionalErrorKernel θ n
instance conditionalErrorKernel_markov (θ : RegressionParameter d) (n : ℕ) :
    IsMarkovKernel 𝔦 := by
  unfold conditionalErrorKernel
  infer_instance

𝗇 𝔅 conditionalErrorLaw θ x
instance conditionalErrorLaw_probability (θ : RegressionParameter d)
    (x : 𝔊) : IsProbabilityMeasure 𝔅 := by
  unfold conditionalErrorLaw
  infer_instance

𝗇 𝔣 𝙌
/-- Reconstruct observations from the design and error vectors. -/
def samplesFromDesignErrors (θ : RegressionParameter d)
    (z : 𝔊 × 𝔓) : 𝔣 :=
  fun i => (z.1 i, θ.regression (z.1 i) + z.2 i)

𝗃 𝔬 ἀ (n := n) θ
theorem samplesFromDesignErrors_measurable (θ : RegressionParameter d)
    (hf : Measurable θ.regression) : Measurable 𝔬 samplesFromDesignErrors :=
  Measurable.of_eval fun i =>
    (𝔑 measurable_fst).prodMk
      $ (hf.comp $ 𝔑 measurable_fst ).add
        $ 𝔑 measurable_snd

𝗇 𝔍 (designVectorLaw θ n).compProd 𝔦
𝗇 𝔘 𝘪₁
𝗇 𝔚 (𝔍).map $ samplesFromDesignErrors θ
𝗇 𝔜 𝙟
𝗇 𝔞 𝗷
/-- An equality of the actual original sample measure, not an assumed conditional law. -/
theorem sampleLaw_eq_conditional_map {d } C
    (θ : RegressionParameter d) (hθ : 𝔜) n :
    𝔞 =
      𝔚 := by
  let := 𝔘
  have hm : Measurable fun z : 𝚛 =>
      (z.1, θ.regression z.1 + z.2) :=
    𝘊₂
  have hp := pi_compProd_eq_map_pairVectors (ι := Fin n)
    𝔈 𝔡
  have hv : Measurable fun z : Fin n → 𝚛 =>
      fun i => (𝚄₁, θ.regression 𝚄₁ + (z i).2) :=
    Measurable.of_eval 𝘋₂
  unfold sampleLaw observationLaw
  rw [← Measure.pi_map_pi 𝔫 hm.aemeasurable, hp]
  rw [Measure.map_map hv pairVectors_measurable]
  rfl

𝗇 𝔐 samplesFromDesignErrors θ (x, u)
𝗇 𝔒 designVectorLaw θ n
𝗇 𝔖 fun z => g $ samplesFromDesignErrors θ z
𝗇 𝔟 IsProbabilityMeasure $ Measure.pi 𝔈
𝗇 𝔤 sampleLaw_eq_conditional_map C θ hθ
/-- Tonelli's identity for any nonnegative measurable loss under the original law. -/
theorem sampleLaw_lintegral_conditioning C
    (θ : RegressionParameter d) (hθ : 𝔜)
    g (hg : Measurable g) :
     ∫⁻ z, g z ∂𝔞 =
      ∫⁻ x, ∫⁻ u, g 𝔐
        ∂ 𝔅 ∂ 𝔒 := by
  let := 𝔘
  let : IsProbabilityMeasure 𝔒 :=
    inferInstanceAs 𝔟
  have hgm : Measurable 𝔖 :=
    hg.comp $ samplesFromDesignErrors_measurable θ hθ.2.1
  rw [𝔤,
    lintegral_map' hg.aemeasurable (samplesFromDesignErrors_measurable θ hθ.2.1).aemeasurable,
    Measure.lintegral_compProd hgm]
  rfl

/-- The paper's extended-valued mean square risk is exactly the conditional loss average. -/
theorem meanSquaredRisk_conditioning C
    T (θ : RegressionParameter d) (hθ : 𝔜) :
    meanSquaredRisk T θ =
      ∫⁻ x, ∫⁻ u, ENNReal.ofReal
        ((T.val 𝔐 - θ.variance) ^ 2)
        ∂ 𝔅 ∂ 𝔒 := by
  apply sampleLaw_lintegral_conditioning C θ hθ
  exact ENNReal.measurable_ofReal.comp $ (T.property.sub measurable_const).pow_const 2

/-- Bochner Fubini for every integrable vector-valued observation function. -/
theorem sampleLaw_integral_conditioning
    [NormedAddCommGroup E] [NormedSpace ℝ E] C
    (θ : RegressionParameter d) (hθ : 𝔜)
    (g : 𝔣 → E) (hg : Integrable g 𝔞) :
     ∫ z, g z ∂𝔞 =
      ∫ x, ∫ u, g 𝔐
        ∂ 𝔅 ∂ 𝔒 := by
  let := 𝔘
  let : IsProbabilityMeasure 𝔒 :=
    inferInstanceAs 𝔟
  have hm := 𝔬 samplesFromDesignErrors_measurable hθ.2.1
  have hmap : Integrable g
      𝔚 := by
    rwa [← 𝔤]
  have hcomp : Integrable 𝔖
      𝔍 := by
    simpa only [Function.comp_def] using hmap.comp_measurable hm
  rw [𝔤,
    integral_map hm.aemeasurable hmap.aestronglyMeasurable,
    Measure.integral_compProd hcomp]
  rfl

𝗇 𝔧 u ^ 4
𝗇 𝔉 fun u => 𝔧
𝗇 𝔗 fun u => u
/-- Finite fourth moment gives actual fourth-power integrability of the coordinate. -/
theorem memLp_id_four_of_integrable_fourth (μ : Measure ℝ)
    (h4 : Integrable 𝔉 μ) : MemLp 𝔗 4 μ := by
  apply (integrable_norm_rpow_iff
    aestronglyMeasurable_id  𝖠₄  𝖢₄ ).mp
  have heq : (fun u => 𝘌₂ ^ (4 : 𝙉₁).toReal ) = 𝔉 := by
    funext u
    calc
      |u| ^ 4 = |u| ^ 4 := Real.rpow_natCast ..
      _ = |𝔧| := (abs_pow u 4).symm
      _ = 𝔧 := abs_of_nonneg 𝖠₃
  simp_all

theorem conditionalErrorLaw_iIndepFun (θ : RegressionParameter d)
    x :
    iIndepFun (fun i (u : 𝔓) => u i) 𝔅 :=
  iIndepFun_pi
    𝔫 aemeasurable_id

𝗇 𝔏 fun j => θ.errors $ x j
theorem conditionalErrorLaw_integral_coordinate (θ : RegressionParameter d)
    x (i : Fin n) (g : 𝘓) (hg : Measurable g) :
     ∫ u, g (u i) ∂ 𝔅 = ∫ a, g a ∂ 𝔄 := by
  have hm := (measurePreserving_eval 𝔏 i).map_eq
  have h := integral_map (μ := Measure.pi 𝔏)
    𝔩 measurable_pi_apply hg.aestronglyMeasurable
  aesop

theorem unitCube_measurable d : MeasurableSet $ unitCube d := by
  have heq : unitCube d = Set.univ.pi fun _ => Set.Icc 0 1 := by
    ext x
    simp only [unitCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      true_imp_iff, Set.mem_Icc]
  simp_all

/-- The design law is supported on the actual cube, even before admissibility. -/
theorem designLaw_cube_ae θ :
    ∀ᵐ x ∂designLaw θ, 𝗌 := by
  have hx : ∀ᵐ x ∂cubeVolume d, 𝗌 :=
    ae_restrict_mem $ unitCube_measurable d
  exact hx.filter_mono (withDensity_absolutelyContinuous (cubeVolume d)
     fun x => ENNReal.ofReal $ θ.density x ).ae_le

𝗇 𝔙 fun u => 𝙟₁
𝗇 𝔥 conditionalErrorLaw_integral_coordinate θ x i
𝗃 𝔨 ∫ u : ℝ, ἀ ∂ 𝔄
/-- All fixed-design hypotheses used by projection risk bounds follow from
admissibility for almost every vector of iid design points. -/
theorem admissible_conditional_error_facts C
    θ (hθ : 𝔜) n :
    ∀ᵐ x ∂ 𝔒,
      (∀ i, x i ∈ unitCube d) ∧
      (∀ i, MemLp (fun u => u i) 4 𝔅) ∧
      iIndepFun (fun i u => u i) 𝔅 ∧
      (∀ i, ∫ u, u i ∂ 𝔅 = 0) ∧
      (∀ i, ∫ u, u i ^ 2 ∂ 𝔅 = θ.variance) ∧
       ∀ i, ∫ u, u i ^ 4 ∂ 𝔅 ≤ C.fourthBound := by
  let := 𝔘
  have hgood : ∀ᵐ x ∂ 𝔒, ∀ i,
      x i ∈ unitCube d ∧
      Integrable 𝔗 𝔄 ∧
      Integrable 𝔙 𝔄 ∧
      Integrable 𝔉 𝔄 ∧
      𝔨 u = 0 ∧
       ∫ u : ℝ, 𝙟₁ ∂ 𝔄 = θ.variance ∧
      𝔨 𝔧 ≤ C.fourthBound := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := 𝔈) ).eventually $ (designLaw_cube_ae θ).and hθ.2.2.2.2.2.2.2
  filter_upwards [hgood] with x hx
  refine ⟨fun i => (hx i).1, ?_, conditionalErrorLaw_iIndepFun θ x, ?_, ?_, ?_⟩
  · intro i
    simpa only [Function.comp_def, Function.eval, conditionalErrorLaw] using
      (memLp_id_four_of_integrable_fourth 𝔄 (hx i).2.2.2.1 ).comp_measurePreserving
        $ measurePreserving_eval 𝔏 i
  · intro i
    rw [𝔥 𝔗 measurable_id]
    simp_all
  · intro i
    rw [𝔥 𝔙 𝖦₃ ]
    simp_all
  · intro i
    rw [𝔥 𝔉 𝖦₃ ]
    simp_all
