module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

public section

/-! Hilbert-space localization for unbounded square-integrable kernel fields. -/
𝚯
𝚻
namespace NearlyMinimax.LocalizationL2


variable {W E : Type*} [MeasurableSpace W]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : Measure W} [IsFiniteMeasure M]

𝗇 𝔖 ∫ w, f w ^ 2 ∂M
𝗇 𝔜 a / b
𝗃 𝔥 ἀ ^ 2
𝗇 𝔄 𝔖 - 2 * 𝔜 * a + b * 𝔥 𝔜
𝗇 𝔈 𝔜
𝗇 𝔓 𝔖
𝗇 𝔗 2 * 𝔈
𝗇 𝔇 ∫ w, f w ∂M
𝗇 𝔛 (f w - 𝔈) ^ 2
𝗃 𝔣 ∫ w, ἀ ∂M
𝗃 𝔤 fun w => ἀ
/-- The finite-measure Cauchy bound, proved by integrating a nonnegative square. -/
theorem integral_sq_le_mass_mul_integral_sq (hf : MemLp f 2 M) :
    𝔥 𝔇 ≤ M.real Set.univ * 𝔓 := by
  let a := 𝔇
  let b := M.real Set.univ
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  by_cases hb0 : b = 0
  · have hM0 : M = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact (measureReal_eq_zero_iff).mp hb0
    simp_all
  · have hi := hf.integrable $ by norm_num
    have hi2 := hf.integrable_sq
    have heq : 𝔣 𝔛 =
        𝔄 := by
      have hfalg : 𝔤 𝔛 =
           fun w => f w ^ 2 - 𝔗 * f w + 𝔥 𝔈 := by
        funext w
        ring
      rw [hfalg]
      have ha := integral_add (hi2.sub $ hi.const_mul 𝔗 )
        $ integrable_const 𝔥 𝔈
      have hs := integral_sub hi2 $ hi.const_mul 𝔗
      simp only [Pi.sub_apply] at ha hs
      rw [ha, hs, integral_const_mul, integral_const]
      rfl
    have hnon : 0 ≤ 𝔄 := by
      rw [← heq]
      positivity
    have hid : b * 𝔄 =
        b * 𝔓 - 𝔥 a := by
      field_simp
      ring
    nlinarith

𝗇 𝔎 W → E
/-- Integration of a Hilbert-valued `L²` field is bounded by its mass and energy. -/
theorem norm_integral_sq_le_mass_mul_integral_norm_sq {f : 𝔎} (hf : MemLp f 2 M) :
    ‖𝔇‖ ^ 2 ≤ M.real Set.univ * ∫ w, ‖f w‖ ^ 2 ∂M := by
  have hsq :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm (f := f) (μ := M)) 2
  exact hsq.trans $ integral_sq_le_mass_mul_integral_sq hf.norm

𝗇 𝔉 ν w ^ 2
𝗇 𝔐 b w = c
𝗇 𝔟 W → Fin q
𝗇 𝔠 MemLp ν 2 M
𝗇 𝔢 b w ≠ b v
section Hilbert

𝗇 𝔊 ∫ w, f w ∂N
theorem inner_integral_right (x : E)
    (hf : Integrable f N) :
    ⟪x, 𝔊 ⟫ = ∫ w, ⟪x, f w⟫ ∂N :=
  ((innerSL ℝ x).integral_comp_comm hf).symm

𝗇 𝔞 ⟪g v, f w⟫
/-- Almost-everywhere cross-block orthogonality is sufficient. -/
theorem integral_inner_eq_zero_of_ae {N P : Measure W} {f g : 𝔎}
    (hf : Integrable f N) (hg : Integrable g P)
    (horth : ∀ᵐ v ∂P, ∀ᵐ w ∂N, ⟪f w, g v⟫ = 0) :
    ⟪ 𝔊, ∫ v, g v ∂P⟫ = 0 := by
  rw [inner_integral_right _ hg]
  apply integral_eq_zero_of_ae
  filter_upwards [horth] with v hv
  calc
    ⟪ 𝔊, g v⟫ = ⟪g v, 𝔊 ⟫ := real_inner_comm ..
    _ = ∫ w, 𝔞 ∂N := inner_integral_right _ hf
    _ = 0 := integral_eq_zero_of_ae $ hv.mono fun w hw => by
      change 𝔞 = 0
      rw [real_inner_comm, hw]

𝗇 𝔘 ∫ w, F c w ∂N c
/-- The localization inequality for finitely many orthogonal blocks. The
block measures may be restrictions of one finite parameter measure. -/
theorem finite_block_integral_bound {q : ℕ}
    (N : Fin q → Measure W) [∀ c, IsFiniteMeasure $ N c ]
    (F : Fin q → 𝔎) (hF : ∀ c, MemLp (F c) 2 $ N c )
    (horth : ∀ c d, c ≠ d → ∀ᵐ v ∂N d, ∀ᵐ w ∂N c, ⟪F c w, F d v⟫ = 0)
    L (hL : ∀ c, (N c).real Set.univ ≤ L) :
    ‖∑ c : Fin q, 𝔘‖ ^ 2 ≤
      L * ∑ c : Fin q, ∫ w, ‖F c w‖ ^ 2 ∂N c := by
  let I := fun c => 𝔘
  have hIorth := fun c d hcd =>
    integral_inner_eq_zero_of_ae ((hF c).integrable 𝖠₄ )
      ((hF d).integrable 𝖠₄ ) $ horth c d hcd
  have hsum : ‖∑ c : Fin q, I c‖ ^ 2 = ∑ c : Fin q, ‖I c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro c _
    rw [inner_sum, Finset.sum_eq_single c]
    all_goals bound
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  exact (norm_integral_sq_le_mass_mul_integral_norm_sq $ hF c ).trans
    $ mul_le_mul_of_nonneg_right (hL c) $ integral_nonneg fun _ => sq_nonneg _

𝗇 𝔏 b v = c
/-- Integrating over a measurable finite partition is summing the block integrals. -/
theorem integral_eq_sum_fibers {q } b (hb : Measurable b)
    {f : 𝔎} (hf : Integrable f M) :
    𝔇 = ∑ c : Fin q, ∫ w in {v | 𝔏}, f w ∂M := by
  classical
  have hB : ∀ c, MeasurableSet {v | 𝔏} := fun c => measurableSet_eq_fun hb measurable_const
  calc
    _ = ∫ w, ∑ c : Fin q, ({v | 𝔏}).indicator f w ∂M := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        change f w = ∑ c : Fin q, ({v | 𝔏}).indicator f w
        rw [Finset.sum_eq_single $ b w ]
        all_goals aesop
    _ = ∑ c : Fin q, ∫ w, ({v | 𝔏}).indicator f w ∂M :=
      integral_finsetSum _ fun c _ => (fun c => hf.indicator $ hB c ) c
    𝘿 := Finset.sum_congr rfl fun c _ => integral_indicator $ hB c

𝗇 𝔍 ∀ w v, 𝔢 → ⟪K w, K v⟫ = 0
𝗇 𝔒 ‖K w‖
/-- A finite partition with mutually orthogonal kernel blocks gains the largest
block mass instead of the total mass in the integral Cauchy bound. -/
theorem partition_localization_bound {q } (b : 𝔟) (hb : Measurable b)
    (K : 𝔎) (hK : MemLp K 2 M)
    (horth : 𝔍)
    L (hL : ∀ c, M.real {w | 𝔐} ≤ L) :
    ‖∫ w, K w ∂M‖ ^ 2 ≤ L * ∫ w, 𝔥 𝔒 ∂M := by
  have hB : ∀ c, MeasurableSet {w | 𝔐} := fun c => measurableSet_eq_fun hb measurable_const
  have hnormint := hK.norm.integrable_sq
  have hsum := finite_block_integral_bound (fun c => M.restrict {w | 𝔐})
    (fun _ => K) (fun c => hK.restrict _) fun c d hcd => by
      filter_upwards [ae_restrict_mem $ hB d ] with v hv
      filter_upwards [ae_restrict_mem $ hB c ] with w hw
      simp_all
    L fun c => 𝖤₄
  rw [← integral_eq_sum_fibers b hb $ hK.integrable 𝖠₄ ] at hsum
  have hscalar := (integral_eq_sum_fibers b hb hnormint).symm
  simp_all

𝗇 𝔔 ν w • K w
𝗇 𝔙 ∀ᵐ w ∂M, 𝔒 ≤ C
/-- A uniformly `L²` bounded kernel field times an `L²` weight is an `L²`
Bochner field. Here the Hilbert norm is the kernel's observation `L²` norm. -/
theorem weighted_field_memLp_two (ν : W → ℝ) (hν : 𝔠)
    (K : 𝔎) (hK : AEStronglyMeasurable K M)
    C (hC : 0 ≤ C) (hbound : 𝔙) :
    MemLp 𝔤 𝔔 2 M := by
  apply (hν.const_mul C).of_le $ hν.aestronglyMeasurable.smul hK
  filter_upwards [hbound] with w hw
  calc
    ‖𝔔‖ = ‖ν w‖ * 𝔒 := norm_smul ..
    _ ≤ ‖ν w‖ * C := mul_le_mul_of_nonneg_left hw $ norm_nonneg _
    _ = ‖C * ν w‖ := by rw [norm_mul, Real.norm_of_nonneg hC]; ring

/-- The weighted localization estimate of original U6, with actual Bochner
integration and unbounded observation kernels represented in a Hilbert space. -/
theorem weighted_partition_localization_bound
    (b : 𝔟) (hb : Measurable b)
    ν (hν : 𝔠)
    (K : 𝔎) (hK : AEStronglyMeasurable K M)
    C (hC : 0 ≤ C) (hbound : 𝔙)
    (horth : 𝔍)
    L (hL : ∀ c, M.real {w | 𝔐} ≤ L) :
    ‖𝔣 𝔔‖ ^ 2 ≤ L * ∫ w, 𝔉 * 𝔥 𝔒 ∂M := by
  have hweightedorth : ∀ w v, 𝔢 → ⟪𝔔, ν v • K v⟫ = 0 := by
    intro w v hwv
    rw [real_inner_smul_left, real_inner_smul_right, horth w v hwv]
    ring
  have h := partition_localization_bound b hb _ (weighted_field_memLp_two ν hν K hK C hC hbound) hweightedorth L hL
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using h

end Hilbert

section ObservationKernels
𝛒

/-- The genuine Hilbert `L²` norm is the integral second moment. -/
theorem toLp_norm_sq_eq_integral_sq (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp_all

/-- Disjoint raw observation supports imply orthogonality of the actual `L²`
kernel elements; the supports need only be disjoint almost everywhere. -/
theorem toLp_inner_eq_zero_of_disjoint {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hdisjoint : ∀ᵐ ω ∂μ, f ω * g ω = 0) :
    ⟪hf.toLp f, hg.toLp g⟫ = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, hdisjoint] with ω hfω hgω hω
  aesop

end ObservationKernels
𝗇 𝔅 ‖K r w‖ ^ 2
𝗃 𝔦 ∑ r : Fin D, δ r * ἀ
𝗇 𝔑 ∫ w, 𝔉 * 𝔦 𝔅 ∂M
𝗇 𝔚 𝔉 * 𝔅
𝗇 𝔡 K r w
/-- The block estimate summed over kernel orders, allowing each order to live
in its own observation Hilbert space. This is U6's second localized inequality. -/
theorem weighted_kernel_series_localization_bound {D q : ℕ}
    {H : Fin D → Type*} [∀ r, NormedAddCommGroup $ H r ]
    [∀ r, InnerProductSpace ℝ $ H r ] [∀ r, CompleteSpace $ H r ]
    (b : 𝔟) (hb : Measurable b)
    ν (hν : 𝔠)
    (K : (r : Fin D) → W → H r)
    (hK : ∀ r, AEStronglyMeasurable (K r) M)
    (C : Fin D → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M, ‖𝔡‖ ≤ C r)
    (horth : ∀ r w v, 𝔢 → inner ℝ 𝔡 (K r v) = 0)
    (δ : Fin D → ℝ) (hδ : ∀ r, 0 ≤ δ r)
    L (hL : ∀ c, M.real {w | 𝔐} ≤ L) :
     ∑ r : Fin D, δ r * ‖∫ w, ν w • 𝔡 ∂M‖ ^ 2 ≤
      L * 𝔑 := by
  have hi : ∀ r, Integrable 𝔤 𝔚 M := by
    intro r
    have hlp := weighted_field_memLp_two ν hν (K r) (hK r) (C r) (hC r) $ hbound r
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hlp.norm.integrable_sq
  have heq : 𝔑 =
      ∑ r : Fin D, δ r * 𝔣 𝔚 := by
    simp_rw [Finset.mul_sum]
    have hfalg : (fun w => ∑ r : Fin D, 𝔉 * (δ r * 𝔅)) =
         fun w => 𝔦 𝔚 := by
      grind
    rw [hfalg, integral_finsetSum _ fun r _ => (hi r).const_mul $ δ r ]
    simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ r : Fin D, δ r * (L * 𝔣 𝔚) := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (weighted_partition_localization_bound b hb ν hν (K r) (hK r)
          (C r) (hC r) (hbound r) (horth r) L hL) $ hδ r
    𝘿 := by rw [heq, Finset.mul_sum]; grind
