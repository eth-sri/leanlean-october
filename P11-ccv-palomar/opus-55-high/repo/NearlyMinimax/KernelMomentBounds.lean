module

public import NearlyMinimax.LiftL2
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Raw multilinear kernel moment bounds under genuine independent L²
observations. Increasing lift order requires no higher response moments. -/

𝚵
𝚪
namespace NearlyMinimax.KernelMomentBounds

𝚭
𝚩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

𝗇 𝔈 𝗓
𝗇 𝔑 𝗩₁
theorem pi_norm_sq_le_sum_sq (v : 𝔈) : 𝚡₁ ^ 2 ≤ ∑ a, v a ^ 2 := by
  have hn : 𝚡₁ ≤ Real.sqrt (∑ a : Fin p, v a ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg $ Real.sqrt_nonneg _ ).mpr
    intro a
    simpa only [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt $ Finset.single_le_sum (fun a _ => sq_nonneg $ v a ) $ Finset.mem_univ a
  exact (𝔑 hn 2).trans_eq $ Real.sq_sqrt $ Finset.sum_nonneg fun a _ => sq_nonneg _

𝗇 𝔇 fun a _ => (hL2 a).integrable_sq
𝗇 𝔍 ∀ a, MemLp (fun ω => X ω a) 2 μ
𝗇 𝔓 Ω → 𝔈
/-- Coordinatewise L² gives genuine vector L² and a sharp dimension-free
comparison with the sum of coordinate energies. -/
theorem vector_memLp_two (X : 𝔓) (hm : Measurable X)
    (hL2 : 𝔍) : MemLp X 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi := integrable_finsetSum Finset.univ 𝔇
  apply hi.mono' (hm.norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, 𝗤]
    exact pi_norm_sq_le_sum_sq $ X ω

theorem vector_second_le_sum_coordinates (X : 𝔓) (hm : Measurable X)
    (hL2 : 𝔍) :
     ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤ ∑ a, ∫ ω, X ω a ^ 2 ∂μ := by
  have h := integral_mono (vector_memLp_two X hm hL2).norm.integrable_sq (integrable_finsetSum Finset.univ 𝔇) fun ω => pi_norm_sq_le_sum_sq $ X ω
  rwa [integral_finsetSum _ 𝔇] at h

𝗇 𝔖 fun i => X i ω
𝗇 𝔄 ∫ ω, H 𝔖 ^ 2 ∂μ
𝗇 𝔅 ‖X i ω‖ ^ 2
𝗇 𝔉 ∀ i a, MemLp (fun ω => X i ω a) 2 μ
𝗇 𝔊 ‖H‖ ^ 2
𝗇 𝔎 𝔖
𝗇 𝔏 ∀ i, ∫ ω, 𝔅 ∂μ ≤ E
𝗇 𝔐 ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔈) ℝ
𝗇 𝔒 𝘫₁
𝗇 𝔔 ∏ i : Fin k, 𝔅
/-- Independence makes the raw order-k kernel energy at most its squared
operator norm times the k-th power of a single-observation energy cap. -/
theorem multilinear_second_le
    (H : 𝔐)
    (X : Fin k → 𝔓) (hind : iIndepFun X μ)
    (hm : 𝔒) (hL2 : 𝔉)
    E (hE : 𝘃₂) (henergy : 𝔏) :
    𝔄 ≤ 𝔊 * E ^ k := by
  classical
  have hnorm i := (vector_memLp_two (X i) (hm i) $ hL2 i ).norm
  have hind' : iIndepFun (fun i ω => 𝔅) μ :=
    hind.comp (fun _ => fun v => 𝚡₁ ^ 2)
       fun _ => measurable_norm.pow_const 2
  have hmeas' i := (hm i).norm.pow_const 2
  have hd := LiftL2.independent_finset_product_integrable hind' hmeas'
    (fun i => (hnorm i).integrable_sq) Finset.univ
  have hraw := (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap
    (Function.Embedding.refl $ Fin k ) X hind hm hL2).integrable_sq
  have hcomp : 𝔄 ≤
      𝔊 * ∫ ω, 𝔔 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hraw $ hd.const_mul 𝔊
    intro ω
    change H 𝔎 ^ 2 ≤ 𝔊 * 𝔔
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Finset.prod_pow] using
      𝔑 (H.le_opNorm 𝔎) 2
  rw [ hind'.integral_fun_prod_eq_prod_integral fun i => (hmeas' i).aestronglyMeasurable ] at hcomp
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_left _ $ sq_nonneg _
  calc
    _ ≤ ∏ _i : Fin k, E := Finset.prod_le_prod₀
      (fun i _ => integral_nonneg 𝖸) fun i _ => henergy i
    _ = E ^ k := 𝖢₄

/-- A factorial derivative cap produces the precise factorial power series
used in the pilot budget, proved from actual independent feature moments. -/
theorem factorial_kernel_budget
    (H : 𝔐)
    (X : Fin k → 𝔓) (hind : iIndepFun X μ)
    (hm : 𝔒) (hL2 : 𝔉)
    E a c Λ (hE : 𝘃₂) (ha : 𝖢₂) (hc : 𝗂₁) (hΛ : 𝖠₂)
    (henergy : 𝔏)
    (hderiv : ‖H‖ ≤ a * k.factorial * c ^ k) :
     (𝖽₁ * Λ ^ k)⁻¹ * 𝔄 ≤
      𝗅 * k.factorial * (𝗆₂ * E / Λ) ^ k := by
  have hfac : 0 < k.factorial := 𝖠₃
  have he := multilinear_second_le H X hind hm hL2 E hE henergy
  have h := mul_le_mul_of_nonneg_left
    (he.trans $ mul_le_mul_of_nonneg_right (𝔑 hderiv 2) $ pow_nonneg hE k )
    $ show 0 ≤ (k.factorial * Λ ^ k)⁻¹ by positivity
  apply h.trans_eq
  simp only [div_pow]
  field_simp [ne_of_gt hfac, ne_of_gt hΛ] <;> ring
