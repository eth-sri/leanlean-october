module

public import RequestProject.HerglotzGreen
public import RequestProject.HerglotzPoincare
public import RequestProject.BZField

/-!
# The trace inequality on a Lipschitz domain

For a bounded Lipschitz domain `Ω` with boundary parametrization `γ` (of constant speed `c`) we
prove the trace inequality

  `∫₀^{2π} |f(γ(θ))|² dθ ≤ C (∫_Ω |f|² + ∫_Ω |∇f|²)`

for bounded Lipschitz `f` (`trace_sq_le`). The proof uses a Lipschitz vector field `X` transversal
to the boundary (`exists_transversalField`): along the boundary the quantity
`g(θ) = Im(conj X(γ θ) · γ'(θ))` satisfies `|g| ≥ cκ/2` almost everywhere (a first-order
comparison of the flow of `X` with the curve), and `g ≤ 0` almost everywhere (Green's formula
against `ψ X̄ (1 - u_ε)`, with `u_ε` a cutoff of the signed distance, shows `∫ ψ(γ) g ≤ 0` for
every nonnegative Lipschitz `ψ`). Green's formula for `|f|² X̄` then gives the inequality.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- The transversality defect `g(θ) = Im(conj X(γ θ) · γ'(θ))` of a vector field `X` along `γ`. -/
def transGap (X : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℝ := (conj (X (γ θ)) * deriv γ θ).im

/-- Distance from `t x` to the line through `v`: with `s = t Re(conj v x)/|v|²`,
`|v| |t x - s v| = t |Im(conj v x)|`. -/
lemma norm_mul_norm_sub_proj {v x : ℂ} (hv : v ≠ 0) (t : ℝ) :
    ‖v‖ * ‖t * x - (t * (conj v * x).re / ‖v‖ ^ 2 : ℝ) * v‖ =
      |t| * |(conj v * x).im| := by
  have hn : (‖v‖ : ℂ) ≠ 0 := by simp_all
  have key : conj v * (t * x - (t * (conj v * x).re / ‖v‖ ^ 2 : ℝ) * v) =
      (t * (conj v * x).im : ℝ) * Complex.I := by
    have hvv : conj v * v = ‖v‖ ^ 2 := by
      simp [Complex.conj_mul']
    set w := conj v * x
    have : w = w.re + w.im * Complex.I := (Complex.re_add_im _).symm
    calc _ = t * w - (t * w.re / ‖v‖ ^ 2 : ℝ) * (conj v * v) := by ring
      _ = _ := by
        push_cast
        grind
  calc _ = ‖conj v * (t * x - (t * (conj v * x).re / ‖v‖ ^ 2 : ℝ) * v)‖ := by
        norm_num
    _ = _ := by
      rw [key, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]

/-- Pointwise transversality: at a point of differentiability of `γ` with `|γ'| = c`,
`|g(θ)| ≥ cκ/2`. -/
lemma abs_transGap_ge {X : ℂ → ℂ} {r₀ τ κ c : ℝ} (hr₀ : 0 < r₀) (hτ : 0 < τ)
    (hflow : ∀ z, |signedDist Ω z| < r₀ → ∀ t, 0 ≤ t → t ≤ τ →
        signedDist Ω z + κ * t ≤ signedDist Ω (z + t * X z))
    (hd : ∀ θ, signedDist Ω (γ θ) = 0) {θ : ℝ} (hγd : HasDerivAt γ (deriv γ θ) θ)
    (hc0 : 0 < c) (hc : ‖deriv γ θ‖ = c) :
    c * κ / 2 ≤ |transGap X γ θ| := by
  set v := deriv γ θ with hv
  set x := X (γ θ) with hx
  have hg : |(conj v * x).im| = |transGap X γ θ| := by
    rw [transGap, show conj v * x = conj (conj x * v) by simp [mul_comm],
      Complex.conj_im, abs_neg]
  set g := |transGap X γ θ| with hgdef
  by_contra hcon
  have hη : 0 < (c * κ - 2 * g) / (4 * (‖x‖ + 1)) := by
    apply div_pos <;> [linarith; positivity]
  set η := (c * κ - 2 * g) / (4 * (‖x‖ + 1)) with hηdef
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp ((hasDerivAt_iff_isLittleO_nhds_zero.mp hγd).def hη)
  have hv0 : v ≠ 0 := by rw [← norm_ne_zero_iff, hc]; positivity
  set t := min τ (δ * c / (2 * (‖x‖ + 1))) with htdef
  have ht0 : 0 < t := lt_min hτ (by positivity)
  have htτ : t ≤ τ := min_le_left _ _
  set s := t * (conj v * x).re / c ^ 2 with hs
  have hre : |(conj v * x).re| ≤ c * ‖x‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    simp_all
  have hsabs : |s| ≤ t * ‖x‖ / c := by
    rw [abs_div, abs_mul, abs_of_pos ht0, abs_of_pos (by positivity : 0 < c ^ 2)]
    rw [div_le_div_iff₀ (by positivity) hc0]
    have := mul_le_mul_of_nonneg_left hre ht0.le
    nlinarith
  have hsδ : |s| < δ := by
    refine hsabs.trans_lt ?_
    rw [div_lt_iff₀ hc0]
    have h1 : t * ‖x‖ ≤ δ * c / (2 * (‖x‖ + 1)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
    have h2 : δ * c / (2 * (‖x‖ + 1)) * ‖x‖ < δ * c := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg x, mul_pos hδ hc0]
    linarith
  have hfl := hflow (γ θ) (by simp_all) t ht0.le htτ
  rw [hd θ] at hfl
  have hlip := (lipschitzWith_signedDist Ω).dist_le_mul (γ θ + t * x) (γ (θ + s))
  rw [hd (θ + s), Real.dist_eq] at hlip
  have hproj := norm_mul_norm_sub_proj hv0 t (x := x)
  rw [hc, hg, abs_of_pos ht0] at hproj
  have hsplit : γ θ + t * x - γ (θ + s) = (t * x - s * v) -
      (γ (θ + s) - γ θ - s • v) := by
    rw [Complex.real_smul]; ring
  have hnorm : ‖γ θ + t * x - γ (θ + s)‖ ≤ t * g / c + η * (t * ‖x‖ / c) := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [le_div_iff₀ hc0, mul_comm, ← hproj]
    · refine (hδb  (by simpa [Real.dist_eq] using hsδ)).trans (mul_le_mul_of_nonneg_left ?_ hη.le)
      assumption
  have hmain : κ * t ≤ 2 * (t * g / c + η * (t * ‖x‖ / c)) := by
    have : |signedDist Ω (γ θ + ↑t * x)| ≤ 2 * ‖γ θ + t * x - γ (θ + s)‖ := by
      simp_all [dist_eq_norm]
    grind
  have hη2 : η * ‖x‖ ≤ (c * κ - 2 * g) / 4 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith 
  have : c * κ * t ≤ 2 * t * g + 2 * t * (η * ‖x‖) := by
    have := mul_le_mul_of_nonneg_left hmain hc0.le
    field_simp at this
    nlinarith
  nlinarith

lemma boundaryParam_mem_frontier (hγ : IsBoundaryParam Ω γ) (s : ℝ) : γ s ∈ frontier Ω := by
  have h2π : 0 < 2 * π := by positivity
  have hm := toIcoMod_mem_Ico h2π 0 s
  have he : γ (toIcoMod h2π 0 s) = γ s := by
    rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  rw [← hγ.image]
  grind

lemma dbar_mul_of_differentiableAt {F G : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) :
    dbar (fun x => F x * G x) z = F z * dbar G z + G z * dbar F z := by
  unfold dbar
  rw [(hF.hasFDerivAt.fun_mul hG.hasFDerivAt).fderiv]
  simp 
  ring

/-- For real `u`, `Re(conj w · ∂̄u) = Du(w)/2`. -/
lemma re_conj_mul_dbar_ofReal {u : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (w : ℂ) :
    (conj w * dbar (fun x => u x) z).re = fderiv ℝ u z w / 2 := by
  have h : fderiv ℝ (fun x => (u x : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ u z) :=
    ((Complex.ofRealCLM.hasFDerivAt ).comp z hu.hasFDerivAt).fderiv
  unfold dbar
  rw [h]
  have hlin : fderiv ℝ u z w = w.re * fderiv ℝ u z 1 + w.im * fderiv ℝ u z Complex.I := by
    conv_lhs => rw [show w = w.re • 1 + w.im • Complex.I by
      simp ]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin]
  simp 
  ring

/-- A function nondecreasing along a direction from a point has nonnegative directional
derivative there. -/
lemma fderiv_apply_nonneg_of_monotone {u : ℂ → ℝ} {z w : ℂ} (hu : DifferentiableAt ℝ u z)
    (hmono : ∀ᶠ t : ℝ in 𝓝[>] 0, u z ≤ u (z + t * w)) : 0 ≤ fderiv ℝ u z w := by
  have h1 : HasDerivAt (fun t : ℝ => z + t * w) w 0 := by
    have := ((hasDerivAt_id 0).ofReal_comp).mul_const w
    simp_all
  have hu' : HasFDerivAt u (fderiv ℝ u z) (z + 0 * w) := by
    simpa using hu.hasFDerivAt
  refine ge_of_tendsto (hu'.comp_hasDerivAt 0 h1).tendsto_slope_zero_right ?_
  filter_upwards [hmono, self_mem_nhdsWithin] with t ht htpos
  simp_all

/-- A bounded measurable `g` on the parameter interval with `∫ ψ(γ) g ≤ 0` for every Lipschitz
`ψ : ℂ → [0, 1]` is nonpositive almost everywhere (inner regularity and injectivity of `γ`). -/
lemma ae_nonpos_of_integral_comp_nonpos (hγ : IsBoundaryParam Ω γ) {g : ℝ → ℝ}
    (hgm : Measurable g) {B : ℝ} (hgb : ∀ θ, |g θ| ≤ B)
    (h : ∀ ψ : ℂ → ℝ, ∀ K : NNReal, LipschitzWith K ψ → (∀ z, 0 ≤ ψ z) → (∀ z, ψ z ≤ 1) →
      ∫ θ in 0..(2 * π), ψ (γ θ) * g θ ≤ 0) :
    ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), g θ ≤ 0 := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  set S := {θ | 0 < g θ} ∩ Ioo 0 (2 * π) with hSdef
  suffices hS : volume S = 0 by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have h2 : ∀ᵐ θ ∂volume, θ ≠ 2 * π := by
      simp [ae_iff]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS, h2] with θ h1 h2 hθ
    grind
  by_contra hS
  obtain ⟨K, hKS, hKc, hKpos⟩ := ((measurableSet_lt measurable_const hgm).inter measurableSet_Ioo).exists_lt_isCompact (pos_iff_ne_zero.mpr hS)
  set T := γ '' K with hT
  have hTc  := (hKc.image hKγ.continuous).isClosed
  have hTne : T.Nonempty := (nonempty_of_measure_ne_zero hKpos.ne').image _
  set ψ : ℕ → ℂ → ℝ := fun n z => max (1 - n * infDist z T) 0 with hψ
  have hψlip : ∀ n : ℕ, LipschitzWith n (ψ n) := fun n => by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    calc |max (1 - n * infDist z T) 0 - max (1 - n * infDist w T) 0|
        ≤ |(1 - n * infDist z T) - (1 - n * infDist w T)| :=
          abs_max_sub_max_le_abs _ _ _
      _ = n * |infDist z T - infDist w T| := by
          simp [show 1 - n * infDist z T - (1 - n * infDist w T) =             -(n * (infDist z T - infDist w T)) by ring, abs_neg, abs_mul, Nat.abs_cast]
      _ ≤ n * dist z w := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have := (lipschitz_infDist_pt T).dist_le_mul z w
          simp_all [Real.dist_eq]
  have hψ0 : ∀ n z, 0 ≤ ψ n z := fun n z => le_max_right _ _
  have hψ1 : ∀ n z, ψ n z ≤ 1 := fun n z =>
    max_le (by nlinarith [infDist_nonneg (x := z) (s := T)])
      zero_le_one
  have hlim : ∀ θ ∈ Ioc 0 (2 * π), Tendsto (fun n => ψ n (γ θ) * g θ) atTop
      (𝓝 (K.indicator g θ)) := by
    intro θ hθ
    by_cases hθK : θ ∈ K
    · have h0 : infDist (γ θ) T = 0 := infDist_zero_of_mem ⟨θ, hθK, rfl⟩
      simp_all
    · have hpos  := (hTc.notMem_iff_infDist_pos hTne).mp (by
        rintro ⟨k, hk, hkθ⟩
        have hkI  := (hKS hk).2
        rcases lt_or_eq_of_le hθ.2 with hlt | heq
        · exact hθK (hγ.injOn ⟨hkI.1.le, hkI.2⟩ ⟨hθ.1.le, hlt⟩ hkθ ▸ hk)
        · have : γ k = γ 0 := by rw [hkθ, heq]; simpa using hγ.periodic 0
          have := hγ.injOn ⟨hkI.1.le, hkI.2⟩ ⟨le_refl _, by positivity⟩ this
          simp_all)
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist (γ θ) T)
      filter_upwards [eventually_ge_atTop N] with n hn
      have : ψ n (γ θ) = 0 := by
        refine max_eq_right ?_
        have h1 : 1 < n * infDist (γ θ) T := by
          rw [div_lt_iff₀ hpos] at hN
          nlinarith [(Nat.cast_le (α := ℝ)).mpr hn]
        linarith
      simp_all
  have hT2 : Tendsto (fun n => ∫ θ in 0..(2 * π), ψ n (γ θ) * g θ) atTop
      (𝓝 (∫ θ in Ioc 0 (2 * π), K.indicator g θ)) := by
    simp_rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * π)]
    refine tendsto_integral_of_dominated_convergence (fun _ => B) (fun n => ?_)
      (integrable_const B) (fun n => Eventually.of_forall fun θ => ?_) ?_
    · exact (((hψlip n).continuous.comp hKγ.continuous).measurable.mul hgm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 n _)]
      nlinarith [hψ1 n (γ θ), hgb θ, abs_nonneg (g θ)]
    · rw [ae_restrict_iff' measurableSet_Ioc]
      simp_all
  have hle  :=
    le_of_tendsto' hT2 fun n => h (ψ n) n (hψlip n) (hψ0 n) (hψ1 n)
  have hKsub : K ⊆ Ioc 0 (2 * π) := fun k hk => ⟨(hKS hk).2.1, (hKS hk).2.2.le⟩
  rw [integral_indicator hKc.measurableSet, Measure.restrict_restrict hKc.measurableSet,
    inter_eq_left.mpr hKsub] at hle
  have hpos : 0 < ∫ θ in K, g θ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ (by
    refine Measure.integrableOn_of_bounded (M := B) hKc.measure_lt_top.ne
      hgm.aestronglyMeasurable ?_
    simp_all)]
    · have : Function.support g ∩ K = K :=
        inter_eq_right.mpr fun k hk => ((hKS hk).1).ne'
      grind
    · rw [EventuallyLE, ae_restrict_iff' hKc.measurableSet]
      exact Eventually.of_forall fun k hk => ((hKS hk).1).le
  linarith

lemma compl_nonempty_of_isBounded (hb : Bornology.IsBounded Ω) : Ωᶜ.Nonempty := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  refine ⟨(|R| + 1 : ℝ), fun h => ?_⟩
  have := hR h
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at this
  grind

/-- The cutoff `v_ε = 1 - clamp(d/ε)` of the signed distance. -/
def distCutoff (Ω : Set ℂ) (ε : ℝ) (z : ℂ) : ℝ := 1 - min 1 (max 0 (signedDist Ω z / ε))

lemma distCutoff_nonneg (ε : ℝ) (z : ℂ) : 0 ≤ distCutoff Ω ε z := by
  unfold distCutoff; norm_num

lemma distCutoff_le_one (ε : ℝ) (z : ℂ) : distCutoff Ω ε z ≤ 1 := by
  unfold distCutoff; norm_num

lemma lipschitzWith_distCutoff {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (2 / ε)) (distCutoff Ω ε) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  calc |1 - min 1 (max 0 (signedDist Ω z / ε)) - (1 - min 1 (max 0 (signedDist Ω w / ε)))|
      = |min 1 (max 0 (signedDist Ω w / ε)) - min 1 (max 0 (signedDist Ω z / ε))| := by
        ring
    _ ≤ |max 0 (signedDist Ω w / ε) - max 0 (signedDist Ω z / ε)| := abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
    _ ≤ |signedDist Ω w / ε - signedDist Ω z / ε| := abs_max_sub_max_le_max _ _ _ _ |>.trans (by simp)
    _ = |signedDist Ω w - signedDist Ω z| / ε := by rw [← sub_div, abs_div, abs_of_pos hε]
    _ ≤ 2 * dist w z / ε := by
        gcongr
        have := (lipschitzWith_signedDist Ω).dist_le_mul w z
        assumption
    _ = 2 / ε * dist z w := by rw [dist_comm]; ring

lemma distCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ε ≤ signedDist Ω z) :
    distCutoff Ω ε z = 0 := by
  unfold distCutoff
  simp_all [le_div_iff₀ hε]

lemma distCutoff_eq_one {ε : ℝ} {z : ℂ} (hz : signedDist Ω z = 0) : distCutoff Ω ε z = 1 := by
  simp [distCutoff, hz]

lemma distCutoff_antitone {ε : ℝ} (hε : 0 < ε) {z w : ℂ} (h : signedDist Ω z ≤ signedDist Ω w) :
    distCutoff Ω ε w ≤ distCutoff Ω ε z := by
  unfold distCutoff
  have  := div_le_div_of_nonneg_right h hε.le
  grind

/-- **Sign of the transversality defect** (integrated form): Green's formula for
`ψ X̄ v_ε` and `ε → 0` give `∫ ψ(γ) g ≤ 0` for nonnegative Lipschitz `ψ ≤ 1`. -/
theorem integral_comp_transGap_nonpos (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) {X : ℂ → ℂ} {LX : NNReal} {M r₀ τ κ : ℝ}
    (hX : LipschitzWith LX X) (hXM : ∀ z, ‖X z‖ ≤ M) (hr₀ : 0 < r₀) (hτ : 0 < τ) (hκ : 0 < κ)
    (hflow : ∀ z, |signedDist Ω z| < r₀ → ∀ t, 0 ≤ t → t ≤ τ →
        signedDist Ω z + κ * t ≤ signedDist Ω (z + t * X z))
    {ψ : ℂ → ℝ} {Kψ : NNReal} (hψ : LipschitzWith Kψ ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψ1 : ∀ z, ψ z ≤ 1) :
    ∫ θ in 0..(2 * π), ψ (γ θ) * transGap X γ θ ≤ 0 := by
  have hΩo  := hL.1.1
  have hΩu  := compl_nonempty_of_isBounded hb
  have hΩfin : volume Ω < ⊤ := hb.measure_lt_top
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hM0  := (norm_nonneg _).trans (hXM 0)
  -- the function `P = ψ X̄`
  have hψc : LipschitzWith Kψ (fun z => (ψ z : ℂ)) :=
    Complex.isometry_ofReal.lipschitz.comp hψ |>.weaken (by simp)
  have hXc : LipschitzWith LX (fun z => conj (X z)) :=
    (Complex.isometry_conj.lipschitz.comp hX).weaken (by simp)
  have hψb : ∀ z, ‖(ψ z : ℂ)‖ ≤ 1 := fun z => by
    simp_all [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 z)]
  have hXcb : ∀ z, ‖conj (X z)‖ ≤ M := fun z => by simp_all
  obtain ⟨KP, hKP⟩ := lipschitzWith_mul_of_bounded hψc hXc hψb hXcb
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ → ℂ, P = fun z => ψ z * conj (X z) := ⟨_, rfl⟩
  rw [← hPdef] at hKP
  have hPb : ∀ z, ‖P z‖ ≤ M := fun z => by
    simp only [hPdef, norm_mul]
    nlinarith [hψb z, hXcb z, norm_nonneg (conj (X z))]
  -- the boundary integral `J`
  have hJ : (∫ θ in 0..(2 * π), P (γ θ) * deriv γ θ).im =
      ∫ θ in 0..(2 * π), ψ (γ θ) * transGap X γ θ := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm (intervalIntegrable_comp_mul_deriv hKγ hKP.continuous)]
    simp [Complex.imCLM_apply, hPdef, transGap, mul_assoc]
  -- for each `ε`, the Green identity bounds `∫ ψ g`
  have hbound : ∀ ε, 0 < ε → ε < r₀ →
      ∫ θ in 0..(2 * π), ψ (γ θ) * transGap X γ θ ≤
        2 * ∫ z in Ω, distCutoff Ω ε z * KP := by
    intro ε hε hεr
    have hvlip := lipschitzWith_distCutoff (Ω := Ω) hε
    obtain ⟨V, hVdef⟩ : ∃ V : ℂ → ℂ, V = fun z => (distCutoff Ω ε z : ℂ) := ⟨_, rfl⟩
    have hVlip : LipschitzWith (Real.toNNReal (2 / ε)) V := by
      rw [hVdef]; exact (Complex.isometry_ofReal.lipschitz.comp hvlip).weaken (by simp)
    have hVb : ∀ z, ‖V z‖ ≤ 1 := fun z => by
      rw [hVdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (distCutoff_nonneg _ _)]
      exact distCutoff_le_one _ _
    obtain ⟨KΦ, hKΦ⟩ := lipschitzWith_mul_of_bounded hKP hVlip hPb hVb
    have hG := integral_boundary_eq_dbar_of_bounded hb hL hγ hKΦ fun z => by
      rw [norm_mul]; exact mul_le_mul (hPb z) (hVb z) (norm_nonneg _) hM0
    have hbd : ∀ θ, P (γ θ) * V (γ θ) * deriv γ θ = P (γ θ) * deriv γ θ := fun θ => by
      simp [hVdef, distCutoff_eq_one (signedDist_eq_zero_of_frontier hΩo (boundaryParam_mem_frontier hγ θ))]
    simp only [hbd] at hG
    have hint : IntegrableOn (dbar (fun x => P x * V x)) Ω := by
      refine Measure.integrableOn_of_bounded (M := KΦ) hΩfin.ne
        (measurable_dbar _).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      exact norm_dbar_le hKΦ z
    rw [← hJ, hG]
    have him : (2 * Complex.I * ∫ z in Ω, dbar (fun x => P x * V x) z).im =
        2 * ∫ z in Ω, (dbar (fun x => P x * V x) z).re := by
      have hre : ∫ z in Ω, (dbar (fun x => P x * V x) z).re =
          (∫ z in Ω, dbar (fun x => P x * V x) z).re := by
        have := Complex.reCLM.integral_comp_comm hint; assumption
      simp_all
    rw [him]
    gcongr 2 * ?_
    refine integral_mono_ae hint.re ?_ ?_
    · exact (Measure.integrableOn_of_bounded (M := KP) hΩfin.ne
        ((hvlip.continuous.mul continuous_const).aestronglyMeasurable)
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (distCutoff_nonneg _ _), NNReal.abs_eq]
          nlinarith [distCutoff_le_one (Ω := Ω) ε z]))
    · filter_upwards [ae_restrict_mem hΩo.measurableSet,
        ae_restrict_of_ae (hKP.ae_differentiableAt ),
        ae_restrict_of_ae (hvlip.ae_differentiableAt )] with z hz hPd hvd
      rw [dbar_mul_of_differentiableAt hPd (by
        rw [hVdef]; fun_prop), Complex.add_re]
      -- the transport term has a sign
      have hmono : ∀ᶠ t : ℝ in 𝓝[>] 0, -distCutoff Ω ε z ≤ -distCutoff Ω ε (z + t * X z) := by
        have hdz  := signedDist_pos_of_mem hΩo hΩu hz
        rcases lt_or_ge (signedDist Ω z) r₀ with hlt | hge
        · filter_upwards [Ioo_mem_nhdsGT hτ] with t ht
          have := hflow z (by grind) t ht.1.le ht.2.le
          have := distCutoff_antitone  hε
            (show signedDist Ω z ≤ signedDist Ω (z + t * X z) by nlinarith [ht.1])
          linarith
        · have hc : ContinuousAt (fun t : ℝ => signedDist Ω (z + t * X z)) 0 :=
            ((continuous_signedDist Ω).comp (continuous_const.add
              (Complex.continuous_ofReal.mul continuous_const))).continuousAt
          filter_upwards [nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds (by simpa using hεr.trans_le hge)))] with t ht
          rw [distCutoff_eq_zero hε ht.le, distCutoff_eq_zero hε (by linarith)]
      have hD := fderiv_apply_nonneg_of_monotone hvd.neg hmono
      rw [fderiv_neg, ContinuousLinearMap.neg_apply] at hD
      have h1 : (P z * dbar V z).re = ψ z * (fderiv ℝ (distCutoff Ω ε) z (X z) / 2) := by
        simp [hPdef, hVdef, mul_assoc, re_conj_mul_dbar_ofReal hvd]
      have h2 : (V z * dbar P z).re ≤ distCutoff Ω ε z * KP := by
        rw [hVdef]; rw [Complex.re_ofReal_mul]
        exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (norm_dbar_le hKP z))
          (distCutoff_nonneg _ _)
      have h3 : ψ z * (fderiv ℝ (distCutoff Ω ε) z (X z) / 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hψ0 z) (by linarith)
      linarith
  -- let `ε → 0`
  have hlim : Tendsto (fun n : ℕ => 2 * ∫ z in Ω, distCutoff Ω (r₀ / (n + 2)) z * KP) atTop
      (𝓝 (2 * 0)) := by
    refine Tendsto.const_mul 2 ?_
    have : (0 : ℝ) = ∫ z in Ω, 0 := by simp
    rw [this]
    haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hΩfin⟩
    refine tendsto_integral_of_dominated_convergence (fun _ => KP) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun z => ?_) ?_
    · exact ((lipschitzWith_distCutoff (by positivity)).continuous.mul
        continuous_const).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (distCutoff_nonneg _ _), NNReal.abs_eq]
      nlinarith [distCutoff_le_one (Ω := Ω) (r₀ / (n + 2)) z]
    · filter_upwards [ae_restrict_mem hΩo.measurableSet] with z hz
      have ht : Tendsto (fun n : ℕ => r₀ / (n + 2)) atTop (𝓝 0) := by
        have := tendsto_const_div_atTop_nhds_zero_nat r₀
        have h2 := (tendsto_add_atTop_iff_nat 2).mpr this
        grind
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ht.eventually (gt_mem_nhds (signedDist_pos_of_mem hΩo hΩu hz))] with n hn
      simp [distCutoff_eq_zero (by positivity) hn.le]
  refine ge_of_tendsto' (by simpa using hlim) fun n => hbound _ (by positivity) ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith 

/-- The transversality defect is `≤ -cκ/2` almost everywhere. -/
theorem transGap_le_ae (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) {X : ℂ → ℂ} {LX : NNReal} {M r₀ τ κ c : ℝ}
    (hX : LipschitzWith LX X) (hXM : ∀ z, ‖X z‖ ≤ M) (hr₀ : 0 < r₀) (hτ : 0 < τ) (hκ : 0 < κ)
    (hflow : ∀ z, |signedDist Ω z| < r₀ → ∀ t, 0 ≤ t → t ≤ τ →
        signedDist Ω z + κ * t ≤ signedDist Ω (z + t * X z))
    (hc0 : 0 < c) (hc : ∀ᵐ θ, ‖deriv γ θ‖ = c) :
    ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), transGap X γ θ ≤ -(c * κ / 2) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hgb : ∀ θ, |transGap X γ θ| ≤ M * Kγ := fun θ => by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hXM _) (norm_deriv_le_of_lipschitz hKγ) (norm_nonneg _)
      ((norm_nonneg _).trans (hXM 0))
  filter_upwards [ae_nonpos_of_integral_comp_nonpos hγ (by
    exact Complex.measurable_im.comp
      (((Complex.continuous_conj.comp (hX.continuous.comp hKγ.continuous)).measurable).mul
        (measurable_deriv γ))) hgb fun ψ K hψ hψ0 hψ1 =>
    integral_comp_transGap_nonpos hb hL hγ hX hXM hr₀ hτ hκ hflow hψ hψ0 hψ1, ae_restrict_of_ae (by
    filter_upwards [hc, hKγ.ae_differentiableAt ] with θ h1 h2
    exact abs_transGap_ge hr₀ hτ hflow (fun θ =>
    signedDist_eq_zero_of_frontier hL.1.1 (boundaryParam_mem_frontier hγ θ)) h2.hasDerivAt hc0 h1)] with θ h1 h2
  grind


lemma norm_dbar_le_half (F : ℂ → ℂ) (z : ℂ) :
    ‖dbar F z‖ ≤ (‖fderiv ℝ F z 1‖ + ‖fderiv ℝ F z Complex.I‖) / 2 := by
  unfold dbar
  rw [norm_div, Complex.norm_ofNat]
  gcongr
  refine (norm_add_le _ _).trans ?_
  norm_num

lemma fderiv_conj_apply {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (w : ℂ) :
    fderiv ℝ (fun x => conj (f x)) z w = conj (fderiv ℝ f z w) := by
  have := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt ).comp z hf.hasFDerivAt
  rw [show (fun x => conj (f x)) = (Complex.conjCLE.toContinuousLinearMap ∘ f) from rfl,
    this.fderiv]
  rfl

lemma norm_dbar_normSq_mul_le {f Y : ℂ → ℂ} {z : ℂ} {LY : NNReal} {M : ℝ}
    (hf : DifferentiableAt ℝ f z) (hY : DifferentiableAt ℝ Y z) (hYL : LipschitzWith LY Y)
    (hYM : ‖Y z‖ ≤ M) :
    ‖dbar (fun x => (f x * conj (f x)) * Y x) z‖ ≤
      ‖f z‖ ^ 2 * LY + M * (‖f z‖ ^ 2 / 2 + gradSq f z) := by
  have hcf : DifferentiableAt ℝ (fun x => conj (f x)) z :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp z hf
  have hN : DifferentiableAt ℝ (fun x => f x * conj (f x)) z := hf.mul hcf
  rw [dbar_mul_of_differentiableAt hN hY, dbar_mul_of_differentiableAt hf hcf]
  set a := ‖fderiv ℝ f z 1‖
  set b := ‖fderiv ℝ f z Complex.I‖
  have h1  := norm_dbar_le_half f z
  have h2 : ‖dbar (fun x => conj (f x)) z‖ ≤ (a + b) / 2 := by
    refine (norm_dbar_le_half _ z).trans ?_
    rw [fderiv_conj_apply hf, fderiv_conj_apply hf, Complex.norm_conj, Complex.norm_conj]
  have h3  := norm_dbar_le hYL z
  have hM0  := (norm_nonneg _).trans hYM
  have hgs : gradSq f z = a ^ 2 + b ^ 2 := rfl
  have hfz : ‖f z * conj (f z)‖ = ‖f z‖ ^ 2 := by rw [norm_mul, Complex.norm_conj]; ring
  calc ‖f z * conj (f z) * dbar Y z + Y z * (f z * dbar (fun x => conj (f x)) z +
        conj (f z) * dbar f z)‖
      ≤ ‖f z‖ ^ 2 * LY + M * (‖f z‖ * (a + b)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]; nlinarith
        · rw [norm_mul]
          refine mul_le_mul hYM ?_ (norm_nonneg _) hM0
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          nlinarith [norm_nonneg (f z)]
    _ ≤ _ := by
        nlinarith [sq_nonneg (‖f z‖ - (a + b)), sq_nonneg (a - b)]

/-- **Trace inequality** on a bounded Lipschitz domain: for bounded Lipschitz `f`,
`∫₀^{2π} |f(γ θ)|² dθ ≤ C (∫_Ω |f|² + ∫_Ω |∇f|²)`. -/
theorem trace_sq_le (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℂ) (Kf : NNReal), LipschitzWith Kf f → ∀ B : ℝ,
      (∀ z, ‖f z‖ ≤ B) →
      ∫ θ in 0..(2 * π), ‖f (γ θ)‖ ^ 2 ≤
        C * ((∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq f z) := by
  have hΩfin : volume Ω < ⊤ := hb.measure_lt_top
  obtain ⟨X, LX, M, r₀, τ, κ, hX, hXM, hr₀, hτ, hκ, hflow⟩ :=
    exists_transversalField hb hL hL.1.2.nonempty (compl_nonempty_of_isBounded hb)
  obtain ⟨c, hc0, hc⟩ := hγ.const_speed
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hg := transGap_le_ae hb hL hγ hX hXM hr₀ hτ hκ hflow hc0 hc
  have hM0  := (norm_nonneg _).trans (hXM 0)
  refine ⟨4 * (LX + M) / (c * κ), by positivity, fun f Kf hf B hB => ?_⟩
  have hB0  := (norm_nonneg _).trans (hB 0)
  set Y : ℂ → ℂ := fun z => conj (X z) with hYdef
  have hYL : LipschitzWith LX Y := (Complex.isometry_conj.lipschitz.comp hX).weaken (by simp)
  have hYM : ∀ z, ‖Y z‖ ≤ M := fun z => by simp_all
  have hcf : LipschitzWith Kf (fun z => conj (f z)) :=
    (Complex.isometry_conj.lipschitz.comp hf).weaken (by simp)
  have hcfB : ∀ z, ‖conj (f z)‖ ≤ B := fun z => by simp_all
  obtain ⟨KN, hKN⟩ := lipschitzWith_mul_of_bounded hf hcf hB hcfB
  have hNB : ∀ z, ‖f z * conj (f z)‖ ≤ B * B := fun z => by
    rw [norm_mul]; exact mul_le_mul (hB z) (hcfB z) (norm_nonneg _) hB0
  obtain ⟨KΦ, hKΦ⟩ := lipschitzWith_mul_of_bounded hKN hYL hNB hYM
  have hΦB : ∀ z, ‖f z * conj (f z) * Y z‖ ≤ B * B * M := fun z => by
    rw [norm_mul]; exact mul_le_mul (hNB z) (hYM z) (norm_nonneg _) (by positivity)
  have hIm : (∫ θ in 0..(2 * π), f (γ θ) * conj (f (γ θ)) * Y (γ θ) * deriv γ θ).im =
      ∫ θ in 0..(2 * π), ‖f (γ θ)‖ ^ 2 * transGap X γ θ := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm (intervalIntegrable_comp_mul_deriv hKγ hKΦ.continuous)]
    simp_all [Complex.imCLM_apply, transGap, Complex.mul_conj', mul_assoc, ← Complex.ofReal_pow]
  -- the interior side
  have hdint : IntegrableOn (dbar (fun x => f x * conj (f x) * Y x)) Ω := by
    refine Measure.integrableOn_of_bounded (M := KΦ) hΩfin.ne
      (measurable_dbar _).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    exact norm_dbar_le hKΦ z
  have hre : (2 * Complex.I * ∫ z in Ω, dbar (fun x => f x * conj (f x) * Y x) z).im ≥
      -(2 * ∫ z in Ω, ‖dbar (fun x => f x * conj (f x) * Y x) z‖) := by
    have : (2 * Complex.I * ∫ z in Ω, dbar (fun x => f x * conj (f x) * Y x) z).im =
        2 * (∫ z in Ω, dbar (fun x => f x * conj (f x) * Y x) z).re := by simp
    have h1 := norm_integral_le_integral_norm
      (μ := volume.restrict Ω) (dbar (fun x => f x * conj (f x) * Y x))
    have h2 := Complex.abs_re_le_norm (∫ z in Ω, dbar (fun x => f x * conj (f x) * Y x) z)
    grind
  -- integrability of the interior majorant
  have hfsq : IntegrableOn (fun z => ‖f z‖ ^ 2) Ω :=
    Measure.integrableOn_of_bounded  hΩfin.ne
      (hf.continuous.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB z) 2)
  have hgsq : IntegrableOn (gradSq f) Ω := by
    refine Measure.integrableOn_of_bounded (M := 2 * Kf ^ 2) hΩfin.ne ?_
      (Eventually.of_forall fun z => ?_)
    · exact (((measurable_fderiv_apply_const ℝ f 1).norm.pow_const 2).add
        ((measurable_fderiv_apply_const ℝ f Complex.I).norm.pow_const 2)).aestronglyMeasurable
    · have hD := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := z)
      have h1 : ‖fderiv ℝ f z 1‖ ≤ Kf := by
        simpa using (fderiv ℝ f z).le_of_opNorm_le hD 1
      have h2 : ‖fderiv ℝ f z Complex.I‖ ≤ Kf := by
        simpa using (fderiv ℝ f z).le_of_opNorm_le hD Complex.I
      unfold gradSq
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (fderiv ℝ f z 1), norm_nonneg (fderiv ℝ f z Complex.I)]
  have hmaj : ∫ z in Ω, ‖dbar (fun x => f x * conj (f x) * Y x) z‖ ≤
      (LX + M) * ((∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq f z) := by
    have hI1 : IntegrableOn (fun z => ‖f z‖ ^ 2 * LX) Ω := hfsq.mul_const _
    have hI3  := hfsq.div_const 2
    have hI2 : IntegrableOn (fun z => M * (‖f z‖ ^ 2 / 2 + gradSq f z)) Ω :=
      (hI3.add hgsq).const_mul M
    have hle : ∫ z in Ω, ‖dbar (fun x => f x * conj (f x) * Y x) z‖ ≤
        ∫ z in Ω, (‖f z‖ ^ 2 * LX + M * (‖f z‖ ^ 2 / 2 + gradSq f z)) := by
      refine integral_mono_ae hdint.norm ?_ ?_
      · exact hI1.add hI2
      · filter_upwards [ae_restrict_of_ae (hf.ae_differentiableAt ),
          ae_restrict_of_ae (hYL.ae_differentiableAt )] with z h1 h2
        exact norm_dbar_normSq_mul_le h1 h2 hYL (hYM z)
    refine hle.trans ?_
    rw [integral_add hI1 hI2, integral_const_mul, integral_add hI3 hgsq, integral_mul_const,
      integral_div]
    have hf0 : 0 ≤ ∫ z in Ω, ‖f z‖ ^ 2 := integral_nonneg fun z => by positivity
    have hg0 : 0 ≤ ∫ z in Ω, gradSq f z := integral_nonneg fun z => by unfold gradSq; positivity
    nlinarith 
  -- the boundary side
  have hbd : ∫ θ in 0..(2 * π), ‖f (γ θ)‖ ^ 2 * transGap X γ θ ≤
      -(c * κ / 2) * ∫ θ in 0..(2 * π), ‖f (γ θ)‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * π)]
    have hcont  := (hf.continuous.comp hKγ.continuous).norm.pow 2
    refine integral_mono_ae ?_ ?_ ?_
    · refine Measure.integrableOn_of_bounded (M := B ^ 2 * (M * Kγ)) measure_Ioc_lt_top.ne
        (hcont.measurable.mul (Complex.measurable_im.comp
          (((Complex.continuous_conj.comp (hX.continuous.comp hKγ.continuous)).measurable).mul
            (measurable_deriv γ)))).aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hB _) 2) ?_ (abs_nonneg _)
        (by positivity)
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hXM _) (norm_deriv_le_of_lipschitz hKγ) (norm_nonneg _) hM0
    · exact (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul _
    · filter_upwards [hg] with θ hθ
      nlinarith
  rw [integral_boundary_eq_dbar_of_bounded hb hL hγ hKΦ hΦB] at hIm
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hc0 hκ)]
  nlinarith
end PolyaNeumann
