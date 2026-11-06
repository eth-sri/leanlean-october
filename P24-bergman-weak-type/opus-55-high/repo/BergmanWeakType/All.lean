module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import BergmanWeakType.Domain
public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.UniformSpace.Ascoli
import all Mathlib.Analysis.Complex.RiemannMapping
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import BergmanWeakType.Domain

@[expose] public section

noncomputable section

open MeasureTheory Set Real Filter Metric
open scoped ENNReal Topology ComplexConjugate Pointwise
local macro "𝔣" : term => `(by fun_prop)
local macro "𝔩" : term => `(by linarith)
local macro "𝔭" : term => `(by positivity)
local macro "𝔞" : term => `(by simp_all)
local macro "𝔤" : term => `(by grind)
local macro "𝔫" : term => `(by norm_num)
local macro "𝔰" : term => `(by simp)
local macro "𝔑" : term => `(by nlinarith)
local notation "I₁" => Ioo (0 : ℝ) 1
local notation "J₁" => Ico 0 1
set_option hygiene false
local notation:max "𝔣ᵥ" F:max => F volume hU.measurableSet (hasFDerivWithinAt_of_differentiableOn hU hφ_ hinj) hinj g
local notation "𝔄" X => ∀ r ∈ I₁, X
local notation:max "𝔠₁" r:max => (1 + r ^ 2 - 2 * r * cos θ)
-- p1
-- p2
local notation:max "𝖜" F:max => F _ _
local notation:max "𝖞" F:max => F r hr
local notation:max "𝖕" F:max => F α f z
local notation:max "𝖗" F:max => F r θ
local notation "𝖔" => (1 - u) ^ α
local notation "𝖙" => (1 - star ζ * w) ^ 2
local notation "𝖊" => ℂ → E
local notation "𝖘" => a w ^ 2 + b w ^ 2
local notation "𝖈" => SourceCont K a b
local notation "𝖆" => K a w
local macro "𝕡" : tactic => `(tactic| let := weightedArea_isProbabilityMeasure hα)
local notation "𝕀" => r ∈ I₁
local notation "𝕆" => 1 - z
local notation "𝕖" => ε ^ 2
local notation "𝕓" => ball 0 r
local notation "𝕙" => α / 2
local notation "𝕥" => angularComponent a b θ
local notation "𝕤" => polarDenominator a b r θ
local notation:max "𝕄" F:max k:max => F k a b r θ
local notation:max "𝕐" F:max => F hK_ hμ hf_
-- 𝔴
local notation "𝕯" => deriv φ
local notation "𝕂" => kernel ζ w
local notation "𝕹" => normalizer α
local notation "𝕮" => DifferentiableOn ℂ
local notation "𝕱" => f w
local notation "𝖃" => X → ℝ
local notation "𝕭" => (ball a R)
local notation "𝖚" => ‖u‖ ^ 2
local notation "𝖟" => 1 - z * star w
local notation "𝕏" => circleDenominator r x
local notation "𝕘" => ‖g z‖ ^ 2
local notation "𝕗" => ℝ → ℝ
local notation "𝕦" => ℂ → ℝ
local notation "𝕒" => radialComponent a b θ
local notation "𝕟" => normalizer α r
local notation "𝕋" => ℂ → ℂ
local notation "𝕔" => circleDenominator r (Real.cos θ)
local notation "𝕕" => 𝕯 w
local notation "𝕜" => weightedKernel α z
local notation "𝕣" => r ^ 2
local notation "𝕫" => ‖z‖
local notation:max "𝓏" b => fun z ↦ b
local notation:max "𝓌" b => fun w ↦ b
local notation:max "𝒽" b => fun _ ↦ b
local notation:max "𝓍" b => fun x ↦ b
local notation:max "𝓉" b => fun θ ↦ b
local notation:max "𝒷" b => fun h ↦ b
local notation:max "𝓊" b => fun u ↦ b
local notation "𝔴" => weightedArea α
local notation "α₁" => α + 1
local notation "α₂" => α + 2
local notation "𝔯" => 1 - 𝕣
local notation "𝔨₂" => k ^ 2 / 𝔯
local notation "𝔨₁" => 2 * k * r / 𝔯
local notation "𝔵" => 1 - x ^ 2
local notation "𝔷" => 1 - 𝕫 ^ 2
local notation "τ" => 2 * π
local notation "𝔨" => -k / 2
local notation "𝔓" => fun f z ↦ ‖𝖕 weightedProjection‖ₑ
local notation "𝔟" => a ^ 2 + b ^ 2
local notation "𝔢" => (x - c) ^ 2 + 𝕖
local notation "𝔥" => -α₂ / 2
local notation "𝔪" => -α₂
local notation "𝟘" => (0 : ℝ)
local notation "𝟎" => (0 : ℂ)
local notation "𝔮" => 𝖗 F / J r
local notation "𝔡" => (‖𝕕‖ ^ 2 : ℝ)
local notation "𝔦" => integrable_const (1 : ℂ)
local notation "𝔠" => 𝓏 min 𝖕 weightedDiskPotential c
local notation "𝔳" => fun z : ℂ ↦ 𝕫 ^ 2
local notation "ℛ" => (r : ℂ)
local notation "ℭ" => (c : ℂ)
local notation "𝔧" => (-1 : ℝ)
local notation "𝔬" => norm_nonneg _
local notation "𝔔" => q - 1
local notation "𝔄" => 1 + 𝕙
local notation "𝔅" => boundaryCap R
local notation "𝔦ᵢ" => (𝔅).indicator (𝓏 𝔷 ^ α)
local notation "𝔇" => area.restrict Ω
local notation "𝔈" => 𝖜 measure_ne_top
local notation "𝔊" => ℝ → ℝ → ℝ → ℝ → ℝ
local notation "𝔉" => ℝ → ℝ → ℝ
local notation "ℌ" => Icc 0 1
local notation "ℑ" => ball 0 1
local notation "𝔍" => 1 / 2
local notation "𝔎" => p / 2
local notation "𝔏" => 2 * r
local notation "𝔐" => x - c
local notation "𝔒" => y + h
local notation "𝔗" => 𝖞 hr2
local notation "𝔘" => φ w
local notation "𝔙" => φ z
local notation "𝔚" => F f
local notation "𝔛" => a w
local notation "𝔜" => b w
local notation:max "𝒵" b => fun z hz ↦ b
local notation:max "𝒲" b => fun w hw ↦ b
local notation:max "𝓡" b => fun r hr ↦ b
local notation:max "𝒳" b => fun x hx ↦ b
local notation:max "𝒴" b => fun y hy ↦ b
local notation:max "𝒫" b => fun p hp ↦ b
local notation:max "𝓡θ" b => fun r hr θ ↦ b
local notation:max "𝒰" b => fun _ _ ↦ b
local notation:max "𝒯" b => fun θ _ ↦ b
local notation "ℐ" K:max u:max t:max => polarIntegral K a b μ f u t
local notation "𝔅ᵖ" K:max u:max t:max => polarIntegral K cos sin (volume.restrict (Set.Icc 0 τ)) (𝒽 τ⁻¹) u t
local notation "𝔠ᵃ" X:max => Real.circleAverage (fun ζ : ℂ ↦ ‖1 - ℛ * ζ‖ ^ X) 0 1
local notation "𝔷ᵣ" => ℛ ^ 2 * z
local notation "𝔍ᵧ" X => ∫ y in 𝟘..1, X
local notation "𝔠ₘ" => circleMap 0 r
local notation:max "𝔬ₖ" X:max => 𝓏 ‖𝕆‖ ^ X
local notation "𝔈ₙ" X => ∃ η, 0 < η ∧ η ≤ 1 ∧ X
local notation "𝔰ₑ" => smoothCap ε c
local notation "𝔭ₒ" => polarOperator k a b μ f r θ
local notation "𝔴ᵣ" => (𝔴).real (Metric.ball a r)
local notation "𝔄ₖ" X => ∀ w ∈ K, X
local notation:max "𝔫₂" X:max => ‖X‖ ^ 2

local notation "𝔤ᵧ" => gammaConstant α
local notation "𝔞₂" => α₁ / 2
local notation "𝔮ₖ" => q w * 𝕂
local notation "𝔨ᵥ" => ‖𝕜 w‖
local notation "𝔍ᵢ" X => ∫ x in 𝔧..1, X
local notation "𝔍ᵦ" X => ∫ w in 𝕓, X ∂area

namespace Complex.UnitDisc
-- FILE BergmanWeakType.Rigidity.UnitDiscShift
/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Adapted from mathlib pull request 33505, commit
d43061d911b1aeae0788591da437a3b115098962, for Lean v4.35.0-rc2.
Upstream source: Mathlib/Analysis/Complex/UnitDisc/Shift.lean
-/
/-! # Shift on the unit disc -/


lemma shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero


/-- Auxiliary definition for `shift` below. -/
def shiftFun (z w : 𝔻) : 𝔻 :=
  mk ((z + w : ℂ) / (1 + conj ↑z * w)) <| by
    rw [norm_div, div_lt_one (norm_pos_iff.2 (shift_den_ne_zero z w)),
      ← sq_lt_sq₀ 𝔬 𝔬, ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    have hz := z.normSq_lt_one
    have hw := w.normSq_lt_one
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, one_re,
      one_im] at *
    nlinarith [mul_pos (sub_pos.2 hz) (sub_pos.2 hw)]

theorem shiftFun_eq_iff {z w u} : shiftFun z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← coe_inj, shiftFun, coe_mk, div_eq_iff <| 𝖜 shift_den_ne_zero]
  ring_nf

theorem shiftFun_neg_apply_shiftFun (z w) : shiftFun (-z) (shiftFun z w) = w := by
  rw [shiftFun_eq_iff, shiftFun, coe_mk, add_div_eq_mul_add_div, ← mul_div_assoc,
    add_div_eq_mul_add_div]
  · simp; ring
  all_goals exact shift_den_ne_zero z w


/-- The automorphism of the unit disc that sends zero to `z`. -/
def shift (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun z
  invFun := shiftFun (-z)
  left_inv := shiftFun_neg_apply_shiftFun _
  right_inv w := by simpa using shiftFun_neg_apply_shiftFun (-z) w

theorem coe_shift (z w) : (shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := by rfl

@[simp]
theorem shift_eq_zero_iff {z w} : shift z w = 0 ↔ w = -z := by
  show shiftFun z w = 0 ↔ _
  rw [shiftFun_eq_iff, ← coe_inj]
  simp [add_eq_zero_iff_eq_neg']




theorem continuous_shift (z : 𝔻) : Continuous z.shift := by
  simp only [isEmbedding_coe.continuous_iff]
  exact .div 𝔣 𝔣 𝒽 shift_den_ne_zero _ _

end UnitDisc
-- FILE BergmanWeakType.Rigidity.RiemannMapping
/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Adapted from mathlib pull request 33505, commit
d43061d911b1aeae0788591da437a3b115098962, for Lean v4.35.0-rc2.
Upstream source: Mathlib/Analysis/Complex/RiemannMapping.lean
-/
/-!
# Riemann mapping theorem (draft)
-/

section
variable {ι : Type*} {U : Set ℂ} {l : Filter ι} [l.NeBot] {F : ι → 𝕋} {f : 𝕋} (hUo : IsOpen U) (hUc : IsPreconnected U)
  (hFd : ∀ᶠ i in l, 𝕮 (F i) U) (hf : TendstoLocallyUniformlyOn F f l U)
include hUo hUc hFd hf
theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn (hF : ∀ᶠ i in l, ∀ x ∈ U, F i x ≠ 0) :
    EqOn f 0 U ∨ ∀ x ∈ U, f x ≠ 0 := by
  have hfd := hf.differentiableOn hFd hUo
  rw [or_iff_not_imp_left]
  intro hf₀ c hc hfc
  rcases hfd.analyticAt (hUo.mem_nhds hc) |>.eventually_eq_zero_or_eventually_ne_zero
    with hfc₀ | hfc₀
  · exact hf₀ <| hfd.analyticOnNhd hUo |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hc hfc₀
  rw [eventually_nhdsWithin_iff] at hfc₀
  rcases Metric.nhds_basis_closedBall.eventually_iff.mp (hfc₀.and <| hUo.eventually_mem hc)
    with ⟨R, hR₀, hR⟩
  have hRU : closedBall c R ⊆ U := by grind
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere c R).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hR₀.le) (hfd.continuousOn.mono <| sphere_subset_closedBall.trans hRU).norm
  have hm : 0 < ‖f w₀‖ / 2 := by
    simpa using (hR <| sphere_subset_closedBall hw₀).1 <| ne_of_mem_sphere hw₀ hR₀.ne'
  rcases (hF.and <| hFd.and (Metric.tendstoUniformlyOn_iff.1 ((tendstoLocallyUniformlyOn_iff_forall_isCompact
    hUo).1 hf _ hRU (isCompact_closedBall c R)) _ hm)).exists with ⟨i, hi₀, hid, hi⟩
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    ((hid.inv hi₀).diffContOnCl_ball hRU) (C := (‖f w₀‖ / 2)⁻¹) (𝒲 ?_)
    (subset_closure <| mem_ball_self hR₀)
  · have := hi c (mem_closedBall_self hR₀.le)
    rw [Pi.inv_apply, norm_inv, inv_le_inv₀ 𝔞 hm] at key
    simp [hfc] at this
    linarith
  · rw [frontier_ball c hR₀.ne'] at hw
    have h1 := hi w <| sphere_subset_closedBall hw
    have h2 : ‖f w₀‖ ≤ ‖𝕱‖ := hmin hw
    rw [Pi.inv_apply, norm_inv]
    apply inv_anti₀ hm
    rw [dist_eq_norm] at h1
    linarith [norm_sub_norm_le 𝕱 <| F i w]

theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn (hF : ∀ᶠ i in l, InjOn (F i) U) :
    (∃ C, ∀ x ∈ U, f x = C) ∨ InjOn f U := by
  rw [or_iff_not_imp_left]
  intro hfU x hx y hy hxy
  by_contra! hne
  obtain ⟨r, hr₀, hrU, hry⟩ : ∃ r > 0, ball x r ⊆ U ∧ y ∉ ball x r := by
    simp_rw [← subset_compl_singleton_iff, ← subset_inter_iff, ← Metric.mem_nhds_iff]
    simp [hUo.mem_nhds hx, hne]
  have hf_sub : TendstoLocallyUniformlyOn (fun i z ↦ F i z - F i y) (f · - f y) l (ball x r) :=
    (hf.mono hrU).fun_sub ((hf.tendsto_at hy).tendstoUniformlyOn_const _).tendstoLocallyUniformlyOn
  refine eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn isOpen_ball isPreconnected_ball
    ?_ hf_sub (hF.mono fun i hi z hz ↦ ?_) |>.resolve_left ?_ x (by simpa) 𝔞
  · exact hFd.mono fun i hi ↦ hi.mono hrU |>.sub_const _
  · rw [sub_ne_zero, hi.ne_iff (hrU hz) hy]
    exact ne_of_mem_of_not_mem hz hry
  · intro heq
    refine hfU ⟨f y, ?_⟩
    refine hf.differentiableOn hFd hUo |>.analyticOnNhd hUo
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hx ?_
    exact heq.eventuallyEq_of_mem (ball_mem_nhds _ hr₀) |>.mono 𝒵 sub_eq_zero.mp hz
end

theorem UnitDisc.hasDerivAt_shift_comp {f : ℂ → UnitDisc} {z f'} (w : UnitDisc)
    (hf : HasDerivAt (𝓍 ↑(f x)) f' z) :
    HasDerivAt (𝓍 w.shift (f x) : 𝕋)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z := by
  simp only [coe_shift]
  convert (hf.const_add _).fun_div ((hf.const_mul _).const_add _) (𝖜 shift_den_ne_zero) using 1
  rw [← mul_conj']
  ring

section
variable {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
include hUo hUc hU
theorem exist_map_unitDisc_injOn_norm_deriv_gt {x} (hx : x ∈ U) {f}
    (hdf : 𝕮 (UnitDisc.coe ∘ f) U) (hf₀ : f x = 0) (hf_inj : InjOn f U)
    (hsurj : ¬SurjOn f U univ) (hdf₀ : deriv (UnitDisc.coe ∘ f) x ≠ 0) :
    ∃ g, g x = 0 ∧ InjOn g U ∧ 𝕮 (UnitDisc.coe ∘ g) U ∧
      ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ g) x‖ := by
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by simpa [SurjOn, eq_univ_iff_forall] using hsurj
  rcases UnitDisc.exists_continuousOn_pow_eq hUc hUo ((-c).continuous_shift.comp_continuousOn
    (UnitDisc.isEmbedding_coe.continuousOn_iff.2 hdf.continuousOn))
    (by simpa) 2 with ⟨g, hgc, hgf⟩
  have hg₀ : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    suffices g z ^ (2 : ℕ+) ≠ 0 by simpa using this
    simp_all
  have hdg : ∀ z ∈ U, HasDerivAt (g · : 𝕋)
      ((1 - 𝔫₂ ℭ) / (2 * g z * (1 - conj ↑c * f z) ^ 2) * deriv (f · : 𝕋) z) z := by
    intro z hz
    convert (hasDerivAt_pow 2 _).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (UnitDisc.hasDerivAt_shift_comp _ <| (hdf.hasDerivAt <| hUo.mem_nhds hz)) _
      (.of_forall 𝓍 congr(UnitDisc.coe $(hgf x))) using 1
    · rfl
    · simp [Function.comp_def, field]
      ring
    · simp_all
  refine ⟨(-g x).shift ∘ g, 𝔰, (-g x).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_,
    𝒵 (UnitDisc.hasDerivAt_shift_comp _ <| hdg z hz).differentiableAt.differentiableWithinAt, ?_⟩
  · simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  · have hkey : ‖deriv (UnitDisc.coe ∘ ⇑(-g x).shift ∘ g) x‖ =
        ‖deriv (f · : 𝕋) x‖ * (√‖ℭ‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgx : ‖(g x : ℂ)‖ = √‖ℭ‖ := by
        rw [← Real.sqrt_sq 𝔬, ← norm_pow, ← PNat.val_ofNat, ← UnitDisc.coe_pow, hgf]
        simp [hf₀, UnitDisc.coe_shift]
      simp only [Function.comp_def, (UnitDisc.hasDerivAt_shift_comp _ <| hdg x hx).deriv, norm_mul, norm_div,
        ← mul_assoc, conj_mul', UnitDisc.coe_neg, map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ := sub_pos.2 c.norm_lt_one
      have hpos₂ := sub_pos.2 c.sq_norm_lt_one
      simp [field, hgx, hf₀, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hdf₀
    · have hc₀ : 0 < ‖ℭ‖ := by simpa [hf₀] using (hc x hx).symm
      suffices √‖ℭ‖ * 2 < ‖ℭ‖ + 1 by simpa [field] using this
      have : √‖ℭ‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at this
      · linear_combination this
      · apply norm_nonneg

open scoped UniformConvergence in
theorem exists_bijOn_unitBall_map_eq_zero {x₀} (hx₀ : x₀ ∈ U) :
    ∃ f : 𝕋, 𝕮 f U ∧ BijOn f U ℑ ∧ f x₀ = 0 := by
  set 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  set F : (ℂ →ᵤ[𝔖] ℂ) → 𝕋 := fun f ↦ UniformOnFun.toFun _ f
  have hF {f : ℂ →ᵤ[𝔖] ℂ} {s} : TendstoLocallyUniformlyOn F 𝔚 (𝓝[s] f) U := by
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using (tendsto_id'.mpr nhdsWithin_le_nhds : Tendsto id (𝓝[s] f) (𝓝 f))
  set s : Set (ℂ →ᵤ[𝔖] ℂ) :=
    {f |
      MapsTo 𝔚 U ℑ ∧
      InjOn 𝔚 U ∧
      𝕮 𝔚 U ∧
      deriv 𝔚 x₀ ≠ 0 ∧
      F f x₀ = 0}
  have hsd : ∀ f ∈ s, 𝕮 𝔚 U := by aesop
  have hs_ne : s.Nonempty := by
    classical
    rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hU with ⟨f, hfU, hf_inj, hdf⟩
    let φ : ℂ → UnitDisc := 𝓏 if hz : z ∈ U then .mk (f z) (by simpa using hfU hz) else 0
    have hd : ∀ z ∈ U, HasDerivAt (𝓌 ((-φ x₀).shift 𝔘 : ℂ)) _ z := 𝒵
      UnitDisc.hasDerivAt_shift_comp _ ((differentiableAt_of_deriv_ne_zero <| hdf z hz).hasDerivAt.congr_of_eventuallyEq
        (by filter_upwards [hUo.mem_nhds hz] with w hw; simp [φ, hw]))
    refine ⟨UniformOnFun.ofFun 𝔖 𝓏 ((-φ x₀).shift 𝔙 : ℂ), fun z _ ↦ by simpa [F] using UnitDisc.norm_lt_one _,
      fun z hz w hw h ↦ hf_inj hz hw ?_, 𝒵 (hd z hz).differentiableAt.differentiableWithinAt,
      ?_, by simp [F]⟩
    · simpa [F, φ, hz, hw] using h
    · simp only [F, UniformOnFun.toFun_ofFun, (hd x₀ hx₀).deriv]
      exact mul_ne_zero (div_ne_zero (sub_ne_zero.2 <| mod_cast (UnitDisc.sq_norm_lt_one _).ne')
        (pow_ne_zero _ <| 𝖜 UnitDisc.shift_den_ne_zero)) (hdf x₀ hx₀)
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (𝒽 And.right) (s := s) (F := F)
    .id ?eqcont fun K hK x hx ↦ ⟨closedBall 0 1, 𝖜 isCompact_closedBall, fun i hi ↦
      ball_subset_closedBall <| hi.1 <| hK.1 hx⟩
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    rcases Metric.mem_nhds_iff.1 (hUo.mem_nhds <| hKU hz) with ⟨r, hr, hrU⟩
    refine (equicontinuousAt_of_continuity_modulus (fun y ↦ 2 / r * dist y z) ?_ _ ?_).equicontinuousWithinAt _
    · simpa using ((continuous_id.dist <| continuous_const (y := z)).const_mul <| 2 / r).tendsto z
    · filter_upwards [ball_mem_nhds z hr] with y hy i
      rw [dist_comm]
      refine dist_le_div_mul_dist_of_mapsTo_ball ((hsd _ i.2).mono hrU) (𝒲 ?_) hy
      have h1 := i.2.1 <| hrU hw
      have h2 := i.2.1 <| hKU hz
      simp at h1 h2 ⊢
      linarith [dist_le_norm_add_norm (F i w) <| F i z]
  have hcl : closure s ⊆
      {f | MapsTo 𝔚 U ℑ ∧
           ((∃ C, EqOn 𝔚 (Function.const ℂ C) U) ∨ InjOn 𝔚 U) ∧
           𝕮 𝔚 U ∧
           F f x₀ = 0} := by
    intro f hf
    rw [mem_closure_iff_nhdsWithin_neBot] at hf
    have hF := @hF f s
    have hdf := hF.differentiableOn
      (eventually_mem_nhdsWithin.mono hsd) hUo
    have hf_le (z) (hz : z ∈ U) : ‖F f z‖ ≤ 1 := le_of_tendsto (hF.tendsto_at hz).norm <|
      eventually_mem_nhdsWithin.mono fun g hg ↦ (by simpa using hg.1 hz : ‖F g z‖ < 1).le
    have hfx₀ := tendsto_nhds_unique (hF.tendsto_at hx₀) <|
      tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.2.2.2.symm
    refine ⟨?_, ?_, hdf, hfx₀⟩
    · by_contra hf_ball
      obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
      have : IsMaxOn (‖F f ·‖) U z := 𝒴 𝔤
      have : F f x₀ = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        hUc.isPathConnected.isConnected.isPreconnected hUo hdf hzU this hx₀
      norm_num [← this, hfx₀] at hz
    · exact eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo
        hUc.isPathConnected.isConnected.isPreconnected
        (eventually_mem_nhdsWithin.mono hsd) hF
        (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.1)
  have hcont : ContinuousOn (fun f ↦ ‖deriv 𝔚 x₀‖) (closure s) :=
    .mono (.norm fun f hf ↦ TendstoLocallyUniformlyOn.tendsto_at
      (.deriv hF (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.2.1) hUo) hx₀) hcl
  rcases hcmpct.exists_isMaxOn hs_ne.closure hcont with ⟨f₀, hf₀_mem, hf₀_max⟩
  have hdf₀_x₀ : 0 < ‖deriv (F f₀) x₀‖ := by
    rcases hs_ne with ⟨f', hf'⟩
    refine lt_of_lt_of_le ?_ (hf₀_max <| subset_closure hf')
    simpa using hf'.2.2.2.1
  rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hf₀_diff, hf₀_x₀⟩
  replace hf₀_inj := hf₀_inj.resolve_left fun ⟨C, hC⟩ ↦ by
    simp [hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq] at hdf₀_x₀
    aesop
  refine ⟨F f₀, hf₀_diff, ⟨hf₀_mapsTo, hf₀_inj, ?_⟩, hf₀_x₀⟩
  by_contra! hsurj
  clear hf₀_mem
  rw [isMaxOn_iff] at hf₀_max
  wlog hf₀_lt : ∀ z, ‖F f₀ z‖ < 1 generalizing f₀
  · classical
    have hd : deriv (U.indicator <| F f₀) x₀ = deriv (F f₀) x₀ :=
      U.eqOn_indicator.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq
    apply this (UniformOnFun.ofFun _ <| U.indicator <| F f₀)
    · simpa [hd, F] using hf₀_max
    · simpa [hd, F] using hdf₀_x₀
    · simpa [F, U.eqOn_indicator.mapsTo_iff]
    · simpa [F, differentiableOn_congr U.eqOn_indicator]
    · simp [F, hf₀_x₀]
    · simpa [F, U.eqOn_indicator.injOn_iff]
    · simpa [F, U.eqOn_indicator.surjOn_iff]
    · intro z
      by_cases hz : z ∈ U <;> simp [F, hz, mem_ball_zero_iff.mp <| hf₀_mapsTo _]
  lift F f₀ to ℂ → UnitDisc using hf₀_lt with f hf
  replace hsurj : ¬SurjOn f U univ := by
    simpa [SurjOn, subset_def, UnitDisc.exists, ← UnitDisc.coe_inj] using hsurj
  rcases exist_map_unitDisc_injOn_norm_deriv_gt hUo hUc hU hx₀ hf₀_diff 𝔞
    (by simpa [InjOn] using hf₀_inj) hsurj (by aesop) with ⟨g, hg₀, hg_inj, hdg, hg_lt⟩
  refine hf₀_max (UniformOnFun.ofFun _ (g · : 𝕋)) (subset_closure ?_) |>.not_gt hg_lt
  refine ⟨fun z _ ↦ (g z).2, by simpa [F, InjOn] using hg_inj, hdg, ?_, by aesop⟩
  rw [← norm_pos_iff]
  exact (𝔬).trans_lt hg_lt

end
end Complex
attribute [-instance] instCommCStarAlgebraComplex
namespace BergmanWeakType
variable {α r R M ε c x : ℝ} {f g φ : 𝕋} {z w a ζ : ℂ} {U Ω : Set ℂ} {K : ℂ → ℂ → ℂ} {μ : Measure ℂ} {v : 𝕦}
variable (hα : -1 < α) (hf : Integrable f 𝔴) (hz : z ∈ disk) (hw : w ∈ disk) (hK : IsBergmanKernel Ω K) (hΩ : MeasurableSet Ω) (hr : |r| < 1) (hR : 0 < R) (hε : 0 < ε) (hφ : 𝕮 φ disk) (hζ : ‖ζ‖ ≤ 1) (hv : CircleIntegrable v 0 R)
-- FILE BergmanWeakType.CompactGap
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # A uniform relative gap on a compact parameter set
This is the compactness ingredient for converting pointwise cancellation of an integral into
a uniform relative cancellation estimate. It does not establish that cancellation for a kernel.
-/

/-- A strict inequality between continuous nonnegative and positive functions on a nonempty
compact set has a uniform relative gap, with the gap lying in the interval `(0, 1]`. -/
theorem exists_uniform_relative_gap {X} [TopologicalSpace X] {s}
    {I J : 𝖃} (hs : IsCompact s) (hne : s.Nonempty)
    (hI : ContinuousOn I s) (hJ : ContinuousOn J s)
    (hI_nonneg : ∀ x ∈ s, 0 ≤ I x) (hJ_pos : ∀ x ∈ s, 0 < J x)
    (hlt : ∀ x ∈ s, I x < J x) :
    𝔈ₙ ∀ x ∈ s, I x ≤ (1 - η) * J x := by
  obtain ⟨a, ha, hmax⟩ := hs.exists_isMaxOn hne <| hI.div hJ 𝒳 (hJ_pos x hx).ne'
  refine ⟨1 - I a / J a, sub_pos.2 <| (div_lt_one (hJ_pos a ha)).2 (hlt a ha),
    by linarith [div_nonneg (hI_nonneg a ha) (hJ_pos a ha).le], 𝒳 ?_⟩
  simpa using (div_le_iff₀ <| hJ_pos x hx).1 <| hmax hx


-- FILE BergmanWeakType.Kernel
/-! # Elementary identities for the Bergman kernels
These lemmas establish the kernels' normalizations and the pointwise comparison of the complex
projection with its positive majorant. They do not assert a sharp weak type estimate.
-/

@[simp]
theorem mem_disk_iff : z ∈ disk ↔ 𝕫 < 1 := by
  simp [disk]

section
include hz hw
theorem kernel_norm_lt_one : ‖z * star w‖ < 1 := by
  simp_all
  nlinarith [norm_nonneg z]

theorem kernel_denominator_ne_zero :
    𝖟 ≠ 0 := 𝒷
  (kernel_norm_lt_one hz hw).ne (by rw [← sub_eq_zero.1 h, norm_one])

/-- The kernel's base lies in the right half-plane on the disk. -/
theorem kernel_denominator_re_pos :
    0 < (𝖟).re := by
  simpa using (Complex.re_le_norm _).trans_lt <| kernel_norm_lt_one hz hw

end
/-- The weighted pointwise comparison requires no weak type estimate. -/
theorem enorm_weightedProjection_le_weightedPositiveProjection
    (z) : ‖𝖕 weightedProjection‖ₑ ≤ 𝖕 weightedPositiveProjection := by
  simpa [weightedProjection, weightedPositiveProjection] using
    enorm_integral_le_lintegral_enorm (𝕜 * f)

@[simp]
theorem norm_weightedKernel :
    𝔨ᵥ = ‖𝖟‖ ^ 𝔪 := by
  simpa [weightedKernel] using Complex.norm_cpow_real 𝖟 𝔪

@[simp]
theorem weightedKernel_zero (z w) : weightedKernel 0 z w = kernel z w := by
  simp [weightedKernel, kernel, Complex.cpow_neg]

@[simp]
theorem weightedArea_zero : weightedArea 0 = diskArea := by
  simp [weightedArea]

include hα in
theorem gammaConstant_pos : 0 < 𝔤ᵧ :=
  div_pos (Real.Gamma_pos_of_pos 𝔩) (sq_pos_of_pos <| Real.Gamma_pos_of_pos 𝔩)


-- FILE BergmanWeakType.Measure
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Normalization and support of Bergman area measures -/

theorem area_ball (c) (r) : area (Metric.ball c r) = ENNReal.ofReal r ^ 2 ∧
    area (Metric.closedBall c r) = ENNReal.ofReal r ^ 2 := by
  have h : ENNReal.ofReal Real.pi⁻¹ * NNReal.pi = 1 := by
    rw [ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal,
      ENNReal.inv_mul_cancel (by simp [NNReal.pi_ne_zero]) ENNReal.coe_ne_top]
  simp only [area, Measure.smul_apply, smul_eq_mul, Complex.volume_ball, Complex.volume_closedBall,
    mul_left_comm _ (ENNReal.ofReal r ^ 2), h, mul_one, and_self]

theorem area_disk : area disk = 1 := by
  simpa [disk] using (area_ball 0 1).1

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea where
  measure_univ := by simpa [diskArea] using area_disk

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk :=
  ae_restrict_mem Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weightedArea : ∀ᵐ z ∂𝔴, z ∈ disk :=
  (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- Under normalized disk area, the squared radius is uniform on the unit interval. -/
theorem map_norm_sq_diskArea :
    diskArea.map 𝔳 = volume.restrict (Icc 𝟘 1) := by
  refine Measure.ext_of_Iic _ _ fun t ↦ ?_
  rw [Measure.map_apply 𝔣 measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
    inter_comm, ← Ici_inter_Iic, inter_assoc, Iic_inter_Iic, Ici_inter_Iic, Real.volume_Icc,
    sub_zero, diskArea, Measure.restrict_apply (measurableSet_Iic.preimage 𝔣)]
  rcases lt_or_ge t 0 with ht | ht
  · rw [ENNReal.ofReal_of_nonpos 𝔤, ← measure_empty (μ := area)]
    congr
    ext z
    simp
    intro h
    nlinarith
  have hpre : 𝔳 ⁻¹' Iic t = Metric.closedBall 0 (Real.sqrt t) := by
    ext z
    simp [Real.le_sqrt 𝔬 ht]
  rw [hpre]
  rcases lt_or_ge t 1 with ht1 | ht1
  · rw [inter_eq_left.2 𝒵 ?_, (area_ball 0 _).2, inf_of_le_right ht1.le,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg t), Real.sq_sqrt ht]
    simp at hz ⊢
    nlinarith [Real.sq_sqrt ht]
  · rw [inter_eq_right.2 𝒵 ?_, inf_of_le_left ht1, area_disk, ENNReal.ofReal_one]
    simp at hz ⊢
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]

section
include hα
theorem lintegral_weight_Ioc {a} (ha : a ≤ 1) :
    ∫⁻ u in Ioc a 1, ENNReal.ofReal (α₁ * 𝖔) =
      ENNReal.ofReal ((1 - a) ^ α₁) := by
  have hpos : 0 < α₁ := 𝔩
  have hf : IntervalIntegrable (𝓊 𝖔) volume a 1 := by
    have := ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 - a)
      hα).comp_sub_left 1).symm
    simp_all
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.const_mul α₁).1
      ((ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦
        mul_nonneg hpos.le (Real.rpow_nonneg (sub_nonneg.2 hu.2) _)),
    ← intervalIntegral.integral_of_le ha, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (𝓍 x ^ α) 1, sub_self,
    integral_rpow (Or.inl hα), Real.zero_rpow hpos.ne', sub_zero, mul_div_cancel₀ _ hpos.ne']

theorem weightedArea_isProbabilityMeasure :
    IsProbabilityMeasure 𝔴 := by
  constructor
  rw [weightedArea, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← lintegral_map (f := 𝓊 ENNReal.ofReal <| α₁ * 𝖔) 𝔣
      𝔣, map_norm_sq_diskArea, ← Measure.restrict_congr_set Ioc_ae_eq_Icc,
    lintegral_weight_Ioc hα zero_le_one]
  simp

/-- The admissible radial weights have the same null sets as disk area. -/
theorem diskArea_absolutelyContinuous_weightedArea :
    diskArea ≪ 𝔴 :=
  withDensity_absolutelyContinuous' 𝔣 (ae_mem_disk.mono 𝒵
    (ENNReal.ofReal_pos.2 <| mul_pos 𝔩 (Real.rpow_pos_of_pos
      𝔞 _)).ne')


end
-- FILE BergmanWeakType.KernelIntegrability
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Integrability of the Bergman integral formulas
For each interior output point, both kernel columns are bounded on the input disk. Consequently
their products with integrable inputs are integrable. The Bochner integrals defining the complex
projections therefore represent genuine integrable functions, and the positive outputs are finite.
-/

theorem measurableSet_disk : MeasurableSet disk := Metric.isOpen_ball.measurableSet

include hw in
/-- A fixed interior output point keeps the kernel denominator uniformly away from zero. -/
theorem kernel_denominator_norm_lower :
    1 - 𝕫 ≤ ‖𝖟‖ := by
  have := norm_sub_norm_le (1) <| z * star w
  rw [norm_mul, norm_star, norm_one] at this
  nlinarith [mem_disk_iff.1 hw, norm_nonneg z]

include hα hz hw in
theorem norm_weightedKernel_le 
    :
    𝔨ᵥ ≤ (1 - 𝕫) ^ 𝔪 := by
  rw [norm_weightedKernel]
  exact Real.rpow_le_rpow_of_nonpos 𝔞
    (kernel_denominator_norm_lower hw) 𝔩

include hz in
/-- The principal-power kernel is continuous throughout the input disk. -/
theorem continuousOn_weightedKernel :
    ContinuousOn 𝕜 disk :=
  (continuous_const.sub <| continuous_const.mul continuous_star).continuousOn.cpow_const
    𝒲 Or.inl (kernel_denominator_re_pos hz hw)

section
include hα hf hz
/-- Every admissible input gives an integrable weighted kernel integrand at an interior point. -/
theorem integrable_weightedKernel_mul 
    :
    Integrable (𝓌 𝕜 w * 𝕱) 𝔴 :=
  hf.bdd_mul (((continuousOn_weightedKernel hz).aestronglyMeasurable
    measurableSet_disk).mono_ac (withDensity_absolutelyContinuous diskArea _))
    (ae_mem_disk_weightedArea.mono 𝒲 norm_weightedKernel_le hα hz hw)

theorem weightedPositiveProjection_lt_top 
    :
    𝖕 weightedPositiveProjection < ∞ := by
  simpa only [weightedPositiveProjection, enorm_mul, ofReal_norm] using
    (hasFiniteIntegral_iff_enorm.mp
      (integrable_weightedKernel_mul hα hf hz).hasFiniteIntegral)


end
-- FILE BergmanWeakType.Rigidity.AnalyticInverse
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

/-- A set-theoretic inverse of a holomorphic bijection between open complex sets is holomorphic.
Continuity follows from the open mapping theorem; isolated possible critical points are removable
singularities of the inverse. -/
theorem differentiableOn_inverse {V} 
    (hU : IsOpen U) (hV : IsOpen V) (hf : 𝕮 f U)
    (hinv : InvOn g f U V) (hgmap : MapsTo g V U) : 𝕮 g V := by
  have hnc {x} (hx : x ∈ U) : ¬ ∀ᶠ z in 𝓝 x, f z = f x := 𝒷 by
    obtain ⟨z, ⟨hz, hzU⟩, hne⟩ := (((h.and <| hU.eventually_mem hx).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists (f := 𝓝[≠] x)
    exact hne <| hinv.1.injOn hzU hx hz
  have hcont {y} (hy : y ∈ V) : ContinuousAt g y := by
    have hx := hgmap hy
    rw [← hinv.2 hy, ContinuousAt, hinv.1 hx]
    exact (tendsto_map'_iff.2 <| tendsto_id.congr' ((hU.eventually_mem hx).mono 𝒵
      (hinv.1 hz).symm)).mono_left ((hf.analyticAt (hU.mem_nhds hx)
        ).eventually_constant_or_nhds_le_map_nhds.resolve_left (hnc hx))
  intro y hy
  have hcrit := ((hf.analyticOnNhd hU).deriv _ (hgmap hy)
    ).eventually_eq_zero_or_eventually_ne_zero.resolve_left 𝒷 hnc (hgmap hy) (by
      obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_ball.mem_iff.mp <| h.and (hU.eventually_mem (hgmap hy))
      filter_upwards [ball_mem_nhds _ hr] with z hz
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ r).isPreconnected
        (hf.mono 𝒵 (hrU hz).2) (𝒵 (hrU hz).1) hz (mem_ball_self hr))
  rw [eventually_nhdsWithin_iff] at hcrit
  refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    (hcont hy)).differentiableAt.differentiableWithinAt
  filter_upwards [((hcont hy).tendsto.eventually hcrit).filter_mono nhdsWithin_le_nhds,
    (hV.eventually_mem hy).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzV hzneq
  exact ((hf.differentiableAt <| hU.mem_nhds (hgmap hzV)).hasDerivAt.of_local_left_inverse
    (hcont hzV) (hz fun heq ↦ hzneq <| by rw [← hinv.2 hzV, heq, hinv.2 hy]; exact rfl)
      ((hV.eventually_mem hzV).mono @hinv.2)).differentiableAt

/-- Every proper simply connected open complex domain admits mutually inverse holomorphic maps
to and from the unit disk, with nowhere-vanishing derivatives. -/
theorem exists_biholomorphic_unitBall (hU : IsOpen U)
    (hconn : IsSimplyConnected U) (hproper : U ≠ univ) :
    ∃ φ ψ : 𝕋,
      𝕮 φ ℑ ∧ 𝕮 ψ U ∧
      BijOn φ ℑ U ∧ InvOn ψ φ ℑ U ∧
      ∀ z ∈ ball 0 1, 𝕯 z ≠ 0 := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨ψ, hψ, hbij, _⟩ := Complex.exists_bijOn_unitBall_map_eq_zero hU hconn hproper hx
  have hinv := hbij.invOn_invFunOn
  have hφ := differentiableOn_inverse hU isOpen_ball hψ hinv <| hinv.1.mapsTo hbij.surjOn
  exact ⟨_, ψ, hφ, hψ, hbij.symm hinv.symm, hinv.symm, 𝒵 right_ne_zero_of_mul_eq_one <|
    (((hψ.differentiableAt <| hU.mem_nhds (hinv.1.mapsTo hbij.surjOn hz)).hasDerivAt.comp z
    (hφ.differentiableAt <| isOpen_ball.mem_nhds hz).hasDerivAt).congr_of_eventuallyEq
    ((isOpen_ball.eventually_mem hz).mono 𝒲 (hinv.2 hw).symm)).unique (hasDerivAt_id z)⟩


-- FILE BergmanWeakType.Rigidity.ChangeOfVariables
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
section
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

/-- A complex derivative scales real area by its squared norm. -/
theorem det_complex_derivative (c) :
    |((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det| = 𝔫₂ c := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

variable (hU : IsOpen U) (hφ_ : 𝕮 φ U) (hinj : InjOn φ U)
include hU hφ_ hinj

theorem hasFDerivWithinAt_of_differentiableOn (w) (hw : w ∈ U) :
    HasFDerivWithinAt φ ((ContinuousLinearMap.toSpanSingleton ℂ 𝕕).restrictScalars ℝ)
      U w :=
  ((hφ_.differentiableAt <| hU.mem_nhds hw).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

/-- The normalized-area version of holomorphic change of variables for nonnegative integrals. -/
theorem area_lintegral_image_eq (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in φ '' U, g z ∂area =
      ∫⁻ w in U, ENNReal.ofReal (𝔫₂ 𝕕) * g 𝔘 ∂area := by
  simp only [area, Measure.restrict_smul, lintegral_smul_measure,
    𝔣ᵥ lintegral_image_eq_lintegral_abs_det_fderiv_mul, det_complex_derivative]

/-- The normalized-area version of holomorphic change of variables for complex integrals. -/
theorem area_integral_image_eq (g : 𝖊) :
    ∫ z in φ '' U, g z ∂area = ∫ w in U, 𝔡 • g 𝔘 ∂area := by
  simp only [area, Measure.restrict_smul, integral_smul_measure,
    𝔣ᵥ integral_image_eq_integral_abs_det_fderiv_smul, det_complex_derivative]

/-- Normalizing area preserves the integrability equivalence in holomorphic substitution. -/
theorem area_integrableOn_image_iff_norm_deriv_sq (g : 𝖊) :
    IntegrableOn g (φ '' U) area ↔
      IntegrableOn (𝓌 𝔡 • g 𝔘) U area := by
  simp only [IntegrableOn, area, Measure.restrict_smul]
  rw [integrable_smul_measure 𝔭 ENNReal.ofReal_ne_top,
    integrable_smul_measure 𝔭 ENNReal.ofReal_ne_top]
  simpa only [IntegrableOn, det_complex_derivative] using
    𝔣ᵥ integrableOn_image_iff_integrableOn_abs_det_fderiv_smul

end

-- FILE BergmanWeakType.Rigidity.IntegralPhase
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

instance area_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts area :=
  IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top

instance area_isOpenPosMeasure : Measure.IsOpenPosMeasure area :=
  Measure.isOpenPosMeasure_smul volume 𝔭


-- FILE BergmanWeakType.Rigidity.PhaseRigidity
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

include hζ in
theorem kernel_denominator_ne_zero_closed_left (hw : w ∈ disk) :
    1 - ζ * star w ≠ 0 := 𝒷 by
  have := congr_arg norm <| sub_eq_zero.1 h
  rw [norm_one, norm_mul, norm_star] at this
  nlinarith [mem_disk_iff.1 hw, norm_nonneg w]

include hζ in
/-- Equality in the compact-core triangle inequality forces the Möbius derivative form. -/
theorem derivative_form_of_core_triangle_eq {q}
    (hq : 𝕮 q disk)
    (hr : 0 < r) (hr1 : r < 1)
    (hI : (𝔍ᵦ q w * 𝕂) ≠ 0)
    (heq : ‖𝔍ᵦ q w * 𝕂‖ =
      𝔍ᵦ ‖q w * 𝕂‖) :
    ∀ w ∈ disk, q w * 𝖙 = q 0 := by
  set c := 𝔍ᵦ q w * 𝕂
  have hsub : closedBall 𝟎 r ⊆ disk := fun _ hw ↦ lt_of_le_of_lt hw hr1
  have hB : ContinuousOn (𝓌 𝔮ₖ / c) (closedBall 0 r) :=
    ((hq.continuousOn.mono hsub).mul <| ((continuousOn_const.sub (continuousOn_const.mul
      continuousOn_id.star)).inv₀ 𝒲 kernel_denominator_ne_zero_closed_left hζ
        (hsub hw)).pow 2).div_const c
  have hg : Integrable (𝓌 𝔮ₖ / c) (area.restrict <| 𝕓) :=
    (hB.integrableOn_compact <| isCompact_closedBall 0 r).mono_set ball_subset_closedBall
  replace hB := hB.mono ball_subset_closedBall
  have hre := Measure.eqOn_open_of_ae_eq ((integral_eq_iff_of_ae_le hg.re hg.norm
    (.of_forall 𝓏 Complex.re_le_norm _)).1 (by
      simp_rw [norm_div]
      rw [integral_re hg, integral_div, integral_div, div_self hI, ← heq,
        div_self (norm_ne_zero_iff.mpr hI)]
      rfl)) isOpen_ball (Complex.continuous_re.comp_continuousOn hB) hB.norm
  let G w := q w * 𝖙 / c
  have hGd : 𝕮 G disk := by fun_prop
  have him (w) (hw : w ∈ ball 𝟎 r) : (G w).im = 0 := by
    have hd := kernel_denominator_ne_zero_closed_left hζ <| hsub (ball_subset_closedBall hw)
    rw [show G w = 𝔮ₖ / c * ((‖1 - ζ * star w‖ ^ 2) ^ 2 : ℝ) by
        push_cast; rw [← Complex.conj_mul']; simp only [G, kernel] at hd ⊢
        field_simp; simp, Complex.im_mul_ofReal,
      Complex.abs_re_eq_norm.1 (by have : (𝔮ₖ / c).re = _ := hre hw; rw [this, abs_norm]), zero_mul]
  obtain ⟨d, hd⟩ := (hGd.analyticOnNhd isOpen_ball).mono (ball_subset_closedBall.trans hsub)
    |>.eq_const_of_im_eq_const him isOpen_ball
      ⟨⟨0, mem_ball_self hr⟩, (convex_ball 0 r).isPreconnected⟩
  have hall : EqOn G (𝒽 d) disk :=
    (hGd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball 𝟎 1).isPreconnected 𝔰
      ((isOpen_ball.eventually_mem <| mem_ball_self hr).mono hd)
  intro w hw
  simpa [G, hI] using (hall hw).trans (hall <| mem_ball_self one_pos).symm


-- FILE BergmanWeakType.Rigidity.MobiusGeometry
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

theorem image_affine_disk {b} (hb : b ≠ 0) :
    (𝓌 a + b * w) '' disk = ball a ‖b‖ := by
  simpa [disk, ← image_smul, ← image_vadd, image_image] using
    congr_arg (a +ᵥ ·) (smul_ball hb 𝟎 1)

open Complex UnitDisc in
include hφ hζ in
/-- In the bounded case the equality derivative can only parametrize a Euclidean disk. -/
theorem image_is_disk_of_derivative_form 
    (hφ0 : 𝕯 0 ≠ 0)
    (hbounded : Bornology.IsBounded (φ '' disk))
    (hderiv : ∀ w ∈ disk, 𝕕 * 𝖙 = 𝕯 0) :
    ∃ c, ∃ R, 0 < R ∧ φ '' disk = ball c R := by
  simp only [Complex.star_def] at hderiv
  set H := 𝓌 φ 0 + 𝕯 0 * w / (1 - conj ζ * w)
  have hn (w) (hw : w ∈ disk) : 1 - conj ζ * w ≠ 0 := 𝔤
  have hH (w) (hw : w ∈ disk) : HasDerivAt H (𝕯 0 / (1 - conj ζ * w) ^ 2) w := by
    convert (((hasDerivAt_id w).const_mul <| 𝕯 0).div
      (((hasDerivAt_id w).const_mul <| conj ζ).const_sub 1) (hn w hw)).const_add (φ 0) using 1
    · rfl
    grind
  have heq : φ '' disk = H '' disk := image_congr <| isOpen_ball.eqOn_of_deriv_eq
    (convex_ball 0 1).isPreconnected hφ (𝒲 (hH w hw).differentiableAt.differentiableWithinAt)
    (𝒲 (hH w hw).deriv ▸ (eq_div_iff (pow_ne_zero 2 (hn w hw))).2 (hderiv w hw))
    (x := 0) 𝔰 (by ring)
  have hζlt := hζ.lt_of_ne 𝒷 by
    obtain ⟨M, hM0, hM⟩ := (heq ▸ hbounded).exists_pos_norm_le
    obtain ⟨N, hN, hNd⟩ : ∃ N, 0 < N ∧ ‖𝕯 0‖ * N = M + ‖φ 0‖ + 1 :=
      ⟨_, div_pos 𝔭 <| norm_pos_iff.2 hφ0, mul_div_cancel₀ _ <| norm_ne_zero_iff.2 hφ0⟩
    have hb := hM _ ⟨(N / (N + 1) : ℝ) * ζ, by
      simp only [mem_disk_iff, norm_mul, norm_real, h]
      rw [Real.norm_of_nonneg 𝔭, mul_one, div_lt_one] <;> linarith, rfl⟩
    have e : H (↑(N / (N + 1)) * ζ) = 𝕯 0 * N * ζ - -φ 0 := by
      simp only [H]
      rw [mul_left_comm <| conj ζ, conj_mul', h]
      push_cast
      field_simp [show (N : ℂ) + 1 ≠ 0 from mod_cast 𝔭]
      ring
    have := norm_sub_norm_le (𝕯 0 * N * ζ) <| -φ 0
    simp only [e, norm_neg, norm_mul, norm_real, h, Real.norm_of_nonneg hN.le] at this hb
    linarith
  have hd : 0 < 1 - 𝔫₂ ζ := 𝔞
  have hb := div_ne_zero hφ0 <| ofReal_ne_zero.2 hd.ne'
  refine ⟨φ 0 + 𝕯 0 * ζ / (1 - 𝔫₂ ζ : ℝ), _, norm_pos_iff.2 hb, heq.trans ?_⟩
  rw [← image_affine_disk hb, ← show range ((↑) : 𝔻 → ℂ) = disk from Subtype.range_val,
    ← range_comp, ← range_comp, ← (shift <| mk ζ hζlt).surjective.range_comp]
  congr 1
  ext W
  have h1 := shift_den_ne_zero (mk ζ hζlt) W
  have := mul_comm (W : ℂ) (conj ζ) ▸ h1
  simp only [Function.comp, H, coe_shift, coe_mk] at h1 ⊢
  rw [show 1 - conj ζ * ((ζ + W) / (1 + conj ζ * W)) = ((1 - 𝔫₂ ζ : ℝ) : ℂ) / (1 + conj ζ * W)
    by field_simp; push_cast; rw [← conj_mul']; ring]
  field_simp
  ring


-- FILE BergmanWeakType.Rigidity.CoreGap
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

include hφ in
/-- Every bounded nondisk conformal image has a uniform cancellation gap on each fixed inner
disk, including all parameters on the closed unit disk. -/
theorem exists_core_relative_gap
    (hne : ∀ w ∈ disk, 𝕕 ≠ 0) (hbdd : Bornology.IsBounded (φ '' disk))
    (hnd : ¬∃ c, ∃ R, 0 < R ∧ φ '' disk = ball c R)
    (hr : 0 < r) (hr1 : r < 1) :
    𝔈ₙ ∀ ζ ∈ closedBall 𝟎 1,
      ‖𝔍ᵦ 𝕕 * 𝕂‖ ≤
        (1 - η) * 𝔍ᵦ ‖𝕕 * 𝕂‖ := by
  have hq : 𝕮 𝕯 disk :=
    (hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hsub {p} (hp : p ∈ closedBall 𝟎 1 ×ˢ closedBall 0 r) : p.2 ∈ disk :=
    lt_of_le_of_lt hp.2 hr1
  have hF : ContinuousOn (fun p ↦ 𝕯 p.2 * kernel p.1 p.2)
      (closedBall 0 1 ×ˢ closedBall 0 r) :=
    (hq.continuousOn.comp continuous_snd.continuousOn @hsub).mul
      (((continuousOn_const.sub <| continuous_fst.continuousOn.mul
        continuous_snd.star.continuousOn).inv₀ 𝒫
          kernel_denominator_ne_zero_closed_left 𝔞 (hsub hp)).pow 2)
  have hz {ζ} (hζ : ζ ∈ closedBall 𝟎 1) :
      ContinuousOn (𝓌 𝕕 * 𝕂) (closedBall 0 r) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn 𝒲 ⟨hζ, hw⟩
  have hc {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {G : ℂ → 𝖊}
      (hG : ContinuousOn (fun p ↦ G p.1 p.2) (closedBall 0 1 ×ˢ closedBall 0 r)) :
      ContinuousOn (𝓏 𝔍ᵦ G z w) (closedBall 0 1) := by
    obtain ⟨M, hM⟩ := ((𝖜 isCompact_closedBall).prod <| 𝖜 isCompact_closedBall).bddAbove_image
      hG.norm
    refine continuousOn_of_dominated (𝒵 ?_) (𝒵
      ae_restrict_of_forall_mem measurableSet_ball 𝒲 hM (mem_image_of_mem _
        (show (z, w) ∈ _ ×ˢ _ from ⟨hz, ball_subset_closedBall hw⟩))) integrableOn_const
      (ae_restrict_of_forall_mem measurableSet_ball 𝒲 hG.comp
        (continuous_id.prodMk continuous_const).continuousOn 𝒵
          ⟨hz, ball_subset_closedBall hw⟩)
    exact ((hG.comp (continuous_const.prodMk continuous_id).continuousOn 𝒲
      ⟨hz, hw⟩).mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hpos {ζ} (hζ : ζ ∈ closedBall 𝟎 1) :
      0 < 𝔍ᵦ ‖𝕕 * 𝕂‖ := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae (.of_forall 𝒽 norm_nonneg _)
      (((hz hζ).integrableOn_compact <| isCompact_closedBall 0 r).mono_set
        ball_subset_closedBall).norm).2 ?_
    exact (measure_ball_pos area 0 hr).trans_le <| measure_mono 𝒲 ⟨norm_ne_zero_iff.2
      (mul_ne_zero (hne w (lt_trans hw hr1)) (pow_ne_zero 2 (inv_ne_zero
        (kernel_denominator_ne_zero_closed_left 𝔞 (lt_trans hw hr1))))), hw⟩
  refine exists_uniform_relative_gap (isCompact_closedBall 𝟎 1) ⟨0, 𝔰⟩ (hc hF).norm
    (hc hF.norm) (𝒰 norm_nonneg _) @hpos fun ζ hζ ↦
      (norm_integral_le_integral_norm _).lt_of_ne fun heq ↦ hnd ?_
  have hζ' : ‖ζ‖ ≤ 1 := 𝔞
  exact image_is_disk_of_derivative_form hφ hζ' 𝔞 hbdd
    (derivative_form_of_core_triangle_eq hζ' hq hr hr1 (norm_pos_iff.1 <| heq ▸ hpos hζ) heq)


-- FILE BergmanWeakType.Rigidity.PolarIntegral
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Integration on the disk in polar coordinates -/


/-- Disk integration is twice the radius-weighted integral of circular means. -/
theorem integral_diskArea_eq_circleAverage {f : 𝖊}
    (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ r in I₁, 𝔏 • Real.circleAverage f 0 r := by
  have hD : MeasurableSet disk := isOpen_ball.measurableSet
  have hfi := (integrable_indicator_iff hD).2
    ((integrable_smul_measure (by simp [Real.pi_pos] : ENNReal.ofReal π⁻¹ ≠ 0)
      ENNReal.ofReal_ne_top).1 (by simpa only [diskArea, area, Measure.restrict_smul] using hf))
  have hs := Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hfi
    |>.integrableOn (s := polarCoord.source)
  rw [← polarCoord.symm_image_target_eq_source] at hs
  have hp := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn _).1 hs
  rw [diskArea, area, Measure.restrict_smul, integral_smul_measure, ← integral_indicator hD,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    setIntegral_prod _ (hp.congr ?_), ← Ioi_inter_Iio (a := 𝟘),
    ← setIntegral_indicator measurableSet_Iio, ← integral_smul]
  · refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    simp only [indicator, mem_Iio, disk, mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
      abs_of_pos hr]
    split_ifs
    · rw [Real.circleAverage_eq_integral_add <| -π, intervalIntegral.integral_comp_add_right
        (𝓉 f <| 𝔠ₘ θ), intervalIntegral.integral_of_le <| by linarith [Real.pi_pos],
        integral_Ioc_eq_integral_Ioo, zero_add, show 2 * π + -π = π by ring, smul_smul,
        ← integral_smul, ← integral_smul]
      refine setIntegral_congr_fun measurableSet_Ioo 𝒯 ?_
      rw [smul_smul]
      congr 1
      · simp [Real.pi_pos.le]
        field_simp
      · simp [circleMap, Complex.exp_mul_I]
    · simp
  · filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    simp only [det_fderivPolarCoordSymm, Function.comp_apply,
      Complex.measurableEquivRealProd_symm_polarCoord_symm_apply, abs_of_pos hp.1]

/-- The complementary squared radius is also uniform. -/
theorem integral_diskArea_eq_circleAverage_sqrt_one_sub {f : 𝖊}
    (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea =
      𝔍ᵧ Real.circleAverage f 0 (Real.sqrt (1 - y)) := by
  rw [intervalIntegral.integral_comp_sub_left (fun y ↦ Real.circleAverage f 0 <| Real.sqrt y) 1, integral_diskArea_eq_circleAverage hf, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  have := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := 1)
    (f := fun r ↦ 𝕣) (f' := fun r ↦ 𝔏) (g := fun y ↦ Real.circleAverage f 0 <| Real.sqrt y)
    𝔣 (fun x _ ↦ by simpa using hasDerivAt_pow 2 x)
    𝒳 𝔤
  simpa [Real.sqrt_sq_eq_abs] using this


-- FILE BergmanWeakType.Rigidity.DiskReproducing
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

open Complex in
/-- The explicit unit-disk kernel satisfies the standard Bergman-kernel characterization. -/
theorem isBergmanKernel_disk : IsBergmanKernel disk kernel where
  holomorphic w hw := by
    unfold kernel
    fun_prop (disch := exact 𝒵 kernel_denominator_ne_zero hz hw)
  hermitian z _ w _ := by simp [kernel, star_mul]
  squareIntegrable z hz := by
    simpa [diskArea, funext <| weightedKernel_zero z] using MemLp.of_bound (μ := diskArea) ((continuousOn_weightedKernel (α := 0) hz).aestronglyMeasurable
      measurableSet_disk) _ (ae_mem_disk.mono 𝒲 norm_weightedKernel_le 𝔫 hz hw)
  reproduces f hf hfi z hz := by
    change ∫ w, kernel z w * 𝕱 ∂diskArea = f z
    have hmap : MapsTo (fun r : ℝ ↦ 𝔷ᵣ) ℌ disk := 𝓡 by
      simp
      exact (mul_le_of_le_one_left 𝔬 <| pow_le_one₀ hr.1 hr.2).trans_lt
        (mem_disk_iff.mp hz)
    set g := fun r : ℝ ↦ 𝔏 • (f 𝔷ᵣ + 𝔷ᵣ * deriv f 𝔷ᵣ)
    have hcont : ContinuousOn g ℌ := by
      have := hf.continuousOn
      have := (hf.analyticOnNhd isOpen_ball).deriv.continuousOn
      fun_prop
    have : Integrable (𝓌 kernel z w * 𝕱) diskArea := by
      simpa using integrable_weightedKernel_mul (α := 0) 𝔫 (by simpa using MemLp.integrable (μ := diskArea) one_le_two hfi) hz
    rw [integral_diskArea_eq_circleAverage this]
    calc
      _ = ∫ r in I₁, g r := setIntegral_congr_fun measurableSet_Ioo fun r ⟨hr, hr1⟩ ↦ by
        congr 1
        set a : ℂ := 𝔷ᵣ
        have ha : a ∈ 𝕓 := by
          simp only [a, mem_ball, dist_zero_right, norm_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hr]
          nlinarith [mem_disk_iff.mp hz]
        have hsub : closedBall 𝟎 r ⊆ disk := 𝒲 lt_of_le_of_lt hw hr1
        rw [circleAverage_eq_circleIntegral hr.ne', circleIntegral.integral_congr hr.le
          𝒲 ?_,
          Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable isOpen_ball hsub
          (f := 𝓌 w * 𝕱) 𝔣 ha, ((hasDerivAt_id' a).fun_mul (hf.differentiableAt
          (isOpen_ball.mem_nhds <| hsub (ball_subset_closedBall ha))).hasDerivAt).deriv]
        · simp
        have hw0 : w ≠ 0 := by aesop
        have : w * conj w = ℛ ^ 2 := by
          rw [mul_conj, normSq_eq_norm_sq, mem_sphere_zero_iff_norm.1 hw]; norm_cast
        have : 1 - z * conj w = (w - a) / w := 𝔤
        simp only [sub_zero, smul_eq_mul, kernel, ← starRingEnd_apply, this]
        field_simp
      _ = f z := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s ↦ s ^ 2 * f (s ^ 2 * z))
          (𝓡 ?_) (hcont.intervalIntegrable_of_Icc zero_le_one)]
        · simp
        rw [uIcc_of_le zero_le_one] at hr
        have hpow := (hasDerivAt_id ℛ).pow 2
        convert (hpow.mul <| (hf.differentiableAt (isOpen_ball.mem_nhds (hmap hr))).hasDerivAt.comp
          ℛ (hpow.mul_const z)).comp_ofReal using 1
        · rfl
        simp [g]
        ring


-- FILE BergmanWeakType.Rigidity.KernelTransform
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

include hK hΩ in
/-- Both sections of a Hermitian Bergman kernel are square integrable. -/
theorem IsBergmanKernel.column_memLp 
    (hz : z ∈ Ω) :
    MemLp (𝓌 K w z) 2 𝔇 :=
  (memLp_congr_ae <| by filter_upwards [ae_restrict_mem hΩ] with w hw using
    (hK.hermitian w hw z hz).symm).mp (hK.squareIntegrable z hz).star

include hK hΩ in
/-- The standard reproducing and Hermitian properties uniquely determine a Bergman kernel. -/
theorem IsBergmanKernel.unique {L}
    (hL : IsBergmanKernel Ω L)
    (hz : z ∈ Ω) (hw : w ∈ Ω) : K z w = L z w := by
  rw [← (hL.reproduces _ (hK.holomorphic w hw) (hK.column_memLp hΩ hw) z hz), hL.hermitian z hz w hw, ← (hK.reproduces _ (hL.holomorphic z hz) (hL.column_memLp hΩ hz) w hw), ← starRingEnd_apply, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hΩ] with u hu
  simp [hK.hermitian u hu w hw, hL.hermitian z hz u hu, mul_comm]

/-- The holomorphic pullback, including one complex derivative, preserves square integrability. -/
theorem memLp_pullback_deriv {V} 
    (hU : IsOpen U) (hφ : 𝕮 φ U) (hbij : BijOn φ U V)
    (hf : ContinuousOn f V) (hfi : MemLp f 2 (area.restrict V)) :
    MemLp (𝓌 𝕕 * f 𝔘) 2 (area.restrict U) := by
  refine (memLp_two_iff_integrable_sq_norm <| ((hφ.analyticOnNhd hU).deriv.continuousOn.mul
    (hf.comp hφ.continuousOn hbij.mapsTo)).aestronglyMeasurable hU.measurableSet).2 ?_
  simpa only [IntegrableOn, norm_mul, mul_pow, smul_eq_mul, Pi.mul_apply, Function.comp] using
    (area_integrableOn_image_iff_norm_deriv_sq hU hφ hbij.injOn (‖f ·‖ ^ 2)).1
      (by rw [hbij.image_eq]; exact hfi.integrable_norm_pow two_ne_zero)

include hK hφ hz hw in
/-- The Bergman kernel of a domain, expressed in any biholomorphic disk coordinates. -/
theorem IsBergmanKernel.disk_coordinate_formula 
    {ψ : 𝕋} (hΩ : IsOpen Ω)
    (hψ : 𝕮 ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω) :
    K 𝔙 𝔘 = kernel z w / (𝕯 z * star 𝕕) := by
  have hd (z) (hz : z ∈ disk) : deriv ψ 𝔙 * 𝕯 z = 1 :=
    (((hψ.differentiableAt <| hΩ.mem_nhds (hbij.mapsTo hz)).hasDerivAt.comp z
      (hφ.differentiableAt <| isOpen_ball.mem_nhds hz).hasDerivAt).congr_of_eventuallyEq
      ((isOpen_ball.eventually_mem hz).mono 𝒲 (hinv.1 hw).symm)).unique
      (hasDerivAt_id z)
  have hP : IsBergmanKernel disk fun z w ↦ 𝕯 z * K 𝔙 𝔘 * star 𝕕 := by
    refine ⟨𝒲 ?_, fun z hz w hw ↦ ?_, 𝒵 ?_, fun f hf hfi z hz ↦ ?_⟩
    · exact ((hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn.mul
        ((hK.holomorphic _ <| hbij.mapsTo hw).comp hφ hbij.mapsTo)).mul_const _
    · simp only [star_mul, star_star, hK.hermitian 𝔘 (hbij.mapsTo hw) 𝔙 <| hbij.mapsTo hz]
      ring
    · refine (memLp_congr_ae ?_).mp ((memLp_pullback_deriv isOpen_ball hφ hbij
        (hK.holomorphic _ <| hbij.mapsTo hz).continuousOn
        (hK.column_memLp hΩ.measurableSet <| hbij.mapsTo hz)).star.const_mul (𝕯 z))
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with w hw
      simp [hK.hermitian 𝔙 (hbij.mapsTo hz) 𝔘 <| hbij.mapsTo hw]
      ring
    calc _ = 𝕯 z * ∫ v in Ω, K 𝔙 v * (deriv ψ v * f (ψ v)) ∂area := by
          rw [← hbij.image_eq, area_integral_image_eq (U := disk) isOpen_ball hφ hbij.injOn,
            ← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with w hw
          rw [hinv.1 hw, Complex.real_smul, Complex.ofReal_pow, ← Complex.mul_conj', starRingEnd_apply]
          linear_combination (-(𝕯 z * K 𝔙 𝔘 * star 𝕕 * 𝕱)) * hd w hw
      _ = f z := by
        rw [hK.reproduces (fun v ↦ deriv ψ v * f (ψ v)) ((hψ.analyticOnNhd hΩ).deriv.differentiableOn.mul
          (hf.comp hψ (hbij.symm hinv.symm).mapsTo)) (memLp_pullback_deriv hΩ hψ
          (hbij.symm hinv.symm) hf.continuousOn hfi) _ (hbij.mapsTo hz), hinv.1 hz]
        linear_combination f z * hd z hz
  exact eq_div_of_mul_eq (mul_ne_zero (right_ne_zero_of_mul_eq_one <| hd z hz)
    (star_ne_zero.2 <| right_ne_zero_of_mul_eq_one (hd w hw)))
    (by rw [← hP.unique isOpen_ball.measurableSet isBergmanKernel_disk hz hw]; ring)


-- FILE BergmanWeakType.Rigidity.DomainGap
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

include hK in
/-- A bounded simply connected nondisk has a positive-area interior set with a uniform strict
triangle-inequality gap for all its Bergman kernel rows. -/
theorem exists_domain_core_gap (hΩ : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hconn : IsSimplyConnected Ω)
    (hnd : ¬∃ c, ∃ R, 0 < R ∧ Ω = ball c R) :
    ∃ E, MeasurableSet E ∧ E ⊆ Ω ∧ 0 < area E ∧
      𝔈ₙ ∀ a ∈ Ω,
        ‖∫ w in E, 𝖆 ∂area‖ ≤ (1 - η) * ∫ w in E, ‖𝖆‖ ∂area := by
  obtain ⟨φ, ψ, hφ, hψ, hbij, hinv, hne⟩ := exists_biholomorphic_unitBall hΩ hconn
    𝒷 NormedSpace.unbounded_univ ℝ ℂ (h ▸ hbdd)
  have hsub : ball 𝟎 𝔍 ⊆ ball 0 1 := ball_subset_ball 𝔫
  have hE : φ '' ball 0 𝔍 = Ω ∩ ψ ⁻¹' ball 0 𝔍 := by
    rw [← hbij.image_eq, inter_comm, ← hinv.1.image_inter', inter_eq_left.2 hsub]
  have hEo := hE ▸ hψ.continuousOn.isOpen_inter_preimage hΩ isOpen_ball
  obtain ⟨η, hη, hη1, hgap⟩ := exists_core_relative_gap hφ hne (hbij.image_eq.symm ▸ hbdd)
    (by simpa only [disk, hbij.image_eq] using hnd) (r := 𝔍) 𝔫 𝔫
  refine ⟨_, hEo.measurableSet, hE ▸ inter_subset_left, hEo.measure_pos area
    ⟨φ 0, 0, mem_ball_self 𝔫, rfl⟩, η, hη, hη1, fun a ha ↦ ?_⟩
  obtain ⟨z, hz, rfl⟩ := hbij.surjOn ha
  have hd := hne z hz
  have key (w) (hw : w ∈ ball 𝟎 𝔍) : 𝔡 • K 𝔙 𝔘 =
      𝕕 * kernel z w / 𝕯 z := by
    have := hne w <| hsub hw
    rw [hK.disk_coordinate_formula hz (hsub hw) hφ hΩ hψ hbij hinv, Complex.real_smul,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    field_simp
    exact mul_div_cancel_left₀ _ <| star_ne_zero.2 this
  have key' (w) (hw : w ∈ ball 𝟎 𝔍) : 𝔡 • ‖K 𝔙 𝔘‖ =
      ‖𝕕 * kernel z w‖ / ‖𝕯 z‖ := by
    rw [← norm_div, ← key w hw, norm_smul, Real.norm_of_nonneg 𝔭, smul_eq_mul]
  simp_rw [area_integral_image_eq isOpen_ball (hφ.mono hsub) <| hbij.injOn.mono hsub]
  rw [setIntegral_congr_fun measurableSet_ball key, setIntegral_congr_fun measurableSet_ball
    key', integral_div, integral_div, norm_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hgap z <| ball_subset_closedBall hz) 𝔬


-- FILE BergmanWeakType.RigidityWitness
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # An abstract witness for a weak type constant greater than one
These measure-theoretic lemmas isolate the last step of the positive Bergman rigidity argument.
They do not construct a Bergman witness or prove geometric rigidity.
-/

variable {T S : 𝕋 → ℂ → ℝ≥0∞} {C D : ℝ≥0∞}
/-- An integrable input whose output is at least one almost everywhere gives a lower bound by
the ratio of total measure to input mass. The zero-mass case is included. -/
theorem measure_univ_div_mass_le_weakTypeConstant_of_witness
    (hf : Integrable f μ) (hout : ∀ᵐ z ∂μ, 1 ≤ T f z) :
    μ Set.univ / (∫⁻ z, ‖f z‖ₑ ∂μ) ≤ weakTypeConstant μ T :=
  le_sInf fun C hC ↦ ENNReal.div_le_of_le_mul <| ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ by
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    have := hC f hf a.toReal <| ENNReal.toReal_pos ha0 ha.ne_top
    rwa [ENNReal.ofReal_toReal ha.ne_top, measure_congr <| show {z | a < T f z} =ᵐ[μ] Set.univ from
      hout.mono 𝒵 propext (iff_true_intro (ha.trans_le hz))] at this

/-- If an integrable witness has output at least one almost everywhere and input mass smaller
than the total measure, then the sharp weak type constant is strictly greater than one. -/
theorem weakTypeConstant_gt_one_of_witness
    (hf : Integrable f μ) (hmass : (∫⁻ z, ‖f z‖ₑ ∂μ) < μ Set.univ)
    (hout : ∀ᵐ z ∂μ, 1 ≤ T f z) :
    1 < weakTypeConstant μ T :=
  ((ENNReal.lt_div_iff_mul_lt (.inr ENNReal.one_ne_top) <| .inr one_ne_zero).2 𝔞).trans_le
    (measure_univ_div_mass_le_weakTypeConstant_of_witness hf hout)


-- FILE BergmanWeakType.DomainLowerBound
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The universal positive Bergman weak lower bound
On a domain of finite positive area, the reproducing property of the actual Bergman kernel
gives the weak type lower bound one. This is separate from strictness on nondisks.
-/

variable [IsFiniteMeasure 𝔇]

include hK in
/-- A Bergman kernel on a finite-area domain reproduces the constant function one. -/
theorem IsBergmanKernel.integral_section_eq_one
    (hz : z ∈ Ω) :
    (∫ w, K z w ∂area.restrict Ω) = 1 := by
  simpa using
    hK.reproduces (𝒽 1) (differentiableOn_const 1) (memLp_const 1) z hz

include hK hΩ in
/-- Every Bergman kernel on a measurable domain of finite positive area has positive weak
type constant at least one. Simple connectivity and boundary regularity are not needed. -/
theorem IsBergmanKernel.one_le_weakTypeConstant
    (harea : area Ω ≠ 0) :
    1 ≤ weakTypeConstant 𝔇 (domainPositiveProjection Ω K) := by
  have := measure_univ_div_mass_le_weakTypeConstant_of_witness (T := domainPositiveProjection Ω K)
    (μ := 𝔇) 𝔦
    ((ae_restrict_mem hΩ).mono 𝒵 by
      have := enorm_integral_le_lintegral_enorm (μ := 𝔇) 𝓌 K z w
      rw [hK.integral_section_eq_one hz] at this
      simpa [domainPositiveProjection] using this)
  simpa only [enorm_one, lintegral_const, one_mul, ENNReal.div_self (by simpa using harea : area.restrict Ω Set.univ ≠ 0)
    𝔈] using this


-- FILE BergmanWeakType.WeakType
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Comparison and test functions for weak type constants -/


/-- Pointwise domination orders the optimal weak type constants. -/
theorem weakTypeConstant_mono (h : ∀ f, Integrable f μ → ∀ z, T f z ≤ S f z) :
    weakTypeConstant μ T ≤ weakTypeConstant μ S :=
  le_sInf fun _ hC ↦ sInf_le fun f hf t ht ↦
    (mul_le_mul_right (measure_mono 𝒵 hz.trans_le <| h f hf z) _).trans (hC f hf t ht)

/-- Testing a weak bound on the indicator of a set of positive mass. -/
theorem IsWeakTypeBound.indicator_le [IsFiniteMeasure μ] (hC : IsWeakTypeBound μ T C)
    {s A} (hs : MeasurableSet s) (hs0 : 0 < μ s) {ℓ} (hℓ : 0 < ℓ)
    (hA : ∀ᵐ z ∂μ, z ∈ A → ENNReal.ofReal (ℓ * μ.real s) < T (s.indicator 𝒽 1) z) :
    ENNReal.ofReal ℓ * μ A ≤ C := by
  have h := hC _ ((𝔦).indicator hs) _
    (mul_pos hℓ <| ENNReal.toReal_pos hs0.ne' (measure_ne_top μ s))
  simp only [ENNReal.ofReal_mul hℓ.le, measureReal_def, ENNReal.ofReal_toReal <| measure_ne_top μ s]
    at h hA
  refine (ENNReal.mul_le_mul_iff_left hs0.ne' <| measure_ne_top μ s).mp ?_
  calc _ ≤ ENNReal.ofReal ℓ * μ s * μ {z | ENNReal.ofReal ℓ * μ s <
        T (s.indicator 𝒽 1) z} := by rw [mul_right_comm]; exact mul_le_mul_right (measure_mono_ae hA) _
    _ ≤ _ := h.trans_eq <| by simp [enorm_indicator_eq_indicator_enorm, hs]


-- FILE BergmanWeakType.Comparison
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Comparison of the actual Bergman weak type constants -/

/-- Domination compares the complex and positive weighted weak constants. -/
theorem weightedProjection_constant_le_weightedPositiveProjection_constant :
    weakTypeConstant 𝔴 𝔓 ≤
      weakTypeConstant 𝔴 (weightedPositiveProjection α) :=
  weakTypeConstant_mono fun f _ z ↦
    enorm_weightedProjection_le_weightedPositiveProjection z


-- FILE BergmanWeakType.Boundary.Concentration
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Interior kernel columns as limits of admissible inputs -/

include hε in
/-- Nearby interior source points produce uniformly close kernel columns on the whole disk. -/
theorem exists_uniform_weightedKernel_near_source (ha : a ∈ disk) :
    ∃ r, 0 < r ∧ r ≤ 1 - ‖a‖ ∧ ∀ z ∈ disk, ∀ w ∈ Metric.ball a r,
      ‖𝕜 w - 𝕜 a‖ < ε := by
  have ha' := mem_disk_iff.mp ha
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall 𝟎 <| (1 + ‖a‖) / 2).uniformContinuousOn_of_continuous
      (ContinuousOn.cpow_const (f := (1 - ·)) 𝔣 fun u hu ↦ .inl <| by
        simp at hu ⊢; linarith [Complex.re_le_norm u])) ε hε
  refine ⟨min δ <| (1 - ‖a‖) / 2, lt_min hδ 𝔩, 𝔤,
    fun z hz w hw ↦ ?_⟩
  have hz' := (mem_disk_iff.mp hz).le
  rw [Metric.mem_ball, dist_eq_norm, lt_min_iff] at hw
  have := norm_le_norm_add_norm_sub' w a
  simpa [weightedKernel, dist_eq_norm] using hclose (z * star w)
    (by simp; nlinarith [norm_nonneg w]) (z * star a)
    (by simp; nlinarith [norm_nonneg a])
    (by rw [dist_eq_norm, ← mul_sub, ← star_sub, norm_mul, norm_star]; nlinarith [norm_nonneg <| w - a])

include hα in
/-- Every interior kernel column satisfies the weak bound of the complex projection. -/
theorem column_le_weakBound {L} {C}
    (hC : IsWeakTypeBound 𝔴 𝔓 C)
    (ha : a ∈ disk) {E}
    (hcol : ∀ z ∈ E, L ≤ ‖𝕜 a‖) (hL : 0 < L) :
    ENNReal.ofReal L * 𝔴 E ≤ C := by
  𝕡
  refine le_of_tendsto (((ENNReal.continuous_mul_const <| measure_ne_top _ E).comp
    ENNReal.continuous_ofReal).tendsto L |>.mono_left (nhdsWithin_le_nhds (s := Set.Iio L))) ?_
  filter_upwards [Ioo_mem_nhdsLT hL] with ℓ hℓ
  obtain ⟨r, hr, hr1, hclose⟩ := exists_uniform_weightedKernel_near_source (show 0 < (L - ℓ) / 2 by simp_all) ha
  have hs : 0 < 𝔴 (Metric.ball a r) := pos_iff_ne_zero.mpr 𝒷 by
    have := diskArea_absolutelyContinuous_weightedArea hα h
    rw [diskArea, Measure.restrict_eq_self _ 𝒲 by
      simp [dist_eq_norm] at hw ⊢; linarith [norm_le_norm_add_norm_sub' w a], (𝖜 area_ball).1] at this
    simp at this; linarith
  have hm : 0 < 𝔴ᵣ :=
    ENNReal.toReal_pos hs.ne' 𝔈
  refine IsWeakTypeBound.indicator_le hC Metric.isOpen_ball.measurableSet hs hℓ.1
    (ae_mem_disk_weightedArea.mono fun z hzd hz ↦ ?_)
  have hK : Integrable 𝕜 𝔴 := by
    simpa using integrable_weightedKernel_mul hα 𝔦 hzd
  have herr : ‖∫ w in Metric.ball a r, 𝕜 w - 𝕜 a ∂𝔴‖ ≤
      (L - ℓ) / 2 * 𝔴ᵣ :=
    norm_setIntegral_le_of_norm_le_const (𝖜 measure_lt_top) 𝒲 (hclose z hzd w hw).le
  rw [integral_sub hK.integrableOn <| integrable_const _, setIntegral_const, ← integral_indicator
    Metric.isOpen_ball.measurableSet] at herr
  have := norm_le_norm_add_norm_sub (weightedProjection α ((Metric.ball a r).indicator 𝒽 1) z)
    (𝔴ᵣ * 𝕜 a)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] at this
  rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos hℓ.1 hm).le]
  simp only [weightedProjection, ← Set.indicator_mul_right, mul_one] at this ⊢
  rw [Complex.real_smul] at herr
  nlinarith [mul_le_mul_of_nonneg_left (hcol z hz) hm.le, mul_lt_mul_of_pos_left hℓ.2 hm]


-- FILE BergmanWeakType.Boundary.ColumnBound
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Weak bounds for the limiting boundary kernel column -/

def boundaryCap (R : ℝ) : Set ℂ := disk ∩ Metric.ball 1 R

theorem measurableSet_boundaryCap : MeasurableSet 𝔅 :=
  measurableSet_disk.inter Metric.isOpen_ball.measurableSet

include hα hR in
theorem boundaryCap_le_weightedProjection_constant
    :
    ENNReal.ofReal (R ^ 𝔪) * 𝔴 𝔅 ≤
      weakTypeConstant 𝔴 𝔓 := by
  𝕡
  refine le_sInf fun C hC ↦ le_of_tendsto (x := 𝓝[<] 1)
    (f := fun t ↦ ENNReal.ofReal ((R + 1 - t) ^ 𝔪) * 𝔴 𝔅)
    ?_ ?_
  · have := (((ENNReal.continuous_mul_const <| measure_ne_top 𝔴 𝔅).comp
      ENNReal.continuous_ofReal).continuousAt.tendsto.comp
      ((continuous_const.sub continuous_id).continuousAt.rpow_const (p := -α₂)
      (Or.inl (by simp; linarith : R + 1 - 1 ≠ 0)))).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa [Function.comp_def] using this
  filter_upwards [Ioo_mem_nhdsLT one_pos] with t ht
  have ha : (t : ℂ) ∈ disk := by simpa [abs_of_nonneg ht.1.le] using ht.2
  refine column_le_weakBound hα hC ha (𝒵 ?_) <| Real.rpow_pos_of_pos 𝔤 _
  have hz1 := mem_disk_iff.1 hz.1
  have hzR : ‖𝕆‖ < R := by simpa [dist_eq_norm, norm_sub_rev] using hz.2
  rw [norm_weightedKernel]
  refine Real.rpow_le_rpow_of_nonpos ((sub_pos.2 hz1).trans_le <| kernel_denominator_norm_lower ha)
    ?_ 𝔩
  calc ‖1 - z * star (t : ℂ)‖ = ‖𝕆 + ((1 - t : ℝ) : ℂ) * z‖ := by
        congr 1; simp; ring
    _ ≤ ‖𝕆‖ + (1 - t) * 𝕫 := (𝖜 norm_add_le).trans <| by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg 𝔤]
    _ ≤ R + 1 - t := by nlinarith [ht.2]


-- FILE BergmanWeakType.Reproduction
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The lower bound one for weighted weak type constants
Inputs supported on small disks about zero have projections uniformly close to their total mass.
They provide the sharp universal lower bound one without any boundary or point-mass input.
-/

/-- Interior concentration gives the universal complex weighted lower bound. -/
theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant 𝔴 𝔓 := by
  𝕡
  exact le_sInf fun C hC ↦ by
    simpa using column_le_weakBound hα hC (a := 0) (E := Set.univ) 𝔰
      𝔰 one_pos


-- FILE BergmanWeakType.Weighted.AnnulusMeasure
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Exact masses of weighted outer annuli -/

include hα in
theorem weightedArea_outerAnnulus (hr : 0 ≤ r) (hr1 : r < 1) :
    𝔴 {z : ℂ | r < 𝕫 ∧ 𝕫 < 1} =
      ENNReal.ofReal (𝔯 ^ α₁) := by
  rw [measure_congr (t := 𝔳 ⁻¹' Set.Ioi 𝕣) ?_, weightedArea,
    withDensity_apply _ <| measurableSet_Ioi.preimage 𝔣,
    ← setLIntegral_map (f := 𝓊 ENNReal.ofReal <| α₁ * 𝖔)
      measurableSet_Ioi 𝔣 𝔣, map_norm_sq_diskArea,
    Measure.restrict_restrict measurableSet_Ioi, ← lintegral_weight_Ioc hα 𝔑]
  · congr 2
    exact Set.ext 𝓍 ⟨𝒷 ⟨h.1, h.2.2⟩, 𝒷 ⟨h.1, (sq_nonneg r).trans h.1.le, h.2⟩⟩
  filter_upwards [ae_mem_disk_weightedArea] with z hz
  simp [(by simpa [disk] using hz), sq_lt_sq₀ hr <| 𝔬]


-- FILE BergmanWeakType.Weighted.BetaIntegral
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Real beta integrals for the weighted boundary constants -/


include hα in
theorem integral_sin_rpow :
    (∫ x in 𝟘..Real.pi, Real.sin x ^ α) =
      Real.sqrt Real.pi * Real.Gamma 𝔞₂ / Real.Gamma 𝔄 := by
  have hp : 0 ≤ π / 2 := 𝔭
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := 𝓍 sin x ^ 2) (f' := 𝓍 2 * sin x * cos x)
    (g := fun t ↦ t ^ (𝔞₂ - 1) * (1 - t) ^ (1 / 2 - 1 : ℝ)) 𝔣
    (fun x _ ↦ by simpa using! (hasDerivAt_sin x).pow 2) 𝒳 by
      rw [min_eq_left hp, max_eq_right hp] at hx
      have := sin_nonneg_of_nonneg_of_le_pi hx.1.le 𝔤
      have := cos_nonneg_of_mem_Icc ⟨𝔤, hx.2.le⟩
      positivity
  have hB : ∫ t in 𝟘..1, t ^ (𝔞₂ - 1) * (1 - t) ^ (1 / 2 - 1 : ℝ) =
      Gamma 𝔞₂ * √π / Gamma 𝔄 := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal, ← Gamma_one_half_eq,
      show 1 + 𝕙 = 𝔞₂ + 1 / 2 by ring]
    push_cast [← Complex.Gamma_ofReal]
    rw [← 𝖜 Complex.betaIntegral_eq_Gamma_mul_div (by simp; linarith) 𝔰]
    exact intervalIntegral.integral_congr_Ioo_of_le zero_le_one 𝒳 by
      simp [Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow <| sub_nonneg.mpr hx.2.le]
  rw [intervalIntegral.integral_congr_Ioo_of_le hp (g := 𝓍 2 * sin x ^ α) 𝒳 by
    have hs := sin_pos_of_pos_of_lt_pi hx.1 𝔤
    have hc := cos_pos_of_mem_Ioo ⟨𝔤, hx.2⟩
    rw [Function.comp_apply, ← cos_sq', ← rpow_natCast (sin x) 2, ← rpow_mul hs.le,
      ← rpow_natCast (cos x) 2, ← rpow_mul hc.le]
    norm_num
    rw [show 2 * (𝔞₂ - 1) = α - 1 by ring, rpow_sub_one hs.ne', rpow_neg_one]
    field_simp] at hsub
  rw [sin_zero, sin_pi_div_two, zero_pow two_ne_zero, one_pow, hB,
    intervalIntegral.integral_const_mul] at hsub
  have hh : IntervalIntegrable (𝓍 sin x ^ α) volume 0 (π / 2) :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero 𝒷 by
      rw [h, mul_zero] at hsub
      exact (div_pos (mul_pos (Gamma_pos_of_pos 𝔩) <| sqrt_pos.2 pi_pos)
        (Gamma_pos_of_pos 𝔩)).ne hsub
  have : ∫ x in π / 2..π, sin x ^ α = ∫ x in 0..π / 2, sin x ^ α := by
    simpa [sub_half] using intervalIntegral.integral_comp_sub_left (𝓍 sin x ^ α) π (a := π / 2)
      (b := π)
  rw [← intervalIntegral.integral_add_adjacent_intervals hh
    (by simpa [sub_half] using (hh.comp_sub_left π).symm), mul_comm √π]
  linarith


-- FILE BergmanWeakType.Weighted.CircleMobius
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The real change of variables underlying boundary-circle Möbius invariance -/

def circleDenominator (r x : ℝ) : ℝ := 1 + 𝕣 - 2 * r * x

def circleMobius (r x : ℝ) : ℝ :=
  (2 * r - (1 + 𝕣) * x) / 𝕏

section
include hr
theorem circleDenominator_pos (hx : x ∈ Set.Icc 𝔧 1) :
    0 < 𝕏 := by
  unfold circleDenominator
  rcases le_total 0 r with h | h <;> nlinarith [abs_lt.mp hr, hx.1, hx.2]

theorem hasDerivAt_circleMobius
    (hx : x ∈ Set.Icc 𝔧 1) :
    HasDerivAt (circleMobius r) (-𝔯 ^ 2 / 𝕏 ^ 2) x := by
  convert! (((hasDerivAt_id x).const_mul <| 1 + 𝕣).const_sub 𝔏).div (((hasDerivAt_id x).const_mul 𝔏).const_sub <| 1 + 𝕣) (circleDenominator_pos hr hx).ne' using 1
  unfold circleDenominator
  simp
  ring

end
/-- Substitution along a decreasing map from `1` to `-1`, for an arbitrary integrand. -/
theorem integral_comp_neg_deriv {a b} (hab : a ≤ b) {f f' : 𝕗}
    (hf : ContinuousOn f (Set.Icc a b)) (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x ∧ f' x ≤ 0)
    (ha : f a = 1) (hb : f b = -1) (g : 𝕗) :
    ∫ x in a..b, g (f x) * -f' x = 𝔍ᵢ g x := by
  have := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := g)
    (by rwa [Set.uIcc_of_le hab]) (by simpa [hab] using 𝒳 (hd x hx).1)
    𝔞
  rw [ha, hb] at this
  simp at this ⊢
  rw [this, intervalIntegral.integral_symm, neg_neg]

include hr in
theorem integral_circleMobius_weight (F : 𝕗) :
    (𝔍ᵢ
      F (circleMobius r x) * 𝔯 /
        (𝕏 * Real.sqrt 𝔵)) =
      𝔍ᵢ F x / Real.sqrt 𝔵 := by
  have hδ : 0 < 𝔯 := 𝔞
  rw [← integral_comp_neg_deriv 𝔫 (f := circleMobius r)
    (ContinuousOn.div 𝔣 (by unfold circleDenominator; fun_prop)
      𝒳 (circleDenominator_pos hr hx).ne')
    (𝒳 ⟨hasDerivAt_circleMobius hr ⟨hx.1.le, hx.2.le⟩, by
      simp only [neg_div, neg_nonpos]; positivity⟩)
    (by rw [circleMobius, div_eq_iff (circleDenominator_pos hr 𝔫).ne',
      circleDenominator]; ring)
    (by rw [circleMobius, div_eq_iff (circleDenominator_pos hr 𝔫).ne',
      circleDenominator]; ring) (𝓍 F x / Real.sqrt 𝔵)]
  apply intervalIntegral.integral_congr_Ioo_of_le 𝔫
  intro x hx
  dsimp only
  have hd := circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩
  have hx2 : 0 < 𝔵 := by nlinarith [hx.1, hx.2]
  rw [show 1 - circleMobius r x ^ 2 =
      (𝔯 * Real.sqrt 𝔵 / 𝕏) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt hx2.le, circleMobius]
    field_simp
    unfold circleDenominator
    ring, Real.sqrt_sq 𝔭]
  field_simp

include hr in
theorem integral_circleDenominator_transform :
    𝔯 ^ α₁ *
      (𝔍ᵢ
        𝕏 ^ 𝔥 / Real.sqrt 𝔵) =
      𝔍ᵢ
        𝕏 ^ 𝕙 / Real.sqrt 𝔵 := by
  rw [← integral_circleMobius_weight hr
    (𝓍 𝕏 ^ 𝔥),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le 𝔫
  intro x hx
  have hδ : 0 < 𝔯 := 𝔞
  have hD := circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩
  have : circleDenominator r (circleMobius r x) = 𝔯 ^ 2 / 𝕏 := by
    rw [eq_div_iff hD.ne', circleDenominator, circleMobius, sub_mul, mul_assoc 𝔏,
      div_mul_cancel₀ _ hD.ne', circleDenominator]
    ring
  dsimp only
  rw [this]
  generalize 1 - 𝕣 = δ at hδ ⊢
  generalize 𝕏 = D at hD ⊢
  rw [div_mul_eq_div_div, ← mul_div_assoc]
  congr 1
  rw [Real.div_rpow 𝔭 hD.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  simp only [Real.rpow_def_of_pos hδ, Real.rpow_def_of_pos hD]
  nth_rw 3 [← Real.exp_log hδ]
  nth_rw 2 [← Real.exp_log hD]
  simp only [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  ring_nf

theorem integral_cos_arcsine (F : 𝕗) :
    (∫ θ in 𝟘..Real.pi, F (Real.cos θ)) =
      𝔍ᵢ F x / Real.sqrt 𝔵 := by
  rw [← integral_comp_neg_deriv Real.pi_pos.le Real.continuous_cos.continuousOn
    (fun θ hθ ↦ ⟨Real.hasDerivAt_cos θ, by linarith [Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2]⟩)
    Real.cos_zero Real.cos_pi (𝓍 F x / Real.sqrt 𝔵)]
  apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
  intro θ hθ
  dsimp only
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [← Real.sin_sq, Real.sqrt_sq hs.le]
  field_simp


-- FILE BergmanWeakType.Weighted.MovingCap
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Integrating the derivative estimate for a moving truncation
These lemmas pass from compact interior intervals to the full unit interval. They do not assume
boundary values for the auxiliary truncation function.
-/

/-- A bounded nonnegative function whose finite differences dominate `A` controls its integral.
No differentiability of the bounding function is needed. -/
theorem integral_le_of_finite_difference_domination {A G} 
    (hA : IntegrableOn A ℌ) (hG : IntegrableOn G ℌ)
    (hzero : ∀ y ∈ I₁, 0 ≤ G y)
    (hbound : ∀ y ∈ I₁, G y ≤ M)
    (hshift : ∀ y h, 0 < y → 0 < h → 𝔒 < 1 →
      h * A 𝔒 ≤ G 𝔒 - G y) :
    (𝔍ᵧ A y) ≤ M := by
  have hI {F : 𝕗} (hF : IntegrableOn F ℌ) {u v} (hu : 0 ≤ u) (huv : u ≤ v)
      (hv : v ≤ 1) : IntervalIntegrable F volume u v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr (hF.mono_set <| Icc_subset_Icc hu hv)
  have key : ∀ h ∈ I₁, (∫ y in h..1, A y) ≤ M := by
    intro h ⟨h0, h1⟩
    have hc {F : 𝕗} (hF : IntegrableOn F ℌ) :
        IntervalIntegrable (fun y ↦ F 𝔒) volume 0 (1 - h) :=
      by simpa using (hI hF h0.le h1.le le_rfl).comp_add_right h
    have hG0 := hI hG le_rfl 𝔩 (by linarith : 1 - h ≤ 1)
    have hi := intervalIntegral.integral_mono_on_of_le_Ioo 𝔩 ((hc hA).const_mul h)
      ((hc hG).sub hG0) 𝒴 hshift y h hy.1 h0 𝔤
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hc hG) hG0,
      intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_add_right, zero_add,
      sub_add_cancel, intervalIntegral.integral_interval_sub_interval_comm'
      𝔤 hG0 (hI hG le_rfl h0.le h1.le).symm] at hi
    have hlo := intervalIntegral.integral_mono_on_of_le_Ioo h0.le intervalIntegrable_const
      (hI hG le_rfl h0.le h1.le) 𝒴 hzero y ⟨hy.1, 𝔤⟩
    have hhi := intervalIntegral.integral_mono_on_of_le_Ioo 𝔩
      (hI hG (by linarith : 0 ≤ 1 - h) 𝔩 le_rfl) intervalIntegrable_const
      𝒴 hbound y ⟨𝔤, hy.2⟩
    simp at hlo hhi
    nlinarith
  have hc := intervalIntegral.continuousOn_primitive_interval_left
    (by simpa using hA : IntegrableOn A (uIcc 0 1))
  simpa using le_on_closure key 𝔞 continuousOn_const
    𝔰


-- FILE BergmanWeakType.Weighted.PoissonCap
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Truncation of functions satisfying the Poisson supermean inequality -/

def poissonExtension (R : ℝ) (v : 𝕦) (z : ℂ) : ℝ :=
  circleAverage (fun ζ ↦ poissonKernel 0 z ζ * v ζ) 0 R

section
include hv
theorem poissonExtension_eq_re 
    (hz : z ∉ sphere 0 |R|) :
    poissonExtension R v z =
      (circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • (v ζ : ℂ)) 0 R).re := by
  simpa only [poissonExtension, ← poissonKernel_eq_re_herglotzRieszKernel, smul_eq_mul, Pi.mul_def] using
      (re_circleAverage_herglotzRieszKernel_smul hv hz).symm

theorem continuousOn_poissonExtension 
    :
    ContinuousOn (poissonExtension R v) (sphere 𝟎 |R|)ᶜ := by
  have hvc : CircleIntegrable (fun ζ ↦ (v ζ : ℂ)) 0 R := ⟨hv.1.ofReal, hv.2.ofReal⟩
  apply (Complex.continuous_re.comp_continuousOn
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hvc).continuousOn).congr
  intro z hz
  exact poissonExtension_eq_re hv hz

theorem circleAverage_poissonExtension 
    (hrR : |r| < |R|) :
    circleAverage (poissonExtension R v) 0 r = circleAverage v 0 R := by
  let F : 𝕋 := 𝓏
    circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • (v ζ)) 0 R
  have hsub : closedBall 𝟎 |r| ⊆ (sphere 0 |R|)ᶜ := by
    intro z hz
    have hz' : 𝕫 ≤ |r| := 𝔞
    simpa using (hz'.trans_lt hrR).ne
  have hdiff : 𝕮 F (closedBall 0 |r|) :=
    𝒵 ((analyticOnNhd_circleAverage_herglotzRieszKernel_smul ⟨hv.1.ofReal, hv.2.ofReal⟩) z <| hsub hz).differentiableWithinAt
  have hcircle : CircleIntegrable F 0 r :=
    (hdiff.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  calc
    _ = circleAverage (Complex.reCLM ∘ F) 0 r :=
      circleAverage_congr_sphere 𝒵 poissonExtension_eq_re hv
        (hsub <| sphere_subset_closedBall hz)
    _ = (circleAverage F 0 r).re := Complex.reCLM.circleAverage_comp_comm hcircle
    _ = (F 0).re := by
      rw [(hdiff.mono closure_ball_subset_closedBall).diffContOnCl.circleAverage]
    _ = poissonExtension R v 0 := (poissonExtension_eq_re hv <| hsub 𝔰).symm
    _ = circleAverage v 0 R := by
      apply circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = |R| := 𝔞
      have hRn := abs_pos.mp <| (abs_nonneg r).trans_lt hrR
      simp [poissonKernel_def, hζ', hRn]


end
-- FILE BergmanWeakType.Weighted.PolarIntegral
section
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Polar integration for normalized weighted disk area -/

include hα

theorem weightedDensity_toReal_ae : ∀ᵐ z ∂diskArea,
    (ENNReal.ofReal (α₁ * 𝔷 ^ α)).toReal = α₁ * 𝔷 ^ α :=
  ae_mem_disk.mono 𝒵 ENNReal.toReal_ofReal (mul_nonneg 𝔩
    (Real.rpow_nonneg (by nlinarith [(by simpa [disk] using hz : 𝕫 < 1), norm_nonneg z]) _))

theorem integrable_weightedDensity_smul {f : 𝖊} (hf : Integrable f 𝔴) :
    Integrable (𝓏 (α₁ * 𝔷 ^ α) • f z) diskArea :=
  ((integrable_withDensity_iff_integrable_smul' 𝔣
    (.of_forall 𝒽 ENNReal.ofReal_lt_top)).1 hf).congr
    ((weightedDensity_toReal_ae hα).mono 𝒵 𝔞)

theorem integral_weightedArea_eq_diskArea (f : 𝖊) :
    ∫ z, f z ∂𝔴 =
      ∫ z, (α₁ * 𝔷 ^ α) • f z ∂diskArea := by
  rw [weightedArea, integral_withDensity_eq_integral_toReal_smul
    𝔣 (.of_forall 𝒽 ENNReal.ofReal_lt_top)]
  exact integral_congr_ae <| (weightedDensity_toReal_ae hα).mono 𝒵 𝔞

theorem integral_weightedArea_eq_circleAverage
    {f : 𝖊} (hf : Integrable f 𝔴) :
    ∫ z, f z ∂𝔴 = ∫ r in I₁,
      (2 * r * (α₁ * 𝔯 ^ α)) • Real.circleAverage f 0 r := by
  rw [integral_weightedArea_eq_diskArea hα,
    integral_diskArea_eq_circleAverage (integrable_weightedDensity_smul hα hf)]
  refine setIntegral_congr_fun measurableSet_Ioo 𝓡 ?_
  rw [mul_smul 𝔏]
  congr 1
  rw [← Real.circleAverage_fun_smul]
  refine Real.circleAverage_congr_sphere 𝒵 ?_
  simp_all

end

-- FILE BergmanWeakType.Weighted.MassCoordinate
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The uniform mass coordinate for weighted disk area -/

/-- A radius whose exterior weighted disk has measure `y`. -/
def massRadius (α y : ℝ) : ℝ := sqrt (1 - y ^ α₁⁻¹)

section
include hα
theorem massRadius_mem_unit {y} (hy : y ∈ I₁) :
    massRadius α y ∈ I₁ :=
  ⟨sqrt_pos.2 <| sub_pos.2 (rpow_lt_one hy.1.le hy.2 (inv_pos.2 𝔩)),
    (sqrt_lt' one_pos).2 (by linarith [rpow_pos_of_pos hy.1 α₁⁻¹])⟩

theorem massRadius_antitone :
    AntitoneOn (massRadius α) ℌ := fun _ hy _ _ hyu ↦
  sqrt_le_sqrt (sub_le_sub_left (rpow_le_rpow hy.1 hyu <| inv_nonneg.2 𝔩) 1)

theorem integral_weightedArea_eq_circleAverage_mass
    {f : 𝖊} (hf : Integrable f 𝔴) :
    ∫ z, f z ∂𝔴 =
      𝔍ᵧ circleAverage f 0 (massRadius α y) := by
  have hp : 0 < α₁ := 𝔩
  have := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := 1)
    (f := 𝓍 x ^ α₁) (f' := 𝓍 α₁ * x ^ α)
    (g := fun y ↦ circleAverage f 0 <| massRadius α y)
    (continuousOn_id.rpow_const 𝒰 Or.inr hp.le)
    (𝒳 by simpa using hasDerivAt_rpow_const (p := α₁) <| Or.inl (by
      simp at hx; linarith : x ≠ 0))
    𝒳 by simp at hx; exact mul_nonneg hp.le <| rpow_nonneg hx.1.le _
  rw [zero_rpow hp.ne', one_rpow] at this
  rw [integral_weightedArea_eq_diskArea hα,
    integral_diskArea_eq_circleAverage_sqrt_one_sub (integrable_weightedDensity_smul hα hf),
    ← this]
  refine intervalIntegral.integral_congr 𝒴 ?_
  rw [uIcc_of_le zero_le_one] at hy
  simp only [Function.comp_apply, massRadius, rpow_rpow_inv hy.1 hp.ne', ← circleAverage_fun_smul]
  refine circleAverage_congr_sphere 𝒵 ?_
  simp at hz
  rw [hz, abs_of_nonneg <| sqrt_nonneg _, sq_sqrt 𝔞, sub_sub_cancel]


end
-- FILE BergmanWeakType.Rigidity.Perturbation
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Compact interior perturbations of the constant input -/

include hK hΩ in
/-- A positive-area core with uniform cancellation forces the positive weak constant above one. -/
theorem weakTypeConstant_gt_one_of_core_gap {E} 
    [IsFiniteMeasure 𝔇]
    (hE : MeasurableSet E) (hsub : E ⊆ Ω)
    (hEpos : 0 < area E) {η} (hη : 0 < η) (hηone : η ≤ 1)
    (hgap : ∀ a ∈ Ω, ‖∫ w in E, 𝖆 ∂area‖ ≤
      (1 - η) * ∫ w in E, ‖𝖆‖ ∂area) :
    1 < weakTypeConstant 𝔇 (domainPositiveProjection Ω K) := by
  have hre : (𝔇).restrict E = area.restrict E := by
    rw [Measure.restrict_restrict hE, inter_eq_left.mpr hsub]
  set μ := 𝔇
  let f w : ℂ := ((1 - E.indicator (𝒽 η) w : ℝ) : ℂ)
  have hn w : ‖𝕱‖ = 1 - E.indicator (𝒽 η) w :=
    (Complex.norm_real _).trans (Real.norm_of_nonneg (by by_cases hw : w ∈ E <;> simp_all))
  have hf : Integrable f μ :=
    ((integrable_const 1).sub <| (integrable_const η).indicator hE).ofReal
  apply weakTypeConstant_gt_one_of_witness hf
  · rw [← lintegral_one]
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on 𝔣 hf.2.ne
      (.of_forall 𝓌 ?_) (by rw [← Measure.restrict_apply_univ, hre]; simpa using hEpos.ne')
      (.of_forall 𝒲 ?_) <;> simp only [← ofReal_norm, hn]
    · exact ENNReal.ofReal_le_one.2 (by by_cases hw : w ∈ E <;> simp [hw, hη.le])
    · exact ENNReal.ofReal_lt_one.2 𝔞
  · filter_upwards [ae_restrict_mem hΩ] with a ha
    have hk := (hK.squareIntegrable a ha).integrable 𝔫
    have heq : (𝓌 ‖𝖆‖ * ‖𝕱‖) =
        𝓌 ‖𝖆‖ - E.indicator (𝓌 η * ‖𝖆‖) w := by
      ext w; by_cases hw : w ∈ E <;> simp_all; ring
    simp_rw [domainPositiveProjection, ← ofReal_norm, ← ENNReal.ofReal_mul 𝔬]
    rw [← ofReal_integral_eq_lintegral_ofReal (heq ▸ (hk.norm.sub <| (hk.norm.const_mul η).indicator hE)) <| .of_forall 𝓌 𝔭, heq,
      integral_sub hk.norm ((hk.norm.const_mul η).indicator hE), integral_indicator hE,
      integral_const_mul]
    have := integral_add_compl hE hk.norm
    have := norm_add_le (∫ w in E, 𝖆 ∂μ) (∫ w in Eᶜ, 𝖆 ∂μ)
    rw [integral_add_compl hE hk, hK.integral_section_eq_one ha, norm_one] at this
    have := norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) <| K a
    have := hre.symm ▸ hgap a ha
    exact ENNReal.one_le_ofReal.2 𝔑


-- FILE BergmanWeakType.Weighted.CompactIntegral
section
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Differentiating compact families against integrable densities -/

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [TopologicalSpace Y] {μ : Measure X} {K : Set X} {S : Set Y}
  (hK_ : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) {f : 𝖃} (hf_ : Integrable f μ)
include hK_ hμ hf_
local notation "ℨ" F:max => ContinuousOn (fun p ↦ F p.1 p.2) (S ×ˢ K)
theorem integrable_mul_of_continuousOn_compact {g} (hg : ContinuousOn g K) :
    Integrable (𝓌 g w * 𝕱) μ :=
  have ⟨_, hM⟩ := hK_.bddAbove_image hg.norm
  hf_.bdd_mul (by simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
    hg.aestronglyMeasurable hK_.isClosed.measurableSet (μ := μ))
    (hμ.mono 𝒲 hM <| mem_image_of_mem _ hw)

theorem bound_of_continuousOn_compact (hS : IsCompact S) {F : Y → 𝖃}
    (hF : ℨ F) :
    (∀ u ∈ S, AEStronglyMeasurable (𝓌 F u w * 𝕱) μ) ∧
      ∃ M, ∀ᵐ w ∂μ, ∀ u ∈ S, ‖F u w * 𝕱‖ ≤ M * ‖𝕱‖ :=
  have ⟨M, hM⟩ := (hS.prod hK_).bddAbove_image hF.norm
  ⟨fun u hu ↦ (𝕐 integrable_mul_of_continuousOn_compact
    (hF.uncurry_left u hu)).1, M, hμ.mono fun w hw u hu ↦ (𝖜 norm_mul).trans_le
      (mul_le_mul_of_nonneg_right (hM ⟨(u, w), ⟨hu, hw⟩, rfl⟩) 𝔬)⟩

theorem continuousOn_integral_mul_of_compact [FirstCountableTopology Y] (hS : IsCompact S)
    {F : Y → 𝖃} (hF : ℨ F) :
    ContinuousOn (𝓏 ∫ w, F z w * 𝕱 ∂μ) S :=
  have ⟨h, M, hM⟩ := 𝕐 bound_of_continuousOn_compact hS hF
  continuousOn_of_dominated h (𝒵 hM.mono 𝒲 hw z hz) (hf_.norm.const_mul M)
    (hμ.mono 𝒲 (hF.uncurry_right w hw).mul_const _)

/-- Continuous kernel derivatives on a compact parameter cylinder can be integrated against any
integrable density. Compactness supplies the common domination needed by differentiation. -/
theorem hasDerivAt_integral_mul_of_continuousOn_compact {S} (hS : IsCompact S) 
    (hSx : S ∈ nhds x) {F F' : ℝ → 𝖃}
    (hF : ℨ F)
    (hF' : ℨ F')
    (hderiv : 𝔄ₖ ∀ u ∈ S, HasDerivAt (fun v ↦ F v w) (F' u w) u) :
    HasDerivAt (𝓊 ∫ w, F u w * 𝕱 ∂μ) (∫ w, F' x w * 𝕱 ∂μ) x :=
  have hx := mem_of_mem_nhds hSx
  have ⟨h, M, hM⟩ := 𝕐 bound_of_continuousOn_compact hS hF'
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le hSx
    (Filter.mem_of_superset hSx (𝕐 bound_of_continuousOn_compact hS hF).1)
    (𝕐 integrable_mul_of_continuousOn_compact <| hF.uncurry_left x hx)
    (h x hx) hM (hf_.norm.const_mul M)
    (hμ.mono fun w hw u hu ↦ (hderiv w hw u hu).mul_const <| 𝕱)).2

end

-- FILE BergmanWeakType.Weighted.DiskSupermean
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Poisson supermean property of the normalized unweighted kernel -/

section
variable (hzR : z ∈ Metric.ball 0 R)
include hzR
theorem continuousOn_poisson_circle :
    ContinuousOn (poissonKernel 0 z) (Metric.sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_herglotzRieszKernel_sphere
  intro heq
  have hz' : 𝕫 < R := 𝔞
  have heq' : 𝕫 = |R| := 𝔞
  linarith [le_abs_self R]

theorem poisson_nonneg_on_circle
    (hζ : ζ ∈ Metric.sphere 0 |R|) : 0 ≤ poissonKernel 0 z ζ := by
  have hz' : 𝕫 < R := 𝔞
  have hζ' : ‖ζ‖ = R := by simpa [abs_of_pos <| (norm_nonneg z).trans_lt hz'] using hζ
  simp only [poissonKernel_def, sub_zero]
  exact div_nonneg (by nlinarith [norm_nonneg z]) <| sq_nonneg _

/-- The elementary Poisson Jensen inequality for the squared norm of a holomorphic function. -/
theorem norm_sq_le_circleAverage_poisson 
    (hg : DiffContOnCl ℂ g (Metric.ball 0 R)) :
    𝕘 ≤ Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * ‖g ζ‖ ^ 2) 0 R := by
  have hR := Metric.pos_of_mem_ball hzR
  have hs : Metric.sphere 𝟎 |R| ⊆ closure (Metric.ball 0 R) := by
    rw [closure_ball 0 hR.ne', abs_of_pos hR]
    exact Metric.sphere_subset_closedBall
  let H : 𝕋 := fun ζ ↦ (2 * star (g z)) * g ζ - ((𝕘 : ℝ) : ℂ)
  have hH : DiffContOnCl ℂ H (Metric.ball 0 R) := (hg.const_smul <| 2 * star (g z)).sub_const _
  have hi : CircleIntegrable (poissonKernel 0 z • H) 0 R :=
    ((continuousOn_poisson_circle hzR).smul <| hH.continuousOn.mono hs).circleIntegrable'
  have h := Complex.reCLM.circleAverage_comp_comm hi
  rw [hH.circleAverage_poissonKernel_smul hzR] at h
  simp only [Function.comp_def, Complex.reCLM_apply, Pi.smul_apply', Complex.real_smul,
    Complex.re_ofReal_mul] at h
  rw [show 𝕘 = (H z).re by simp [H, Complex.sq_norm, Complex.normSq_apply]; ring, ← h]
  apply Real.circleAverage_mono ((continuousOn_poisson_circle hzR).mul
    (Complex.continuous_re.comp_continuousOn <| hH.continuousOn.mono hs)).circleIntegrable'
    ((continuousOn_poisson_circle hzR).mul <| (hg.continuousOn.mono hs).norm.pow 2).circleIntegrable'
  intro ζ hζ
  refine mul_le_mul_of_nonneg_left ?_ <| poisson_nonneg_on_circle hzR hζ
  simp [H, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg <| (g ζ).re - (g z).re, sq_nonneg <| (g ζ).im - (g z).im]

end

-- FILE BergmanWeakType.Weighted.PolarKernel
section
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Pure radial and angular derivatives of the weighted kernel -/

variable (q a b r θ : ℝ)
def radialComponent : ℝ := a * cos θ + b * sin θ
def angularComponent : ℝ := b * cos θ - a * sin θ

def polarDenominator : ℝ :=
  𝔟 * 𝕣 - 2 * r * 𝕒 + 1

def polarKernel : ℝ := 𝕤 ^ q

def polarKernelR : ℝ :=
  2 * q * (𝔟 * r - 𝕒) * 𝕄 polarKernel 𝔔

def polarKernelRR : ℝ :=
  2 * q * 𝔟 * 𝕄 polarKernel 𝔔 +
    4 * q * 𝔔 * (𝔟 * r - 𝕒) ^ 2 *
      𝕄 polarKernel (q - 2)

def polarKernelT : ℝ :=
  -2 * q * r * 𝕥 * 𝕄 polarKernel 𝔔

def polarKernelTT : ℝ :=
  2 * q * r * 𝕒 * 𝕄 polarKernel 𝔔 +
    4 * q * 𝔔 * 𝕣 * 𝕥 ^ 2 * 𝕄 polarKernel (q - 2)

theorem component_norm_sq :
    𝕒 ^ 2 + 𝕥 ^ 2 = a ^ 2 + b ^ 2 := by
  simp only [radialComponent, angularComponent]
  linear_combination 𝔟 * sin_sq_add_cos_sq θ

theorem polarDenominator_pos {r a b} (hr : 𝕣 < 1)
    (hw : a ^ 2 + b ^ 2 ≤ 1) (θ) : 0 < 𝕤 := by
  have := component_norm_sq a b θ
  have : r * 𝕒 < 1 := by
    nlinarith
  unfold polarDenominator
  nlinarith

variable (hd : 0 < 𝕤)
include hd

theorem polarKernel_hasDerivAt_r :
    HasDerivAt (𝓊 polarKernel q a b u θ) 𝕄 polarKernelR q r := by
  convert ((((hasDerivAt_pow 2 r).const_mul 𝔟).sub <| ((hasDerivAt_id r).mul_const
    𝕒).const_mul 2).add_const 1).rpow_const (Or.inl <| ne_of_gt (by simp [polarDenominator] at hd ⊢; linarith)) using 1
  · ext; simp [polarKernel, polarDenominator]; ring_nf
  · simp [polarKernelR, polarKernel, polarDenominator]; ring

theorem polarKernelR_hasDerivAt_r :
    HasDerivAt (𝓊 polarKernelR q a b u θ) 𝕄 polarKernelRR q r := by
  convert ((((hasDerivAt_id r).const_mul 𝔟).sub_const <| 𝕒).mul
    (𝕄 polarKernel_hasDerivAt_r 𝔔 hd)).const_mul (2 * q) using 1
  · ext u; simp [polarKernelR]; ring
  · simp [polarKernelRR, polarKernelR]; ring

theorem polarKernel_hasDerivAt_t :
    HasDerivAt (polarKernel q a b r) 𝕄 polarKernelT q θ := by
  convert (((((hasDerivAt_cos θ).const_mul a).add <| (hasDerivAt_sin θ).const_mul b).const_mul
    (-2 * r)).const_add (𝔟 * 𝕣 + 1)).rpow_const (Or.inl <| ne_of_gt (by simp [polarDenominator, radialComponent] at hd ⊢; linarith)) using 1
  · ext; simp [polarKernel, polarDenominator, radialComponent]; ring_nf
  · simp [polarKernelT, polarKernel, polarDenominator, radialComponent, angularComponent]; ring

theorem polarKernelT_hasDerivAt_t :
    HasDerivAt (polarKernelT q a b r) 𝕄 polarKernelTT q θ := by
  convert ((((hasDerivAt_cos θ).const_mul b).sub <| (hasDerivAt_sin θ).const_mul a).mul
    (𝕄 polarKernel_hasDerivAt_t 𝔔 hd)).const_mul (-2 * q * r) using 1
  · ext u; simp [polarKernelT, angularComponent]; ring
  · simp [polarKernelTT, polarKernelT, radialComponent, angularComponent]; ring

/-- The weighted elliptic equation in polar coordinates, with no mixed derivatives. -/
theorem polarKernel_equation (k) (hr : r ≠ 0) (ht : 𝔯 ≠ 0) :
    𝕄 polarKernelRR 𝔨 + 𝕄 polarKernelR 𝔨 / r +
      𝕄 polarKernelTT 𝔨 / 𝕣 -
      𝔨₁ * 𝕄 polarKernelR 𝔨 -
      𝔨₂ * 𝕄 polarKernel 𝔨 =
        -(k ^ 2 * (1 - 𝔟)) /
          (𝔯 * 𝕤) * 𝕄 polarKernel 𝔨 := by
  have hB : 𝕥 ^ 2 = a ^ 2 + b ^ 2 - 𝕒 ^ 2 := by
    linarith [component_norm_sq a b θ]
  simp only [polarKernelRR, polarKernelR, polarKernelTT, polarKernel, show -k / 2 - 2 = -k / 2 - 1 - 1 by ring, (rpow_sub_one hd.ne' <| -k / 2 - 1), (rpow_sub_one hd.ne' 𝔨), hB]
  field_simp
  unfold polarDenominator
  ring

omit hd in
theorem polarKernel_eq_norm_weightedKernel (w) :
    polarKernel 𝔥 w.re w.im r θ = ‖weightedKernel α (𝔠ₘ θ) w‖ := by
  have : polarDenominator w.re w.im r θ = ‖1 - 𝔠ₘ θ * star w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, polarDenominator, radialComponent, circleMap]
    linear_combination -𝕣 * (w.re ^ 2 + w.im ^ 2) * sin_sq_add_cos_sq θ
  rw [polarKernel, this, norm_weightedKernel, ← rpow_natCast_mul 𝔬]
  ring_nf

end

-- FILE BergmanWeakType.Weighted.PolarPotential
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Polar differential equations under compact source integrals -/

variable {X : Type*} [TopologicalSpace X]

def polarSourceDomain (K : Set X) : Set ((ℝ × ℝ) × X) :=
  {p | p.1.1 ^ 2 < 1 ∧ p.2 ∈ K}

abbrev SourceCont (K : Set X) (a b : 𝖃) (H : 𝔊) : Prop :=
  ContinuousOn (fun p : (ℝ × ℝ) × X ↦ H (a p.2) (b p.2) p.1.1 p.1.2) (polarSourceDomain K)

abbrev PolarCont (F : 𝔉) : Prop := ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (J₁ ×ˢ univ)

abbrev PolarDR (F G : 𝔉) : Prop := 𝔄 ∀ θ, HasDerivAt (F · θ) 𝖗 G r

abbrev PolarDT (F G : 𝔉) : Prop := 𝔄 ∀ θ, HasDerivAt (F r) 𝖗 G θ

section

variable {K : Set X} {a b : 𝖃} (ha : Continuous a) (hb : Continuous b)
  (hsource : 𝔄ₖ 𝖘 ≤ 1) (q : ℝ)

include ha hb hsource

theorem continuousOn_polarKernel_source :
    𝖈 (polarKernel q) :=
  ContinuousOn.rpow_const (by unfold polarDenominator radialComponent; fun_prop)
    𝒫 Or.inl (polarDenominator_pos hp.1 (hsource p.2 hp.2) p.1.2).ne'

local macro "kc" : tactic => `(tactic| (
  have := continuousOn_polarKernel_source ha hb hsource 𝔔
  have := continuousOn_polarKernel_source ha hb hsource (q - 2)
  simp only [SourceCont, polarKernelR, polarKernelRR, polarKernelT, polarKernelTT, radialComponent,
    angularComponent]
  fun_prop))

theorem continuousOn_polarKernelR_source :
    𝖈 (polarKernelR q) := by kc

theorem continuousOn_polarKernelRR_source :
    𝖈 (polarKernelRR q) := by kc

theorem continuousOn_polarKernelT_source :
    𝖈 (polarKernelT q) := by kc

theorem continuousOn_polarKernelTT_source :
    𝖈 (polarKernelTT q) := by kc

end

section

variable [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

def polarIntegral (H : 𝔊) (a b : 𝖃)
    (μ : Measure X) (f : 𝖃) (r θ : ℝ) : ℝ :=
  ∫ w, H 𝔛 𝔜 r θ * 𝕱 ∂μ

def polarOperator (k : ℝ) (a b : 𝖃) (μ : Measure X) (f : 𝖃) (r θ : ℝ) : ℝ :=
  ℐ (polarKernelRR 𝔨) r θ +
    ℐ (polarKernelR 𝔨) r θ / r +
    ℐ (polarKernelTT 𝔨) r θ / 𝕣 -
    𝔨₁ * ℐ (polarKernelR 𝔨) r θ -
    𝔨₂ * ℐ (polarKernel 𝔨) r θ

variable {K : Set X} {a b : 𝖃} {μ : Measure X} {f : 𝖃}
  (hK_ : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hf_ : Integrable f μ)
  {H H' : 𝔊}

include hK_ hμ hf_
section
variable (hH : 𝖈 H) (hH' : 𝖈 H')
include hH
theorem continuousOn_polarIntegral_unit :
    PolarCont (polarIntegral H a b μ f) := by
  rintro p ⟨hp, -⟩
  obtain ⟨S, hS, hpS, hsub⟩ := exists_compact_subset
    (isOpen_lt (continuous_fst.pow 2) continuous_const : IsOpen {p : ℝ × ℝ | p.1 ^ 2 < 1})
    (show p.1 ^ 2 < 1 by nlinarith [hp.1, hp.2])
  exact ((𝕐 continuousOn_integral_mul_of_compact hS (hH.mono 𝒫 ⟨hsub hp.1, hp.2⟩)
    ).continuousAt (mem_interior_iff_mem_nhds.mp hpS)).continuousWithinAt

variable (hr_ : 𝕣 < 1) (θ : ℝ)
include hH' hr_
theorem polarIntegral_hasDerivAt_r
    (hd : 𝔄ₖ ∀ r θ, 𝕣 < 1 →
      HasDerivAt (𝓊 H 𝔛 𝔜 u θ) (H' 𝔛 𝔜 r θ) r) :
    HasDerivAt (𝓊 ℐ H u θ) (ℐ H' r θ) r := by
  obtain ⟨l, u, -, hSr, htarget⟩ := exists_Icc_mem_subset_of_mem_nhds
    ((isOpen_lt 𝔣 continuous_const).mem_nhds hr_ : {u : ℝ | u ^ 2 < 1} ∈ 𝓝 r)
  have hmap : MapsTo (fun p ↦ ((p.1, θ), p.2)) (Icc l u ×ˢ K) (polarSourceDomain K) :=
    𝒫 ⟨htarget hp.1, hp.2⟩
  exact 𝕐 hasDerivAt_integral_mul_of_continuousOn_compact isCompact_Icc hSr
    (hH.comp 𝔣 hmap) (hH'.comp 𝔣 hmap)
    (fun w hw u hu ↦ hd w hw u θ <| htarget hu)

theorem polarIntegral_hasDerivAt_t
    (hd : 𝔄ₖ ∀ r θ, 𝕣 < 1 →
      HasDerivAt (H 𝔛 𝔜 r) (H' 𝔛 𝔜 r θ) θ) :
    HasDerivAt (polarIntegral H a b μ f r) (ℐ H' r θ) θ := by
  have hmap : MapsTo (fun p ↦ ((r, p.1), p.2))
      (Metric.closedBall θ 1 ×ˢ K) (polarSourceDomain K) := fun _ hp ↦ ⟨hr_, hp.2⟩
  exact 𝕐 hasDerivAt_integral_mul_of_continuousOn_compact (isCompact_closedBall θ 1)
    (Metric.closedBall_mem_nhds θ one_pos) (hH.comp 𝔣 hmap)
    (hH'.comp 𝔣 hmap) (fun w hw u _ ↦ hd w hw r u hr_)
end
variable (ha : Continuous a) (hb : Continuous b)
  (hsource : 𝔄ₖ 𝖘 ≤ 1) (q : ℝ) {r : ℝ} (hr_ : 𝕣 < 1) (θ : ℝ)

include ha hb hsource hr_

local macro "pk" g:ident h:ident h':ident d:ident : term =>
  `($g hK_ hμ hf_ ($h ha hb hsource q) ($h' ha hb hsource q)
    hr_ θ (fun w hw s t hs ↦ $d q _ _ s t (polarDenominator_pos hs (hsource w hw) t)))

theorem polarIntegral_kernel_hasDerivAt_r :
    HasDerivAt (𝓊 ℐ (polarKernel q) u θ)
      (ℐ (polarKernelR q) r θ) r :=
  pk polarIntegral_hasDerivAt_r continuousOn_polarKernel_source continuousOn_polarKernelR_source polarKernel_hasDerivAt_r

theorem polarIntegral_kernelR_hasDerivAt_r :
    HasDerivAt (𝓊 ℐ (polarKernelR q) u θ)
      (ℐ (polarKernelRR q) r θ) r :=
  pk polarIntegral_hasDerivAt_r continuousOn_polarKernelR_source continuousOn_polarKernelRR_source polarKernelR_hasDerivAt_r

theorem polarIntegral_kernel_hasDerivAt_t :
    HasDerivAt (polarIntegral (polarKernel q) a b μ f r)
      (ℐ (polarKernelT q) r θ) θ :=
  pk polarIntegral_hasDerivAt_t continuousOn_polarKernel_source continuousOn_polarKernelT_source polarKernel_hasDerivAt_t

theorem polarIntegral_kernelT_hasDerivAt_t :
    HasDerivAt (polarIntegral (polarKernelT q) a b μ f r)
      (ℐ (polarKernelTT q) r θ) θ :=
  pk polarIntegral_hasDerivAt_t continuousOn_polarKernelT_source continuousOn_polarKernelTT_source polarKernelT_hasDerivAt_t

variable (k : ℝ) (hr0 : r ≠ 0)
include hr0
theorem polarIntegral_operator :
    𝔭ₒ =
    ∫ w, -(k ^ 2 * (1 - 𝖘)) / (𝔯 *
      polarDenominator 𝔛 𝔜 r θ) * polarKernel 𝔨 𝔛 𝔜 r θ * 𝕱 ∂μ := by
  have hi (G : 𝔊) (hG : ContinuousOn (fun p : (ℝ × ℝ) × X ↦ G (a p.2) (b p.2) p.1.1 p.1.2)
      (polarSourceDomain K)) : Integrable (𝓌 G 𝔛 𝔜 r θ * 𝕱) μ :=
    𝕐 integrable_mul_of_continuousOn_compact (hG.comp (f := 𝓌 ((r, θ), w)) 𝔣
      𝒲 ⟨hr_, hw⟩)
  have := hi _ <| continuousOn_polarKernel_source ha hb hsource 𝔨
  have := hi _ <| continuousOn_polarKernelR_source ha hb hsource 𝔨
  have := hi _ <| continuousOn_polarKernelRR_source ha hb hsource 𝔨
  have := hi _ <| continuousOn_polarKernelTT_source ha hb hsource 𝔨
  simp only [polarOperator, polarIntegral, ← integral_div, ← integral_const_mul]
  rw [← integral_add, ← integral_add, ← integral_sub, ← integral_sub]
  · refine integral_congr_ae (hμ.mono 𝒲 ?_)
    simp only [← 𝖜 polarKernel_equation r θ (polarDenominator_pos hr_ (hsource w hw) θ) k hr0
      𝔑]
    ring
  all_goals fun_prop

theorem polarIntegral_operator_nonpos (hfn : ∀ᵐ w ∂μ, 0 ≤ 𝕱) :
    𝔭ₒ ≤ 0 := by
  rw [polarIntegral_operator] <;> try assumption
  refine integral_nonpos_of_ae ?_
  filter_upwards [hμ, hfn] with w hw hfw
  have hd := polarDenominator_pos hr_ (hsource w hw) θ
  have := hsource w hw
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg 𝔑 𝔑) (rpow_nonneg hd.le _)) hfw

theorem polarIntegral_operator_boundary
    (hboundary : 𝔄ₖ 𝖘 = 1) :
    𝔭ₒ = 0 := by
  rw [polarIntegral_operator] <;> try assumption
  exact integral_eq_zero_of_ae <| hμ.mono 𝒲 𝔞

end


-- FILE BergmanWeakType.Weighted.QuotientCap
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Truncated angular means of normalized polar supersolutions -/

/-- A smooth approximation to `min x c`. -/
def smoothCap (ε c x : ℝ) : ℝ :=
  (x + c - √𝔢 + ε) / 2

/-- The derivative of the smooth truncation with respect to its input. -/
def smoothCapInputDeriv (ε c x : ℝ) : ℝ :=
  (1 - 𝔐 / √𝔢) / 2

theorem smoothCap_bounds (hε : 0 ≤ ε) :
    min x c ≤ 𝔰ₑ x ∧ 𝔰ₑ x ≤ min x c + ε / 2 := by
  have := Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε) : 𝔐 ^ 2 ≤ _)
  have : √𝔢 ≤ |x - c| + ε := Real.sqrt_le_iff.mpr
    ⟨𝔭, by nlinarith [sq_abs 𝔐, mul_nonneg (abs_nonneg 𝔐) hε]⟩
  unfold smoothCap
  rcases abs_cases 𝔐 with h | h <;> rcases min_cases x c with h' | h' <;>
    constructor <;> linarith

theorem smoothCapInputDeriv_nonneg : 0 ≤ smoothCapInputDeriv ε c x := by
  unfold smoothCapInputDeriv
  linarith [div_le_one_of_le₀ ((le_abs_self _).trans <| Real.abs_le_sqrt
    (le_add_of_nonneg_right (sq_nonneg ε))) (Real.sqrt_nonneg 𝔢)]

section
include hε
theorem hasDerivAt_smoothCap_input :
    HasDerivAt 𝔰ₑ (smoothCapInputDeriv ε c x) x := by
  unfold smoothCap
  have hn : 𝔐 ^ 2 + 𝕖 ≠ 0 := ne_of_gt 𝔑
  have hs := (((hasDerivAt_id x).sub_const c).pow 2 |>.add_const 𝕖).sqrt hn
  convert (((hasDerivAt_id x).add_const c).sub hs |>.add_const ε).div_const 2 using 1 <;>
    dsimp [smoothCapInputDeriv]
  ring

theorem hasDerivAt_smoothCapInputDeriv :
    HasDerivAt (smoothCapInputDeriv ε c)
      (-𝕖 / (2 * Real.sqrt 𝔢 ^ 3)) x := by
  have hp : 0 < 𝔐 ^ 2 + 𝕖 := 𝔑
  unfold smoothCapInputDeriv
  convert ((((hasDerivAt_id x).sub_const c).div ((((hasDerivAt_id x).sub_const c).pow 2 |>.add_const 𝕖).sqrt hp.ne') (Real.sqrt_pos.mpr hp).ne').const_sub 1).div_const 2 using 1 <;> dsimp
  have heq := Real.sq_sqrt hp.le
  field_simp
  nlinarith

end
def angularMean (F : 𝔉) (r : ℝ) : ℝ :=
  τ⁻¹ * ∫ θ in 𝟘..2 * π, 𝖗 F

theorem continuousOn_angularMean {F} {S}
    (hF : ContinuousOn (fun p ↦ F p.1 p.2) (S ×ˢ univ)) :
    ContinuousOn (angularMean F) S := by
  have hc : Continuous (fun p : S × ℝ ↦ F p.1 p.2) := by
    apply continuousOn_univ.mp
    apply hF.comp (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd).continuousOn
    simp
  rw [continuousOn_iff_continuous_domRestrict]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hc 0 τ).const_mul _

theorem hasDerivAt_angularMean {F Fr} (hr : 𝕀)
    (hF : PolarCont F)
    (hFr : PolarCont Fr)
    (hd : PolarDR F Fr) :
    HasDerivAt (angularMean F) (angularMean Fr r) r := by
  have hsub : Icc (r / 2) ((r + 1) / 2) ⊆ Ioo 0 1 := by grind
  have hS : Icc (r / 2) ((r + 1) / 2) ×ˢ Icc 𝟘 τ ⊆ J₁ ×ˢ univ := by grind
  unfold angularMean
  simpa only [mul_one, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le two_pi_pos.le] using
    ((hasDerivAt_integral_mul_of_continuousOn_compact (μ := volume.restrict <| Icc 0 τ) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) (integrable_const (1)) isCompact_Icc (Icc_mem_nhds 𝔞
    𝔤) (hF.mono hS) (hFr.mono hS)
    fun θ _ u hu ↦ hd u (hsub hu) θ).const_mul τ⁻¹)

/-- A polar divergence inequality with periodic angular derivative makes the angular mean
nonincreasing, including at the origin. -/
theorem antitoneOn_angularMean_of_polar_flux {G Gr Grr Gt Gtt} {w w' : 𝕗}
    (hG : PolarCont G)
    (hGr : PolarCont Gr)
    (hGrr : PolarCont Grr)
    (hGtt : PolarCont Gtt)
    (hGd : PolarDR G Gr)
    (hGrd : PolarDR Gr Grr)
    (hGtd : PolarDT Gt Gtt)
    (hperiod : 𝔄 Gt r τ = Gt r 0)
    (hw : ContinuousOn w J₁) (hwd : 𝔄 HasDerivAt w (w' r) r)
    (hwpos : 𝔄 0 < w r)
    (hineq : 𝔄 ∀ θ,
      r * w r * 𝖗 Grr + (w r + r * w' r) * 𝖗 Gr + (w r / r) * 𝖗 Gtt ≤ 0) :
    AntitoneOn (angularMean G) J₁ := by
  have hi {H} (hH : PolarCont H)
      {r} (hr : 𝕀) : IntervalIntegrable (H r) volume 0 τ :=
    (continuousOn_univ.mp <| hH.comp (continuous_const.prodMk continuous_id).continuousOn
      𝒯 ⟨Ioo_subset_Ico_self hr, mem_univ θ⟩).intervalIntegrable _ _
  have hΦ := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1)
    ((continuousOn_id.mul hw).mul <| continuousOn_angularMean hGr) (𝓡 by
      rw [interior_Ico] at hr
      exact (((hasDerivAt_id r).mul <| 𝖞 hwd).mul
        (hasDerivAt_angularMean hr hGr hGrr hGrd)).hasDerivWithinAt) 𝓡 by
    rw [interior_Ico] at hr
    have := intervalIntegral.integral_mono_on two_pi_pos.le
      ((((hi hGrr hr).const_mul _).add <| (hi hGr hr).const_mul _).add <| (hi hGtt hr).const_mul _)
      intervalIntegrable_const 𝒯 hineq r hr θ
    rw [intervalIntegral.integral_add (((hi hGrr hr).const_mul _).add <| (hi hGr hr).const_mul _)
      ((hi hGtt hr).const_mul _), intervalIntegral.integral_add ((hi hGrr hr).const_mul _)
      ((hi hGr hr).const_mul _)] at this
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (𝒯 hGtd r hr θ) (hi hGtt hr), 𝖞 hperiod] at this
    simp only [angularMean, Pi.mul_apply, id]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 two_pi_pos).le
      (this.trans_eq 𝔰)]
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) (continuousOn_angularMean hG)
    (𝓡 (hasDerivAt_angularMean 𝔞 hG hGr hGd).hasDerivWithinAt)
    𝓡 ?_
  rw [interior_Ico] at hr
  have := hΦ (left_mem_Ico.2 one_pos) (Ioo_subset_Ico_self hr) hr.1.le
  simp at this
  exact nonpos_of_mul_nonpos_right 𝔩 <| mul_pos hr.1 (𝖞 hwpos)

/-- Normalizing a polar supersolution by a positive radial solution makes the angular means
of its truncations decrease. -/
theorem antitoneOn_angularMean_min_quotient {F Fr Frr Ft Ftt}
    {J Jr Jrr : 𝕗} (k c)
    (hF : PolarCont F)
    (hFr : PolarCont Fr)
    (hFrr : PolarCont Frr)
    (hFt : PolarCont Ft)
    (hFtt : PolarCont Ftt)
    (hFd : PolarDR F Fr)
    (hFrd : PolarDR Fr Frr)
    (hFdt : PolarDT F Ft)
    (hFtd : PolarDT Ft Ftt)
    (hperiodF : 𝔄 F r τ = F r 0)
    (hperiodFt : 𝔄 Ft r τ = Ft r 0)
    (hJ : ContinuousOn J J₁) (hJr : ContinuousOn Jr J₁)
    (hJrr : ContinuousOn Jrr J₁)
    (hJd : 𝔄 HasDerivAt J (Jr r) r)
    (hJrd : 𝔄 HasDerivAt Jr (Jrr r) r)
    (hJpos : ∀ r ∈ J₁, 0 < J r)
    (hJode : 𝔄
      Jrr r + (1 / r - 𝔨₁) * Jr r - 𝔨₂ * J r = 0)
    (hFode : 𝔄 ∀ θ,
      𝖗 Frr + (1 / r - 𝔨₁) * 𝖗 Fr + 𝖗 Ftt / 𝕣 -
        𝔨₂ * 𝖗 F ≤ 0) :
    AntitoneOn (angularMean (fun r θ ↦ min 𝔮 c)) J₁ := by
  have h1 (r) (hr : 𝕀) : 0 < 𝔯 := by nlinarith [hr.1, hr.2]
  have hJ0 (r) (hr : 𝕀) := (hJpos r <| Ioo_subset_Ico_self hr).ne'
  intro r hr R hR hrR
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hc1 : Continuous (smoothCapInputDeriv ε c) :=
    continuous_iff_continuousAt.2 𝓍 (hasDerivAt_smoothCapInputDeriv hε).continuousAt
  have hcap : AntitoneOn (angularMean fun r θ ↦ 𝔰ₑ 𝔮) J₁ := by
    refine antitoneOn_angularMean_of_polar_flux (w := fun r ↦ 𝔯 ^ k * J r ^ 2) ?_ ?_ ?_ ?_
      (𝓡θ (hasDerivAt_smoothCap_input hε).comp r <| (𝖞 hFd θ).div (𝖞 hJd) (𝖞 hJ0))
      (𝓡θ ((hasDerivAt_smoothCapInputDeriv hε).comp r <| (𝖞 hFd θ).div (𝖞 hJd)
        (𝖞 hJ0)).mul ((((𝖞 hFrd θ).mul <| 𝖞 hJd).sub <| (𝖞 hFd θ).mul (𝖞 hJrd)).div
        ((𝖞 hJd).pow 2) 𝔞))
      (𝓡θ ((hasDerivAt_smoothCapInputDeriv (c := c) hε).comp θ <| (𝖞 hFdt θ).div_const (J r)).mul
        ((𝖞 hFtd θ).div_const <| J r)) (𝓡 𝔞)
      ((continuousOn_const.sub <| continuousOn_id.pow 2).rpow_const (𝓡 Or.inl
        (by nlinarith [hr.1, hr.2] : 0 < 𝔯).ne') |>.mul (hJ.pow 2))
      (𝓡 ((((hasDerivAt_id r).pow 2).const_sub 1).rpow_const <| Or.inl (𝖞 h1).ne').mul
        ((𝖞 hJd).pow 2)) (𝓡 by have := hJpos r (Ioo_subset_Ico_self hr); have := 𝖞 h1; positivity) 𝓡θ ?_
    any_goals unfold smoothCap
    all_goals try simp only [PolarCont, Pi.div_apply, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply,
      Function.comp_apply, id]
    any_goals fun_prop (disch := first | exact 𝒽 And.left | (intro p hp; have := hJpos _ (And.left hp); positivity) | (intro; positivity))
    have hr0 := hr.1
    have hJp := hJpos r <| Ioo_subset_Ico_self hr
    have h1r := 𝖞 h1
    have hd1 := smoothCapInputDeriv_nonneg (ε := ε) (c := c) (x := 𝔮)
    have hd2 : -𝕖 / (2 * √((𝖗 F / J r - c) ^ 2 + 𝕖) ^ 3) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg 𝔑 𝔭
    have hP := rpow_pos_of_pos h1r k
    rw [rpow_sub_one h1r.ne'] at *
    generalize smoothCapInputDeriv ε c 𝔮 = d1 at *
    generalize -𝕖 / (2 * √((𝖗 F / J r - c) ^ 2 + 𝕖) ^ 3) = d2 at *
    generalize 𝔯 ^ k = P at *
    linear_combination (norm := (field_simp; ring_nf; exact le_rfl)) (d1 * r * P * J r) * 𝖞 hFode θ
      - (d1 * r * P * 𝖗 F) * 𝖞 hJode
      + (r * P * J r ^ 2 * ((𝖗 Fr * J r - 𝖗 F * Jr r) / J r ^ 2) ^ 2
        + P * J r ^ 2 / r * (𝖗 Ft / J r) ^ 2) * hd2
  have hle (f g) {s d} (hf : Continuous (f s)) (hg : Continuous (g s))
      (h : ∀ θ, f s θ ≤ g s θ + d) : angularMean f s ≤ angularMean g s + d := by
    have := intervalIntegral.integral_mono_on two_pi_pos.le (𝖜 hf.intervalIntegrable)
      ((hg.add continuous_const).intervalIntegrable (μ := volume) 0 τ) 𝒯 h θ
    simp at this
    rw [intervalIntegral.integral_add (𝖜 hg.intervalIntegrable) intervalIntegrable_const] at this
    simp only [angularMean, intervalIntegral.integral_const, smul_eq_mul] at this ⊢
    field_simp
    linarith
  have hs : Continuous 𝔰ₑ := by unfold smoothCap; fun_prop
  have hq {s} (hs : s ∈ J₁) : Continuous 𝓉 F s θ / J s :=
    (continuousOn_univ.mp <| hF.comp (continuous_const.prodMk continuous_id).continuousOn
      𝒯 ⟨hs, mem_univ θ⟩).div_const _
  linarith [hcap hr hR hrR, hle (fun r θ ↦ min 𝔮 c) (fun r θ ↦ 𝔰ₑ 𝔮)
    ((hq hR).min continuous_const) 𝔣 (d := 0)
    𝓉 by simpa using (smoothCap_bounds hε.le).1, hle (fun r θ ↦ 𝔰ₑ 𝔮)
    (fun r θ ↦ min 𝔮 c) 𝔣 ((hq hr).min continuous_const)
    𝓉 (smoothCap_bounds hε.le).2]


-- FILE BergmanWeakType.Weighted.RadialLevel
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Distribution estimates from increasing truncations in a radial mass coordinate -/

theorem circleIntegrable_of_measurable_bounded {g : 𝕦} (hg : Measurable g)
    (hbound : ∀ z, ‖g z‖ ≤ M) (r) : CircleIntegrable g 0 r :=
  (Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (hg.comp (continuous_circleMap 0 r).measurable).aestronglyMeasurable
    (.of_forall 𝒽 hbound _)).intervalIntegrable

def radialCapMean (U : 𝕦) (ρ : 𝕗) (y c : ℝ) : ℝ :=
  circleAverage (𝓏 min (U z) c) 0 (ρ y)

def radialLevelFraction (U : 𝕦) (ρ : 𝕗) (t y : ℝ) : ℝ :=
  circleAverage (𝓏 if t * y < U z then (1 : ℝ) else 0) 0 (ρ y)

/-- Increasing cap means in the mass coordinate give the integrated level-set estimate. -/
theorem integral_mul_radialLevelFraction_le {U : 𝕦} (hU : Measurable U)
    (hUpos : ∀ z, 0 ≤ U z) {ρ} (hρ : Measurable ρ) 
    (hmono : ∀ c, MonotoneOn (fun y ↦ radialCapMean U ρ y c) (Ioo 0 1))
    (hbound : ∀ y ∈ I₁, ∀ c, radialCapMean U ρ y c ≤ M)
    {t} (ht : 0 ≤ t) :
    (𝔍ᵧ t * radialLevelFraction U ρ t y) ≤ M := by
  have hm {F : ℝ → 𝕦} (hF : Measurable (Function.uncurry F)) {B}
      (hB : ∀ y ∈ Icc 𝟘 1, ∀ z, ‖F y z‖ ≤ B) :
      IntegrableOn (fun y ↦ circleAverage (F y) 0 <| ρ y) ℌ := by
    refine Measure.integrableOn_of_bounded measure_Icc_lt_top.ne ?_
      ((ae_restrict_mem measurableSet_Icc).mono 𝒴 norm_circleAverage_le_circleAverage_norm.trans
        (circleAverage_mono_on_of_le_circle (circleIntegrable_of_measurable_bounded
        (hF.comp measurable_prodMk_left).norm (𝓏 by aesop) _)
        fun z _ ↦ hB y hy z))
    simp only [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le]
    exact (measurable_const.mul (StronglyMeasurable.integral_prod_right'
     
      (hF.comp <| measurable_fst.prodMk (circleMap.continuous.measurable.comp
        ((hρ.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable).measurable).aestronglyMeasurable
  have hC (c r) := circleIntegrable_of_measurable_bounded (hU.min measurable_const)
    (𝓏 abs_le.2 ⟨le_min ((neg_nonpos.2 <| abs_nonneg c).trans <| hUpos z)
      (neg_abs_le c), (𝖜 min_le_right).trans <| le_abs_self c⟩) r
  refine integral_le_of_finite_difference_domination ((hm
    (B := 1) (measurable_const.ite
      (measurableSet_lt 𝔣 <| hU.comp measurable_snd) measurable_const)
      fun y _ z ↦ by split_ifs <;> simp).const_mul t)
    (hm ((hU.comp measurable_snd).min 𝔣)
      fun y hy z ↦ by
        rw [Real.norm_of_nonneg <| le_min (hUpos z) (mul_nonneg ht hy.1)]
        exact (𝖜 min_le_right).trans <| mul_le_of_le_one_right ht hy.2)
    (𝒴 circleAverage_nonneg_of_nonneg fun z _ ↦ le_min (hUpos z) <| mul_nonneg ht hy.1.le)
    (𝒴 hbound y hy _) fun y h hy hh hyh ↦ ?_
  have := circleAverage_mono (CircleIntegrable.const_smul
    (circleIntegrable_of_measurable_bounded (M := 1)
    (measurable_const.ite (measurableSet_lt measurable_const hU) measurable_const)
    (𝓏 by aesop) (ρ 𝔒))) ((𝖜 hC).sub <| 𝖜 hC)
    fun z _ ↦ show (h * t) • (if t * 𝔒 < U z then 1 else 0) ≤
      min (U z) (t * 𝔒) - min (U z) (t * y) by
      simp only [min_def, smul_eq_mul]; split_ifs <;> nlinarith
  rw [circleAverage_smul, circleAverage_sub (𝖜 hC) <| 𝖜 hC] at this
  have := hmono (t * y) ⟨hy, 𝔩⟩ ⟨𝔩, hyh⟩ 𝔩
  simp only [radialLevelFraction, radialCapMean, smul_eq_mul] at *
  linarith


-- FILE BergmanWeakType.Weighted.Normalizer
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The circular boundary-kernel normalizer
The normalizer is the average of the actual positive boundary kernel. Its sharp
bound requires a circle change of variables and a beta integral; neither estimate
is included as a hypothesis or an axiom here.
-/

/-- Circular mean of the positive boundary kernel at radial coordinate `r`. -/
def normalizer (α r : ℝ) : ℝ :=
  𝔠ᵃ 𝔪

theorem normalizer_eq_circleAverage_radius (r) :
    𝕟 = Real.circleAverage 𝔬ₖ 𝔪 0 r := by
  simpa [normalizer] using
    (Real.circleAverage_eq_circleAverage_zero_one
      (f := 𝓏 ‖𝕆‖ ^ 𝔪) (c := 0)).symm

theorem normalizer_nonneg : 0 ≤ 𝕟 :=
  Real.circleAverage_nonneg_of_nonneg 𝒰 Real.rpow_nonneg 𝔬 _

theorem continuousOn_boundaryKernel_norm (p : ℝ) :
    ContinuousOn 𝔬ₖ p disk :=
  ContinuousOn.rpow_const 𝔣 𝒵
    .inl (norm_ne_zero_iff.2 <| sub_ne_zero.2 𝒷 by aesop)

theorem continuousOn_normalizer : ContinuousOn 𝕹 J₁ := by
  simp_rw [funext normalizer_eq_circleAverage_radius]
  exact Real.ContinuousOn.circleAverage ((continuousOn_boundaryKernel_norm _).mono
    𝒵 by simpa using hz.2) 𝓡 hr.1

include hα hr in
theorem normalizer_pos :
    0 < 𝕟 := by
  refine (Real.rpow_pos_of_pos (by positivity : 0 < 1 + |r|) 𝔪).trans_le ?_
  rw [normalizer_eq_circleAverage_radius, ← Real.circleAverage_const ((1 + |r|) ^ 𝔪) 0 r]
  refine Real.circleAverage_mono continuousOn_const.circleIntegrable'
    ((continuousOn_boundaryKernel_norm _).mono 𝒵 𝔞).circleIntegrable' 𝒵 ?_
  have h1 := norm_sub_norm_le (1) z
  have h2 := norm_sub_le 1 z
  simp_all
  exact Real.rpow_le_rpow_of_nonpos 𝔩 h2 𝔩

section
include hα
/-- Duplication expresses the proposed sharp constant in the boundary beta-integral form. -/
theorem gammaConstant_eq_boundaryGamma :
    𝔤ᵧ =
      2 ^ α * Real.Gamma 𝔞₂ /
        (Real.sqrt Real.pi * Real.Gamma 𝔄) := by
  have hG := Real.Gamma_mul_Gamma_add_half_of_pos <| show 0 < 𝔞₂ by linarith
  rw [show 𝔞₂ + 1 / 2 = 1 + 𝕙 by ring, show 2 * 𝔞₂ = α + 1 by ring,
    show 1 - α₁ = -α by ring] at hG
  have h2 : (2 : ℝ) ^ α * 2 ^ (-α) = 1 := by simp [← Real.rpow_add]
  have hb := (Real.Gamma_pos_of_pos <| show 0 < 1 + 𝕙 by linarith).ne'
  rw [gammaConstant, div_eq_div_iff (pow_ne_zero 2 hb) 𝔭]
  linear_combination (-2 ^ α * Real.Gamma 𝔄) * hG -
    Real.Gamma α₁ * √Real.pi * Real.Gamma 𝔄 * h2

theorem circleAverage_boundary_power :
    Real.circleAverage (fun ζ ↦ ‖1 - ζ‖ ^ α) 0 1 = 𝔤ᵧ := by
  rw [Real.circleAverage_def]
  have heq : (∫ θ in 𝟘..2 * Real.pi, ‖1 - circleMap 0 1 θ‖ ^ α) =
      2 ^ α * (∫ θ in 𝟘..2 * Real.pi, Real.sin (θ / 2) ^ α) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le 𝔭
    intro θ hθ
    have hs : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi 𝔤 𝔤
    simp [circleMap, norm_sub_rev, mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
      abs_of_nonneg hs, Real.mul_rpow zero_le_two hs]
  rw [heq, intervalIntegral.integral_comp_div (𝓉 Real.sin θ ^ α) 𝔫]
  simp
  rw [integral_sin_rpow hα, gammaConstant_eq_boundaryGamma hα]
  field_simp
  simp [Real.pi_pos.le]

end
theorem norm_boundaryKernel_circleMap_sq (r θ : ℝ) :
    ‖1 - ℛ * circleMap 0 1 θ‖ ^ 2 = 𝕔 := by
  simp [Complex.sq_norm, Complex.normSq_apply, circleDenominator, circleMap]
  linear_combination 𝕣 * Real.sin_sq_add_cos_sq θ

theorem norm_boundaryKernel_circleMap_rpow (p r θ : ℝ) :
    ‖1 - ℛ * circleMap 0 1 θ‖ ^ p =
      𝕔 ^ 𝔎 := by
  rw [← norm_boundaryKernel_circleMap_sq, ← Real.rpow_natCast, ← Real.rpow_mul 𝔬]
  ring_nf

include hr in
theorem circleAverage_radialKernel_eq_arcsine (p : ℝ) :
    𝔠ᵃ p =
      Real.pi⁻¹ * (𝔍ᵢ
        𝕏 ^ 𝔎 / Real.sqrt 𝔵) := by
  have hc : Continuous (𝓉 𝕔 ^ 𝔎) := by
    apply Continuous.rpow_const <| by unfold circleDenominator; fun_prop
    exact 𝓉 Or.inl (circleDenominator_pos hr
      ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).ne'
  have heq : (∫ θ in Real.pi..2 * Real.pi,
      𝕔 ^ 𝔎) =
      ∫ θ in 𝟘..Real.pi, 𝕔 ^ 𝔎 := by
    conv_lhs => arg 1; intro θ; rw [← Real.cos_two_pi_sub θ]
    rw [intervalIntegral.integral_comp_sub_left
      (𝓉 𝕔 ^ 𝔎), sub_self,
      show 2 * Real.pi - Real.pi = Real.pi by ring]
  rw [Real.circleAverage_def]
  simp_rw [norm_boundaryKernel_circleMap_rpow]
  rw [← intervalIntegral.integral_add_adjacent_intervals
   
    (𝖜 hc.intervalIntegrable) (𝖜 hc.intervalIntegrable), heq,
    integral_cos_arcsine (𝓍 𝕏 ^ 𝔎)]
  ring

include hr in
/-- The exact Möbius identity for the weighted boundary-kernel normalizer. -/
theorem radialMass_mul_normalizer :
    𝔯 ^ α₁ * 𝕟 =
      𝔠ᵃ α := by
  rw [normalizer, circleAverage_radialKernel_eq_arcsine hr _,
    circleAverage_radialKernel_eq_arcsine hr _, ← integral_circleDenominator_transform (α := α) hr]
  ring

theorem circleAverage_norm_sq_mono 
    (hr : 0 ≤ r) (hrR : r < R) (hg : 𝕮 g (Metric.closedBall 0 R)) :
    Real.circleAverage (𝓏 𝕘) 0 r ≤
      Real.circleAverage (𝓏 𝕘) 0 R := by
  have hv := hg.continuousOn.norm.pow 2
  have hi : CircleIntegrable (𝓏 𝕘) 0 R :=
    (hv.mono 𝒵 by simp_all [abs_of_nonneg <| hr.trans hrR.le]).circleIntegrable'
  have habs : |r| < |R| := 𝔤
  rw [← circleAverage_poissonExtension hi habs]
  apply Real.circleAverage_mono (hv.mono 𝒵 by simp_all [abs_of_nonneg hr]; linarith).circleIntegrable'
    ((continuousOn_poissonExtension hi).mono 𝒵 by aesop).circleIntegrable'
  intro z hz
  exact norm_sq_le_circleAverage_poisson (by simp_all [abs_of_nonneg hr]) <| hg.diffContOnCl_ball subset_rfl

theorem circleAverage_boundaryPower_mono (α : ℝ) 
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) :
    Real.circleAverage 𝔬ₖ α 0 r ≤
      Real.circleAverage 𝔬ₖ α 0 R := by
  rcases hrR.eq_or_lt with rfl | hrR
  · rfl
  have h := circleAverage_norm_sq_mono hr hrR (g := 𝓏 𝕆 ^ ((𝕙 : ℝ) : ℂ))
    (DifferentiableOn.cpow_const 𝔣 𝒵
      .inl (by simp at hz; simp; linarith [Complex.re_le_norm z]))
  simp only [Complex.norm_cpow_real, ← Real.rpow_natCast, ← Real.rpow_mul 𝔬] at h
  ring_nf at h ⊢
  exact h


-- FILE BergmanWeakType.Boundary.HalfDiskIntegral
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The half-disk power integral in the boundary concentration limit -/

/-- The limiting density after blowing up a boundary cap at the point one. -/
def halfDiskPower (α : ℝ) (z : ℂ) : ℝ :=
  if 0 < z.re then (2 * z.re) ^ α else 0

theorem integral_halfDiskPower (hα : 0 ≤ α) :
    (∫ z, halfDiskPower α z ∂diskArea) = 𝔤ᵧ / α₂ := by
  have hm : Measurable (halfDiskPower α) :=
    Measurable.ite (measurableSet_lt measurable_const Complex.measurable_re) 𝔣
      measurable_const
  have hb (z) : ‖halfDiskPower α z‖ ≤ (2 * 𝕫) ^ α := by
    unfold halfDiskPower
    split_ifs
    · rw [norm_of_nonneg 𝔭]
      exact rpow_le_rpow 𝔭 (by linarith [Complex.re_le_norm z]) hα
    · simp [rpow_nonneg]
  have hc {r} (hr : 𝕀) :
      circleAverage (halfDiskPower α) 0 r = r ^ α * 𝔤ᵧ / 2 := by
    set H := 𝓉 halfDiskPower α <| 𝔠ₘ (θ + -(π / 2))
    have hpoint (θ) : H θ = if 0 < sin θ then 𝔏 ^ α * sin θ ^ α else 0 := by
      simp only [H, halfDiskPower, circleMap_zero_re, ← sub_eq_add_neg, cos_sub_pi_div_two,
        mul_pos_iff_of_pos_left hr.1]
      split_ifs with hs
      · rw [← mul_rpow 𝔤 hs.le, mul_assoc]
      · rfl
    have hi (a b) : IntervalIntegrable H volume a b :=
      (Measure.integrableOn_of_bounded measure_Icc_lt_top.ne (hm.comp
        𝔣).aestronglyMeasurable (.of_forall 𝓉 by simpa using hb <| 𝔠ₘ (θ + -(π / 2)))
          ).intervalIntegrable
    rw [circleAverage_eq_integral_add <| -(π / 2), smul_eq_mul,
      ← intervalIntegral.integral_add_adjacent_intervals (hi 0 π) 𝔞,
      intervalIntegral.integral_congr_Ioo_of_le pi_pos.le
        fun θ hθ ↦ by rw [hpoint, ite_eq_left <| sin_pos_of_pos_of_lt_pi hθ.1 hθ.2],
      intervalIntegral.integral_congr_Ioo_of_le (b := 2 * π) (by linarith [pi_pos])
        fun θ hθ ↦ by
          have := sin_nonpos_of_nonpos_of_neg_pi_le (x := θ - 2 * π) 𝔤
            𝔤
          rw [hpoint, ite_eq_right 𝔞],
      intervalIntegral.integral_zero, add_zero, intervalIntegral.integral_const_mul, integral_sin_rpow 𝔩,
      mul_rpow 𝔰 hr.1.le,
      gammaConstant_eq_boundaryGamma 𝔩]
    field_simp
    simp [sq_sqrt pi_pos.le]; ring
  rw [integral_diskArea_eq_circleAverage <| (integrable_const (2 ^ α)).mono'
    hm.aestronglyMeasurable (ae_mem_disk.mono 𝒵 (hb z).trans (rpow_le_rpow
      𝔭 (by linarith [mem_disk_iff.1 hz]) hα)),
    setIntegral_congr_fun measurableSet_Ioo (g := fun r ↦ 𝔤ᵧ * r ^ α₁)
      𝓡 by simp only [hc hr, rpow_add hr.1, rpow_one]; ring,
    integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl 𝔩), one_rpow, zero_rpow 𝔩]
  ring


-- FILE BergmanWeakType.Boundary.CapMass
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The mass of small caps at the boundary of the disk -/

def capProfile (α R : ℝ) (u : ℂ) : ℝ :=
  if R * 𝖚 < 2 * u.re then (2 * u.re - R * 𝖚) ^ α else 0

theorem tendsto_rescaled_boundaryCap_real (hα : 0 ≤ α) :
    Filter.Tendsto (fun R ↦ R ^ 𝔪 * (𝔴).real 𝔅)
      (𝓝[>] 𝟘) (𝓝 (boundaryConstant α)) := by
  rw [boundaryConstant, div_mul_comm, mul_comm, ← integral_halfDiskPower hα]
  refine ((tendsto_integral_filter_of_dominated_convergence (F := capProfile α) (𝒽 2 ^ α)
    (.of_forall fun R ↦ ?_) ?_ (integrable_const _) (.of_forall 𝓊 ?_)).const_mul _).congr' ?_
  · exact (Measurable.ite (measurableSet_lt 𝔣 𝔣) 𝔣
      measurable_const).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with R hR
    filter_upwards [ae_mem_disk] with u hu
    unfold capProfile
    split_ifs with h
    · rw [Real.norm_of_nonneg <| Real.rpow_nonneg 𝔩 _]
      refine Real.rpow_le_rpow 𝔩 ?_ hα
      nlinarith [Complex.re_le_norm u, mul_nonneg (le_of_lt hR) <| sq_nonneg ‖u‖, mem_disk_iff.1 hu]
    · simp; positivity
  · unfold halfDiskPower capProfile
    split_ifs with hu
    · have := (continuous_id.mul continuous_const).continuousAt.eventually_lt
        (continuousAt_const) (by simpa : 0 * 𝖚 < 2 * u.re)
      refine Filter.Tendsto.congr' (eventually_nhdsWithin_of_eventually_nhds <| this.mono
        fun R hR ↦ (if_pos hR).symm) (tendsto_nhdsWithin_of_tendsto_nhds ?_)
      simpa using ((by fun_prop : Continuous fun R ↦ 2 * u.re - R * 𝖚).rpow_const
        𝒽 Or.inr hα).tendsto 0
    · exact tendsto_const_nhds.congr' <| eventually_nhdsWithin_of_forall fun R (hR : 0 < R) ↦
        (if_neg 𝔑).symm
  filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
  have hc := Measure.integral_comp_smul_of_nonneg volume
    (𝓏 𝔦ᵢ <| 𝕆) R (hR := hR.le)
  rw [Complex.finrank_real_complex, integral_sub_left_eq_self _ volume 1] at hc
  have hi (u) : 𝔦ᵢ (1 - R • u) =
      R ^ α * disk.indicator (capProfile α R) u := by
    have h : ‖1 - R * u‖ ^ 2 = 1 - 2 * R * u.re + R ^ 2 * 𝖚 := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have : 1 - R * u ∈ boundaryCap R ↔ u ∈ disk ∧ R * 𝖚 < 2 * u.re := by
      simp only [boundaryCap, Set.mem_inter_iff, mem_disk_iff, Metric.mem_ball, dist_eq_norm,
        sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
        nlinarith [norm_nonneg <| 1 - R * u]
    simp only [Set.indicator, capProfile]
    split_ifs <;> simp_all
    rw [← Real.mul_rpow hR.le 𝔩]
    ring_nf
  have hm : (𝔴).real 𝔅 =
      α₁ * ∫ z, 𝔦ᵢ z ∂area := by
    rw [← integral_indicator_one measurableSet_boundaryCap, integral_weightedArea_eq_diskArea
      𝔩, diskArea, ← integral_indicator measurableSet_disk, ← integral_const_mul]
    refine integral_congr_ae <| .of_forall 𝓏 ?_
    simp only [Set.indicator]; split_ifs <;> simp_all [boundaryCap] <;> linarith
  simp only [hi, integral_const_mul, integral_indicator measurableSet_disk, smul_eq_mul] at hc
  simp only [hm, diskArea, area, Measure.restrict_smul, integral_smul_measure, smul_eq_mul]
  rw [Real.rpow_neg hR.le, Real.rpow_add hR, Real.rpow_two]
  field_simp at hc ⊢
  linear_combination hc


-- FILE BergmanWeakType.Boundary.Sharpness
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The explicit boundary lower bound for the complex weighted projection -/

/-- The boundary concentration lower bound uses ordinary integrable complex inputs. -/
theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤
      weakTypeConstant 𝔴 𝔓 := by
  have hα' : -1 < α := 𝔩
  let := weightedArea_isProbabilityMeasure hα'
  refine le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_rescaled_boundaryCap_real hα)) ?_
  filter_upwards [self_mem_nhdsWithin] with R hR
  rw [Function.comp_apply, ENNReal.ofReal_mul <| Real.rpow_nonneg hR.le _, measureReal_def,
    ENNReal.ofReal_toReal 𝔈]
  exact boundaryCap_le_weightedProjection_constant hα' hR


-- FILE BergmanWeakType.Weighted.NormalizerEndpoint
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The sharp bound and endpoint limit of the weighted circular normalizer -/

open scoped Interval in
section
include hα
theorem tendsto_circleAverage_boundaryPower :
    Tendsto (fun r : ℝ ↦ 𝔠ᵃ α)
      (𝓝[<] 1) (𝓝 (𝔤ᵧ)) := by
  have key : 𝔤ᵧ =
      Real.circleAverage (fun ζ ↦ ‖1 - ((1 : ℝ) : ℂ) * ζ‖ ^ α) 0 1 := by
    simp [circleAverage_boundary_power hα]
  have hi : IntervalIntegrable (𝓉 circleDenominator 1 (cos θ) ^ 𝕙) volume 0 τ := by
    by_contra hn
    refine (gammaConstant_pos hα).ne' ?_
    simp only [key, Real.circleAverage_def, norm_boundaryKernel_circleMap_rpow,
      intervalIntegral.integral_undef hn, smul_zero]
  simp only [key, Real.circleAverage_def, norm_boundaryKernel_circleMap_rpow]
  refine Tendsto.const_mul _ ?_
  unfold circleDenominator at hi ⊢
  rcases le_or_gt 0 α with hα0 | hα0
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (Continuous.rpow_const 𝔣 𝒽 Or.inr 𝔩) _ _).tendsto 1)
  have hae : ∀ᵐ θ : ℝ, θ ∈ Ι 0 τ → 0 < 𝔠₁ 1 := by
    filter_upwards [Measure.ae_ne volume τ] with θ hθ h
    rw [uIoc_of_le 𝔭] at h
    linarith [(cos_le_one θ).lt_of_ne <| mt (cos_eq_one_iff_of_lt_of_lt 𝔤
      (h.2.lt_of_ne hθ)).1 h.1.ne']
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (𝓉 (1 / 2 : ℝ) ^ 𝕙 * 𝔠₁ 1 ^ 𝕙)
    (.of_forall fun r ↦ (Measurable.pow_const 𝔣 _).aestronglyMeasurable) ?_ (hi.const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
    filter_upwards [hae] with θ hθ h
    have he : 1 / 2 * 𝔠₁ 1 ≤ 𝔠₁ r := by
      nlinarith [mul_nonneg (by linarith [hr.1] : 0 ≤ 2 * r - 1) <| sub_nonneg.2 (cos_le_one θ),
        sq_nonneg (1 - r)]
    rw [Real.norm_of_nonneg <| Real.rpow_nonneg 𝔤 _,
      ← Real.mul_rpow 𝔫 (hθ h).le]
    exact Real.rpow_le_rpow_of_nonpos 𝔞 he 𝔩
  · filter_upwards [hae] with θ hθ h
    exact tendsto_nhdsWithin_of_tendsto_nhds <| (by fun_prop : Continuous fun r ↦
      𝔠₁ r).continuousAt.rpow_const (.inl (hθ h).ne')

/-- The sharp radial estimate used by the weighted weak-type upper bound. -/
theorem radialMass_mul_normalizer_le 
    (hr : 0 ≤ r) (hr1 : r < 1) :
    𝔯 ^ α₁ * 𝕟 ≤ 𝔤ᵧ := by
  rw [radialMass_mul_normalizer 𝔤]
  refine ge_of_tendsto (tendsto_circleAverage_boundaryPower hα) ?_
  filter_upwards [Ioo_mem_nhdsLT hr1] with R hR
  have := circleAverage_boundaryPower_mono α hr hR.1.le hR.2
  rw [Real.circleAverage_eq_circleAverage_zero_one,
    Real.circleAverage_eq_circleAverage_zero_one (R := R)] at this
  simpa using this

theorem tendsto_radialMass_mul_normalizer :
    Tendsto (fun r ↦ 𝔯 ^ α₁ * 𝕟)
      (𝓝[<] 1) (𝓝 (𝔤ᵧ)) := by
  apply (tendsto_circleAverage_boundaryPower hα).congr'
  filter_upwards [Ioo_mem_nhdsLT 𝔭] with r hr
  exact (radialMass_mul_normalizer 𝔤).symm


end
-- FILE BergmanWeakType.Weighted.RadialKernel
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Angular means of weighted kernel columns -/

theorem circleAverage_weightedKernel_norm (z) (r) :
    Real.circleAverage (𝓌 𝔨ᵥ) 0 r = 𝕹 (r * 𝕫) := by
  rw [Real.circleAverage_eq_integral_add <| Complex.arg z, normalizer]
  congr 1
  refine intervalIntegral.integral_congr 𝒯 ?_
  simp only [norm_weightedKernel, ← Complex.norm_conj <| 1 - z * _]
  have key : starRingEnd ℂ z * Complex.exp (z.arg * Complex.I) = 𝕫 := by
    rw [← congrArg (starRingEnd ℂ) <| Complex.norm_mul_exp_arg_mul_I z, map_mul, ← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
    simp
  congr 2
  simp [circleMap, add_mul, Complex.exp_add]
  linear_combination (r * Complex.exp (θ * Complex.I)) * key

theorem normalizer_mono 
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) : 𝕟 ≤ 𝕹 R := by
  simpa only [normalizer_eq_circleAverage_radius] using
    circleAverage_boundaryPower_mono _ hr hrR hR


-- FILE BergmanWeakType.Weighted.AnnularSharpness
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Admissible annular inputs for positive weighted sharpness -/

def outerAnnulus (t : ℝ) : Set ℂ := {w | t < ‖w‖ ∧ ‖w‖ < 1}

theorem measurableSet_outerAnnulus (t) : MeasurableSet (outerAnnulus t) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem circleAverage_outerAnnulus {t} (hr : 𝕀) (g : 𝕦) :
    Real.circleAverage ((outerAnnulus t).indicator g) 0 r =
      if t < r then Real.circleAverage g 0 r else 0 := by
  split_ifs
  · exact Real.circleAverage_congr_sphere 𝒲
      Set.indicator_of_mem (by simp_all [outerAnnulus, abs_of_pos hr.1]) _
  · exact Real.circleAverage_const_on_circle 𝒲
      Set.indicator_of_notMem (by simp_all [outerAnnulus, abs_of_pos hr.1]) _

section
include hα hz
theorem integrable_normalizer_radial :
    Integrable (𝓌 𝕹 (‖w‖ * 𝕫)) 𝔴 := by
  𝕡
  have hz' := mem_disk_iff.mp hz
  refine (integrable_const <| 𝕹 𝕫).mono' (((continuousOn_normalizer.comp
    𝔣 𝒲 ⟨𝔭, ?_⟩).aestronglyMeasurable
      measurableSet_disk).mono_ac (withDensity_absolutelyContinuous diskArea _)) ?_
  · simp at hw
    nlinarith [norm_nonneg z]
  filter_upwards [ae_mem_disk_weightedArea] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg normalizer_nonneg]
  exact normalizer_mono 𝔭
    (mul_le_of_le_one_left 𝔬 (mem_disk_iff.mp hw).le) hz'

theorem integral_kernel_outerAnnulus_eq_normalizer
    (t) :
    (∫ w in outerAnnulus t, 𝔨ᵥ ∂𝔴) =
      ∫ w in outerAnnulus t, 𝕹 (‖w‖ * 𝕫) ∂𝔴 := by
  𝕡
  rw [← integral_indicator <| measurableSet_outerAnnulus t,
    ← integral_indicator (measurableSet_outerAnnulus t),
    integral_weightedArea_eq_circleAverage hα (Integrable.indicator (by
      simpa using (integrable_weightedKernel_mul hα 𝔦 hz).norm)
      (measurableSet_outerAnnulus t)),
    integral_weightedArea_eq_circleAverage hα
      ((integrable_normalizer_radial hα hz).indicator <| measurableSet_outerAnnulus t)]
  refine setIntegral_congr_fun measurableSet_Ioo 𝓡 ?_
  simp only [circleAverage_outerAnnulus hr, circleAverage_weightedKernel_norm z]
  rw [Real.circleAverage_const_on_circle (a := 𝕹 <| r * 𝕫) 𝒲 by
    simp_all [abs_of_pos hr.1]]

end
include hα in
/-- Admissible outer-annulus inputs recover the exact positive weighted lower constant. -/
theorem gammaConstant_le_weightedPositiveProjection_constant :
    ENNReal.ofReal (𝔤ᵧ) ≤
      weakTypeConstant 𝔴 (weightedPositiveProjection α) := by
  refine le_sInf fun C hC ↦ ?_
  have hS : IsClosed {x : ℝ | ENNReal.ofReal x ≤ C} :=
    isClosed_le ENNReal.continuous_ofReal continuous_const
  refine hS.mem_of_tendsto (tendsto_radialMass_mul_normalizer hα) ?_
  filter_upwards [Ioo_mem_nhdsLT one_pos] with R hR
  refine hS.mem_of_tendsto (((continuous_const.mul continuous_id).tendsto <| 𝕹 R).mono_left
    (nhdsWithin_le_nhds (s := Set.Iio <| 𝕹 R))) ?_
  filter_upwards [Ioo_mem_nhdsLT <| normalizer_pos hα 𝔤]
    with ℓ hℓ
  have hn : Tendsto (fun t ↦ 𝕹 <| t * R) (𝓝[<] 1) (𝓝 <| 𝕹 R) :=
    (continuousOn_normalizer.continuousAt <| Ico_mem_nhds hR.1 hR.2).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds <| by simpa using (continuous_id.mul_const R).tendsto 1)
  obtain ⟨t, ht, hlt⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT one_pos) <| hn.eventually (lt_mem_nhds hℓ.2)).exists
  𝕡
  have hs : 0 < 𝔴 (outerAnnulus t) := by
    rw [outerAnnulus, weightedArea_outerAnnulus hα ht.1.le ht.2]
    exact ENNReal.ofReal_pos.2 <| Real.rpow_pos_of_pos 𝔑 _
  have hm : 0 < (𝔴).real (outerAnnulus t) := ENNReal.toReal_pos hs.ne' 𝔈
  rw [Pi.mul_apply, id, mul_comm, ENNReal.ofReal_mul hℓ.1.le, ← weightedArea_outerAnnulus hα hR.1.le hR.2]
  refine IsWeakTypeBound.indicator_le hC (measurableSet_outerAnnulus t) hs hℓ.1 <| .of_forall 𝒵 ?_
  have hzd := mem_disk_iff.mpr hz.2
  have hK : Integrable (𝓌 𝔨ᵥ) 𝔴 := by
    simpa using
      (integrable_weightedKernel_mul hα 𝔦 hzd).norm
  have : weightedPositiveProjection α ((outerAnnulus t).indicator 𝒽 1) z =
      ENNReal.ofReal (∫ w in outerAnnulus t, 𝔨ᵥ ∂𝔴) := by
    rw [ofReal_integral_eq_lintegral_ofReal hK.integrableOn <| .of_forall 𝒽 norm_nonneg _, ← lintegral_indicator <| measurableSet_outerAnnulus t]
    refine lintegral_congr 𝓌 ?_
    by_cases hw : w ∈ outerAnnulus t <;> simp_all
  rw [this, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos hℓ.1 hm).le]
  refine (mul_lt_mul_of_pos_right hlt hm).trans_le ?_
  rw [integral_kernel_outerAnnulus_eq_normalizer hα hzd]
  calc _ = ∫ w in outerAnnulus t, 𝕹 (t * R) ∂𝔴 := by simp [mul_comm]
    _ ≤ _ := integral_mono_ae (integrable_const _) (integrable_normalizer_radial hα hzd).integrableOn
      (by filter_upwards [ae_restrict_mem <| measurableSet_outerAnnulus t] with w hw
          exact normalizer_mono (mul_nonneg ht.1.le hR.1.le) (mul_le_mul hw.1.le hz.1.le hR.1.le
            𝔬) ((mul_le_of_le_one_left 𝔬 hw.2.le).trans_lt hz.2))


-- FILE BergmanWeakType.Weighted.NormalizerRadial
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # The circular normalizer as a polar kernel potential -/

theorem polarIntegral_boundary_eq_normalizer (α r θ) :
    𝔅ᵖ (polarKernel 𝔥) r θ =
        𝕟 := by
  have hk (t) : polarKernel 𝔥 (cos t) (sin t) r θ =
      ‖weightedKernel α (𝔠ₘ θ) (circleMap 0 1 t)‖ := by
    simpa only [circleMap_zero_re, circleMap_zero_im, one_mul] using
      𝖗 polarKernel_eq_norm_weightedKernel (circleMap 0 1 t)
  have hcircle := circleAverage_weightedKernel_norm (α := α) (𝔠ₘ θ) 1
  simp only [one_mul, norm_circleMap_zero, normalizer_eq_circleAverage_radius,
    circleAverage_abs_radius] at hcircle
  rw [polarIntegral, normalizer_eq_circleAverage_radius]
  simp_rw [hk]
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le 𝔭]
  simpa [Real.circleAverage_def, mul_comm] using hcircle

def normalizerFirst (α r : ℝ) : ℝ :=
  𝔅ᵖ (polarKernelR 𝔥) r 0

def normalizerSecond (α r : ℝ) : ℝ :=
  𝔅ᵖ (polarKernelRR 𝔥) r 0

local macro "bd" f:ident x:(colGt term:max)* : term => `($f isCompact_Icc (ae_restrict_mem measurableSet_Icc)
  (integrable_const (μ := volume.restrict (Set.Icc 𝟘 τ)) (τ⁻¹))
  continuous_cos continuous_sin (fun t _ ↦ (cos_sq_add_sin_sq t).le) $x*)

theorem continuousOn_normalizerSecond :
    ContinuousOn (normalizerSecond α) J₁ := by
  apply (continuousOn_polarIntegral_unit isCompact_Icc (ae_restrict_mem measurableSet_Icc)
    (integrable_const _) (continuousOn_polarKernelRR_source continuous_cos continuous_sin
    (fun t _ ↦ (cos_sq_add_sin_sq t).le) _)).comp (continuous_id.prodMk continuous_const).continuousOn
  exact 𝓡 ⟨hr, Set.mem_univ _⟩

section
variable (h₂ : 𝕣 < 1)
include h₂
theorem normalizer_hasDerivAt :
    HasDerivAt 𝕹 (normalizerFirst α r) r := by
  simpa only [polarIntegral_boundary_eq_normalizer, normalizerFirst] using
    bd polarIntegral_kernel_hasDerivAt_r 𝔥 h₂ 0

theorem normalizerFirst_hasDerivAt :
    HasDerivAt (normalizerFirst α) (normalizerSecond α r) r :=
  bd polarIntegral_kernelR_hasDerivAt_r 𝔥 h₂ 0

theorem polarIntegral_boundary_angular_eq_zero (θ) :
    𝔅ᵖ (polarKernelT 𝔥) r θ = 0 := by
  have hd := bd polarIntegral_kernel_hasDerivAt_t 𝔥 h₂ θ
  rw [funext <| polarIntegral_boundary_eq_normalizer α r] at hd
  exact hd.unique <| hasDerivAt_const θ _

/-- The exact radial differential equation for the normalizing circular average. -/
theorem normalizer_ode (hr0 : r ≠ 0) :
    normalizerSecond α r + normalizerFirst α r / r -
      (2 * α₂ * r / 𝔯) * normalizerFirst α r -
      (α₂ ^ 2 / 𝔯) * 𝕟 = 0 := by
  have hd := bd polarIntegral_kernelT_hasDerivAt_t 𝔥 h₂ 0
  rw [funext <| polarIntegral_boundary_angular_eq_zero h₂] at hd
  simpa only [polarIntegral_boundary_eq_normalizer, hd.unique <| hasDerivAt_const 0 0,
    polarOperator, normalizerFirst, normalizerSecond, zero_div, add_zero] using bd polarIntegral_operator_boundary h₂ 0 α₂ hr0
      fun t _ ↦ cos_sq_add_sin_sq t
end

-- FILE BergmanWeakType.Weighted.WeightedPotential
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Weighted positive potentials and their normalized circular caps -/

def weightedPotential (α : ℝ) (f : 𝕋) (z : ℂ) : ℝ :=
  ∫ w, 𝔨ᵥ * ‖𝕱‖ ∂𝔴

def weightedNormalizedPotential (α : ℝ) (f : 𝕋) (z : ℂ) : ℝ :=
  𝖕 weightedPotential / 𝕹 𝕫

def weightedDiskPotential (α : ℝ) (f : 𝕋) : 𝕦 :=
  disk.indicator (weightedNormalizedPotential α f)

theorem weightedDiskPotential_nonneg (z) :
    0 ≤ 𝖕 weightedDiskPotential :=
  indicator_nonneg (𝒰 div_nonneg (integral_nonneg 𝒽 𝔭)
    normalizer_nonneg) z

include hz in
theorem weightedDiskPotential_eq :
    𝖕 weightedDiskPotential = 𝖕 weightedNormalizedPotential :=
  indicator_of_mem hz _

include hα hf hz in
theorem weightedPotential_eq_toReal 
    :
    𝖕 weightedPotential = (𝖕 weightedPositiveProjection).toReal := by
  simp only [weightedPotential, weightedPositiveProjection, ← ofReal_norm,
    ← ENNReal.ofReal_mul 𝔬]
  rw [integral_eq_lintegral_of_nonneg_ae <| .of_forall 𝓌 𝔭]
  simpa using (integrable_weightedKernel_mul hα hf hz).norm.aestronglyMeasurable

include hf in
theorem continuousOn_weightedPotential_disk 
    : ContinuousOn (weightedPotential α f) disk := by
  intro z hz
  have hz' := mem_disk_iff.mp hz
  refine ((continuousOn_integral_mul_of_compact (isCompact_closedBall 0 1)
    (ae_mem_disk_weightedArea.mono 𝒽 (Metric.ball_subset_closedBall ·))
    hf.norm (isCompact_closedBall 0 _) ?_).continuousAt
    (Metric.closedBall_mem_nhds_of_mem (by simp; linarith : z ∈ Metric.ball 0 ((𝕫 + 1) / 2)))
    ).continuousWithinAt
  simp_rw [norm_weightedKernel]
  exact ContinuousOn.rpow_const 𝔣 fun p ⟨h1, h2⟩ ↦ Or.inl <| norm_ne_zero_iff.2 𝒷 by
    have := congrArg norm <| sub_eq_zero.1 h
    simp at h1 h2 this
    nlinarith [norm_nonneg p.1]

section
include hα hf
theorem measurable_weightedDiskPotential 
    : Measurable (weightedDiskPotential α f) := by
  classical
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_disk
  refine (continuousOn_weightedPotential_disk hf).div (continuousOn_normalizer.comp
    continuous_norm.continuousOn 𝒵 ⟨𝔬, mem_disk_iff.mp hz⟩) 𝒵 ?_
  exact (normalizer_pos hα 𝔞).ne'

/-- Normalizing by the exact circular kernel average makes every capped circular mean
of an admissible weighted potential decrease with radius. -/
local notation:max "𝔾" X:max => 𝓡 X hK hμ hf.norm Complex.continuous_re Complex.continuous_im hs _ 𝔗
local notation:max "𝔾'" X:max => continuousOn_polarIntegral_unit hK hμ hf.norm <| X Complex.continuous_re Complex.continuous_im hs _
theorem antitoneOn_circleAverage_min_weightedNormalizedPotential
    (c) :
    AntitoneOn (fun r ↦ circleAverage (𝓏 min 𝖕 weightedNormalizedPotential c) 0 r)
      J₁ := by
  have hK := isCompact_closedBall 𝟎 1
  have hμ : ∀ᵐ w ∂𝔴, w ∈ Metric.closedBall 0 1 :=
    ae_mem_disk_weightedArea.mono 𝒽 (Metric.ball_subset_closedBall ·)
  have hs (w : ℂ) (hw : w ∈ Metric.closedBall 0 1) : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have : 𝔫₂ w ≤ 1 := 𝔞
    simpa [Complex.sq_norm, Complex.normSq_apply, ← sq] using this
  have hr2 (r) (hr : 𝕀) : 𝕣 < 1 := by nlinarith [hr.1, hr.2]
  have h : AntitoneOn (angularMean fun r θ ↦ min (polarIntegral (polarKernel 𝔥)
      Complex.re Complex.im 𝔴 (‖f ·‖) r θ / 𝕟) c) J₁ :=
    antitoneOn_angularMean_min_quotient α₂ c
      𝔾' continuousOn_polarKernel_source 𝔾' continuousOn_polarKernelR_source
      𝔾' continuousOn_polarKernelRR_source 𝔾' continuousOn_polarKernelT_source
      𝔾' continuousOn_polarKernelTT_source
      𝔾 polarIntegral_kernel_hasDerivAt_r
      𝔾 polarIntegral_kernelR_hasDerivAt_r
      𝔾 polarIntegral_kernel_hasDerivAt_t
      𝔾 polarIntegral_kernelT_hasDerivAt_t
      (by simp [polarIntegral, polarKernel, polarDenominator, radialComponent])
      (by simp [polarIntegral, polarKernelT, polarKernel, polarDenominator, radialComponent,
        angularComponent]) continuousOn_normalizer (𝓡 (normalizerFirst_hasDerivAt <| by nlinarith [hr.1, hr.2]).continuousAt.continuousWithinAt)
      continuousOn_normalizerSecond (𝓡 normalizer_hasDerivAt 𝔗)
      (𝓡 normalizerFirst_hasDerivAt 𝔗)
      (𝓡 normalizer_pos hα 𝔤)
      (𝓡 by convert normalizer_ode 𝔗 hr.1.ne' using 1; ring) 𝓡θ by
        convert polarIntegral_operator_nonpos hK hμ hf.norm Complex.continuous_re Complex.continuous_im hs 𝔗 θ α₂ hr.1.ne'
          (.of_forall 𝒽 norm_nonneg _) using 1
        simp only [polarOperator]; ring
  intro r hr s hs hrs
  convert h hr hs hrs using 1 <;>
  simp only [Real.circleAverage_def, angularMean, weightedNormalizedPotential, weightedPotential,
    polarIntegral, polarKernel_eq_norm_weightedKernel, norm_circleMap_zero, abs_of_nonneg hr.1,
    abs_of_nonneg hs.1, smul_eq_mul]

end
theorem circleAverage_min_weightedDiskPotential_eq 
    (hr : r ∈ J₁) (c) :
    circleAverage 𝔠 0 r =
      circleAverage (𝓏 min 𝖕 weightedNormalizedPotential c) 0 r :=
  circleAverage_congr_sphere 𝒵 by
    rw [weightedDiskPotential_eq <| mem_disk_iff.mpr (by simp_all [abs_of_nonneg hr.1])]

section
include hα hf
theorem antitoneOn_circleAverage_min_weightedDiskPotential
    (c) :
    AntitoneOn (fun r ↦ circleAverage 𝔠 0 r)
      J₁ := fun r hr s hs hrs ↦ by
  simpa only [circleAverage_min_weightedDiskPotential_eq hr,
    circleAverage_min_weightedDiskPotential_eq hs] using
    antitoneOn_circleAverage_min_weightedNormalizedPotential hα hf c hr hs hrs

theorem circleAverage_min_weightedDiskPotential_le_mass
    
    (hr : r ∈ J₁) (c) :
    circleAverage 𝔠 0 r ≤
      ∫ w, ‖𝕱‖ ∂𝔴 := by
  rw [circleAverage_min_weightedDiskPotential_eq hr]
  have h := antitoneOn_circleAverage_min_weightedNormalizedPotential hα hf c
    𝔰 hr hr.1
  simp only [weightedNormalizedPotential, weightedPotential] at h
  exact h.trans <| by simp [normalizer, circleAverage_const]


end
-- FILE BergmanWeakType.WeightedSharp
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Sharp positive weighted constants and the complex weighted upper bound -/


include hα in
/-- The sharp positive weighted weak type bound for every admissible standard weight. -/
theorem isWeakTypeBound_weightedPositiveProjection :
    IsWeakTypeBound 𝔴 (weightedPositiveProjection α)
      (ENNReal.ofReal (𝔤ᵧ)) := by
  𝕡
  intro f hf t ht
  have hD := gammaConstant_pos hα
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ t = 𝔤ᵧ * s :=
    ⟨t / 𝔤ᵧ, div_pos ht hD, (mul_div_cancel₀ _ hD.ne').symm⟩
  have hU := measurable_weightedDiskPotential hα hf
  have hr (y) (hy : y ∈ I₁) := massRadius_mem_unit hα hy
  have hi := integral_mul_radialLevelFraction_le hU weightedDiskPotential_nonneg
    (by unfold massRadius; fun_prop) (fun c y hy u hu hyu ↦
      antitoneOn_circleAverage_min_weightedDiskPotential hα hf c ⟨(hr u hu).1.le, (hr u hu).2⟩
      ⟨(hr y hy).1.le, (hr y hy).2⟩ (massRadius_antitone hα ⟨hy.1.le, hy.2.le⟩ ⟨hu.1.le, hu.2.le⟩ hyu))
    (fun y hy c ↦ circleAverage_min_weightedDiskPotential_le_mass hα hf
      ⟨(hr y hy).1.le, (hr y hy).2⟩ c) hs.le
  set S := disk ∩ {z : ℂ | s * 𝔷 ^ α₁ < 𝖕 weightedDiskPotential}
  have hS : MeasurableSet S := measurableSet_disk.inter <| measurableSet_lt 𝔣 hU
  have heq : (𝔍ᵧ radialLevelFraction (weightedDiskPotential α f) (massRadius α) s y)
      = (𝔴).real S := by
    rw [← integral_indicator_one hS,
      integral_weightedArea_eq_circleAverage_mass hα ((integrable_const 1).indicator hS)]
    refine intervalIntegral.integral_congr_ae <| .of_forall 𝒴 circleAverage_congr_sphere
      𝒵 ?_
    rw [uIoc_of_le zero_le_one] at hy
    have hsq : 𝕫 ^ 2 = 1 - y ^ α₁⁻¹ := by
      simp at hz
      rw [hz, massRadius, abs_of_nonneg <| sqrt_nonneg _, sq_sqrt <| sub_nonneg.2
        (rpow_le_one hy.1.le hy.2 (inv_nonneg.2 𝔩))]
    have hzD : z ∈ disk := by
      rw [mem_disk_iff]
      nlinarith [rpow_pos_of_pos hy.1 α₁⁻¹]
    simp [S, Set.indicator, hzD, hsq, rpow_inv_rpow hy.1.le (by linarith : α₁ ≠ 0)]
  rw [intervalIntegral.integral_const_mul] at hi
  have hm : (𝔴).real {z | ENNReal.ofReal (𝔤ᵧ * s) <
      𝖕 weightedPositiveProjection} ≤ (𝔴).real S := by
    refine ENNReal.toReal_mono 𝔈 <| measure_mono_ae ?_
    filter_upwards [ae_mem_disk_weightedArea] with z hz hlev
    have hF := (ENNReal.ofReal_lt_iff_lt_toReal 𝔭
      (weightedPositiveProjection_lt_top hα hf hz).ne).mp hlev
    rw [← weightedPotential_eq_toReal hα hf hz] at hF
    refine ⟨hz, ?_⟩
    rw [mem_ofPred_eq, weightedDiskPotential_eq hz, weightedNormalizedPotential,
      lt_div_iff₀ (normalizer_pos hα 𝔞)]
    nlinarith [mul_le_mul_of_nonneg_left (radialMass_mul_normalizer_le hα 𝔬 <| mem_disk_iff.mp hz)
      hs.le]
  rw [← ofReal_integral_norm_eq_lintegral_enorm hf, ← ENNReal.ofReal_mul hD.le,
    ← ofReal_measureReal 𝔈, ← ENNReal.ofReal_mul 𝔭]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant 𝔴 (weightedPositiveProjection α) =
      ENNReal.ofReal (𝔤ᵧ) :=
  le_antisymm (sInf_le <| isWeakTypeBound_weightedPositiveProjection hα)
    (gammaConstant_le_weightedPositiveProjection_constant hα)

theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant 𝔴 𝔓 ≤
      ENNReal.ofReal (𝔤ᵧ) :=
  weightedProjection_constant_le_weightedPositiveProjection_constant.trans_eq
    (weightedPositiveProjection_constant_eq α hα)


-- FILE BergmanWeakType.DiskSharp
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
/-! # Sharp weak type constants on the unit disk -/

theorem weightedPositiveProjection_zero : weightedPositiveProjection 0 = positiveProjection := by
  ext
  simp [weightedPositiveProjection, positiveProjection]

/-- The positive Bergman projection has weak type bound one on the unit disk. -/
theorem isWeakTypeBound_positiveProjection_one :
    IsWeakTypeBound diskArea positiveProjection 1 := by
  simpa [gammaConstant, ← weightedPositiveProjection_zero] using
    isWeakTypeBound_weightedPositiveProjection (α := 0) 𝔫

/-- The sharp weak type constant of the positive disk Bergman projection is one. -/
theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 := by
  simpa [gammaConstant, ← weightedPositiveProjection_zero] using
    weightedPositiveProjection_constant_eq 0 𝔫

/-- The sharp weak type constant of the complex disk Bergman projection is one. -/
theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 :=
  le_antisymm (by simpa [gammaConstant, weightedProjection, projection] using
    weightedProjection_constant_le 0 𝔫)
    (by simpa [weightedProjection, projection] using one_le_weightedProjection_constant 0 𝔫)


-- FILE BergmanWeakType.Rigidity.DiskSimilarity
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

include hR in
/-- Every Euclidean disk has positive Bergman weak type constant one. -/
theorem weakTypeConstant_domainPositiveProjection_ball_eq_one
    (hK : IsBergmanKernel 𝕭 K) :
    weakTypeConstant (area.restrict 𝕭) (domainPositiveProjection 𝕭 K) = 1 := by
  have hb := Complex.ofReal_ne_zero.mpr hR.ne'
  let e := ((Homeomorph.mulLeft₀ _ hb).trans <| Homeomorph.addLeft a).toMeasurableEquiv
  have he : e = 𝓌 a + R * w := rfl
  have hd (w) : HasDerivAt e R w := by
    simpa [he] using ((hasDerivAt_id w).const_mul (R : ℂ)).const_add a
  have himage : e '' disk = ball a R := by
    simpa [he, abs_of_pos hR] using image_affine_disk hb
  have hbij := himage ▸ e.injective.injOn.bijOn_image
  have hdiff : 𝕮 e disk := fun w _ ↦ (hd w).differentiableAt.differentiableWithinAt
  have hinv : InvOn e.symm e disk 𝕭 :=
    ⟨𝒰 e.symm_apply_apply _, 𝒰 e.apply_symm_apply _⟩
  have hμ : area.restrict 𝕭 = ENNReal.ofReal (R ^ 2) • Measure.map e diskArea := by
    ext S hS
    rw [Measure.smul_apply, e.map_apply, smul_eq_mul, ← himage, ← lintegral_indicator_one hS,
      ← lintegral_indicator_one (e.measurable hS), area_lintegral_image_eq (U := disk) isOpen_ball
      hdiff hbij.injOn, ← 𝖜 lintegral_const_mul' ENNReal.ofReal_ne_top]
    aesop
  have hP (f) {z} (hz : z ∈ disk) :
      domainPositiveProjection 𝕭 K f (e z) = positiveProjection (f ∘ e) z := by
    rw [domainPositiveProjection, hμ, lintegral_smul_measure, e.measurableEmbedding.lintegral_map,
      smul_eq_mul, ← 𝖜 lintegral_const_mul' ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_disk] with w hw
    have hk := hK.disk_coordinate_formula hz hw hdiff isOpen_ball (differentiableOn_inverse isOpen_ball
      isOpen_ball hdiff hinv (hinv.1.mapsTo hbij.surjOn)) hbij hinv
    simp only [(hd _).deriv] at hk
    rw [← mul_assoc, ← ENNReal.ofReal_mul 𝔭, hk]
    congr 2
    simp
    field_simp
  have : IsFiniteMeasure (area.restrict <| ball a R) :=
    isFiniteMeasure_restrict.mpr isBounded_ball.measure_lt_top.ne
  refine le_antisymm (sInf_le fun f hf t ht ↦ ?_)
    (hK.one_le_weakTypeConstant isOpen_ball.measurableSet (measure_ball_pos area a hR).ne')
  rw [hμ] at hf ⊢
  have := isWeakTypeBound_positiveProjection_one _ (e.measurableEmbedding.integrable_map_iff.1
    ((integrable_smul_measure 𝔭 ENNReal.ofReal_ne_top).1 hf)) t ht
  rw [Measure.smul_apply, e.map_apply, lintegral_smul_measure, e.measurableEmbedding.lintegral_map, smul_eq_mul, one_mul, mul_left_comm]
  convert mul_le_mul_right this (ENNReal.ofReal <| R ^ 2) using 3
  · exact measure_congr <| by filter_upwards [ae_mem_disk] with w hw using by simp_all
  simp


-- FILE BergmanWeakType.Rigidity.BoundedRigidity
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

-- Keep the public statement's topology, bornology, and metric instances identical to the
-- independently elaborated Challenge statement, which imports no C*-algebra instances.
/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant 𝔇 (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  refine ⟨fun hc ↦ by_contra fun hnd ↦ ?_, ?_⟩
  · have : IsFiniteMeasure 𝔇 := isFiniteMeasure_restrict.2 hbounded.measure_lt_top.ne
    obtain ⟨E, hE, hsub, hEpos, η, hη, hη1, hgap⟩ := exists_domain_core_gap hK hopen hbounded hconnected hnd
    exact (weakTypeConstant_gt_one_of_core_gap hK hopen.measurableSet hE hsub hEpos hη hη1
      hgap).ne' hc
  · rintro ⟨c, R, hR, rfl⟩
    exact weakTypeConstant_domainPositiveProjection_ball_eq_one hR hK


end BergmanWeakType
