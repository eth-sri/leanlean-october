/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.ShiftGood
public import DOZZ.ShiftEquations.DualR.DualL
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
public import DOZZ.Statements.Complex.HorizontalStrip
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Correlations.ComplexifyNCharges
import DOZZ.Brownian.Reflection.RtheorAnalytic
public import DOZZ.Correlations.Analytic.UnitVolumeExtension

/-!
# Factors along real segments of charges

Along a real segment of charge triples `t ↦ p + t (q - p)`, complexified in `t`:

* the continued structure constant `C_f` is meromorphic on the preimage of the holomorphy domain,
  equals the physical structure constant at real parameters in the extended Seiberg domain, and is
  analytic at `t = 1` when `Γ` is analytic at `s(q)`;
* a strip-meromorphic function composed with a real segment is meromorphic on the preimage of the
  strip, which contains every real parameter.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- A complexified real segment of charge triples. -/
noncomputable def segT (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) (t : ℂ) : Fin 3 → ℂ :=
  ![segC a₀ a₁ t, segC b₀ b₁ t, segC c₀ c₁ t]

theorem differentiable_segT (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    Differentiable ℂ (segT a₀ a₁ b₀ b₁ c₀ c₁) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_segC a₀ a₁
  · exact differentiable_segC b₀ b₁
  · exact differentiable_segC c₀ c₁

theorem vec3_ofReal (a b c : ℝ) :
    (![(a : ℂ), (b : ℂ), (c : ℂ)] : Fin 3 → ℂ) = complexifyNCharges ![a, b, c] := by
  funext i
  fin_cases i <;> simp [complexifyNCharges]

theorem segT_ofReal (a₀ a₁ b₀ b₁ c₀ c₁ t : ℝ) :
    segT a₀ a₁ b₀ b₁ c₀ c₁ (t : ℂ) =
      complexifyNCharges ![a₀ + t * (a₁ - a₀), b₀ + t * (b₁ - b₀), c₀ + t * (c₁ - c₀)] := by
  unfold segT
  rw [segC_ofReal, segC_ofReal, segC_ofReal, vec3_ofReal]

theorem segT_one (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    segT a₀ a₁ b₀ b₁ c₀ c₁ 1 = complexifyNCharges ![a₁, b₁, c₁] := by
  unfold segT
  rw [segC_one, segC_one, segC_one, vec3_ofReal]

/-- Real points of a segment between two extended Seiberg triples lie in any open set containing
the complexified extended Seiberg domain. -/
theorem segT_mem {γ : ℝ} (hγ : 0 < γ) {V : Set (Fin 3 → ℂ)}
    (hVmem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V)
    {a₀ a₁ b₀ b₁ c₀ c₁ : ℝ} (h₀ : ExtendedSeiberg3 γ a₀ b₀ c₀)
    (h₁ : ExtendedSeiberg3 γ a₁ b₁ c₁) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segT a₀ a₁ b₀ b₁ c₀ c₁ (t : ℂ) ∈ V := by
  rw [segT_ofReal]
  exact hVmem _ (extendedSeiberg3_segment hγ h₀ h₁ ht0 ht1)

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ) {γ μ : ℝ} (hμ : 0 < μ)
  {f : (Fin 3 → ℂ) → ℂ}
  (hfeq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
include Ω hμ hfeq

/-- The continued structure constant at a real point of a segment. -/
theorem segH_ofReal
    {a₀ a₁ b₀ b₁ c₀ c₁ t : ℝ}
    (h : ExtendedSeiberg3 γ (a₀ + t * (a₁ - a₀)) (b₀ + t * (b₁ - b₀)) (c₀ + t * (c₁ - c₀))) :
    structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ (t : ℂ)) =
      (structureConstant P M γ μ (a₀ + t * (a₁ - a₀)) (b₀ + t * (b₁ - b₀))
        (c₀ + t * (c₁ - c₀)) : ℂ) := by
  rw [segT_ofReal]
  exact structureConstantH_complexify P M hμ _ (hfeq _ h)

/-- The continued structure constant at the end of a segment. -/
theorem segH_one
    {a₀ a₁ b₀ b₁ c₀ c₁ : ℝ} (h : ExtendedSeiberg3 γ a₁ b₁ c₁) :
    structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ 1) =
      (structureConstant P M γ μ a₁ b₁ c₁ : ℂ) := by
  rw [segT_one]
  exact structureConstantH_complexify P M hμ _ (hfeq _ h)

end

section
variable {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V)
  {γ μ : ℝ} (hμ : 0 < μ)
include hV hf hμ

/-- The continued structure constant is meromorphic along a segment, on the preimage of the
holomorphy domain. -/
theorem segH_meromorphicOn (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    MeromorphicOn (fun t => structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ t))
      (segT a₀ a₁ b₀ b₁ c₀ c₁ ⁻¹' V) :=
  meromorphicOn_structureConstantH_comp hV hf hμ (differentiable_segT a₀ a₁ b₀ b₁ c₀ c₁)

/-- The continued structure constant is analytic at the end of a segment when `Γ` is analytic at
the `s`-parameter of the endpoint. -/
theorem segH_analyticAt_one {a₀ a₁ b₀ b₁ c₀ c₁ : ℝ}
    (hmem : complexifyNCharges ![a₁, b₁, c₁] ∈ V)
    (hs : AnalyticAt ℂ Complex.Gamma (sExp γ a₁ b₁ c₁ : ℂ)) :
    AnalyticAt ℂ (fun t => structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ t)) 1 := by
  refine analyticAt_structureConstantH_comp' hV hf hμ (differentiable_segT a₀ a₁ b₀ b₁ c₀ c₁)
    (by rw [segT_one]; exact hmem) ?_
  rw [segT_one, sExpC_complexify]
  exact hs

end

/-- A strip-meromorphic function along a real segment. -/
theorem segR_meromorphicOn {R : ℂ → ℂ} {h : ℝ} (hR : MeromorphicOn R (horizontalStrip h))
    (a₀ a₁ : ℝ) :
    MeromorphicOn (fun t => R (segC a₀ a₁ t)) (segC a₀ a₁ ⁻¹' horizontalStrip h) :=
  fun t ht => (hR _ ht).comp_analyticAt (g := segC a₀ a₁) (analyticAt_segC a₀ a₁ t)

/-- A function analytic at the endpoint is analytic along the segment at `t = 1`. -/
theorem segR_analyticAt_one {R : ℂ → ℂ} {a₀ a₁ : ℝ} (hR : AnalyticAt ℂ R (a₁ : ℂ)) :
    AnalyticAt ℂ (fun t => R (segC a₀ a₁ t)) 1 :=
  AnalyticAt.comp_of_eq (g := R) (f := segC a₀ a₁) hR (analyticAt_segC a₀ a₁ 1) (segC_one a₀ a₁)

/-- Real parameters of a segment map into a strip. -/
theorem segC_mem_horizontalStrip {h : ℝ} (hh : 0 < h) (a₀ a₁ t : ℝ) :
    segC a₀ a₁ (t : ℂ) ∈ horizontalStrip h := by
  rw [segC_ofReal]
  exact ofReal_mem_horizontalStrip hh _

/-- Continue a structure shift from a real box along two charge segments. The first charge
on the left is affine in the box coordinate; the pointwise left factor is strip-meromorphic. -/
theorem affineLeftShift_of_box {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    {V₃ : Set (Fin 3 → ℂ)} {f₃ : (Fin 3 → ℂ) → ℂ}
    (hExt : IsUnitVolumeExtension P M γ V₃ f₃)
    (a d : ℝ) {h : ℝ} (hh : 0 < h) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip h))
    {xl xu bl bu cl cu : ℝ}
    (hbox : ∀ y b' c' : ℝ, xl < y → y < xu → bl < b' → b' < bu → cl < c' → c' < cu →
      AnalyticAt ℂ R (y : ℂ) →
      R y * (structureConstant P M γ μ (a * y + d) b' c' : ℂ) = -(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) ((y : ℂ) - γ / 2) b' c' * (structureConstant P M γ μ (y - γ) b' c' : ℂ))
    {x₀ b₀ c₀ : ℝ} (hx₀ : x₀ ∈ Ioo xl xu) (hb₀ : b₀ ∈ Ioo bl bu) (hc₀ : c₀ ∈ Ioo cl cu)
    (hR₀ : AnalyticAt ℂ R (x₀ : ℂ))
    (hq₀₁ : ExtendedSeiberg3 γ (a * x₀ + d) b₀ c₀) (hq₀₂ : ExtendedSeiberg3 γ (x₀ - γ) b₀ c₀)
    {x b c : ℝ} (h₁ : ExtendedSeiberg3 γ (a * x + d) b c)
    (h₂ : ExtendedSeiberg3 γ (x - γ) b c) (hR : AnalyticAt ℂ R (x : ℂ))
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ (a * x + d) b c : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ (x - γ) b c : ℂ))
    (hA : ShiftCoeffGood γ ((x : ℂ) - γ / 2) b c) :
    R x * (structureConstant P M γ μ (a * x + d) b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((x : ℂ) - γ / 2) b c * (structureConstant P M γ μ (x - γ) b c : ℂ) := by
  set U : Set ℂ := segC x₀ x ⁻¹' horizontalStrip h ∩
    (segT (a * x₀ + d) (a * x + d) b₀ b c₀ c ⁻¹' V₃ ∩
      segT (x₀ - γ) (x - γ) b₀ b c₀ c ⁻¹' V₃) with hU
  set F : ℂ → ℂ := fun t => R (segC x₀ x t) *
    structureConstantH f₃ γ μ (segT (a * x₀ + d) (a * x + d) b₀ b c₀ c t) with hF
  set G : ℂ → ℂ := fun t => -(1 / (Real.pi * μ)) *
    shiftCoeffA γ ((γ : ℂ) / 2) (segC x₀ x t - γ / 2) (segC b₀ b t) (segC c₀ c t) *
      structureConstantH f₃ γ μ (segT (x₀ - γ) (x - γ) b₀ b c₀ c t) with hG
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U := fun t h0 h1 =>
    ⟨segC_mem_horizontalStrip hh x₀ x t, segT_mem hγ hExt.mem hq₀₁ h₁ h0 h1,
      segT_mem hγ hExt.mem hq₀₂ h₂ h0 h1⟩
  have hFm : MeromorphicOn F U := fun t ht =>
    (segR_meromorphicOn hRm x₀ x t ht.1).fun_mul
      (segH_meromorphicOn hExt.isOpen hExt.holomorphic hμ (a * x₀ + d) (a * x + d) b₀ b c₀ c t ht.2.1)
  have hGm : MeromorphicOn G U := fun t ht =>
    (MeromorphicAt.const _ t |>.fun_mul (meromorphicAt_shiftCoeffA_comp
      (f₁ := fun t => segC x₀ x t - γ / 2) ((analyticAt_segC x₀ x t).sub analyticAt_const)
      (analyticAt_segC b₀ b t) (analyticAt_segC c₀ c t))).fun_mul
      (segH_meromorphicOn hExt.isOpen hExt.holomorphic hμ (x₀ - γ) (x - γ) b₀ b c₀ c t ht.2.2)
  have hRev : ∀ᶠ t : ℝ in 𝓝[>] 0, AnalyticAt ℂ R ((x₀ + t * (x - x₀) : ℝ) : ℂ) := by
    have hc : ContinuousAt (fun t : ℝ => ((x₀ + t * (x - x₀) : ℝ) : ℂ)) 0 := by fun_prop
    have h0 : ((x₀ + 0 * (x - x₀) : ℝ) : ℂ) = (x₀ : ℂ) := by simp
    have hev := hc.preimage_mem_nhds (by rw [h0]; exact hR₀.eventually_analyticAt)
    exact nhdsWithin_le_nhds hev
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, F t = G t := by
    filter_upwards [eventually_segC_mem (b := x) isOpen_Ioo hx₀,
      eventually_segC_mem (b := b) isOpen_Ioo hb₀, eventually_segC_mem (b := c) isOpen_Ioo hc₀,
      Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hRev] with t hxt hbt hct ht hRt
    have hE₁ := extendedSeiberg3_segment hγ hq₀₁ h₁ ht.1.le ht.2.le
    have hE₂ := extendedSeiberg3_segment hγ hq₀₂ h₂ ht.1.le ht.2.le
    simp only [hF, hG]
    rw [segH_ofReal P M hμ hExt.value hE₁, segH_ofReal P M hμ hExt.value hE₂, segC_ofReal, segC_ofReal,
      segC_ofReal, show x₀ - γ + t * (x - γ - (x₀ - γ)) = x₀ + t * (x - x₀) - γ by ring,
      show a * x₀ + d + t * (a * x + d - (a * x₀ + d)) = a * (x₀ + t * (x - x₀)) + d by
        ring]
    exact hbox _ _ _ hxt.1 hxt.2 hbt.1 hbt.2 hct.1 hct.2 hRt
  have hF1 : AnalyticAt ℂ F 1 :=
    (segR_analyticAt_one hR).mul
      (segH_analyticAt_one hExt.isOpen hExt.holomorphic hμ (hExt.mem ![a * x + d, b, c] h₁) hs₁)
  have hG1 : AnalyticAt ℂ G 1 := by
    refine (analyticAt_const.mul (analyticAt_shiftCoeffA_comp
      (f₁ := fun t => segC x₀ x t - γ / 2)
      ((analyticAt_segC x₀ x 1).sub analyticAt_const) (analyticAt_segC b₀ b 1)
      (analyticAt_segC c₀ c 1) ?_)).mul
      (segH_analyticAt_one hExt.isOpen hExt.holomorphic hμ (hExt.mem ![x - γ, b, c] h₂) hs₂)
    rwa [segC_one, segC_one, segC_one]
  have key := eq_at_one_of_segment hseg hFm hGm hstart hF1 hG1
  simp only [hF, hG] at key
  rw [segH_one P M hμ hExt.value h₁, segH_one P M hμ hExt.value h₂, segC_one, segC_one, segC_one] at key
  exact key

/-- Continue the second dual seed along a real segment, allowing a shift and a meromorphic
multiplier on its first structure constant. -/
theorem dual_seed_eq_at_segment_end {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {es as bs ef af bf δ : ℝ} {A : ℂ → ℂ → ℂ → ℂ}
    (hAm : ∀ t, MeromorphicAt (fun z => A (segC es ef z) (segC as af z) (segC bs bf z)) t)
    (hA1 : AnalyticAt ℂ (fun z => A (segC es ef z) (segC as af z) (segC bs bf z)) 1)
    (hS₁ : ExtendedSeiberg3 γ (2 * Q γ - es - 2 / γ - δ) as bs)
    (hS₂ : ExtendedSeiberg3 γ es (2 * Q γ - as - 2 / γ) bs)
    (hE₁ : ExtendedSeiberg3 γ (2 * Q γ - ef - 2 / γ - δ) af bf)
    (hE₂ : ExtendedSeiberg3 γ ef (2 * Q γ - af - 2 / γ) bf)
    (hRe : AnalyticAt ℂ R (ef : ℂ)) (hRa : AnalyticAt ℂ R (af : ℂ))
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - ef - 2 / γ - δ) af bf : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ ef (2 * Q γ - af - 2 / γ) bf : ℂ))
    (g₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ef))
    (g₂ : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ af))
    (g₃ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ ef af bf))
    (g₄ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ ef af bf))
    (hstart : ∀ᶠ t : ℝ in 𝓝[>] 0,
      let e := es + t * (ef - es)
      let a := as + t * (af - as)
      let b := bs + t * (bf - bs)
      R e * (A e a b * (structureConstant P M γ μ (2 * Q γ - e - 2 / γ - δ) a b : ℂ)) =
        dualLC γ e a b * R a * (structureConstant P M γ μ e (2 * Q γ - a - 2 / γ) b : ℂ)) :
    R ef * (A ef af bf * (structureConstant P M γ μ (2 * Q γ - ef - 2 / γ - δ) af bf : ℂ)) =
      dualLC γ ef af bf * R af * (structureConstant P M γ μ ef (2 * Q γ - af - 2 / γ) bf : ℂ) := by
  obtain ⟨V, f, hV, hVmem, hf, hfe⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  let seg₁ := segT (2 * Q γ - es - 2 / γ - δ) (2 * Q γ - ef - 2 / γ - δ) as af bs bf
  let seg₂ := segT es ef (2 * Q γ - as - 2 / γ) (2 * Q γ - af - 2 / γ) bs bf
  let U := (segC es ef ⁻¹' horizontalStrip hR ∩ segC as af ⁻¹' horizontalStrip hR) ∩
    (seg₁ ⁻¹' V ∩ seg₂ ⁻¹' V)
  let F := fun t => R (segC es ef t) *
    (A (segC es ef t) (segC as af t) (segC bs bf t) * structureConstantH f γ μ (seg₁ t))
  let G := fun t => dualLC γ (segC es ef t) (segC as af t) (segC bs bf t) *
    R (segC as af t) * structureConstantH f γ μ (seg₂ t)
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U := fun t h0 h1 =>
    ⟨⟨segC_mem_horizontalStrip hhR es ef t, segC_mem_horizontalStrip hhR as af t⟩,
      segT_mem hγ hVmem hS₁ hE₁ h0 h1, segT_mem hγ hVmem hS₂ hE₂ h0 h1⟩
  have hFm : MeromorphicOn F U := fun t ht =>
    (segR_meromorphicOn hRm es ef t ht.1.1).fun_mul
      ((hAm t).fun_mul (segH_meromorphicOn hV hf hμ _ _ as af bs bf t ht.2.1))
  have hGm : MeromorphicOn G U := fun t ht =>
    ((meromorphicAt_dualLC_comp (analyticAt_segC es ef t) (analyticAt_segC as af t)
      (analyticAt_segC bs bf t)).fun_mul (segR_meromorphicOn hRm as af t ht.1.2)).fun_mul
      (segH_meromorphicOn hV hf hμ es ef _ _ bs bf t ht.2.2)
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, F t = G t := by
    filter_upwards [hstart, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht hI
    simp only [F, G, seg₁, seg₂, segC_ofReal,
      segH_ofReal P M hμ hfe (extendedSeiberg3_segment hγ hS₁ hE₁ hI.1.le hI.2.le),
      segH_ofReal P M hμ hfe (extendedSeiberg3_segment hγ hS₂ hE₂ hI.1.le hI.2.le)]
    convert ht using 4 <;> ring
  have hF1 : AnalyticAt ℂ F 1 := (segR_analyticAt_one hRe).mul
    (hA1.mul (segH_analyticAt_one hV hf hμ (hVmem _ hE₁) hs₁))
  have hG1 : AnalyticAt ℂ G 1 := by
    refine ((analyticAt_dualLC_comp (analyticAt_segC es ef 1) (analyticAt_segC as af 1)
      (analyticAt_segC bs bf 1) ?_ ?_ ?_ ?_).mul (segR_analyticAt_one hRa)).mul
      (segH_analyticAt_one hV hf hμ (hVmem _ hE₂) hs₂)
    all_goals simpa only [segC_one] using ‹AnalyticAt ℂ Complex.Gamma _›
  simpa only [F, G, seg₁, seg₂, segH_one P M hμ hfe hE₁, segH_one P M hμ hfe hE₂, segC_one]
    using eq_at_one_of_segment hseg hFm hGm hevent hF1 hG1

end DOZZ.Proofs

end
