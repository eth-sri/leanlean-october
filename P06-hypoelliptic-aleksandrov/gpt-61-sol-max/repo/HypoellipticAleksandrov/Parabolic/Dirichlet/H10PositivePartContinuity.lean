module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1PositivePart

open private PDE.H1Function.tendsto_eLpNorm_two_zero_of_ae_dominated from HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1PositivePart


/-!
# Continuity of positive parts in spatial `H¹₀`

This module proves the sharp graph-norm contraction of the positive-part
operation and its strong continuity on an arbitrary open set.
-/

 public section

open Filter MeasureTheory Set
open scoped ENNReal Topology



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

variable {α E : Type*}




private theorem tendsto_indicator_sub_indicator_of_tendsto
     [NormedAddCommGroup E] {f : ℕ → α → ℝ} {f₀ : α → ℝ}
    {g₀ : α → E} {x : α}
    (hf : Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hzero : f₀ x = 0 → g₀ x = 0) :
    Tendsto (fun n =>
      {y | 0 < f n y}.indicator g₀ x - {y | 0 < f₀ y}.indicator g₀ x)
      atTop (𝓝 0) := by
  rcases lt_trichotomy (f₀ x) 0 with hneg | hz | hpos
  ·
    apply (tendsto_congr' (((tendsto_order.1 hf).2 _ hneg).mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, hn.not_gt, hneg.not_gt, sub_self]
  ·
    have heq : (fun n =>
        {y | 0 < f n y}.indicator g₀ x - {y | 0 < f₀ y}.indicator g₀ x) =
        (fun _ => (0 : E)) := by
      funext n
      simp only [indicator_apply, (hzero hz)]
      split <;> split <;> simp
    rw [heq]
    exact tendsto_const_nhds
  ·
    apply (tendsto_congr' (((tendsto_order.1 hf).1 _ hpos).mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, hn, hpos, sub_self]

private theorem indicator_gradient_error_ae
     [MeasurableSpace α] [AddCommGroup E]
    {μ : Measure α} {f f₀ : α → ℝ} {g g₀ p p₀ q : α → E}
    (hp : p =ᵐ[μ] {y | 0 < f y}.indicator g)
    (hp₀ : p₀ =ᵐ[μ] {y | 0 < f₀ y}.indicator g₀)
    (hout : q =ᵐ[μ] fun x => p x - p₀ x) :
    q =ᵐ[μ] fun x =>
      {y | 0 < f y}.indicator (g - g₀) x +
        ({y | 0 < f y}.indicator g₀ x - {y | 0 < f₀ y}.indicator g₀ x) := by
  filter_upwards [hp, hp₀, hout] with x hpx hp₀x houtx
  rw [houtx, hpx, hp₀x]
  simp only [Pi.sub_apply, indicator_apply]
  split <;> split <;> simp

variable (hΩ : IsOpen Ω)

/-- Taking the positive part contracts the full spatial `H¹₀` graph norm,
with sharp constant one. -/
theorem norm_h10PositivePart_le
     (u : H10HilbertGraph hΩ) :
    ‖h10PositivePart hΩ u‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_h10HilbertGraph hΩ, norm_sq_h10HilbertGraph hΩ]
  exact add_le_add
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_valueCLM_h10PositivePart_le hΩ u))
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_gradientCLM_h10PositivePart_le hΩ u))

/-- The positive-part operation is strongly continuous on the spatial
`H¹₀` Hilbert graph. -/
theorem continuous_h10PositivePart  :
    Continuous (h10PositivePart hΩ ) := by
  rw [continuous_iff_seqContinuous]
  intro un u hun
  have hvalue : Tendsto (fun n => valueCLM hΩ (h10PositivePart hΩ (un n)))
      atTop (𝓝 (valueCLM hΩ (h10PositivePart hΩ u))) := by
    simpa only [valueCLM_h10PositivePart, Function.comp_def] using
      Lp.continuous_posPart.comp (valueCLM hΩ).continuous |>.tendsto u |>.comp hun

  have huGrad : Tendsto (fun n => gradientCLM hΩ (un n))
      atTop (𝓝 (gradientCLM hΩ u)) :=
    ((gradientCLM hΩ).continuous.tendsto u).comp hun
  let μ := PDE.volumeOn Ω
  let f : ℕ → PDE.ScalarField d := fun n => valueCLM hΩ (un n)
  let f₀ : PDE.ScalarField d := valueCLM hΩ u
  let g : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) :=
    fun n => gradientCLM hΩ (un n)
  let g₀ : PDE.Vec d → WithLp 2 (PDE.Vec d) := gradientCLM hΩ u

  let A₀  := ({y | 0 < f₀ y}.indicator g₀)
  let R  := fun n x =>
    {y | 0 < f n y}.indicator g₀ x - A₀ x
  have hfMeasure  := tendstoInMeasure_of_tendsto_Lp (((valueCLM hΩ).continuous.tendsto u).comp hun)

  have hgrad : Tendsto
      (fun n => gradientCLM hΩ (h10PositivePart hΩ (un n)))
      atTop (𝓝 (gradientCLM hΩ (h10PositivePart hΩ u))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hfirst : Tendsto (fun n =>
        eLpNorm ({y | 0 < f n y}.indicator (g n - g₀)) 2 μ)
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'
          (fun n => gradientCLM hΩ (un n)) (gradientCLM hΩ u)).1 huGrad)
        (fun n => zero_le') (fun n => eLpNorm_indicator_le _
          (measurableSet_lt measurable_const
            (Lp.stronglyMeasurable (valueCLM hΩ (un n))).measurable))



    refine (show Tendsto (fun n =>
        eLpNorm ({y | 0 < f n y}.indicator (g n - g₀) + R n) 2 μ)
        atTop (𝓝 0) by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (by simpa only [zero_add] using hfirst.add (by
              apply tendsto_of_subseq_tendsto
              intro ns hns
              obtain ⟨ms, -, hae⟩ :=
                (hfMeasure.comp hns).exists_seq_tendsto_ae
              refine ⟨ms, ?_⟩
              apply _root_.PDE.H1Function.tendsto_eLpNorm_two_zero_of_ae_dominated
              · intro n
                apply AEStronglyMeasurable.sub
                · rw [aestronglyMeasurable_indicator_iff₀
                    (nullMeasurableSet_lt aemeasurable_const
                      (Lp.aestronglyMeasurable (valueCLM hΩ (un (ns (ms n))))).aemeasurable)]
                  exact (Lp.aestronglyMeasurable (gradientCLM hΩ u)).restrict
                · rw [aestronglyMeasurable_indicator_iff₀
                    (nullMeasurableSet_lt aemeasurable_const
                      (Lp.aestronglyMeasurable (valueCLM hΩ u)).aemeasurable)]
                  exact (Lp.aestronglyMeasurable (gradientCLM hΩ u)).restrict
              · exact (Lp.memLp (gradientCLM hΩ u))
              · intro n
                filter_upwards with x
                simp only [R, A₀, f, f₀, g₀, indicator_apply]
                split <;> split <;> simp
              · filter_upwards [hae, gradientCLM_ae_zero_on_level_set hΩ u 0] with x hx hgrad
                exact tendsto_indicator_sub_indicator_of_tendsto hx hgrad))
          (fun n => zero_le')
          (fun n => eLpNorm_add_le (by norm_num))).congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    simpa only [μ, f, f₀, g, g₀, R, A₀, Pi.add_def, Pi.sub_def] using
      (indicator_gradient_error_ae

      (gradientCLM_h10PositivePart hΩ (un n))
      (gradientCLM_h10PositivePart hΩ u)
      (Filter.Eventually.of_forall fun _ => rfl)).symm
  rw [Metric.tendsto_atTop] at hvalue hgrad ⊢
  intro ε hε

  obtain ⟨Nv, hNv⟩ := hvalue (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  obtain ⟨Ng, hNg⟩ := hgrad (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  refine ⟨max Nv Ng, fun n hn => ?_⟩
  have hv := hNv n (le_trans (le_max_left _ _) hn)
  have hg := hNg n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm, Function.comp_apply]
  change ‖h10PositivePart hΩ (un n) - h10PositivePart hΩ u‖ < ε
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).1
  rw [norm_sq_h10HilbertGraph hΩ]
  simp only [map_sub]
  rw [dist_eq_norm] at hv hg
  have hv2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hv
  have hg2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hg
  have hdivsq : (ε / Real.sqrt 2) ^ 2 = ε ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hdivsq] at hv2 hg2
  linarith

end HypoellipticAleksandrov.Parabolic.Dirichlet
