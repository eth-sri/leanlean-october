module

public import RequestProject.PlanarTypes

public import RequestProject.LocalDirichletBoundaryRegularity
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Mixed L² derivatives on an actual open rectangle

Two one-dimensional FTC estimates, followed by Fubini, control every
interior value and give a uniform square-root modulus of continuity.
The boundary values are obtained by completing the uniformly continuous
interior function; no boundary derivative or boundary value is assumed.

For side lengths X,Y the squared point-value bound is
`4/(X*Y) Eu + 4*X/Y Ex + 4*Y/X Ey + 4*X*Y Exy`.
The hypotheses are genuine interior derivatives and genuine L² energy.
Applying this result to a derivative requires its four corresponding L²
energies. In particular this file does not supply the still necessary
higher-order elliptic estimates or assert a smooth conformal collar.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter

/-- A quadratic triangle estimate used without expanding a concrete
Sobolev or Lp representation. -/
theorem rectangular_norm_add_sq_le (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := norm_add_le z w
  have hs  :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- FTC and the actual L² inner-product Cauchy--Schwarz inequality.
Both endpoints are interior; no endpoint regularity is imposed. -/
theorem rectangular_interval_sub_norm_sq_le  {v dv : ComplexCurve}
    (hv : ContinuousOn v (Ioo a b)) (hdv : ContinuousOn dv (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt v (dv t) t)
    (hm : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioo a b))
     (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ‖v t - v s‖ ^ 2 ≤ |t - s| * ∫ r in Ioo a b, ‖dv r‖ ^ 2 := by
  have hord {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
      ‖v t - v s‖ ^ 2 ≤ (t - s) * ∫ r in Ioo a b, ‖dv r‖ ^ 2 := by
    let μ := volume.restrict (Ioc s t)
    have hsub : Ioc s t ⊆ Ioo a b := by
      grind
    have hdL  :=
      (memLp_two_iff_integrable_sq_norm
        ((hdv.mono hsub).aestronglyMeasurable measurableSet_Ioc)).mpr (hm.mono_set hsub)
    have hi  :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr (hdL.integrable (by norm_num))
    have hcc : Icc s t ⊆ Ioo a b := by
      grind
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hv.mono hcc)
      (fun r hr => hd r (hcc ⟨hr.1.le, hr.2.le⟩)) hi
    have h1 : MemLp (fun _ : ℝ => (1 : ℂ)) 2 μ := memLp_const 1
    have hinner : (∫ r in s..t, dv r) = inner ℂ (h1.toLp _) (hdL.toLp _) := by
      rw [intervalIntegral.integral_of_le hst, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [h1.coeFn_toLp, hdL.coeFn_toLp] with r hr₁ hr₂
      simp_all
    have hn : ‖∫ r in s..t, dv r‖ ≤ ‖h1.toLp _‖ * ‖hdL.toLp _‖ := by
      rw [hinner]
      exact norm_inner_le_norm _ _
    have hn₂ := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    have hconst : ‖h1.toLp _‖ ^ 2 = t - s := by
      rw [norm_sq_toLp_eq_integral]
      simp [μ, Measure.real, hst]
    have hnorm  :=
      norm_sq_toLp_eq_integral hdL
    rw [mul_pow, hconst, hnorm, hFTC] at hn₂
    have hmono  :=
      integral_mono_measure (Measure.restrict_mono_set volume hsub)
        (Eventually.of_forall fun _ => sq_nonneg _) hm
    nlinarith
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hord hs ht hst
  · have h := hord ht hs hts
    rw [norm_sub_rev] at h
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using h

/-- Averaging the FTC estimate over the whole interval gives an
interior point-value bound in terms of actual value and derivative energy. -/
theorem rectangular_interval_point_norm_sq_le  (hab : a < b)
    {v dv : ComplexCurve} (hv : ContinuousOn v (Ioo a b))
    (hdv : ContinuousOn dv (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt v (dv t) t)
    (hmv : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioo a b))
    (hmd : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioo a b))
     (ht : t ∈ Ioo a b) :
    ‖v t‖ ^ 2 ≤ (2 / (b - a)) * (∫ s in Ioo a b, ‖v s‖ ^ 2) +
      2 * (b - a) * (∫ s in Ioo a b, ‖dv s‖ ^ 2) := by
  have hE : 0 ≤ ∫ s in Ioo a b, ‖dv s‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hp (s : ℝ) (hs : s ∈ Ioo a b) :
      ‖v t‖ ^ 2 ≤ 2 * ‖v s‖ ^ 2 +
        2 * (b - a) * (∫ r in Ioo a b, ‖dv r‖ ^ 2) := by
    have hdiff := rectangular_interval_sub_norm_sq_le hv hdv hd hmd hs ht
    have habs : |t - s| ≤ b - a := abs_le.mpr (by grind)
    have hsum := rectangular_norm_add_sq_le (v s) (v t - v s)
    have heq : v s + (v t - v s) = v t := by abel
    rw [heq] at hsum
    nlinarith
  have hi : Integrable (fun s => 2 * ‖v s‖ ^ 2 +
      2 * (b - a) * (∫ r in Ioo a b, ‖dv r‖ ^ 2)) (volume.restrict (Ioo a b)) :=
    (hmv.const_mul 2).add (integrable_const _)
  have hmean := integral_mono_ae (integrable_const (‖v t‖ ^ 2)) hi
    (ae_restrict_of_forall_mem measurableSet_Ioo hp)
  rw [integral_add (hmv.const_mul 2) (integrable_const _), integral_const_mul] at hmean
  simp only [integral_const, smul_eq_mul] at hmean
  have hvol : (volume.restrict (Ioo a b)).real univ = b - a := by
    simp [hab.le]
  rw [hvol] at hmean
  apply (mul_le_mul_iff_of_pos_right (sub_pos.mpr hab)).mp
  calc
    ‖v t‖ ^ 2 * (b - a) ≤
        2 * (∫ s in Ioo a b, ‖v s‖ ^ 2) +
          (b - a) * (2 * (b - a) * (∫ s in Ioo a b, ‖dv s‖ ^ 2)) := by
      nlinarith [hmean]
    _ = ((2 / (b - a)) * (∫ s in Ioo a b, ‖v s‖ ^ 2) +
        2 * (b - a) * (∫ s in Ioo a b, ‖dv s‖ ^ 2)) * (b - a) := by
      field_simp [ne_of_gt (sub_pos.mpr hab)]

/-- Unitary real product coordinates; these are ordinary Lebesgue energies. -/
def rectangularL2Energy a b c d (f : ℝ × ℝ → ℂ)  :=
  ∫ p, ‖f p‖ ^ 2 ∂(volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))

theorem rectangularL2Energy_nonneg a b c d f :
    0 ≤ rectangularL2Energy a b c d f := integral_nonneg (fun _ => sq_nonneg _)

theorem rectangularL2Energy_swap a b c d f :
    rectangularL2Energy c d a b (fun p => f (p.2, p.1)) = rectangularL2Energy a b c d f := (integral_prod_swap fun p => ‖f p‖ ^ 2)

/-- Every vertical slice has finite energy, including the slices which
Fubini alone does not select. The horizontal FTC bounds remove the
exceptional set without any boundary regularity assumption. -/
theorem rectangular_vertical_slice_energy  (hab : a < b)
    
    (hf : ContinuousOn f (Ioo a b ×ˢ Ioo c d))
    (hg : ContinuousOn g (Ioo a b ×ˢ Ioo c d))
    (hd : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      HasDerivAt (fun s => f (s, y)) (g (x, y)) x)
    (hfm : Integrable (fun p => ‖f p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    (hgm : Integrable (fun p => ‖g p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
     (hx : x ∈ Ioo a b) :
    IntegrableOn (fun y => ‖f (x, y)‖ ^ 2) (Ioo c d) ∧
      (∫ y in Ioo c d, ‖f (x, y)‖ ^ 2) ≤
        (2 / (b - a)) * rectangularL2Energy a b c d f +
          2 * (b - a) * rectangularL2Energy a b c d g := by
  have hfvert  :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hx, hy⟩)
  have hR : Integrable (fun y =>
      (2 / (b - a)) * (∫ s in Ioo a b, ‖f (s, y)‖ ^ 2) +
        2 * (b - a) * (∫ s in Ioo a b, ‖g (s, y)‖ ^ 2))
      (volume.restrict (Ioo c d)) :=
    (hfm.integral_prod_right.const_mul _).add (hgm.integral_prod_right.const_mul _)
  have hbound : ∀ᵐ y ∂volume.restrict (Ioo c d),
      ‖f (x, y)‖ ^ 2 ≤
        (2 / (b - a)) * (∫ s in Ioo a b, ‖f (s, y)‖ ^ 2) +
          2 * (b - a) * (∫ s in Ioo a b, ‖g (s, y)‖ ^ 2) := by
    filter_upwards [hfm.prod_left_ae, hgm.prod_left_ae, ae_restrict_mem measurableSet_Ioo]
      with y hyf hyg hy
    have hfc  :=
      hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hy⟩)
    have hgc  :=
      hg.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hy⟩)
    exact rectangular_interval_point_norm_sq_le hab hfc hgc (fun s hs => hd s hs y hy)
      hyf hyg hx
  have hslice : IntegrableOn (fun y => ‖f (x, y)‖ ^ 2) (Ioo c d) :=
    hR.mono' ((hfvert.norm.pow 2).aestronglyMeasurable measurableSet_Ioo)
      (hbound.mono fun y hy => by
        simp_all)
  refine ⟨hslice, ?_⟩
  have hi := integral_mono_ae hslice hR hbound
  rw [integral_add (hfm.integral_prod_right.const_mul _)
    (hgm.integral_prod_right.const_mul _), integral_const_mul, integral_const_mul] at hi
  simpa only [rectangularL2Energy, ← integral_prod_symm _ hfm,
    ← integral_prod_symm _ hgm] using hi

theorem rectangular_horizontal_slice_energy  (hcd : c < d)
    
    (hf : ContinuousOn f (Ioo a b ×ˢ Ioo c d))
    (hg : ContinuousOn g (Ioo a b ×ˢ Ioo c d))
    (hd : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      HasDerivAt (fun t => f (x, t)) (g (x, y)) y)
    (hfm : Integrable (fun p => ‖f p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    (hgm : Integrable (fun p => ‖g p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
     (hy : y ∈ Ioo c d) :
    IntegrableOn (fun x => ‖f (x, y)‖ ^ 2) (Ioo a b) ∧
      (∫ x in Ioo a b, ‖f (x, y)‖ ^ 2) ≤
        (2 / (d - c)) * rectangularL2Energy a b c d f +
          2 * (d - c) * rectangularL2Energy a b c d g := by
  have hfc : ContinuousOn (fun p : ℝ × ℝ => f (p.2, p.1)) (Ioo c d ×ˢ Ioo a b) :=
    hf.comp continuous_swap.continuousOn (fun _ hp => ⟨hp.2, hp.1⟩)
  have hgc : ContinuousOn (fun p : ℝ × ℝ => g (p.2, p.1)) (Ioo c d ×ˢ Ioo a b) :=
    hg.comp continuous_swap.continuousOn (fun _ hp => ⟨hp.2, hp.1⟩)
  have h := rectangular_vertical_slice_energy hcd hfc hgc
    (fun t ht s hs => hd s hs t ht) hfm.swap hgm.swap hy
  simpa  [rectangularL2Energy_swap] using h

/-- The four true interior directional identities used by tensor FTC.
The mixed derivative is required in both orders; for a smooth function
this is proved from symmetry of its second real differential. -/
structure IsRectangularMixedDifferentiable (a b c d : ℝ)
    (u ux uy uxy : ℝ × ℝ → ℂ) : Prop where
  continuous_u : ContinuousOn u (Ioo a b ×ˢ Ioo c d)
  continuous_ux : ContinuousOn ux (Ioo a b ×ˢ Ioo c d)
  continuous_uy : ContinuousOn uy (Ioo a b ×ˢ Ioo c d)
  continuous_uxy : ContinuousOn uxy (Ioo a b ×ˢ Ioo c d)
  horizontal_u : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
    HasDerivAt (fun s => u (s, y)) (ux (x, y)) x
  vertical_u : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
    HasDerivAt (fun t => u (x, t)) (uy (x, y)) y
  horizontal_uy : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
    HasDerivAt (fun s => uy (s, y)) (uxy (x, y)) x
  vertical_ux : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
    HasDerivAt (fun t => ux (x, t)) (uxy (x, y)) y

def rectangularMixedPointBound a b c d u ux uy uxy  :=
  (2 / (d - c)) * ((2 / (b - a)) * rectangularL2Energy a b c d u +
    2 * (b - a) * rectangularL2Energy a b c d ux) +
  2 * (d - c) * ((2 / (b - a)) * rectangularL2Energy a b c d uy +
    2 * (b - a) * rectangularL2Energy a b c d uxy)

section
variable {a b c d } (hab : a < b) (hcd : c < d) {u ux uy uxy } (h : IsRectangularMixedDifferentiable a b c d u ux uy uxy) (hu : Integrable (fun p => ‖u p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)))) (hx : Integrable (fun p => ‖ux p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)))) (hy : Integrable (fun p => ‖uy p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)))) (hxy : Integrable (fun p => ‖uxy p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))

include a b c d hab hcd u ux uy uxy h hu hx hy hxy in
/-- The genuine uniform point-value estimate. Its constants do not
depend on distance from any of the four edges. -/
theorem rectangular_mixed_point_norm_sq_le
     (hp : p ∈ Ioo a b ×ˢ Ioo c d) :
    ‖u p‖ ^ 2 ≤ rectangularMixedPointBound a b c d u ux uy uxy := by
  obtain ⟨huv, hbu⟩ := rectangular_vertical_slice_energy hab h.continuous_u h.continuous_ux
    h.horizontal_u hu hx hp.1
  obtain ⟨hyv, hby⟩ := rectangular_vertical_slice_energy hab h.continuous_uy h.continuous_uxy
    h.horizontal_uy hy hxy hp.1
  have huc  :=
    h.continuous_u.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hp.1, ht⟩)
  have hyc  :=
    h.continuous_uy.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hp.1, ht⟩)
  have hb := rectangular_interval_point_norm_sq_le hcd huc hyc
    ((h.vertical_u p.1 hp.1)) huv hyv hp.2
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left hbu (div_nonneg (by norm_num) (sub_pos.mpr hcd).le))
    (mul_le_mul_of_nonneg_left hby (mul_nonneg (by norm_num) (sub_pos.mpr hcd).le)))

/-- Tensor FTC gives a square-root modulus in both coordinates,
using only the true first and mixed derivative energies. -/
theorem rectangular_mixed_sub_norm_sq_le  (hab : a < b) (hcd : c < d)
     (h : IsRectangularMixedDifferentiable a b c d u ux uy uxy)
    (hx : Integrable (fun p => ‖ux p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    (hy : Integrable (fun p => ‖uy p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    (hxy : Integrable (fun p => ‖uxy p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
     (hp : p ∈ Ioo a b ×ˢ Ioo c d) (hq : q ∈ Ioo a b ×ˢ Ioo c d) :
    ‖u p - u q‖ ^ 2 ≤
      2 * |p.1 - q.1| * ((2 / (d - c)) * rectangularL2Energy a b c d ux +
        2 * (d - c) * rectangularL2Energy a b c d uxy) +
      2 * |p.2 - q.2| * ((2 / (b - a)) * rectangularL2Energy a b c d uy +
        2 * (b - a) * rectangularL2Energy a b c d uxy) := by
  obtain ⟨hxh, hbx⟩ := rectangular_horizontal_slice_energy hcd h.continuous_ux h.continuous_uxy
    h.vertical_ux hx hxy hp.2
  obtain ⟨hyv, hby⟩ := rectangular_vertical_slice_energy hab h.continuous_uy h.continuous_uxy
    h.horizontal_uy hy hxy hq.1
  have hucx  :=
    h.continuous_u.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => ⟨hs, hp.2⟩)
  have hxc  :=
    h.continuous_ux.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => ⟨hs, hp.2⟩)
  have hxsub := rectangular_interval_sub_norm_sq_le hucx hxc
    (fun s hs => h.horizontal_u s hs p.2 hp.2) hxh hq.1 hp.1
  have hxbound := hxsub.trans (mul_le_mul_of_nonneg_left hbx (abs_nonneg _))
  have hucy  :=
    h.continuous_u.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hq.1, ht⟩)
  have hyc  :=
    h.continuous_uy.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hq.1, ht⟩)
  have hysub := rectangular_interval_sub_norm_sq_le hucy hyc
    ((h.vertical_u q.1 hq.1)) hyv hq.2 hp.2
  have hybound := hysub.trans (mul_le_mul_of_nonneg_left hby (abs_nonneg _))
  have hsum := rectangular_norm_add_sq_le (u p - u (q.1, p.2)) (u (q.1, p.2) - u q)
  grind

theorem rectangular_mixed_uniformContinuousOn  (hab : a < b) (hcd : c < d)
     (h : IsRectangularMixedDifferentiable a b c d u ux uy uxy)
    (hx : Integrable (fun p => ‖ux p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    (hy : Integrable (fun p => ‖uy p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    (hxy : Integrable (fun p => ‖uxy p‖ ^ 2) ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)))) :
    UniformContinuousOn u (Ioo a b ×ˢ Ioo c d) := by
  let Bx := (2 / (d - c)) * rectangularL2Energy a b c d ux +
    2 * (d - c) * rectangularL2Energy a b c d uxy
  let By := (2 / (b - a)) * rectangularL2Energy a b c d uy +
    2 * (b - a) * rectangularL2Energy a b c d uxy
  have hEx := rectangularL2Energy_nonneg a b c d ux
  have hEy := rectangularL2Energy_nonneg a b c d uy
  have hExy := rectangularL2Energy_nonneg a b c d uxy
  have hBx : 0 ≤ Bx := by positivity
  have hBy : 0 ≤ By := by positivity
  let C := 2 * Bx + 2 * By
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  refine ⟨ε ^ 2 / (C + 1), div_pos (sq_pos_of_pos hε) (by positivity), ?_⟩
  intro p hp q hq hpq
  have hsub := rectangular_mixed_sub_norm_sq_le hab hcd h hx hy hxy hp hq
  have hfst : |p.1 - q.1| ≤ dist p q := by
    exact le_max_left _ _
  have hsnd : |p.2 - q.2| ≤ dist p q := by
    rw [Prod.dist_eq, ← Real.dist_eq]
    exact le_max_right _ _
  have hsmall  := (lt_div_iff₀ (by positivity)).mp hpq
  rw [dist_eq_norm]
  nlinarith [(dist_nonneg : 0 ≤ dist p q), norm_nonneg (u p - u q)]

include a b c d hab hcd u ux uy uxy h hu hx hy hxy in
/-- A genuine continuous boundary representative, obtained by uniform
completion of the interior rectangle. It retains the same energy bound. -/
theorem rectangular_mixed_exists_continuous_extension :
    ∃ v : ℝ × ℝ → ℂ, ContinuousOn v (Icc a b ×ˢ Icc c d) ∧
      EqOn v u (Ioo a b ×ˢ Ioo c d) ∧
      ∀ p ∈ Icc a b ×ˢ Icc c d,
        ‖v p‖ ^ 2 ≤ rectangularMixedPointBound a b c d u ux uy uxy := by
  classical
  let R := Ioo a b ×ˢ Ioo c d
  let e : R → closure R := inclusion subset_closure
  have he : IsUniformInducing e := (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hdense : DenseRange e := (denseRange_inclusion_iff subset_closure).mpr subset_rfl
  have huc  :=
    uniformContinuousOn_iff_restrict.mp (rectangular_mixed_uniformContinuousOn hab hcd h hx hy hxy)
  let V  := (he.isDenseInducing hdense).extend (fun p : R => u p)
  have hV  := (uniformContinuous_uniformly_extend he hdense huc).continuous
  have hVe (p : R) : V (e p) = u p := uniformly_extend_of_ind he hdense huc p
  have hclosed : closure R = Icc a b ×ˢ Icc c d := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo hcd.ne]
  let v  := fun p => if hp : p ∈ closure R then V ⟨p, hp⟩ else 0
  have hv : ContinuousOn v (closure R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun p : closure R => v p)
    have heq : (fun p : closure R => v p) = V := by
      funext p
      exact dif_pos p.property
    rw [heq]
    exact hV
  have hbound : ∀ p : closure R,
      ‖V p‖ ^ 2 ≤ rectangularMixedPointBound a b c d u ux uy uxy := by
    have hA : IsClosed {p : closure R | ‖V p‖ ^ 2 ≤ rectangularMixedPointBound a b c d u ux uy uxy} :=
      isClosed_le (hV.norm.pow 2) continuous_const
    have hrange : range e ⊆ {p : closure R | ‖V p‖ ^ 2 ≤ rectangularMixedPointBound a b c d u ux uy uxy} := by
      rintro _ ⟨p, rfl⟩
      change ‖V (e p)‖ ^ 2 ≤ rectangularMixedPointBound a b c d u ux uy uxy
      grind only [rectangular_mixed_point_norm_sq_le]
    intro p
    exact closure_minimal hrange hA (hdense p)
  refine ⟨v, hclosed ▸ hv, ?_, ?_⟩
  · intro p hp
    have hpc : p ∈ closure R := subset_closure hp
    have hep : e ⟨p, hp⟩ = ⟨p, hpc⟩ := rfl
    simpa only [v, dif_pos hpc, hep] using hVe ⟨p, hp⟩
  grind

end


/-- The genuine real-coordinate map, without an artificial measure scale. -/
def rectangularComplexCoord (p : ℝ × ℝ)  := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

theorem continuous_rectangularComplexCoord : Continuous rectangularComplexCoord :=
  (Complex.ofRealCLM.continuous.comp continuous_fst).add
    ((Complex.ofRealCLM.continuous.comp continuous_snd).mul continuous_const)

theorem rectangularComplexCoord_mem_halfBox  
    (hp : p ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b) :
    rectangularComplexCoord p ∈ smoothDirichletHalfBox a b := by
  simpa [smoothDirichletHalfBox, rectangularComplexCoord, abs_lt] using hp



section
variable {a b } {u : PlaneMap} (hu : RealSmoothOn u (smoothDirichletHalfBox a b))
include a b u hu

theorem rectangular_halfBox_horizontal_hasDerivAt
     (hx : x ∈ Ioo (-a) a) (hy : y ∈ Ioo (0 : ℝ) b) :
    HasDerivAt (fun s : ℝ => u (rectangularComplexCoord (s, y)))
      (dirD u 1 (rectangularComplexCoord (x, y))) x := (HasFDerivAt.comp_hasDerivAt x (DifferentiableAt.hasFDerivAt (DifferentiableOn.differentiableAt (ContDiffOn.differentiableOn hu (of_eq_true (Eq.trans (congrArg Not (Eq.trans WithTop.coe_eq_zero._simp_1 ENat.top_ne_zero._simp_1)) not_false_eq_true))) (IsOpen.mem_nhds (isOpen_smoothDirichletHalfBox a b) (rectangularComplexCoord_mem_halfBox ⟨hx, hy⟩)))) (id (HasDerivAt.add_const (↑y * Complex.I) (HasDerivAt.ofReal_comp (hasDerivAt_id x)))))

/-- A genuinely smooth interior function supplies all four tensor
FTC identities. In particular the reversed mixed identity is proved. -/
theorem rectangular_halfBox_mixedDifferentiable :
    IsRectangularMixedDifferentiable (-a) a 0 b
      (u ∘ rectangularComplexCoord) ((dirD u 1) ∘ rectangularComplexCoord)
      ((dirD u Complex.I) ∘ rectangularComplexCoord)
      ((dirD (dirD u 1) Complex.I) ∘ rectangularComplexCoord) := by
  have hU := isOpen_smoothDirichletHalfBox a b
  have hx := dirichlet_contDiffOn_dirD hU hu 1
  have hy := dirichlet_contDiffOn_dirD hU hu Complex.I
  have hxy := dirichlet_contDiffOn_dirD hU hx Complex.I
  have hmap : MapsTo rectangularComplexCoord (Ioo (-a) a ×ˢ Ioo (0 : ℝ) b)
      (smoothDirichletHalfBox a b) := fun _ hp => rectangularComplexCoord_mem_halfBox hp
  refine ⟨hu.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap,
    hx.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap,
    hy.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap,
    hxy.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap,
    ?_, ?_, ?_, ?_⟩
  · grind only [rectangular_halfBox_horizontal_hasDerivAt, PolyaNeumann.rectangularComplexCoord]
  · intro x hx y hy
    exact dirichlet_halfBox_vertical_hasDerivAt hu (abs_lt.mpr hx) hy
  · grind [rectangular_halfBox_horizontal_hasDerivAt, rectangularComplexCoord_mem_halfBox, dirichlet_dirD_comm, PolyaNeumann.rectangularComplexCoord]
  · intro x hx₀ y hy₀
    exact dirichlet_halfBox_vertical_hasDerivAt hx (abs_lt.mpr hx₀) hy₀

end


/-- Exact physical/product energy identification. The real-coordinate
map has Jacobian one, so the four energies are the actual H¹/H² ones. -/
theorem rectangularL2Energy_eq_halfBox_integral  (hb : 0 < b) 
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    rectangularL2Energy (-a) a 0 b (g ∘ rectangularComplexCoord) =
      ∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2 := by
  have hprod := dirichlet_halfBox_sq_integrable_real_prod hg
  have hi := integral_prod
    (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * Complex.I)‖ ^ 2) hprod
  have hphysical := dirichlet_halfBox_sq_integral_eq_real_prod hb hg
  rw [hphysical]
  simpa  [rectangularL2Energy, rectangularComplexCoord, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo] using hi

def dirichletRectangularMixedEnergyBound a b u  :=
  (2 / b) * ((2 / (a + a)) * (∫ z in smoothDirichletHalfBox a b, ‖u z‖ ^ 2) +
    2 * (a + a) * (∫ z in smoothDirichletHalfBox a b, ‖dirD u 1 z‖ ^ 2)) +
  2 * b * ((2 / (a + a)) * (∫ z in smoothDirichletHalfBox a b, ‖dirD u Complex.I z‖ ^ 2) +
    2 * (a + a) * (∫ z in smoothDirichletHalfBox a b, ‖dirD (dirD u 1) Complex.I z‖ ^ 2))

theorem rectangularMixedPointBound_eq_halfBox  (hb : 0 < b) 
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hy : MemLp (dirD u Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    rectangularMixedPointBound (-a) a 0 b (u ∘ rectangularComplexCoord)
      ((dirD u 1) ∘ rectangularComplexCoord) ((dirD u Complex.I) ∘ rectangularComplexCoord)
      ((dirD (dirD u 1) Complex.I) ∘ rectangularComplexCoord) =
        dirichletRectangularMixedEnergyBound a b u := by
  simp_all [rectangularMixedPointBound, rectangularL2Energy_eq_halfBox_integral, dirichletRectangularMixedEnergyBound]

/-- Actual L² value, first derivatives and mixed derivative imply a
continuous representative on the full closed half rectangle and a
uniform bound there. No boundary values or derivatives are premises. -/
theorem dirichlet_halfBox_exists_continuous_extension  (ha : 0 < a) (hb : 0 < b)
     (hs : RealSmoothOn u (smoothDirichletHalfBox a b))
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hy : MemLp (dirD u Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∃ v : PlaneMap, ContinuousOn v (smoothDirichletClosedHalfBox a b) ∧
      EqOn v u (smoothDirichletHalfBox a b) ∧
      ∀ z ∈ smoothDirichletClosedHalfBox a b,
        ‖v z‖ ^ 2 ≤ dirichletRectangularMixedEnergyBound a b u := by
  have h := rectangular_halfBox_mixedDifferentiable hs
  obtain ⟨V, hVc, hVu, hVbound⟩ := rectangular_mixed_exists_continuous_extension
    (show -a < a by linarith) hb h
    (dirichlet_halfBox_sq_integrable_real_prod hm) (dirichlet_halfBox_sq_integrable_real_prod hx)
    (dirichlet_halfBox_sq_integrable_real_prod hy) (dirichlet_halfBox_sq_integrable_real_prod hxy)
  let v : PlaneMap := fun z => V (z.re, z.im)
  have hmap : MapsTo (fun z : ℂ => (z.re, z.im)) (smoothDirichletClosedHalfBox a b)
      (Icc (-a) a ×ˢ Icc (0 : ℝ) b) := by
    intro z hz
    exact ⟨abs_le.mp hz.1, hz.2⟩
  refine ⟨v, hVc.comp (Complex.continuous_re.prodMk Complex.continuous_im).continuousOn hmap, ?_, ?_⟩
  · intro z hz
    have hzP : (z.re, z.im) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := ⟨abs_lt.mp hz.1, hz.2⟩
    have heq := hVu hzP
    have hzcoord : rectangularComplexCoord (z.re, z.im) = z := by
      simp_all [rectangularComplexCoord, PolyaNeumann.rectangularComplexCoord]
    measurability
  · intro z hz
    have hbound := hVbound (z.re, z.im) (hmap hz)
    grind only [rectangularMixedPointBound_eq_halfBox]

end PolyaNeumann
