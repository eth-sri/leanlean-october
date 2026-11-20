module

public import RequestProject.LipschitzChange
public import RequestProject.Defs

/-!
# Bi-Lipschitz changes of variables and the `L²` pullback

For a homeomorphism `f` of the plane which is `K`-Lipschitz on an open set `Ω` and whose inverse
is `K`-Lipschitz on `f(Ω)`:

* `ae_inv_sq_le_abs_det`: `|det Df| ≥ K⁻²` almost everywhere on `Ω`;
* `quasiMeasurePreserving_restrict`, `quasiMeasurePreserving_symm_restrict`: `f` and `f⁻¹` are
  quasi-measure-preserving between `Ω` and `f(Ω)`;
* `lintegral_image_bilip`, `integral_image_bilip`: the change of variables formulas
  `∫_{f(Ω)} g = ∫_Ω |det Df| g ∘ f`;
* `bilipPull`: the pullback `L²(f(Ω)) ≃ L²(Ω)`, `v ↦ v ∘ f`, with
  `⟨v, w⟩_{L²(f(Ω))} = ∫_Ω |det Df| ⟨v ∘ f, w ∘ f⟩` (`inner_eq_integral_bilipPull`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : NNReal}

/-- A Lipschitz constant may be increased. -/
lemma lipschitzOnWith_weaken {F : ℂ → ℂ} {s : Set ℂ} {K' : NNReal} (h : LipschitzOnWith K F s)
    (hKK : K ≤ K') : LipschitzOnWith K' F s := fun _ hx _ hy =>
  (h hx hy).trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr hKK) _)

/-- A map that is Lipschitz on an open set is differentiable almost everywhere on it. -/
lemma ae_differentiableAt_of_lipschitzOnWith {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : LipschitzOnWith K F U) : ∀ᵐ x ∂(volume.restrict U), DifferentiableAt ℝ F x := by
  have h := hF.ae_differentiableWithinAt_of_mem (μ := volume)
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [h] with x hx hxU
  exact (hx hxU).differentiableAt (hU.mem_nhds hxU)

/-- The pushforward of area from the source is dominated by `K²` times
area on the target. Only the inverse Lipschitz estimate is needed. -/
lemma map_restrict_le_bilip {V : Set ℂ} (hmap : MapsTo f Ω V) (hg : LipschitzOnWith K f.symm V) :
    (volume.restrict Ω).map f ≤ (K : ENNReal)^2 • volume.restrict V := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.map_apply f.continuous.measurable hs, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hs, Measure.restrict_apply (f.continuous.measurable hs)]
  refine (measure_mono ?_).trans (volume_image_le_lipschitz (hg.mono (inter_subset_right (s := s))))
  exact fun x hx => ⟨f x, ⟨hx.1, hmap hx.2⟩, f.symm_apply_apply x⟩

section

variable (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm (f '' Ω))

include hg in
lemma quasiMeasurePreserving_restrict :
    Measure.QuasiMeasurePreserving f (volume.restrict Ω) (volume.restrict (f '' Ω)) :=
  ⟨f.continuous.measurable, Measure.absolutelyContinuous_of_le_smul (map_restrict_le_bilip (mapsTo_image ..) hg)⟩

lemma symm_mapsTo_image : MapsTo f.symm (f '' Ω) Ω := by rintro _ ⟨x, hx, rfl⟩; simpa

include hf in
lemma quasiMeasurePreserving_symm_restrict :
    Measure.QuasiMeasurePreserving f.symm (volume.restrict (f '' Ω)) (volume.restrict Ω) :=
  ⟨f.symm.continuous.measurable, Measure.absolutelyContinuous_of_le_smul (map_restrict_le_bilip symm_mapsTo_image hf)⟩

include hf hΩ in
/-- Change of variables for integrals along a bi-Lipschitz map. -/
lemma integral_image_bilip (g : ℂ → ℂ) :
    ∫ y in f '' Ω, g y = ∫ x in Ω, |(fderiv ℝ f x).det| • g (f x) := by
  obtain ⟨s, _, hs, he, hi, hd⟩ := differentiability_core hΩ hf
  rw [← setIntegral_congr_set hi, ← setIntegral_congr_set he]
  exact integral_image_eq_integral_abs_det_fderiv_smul volume hs hd f.injective.injOn g

include hf hg hΩ in
/-- The Jacobian of a bi-Lipschitz map is bounded below: `|det Df| ≥ K⁻²` a.e. on `Ω`. -/
lemma ae_inv_sq_le_abs_det :
    ∀ᵐ x ∂(volume.restrict Ω), ((K : ℝ) ^ 2)⁻¹ ≤ |(fderiv ℝ f x).det| := by
  have hU  := f.isOpenMap _ hΩ
  have h2 := (quasiMeasurePreserving_restrict hg).ae
    (ae_differentiableAt_of_lipschitzOnWith hU hg)
  filter_upwards [ae_differentiableAt_of_lipschitzOnWith hΩ hf, h2,
    ae_restrict_mem hΩ.measurableSet] with x h1 h2 hx
  have hcomp : (fderiv ℝ f.symm (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ ℂ := by
    have h := h2.hasFDerivAt.comp x h1.hasFDerivAt
    have hid : (f.symm ∘ f : ℂ → ℂ) = id := funext f.symm_apply_apply
    rw [hid] at h
    exact h.unique (hasFDerivAt_id x)
  have hdet : (fderiv ℝ f.symm (f x)).det * (fderiv ℝ f x).det = 1 := by
    have h := congrArg ContinuousLinearMap.det hcomp
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
      ContinuousLinearMap.coe_id, LinearMap.det_id] at h
    exact (LinearMap.det_comp _ _).symm.trans h
  
  have h1' : 1 ≤ K ^ 2 * |(fderiv ℝ f x).det| := by
    calc _ = |(fderiv ℝ f.symm (f x)).det| * |(fderiv ℝ f x).det| := by
          rw [← abs_mul, hdet, abs_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right (abs_det_fderiv_le hU hg (mem_image_of_mem f hx)) (abs_nonneg _)
  by_cases hK : (K : ℝ) ^ 2 = 0
  · simp [hK]
  · rw [inv_le_iff_one_le_mul₀' ((by positivity))]
    exact h1'

end

/-! ### The `L²` pullback -/

lemma memLp_pullback {p : ENNReal} {g : ℂ → ℂ} {V : Set ℂ} (hmap : MapsTo f Ω V)
    (hg : LipschitzOnWith K f.symm V) (h : MemLp g p (volume.restrict V)) : MemLp (g ∘ f) p (volume.restrict Ω) :=
  (h.of_measure_le_smul (by simp) (map_restrict_le_bilip hmap hg)).comp_of_map f.continuous.aemeasurable

lemma memLp_comp_bilip {p : ENNReal} (hg : LipschitzOnWith K f.symm (f '' Ω)) {g : ℂ → ℂ}
    (h : MemLp g p (volume.restrict (f '' Ω))) : MemLp (g ∘ f) p (volume.restrict Ω) :=
  memLp_pullback (mapsTo_image ..) hg h

section

variable (hΩ : IsOpen Ω) (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm (f '' Ω))
    (v : L2 (f '' Ω))
include hf hg

/-- The pullback `L²(f(Ω)) ≃ L²(Ω)`, `v ↦ v ∘ f`, along a bi-Lipschitz homeomorphism. -/
def bilipPull : L2 (f '' Ω) ≃ₗ[ℂ] L2 Ω  := by
  let pull (v : L2 (f '' Ω)) : L2 Ω := (memLp_comp_bilip hg (Lp.memLp v)).toLp _
  let inv (u : L2 Ω) : L2 (f '' Ω) := (memLp_pullback (f := f.symm) symm_mapsTo_image hf (Lp.memLp u)).toLp _
  have hp (v) : pull v =ᵐ[volume.restrict Ω] (v : ℂ → ℂ) ∘ f := MemLp.coeFn_toLp _
  have hi (u) : inv u =ᵐ[volume.restrict (f '' Ω)] (u : ℂ → ℂ) ∘ f.symm := MemLp.coeFn_toLp _
  refine { toFun := pull, invFun := inv, left_inv := ?_, right_inv := ?_, map_add' := ?_, map_smul' := ?_ }
  · intro v w; apply Lp.ext
    filter_upwards [hp (v+w), hp v, hp w, (quasiMeasurePreserving_restrict hg).ae (Lp.coeFn_add v w),
      Lp.coeFn_add (pull v) (pull w)] with z ha hb hc hd he
    simpa [Function.comp_def, Pi.add_apply] using ha.trans (hd.trans ((congrArg₂ (· + ·) hb.symm hc.symm).trans he.symm))
  · intro c v; apply Lp.ext
    filter_upwards [hp (c • v), hp v, (quasiMeasurePreserving_restrict hg).ae (Lp.coeFn_smul c v),
      Lp.coeFn_smul c (pull v)] with z ha hb hd he
    exact ha.trans (hd.trans ((congrArg (c • ·) hb.symm).trans he.symm))
  · intro v; apply Lp.ext
    filter_upwards [hi (pull v), (quasiMeasurePreserving_symm_restrict hf).ae (hp v)] with z hz hz'
    simpa [Function.comp_def] using hz.trans hz'
  · intro v; apply Lp.ext
    filter_upwards [hp (inv v), (quasiMeasurePreserving_restrict hg).ae (hi v)] with z hz hz'
    simpa [Function.comp_def] using hz.trans hz'


lemma bilipPull_ae :
    (bilipPull hf hg v : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => (v : ℂ → ℂ) (f x) :=
  (memLp_comp_bilip hg (Lp.memLp v)).coeFn_toLp

include hΩ in
/-- The pullback carries the `L²(f(Ω))` inner product to the weighted inner product
`∫_Ω |det Df| ⟨·, ·⟩`. -/
lemma inner_eq_integral_bilipPull (w : L2 (f '' Ω)) :
    inner ℂ v w = ∫ x in Ω, ((|(fderiv ℝ f x).det| : ℝ) : ℂ) *
      inner ℂ ((bilipPull hf hg v : ℂ → ℂ) x) ((bilipPull hf hg w : ℂ → ℂ) x) := by
  rw [L2.inner_def, integral_image_bilip hΩ hf (fun y => inner ℂ (v y) (w y))]
  refine integral_congr_ae ?_
  filter_upwards [bilipPull_ae hf hg v, bilipPull_ae hf hg w] with x h1 h2
  simp [*]

end

end PolyaNeumann

end
