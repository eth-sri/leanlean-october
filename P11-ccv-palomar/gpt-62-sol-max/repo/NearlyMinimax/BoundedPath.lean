module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace NearlyMinimax

/-- A parametrized integrand with a common bound on the parameter set. -/
structure BoundedPath {X : Type*} [MeasurableSpace X] (s : Set ℝ) (f : ℝ → X → ℝ) (M : ℝ) : Prop where
  measurable : ∀ t, Measurable (f t)
  nonneg : 0 ≤ M
  norm_le : ∀ t ∈ s, ∀ x, ‖f t x‖ ≤ M

namespace BoundedPath
variable {X : Type*} [MeasurableSpace X] {s : Set ℝ} {f g f' : ℝ → X → ℝ} {A B : ℝ}

protected theorem of_abs (hm : ∀ t, Measurable (f t)) (hA : 0 ≤ A)
    (h : ∀ t ∈ s, ∀ x, |f t x| ≤ A) : BoundedPath s f A :=
  ⟨hm, hA, by simpa only [Real.norm_eq_abs]⟩

protected theorem const {f : X → ℝ} (hm : Measurable f) (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A) : BoundedPath s (fun _ => f) A :=
  .of_abs (fun _ => hm) hA (fun _ _ => hf)

section
variable (hf : BoundedPath s f A)
include hf

protected theorem mul (hg : BoundedPath s g B) :
    BoundedPath s (fun t x => f t x * g t x) (A * B) :=
  ⟨fun t => (hf.measurable t).mul (hg.measurable t), mul_nonneg hf.nonneg hg.nonneg,
    fun t ht x => (norm_mul _ _).le.trans (mul_le_mul (hf.norm_le t ht x)
      (hg.norm_le t ht x) (norm_nonneg _) hf.nonneg)⟩

protected theorem add (hg : BoundedPath s g B) :
    BoundedPath s (fun t x => f t x + g t x) (A + B) :=
  ⟨fun t => (hf.measurable t).add (hg.measurable t), add_nonneg hf.nonneg hg.nonneg,
    fun t ht x => (norm_add_le _ _).trans (add_le_add (hf.norm_le t ht x) (hg.norm_le t ht x))⟩

protected theorem mono {s' : Set ℝ} (h : s' ⊆ s) : BoundedPath s' f A :=
  ⟨hf.measurable, hf.nonneg, fun t ht => hf.norm_le t (h ht)⟩

end

section
variable {Y : Type*} [MeasurableSpace Y]

protected theorem comp (hf : BoundedPath s f A)
    {g : Y → X} (hg : Measurable g) : BoundedPath s (fun t x => f t (g x)) A :=
  ⟨fun t => (hf.measurable t).comp hg, hf.nonneg, fun t ht x => hf.norm_le t ht (g x)⟩

protected theorem marginal {ν : ℝ → Measure X}
    {F : ℝ → X × Y → ℝ} (hF : BoundedPath s F A) (hs : ∀ t, SFinite (ν t))
    (hprob : ∀ t ∈ s, IsProbabilityMeasure (ν t)) :
    BoundedPath s (fun t y => ∫ x, F t (x,y) ∂ν t) A := by
  refine ⟨fun t => ?_, hF.nonneg, fun t ht y => ?_⟩
  · let _ := hs t
    exact (hF.measurable t).stronglyMeasurable.integral_prod_left'.measurable
  · let _ := hprob t ht
    simpa using (norm_integral_le_of_norm_le_const (μ := ν t)
      (Eventually.of_forall fun x => hF.norm_le t ht (x,y)))

end

variable {μ : Measure X} [IsFiniteMeasure μ]

section
variable (hf : BoundedPath s f A)
include hf

protected theorem integrable {t : ℝ} (ht : t ∈ s) : Integrable (f t) μ :=
  Integrable.of_bound (hf.measurable t).aestronglyMeasurable A (Eventually.of_forall (hf.norm_le t ht))

protected theorem hasDerivAt_integral (hf' : BoundedPath s f' B)
    {t : ℝ} (ht : s ∈ 𝓝 t) (hd : ∀ u ∈ s, ∀ x, HasDerivAt (f · x) (f' u x) u) :
    HasDerivAt (fun u => ∫ x, f u x ∂μ) (∫ x, f' t x ∂μ) t :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le ht
    (Eventually.of_forall fun u => (hf.measurable u).aestronglyMeasurable)
    (hf.integrable (mem_of_mem_nhds ht)) (hf'.measurable t).aestronglyMeasurable
    (Eventually.of_forall fun x u hu => hf'.norm_le u hu x) (integrable_const B)
    (Eventually.of_forall fun x u hu => hd u hu x)).2

end

protected theorem lipschitzOnWith (hf' : BoundedPath s f' B) (hs : Convex ℝ s)
    (hd : ∀ t ∈ s, ∀ x, HasDerivAt (f · x) (f' t x) t) (x : X) :
    LipschitzOnWith ⟨B, hf'.nonneg⟩ (f · x) s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hd t ht x).hasDerivWithinAt) (fun t ht => NNReal.coe_le_coe.mp (hf'.norm_le t ht x))

protected theorem lipschitzIntegral (hf : BoundedPath s f A) {K : NNReal}
    (hl : ∀ x, LipschitzOnWith K (f · x) s) :
    LipschitzOnWith ⟨(K : ℝ) * μ.real univ, by positivity⟩ (fun u => ∫ x, f u x ∂μ) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [dist_eq_norm, ← integral_sub (hf.integrable hu) (hf.integrable hv)]
  have hb : ∀ᵐ x ∂μ, ‖f u x - f v x‖ ≤ (K : ℝ) * dist u v :=
    Eventually.of_forall fun x => by simpa only [dist_eq_norm] using (hl x).dist_le_mul u hu v hv
  exact (norm_integral_le_of_norm_le_const hb).trans_eq (by change _ = ((K : ℝ) * μ.real univ) * dist u v; ring)

protected theorem lipschitzIntegral_prob {ν : Measure X} [IsProbabilityMeasure ν]
    (hf : BoundedPath s f A) {K : NNReal} (hl : ∀ x, LipschitzOnWith K (f · x) s) :
    LipschitzOnWith K (fun u => ∫ x, f u x ∂ν) s := by
  have h := hf.lipschitzIntegral (μ := ν) hl
  have hk : (⟨(K : ℝ) * ν.real univ, by positivity⟩ : NNReal) = K :=
    Subtype.ext (by change (K : ℝ) * ν.real univ = K; simp)
  rwa [hk] at h

protected theorem lipschitzMul (hf : BoundedPath s f A) (hg : BoundedPath s g B) {K L : NNReal}
    (hl : ∀ x, LipschitzOnWith K (f · x) s) (hl' : ∀ x, LipschitzOnWith L (g · x) s) (x : X) :
    LipschitzOnWith ⟨(K : ℝ) * B + A * (L : ℝ), by have := hf.nonneg; have := hg.nonneg; positivity⟩
      (fun t => f t x * g t x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [dist_eq_norm, show f u x * g u x - f v x * g v x =
    (f u x - f v x) * g u x + f v x * (g u x - g v x) by ring]
  have h1 : ‖f u x - f v x‖ ≤ K * dist u v := by simpa only [dist_eq_norm] using (hl x).dist_le_mul u hu v hv
  have h2 : ‖g u x - g v x‖ ≤ L * dist u v := by simpa only [dist_eq_norm] using (hl' x).dist_le_mul u hu v hv
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul]
  exact (add_le_add (mul_le_mul h1 (hg.norm_le u hu x) (norm_nonneg _) (by positivity))
    (mul_le_mul (hf.norm_le v hv x) h2 (norm_nonneg _) hf.nonneg)).trans_eq (by change _ = ((K : ℝ) * B + A * (L : ℝ)) * dist u v; ring)

end BoundedPath
end NearlyMinimax
