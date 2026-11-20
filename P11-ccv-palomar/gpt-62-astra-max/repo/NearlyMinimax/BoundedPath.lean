module

public import Mathlib

@[expose] public section
/-! Uniform bounds, differentiation and integration for real observable paths. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace NearlyMinimax

variable {X : Type*} [MeasurableSpace X] {s : Set ℝ} {B C D E : ℝ}
  {f g f' g' : ℝ → X → ℝ} {t : ℝ}

/-- A uniformly bounded family of measurable observables on a time set. -/
structure BoundedFamily (s : Set ℝ) (f : ℝ → X → ℝ) (B : ℝ) : Prop where
  measurable : ∀ u, Measurable (f u)
  bound : ∀ u ∈ s, ∀ x, |f u x| ≤ B

namespace BoundedFamily

theorem add (hf : BoundedFamily s f B) (hg : BoundedFamily s g C) :
    BoundedFamily s (fun u x => f u x + g u x) (B + C) :=
  ⟨fun u => (hf.measurable u).add (hg.measurable u), fun u h x =>
    (abs_add_le ..).trans (add_le_add (hf.bound u h x) (hg.bound u h x))⟩

theorem mul (hf : BoundedFamily s f B) (hg : BoundedFamily s g C) :
    BoundedFamily s (fun u x => f u x * g u x) (B * C) := by
  refine ⟨fun u => (hf.measurable u).mul (hg.measurable u), fun u h x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf.bound u h x) (hg.bound u h x) (abs_nonneg _) ((abs_nonneg _).trans (hf.bound u h x))

theorem constFamily {w : X → ℝ} (hm : Measurable w) (hb : ∀ x, |w x| ≤ B) :
    BoundedFamily s (fun _ => w) B := ⟨fun _ => hm, fun _ _ => hb⟩

section
variable (hf : BoundedFamily s f B) (μ : Measure X)
include hf

theorem integrable [IsFiniteMeasure μ] (ht : t ∈ s) :
    Integrable (f t) μ :=
  Integrable.of_bound (hf.measurable t).aestronglyMeasurable B (Eventually.of_forall (hf.bound t ht))

/-- The pointwise product estimate for two bounded Lipschitz families. -/
theorem lipschitz_mul (hg : BoundedFamily s g C) {K L : NNReal}
    (hK : ∀ x, LipschitzOnWith K (fun u => f u x) s) (hL : ∀ x, LipschitzOnWith L (fun u => g u x) s)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (x : X) : LipschitzOnWith ⟨K * C + B * L, by positivity⟩
      (fun u => f u x * g u x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  calc
    _ ≤ dist (f u x * g u x) (f v x * g u x) + dist (f v x * g u x) (f v x * g v x) := dist_triangle ..
    _ = _ := by
      simp [Real.dist_eq, ← sub_mul, ← mul_sub, abs_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul ((hK x).dist_le_mul _ hu _ hv) (hg.bound u hu x) (abs_nonneg _) (by positivity))
      (mul_le_mul (hf.bound v hv x) ((hL x).dist_le_mul _ hu _ hv) dist_nonneg hB)
    _ = _ := by change _ = (K * C + B * L) * dist u v; ring

/-- Integrating a uniformly Lipschitz family costs only the total mass. -/
theorem integral_lipschitz [IsFiniteMeasure μ]
    {K : NNReal} (hk : ∀ x, LipschitzOnWith K (fun u => f u x) s) :
    LipschitzOnWith (K * (μ univ).toNNReal) (fun u => ∫ x, f u x ∂μ) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [dist_eq_norm, ← integral_sub (hf.integrable μ hu) (hf.integrable μ hv)]
  calc
    _ ≤ _ := norm_integral_le_of_norm_le_const
      (Eventually.of_forall fun x => (hk x).dist_le_mul u hu v hv)
    _ = _ := by change _ = (K * μ.real univ) * _; ring

end

end BoundedFamily

/-- A bounded path with a bounded, pointwise time derivative. -/
structure BoundedPath (s : Set ℝ) (f f' : ℝ → X → ℝ) (B D : ℝ) : Prop where
  family : BoundedFamily s f B
  velocity : BoundedFamily s f' D
  deriv : ∀ x u, u ∈ s → HasDerivAt (fun t => f t x) (f' u x) u

namespace BoundedPath

variable (hf : BoundedPath s f f' B D)
include hf

theorem weight {w : X → ℝ} (hm : Measurable w) (hb : ∀ x, |w x| ≤ C) :
    BoundedPath s (fun u x => w x * f u x) (fun u x => w x * f' u x) (C * B) (C * D) :=
  ⟨(BoundedFamily.constFamily hm hb).mul hf.family, (BoundedFamily.constFamily hm hb).mul hf.velocity,
   fun x u h => (hf.deriv x u h).const_mul _⟩

theorem mul (hg : BoundedPath s g g' C E) :
    BoundedPath s (fun u x => f u x * g u x) (fun u x => f' u x * g u x + f u x * g' u x)
      (B * C) (D * C + B * E) :=
  ⟨hf.family.mul hg.family, (hf.velocity.mul hg.family).add (hf.family.mul hg.velocity),
    fun x u h => (hf.deriv x u h).mul (hg.deriv x u h)⟩

theorem integral_deriv (μ : Measure X) [IsFiniteMeasure μ]
    (hs : s ∈ 𝓝 t) : Integrable (f' t) μ ∧
      HasDerivAt (fun u => ∫ x, f u x ∂μ) (∫ x, f' t x ∂μ) t :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun u => (hf.family.measurable u).aestronglyMeasurable)
    (hf.family.integrable μ (mem_of_mem_nhds hs)) (hf.velocity.measurable t).aestronglyMeasurable
    (Eventually.of_forall fun x u hu => hf.velocity.bound u hu x) (integrable_const D)
    (Eventually.of_forall hf.deriv)

theorem lipschitz (hs : Convex ℝ s) (hD : 0 ≤ D) (x : X) :
    LipschitzOnWith ⟨D, hD⟩ (fun u => f u x) s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun u h => (hf.deriv x u h).hasDerivWithinAt)
    (fun u h => hf.velocity.bound u h x)

end BoundedPath
end NearlyMinimax
