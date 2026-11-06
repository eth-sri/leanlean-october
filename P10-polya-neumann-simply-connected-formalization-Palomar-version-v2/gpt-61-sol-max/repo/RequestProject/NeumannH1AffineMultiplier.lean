module

public import RequestProject.WeakProductRule

public import RequestProject.L2Pairing

public import RequestProject.PlanarTypes

public import RequestProject.NeumannSobolev
public import RequestProject.LpBoundedMultiplier
public import RequestProject.ReconBasic

/-!
# Affine multiplication in the actual weak-gradient H¹ space

Multiplication by `z-p` is constructed from the genuine L² multiplier and
the weak product rule. Testing against `(z-p)φ` proves gradient membership
for arbitrary H¹ inputs. A supplied physical bound gives an explicit H¹
operator norm; boundedness of the domain supplies such a bound at every p.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter

section
variable {Ω : PlanarSet} (p ) {B } (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B)

include Ω p B hB in
/-- A pointwise affine bound gives an essential bound on the actual restricted
measure. Restriction monotonicity avoids a measurability assumption on Ω. -/
theorem neumannAffine_ae_bound :
    ∀ᵐ z ∂volume.restrict Ω, ‖z - p‖ ≤ B := by
  have hsub : Ω ⊆ closedBall p B := by
    intro z hz
    simpa  [dist_eq_norm] using hB z hz
  apply ae_restrict_of_ae_restrict_of_subset hsub
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  simpa  [dist_eq_norm] using hz

/-- The actual affine coefficient multiplier in physical L². -/
def neumannAffineL2Multiplier {Ω : PlanarSet} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (fun z : ℂ => z - p)
    (continuous_id.sub continuous_const).aestronglyMeasurable
    (neumannAffine_ae_bound p hB)

section
include Ω p B hB

theorem neumannAffineL2Multiplier_ae u :
    (neumannAffineL2Multiplier p hB u : PlaneMap) =ᵐ[volume.restrict Ω]
      fun z => (z - p) * u z :=
  lpBoundedMultiplier_ae (fun z : ℂ => z - p)
    (continuous_id.sub continuous_const).aestronglyMeasurable
    (neumannAffine_ae_bound p hB) u

theorem norm_neumannAffineL2Multiplier_apply_le u :
    ‖neumannAffineL2Multiplier p hB u‖ ≤ B * ‖u‖ :=
  norm_lpBoundedMulLin_le (fun z : ℂ => z - p)
    (continuous_id.sub continuous_const).aestronglyMeasurable
    (neumannAffine_ae_bound p hB) u

end


include Ω p B hB in
/-- The affine weak product rule follows from the original weak-gradient
identity tested against the actual compactly supported affine product. -/
theorem isWeakGradient_neumannAffineL2Multiplier  
    (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (neumannAffineL2Multiplier p hB u)
      (fun i => neumannAffineL2Multiplier p hB (g i) + coordDir i • u) := by
  refine isWeakGradient_l2Multiplier (fun z => z - p)
    (contDiff_id.sub contDiff_const) (neumannAffineL2Multiplier p hB)
    (fun i => coordDir i • ContinuousLinearMap.id ℂ (L2 Ω))
    (neumannAffineL2Multiplier_ae p hB) ?_ hu
  intro i v
  filter_upwards [Lp.coeFn_smul (coordDir i) v] with z hz
  change (coordDir i • v : L2 Ω) z = _
  rw [hz, fderiv_sub_const]
  simp

def affineH1Vector {Ω : PlanarSet} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_neumannAffineL2Multiplier p hB (h1Value_weakGradient Ω u))

section
include Ω p B hB

private theorem affineH1Vector_value u :
    h1Value Ω (affineH1Vector p hB u) = neumannAffineL2Multiplier p hB (h1Value Ω u) :=
  h1Value_h1Vector
    (isWeakGradient_neumannAffineL2Multiplier p hB (h1Value_weakGradient Ω u))

private theorem affineH1Vector_gradient u i :
    h1Gradient Ω i (affineH1Vector p hB u) =
      neumannAffineL2Multiplier p hB (h1Gradient Ω i u) + coordDir i • h1Value Ω u :=
  h1Gradient_h1Vector
    (isWeakGradient_neumannAffineL2Multiplier p hB (h1Value_weakGradient Ω u)) i

end


def affineH1Lin {Ω } p {B }
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : NeumannH1 Ω →ₗ[ℂ] NeumannH1 Ω where
  toFun := affineH1Vector p hB
  map_add' u v := by
    apply h1_ext
    · simp  [affineH1Vector_value]
    · intro i
      simp  [affineH1Vector_gradient]
      abel
  map_smul' c u := by
    apply h1_ext
    · simp  [affineH1Vector_value]
    · intro i
      simp  [affineH1Vector_gradient]
      rw [smul_comm]



end


private theorem affine_real_value_norm_bound {a v N B : ℝ}
    (hB : 0 ≤ B) (hN : 0 ≤ N) (ha : a ≤ B * v) (hv : v ≤ N) :
    a ≤ (B + 1) * N := by
  nlinarith

private theorem affine_gradient_norm_bound {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : V →L[ℂ] V) a v (q : ℂ) 
    (hB : 0 ≤ B) (hL : ‖L a‖ ≤ B * ‖a‖)
    (ha : ‖a‖ ≤ N) (hv : ‖v‖ ≤ N) (hq : ‖q‖ = 1) :
    ‖L a + q • v‖ ≤ (B + 1) * N := by
  calc
    _ ≤ ‖L a‖ + ‖q • v‖ := norm_add_le _ _
    _ = ‖L a‖ + ‖v‖ := by rw [norm_smul, hq, one_mul]
    _ ≤ B * ‖a‖ + ‖v‖ := add_le_add hL le_rfl
    _ ≤ B * N + N := add_le_add (mul_le_mul_of_nonneg_left ha hB) hv
    _ = (B + 1) * N := by ring

section
variable {Ω } (p ) {B } (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω)

include Ω p B hB0 hB u in
theorem affineH1Lin_norm_le :
    ‖affineH1Lin p hB u‖ ≤ (Real.sqrt 3 * (B + 1)) * ‖u‖ := by
  have hv : ‖h1Value Ω (affineH1Lin p hB u)‖ ≤ (B + 1) * ‖u‖ := by
    exact affine_real_value_norm_bound hB0 (norm_nonneg u)
      (norm_neumannAffineL2Multiplier_apply_le p hB (h1Value Ω u))
      (h1Value_norm_le u)
  have hg (i : Coord) : ‖h1Gradient Ω i (affineH1Lin p hB u)‖ ≤ (B + 1) * ‖u‖ := by
    exact affine_gradient_norm_bound (V := L2 Ω) (neumannAffineL2Multiplier p hB)
      (h1Gradient Ω i u) (h1Value Ω u) (coordDir i) hB0
      (norm_neumannAffineL2Multiplier_apply_le p hB (h1Gradient Ω i u))
      (h1Gradient_norm_le u i) (h1Value_norm_le u) (norm_coordDir i)
  have h := h1_norm_le_of_components (affineH1Lin p hB u)
    hv hg
  simpa only [mul_assoc] using h

/-- Affine multiplication in genuine H¹ from a specified physical bound. -/
def neumannH1AffineMultiplierOfBound {Ω : PlanarSet} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : ComplexEnd (NeumannH1 Ω) := (affineH1Lin p hB).mkContinuous (Real.sqrt 3 * (B + 1))
    (affineH1Lin_norm_le p hB0 hB)

section
include Ω p B hB0 hB u

theorem h1Value_neumannH1AffineMultiplierOfBound :
    h1Value Ω (neumannH1AffineMultiplierOfBound p hB0 hB u) =
      neumannAffineL2Multiplier p hB (h1Value Ω u) := rfl

theorem h1Gradient_neumannH1AffineMultiplierOfBound i :
    h1Gradient Ω i (neumannH1AffineMultiplierOfBound p hB0 hB u) =
      neumannAffineL2Multiplier p hB (h1Gradient Ω i u) + coordDir i • h1Value Ω u := rfl

end


end


section
variable {Ω : PlanarSet} (hb : Bornology.IsBounded Ω) (p : ℂ)

include Ω hb p in
/-- Every bounded actual domain has a genuine affine coefficient bound. -/
theorem exists_neumannAffine_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ Ω, ‖z - p‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := hb.subset_ball_lt 0 p
  refine ⟨B, hB0.le, fun z hz => ?_⟩
  have h : ‖z - p‖ < B := by
    simpa  [dist_eq_norm] using hB hz
  exact h.le

def neumannH1AffineBound {Ω : PlanarSet} (hb : Bornology.IsBounded Ω) (p : ℂ) : ℝ :=
  Classical.choose (exists_neumannAffine_bound hb p)

section
include Ω hb p

theorem neumannH1AffineBound_nonneg :
    0 ≤ neumannH1AffineBound hb p := (Classical.choose_spec (exists_neumannAffine_bound hb p)).1

theorem neumannH1AffineBound_spec :
    ∀ z ∈ Ω, ‖z - p‖ ≤ neumannH1AffineBound hb p :=
  (Classical.choose_spec (exists_neumannAffine_bound hb p)).2

end


end


/-- Multiplication by `z-p` on the actual H¹ space of any bounded domain. -/
def neumannH1AffineMultiplier {Ω : PlanarSet} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    ComplexEnd (NeumannH1 Ω) :=
  neumannH1AffineMultiplierOfBound p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p)

section
variable {Ω } (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω)
include Ω hb p u

theorem h1Value_neumannH1AffineMultiplier :
    h1Value Ω (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Value Ω u) :=
  h1Value_neumannH1AffineMultiplierOfBound p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p) u

theorem h1Gradient_neumannH1AffineMultiplier i :
    h1Gradient Ω i (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω i u) +
        coordDir i • h1Value Ω u :=
  h1Gradient_neumannH1AffineMultiplierOfBound p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p) u i

theorem h1Gradient_neumannH1AffineMultiplier_x :
    h1Gradient Ω 0 (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω 0 u) +
        h1Value Ω u := by
  simp_all [coordDir, h1Gradient_neumannH1AffineMultiplier]

theorem h1Gradient_neumannH1AffineMultiplier_y :
    h1Gradient Ω 1 (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω 1 u) +
        Complex.I • h1Value Ω u := rfl

end


end PolyaNeumann
