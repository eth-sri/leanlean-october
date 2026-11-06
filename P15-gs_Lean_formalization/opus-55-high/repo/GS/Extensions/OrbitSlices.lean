module

public import GS.OverlapGeometry.SliceAtlas

@[expose] public section


/-!
# Smooth slices from a parametrization and ambient inverse

The constructor keeps the model spaces abstract. Applications supply the
relative openness and smooth inverse data before assembling an orbit atlas.
-/

noncomputable section

namespace GS.Extensions

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set F}

def smoothSliceOfParametrization (p : E → S) (c : F → E) (U : Set E)
    (hp : ContDiff ℝ ⊤ (fun x => (p x).val))
    (hU : IsOpen U) (himage : IsOpen (p '' U))
    (hc : ∀ x ∈ U, ContDiffAt ℝ ⊤ c (p x).val)
    (hi : ∀ x ∈ U, c (p x).val = x) :
    GS.OverlapGeometry.SmoothSlice (E := E) S where
  source := p '' U
  target := U
  coordinates := c
  parametrization := p
  open_source := himage
  open_target := hU
  coordinates_smooth := by
    grind
  parametrization_smooth := hp
  maps_source := by
    grind
  maps_target := by grind
  left_inverse := by
    grind
  right_inverse := hi

def translateSmoothSlice (s : GS.OverlapGeometry.SmoothSlice (E := E) S)
    (f g : F → F) (T U : S → S)
    (hT : ∀ x, (T x).val = f x.val) (hU : ∀ x, (U x).val = g x.val)
    (hTU : ∀ x, T (U x) = x) (hUT : ∀ x, U (T x) = x)
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (hUc : Continuous U) :
    GS.OverlapGeometry.SmoothSlice (E := E) S where
  source := U ⁻¹' s.source
  target := s.target
  coordinates := fun A => s.coordinates (g A)
  parametrization := fun h => T (s.parametrization h)
  open_source := s.open_source.preimage hUc
  open_target := s.open_target
  coordinates_smooth X hX := by
    have hc := s.coordinates_smooth (U X) hX
    rw [hU] at hc
    fun_prop
  parametrization_smooth := by
    simpa only [hT, Function.comp_def] using hf.comp s.parametrization_smooth
  maps_source X hX := by simpa only [hU] using s.maps_source (U X) hX
  maps_target h hh := by simp [hUT, s.maps_target h hh]
  left_inverse X hX := by grind [s.left_inverse (U X) hX]
  right_inverse h hh := by simp [← hU, hUT, s.right_inverse h hh]

end GS.Extensions
