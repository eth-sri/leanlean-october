module
public import Glennie.BasicLaws
public import Glennie.Compact.Sections

@[expose] public section
namespace Glennie.Compact.OperationalPhi
open Glennie
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The swapped-order contrast, with an arbitrary unnormalized final argument. -/
def contrast (x y z v : Albert) : ℝ :=
  inner z (U y (U x (U z v)) - U x (U y (U z v)))

/-- The amplitude h=(1+x)/2, expressed with real scalar multiplication. -/
def halfAmplitude (x : Albert) : Albert := (1 / 2 : ℝ) • ((1 : Albert) + x)

/-- The history difference Delta_a with arbitrary input rho. -/
def delta (x y z a rho : Albert) : ℝ := contrast x y z (U a rho)

theorem jordan_pairing_selfadjoint (x a b : Albert) :
    inner a (jordan x b) = inner (jordan x a) b := by
  rw [← inner_jordan_associative, jordan_comm a x]

/-- Self-adjointness is derived from the native associative pairing. -/
theorem U_pairing_selfadjoint (x a b : Albert) :
    inner a (U x b) = inner (U x a) b := by
  simp only [U, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, jordan_pairing_selfadjoint]

theorem contrast_sub (x y z u v : Albert) :
    contrast x y z (u - v) = contrast x y z u - contrast x y z v := by
  simp only [contrast, U_sub_argument, inner_sub_right]; ring

theorem contrast_smul (x y z v : Albert) (r : ℝ) :
    contrast x y z (r • v) = r * contrast x y z v := by
  simp only [contrast, U_smul_argument, inner_sub_right, inner_smul_right]; ring

/-- Reversing the commutator across the pairing fixes the contrast sign. -/
theorem phi_eq_contrast (x y z : Albert) :
    phi x y z = contrast x y z (jordan x y) := by
  simp only [phi, contrast, inner_sub_left, inner_sub_right,
    ← U_pairing_selfadjoint]

theorem U_one (w : Albert) : U (1 : Albert) w = w := by
  simp only [U, jordan_unit_left]; module

theorem crossU_one (x w : Albert) : crossU (1 : Albert) x w = (2 : ℝ) • jordan x w := by
  simp only [crossU, jordan_unit_left]; module

/-- The required 4U_h-U_x-U_1=2L_x identity, with no spectral hypotheses. -/
theorem four_U_halfAmplitude (x w : Albert) :
    (4 : ℝ) • U (halfAmplitude x) w - U x w - U (1 : Albert) w =
      (2 : ℝ) • jordan x w := by
  rw [halfAmplitude, U_smul_base, U_add_base, U_one, crossU_one]; module

/-- Division-free six-term identity with the original y as input. -/
theorem phi_division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y - delta x y z 1 y =
      2 * phi x y z := by
  have h := congrArg (contrast x y z) (four_U_halfAmplitude x y)
  simp only [contrast_sub, contrast_smul, ← phi_eq_contrast] at h
  exact h

end
end Glennie.Compact.OperationalPhi

namespace Glennie.Compact.LocalContrast
open Glennie Glennie.Compact.Affine20 Glennie.Compact.Sections Glennie.Compact.OperationalPhi
noncomputable section

def score (T : Triple) : ℝ :=
  let x := encoder (T 0)
  let y := encoder (T 1)
  let z := encoder (T 2)
  4 * delta x y z (halfAmplitude x) y - delta x y z x y - delta x y z 1 y

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T :=
  phi_division_free (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

end
end Glennie.Compact.LocalContrast
