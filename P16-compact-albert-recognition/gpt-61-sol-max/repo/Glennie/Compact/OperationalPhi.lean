module
public import Glennie.LinearSimp

public import Glennie.BasicLaws
public import Glennie.Compact.ObservationScript

/- Pure native algebra only. No positivity,
probability interpretation, normalization of effects, or operational framework
is asserted. All products and pairings are the existing Glennie definitions.
-/
@[expose] public section
namespace Glennie.Compact.OperationalPhi
open Glennie
section
export Glennie.SubmissionR03 (contrast halfAmplitude delta)

theorem jordan_pairing_selfadjoint (x a b : Albert) :
    inner a (jordan x b) = inner (jordan x a) b := by
  rw [← inner_jordan_associative, jordan_comm a x]

theorem U_pairing_selfadjoint (x a b : Albert) :
    inner a (U x b) = inner (U x a) b := by
  simp only [albert_linear, U, jordan_pairing_selfadjoint]

theorem contrast_sub (x y z u v : Albert) :
    contrast x y z (u - v) = contrast x y z u - contrast x y z v := by
  simp only [contrast, U_sub_argument, inner_sub_right]
  ring

theorem contrast_smul (x y z v : Albert) (r : ℝ) :
    contrast x y z (r • v) = r * contrast x y z v := by
  simp only [contrast, U_smul_argument, inner_sub_right, inner_smul_right]
  ring

theorem phi_eq_contrast (x y z : Albert) :
    phi x y z = contrast x y z (jordan x y) := by
  simp only [phi, contrast, inner_sub_left, inner_sub_right,
    ← U_pairing_selfadjoint]

theorem U_one (w : Albert) : U (1 : Albert) w = w := by
  simp only [U, jordan_unit_left]
  module

theorem crossU_one (x w : Albert) : crossU (1 : Albert) x w = (2 : ℝ) • jordan x w := by
  simp only [crossU, jordan_unit_left]
  module

theorem four_U_halfAmplitude (x w : Albert) :
    (4 : ℝ) • U (halfAmplitude x) w - U x w - U (1 : Albert) w =
      (2 : ℝ) • jordan x w := by
  rw [halfAmplitude, U_smul_base, U_add_base, U_one, crossU_one]
  module

theorem phi_division_free (x y z : Albert) :
    4 * delta x y z (halfAmplitude x) y - delta x y z x y - delta x y z 1 y =
      2 * phi x y z := by
  have h := congrArg (contrast x y z) (four_U_halfAmplitude x y)
  simp only [contrast_sub, contrast_smul, ← phi_eq_contrast] at h
  exact h

end
end Glennie.Compact.OperationalPhi
