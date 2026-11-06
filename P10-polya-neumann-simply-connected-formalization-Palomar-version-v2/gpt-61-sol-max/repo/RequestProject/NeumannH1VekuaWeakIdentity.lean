module

public import RequestProject.PlanarTypes

public import RequestProject.NeumannH1AffineMultiplier
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic.Module

/-!
# Genuine weak Wirtinger identities for the physical Vekua series

All derivatives below are the components of the actual weak-gradient H¹
space. The second-order identity is obtained by testing those weak gradients
twice and commuting derivatives of compact smooth tests. In particular no
weak Laplacian, smoothness of the H¹ input, or boundary condition is assumed.

This module is part of the verified dependency chain.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set

/-- The genuine weak derivative `(∂x - i∂y)/2`. -/
def h1WirtingerD (Ω : PlanarSet) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  (1 / 2 : ℂ) • (h1Gradient Ω 0 - Complex.I • h1Gradient Ω 1)

/-- The genuine weak derivative `(∂x + i∂y)/2`. -/
def h1WirtingerDbar (Ω : PlanarSet) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  (1 / 2 : ℂ) • (h1Gradient Ω 0 + Complex.I • h1Gradient Ω 1)

theorem h1WirtingerD_apply Ω u :
    h1WirtingerD Ω u =
      (1 / 2 : ℂ) • (h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u) := rfl

theorem h1WirtingerDbar_apply Ω u :
    h1WirtingerDbar Ω u =
      (1 / 2 : ℂ) • (h1Gradient Ω 0 u + Complex.I • h1Gradient Ω 1 u) := rfl

theorem h1WirtingerD_eq_zero_of_antiholomorphic  u
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) :
    h1WirtingerD Ω u = 0 := by
  simp_all [h1WirtingerD_apply]

/-- A genuine antiholomorphic primitive has the stated conjugate derivative. -/
theorem h1WirtingerDbar_eq_value_of_components Ω u v
    (hx : h1Gradient Ω 0 u = h1Value Ω v)
    (hy : h1Gradient Ω 1 u = -Complex.I • h1Value Ω v) :
    h1WirtingerDbar Ω u = h1Value Ω v := by
  rw [h1WirtingerDbar_apply, hx, hy]
  simp  [smul_smul]
  module

section
variable {Ω } (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω)
include Ω hb p u

/-- The affine H¹ product rule for the actual first Wirtinger derivative. -/
theorem h1WirtingerD_neumannH1AffineMultiplier :
    h1WirtingerD Ω (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
        (h1WirtingerD Ω u) + h1Value Ω u := by
  rw [h1WirtingerD_apply, h1Gradient_neumannH1AffineMultiplier_x,
    h1Gradient_neumannH1AffineMultiplier_y, h1WirtingerD_apply]
  simp  [smul_smul]
  module

/-- Multiplication by `z-p` commutes with the conjugate Wirtinger derivative. -/
theorem h1WirtingerDbar_neumannH1AffineMultiplier :
    h1WirtingerDbar Ω (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
        (h1WirtingerDbar Ω u) := by
  rw [h1WirtingerDbar_apply, h1Gradient_neumannH1AffineMultiplier_x,
    h1Gradient_neumannH1AffineMultiplier_y, h1WirtingerDbar_apply]
  simp  [smul_smul]
  module

/-- Powers of the actual H¹ multiplier agree with powers of its L² value
multiplier; this is an operator statement on genuine H¹ inputs. -/
theorem h1Value_neumannH1AffineMultiplier_pow (j : ℕ) :
    h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u) =
      (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) ^ j)
        (h1Value Ω u) := by
  induction j with
  | zero => simp  
  | succ j ih =>
    calc
      _ = neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
          (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u)) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply, h1Value_neumannH1AffineMultiplier]
      _ = _ := by rw [ih, pow_succ', ContinuousLinearMap.mul_apply]

theorem h1WirtingerDbar_affine_pow (j : ℕ) :
    h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ j) u) =
      (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) ^ j)
        (h1WirtingerDbar Ω u) := by
  induction j with
  | zero => simp  
  | succ j ih =>
    calc
      _ = neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
          (h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ j) u)) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply,
          h1WirtingerDbar_neumannH1AffineMultiplier]
      _ = _ := by rw [ih, pow_succ', ContinuousLinearMap.mul_apply]

end


private theorem vekua_nat_succ_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    j (x : V) :
    ((j + 1 : ℕ) : ℂ) • x + x = ((j + 1 + 1 : ℕ) : ℂ) • x := by
  module

private theorem vekua_affine_successor {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (L : V →L[ℂ] V) j x y (hL : L x = y) :
    L (((j + 1 : ℕ) : ℂ) • x) + y = ((j + 1 + 1 : ℕ) : ℂ) • y := by
  rw [map_smul, hL]
  exact vekua_nat_succ_smul j y

/-- The true polynomial differentiation rule for an antiholomorphic H¹
input. No regularity of that input beyond H¹ is used. -/
theorem h1WirtingerD_affine_pow_of_antiholomorphic {Ω : PlanarSet}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω)
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) (j : ℕ) :
    h1WirtingerD Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      ((j + 1 : ℕ) : ℂ) • h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u) := by
  have hzero := h1WirtingerD_eq_zero_of_antiholomorphic u hu
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, ContinuousLinearMap.one_apply,
      h1WirtingerD_neumannH1AffineMultiplier, hzero, map_zero, zero_add,
      Nat.cast_one, one_smul]
  | succ j ih =>
    have hval : neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
        (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u)) =
        h1Value Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply, h1Value_neumannH1AffineMultiplier]
    calc
      _ = neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
          (h1WirtingerD Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u)) +
          h1Value Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply,
          h1WirtingerD_neumannH1AffineMultiplier]
      _ = _ := by
        simp_all only [vekua_affine_successor, L2, neumannAffineL2Multiplier, h1Value, neumannH1AffineMultiplier, PolyaNeumann.L2, PolyaNeumann.NeumannH1, PolyaNeumann.neumannH1AffineMultiplier]

end PolyaNeumann
