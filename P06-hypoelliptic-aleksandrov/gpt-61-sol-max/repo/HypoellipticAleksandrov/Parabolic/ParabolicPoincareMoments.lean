module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareFoundation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct
import Lean.Elab.Tactic.Grind
import all HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime
import all HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments

open private HypoellipticAleksandrov.Parabolic.unit_velocity_cube_integral_eval_mul_eval from HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
open private HypoellipticAleksandrov.Parabolic.continuous_integrable_parabolicMorreyUnitBox from HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime
open private HypoellipticAleksandrov.Parabolic.unit_velocity_cube_integral_eval from HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
open private HypoellipticAleksandrov.Parabolic.unit_velocity_cube_measure from HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
open private HypoellipticAleksandrov.Parabolic.unit_interval_integral_sq from HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
open private HypoellipticAleksandrov.Parabolic.unit_interval_integral_id from HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments


/-!
# Unit-box parabolic moment projection

This module computes the first two velocity moments of the literal open
parabolic Morrey unit box and records the resulting algebra of its normalized
velocity-affine moment projection. Endpoint and product-factorization
calculations remain private.
-/

 public section


namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory
open scoped BigOperators













variable {d : ℕ}

variable (i : Fin d)




private theorem box_int_eval   :
    ∫ z in parabolicMorreyUnitBox d, z.2 i = 0 := by
  rw [_root_.HypoellipticAleksandrov.Parabolic.parabolicMorreyUnitBox_restrict_volume_eq_prod]
  change ∫ z, z.2 i ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (volume.restrict (velocityCube (0 : PDE.Vec d) 1))) = 0
  simpa using (integral_fun_snd (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
    (ν := volume.restrict (velocityCube (0 : PDE.Vec d) 1))
    (fun v  => v i)).trans (by rw [_root_.HypoellipticAleksandrov.Parabolic.unit_velocity_cube_integral_eval i]; simp)

variable (i j : Fin d)




private theorem box_int_eval_mul_eval   :
    ∫ z in parabolicMorreyUnitBox d, z.2 i * z.2 j =
      if i = j then (2 : ℝ) ^ d / 3 else 0 := by
  rw [_root_.HypoellipticAleksandrov.Parabolic.parabolicMorreyUnitBox_restrict_volume_eq_prod]
  change ∫ z, z.2 i * z.2 j ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (volume.restrict (velocityCube (0 : PDE.Vec d) 1))) = _
  calc
    _ = (∫ _ in Set.Ioo (0 : ℝ) 1, (1 : ℝ)) *
        ∫ v in velocityCube (0 : PDE.Vec d) 1, v i * v j := by
      simpa using integral_prod_mul (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
        (ν := volume.restrict (velocityCube (0 : PDE.Vec d) 1)) (fun _  => (1 : ℝ))
        (fun v  => v i * v j)
    _ = _ := by simp [_root_.HypoellipticAleksandrov.Parabolic.unit_velocity_cube_integral_eval_mul_eval]

/-- The unit-box average of the constant function one is one. -/
theorem parabolicMorreyUnitAverage_one (d : ℕ) :
    parabolicMorreyUnitAverage (fun _ : TimeVelocity d => (1 )) = 1 := by
  rw [parabolicMorreyUnitAverage, MeasureTheory.integral_const,
    Measure.real, Measure.restrict_apply_univ,
    volume_parabolicMorreyUnitBox_toReal]
  simp only [smul_eq_mul]
  field_simp

variable {d : ℕ}

/-- Every velocity coordinate has zero average on the symmetric unit box. -/
theorem parabolicMorreyUnitAverage_velocity  (i : Fin d) :
    parabolicMorreyUnitAverage (fun z  => z.2 i) = 0 := by
  rw [parabolicMorreyUnitAverage, box_int_eval]
  ring

/-- The unit-box velocity-coordinate moment matrix is diagonal with diagonal
entry `1 / 3`. -/
theorem parabolicMorreyUnitAverage_velocity_mul_velocity  (i j : Fin d) :
    parabolicMorreyUnitAverage (fun z  => z.2 i * z.2 j) =
      if i = j then (1 / 3 : ℝ) else 0 := by
  rw [parabolicMorreyUnitAverage, box_int_eval_mul_eval,
    volume_parabolicMorreyUnitBox_toReal]
  by_cases hij : i = j
  · simp [hij]
    field_simp
  · simp [hij]

/-- The unit-box average is additive on genuinely integrable inputs. -/
theorem parabolicMorreyUnitAverage_add  (f g : TimeVelocity d → ℝ)
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d)))
    (hg : Integrable g (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitAverage (f + g) =
      parabolicMorreyUnitAverage f + parabolicMorreyUnitAverage g := by
  simp only [parabolicMorreyUnitAverage]
  simp only [Pi.add_apply]
  rw [integral_add hf hg]
  ring

/-- The unit-box average commutes with real scalar multiplication. -/
theorem parabolicMorreyUnitAverage_smul  (c : ℝ) (f : TimeVelocity d → ℝ) :
    parabolicMorreyUnitAverage (c • f) = c • parabolicMorreyUnitAverage f := by
  simp only [parabolicMorreyUnitAverage]
  change (volume (parabolicMorreyUnitBox d)).toReal⁻¹ *
      ∫ z in parabolicMorreyUnitBox d, c • f z = c •
    ((volume (parabolicMorreyUnitBox d)).toReal⁻¹ *
      ∫ z in parabolicMorreyUnitBox d, f z)
  rw [integral_smul]
  simp only [smul_eq_mul]
  ring

variable (f g : TimeVelocity d → ℝ)

/-- A velocity moment coefficient is additive when its two weighted inputs
are integrable on the unit box. -/
theorem parabolicMorreyUnitVelocityCoeff_add   (i : Fin d)
    (hf : Integrable (fun z => f z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)))
    (hg : Integrable (fun z => g z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitVelocityCoeff (f + g) i =
      parabolicMorreyUnitVelocityCoeff f i +
        parabolicMorreyUnitVelocityCoeff g i := by
  simp only [parabolicMorreyUnitVelocityCoeff]
  rw [show (fun z  =>
      (f + g) z * z.2 i) = (fun z => f z * z.2 i) + fun z => g z * z.2 i by
        ext z
        simp only [Pi.add_apply]
        ring, parabolicMorreyUnitAverage_add _ _ hf hg]
  ring

/-- The moment projection is additive when the value and every first moment
of both inputs are integrable on the unit box. -/
theorem parabolicMorreyUnitAffineProjection_add
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d)))
    (hg : Integrable g (volume.restrict (parabolicMorreyUnitBox d)))
    (hfv : ∀ i : Fin d, Integrable (fun z => f z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)))
    (hgv : ∀ i : Fin d, Integrable (fun z => g z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitAffineProjection (f + g) =
      parabolicMorreyUnitAffineProjection f +
        parabolicMorreyUnitAffineProjection g := by
  funext z

  simp only [parabolicMorreyUnitAffineProjection, Pi.add_apply]
  rw [parabolicMorreyUnitAverage_add f g hf hg]
  simp_rw [(fun i => parabolicMorreyUnitVelocityCoeff_add f g i (hfv i) (hgv i))]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring




private theorem average_finset_sum {d ι : ℕ} (s : Finset (Fin ι))
    (f : Fin ι → TimeVelocity d → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitAverage (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, parabolicMorreyUnitAverage (f i) := by
  simp only [parabolicMorreyUnitAverage]
  rw [integral_finset_sum s hf, Finset.mul_sum]

variable {d : ℕ} (a : ℝ) (b : Fin d → ℝ)

private theorem average_velocity_affine  :
    parabolicMorreyUnitAverage
        (fun z  => a + ∑ i : Fin d, b i * z.2 i) = a := by
  let f : Fin d → TimeVelocity d → ℝ := fun i z => b i * z.2 i

  have hf : ∀ i : Fin d, Integrable (f i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i
    apply _root_.HypoellipticAleksandrov.Parabolic.continuous_integrable_parabolicMorreyUnitBox
    fun_prop

  rw [show (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) =
      (fun _ => a) + fun z => ∑ i : Fin d, f i z by
        ext z
        rfl
    , parabolicMorreyUnitAverage_add _ _ (by
        apply _root_.HypoellipticAleksandrov.Parabolic.continuous_integrable_parabolicMorreyUnitBox
        fun_prop) (integrable_finset_sum _ fun i _ => hf i),
      average_finset_sum Finset.univ f (fun i _ => hf i)]
  have hconst_avg : parabolicMorreyUnitAverage (fun _ : TimeVelocity d => a) = a := by
    rw [show (fun _ : TimeVelocity d => a) = a • (fun _ => (1 : ℝ)) by
      ext z
      simp
      , parabolicMorreyUnitAverage_smul, parabolicMorreyUnitAverage_one]
    simp
  rw [hconst_avg]
  simp_rw [show f = fun i => b i • (fun z : TimeVelocity d => z.2 i) by
    funext i z
    rfl]
  simp_rw [parabolicMorreyUnitAverage_smul, parabolicMorreyUnitAverage_velocity]
  simp only [smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]

private theorem coeff_velocity_affine
    (j : Fin d) :
    parabolicMorreyUnitVelocityCoeff
        (fun z  => a + ∑ i : Fin d, b i * z.2 i) j = b j := by
  let g : Fin d → TimeVelocity d → ℝ := fun i z => b i * (z.2 i * z.2 j)

  have hg : ∀ i : Fin d, Integrable (g i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i
    apply _root_.HypoellipticAleksandrov.Parabolic.continuous_integrable_parabolicMorreyUnitBox
    fun_prop

  rw [parabolicMorreyUnitVelocityCoeff]
  rw [show (fun z : TimeVelocity d =>
      (a + ∑ i : Fin d, b i * z.2 i) * z.2 j) =
      (fun z => a * z.2 j) + fun z => ∑ i : Fin d, g i z by
        ext z
        simp only [Pi.add_apply, g]
        rw [add_mul, Finset.sum_mul]
        ring_nf
    , parabolicMorreyUnitAverage_add _ _ (by
        apply _root_.HypoellipticAleksandrov.Parabolic.continuous_integrable_parabolicMorreyUnitBox
        fun_prop) (integrable_finset_sum _ fun i _ => hg i),
      average_finset_sum Finset.univ g (fun i _ => hg i)]
  have hfirst_avg : parabolicMorreyUnitAverage (fun z  => a * z.2 j) = 0 := by
    rw [show (fun z : TimeVelocity d => a * z.2 j) =
        a • (fun z : TimeVelocity d => z.2 j) by
          ext z
          rfl
      , parabolicMorreyUnitAverage_smul, parabolicMorreyUnitAverage_velocity]
    simp
  rw [hfirst_avg]
  simp_rw [show g = fun i => b i • (fun z : TimeVelocity d => z.2 i * z.2 j) by
    funext i z
    rfl]
  simp_rw [parabolicMorreyUnitAverage_smul,
    parabolicMorreyUnitAverage_velocity_mul_velocity]
  simp only [smul_eq_mul, zero_add]

  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · grind
  · intro i _ hij
    simp [hij]

/-- The canonical unit-box moment projection exactly reproduces every
time-independent velocity-affine scalar field. -/
theorem parabolicMorreyUnitAffineProjection_reproduces_velocity_affine
     :
    parabolicMorreyUnitAffineProjection
        (fun z  => a + ∑ i : Fin d, b i * z.2 i) =
      fun z => a + ∑ i : Fin d, b i * z.2 i := by
  funext z
  rw [parabolicMorreyUnitAffineProjection, average_velocity_affine]
  simp_rw [coeff_velocity_affine]

end HypoellipticAleksandrov.Parabolic
