module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculus
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Local directional chain rules used by the position clock -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open scoped Topology

/-- The scalar-coordinate direction corresponding to a named field. -/
def coordinateDirection (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- The directional derivative in native scalar coordinates. -/
def directional (f : (Fin 3 → ℝ) → ℝ) (d q : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ f q d

/-- Exact derivative of a straight scalar-coordinate line. -/
theorem hasDerivAt_coordinateLine (q d : Fin 3 → ℝ) (t₀ t : ℝ) :
    HasDerivAt (fun t  => q + (t-t₀) • d) d t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_zero, one_mul] using!
    (((hasDerivAt_id t).sub_const t₀).mul_const (d i)).const_add (q i)

variable (f : (Fin 3 → ℝ) → ℝ)

variable (q d : Fin 3 → ℝ) (t₀ : ℝ)

/-- The first chain rule along an affine line, with local differentiability only. -/
theorem deriv_coordinateLine   (hf : DifferentiableAt ℝ f q) :
    deriv (fun t => f (q + (t-t₀) • d)) t₀ = directional f d q := by
  have hq : q + (t₀-t₀) • d = q := by simp only [sub_self, zero_smul, add_zero]
  have hf' : HasFDerivAt f (fderiv ℝ f q) (q + (t₀-t₀) • d) := by
    simpa only [hq] using! hf.hasFDerivAt

  simpa only [hq, directional] using! (hf'.comp_hasDerivAt t₀ (hasDerivAt_coordinateLine q d t₀ t₀)).deriv

/-- The second directional chain rule; finite C-two regularity supplies the neighborhood. -/
theorem deriv_deriv_coordinateLine   (hf : ContDiffAt ℝ 2 f q) :
    deriv (deriv (fun t => f (q + (t-t₀) • d))) t₀ =
      directional (directional f d) d q := by
  let sharedTerm_7bb03cd89e := ((fun t => f (q + (t - t₀) • d)))

  have hc : ContinuousAt (fun t  => q + (t-t₀) • d) t₀ := by fun_prop
  have hq : q + (t₀-t₀) • d = q := by simp only [sub_self, zero_smul, add_zero]
  change Filter.Tendsto _ (𝓝 t₀) (𝓝 (q + (t₀-t₀) • d)) at hc
  rw [hq] at hc

  have he : deriv sharedTerm_7bb03cd89e =ᶠ[𝓝 t₀]
      fun t => directional f d (q + (t-t₀) • d) := by
    filter_upwards [(hc.eventually (hf.eventually (by norm_num)))] with t ht
    have hl := deriv_coordinateLine f (q + (t-t₀) • d) d t
      (ht.differentiableAt (by norm_num))
    have heq : (fun s => f ((q + (t-t₀) • d) + (s-t) • d)) =
        sharedTerm_7bb03cd89e := by
      funext s
      congr 1
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq] at hl
    exact hl
  rw [he.deriv_eq]

  exact deriv_coordinateLine (directional f d) q d t₀
    ((show ContDiffAt ℝ 1 (directional f d) q by
        exact (hf.fderiv_right (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num))

variable (q : Fin 3 → ℝ) (i : Fin 3)

/-- A named partial derivative is the scalar derivative on its coordinate line. -/
theorem deriv_coordinate_slice   (hf : DifferentiableAt ℝ f q) :
    deriv (fun t => f (Function.update q i t)) (q i) =
      directional f (coordinateDirection i) q := by
  have he : (fun t => f (Function.update q i t)) =
      fun t => f (q + (t-q i) • coordinateDirection i) := by
    funext t
    congr 1
    ext j
    by_cases hij : j = i
    · subst j
      simp [coordinateDirection]
    · simp [coordinateDirection, hij]
  rw [he]
  exact deriv_coordinateLine f q _ (q i) hf

/-- The second named partial derivative is likewise the scalar second slice derivative. -/
theorem deriv_deriv_coordinate_slice   (hf : ContDiffAt ℝ 2 f q) :
    deriv (deriv (fun t => f (Function.update q i t))) (q i) =
      directional (directional f (coordinateDirection i)) (coordinateDirection i) q := by
  have he : (fun t => f (Function.update q i t)) =
      fun t => f (q + (t-q i) • coordinateDirection i) := by
    funext t
    congr 1
    ext j
    by_cases hij : j = i
    · subst j
      simp [coordinateDirection]
    · simp [coordinateDirection, hij]
  rw [he]
  exact deriv_deriv_coordinateLine f q _ (q i) hf

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
