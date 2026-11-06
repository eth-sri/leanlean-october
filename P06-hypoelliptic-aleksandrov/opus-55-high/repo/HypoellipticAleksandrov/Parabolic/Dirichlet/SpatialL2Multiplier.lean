module

public import PDEFoundation.Measure.LpSpace
public import Mathlib.Tactic.Ring

/-!
# Bounded scalar multipliers on spatial `L²`

This module constructs multiplication by an essentially bounded real coefficient
on the quotient `L²` space for restricted volume.  The construction is entirely
spatial and makes no assertion about a PDE, a variational form, or a solver.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A bounded scalar multiplier preserves spatial `L²` membership. -/
theorem scalarL2Multiplier_memLp
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : MeasureTheory.AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    MemLp (fun y => q y * f y) (2 : ℝ≥0∞) (PDE.volumeOn Ω) := by
  apply (Lp.memLp f).of_le_mul (c := C) (hq.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hqBound] with y hy
  change ‖q y * f y‖ ≤ C * ‖f y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

/-- The linear map underlying the bounded spatial multiplier. -/
def scalarL2MultiplierLinearMap
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : MeasureTheory.AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →ₗ[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) where
  toFun f := (scalarL2Multiplier_memLp q hq C hqBound f).toLp
    (fun y => q y * f y)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [
      (scalarL2Multiplier_memLp q hq C hqBound (f + g)).coeFn_toLp,
      (scalarL2Multiplier_memLp q hq C hqBound f).coeFn_toLp,
      (scalarL2Multiplier_memLp q hq C hqBound g).coeFn_toLp,
      Lp.coeFn_add
        ((scalarL2Multiplier_memLp q hq C hqBound f).toLp _)
        ((scalarL2Multiplier_memLp q hq C hqBound g).toLp _),
      Lp.coeFn_add f g] with y hyadd hyf hyg hyrhs hfg
    calc
      (scalarL2Multiplier_memLp q hq C hqBound _).toLp
          _ y = q y * (f + g) y := hyadd
      _ = q y * (f y + g y) := by simp_all
      _ = q y * f y + q y * g y := by ring
      _ = ((scalarL2Multiplier_memLp q hq C hqBound f).toLp
          _ + (scalarL2Multiplier_memLp q hq C hqBound g).toLp
          _) y := by
            simp_all
      _ = _ := rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [
      (scalarL2Multiplier_memLp q hq C hqBound (c • f)).coeFn_toLp,
      (scalarL2Multiplier_memLp q hq C hqBound f).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c
        ((scalarL2Multiplier_memLp q hq C hqBound f).toLp _)]
      with y hycf hyf hcf hyrhs
    calc
      (scalarL2Multiplier_memLp q hq C hqBound _).toLp
          _ y = q y * (c • f) y := hycf
      _ = q y * (c • f y) := by simp_all
      _ = c • (q y * f y) := by ring
      _ = c • ((scalarL2Multiplier_memLp q hq C hqBound f).toLp
          _) y := by rw [hyf]
      _ = _ := hyrhs.symm

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (q : PDE.Vec d → ℝ) (hq : MeasureTheory.AEStronglyMeasurable q (PDE.volumeOn Ω)) (C : ℝ) (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)

private theorem scalarL2MultiplierLinearMap_apply_ae
    
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ⇑(scalarL2MultiplierLinearMap q hq C hqBound f) =ᵐ[PDE.volumeOn Ω]
      fun y => q y * f y := (scalarL2Multiplier_memLp q hq C hqBound f).coeFn_toLp

/-- The pointwise coefficient bound controls the norm of the underlying linear map. -/
theorem norm_scalarL2MultiplierLinearMap_apply_le
    
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖scalarL2MultiplierLinearMap q hq C hqBound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarL2MultiplierLinearMap_apply_ae q hq C hqBound f, hqBound]
    with y hy hyq
  rw [hy, norm_mul]
  exact mul_le_mul_of_nonneg_right hyq (norm_nonneg _)

/-- Multiplication by an essentially bounded real coefficient on spatial restricted-volume `L²`. -/
def scalarL2Multiplier
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : MeasureTheory.AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  LinearMap.mkContinuous (scalarL2MultiplierLinearMap q hq C hqBound) C
    (norm_scalarL2MultiplierLinearMap_apply_le q hq C hqBound)

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (q : PDE.Vec d → ℝ) (hq : MeasureTheory.AEStronglyMeasurable q (PDE.volumeOn Ω)) (C : ℝ) (hC : 0 ≤ C)

/-- The multiplier is represented almost everywhere by pointwise multiplication. -/
theorem scalarL2Multiplier_apply_ae
    
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ⇑(scalarL2Multiplier q hq C hC hqBound f) =ᵐ[PDE.volumeOn Ω]
      fun y => q y * f y := scalarL2MultiplierLinearMap_apply_ae q hq C hqBound f

/-- The `L²` norm of a multiplied class is bounded by the essential coefficient bound. -/
theorem norm_scalarL2Multiplier_apply_le
    
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖scalarL2Multiplier q hq C hC hqBound f‖ ≤ C * ‖f‖ := norm_scalarL2MultiplierLinearMap_apply_le q hq C hqBound f

end HypoellipticAleksandrov.Parabolic.Dirichlet
