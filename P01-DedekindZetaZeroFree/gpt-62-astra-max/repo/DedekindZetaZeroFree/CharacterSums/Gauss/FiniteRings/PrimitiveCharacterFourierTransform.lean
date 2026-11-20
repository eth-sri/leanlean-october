module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.FiniteRings.Orthogonality

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped BigOperators Classical

section

variable {R : Type*} [CommMonoid R] (χ : Rˣ →* ℂ)

def unitCharExtend (x : R) : ℂ :=
  if hx : IsUnit x then χ hx.unit else 0

@[simp] theorem unitCharExtend_coe (u : Rˣ) : unitCharExtend χ (u : R) = χ u := by
  simp [unitCharExtend, dif_pos, u.isUnit]

theorem unitCharExtend_nonunit {x : R} (hx : ¬ IsUnit x) : unitCharExtend χ x = 0 := by
  simp [unitCharExtend, hx]

private theorem unitCharExtend_mul_unit (u : Rˣ) (x : R) :
    unitCharExtend χ ((u : R) * x) = χ u * unitCharExtend χ x := by
  by_cases hx : IsUnit x
  · obtain ⟨v, rfl⟩ := hx
    simp [← Units.val_mul]
  · simp_all [unitCharExtend_nonunit]

end

def IsPrimitiveRingUnitChar {R : Type*} [CommRing R] (χ : Rˣ →* ℂ) : Prop :=
  ∀ J : Ideal R, J ≠ ⊥ → ∃ u : Rˣ, (u : R) - 1 ∈ J ∧ χ u ≠ 1

variable {R : Type*} [CommRing R] [Fintype R] [hR : Nontrivial R]

include hR

def finiteRingGaussSum (e : AddChar R ℂ) (χ : Rˣ →* ℂ) : ℂ :=
  ∑ x : R, unitCharExtend χ x * e x

private theorem unitChar_inv_conj (χ : Rˣ →* ℂ) (u : Rˣ) :
    χ u⁻¹ = (starRingEnd ℂ) (χ u) := by
  let ψ : AddChar (Additive Rˣ) ℂ :=
    { toFun := fun v => χ v.toMul
      map_zero_eq_one' := χ.map_one
      map_add_eq_mul' := fun a b => χ.map_mul a.toMul b.toMul }
  apply ψ.map_neg_eq_conj

private theorem unitChar_nonunit_transform (e : AddChar R ℂ)
    (χ : Rˣ →* ℂ) (hχ : IsPrimitiveRingUnitChar χ) (k : R)
    (hk : ¬ IsUnit k) : finiteRingFourier e (unitCharExtend χ) k = 0 := by
  have hJ : Ideal.torsionOf R R k ≠ ⊥ := by
    intro h
    apply hk
    rw [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right]
    intro x hx
    have hm : x ∈ Ideal.torsionOf R R k := by
      simpa [Ideal.mem_torsionOf_iff] using hx
    simpa [h] using hm
  obtain ⟨u, hu, hne⟩ := hχ (Ideal.torsionOf R R k) hJ
  have huk : k * (u : R) = k := by
    have h : ((u : R) - 1) * k = 0 := by
      simpa [Ideal.mem_torsionOf_iff] using hu
    calc
      k * (u : R) = ((u : R) - 1) * k + k := by ring
      _ = k := by rw [h, zero_add]
  have hs : finiteRingFourier e (unitCharExtend χ) k =
      χ u * finiteRingFourier e (unitCharExtend χ) k := by
    unfold finiteRingFourier
    calc
      _ =
          ∑ x : R, unitCharExtend χ ((u : R) * x) * e (k * ((u : R) * x)) := (Equiv.sum_comp (Units.mulLeft u) _).symm
      _ = χ u * ∑ x : R, unitCharExtend χ x * e (k * x) := by
        simp only [unitCharExtend_mul_unit, ← mul_assoc, huk, Finset.mul_sum]
  refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  rw [sub_mul, one_mul, ← hs, sub_self]

theorem primitiveUnitChar_fourier (e : AddChar R ℂ)
    (he : IsPrimitiveRingAddChar e) (χ : Rˣ →* ℂ)
    (hχ : IsPrimitiveRingUnitChar χ) (k : R) :
    finiteRingFourier e (unitCharExtend χ) k =
      (starRingEnd ℂ) (unitCharExtend χ k) * finiteRingGaussSum e χ := by
  by_cases hk : IsUnit k
  · obtain ⟨u, rfl⟩ := hk
    rw [unitCharExtend_coe, ← unitChar_inv_conj]
    unfold finiteRingFourier finiteRingGaussSum
    calc
      (∑ x : R, unitCharExtend χ x * e ((u : R) * x)) =
          ∑ x : R, unitCharExtend χ ((↑u⁻¹ : R) * x) *
            e ((u : R) * ((↑u⁻¹ : R) * x)) := by
        exact (Equiv.sum_comp (Units.mulLeft u⁻¹) _).symm
      _ = χ u⁻¹ * ∑ x : R, unitCharExtend χ x * e x := by
        simp [unitCharExtend_mul_unit, Units.mul_inv_cancel_left, Finset.mul_sum, mul_assoc]
  · rw [unitChar_nonunit_transform e χ hχ k hk,
      unitCharExtend_nonunit χ hk, map_zero, zero_mul]

end

end DedekindZetaZeroFree.Hecke
