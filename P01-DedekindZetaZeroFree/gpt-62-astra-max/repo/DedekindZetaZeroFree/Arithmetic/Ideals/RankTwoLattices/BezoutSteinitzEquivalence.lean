module

public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0)

include hI hJ in
theorem kp_cusp_ideal_bezout_row :
    ∃ a b u v : K, a ∈ I⁻¹ ∧ b ∈ J⁻¹ ∧ u ∈ I ∧ v ∈ J ∧ a * u + b * v = 1 := by
  obtain ⟨a₀, ha₀, haI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger
    (show I⁻¹ ≠ 0 by simpa using hI)
  let a := algebraMap R K a₀
  have ha := haI
  have hA : FractionalIdeal.spanSingleton R⁰ a * I ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    exact (FractionalIdeal.mem_inv_iff hI).mp ha
  obtain ⟨b, hab⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq hA
    (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (IsFractionRing.to_map_eq_zero_iff.not.mpr ha₀)) hI) hJ
  have hb : b ∈ J⁻¹ := by
    apply (FractionalIdeal.mem_inv_iff hJ).mpr
    intro y hy
    rw [← hab]
    exact (FractionalIdeal.mem_add _ _ _).mpr
      ⟨0, FractionalIdeal.zero_mem _, b * y, FractionalIdeal.mem_singleton_mul.mpr ⟨y, hy, rfl⟩,
        zero_add _⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := (FractionalIdeal.mem_add _ _ _).mp (by
    rw [hab]
    exact FractionalIdeal.one_mem_one R⁰)
  obtain ⟨u, hu, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hx
  obtain ⟨v, hv, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hy
  exact ⟨a, b, u, v, ha, hb, hu, hv, hxy⟩

include hI hJ in
theorem kp_cusp_ideal_steinitz_equiv_of_bezout
    (a b u v : K) (ha : a ∈ I⁻¹) (hb : b ∈ J⁻¹)
    (hu : u ∈ I) (hv : v ∈ J) (hrow : a * u + b * v = 1) :
    ∃ e : (R × (I * J)) ≃ₗ[R] (I × J),
      (∀ (r : R) (t : I * J),
        (e (r, t)).1.1 = algebraMap R K r * u - b * t.1 ∧
        (e (r, t)).2.1 = algebraMap R K r * v + a * t.1) ∧
      (∀ (x : I) (y : J),
        algebraMap R K (e.symm (x, y)).1 = a * x.1 + b * y.1 ∧
        (e.symm (x, y)).2.1 = u * y.1 - v * x.1) := by
  classical
  have hbt (t : I * J) : b * t.1 ∈ I := by
    simpa [mul_left_comm J⁻¹ I J, inv_mul_cancel₀ hJ] using (FractionalIdeal.mul_mem_mul hb t.property)
  have hat (t : I * J) : a * t.1 ∈ J := by
    simpa [← mul_assoc, inv_mul_cancel₀ hI] using (FractionalIdeal.mul_mem_mul ha t.property)
  let f : (R × (I * J)) →ₗ[R] (I × J) :=
    { toFun := fun p =>
        (⟨algebraMap R K p.1 * u - b * p.2.1,
          (I : Submodule R K).sub_mem
            (by simpa [Algebra.smul_def] using (I : Submodule R K).smul_mem p.1 hu)
            (hbt p.2)⟩,
         ⟨algebraMap R K p.1 * v + a * p.2.1,
          (J : Submodule R K).add_mem
            (by simpa [Algebra.smul_def] using (J : Submodule R K).smul_mem p.1 hv)
            (hat p.2)⟩)
      map_add' := by
        intro p q
        apply Prod.ext <;> apply Subtype.ext <;>
          simp [map_add] <;> ring
      map_smul' := by
        intro r p
        apply Prod.ext <;> apply Subtype.ext <;>
          simp [Algebra.smul_def, map_mul] <;> ring }
  have hfirst (p : R × (I * J)) :
      a * (f p).1.1 + b * (f p).2.1 = algebraMap R K p.1 := by
    change a * (algebraMap R K p.1 * u - b * p.2.1) +
      b * (algebraMap R K p.1 * v + a * p.2.1) = _
    calc
      _ = algebraMap R K p.1 * (a * u + b * v) := by ring
      _ = _ := by simp [hrow]
  have hsecond (p : R × (I * J)) :
      u * (f p).2.1 - v * (f p).1.1 = p.2.1 := by
    change u * (algebraMap R K p.1 * v + a * p.2.1) -
      v * (algebraMap R K p.1 * u - b * p.2.1) = _
    calc
      _ = p.2.1 * (a * u + b * v) := by ring
      _ = _ := by simp [hrow]
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      apply Prod.ext
      · apply IsFractionRing.injective R K
        rw [← hfirst p, ← hfirst q, hpq]
      · apply Subtype.ext
        rw [← hsecond p, ← hsecond q, hpq]
    · rintro ⟨x, y⟩
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff R⁰).mp ((1 : FractionalIdeal R⁰ K).1.add_mem
        ((FractionalIdeal.mem_inv_iff hI).mp ha x.1 x.property)
        ((FractionalIdeal.mem_inv_iff hJ).mp hb y.1 y.property))
      have ht : u * y.1 - v * x.1 ∈ I * J := by
        apply (I * J : FractionalIdeal R⁰ K).1.sub_mem
        · exact FractionalIdeal.mul_mem_mul hu y.property
        · change v * x.1 ∈ I * J
          simpa [mul_comm v] using FractionalIdeal.mul_mem_mul x.property hv
      refine ⟨(r, ⟨u * y.1 - v * x.1, ht⟩), ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · change algebraMap R K r * u - b * (u * y.1 - v * x.1) = x.1
        rw [hr]
        calc
          _ = x.1 * (a * u + b * v) := by ring
          _ = _ := by simp [hrow]
      · change algebraMap R K r * v + a * (u * y.1 - v * x.1) = y.1
        rw [hr]
        calc
          _ = y.1 * (a * u + b * v) := by ring
          _ = _ := by simp [hrow]
  let e := LinearEquiv.ofBijective f hbij
  refine ⟨e, ?_, ?_⟩
  · intro r t
    exact ⟨rfl, rfl⟩
  · intro x y
    have he : f (e.symm (x, y)) = (x, y) := e.apply_symm_apply (x, y)
    constructor
    · rw [← hfirst (e.symm (x, y)), he]
    · rw [← hsecond (e.symm (x, y)), he]

include hI hJ in
theorem kp_cusp_ideal_steinitz_nonempty :
    Nonempty ((I × J) ≃ₗ[R] (R × (I * J))) := by
  obtain ⟨a, b, u, v, ha, hb, hu, hv, hrow⟩ := kp_cusp_ideal_bezout_row R K I J hI hJ
  obtain ⟨e, _⟩ := kp_cusp_ideal_steinitz_equiv_of_bezout R K I J hI hJ
    a b u v ha hb hu hv hrow
  exact ⟨e.symm⟩

end DedekindZetaZeroFree
