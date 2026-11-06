module

public import RequestProject.ArcLength

/-!
# Cyclic shifts of the actual physical boundary parametrization

Changing the starting point preserves all fields of `IsBoundaryParam`.
In particular, the genuine constant-speed condition is transported by
Lebesgue translation, and the signed-area identity is preserved by the
periodic integral identity. This permits choosing the nonzero transport
cut of `BoundaryOrigin` while keeping the original physical definition.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set
open scoped Real ComplexConjugate

private theorem shift_param_eq_of_eq  
    (hγ : IsBoundaryParam Ω γ)  (hxy : γ x = γ y)
    (hlt : |x - y| < 2 * π) : x = y := by
  have hmem : ∀ z, toIcoMod Real.two_pi_pos 0 z ∈ Ico 0 (2 * π) := fun z => by
    have := toIcoMod_mem_Ico Real.two_pi_pos 0 z
    rwa [zero_add] at this
  have hval : ∀ z, γ (toIcoMod Real.two_pi_pos 0 z) = γ z := fun z => by
    rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  have h := hγ.injOn (hmem x) (hmem y) (by rw [hval, hval, hxy])
  simp only [toIcoMod] at h
  set n := toIcoDiv Real.two_pi_pos 0 x
  set m := toIcoDiv Real.two_pi_pos 0 y
  have hd : x - y = (n - m : ℤ) * (2 * π) := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at h
    push_cast
    linarith
  rw [show n - m = 0 by
    rw [hd, abs_mul, abs_of_pos Real.two_pi_pos] at hlt
    have h1 : |((n - m : ℤ) : ℝ)| < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith [Real.two_pi_pos]
    rw [← Int.cast_abs] at h1
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)] at hd
  simp at hd
  linarith

/-- A cyclic change of the starting point is again a positively oriented,
constant-speed parametrization of exactly the same physical boundary. -/
theorem IsBoundaryParam.shift  
    (hγ : IsBoundaryParam Ω γ) t :
    IsBoundaryParam Ω (fun θ => γ (θ + t)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hKt : LipschitzWith K (fun θ => γ (θ + t)) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa using hK.dist_le_mul (x + t) (y + t)
  have hper : Function.Periodic (fun θ => γ (θ + t)) (2 * π) := by
    intro θ
    change γ ((θ + 2 * π) + t) = _
    calc
      _ = γ ((θ + t) + 2 * π) := by congr 1; ring
      _ = _ := hγ.periodic (θ + t)
  have hval s :
      γ (toIcoMod Real.two_pi_pos 0 s + t) = γ (s + t) := by
    change (fun θ => γ (θ + t)) (toIcoMod Real.two_pi_pos 0 s) = _
    rw [toIcoMod]
    exact hper.sub_zsmul_eq (toIcoDiv Real.two_pi_pos 0 s)
  refine ⟨⟨K, hKt⟩, hper, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have heq := shift_param_eq_of_eq hγ hxy (by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
    linarith
  · apply Set.Subset.antisymm
    · rintro z ⟨θ, _, rfl⟩
      exact (by
        rw [← hγ.image]
        refine ⟨toIcoMod Real.two_pi_pos 0 (θ + t), ?_, ?_⟩
        · have := toIcoMod_mem_Ico Real.two_pi_pos 0 (θ + t)
          rw [zero_add] at this
          exact Ico_subset_Icc_self this
        · rw [toIcoMod, hγ.periodic.sub_zsmul_eq])
    · intro z hz
      rw [← hγ.image] at hz
      obtain ⟨s, _, hsz⟩ := hz
      refine ⟨toIcoMod Real.two_pi_pos 0 (s - t), (by
        have h := toIcoMod_mem_Ico Real.two_pi_pos 0 (s - t)
        rw [zero_add] at h
        exact Ico_subset_Icc_self h), ?_⟩
      calc
        _ = _ := hval (s - t)
        _ = _ := by rw [sub_add_cancel]
        _ = z := hsz
  · obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
    refine ⟨c, hc, ?_⟩
    simpa [deriv_comp_add_const] using (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hspeed
  · change (∫ θ in 0..(2 * π), signedAreaDensity (fun θ => γ (θ + t)) θ) =
      2 * (volume Ω).toReal
    calc
      _ = ∫ θ in 0..(2 * π), signedAreaDensity γ (θ + t) := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp [signedAreaDensity, deriv_comp_add_const]
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * π) t]
      _ = _ :=
        integral_signedAreaDensity_shift hγ.periodic t
      _ = _ := hγ.area

end PolyaNeumann

end
