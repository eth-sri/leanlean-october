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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set
open scoped Real ComplexConjugate

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

private theorem shift_param_mem_frontier (hγ : IsBoundaryParam Ω γ) (θ : ℝ) : γ θ ∈ frontier Ω := by
  rw [← hγ.image]
  refine ⟨toIcoMod Real.two_pi_pos 0 θ, ?_, ?_⟩
  · have := toIcoMod_mem_Ico Real.two_pi_pos 0 θ
    grind
  · rw [toIcoMod, hγ.periodic.sub_zsmul_eq]

private theorem shift_param_eq_of_eq (hγ : IsBoundaryParam Ω γ) {x y : ℝ} (hxy : γ x = γ y)
    (hlt : |x - y| < 2 * π) : x = y := by
  have hmem : ∀ z, toIcoMod Real.two_pi_pos 0 z ∈ Ico 0 (2 * π) := fun z => by
    have := toIcoMod_mem_Ico Real.two_pi_pos 0 z
    simp_all
  have hval : ∀ z, γ (toIcoMod Real.two_pi_pos 0 z) = γ z := fun z => by
    rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  have h := hγ.injOn (hmem x) (hmem y) (by simp_all)
  simp only [toIcoMod] at h
  set n := toIcoDiv Real.two_pi_pos 0 x
  set m := toIcoDiv Real.two_pi_pos 0 y
  have hd : x - y = ((n - m : ℤ) : ℝ) * (2 * π) := by
    grind
  have hk : n - m = 0 := by
    rw [hd, abs_mul, abs_of_pos Real.two_pi_pos] at hlt
    have h1 : |((n - m : ℤ) : ℝ)| < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith [Real.two_pi_pos]
    rw [← Int.cast_abs] at h1
    have : |n - m| < 1 := by exact_mod_cast h1
    simp_all
  grind

/-- A cyclic change of the starting point is again a positively oriented,
constant-speed parametrization of exactly the same physical boundary. -/
theorem IsBoundaryParam.shift (hγ : IsBoundaryParam Ω γ) (t : ℝ) :
    IsBoundaryParam Ω (fun θ => γ (θ + t)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hper : Function.Periodic (fun θ => γ (θ + t)) (2 * π) := by
    intro θ
    calc
      _ = γ ((θ + t) + 2 * π) := by ring
      _ = _ := hγ.periodic (θ + t)
  have hval (s : ℝ) :
      γ (toIcoMod Real.two_pi_pos 0 s + t) = γ (s + t) := hper.sub_zsmul_eq (toIcoDiv Real.two_pi_pos 0 s)
  refine ⟨⟨K, LipschitzWith.of_dist_le_mul fun x y => by
      simpa using hK.dist_le_mul (x + t) (y + t)⟩, hper, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have heq := shift_param_eq_of_eq hγ hxy (by
      grind)
    linarith
  · apply Set.Subset.antisymm
    · rintro z ⟨θ, _, rfl⟩
      exact shift_param_mem_frontier hγ (θ + t)
    · intro z hz
      rw [← hγ.image] at hz
      obtain ⟨s, _, hsz⟩ := hz
      refine ⟨toIcoMod Real.two_pi_pos 0 (s - t), by
        have h := toIcoMod_mem_Ico Real.two_pi_pos 0 (s - t)
        grind, ?_⟩
      simp_all
  · obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
    refine ⟨c, hc, ?_⟩
    simpa only [deriv_comp_add_const] using (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hspeed
  · calc
      _ = ∫ θ in 0..(2 * π), signedAreaDensity γ (θ + t) := by
        simp [signedAreaDensity, deriv_comp_add_const]
      _ = ∫ θ in t..t + 2 * π, signedAreaDensity γ θ := by
        simp [add_comm (2 * π) t]
      _ = ∫ θ in 0..(2 * π), signedAreaDensity γ θ :=
        integral_signedAreaDensity_shift hγ.periodic t
      _ = _ := hγ.area

end PolyaNeumann

end
