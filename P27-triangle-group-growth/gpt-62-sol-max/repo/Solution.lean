module
public import CoxeterGrowth.Family

@[expose] public section
namespace TriangleGrowth

open CoxeterGrowth.Triangle PowerSeries Finset Filter Topology

section
variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

section
variable (h01 : M 0 1 = 0)

section
include h01
attribute [local simp] sum_Ico_eq_sum_range sum_range_succ

/-- The closed form for `(2,3,∞)`. -/
theorem growth_series_23 (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    series(cs) * (1 - X ^ 2 - X ^ 3) = (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  linear_combination (norm := (simp; ring))
    growth_series cs (by decide) (by decide) h01 h02 h12

/-- The closed form for `(2,4,∞)`. -/
theorem growth_series_24 (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    series(cs) * (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  linear_combination (norm := (simp; ring))
    growth_series cs (by decide) (by decide) h01 h02 h12

/-- The closed form for `(3,3,∞)`. -/
theorem growth_series_33 (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    series(cs) * (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  linear_combination (norm := (simp; ring))
    growth_series cs (by decide) (by decide) h01 h02 h12
end

private lemma induct23 {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (step : ∀ k, P k → P (k+1) → P (k+3)) : ∀ n, P n
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | k+3 => step k (induct23 h0 h1 h2 step k) (induct23 h0 h1 h2 step (k+1))

variable (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
include h01 h02 h12

local notation:max "a[" n "]" => sphere(cs,n)

/-- The first five sphere sizes and the subsequent Padovan recurrence. -/
theorem sphere23_values : a[0] = 1 ∧ a[1] = 3 ∧ a[2] = 5 ∧ a[3] = 7 ∧ a[4] = 9 ∧
    ∀ n : ℕ, a[n+5] = a[n+3] + a[n+2] := by
  simp only [sphere_card cs (show IsTri M 2 3 from ⟨by decide,by decide,h01,h02,h12⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun n => ?rec⟩
  case rec =>
    have h := slice_rec (p := 2) (q := 3) (by decide) (show 2+3 ≤ n+5 by omega)
    have ho : offsets 2 3 = {(1,1),(1,2)} := by decide
    simpa [ho, hl, add_comm] using h
  all_goals rw [nfCount, Nat.card_eq_fintype_card]; decide +kernel

/-- The recurrence does not hold for the sphere of radius four. -/
theorem sphere23_rec_fails_at_4 : a[4] ≠ a[2] + a[1] := by
  obtain ⟨_,h1,h2,_,h4,_⟩ := sphere23_values cs h01 h02 h12
  omega

/-- Sphere sizes agree with the shifted Padovan sequence from radius two onward. -/
theorem sphere23_padovan (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n+3) = pad (n+1) + pad n) (n : ℕ) (hn : 2 ≤ n) : a[n] = pad (n+5) := by
  obtain ⟨_,_,h2,h3,h4,hr⟩ := sphere23_values cs h01 h02 h12
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' hn
  refine induct23 (P := fun k => a[k+2] = pad (k+7)) ?_ ?_ ?_ (fun k hk hk' => ?step) m
  case step =>
    simp only [hr k, hpr (k+7), hk, hk']
  all_goals repeat' rw [hpr]; norm_num [hp0,hp1,hp2,h2,h3,h4]

variable (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1)
include hρ hρ3

/-- Explicit exponential bounds for the `(2,3,∞)` sphere sizes. -/
theorem sphere23_growth_bounds (n : ℕ) :
    2 * ρ ^ (n+2) ≤ (a[n+2] : ℝ) ∧ (a[n+2] : ℝ) ≤ 4 * ρ ^ (n+2) := by
  obtain ⟨_,_,h2,h3,h4,hr⟩ := sphere23_values cs h01 h02 h12
  have hhi : ρ^2 < 2 := by nlinarith
  have hρ4 : ρ^4 = ρ^2 + ρ := by linear_combination ρ*hρ3
  refine induct23 (P := fun k => 2 * ρ^(k+2) ≤ (a[k+2] : ℝ) ∧ (a[k+2] : ℝ) ≤ 4 * ρ^(k+2)) ?_ ?_ ?_ ?step n
  case step =>
    intro k hk hk'
    have hpow : ρ^(k+5) = ρ^(k+3) + ρ^(k+2) := by linear_combination ρ^(k+2)*hρ3
    rw [hr k, hpow]
    push_cast
    grind
  all_goals norm_num [h2,h3,h4,hρ3,hρ4]; constructor <;> nlinarith

/-- The growth rate for `(2,3,∞)` is the plastic number. -/
theorem sphere23_root_tendsto :
    Tendsto (fun n : ℕ => (a[n] : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 ρ) :=
  sphere_root_tendsto_rate cs (by decide) (by decide) h01 h02 h12 ρ hρ
    ((rate23_iff (by positivity)).2 hρ3)
end

/-- Every hyperbolic member has at least as many elements per sphere as `(2,3,∞)`. -/
theorem sphere_ge_plastic {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p,q) ≠ (2,2))
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ^3 = ρ+1) (n : ℕ) :
    2 * ρ^(n+2) ≤ (sphere(cs,n+2) : ℝ) := by
  obtain ⟨M',h01',h02',h12'⟩ := triangle_matrix_exists 2 3 (by decide) (by decide)
  have h := (sphere23_growth_bounds M'.toCoxeterSystem h01' h02' h12' ρ hρ hρ3 n).1
  rw [sphere_card _ ⟨by decide,by decide,h01',h02',h12'⟩] at h
  rw [sphere_card _ ⟨hp,hq,h01,h02,h12⟩]
  refine h.trans (Nat.cast_le.2 ?_)
  obtain h | h : 3 ≤ p ∨ 3 ≤ q := by grind
  · rw [slice_symm (by decide : 2 ≤ 2) (by decide : 2 ≤ 3)]
    exact slice_mono h hq _
  · exact slice_mono hp h _

end
end TriangleGrowth
