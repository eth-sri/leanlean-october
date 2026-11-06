module

public import OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost
public import OAI.NumberTheory.DirichletL.PrimeRows.CubeScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem cube_height_power_eventually (n : ℕ) (τ p loss : ℝ)
    (hτ : 0<τ) (hp : 0≤p) (hgap : τ*p<loss) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → (3+(3*i+2:ℕ)*Z^τ)^p≤Z^loss := by
  have hh := HeckeDyadic.constant_absorbed_eventually ((3*(n:ℝ)+5)^p)
    (loss-τ*p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by push_cast;nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^p := Real.rpow_le_rpow (by positivity) hx hp
    _ = (3*(n:ℝ)+5)^p*Z^(τ*p) := by
      rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hZp.le]
    _ ≤ Z^(loss-τ*p)*Z^(τ*p) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = Z^loss := by rw [←Real.rpow_add hZp];simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
