module

public import OAI.NumberTheory.DirichletL.Energy.OriginalSource
public import OAI.NumberTheory.DirichletL.Energy.Bands

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergyInputParentCapacity
open CenteredMomentEnergyBands CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
variable {ι:Type*} [Fintype ι]

lemma raw_log_le_length (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    Real.logb Z X≤length Z X :=
  Real.logb_le_logb_of_le hZ hX (by simp)

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X) := by
  by_cases hx:1≤X
  · rw [length,max_eq_right hx,max_eq_right (Real.logb_nonneg hZ hx)]
  · have hh:X≤1:=le_of_not_ge hx
    have hl:Real.logb Z X≤0 := by
      simpa using Real.logb_le_logb_of_le hZ hX hh
    rw [length,max_eq_left hh,Real.logb_one,max_eq_left hl]

theorem postmask_length (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)=length Z X-min (Real.logb Z D) (length Z X) := by
  have hp:0<max 1 X:=by positivity
  have hd:0<D:=zero_lt_one.trans_le hD
  rw [length_eq_max_log Z _ hZ (by positivity),Real.logb_div hp.ne' hd.ne']
  change max 0 (length Z X-Real.logb Z D)=_
  grind

lemma postmask_length_le (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)≤length Z X := by
  rw [postmask_length Z X D hZ hD]
  have hm:0≤min (Real.logb Z D) (length Z X):=
    le_min (Real.logb_nonneg hZ hD) (length_nonneg Z X hZ)
  linarith

theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

theorem input_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [input_volume_log]
  have h1:=raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h2:=raw_log_le_length Z s.X₂ hZ s.X₂_pos
  nlinarith

theorem original_volume_cap (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(hk:1/6≤κ)
    (hP:∀i,1≤s.P i)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    volume s≤Z^M := by
  have hh:=input_affine_capacity s Z κ M hZ hcap
  have hn:0≤∑i,Real.logb Z (s.P i):=
    Finset.sum_nonneg (fun i _=>Real.logb_nonneg hZ (hP i))
  have hp:0≤(6*κ-1)*(∑i,Real.logb Z (s.P i)):=mul_nonneg (by linarith) hn
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (by linarith)

end SevenEighths.CenteredMomentEnergyInputParentCapacity

end

end OAI
