module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Defs

@[expose] public section

open Finset Complex Filter Topology
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

theorem cor34_deriv_theta_at_zero {Δ y : ℝ} (hΔ : Δ < -1) :
    deriv (fun t : ℝ => Bethe.theta Δ t y) 0 =
      -1 + 2 * (1 + Real.cos y - 2 * Δ) /
        ((1 + Real.cos y - 2 * Δ) ^ 2 + (Real.sin y) ^ 2) := by
  let d : ℝ := 1 + Real.cos y - 2 * Δ
  have hd : 0 < d := by linarith [Real.neg_one_le_cos y]
  have hnum : HasDerivAt (fun t : ℝ => Real.sin t - Real.sin y) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).sub_const (Real.sin y)
  have hden : HasDerivAt (fun t : ℝ => Real.cos t + Real.cos y - 2 * Δ) 0 0 := by
    simpa using ((Real.hasDerivAt_cos 0).add_const (Real.cos y)).sub_const (2 * Δ)
  have hfrac : HasDerivAt
      (fun t : ℝ => (Real.sin t - Real.sin y) / (Real.cos t + Real.cos y - 2 * Δ)) (1 / d) 0 := by
    convert hnum.div hden (by rw [Real.cos_zero]; exact hd.ne') using 1
    rw [Real.sin_zero, Real.cos_zero]
    change 1 / d = (1 * d - (0 - Real.sin y) * 0) / d ^ 2
    field_simp [hd.ne']; ring
  have hlin : HasDerivAt (fun t : ℝ => y - t) (-1) 0 := by
    simpa using (hasDerivAt_id 0).const_sub y
  have htheta : HasDerivAt (fun t : ℝ => Bethe.theta Δ t y)
      (-1 + 2 * (1 / (1 + ((Real.sin 0 - Real.sin y) /
          (Real.cos 0 + Real.cos y - 2 * Δ)) ^ 2) * (1 / d))) 0 :=
    hlin.add (((Real.hasDerivAt_arctan _).comp 0 hfrac).const_mul 2)
  rw [htheta.deriv, Real.sin_zero, Real.cos_zero]
  change -1 + 2 * (1 / (1 + ((0 - Real.sin y) / d) ^ 2) * (1 / d)) =
    -1 + 2 * d / (d ^ 2 + Real.sin y ^ 2)
  field_simp [hd.ne']; ring

noncomputable def cor34_derivativeCorrection (ε y : ℝ) : ℝ :=
  2 * ε * (ε * (1 + Real.cos y) - 2) /
    ((ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2)

noncomputable def cor34_normalizedL (ε x : ℝ) : ℂ :=
  (((-ε / 2 : ℝ) : ℂ)) + ((1 - ε : ℝ) : ℂ) *
    BetheAnsatz.z x / (1 - BetheAnsatz.z x)

noncomputable def cor34_normalizedM (ε x : ℝ) : ℂ :=
  (((-ε / 2 : ℝ) : ℂ)) - ((1 - ε : ℝ) : ℂ) /
    (1 - BetheAnsatz.z x)

noncomputable def cor34_normalizedRegularEigenvalue {n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) : ℂ :=
  (∏ j : Fin n, cor34_normalizedL ε (p j)) +
    ∏ j : Fin n, cor34_normalizedM ε (p j)

noncomputable def cor34_normalizedZeroEigenvalue {N n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) (l : Fin n) : ℂ :=
  (((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
      ((N : ℝ) - 1 + ∑ j ∈ Finset.univ.erase l,
        (-1 + cor34_derivativeCorrection ε (p j)))) *
    ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)

private theorem cor34_continuousAt_z {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) :
    ContinuousAt (fun ε => BetheAnsatz.z (p ε j)) 0 := by
  have hpj : ContinuousAt (fun ε => p ε j) 0 := (continuous_apply j).continuousAt.comp hp
  unfold BetheAnsatz.z; fun_prop

theorem cor34_normalizedL_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) (hz : BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedL ε (p ε j)) (𝓝 0)
      (𝓝 (BetheAnsatz.z (p 0 j) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hZ := cor34_continuousAt_z hp j
  have hcont : ContinuousAt (fun ε => cor34_normalizedL ε (p ε j)) 0 := by
    unfold cor34_normalizedL
    exact (by fun_prop : ContinuousAt (fun ε : ℝ => ((-ε / 2 : ℝ) : ℂ)) 0).add
      (((by fun_prop : ContinuousAt (fun ε : ℝ => ((1 - ε : ℝ) : ℂ)) 0).mul hZ).div
        (continuousAt_const.sub hZ) (sub_ne_zero.mpr hz.symm))
  simpa [cor34_normalizedL] using hcont.tendsto

theorem cor34_normalizedM_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) (hz : BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedM ε (p ε j)) (𝓝 0)
      (𝓝 (-1 / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hZ := cor34_continuousAt_z hp j
  have hcont : ContinuousAt (fun ε => cor34_normalizedM ε (p ε j)) 0 := by
    unfold cor34_normalizedM
    exact (by fun_prop : ContinuousAt (fun ε : ℝ => ((-ε / 2 : ℝ) : ℂ)) 0).sub
      ((by fun_prop : ContinuousAt (fun ε : ℝ => ((1 - ε : ℝ) : ℂ)) 0).div
        (continuousAt_const.sub hZ) (sub_ne_zero.mpr hz.symm))
  simpa [cor34_normalizedM, neg_div] using hcont.tendsto

theorem cor34_normalizedRegularEigenvalue_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (hz : ∀ j, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((∏ j : Fin n, BetheAnsatz.z (p 0 j) /
              (1 - BetheAnsatz.z (p 0 j))) +
            ∏ j : Fin n, (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) :=
  (tendsto_finsetProd Finset.univ fun j _ => cor34_normalizedL_tendsto hp j (hz j)).add
    (tendsto_finsetProd Finset.univ fun j _ => cor34_normalizedM_tendsto hp j (hz j))

theorem cor34_derivativeCorrection_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (j : Fin n) :
    Tendsto (fun ε => cor34_derivativeCorrection ε (p ε j)) (𝓝 0) (𝓝 0) := by
  have hpj : ContinuousAt (fun ε => p ε j) 0 := (continuous_apply j).continuousAt.comp hp
  have hcont : ContinuousAt (fun ε => cor34_derivativeCorrection ε (p ε j)) 0 := by
    unfold cor34_derivativeCorrection
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  simpa [cor34_derivativeCorrection] using hcont.tendsto

theorem cor34_normalizedZeroEigenvalue_tendsto {N n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (l : Fin n)
    (hz : ∀ j ∈ Finset.univ.erase l, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε) l) (𝓝 0)
      (𝓝 (((N : ℂ) - (n : ℂ)) *
        ∏ j ∈ Finset.univ.erase l,
          (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hn : 1 ≤ n := Nat.zero_lt_of_lt l.isLt
  have hSum : Tendsto
      (fun ε : ℝ => ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection ε (p ε j)))
      (𝓝 0) (𝓝 (-((n - 1 : ℕ) : ℝ))) := by
    have hcard : (Finset.univ.erase l).card = n - 1 := by simp
    have h := tendsto_finsetSum (Finset.univ.erase l) fun j _ => by
      simpa using (tendsto_const_nhds (x := (-1 : ℝ))).add (cor34_derivativeCorrection_tendsto hp j)
    simpa [Finset.sum_const, hcard, Nat.cast_sub hn] using h
  have hReal : Tendsto
      (fun ε : ℝ => (N : ℝ) - 1 + ∑ j ∈ Finset.univ.erase l, (-1 + cor34_derivativeCorrection ε (p ε j)))
      (𝓝 0) (𝓝 ((N : ℝ) - n)) := by
    convert (tendsto_const_nhds (x := (N : ℝ) - 1)).add hSum using 2
    rw [Nat.cast_sub hn]; ring
  have hcast := (Complex.continuous_ofReal.continuousAt (x := (N : ℝ) - n)).tendsto.comp hReal
  have hneg : Tendsto (fun ε : ℝ => ((-ε : ℝ) : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ => ((-ε : ℝ) : ℂ)).continuousAt (x := 0)).tendsto
  have hOneMinus : Tendsto (fun ε : ℝ => (((1 - ε : ℝ) : ℂ))) (𝓝 0) (𝓝 1) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ => (((1 - ε : ℝ) : ℂ))).continuousAt (x := 0)).tendsto
  have hM := tendsto_finsetProd (Finset.univ.erase l) fun j hj =>
    cor34_normalizedM_tendsto hp j (hz j hj)
  simpa [cor34_normalizedZeroEigenvalue, div_eq_mul_inv, mul_assoc] using
    (hneg.add (hOneMinus.mul hcast)).mul hM

end PottsDiscontinuity.SixVertex
