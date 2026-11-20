module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Corollary 3.4: regularized Bethe wave at infinite anisotropy

The parameter is `ε = 1/Δ`, and `-ε/2 = (-2Δ)⁻¹`.  The regularized coefficient is
written as a product of factors that extend continuously to `ε = 0`; at zero it is the
leading coefficient from the paper.  The paper labels sites from 1, whereas `State N n`
uses `Fin N` values 0 through `N-1`; the state associated with `(2,4,...,2n)` therefore
has underlying sites `{1,3,...,2n-1}`.
-/

@[expose] public section

open Finset Complex Filter Topology
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

/-- The number of ordered pairs `k < l` in `Fin n`, equal to `n(n-1)/2`. -/
def cor34_pairCount (n : ℕ) : ℕ := ∑ k : Fin n, (Finset.Ioi k).card

/-- A single amplitude factor after distributing the normalization `(-2Δ)⁻¹` over
one ordered pair. -/
noncomputable def cor34_amplitudeFactor (ε x y : ℝ) : ℂ :=
  BetheAnsatz.z x *
    (1 + (↑(-ε / 2) *
      (Complex.exp (-(I * x)) + BetheAnsatz.z y)))

section
variable {n : ℕ} (ε : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℤ) (hε : ε ≠ 0)

include ε p σ in
/-- The regularized coefficient `(-2Δ)^(-n(n-1)/2) A_σ`, extended to `ε=0`. -/
noncomputable def cor34_normalizedAmplitude : ℂ :=
  (Equiv.Perm.sign σ) *
    ∏ k, ∏ l ∈ Finset.Ioi k,
      cor34_amplitudeFactor ε (p (σ k)) (p (σ l))

@[simp] theorem cor34_normalizedAmplitude_zero :
    cor34_normalizedAmplitude 0 p σ =
      (Equiv.Perm.sign σ) *
        ∏ k, ∏ _l ∈ Finset.Ioi k,
          BetheAnsatz.z (p (σ k)) := by
  simp [cor34_normalizedAmplitude, cor34_amplitudeFactor]

include hε in
/-- At nonzero ε, the regularized coefficient is exactly the source coefficient multiplied by
`(-ε/2)^(n(n-1)/2)`. -/
theorem cor34_normalizedAmplitude_eq_scaled_amplitude :
    cor34_normalizedAmplitude ε p σ =
      (↑(-ε / 2) ^ cor34_pairCount n) *
        BetheAnsatz.amplitude (1 / ε) p σ := by
  let product (k) (l) := BetheAnsatz.z (p (σ k)) * BetheAnsatz.scattering (1 / ε) (p (σ k)) (p (σ l))
  classical
  let q := -ε / 2
  have hfactor (x y : ℝ) :
      cor34_amplitudeFactor ε x y =
        q * (BetheAnsatz.z x * BetheAnsatz.scattering (1 / ε) x y) := by
    have hscale : q * (-2 * (↑(1 / ε) : ℂ)) = 1 := by
      dsimp [q]
      push_cast
      field_simp [hε]
    change BetheAnsatz.z x *
      (1 + q * (Complex.exp (-(I * x)) + BetheAnsatz.z y)) =
      q * (BetheAnsatz.z x *
        (Complex.exp (-(I * x)) + BetheAnsatz.z y -
          2 * ↑(1 / ε)))
    grind
  have hinner (k : Fin n) :
      (∏ l ∈ Finset.Ioi k, q *
        (product k l)) =
      q ^ (Finset.Ioi k).card *
        ∏ l ∈ Finset.Ioi k,
          (product k l) := by
    simp [Finset.prod_mul_distrib]
  have houter :
      (∏ k, ∏ l ∈ Finset.Ioi k, q *
        (product k l)) =
      ∏ k, (q ^ (Finset.Ioi k).card *
        ∏ l ∈ Finset.Ioi k,
          (product k l)) := by
    grind
  calc
    _ =
        (Equiv.Perm.sign σ) *
          ∏ k, ∏ l ∈ Finset.Ioi k, q *
            (product k l) := by
      unfold cor34_normalizedAmplitude
      grind
    _ = q ^ cor34_pairCount n *
          ((Equiv.Perm.sign σ) *
            ∏ k, ∏ l ∈ Finset.Ioi k,
              (product k l)) := by
      simp only [cor34_pairCount]
      rw [houter, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    _ = _ := rfl

include ε p x in
/-- The regularized coordinate Bethe wave.  This is defined at ε=0 by the continuous extension
of each coefficient, so no default branch is used. -/
noncomputable def cor34_normalizedCoordinate : ℂ :=
  ∑ σ,
    cor34_normalizedAmplitude ε p σ * BetheAnsatz.planeWave p σ x

/-- The regularized coordinate wave is continuous in `(ε,p)`. -/
theorem cor34_normalizedCoordinate_tendsto {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (x : Fin n → ℤ) :
    Tendsto (fun ε => cor34_normalizedCoordinate ε (p ε) x) (𝓝 0)
      (𝓝 (cor34_normalizedCoordinate 0 (p 0) x)) := by
  have hF : ContinuousAt (fun q : ℝ × (Fin n → ℝ) =>
      cor34_normalizedCoordinate q.1 q.2 x) (0, p 0) := by
    have hAmp (σ : Equiv.Perm (Fin n)) : Continuous (fun q : ℝ × (Fin n → ℝ) =>
        cor34_normalizedAmplitude q.1 q.2 σ) := by
      exact continuous_const.mul (by
        apply continuous_finsetProd Finset.univ
        intro k hk
        apply continuous_finsetProd _
        intro l hl
        dsimp [cor34_amplitudeFactor, BetheAnsatz.z]
        fun_prop)
    have hsum : Continuous (fun q : ℝ × (Fin n → ℝ) =>
        ∑ σ,
          cor34_normalizedAmplitude q.1 q.2 σ *
            BetheAnsatz.planeWave q.2 σ x) := by
      apply continuous_finsetSum Finset.univ
      intro σ hσ
      exact (hAmp σ).mul (by
        dsimp [BetheAnsatz.planeWave, BetheAnsatz.z]
        fun_prop)
    exact hsum.continuousAt
  have hlim := hF.tendsto.comp (continuousAt_id.tendsto.prodMk_nhds hp)
  assumption

include hε in
/-- Away from `ε=0`, the regularized coordinate is exactly the source coordinate wave multiplied
by `(-ε/2)^(n(n-1)/2)`. -/
theorem cor34_normalizedCoordinate_eq_scaled_coordinateWave :
    cor34_normalizedCoordinate ε p x =
      (↑(-ε / 2) ^ cor34_pairCount n) *
        BetheAnsatz.coordinateWave (1 / ε) p x := by
  grind [cor34_normalizedAmplitude_eq_scaled_amplitude ε p _ hε, Finset.mul_sum, cor34_normalizedCoordinate, BetheAnsatz.coordinateWave]

end

variable {N n : ℕ} (hN : 2 * n ≤ N)
include hN

end PottsDiscontinuity.SixVertex
