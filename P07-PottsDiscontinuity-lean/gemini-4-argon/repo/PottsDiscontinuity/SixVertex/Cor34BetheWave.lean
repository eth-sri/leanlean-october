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
    (1 + (((-ε / 2 : ℝ) : ℂ) *
      (Complex.exp (-(I * (x : ℂ))) + BetheAnsatz.z y)))

/-- The regularized coefficient `(-2Δ)^(-n(n-1)/2) A_σ`, extended to `ε=0`. -/
noncomputable def cor34_normalizedAmplitude {n : ℕ} (ε : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  (Equiv.Perm.sign σ : ℤ) *
    ∏ k : Fin n, ∏ l ∈ Finset.Ioi k,
      cor34_amplitudeFactor ε (p (σ k)) (p (σ l))

@[simp] theorem cor34_normalizedAmplitude_zero {n : ℕ} (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    cor34_normalizedAmplitude 0 p σ =
      (Equiv.Perm.sign σ : ℤ) *
        ∏ k : Fin n, ∏ _l ∈ Finset.Ioi k,
          BetheAnsatz.z (p (σ k)) := by
  simp [cor34_normalizedAmplitude, cor34_amplitudeFactor]

/-- At nonzero ε, the regularized coefficient is exactly the source coefficient multiplied by
`(-ε/2)^(n(n-1)/2)`. -/
theorem cor34_normalizedAmplitude_eq_scaled_amplitude {n : ℕ} (ε : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hε : ε ≠ 0) :
    cor34_normalizedAmplitude ε p σ =
      (((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n) *
        BetheAnsatz.amplitude (1 / ε) p σ := by
  classical
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  have hfactor (x y : ℝ) :
      cor34_amplitudeFactor ε x y =
        q * (BetheAnsatz.z x * BetheAnsatz.scattering (1 / ε) x y) := by
    have hscale : q * (-2 * ((1 / ε : ℝ) : ℂ)) = 1 := by
      dsimp [q]; push_cast; field_simp [hε]
    change BetheAnsatz.z x * (1 + q * (Complex.exp (-(I * (x : ℂ))) + BetheAnsatz.z y)) =
      q * (BetheAnsatz.z x * (Complex.exp (-(I * (x : ℂ))) + BetheAnsatz.z y - 2 * ((1 / ε : ℝ) : ℂ)))
    linear_combination -BetheAnsatz.z x * hscale
  unfold cor34_normalizedAmplitude BetheAnsatz.amplitude cor34_pairCount
  simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  ring

/-- The source coordinate tuple `(2,4,...,2n)` as an integer-position function. -/
def cor34_sourceEvenPositions {n : ℕ} : Fin n → ℤ :=
  fun k => (2 * (k.val + 1) : ℕ)

/-- The regularized coordinate Bethe wave.  This is defined at ε=0 by the continuous extension
of each coefficient, so no default branch is used. -/
noncomputable def cor34_normalizedCoordinate {n : ℕ} (ε : ℝ) (p : Fin n → ℝ)
    (x : Fin n → ℤ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n),
    cor34_normalizedAmplitude ε p σ * BetheAnsatz.planeWave p σ x

/-- The regularized coordinate wave is continuous in `(ε,p)`. -/
theorem cor34_normalizedCoordinate_tendsto {n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (x : Fin n → ℤ) :
    Tendsto (fun ε => cor34_normalizedCoordinate ε (p ε) x) (𝓝 0)
      (𝓝 (cor34_normalizedCoordinate 0 (p 0) x)) := by
  have hsum : Continuous (fun q : ℝ × (Fin n → ℝ) =>
      ∑ σ : Equiv.Perm (Fin n),
        cor34_normalizedAmplitude q.1 q.2 σ * BetheAnsatz.planeWave q.2 σ x) := by
    refine continuous_finsetSum Finset.univ fun σ _ => ?_
    unfold cor34_normalizedAmplitude
    exact (continuous_const.mul <| continuous_finsetProd Finset.univ fun k _ =>
      continuous_finsetProd (Finset.Ioi k) fun l _ => by
        dsimp [cor34_amplitudeFactor, BetheAnsatz.z]; fun_prop).mul
      (by dsimp [BetheAnsatz.planeWave, BetheAnsatz.z]; fun_prop)
  simpa only [Function.comp_def, cor34_normalizedCoordinate, id_eq] using
    hsum.continuousAt.tendsto.comp (continuousAt_id.tendsto.prodMk_nhds hp)

/-- Away from `ε=0`, the regularized coordinate is exactly the source coordinate wave multiplied
by `(-ε/2)^(n(n-1)/2)`. -/
theorem cor34_normalizedCoordinate_eq_scaled_coordinateWave {n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) (x : Fin n → ℤ) (hε : ε ≠ 0) :
    cor34_normalizedCoordinate ε p x =
      (((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n) *
        BetheAnsatz.coordinateWave (1 / ε) p x := by
  unfold cor34_normalizedCoordinate BetheAnsatz.coordinateWave
  simp_rw [cor34_normalizedAmplitude_eq_scaled_amplitude ε p _ hε, mul_assoc, ← Finset.mul_sum]

/-- The zero-based state corresponding to the paper's one-based sites `(2,4,...,2n)`. -/
noncomputable def cor34_evenCoordinateState {N n : ℕ} (hN : 2 * n ≤ N) : State N n := by
  let f : Fin n → Fin N := fun k => ⟨2 * k.val + 1, by omega⟩
  refine ⟨Finset.univ.image f, ?_⟩
  rw [Finset.card_image_of_injective _ fun i j hij =>
    Fin.ext (by have := congrArg Fin.val hij; dsimp [f] at this; omega)]
  simp

/-- The state sites are exactly the zero-based indices one less than the source's even tuple. -/
theorem cor34_evenCoordinateState_mem {N n : ℕ} (hN : 2 * n ≤ N) (k : Fin n) :
    (⟨2 * k.val + 1, by omega⟩ : Fin N) ∈ (cor34_evenCoordinateState hN).1 := by
  simp [cor34_evenCoordinateState]

/-- The increasing zero-based positions in this state are `1,3,...,2n-1`; these encode the
one-based source sites `2,4,...,2n`. -/
theorem cor34_evenCoordinateState_positions {N n : ℕ} (hN : 2 * n ≤ N) :
    BetheAnsatz.positions (cor34_evenCoordinateState hN) =
      fun k => ((2 * k.val + 1 : ℕ) : ℤ) := by
  classical
  let x := cor34_evenCoordinateState hN
  let f : Fin n → Fin N := fun k => ⟨2 * k.val + 1, by omega⟩
  have horder : f = x.1.orderEmbOfFin x.2 :=
    Finset.orderEmbOfFin_unique x.2 (fun k => cor34_evenCoordinateState_mem hN k)
      fun i j hij => by change 2 * i.val + 1 < 2 * j.val + 1; omega
  funext k
  change ((x.1.orderEmbOfFin x.2 k).val : ℤ) = ((2 * k.val + 1 : ℕ) : ℤ)
  rw [← horder]

end PottsDiscontinuity.SixVertex
