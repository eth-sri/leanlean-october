module

public import PottsDiscontinuity.BetheAnsatz.GapTransfer
public import PottsDiscontinuity.BetheAnsatz.NonconstantWords
public import PottsDiscontinuity.Bethe.RatioProducts

/-! The finite gap sum admits a spectral deformation with *fixed* Bethe
momenta. The shifted phases alone would change the scattering law. Choosing
the interior and upper endpoint weights together leaves the ML exchange
law unchanged, so all nonconstant words cancel even along the deformation. -/

@[expose] public section

namespace PottsDiscontinuity.BetheAnsatz
open Finset Complex Matrix Classical Filter Topology

lemma z_add (x y : ℝ) : z (x+y) = z x * z y := by
  simp [z, mul_add, exp_add]

lemma z_sub (x y : ℝ) : z (x-y) = z x / z y := by
  simp [z, mul_sub, exp_sub]

lemma z_neg (s : ℝ) : z (-s) = (z s)⁻¹ := by simpa using z_sub 0 s

lemma z_mul_nat (n : ℕ) (x : ℝ) : z ((n:ℝ)*x) = z x ^ n := by
  unfold z
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

noncomputable def spectralInterior (Δ s : ℝ) : ℂ := 1 + z s ^ 2 - 2 * (Δ:ℂ) * z s

noncomputable def spectralLeft (Δ s x : ℝ) : ℂ :=
  gapLeft (spectralInterior Δ s) (z (x-s))

noncomputable def spectralRight (Δ s x : ℝ) : ℂ :=
  gapRight (z s ^ 2) (spectralInterior Δ s) (z (x-s))

@[simp] lemma spectralInterior_zero (c : ℝ) : spectralInterior (anisotropy c) 0 = (c:ℂ)^2 := by
  simp [spectralInterior, anisotropy]
  ring

@[simp] lemma spectralLeft_zero (c x : ℝ) : spectralLeft (anisotropy c) 0 x = L c (z x) := by
  simp [spectralLeft, gapLeft, L]

@[simp] lemma spectralRight_zero (c x : ℝ) : spectralRight (anisotropy c) 0 x = M c (z x) := by
  simp [spectralRight, gapRight, M]

private lemma spectralML (Δ s x y : ℝ) (hx : z (x-s) ≠ 1) (hy : z (y-s) ≠ 1) :
    spectralRight Δ s x * spectralLeft Δ s y - z s ^ 2 =
      -spectralInterior Δ s * (z y * scattering Δ y x) / ((1-z (x-s))*(1-z (y-s))) := by
  rw [z_mul_scattering, show z x = z s * z (x-s) by rw [← z_add]; simp,
    show z y = z s * z (y-s) by rw [← z_add]; simp]
  unfold spectralLeft spectralRight spectralInterior gapLeft gapRight
  field_simp [sub_ne_zero.mpr hx.symm, sub_ne_zero.mpr hy.symm]
  ring

private lemma spectralCompatible {n : ℕ} {Δ : ℝ} (hΔ : Δ < -1) (s : ℝ)
    (p : Fin (n+1) → ℝ) (hp : ∀ j, z (p j-s) ≠ 1) :
    (gapWordWeights (z s ^ 2) (spectralInterior Δ s) (fun j => p j-s)).Compatible Δ p := by
  intro i j
  change _ * (spectralRight Δ s (p j) * spectralLeft Δ s (p i) - z s ^ 2) =
    spectralRight Δ s (p i) * spectralLeft Δ s (p j) - z s ^ 2
  rw [spectralML Δ s (p i) (p j) (hp i) (hp j), spectralML Δ s (p j) (p i) (hp j) (hp i),
    exp_I_theta_eq_scattering hΔ]
  field_simp [z_ne_zero, scattering_ne_zero hΔ, sub_ne_zero.mpr (hp i).symm, sub_ne_zero.mpr (hp j).symm]

/-- A common shift of momenta multiplies each plane wave by this factor,
independent of the order of the momenta. -/
noncomputable def waveShift {n : ℕ} (s : ℝ) (x : Fin n → ℤ) : ℂ :=
  Complex.exp (I * (-(s:ℂ)) * ((∑ k, x k : ℤ) : ℂ))

private lemma planeWave_shift {n : ℕ} (s : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℤ) :
    planeWave (fun j => p j-s) σ x = waveShift s x * planeWave p σ x := by
  unfold waveShift planeWave
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Complex.exp_add]
  congr 1
  ring

private lemma waveShift_predecessors {N n : ℕ} (s : ℝ) (x : Fin (n+1) → ℤ) :
    waveShift s (cyclicPredecessorPositions N x) = z s ^ N * waveShift s x := by
  have he : (∑ k, cyclicPredecessorPositions N x k) = (∑ k, x k) - N := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [cyclicPredecessorPositions_zero, cyclicPredecessorPositions_succ]
    ring
  unfold waveShift
  rw [he, ← z_mul_nat, z, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma wordPositions_false {N n : ℕ} (x : Fin (n+1) → ℤ) :
    wordPositions N x (fun _ => false) = x := rfl
private lemma wordPositions_true {N n : ℕ} (x : Fin (n+1) → ℤ) :
    wordPositions N x (fun _ => true) = cyclicPredecessorPositions N x := rfl

private lemma sum_wordTerm_false {N n : ℕ} (c : ℝ) (r : WordWeights n) (x : Fin (n+1) → ℤ)
    (p : Fin (n+1) → ℝ) :
    (∑ σ, wordTerm (N := N) c r x p σ (fun _ => false)) =
      (∏ j, r.right j) * coordinateWave (anisotropy c) p x := by
  simp only [wordTerm, wordCoefficient, wordEdgeFactor, Bool.false_eq_true, ite_false,
    wordPhase, wordPositions_false, coordinateWave, Finset.mul_sum, Equiv.prod_comp]
  exact Finset.sum_congr rfl fun σ _ => by ring

private lemma sum_wordTerm_true {N n : ℕ} {c : ℝ} (hc : 2 < c) (r : WordWeights n)
    (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ) (hBE : BetheEquations N (anisotropy c) p) :
    (∑ σ, wordTerm (N := N) c r x p σ (fun _ => true)) =
      (∏ j, r.left j) * coordinateWave (anisotropy c) p x := by
  rw [coordinateWave_cyclicPredecessor (anisotropy_lt_neg_one hc) p hBE x]
  simp only [wordTerm, wordCoefficient, wordEdgeFactor, ite_true, wordPhase, wordPositions_true,
    coordinateWave, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have h := Equiv.prod_comp (σ * finRotate (n+1)) r.left
  simp only [Equiv.Perm.mul_apply] at h
  rw [h]
  ring

noncomputable def spectralGapSum {N n : ℕ} (c s : ℝ) (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ) : ℂ :=
  ∑ σ, amplitude (anisotropy c) p σ * weightedGapSum (N := N)
     (z s ^ 2) (spectralInterior (anisotropy c) s) x (fun j => p j-s) σ

noncomputable def spectralEigenvalue {n : ℕ} (N : ℕ) (c s : ℝ) (p : Fin n → ℝ) : ℂ :=
  z s ^ N * (∏ j, spectralLeft (anisotropy c) s (p j)) + (∏ j, spectralRight (anisotropy c) s (p j))

/-- The deformed eigenvalue comes from just the two constant words. -/
theorem spectralGapSum_eq {N n : ℕ} {c : ℝ} (hc : 2 < c) (s : ℝ)
    (x : Fin (n+2) → ℤ) (hx : StrictMono x) (hspan : x (Fin.last (n+1)) - x 0 < (N:ℤ))
    (p : Fin (n+2) → ℝ) (hp : ∀ j, z (p j-s) ≠ 1) (hBE : BetheEquations N (anisotropy c) p) :
    spectralGapSum (N := N) c s x p =
      spectralEigenvalue N c s p * (waveShift s x * coordinateWave (anisotropy c) p x) := by
  let r := gapWordWeights (z s ^ 2) (spectralInterior (anisotropy c) s) (fun j => p j-s)
  have hr := spectralCompatible (anisotropy_lt_neg_one hc) s p hp
  have hsum : spectralGapSum (N := N) c s x p = ∑ w, waveShift s (wordPositions N x w) *
      ∑ σ, wordTerm (N := N) c r x p σ w := by
    unfold spectralGapSum
    simp_rw [weightedGapSum_eq_sum_words _ _ x _ _ hx hspan hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro σ _
    unfold wordTerm wordPhase
    rw [planeWave_shift]
    ring
  rw [hsum, ← Finset.sum_subset (show ({(fun _ => true), (fun _ => false)} :
    Finset (Fin (n+2) → Bool)) ⊆ univ by simp)]
  · rw [Finset.sum_pair (by intro he; have := congrFun he 0; contradiction),
      sum_wordTerm_true hc r x p hBE, sum_wordTerm_false]
    simp only [wordPositions_true, wordPositions_false, waveShift_predecessors]
    unfold spectralEigenvalue
    change _ * ((∏ j, spectralLeft (anisotropy c) s (p j)) * _) +
      _ * ((∏ j, spectralRight (anisotropy c) s (p j)) * _) = _
    ring
  · intro w _ hw
    rw [sum_wordTerm_eq_zero_of_nonconstant hc r x p hr hBE w (by aesop) (by aesop), mul_zero]

@[simp] theorem spectralGapSum_zero {N n : ℕ} (c : ℝ) (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ) :
    spectralGapSum (N := N) c 0 x p = ∑ σ, amplitude (anisotropy c) p σ * cyclicGapSum c N x p σ := by
  simp [spectralGapSum, weightedGapSum_eq_cyclicGapSum]

/-- Restrict the calculation to the particle sector, and extend by zero on
other sectors. Both branches use the same transfer-action calculation. -/
theorem betheAnsatz_of_gap {N n : ℕ} {c : ℝ} (hc : 2 < c) (p : Fin (n+2) → ℝ)
    (hBE : BetheEquations N (anisotropy c) p) {E : ℂ}
    (hgap : ∀ x : Fin (n+2) → ℤ, StrictMono x → x (Fin.last (n+1)) - x 0 < (N:ℤ) →
      spectralGapSum (N := N) c 0 x p = E * coordinateWave (anisotropy c) p x) :
    (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p =
      E • betheVector (anisotropy c) p := by
  funext x
  by_cases hs : x.card = n+2
  · let s : SixVertex.State N (n+2) := ⟨x,hs⟩
    have ht := transfer_betheVector_eq_cyclicGapSum c (anisotropy_lt_neg_one hc) p hBE s
    rw [← spectralGapSum_zero, hgap _ (positions_strictMono s) (positions_span_lt s)] at ht
    change _ = E * extendByZero (blockWave (anisotropy c) p) s.val
    rw [extendByZero_coe]
    exact ht
  · rw [complex_transfer_mulVec_supported c (n+2)
      (betheVector (anisotropy c) p) (fun y hy => betheVector_eq_zero _ _ hy) x hs]
    simp [betheVector_eq_zero _ _ hs]

/-- Regular eigenvalue: evaluate the deformed formula at spectral shift zero. -/
theorem betheAnsatz_regular {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n+2) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hp0 : ∀ j, p j ≠ 0) (hBE : BetheEquations N (anisotropy c) p) :
    (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p =
      eigenvalueRegular c p • betheVector (anisotropy c) p := by
  apply betheAnsatz_of_gap hc p hBE
  intro x hx hspan
  have hn : ∀ j, z (p j-0) ≠ 1 := fun j => by simpa using z_ne_one (hp j) (hp0 j)
  have H := spectralGapSum_eq hc 0 x hx hspan p hn hBE
  simpa [spectralEigenvalue, eigenvalueRegular, waveShift] using H

end PottsDiscontinuity.BetheAnsatz
