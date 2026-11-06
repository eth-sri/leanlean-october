module
public import KKP.Witness
public import KKP.Compression
public import KKP.Certificate
@[expose] public section

/-! # The normalized witness plane and its positive compression -/

namespace KKP
open Matrix

/-- Normalize a nonzero coordinate vector by the square root of its squared norm. -/
noncomputable def normalizeVector {n : Type*} [Fintype n] (u : n → ℝ) : n → ℝ :=
  (Real.sqrt (u ⬝ᵥ u))⁻¹ • u

lemma normalizeVector_norm {n : Type*} [Fintype n] (u : n → ℝ) (hu : 0 < u ⬝ᵥ u) :
    normalizeVector u ⬝ᵥ normalizeVector u = 1 := by
  simp only [normalizeVector, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hu.le,
    inv_mul_cancel₀ (ne_of_gt hu)]

/-- The two columns are the actual normalized integer vectors on the graph. -/
noncomputable def witnessPlane (s : ℕ) : Matrix (BridgeVertex s) (Fin 2) ℝ :=
  fun v i => if i = 0 then normalizeVector (witnessU s) v else normalizeVector (witnessV s) v

lemma witness_norm_pos (s : ℕ) (hs : 3 ≤ s) :
    0 < witnessU s ⬝ᵥ witnessU s ∧ 0 < witnessV s ⬝ᵥ witnessV s := by
  have hs0 : 0 < s := by omega
  have hr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  rw [witnessU_norm, witnessV_norm s hs0]
  exact ⟨by positivity,
    mul_pos (by exact_mod_cast hs0) (CounterexampleCertificate.denominator_pos _ hr)⟩

lemma normalizeVector_bilinear {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (u v : n → ℝ) :
    normalizeVector u ⬝ᵥ A *ᵥ normalizeVector v =
      (u ⬝ᵥ A *ᵥ v) / (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) := by
  simp only [normalizeVector, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    div_eq_mul_inv, _root_.mul_inv_rev]
  ring

lemma normalizeVector_quadratic {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (u : n → ℝ) (hu : 0 ≤ u ⬝ᵥ u) :
    normalizeVector u ⬝ᵥ A *ᵥ normalizeVector u = (u ⬝ᵥ A *ᵥ u) / (u ⬝ᵥ u) := by
  rw [normalizeVector_bilinear, ← pow_two, Real.sq_sqrt hu]

/-- The off-diagonal entry obtained directly from the normalized integer witnesses. -/
noncomputable def compressionOffDiagonal (s : ℕ) : ℝ :=
  3 * (s : ℝ) / (Real.sqrt (3 * (s : ℝ)) * Real.sqrt ((s : ℝ) * (37 * (s : ℝ) - 1)))

/-- Exact entries of the compression of the actual adjacency matrix. -/
theorem witnessPlane_compression (s : ℕ) (hs : 3 ≤ s) :
    (witnessPlane s)ᵀ * (bridgeGraph s).adjMatrix ℝ * witnessPlane s =
      !![2 * (s : ℝ), compressionOffDiagonal s;
         compressionOffDiagonal s, (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)] := by
  have hs0 : 0 < s := by omega
  have hu := (witness_norm_pos s hs).1.le
  have hv := (witness_norm_pos s hs).2.le
  have hsym : (bridgeGraph s).adjMatrix ℝ = ((bridgeGraph s).adjMatrix ℝ)ᵀ :=
    (bridgeGraph s).transpose_adjMatrix |>.symm
  ext i j
  rw [Matrix.mul_assoc]
  fin_cases i <;> fin_cases j
  · change normalizeVector (witnessU s) ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ
        normalizeVector (witnessU s) = 2 * (s : ℝ)
    rw [normalizeVector_quadratic _ _ hu, witnessU_quadratic s hs0, witnessU_norm]
    field_simp
    all_goals ring
  · change normalizeVector (witnessU s) ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ
        normalizeVector (witnessV s) = compressionOffDiagonal s
    rw [normalizeVector_bilinear, witnesses_mixed s hs0, witnessU_norm, witnessV_norm s hs0]
    rfl
  · change normalizeVector (witnessV s) ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ
        normalizeVector (witnessU s) = compressionOffDiagonal s
    rw [dotProduct_mulVec, ← mulVec_transpose, ← hsym, dotProduct_comm]
    rw [normalizeVector_bilinear, witnesses_mixed s hs0, witnessU_norm, witnessV_norm s hs0]
    rfl
  · change normalizeVector (witnessV s) ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ
        normalizeVector (witnessV s) = (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)
    rw [normalizeVector_quadratic _ _ hv, witnessV_quadratic s hs0, witnessV_norm s hs0]
    field_simp

/-- The square of the off-diagonal compression entry has the displayed rational value. -/
theorem compressionOffDiagonal_sq (s : ℕ) (hs : 3 ≤ s) :
    compressionOffDiagonal s ^ 2 = 3 / (37 * (s : ℝ) - 1) := by
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hd := CounterexampleCertificate.denominator_pos (s : ℝ) hr
  have hu : 0 ≤ 3 * (s : ℝ) := by positivity
  have hv : 0 ≤ (s : ℝ) * (37 * (s : ℝ) - 1) := mul_nonneg hs0.le hd.le
  simp only [compressionOffDiagonal, div_pow, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hv]
  field_simp [ne_of_gt hs0, ne_of_gt hd]

/-- The exact excess bound from the manuscript, for every integer class size at least three. -/
theorem bridgeGraph_spectral_gap (s : ℕ) (hs : 3 ≤ s) :
    (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
        (3 * (37 * (s : ℝ) - 1) ^ 2) ≤
      BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 -
        (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) := by
  have hr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hQ : (witnessPlane s)ᵀ * witnessPlane s = 1 := by
    obtain ⟨hu, hv⟩ := witness_norm_pos s hs
    have huv : normalizeVector (witnessU s) ⬝ᵥ normalizeVector (witnessV s) = 0 := by
      simp [normalizeVector, smul_dotProduct, dotProduct_smul, witnesses_orthogonal s (by omega)]
    ext i j
    fin_cases i <;> fin_cases j <;> change _ ⬝ᵥ _ = _ <;>
      simp [witnessPlane, normalizeVector_norm _ hu, normalizeVector_norm _ hv, huv, dotProduct_comm]
  have hP : ((witnessPlane s)ᵀ * (bridgeGraph s).adjMatrix ℝ * witnessPlane s).PosSemidef := by
    have hd := CounterexampleCertificate.compression_determinant_pos (s : ℝ) hr
    rw [witnessPlane_compression s hs]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
    · intro x
      have h₁ := sq_nonneg (2 * (s : ℝ) * x 0 + compressionOffDiagonal s * x 1)
      have hdet : 0 ≤ 2 * (s : ℝ) * ((114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) -
          compressionOffDiagonal s ^ 2 := by
        rw [compressionOffDiagonal_sq s hs]
        exact hd.le
      have h₂ := mul_nonneg hdet (sq_nonneg (x 1))
      have hs' : 0 < (s : ℝ) := by linarith
      simp [dotProduct, mulVec, Fin.sum_univ_two]
      nlinarith
  have h := positive_compression_le ((bridgeGraph s).adjMatrix ℝ)
    ((bridgeGraph s).isHermitian_adjMatrix ℝ) (witnessPlane s) hQ hP
  rw [witnessPlane_compression s hs, BN.inner_self] at h
  norm_num [Fin.sum_univ_two] at h
  rw [compressionOffDiagonal_sq s hs] at h
  have h' : 4 * (s : ℝ) ^ 2 + ((114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) ^ 2 +
      6 / (37 * (s : ℝ) - 1) ≤
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
    convert h using 1 <;> first | rfl | ring
  rw [bridgeGraph_edge_count s (by omega)]
  push_cast
  have hid := CounterexampleCertificate.compression_gap_identity (s : ℝ)
    (ne_of_gt (CounterexampleCertificate.denominator_pos _ hr))
  linarith

/-- The actual graph violates the exact `4m/3` inequality. -/
theorem bridgeGraph_spectral_excess (s : ℕ) (hs : 3 ≤ s) :
    (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
      BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  have hr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hn := CounterexampleCertificate.excess_numerator_pos (s : ℝ) hr
  have hd := CounterexampleCertificate.denominator_pos (s : ℝ) hr
  have hpos : 0 < (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
      (3 * (37 * (s : ℝ) - 1) ^ 2) := div_pos hn (by positivity)
  have hgap := bridgeGraph_spectral_gap s hs
  linarith

/-- Connected forbidden-free counterexamples occur above every prescribed edge threshold. -/
theorem unbounded_connected_counterexamples (B : ℕ) :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ (bridgeGraph s).edgeFinset.card ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  refine ⟨B + 3, by omega, ?_, bridgeGraph_connected _ (by omega), bridgeGraph_free _,
    bridgeGraph_spectral_excess _ (by omega)⟩
  rw [bridgeGraph_edge_count _ (by omega)]
  nlinarith

end KKP
