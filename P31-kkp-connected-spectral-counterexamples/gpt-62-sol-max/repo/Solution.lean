module
public import KKP.Bridge
public import BN.Definition
@[expose] public section

/-! # The connected counterexample family and its exact positive spectral gap -/

namespace KKP
open SimpleGraph Matrix

/-- A lower Rayleigh bound on an injective image of dimension `k+1`
is a lower bound on the eigenvalue of index `k`. -/
private lemma eigenvalue_lower {n : Type*} [Fintype n] [DecidableEq n]
    {k : ℕ} (hk : k < Fintype.card n) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {W : Matrix n (Fin (k + 1)) ℝ} {t : ℝ} (hW : (Wᵀ * W).PosDef)
    (hR : ∀ x, t * (x ⬝ᵥ (Wᵀ * W) *ᵥ x) ≤ x ⬝ᵥ (Wᵀ * A * W) *ᵥ x) :
    t ≤ hA.eigenvalues₀ ⟨k, hk⟩ := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let D := diagonal hA.eigenvalues
  let P := Uᵀ * W
  have hU : U * Uᵀ = 1 := Unitary.coe_mul_star_self _
  have hd : A = U * D * Uᵀ := hA.spectral_theorem
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  -- An image vector can be chosen with its first `k` eigen-coordinates zero.
  let L := (LinearMap.pi fun i : Fin k => LinearMap.proj (e (i.castLE hk.le))).comp P.mulVecLin
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) (by simp))
  let y := P *ᵥ x
  let r := hA.eigenvalues₀ ⟨k, hk⟩
  have hb : y ⬝ᵥ D *ᵥ y ≤ r * (y ⬝ᵥ y) := by
    simp only [D, mulVec_diagonal, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : k ≤ (e.symm i).val
    · have : hA.eigenvalues i ≤ r := hA.eigenvalues₀_antitone hi
      nlinarith [sq_nonneg (y i)]
    · have hz : y i = 0 := by
        simpa [L, y] using congrFun (LinearMap.mem_ker.mp hx) ⟨(e.symm i).val, Nat.lt_of_not_ge hi⟩
      simp [hz]
  have cert (B : Matrix n n ℝ) : y ⬝ᵥ B *ᵥ y = x ⬝ᵥ (Wᵀ * (U * B * Uᵀ) * W) *ᵥ x := by
    rw [dotProduct_comm, ← dotProduct_transpose_mulVec]
    simp [y, P, mulVec_mulVec, transpose_mul, Matrix.mul_assoc]
  have hy := by simpa [hU] using cert 1
  rw [hy, cert D, ← hd] at hb
  exact le_of_mul_le_mul_right ((hR x).trans hb) (by simpa using hW.dotProduct_mulVec_pos hx0)

local notation "edgeCount " s:arg => Finset.card (SimpleGraph.edgeFinset (bridgeGraph s))
local notation "spectralMass " s:arg => BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2
local notation "spectralBound " s:arg => (4 / 3 : ℝ) * (edgeCount s : ℝ)

/-- The complete graph, forbidden-subgraph, and ordered-spectrum certificate. -/
theorem connected_counterexample_family (s : ℕ) (hs : 3 ≤ s) :
    forbiddenGraph.chromaticNumber = 4 ∧
      (∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
        (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber) ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      edgeCount s = 3 * s ^ 2 + 7 ∧
      (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
          (3 * (37 * (s : ℝ) - 1) ^ 2) ≤
        spectralMass s - spectralBound s ∧
      spectralBound s < spectralMass s := by
  have hc : forbiddenGraph.chromaticNumber = 4 := by
    refine (Colorable.chromaticNumber_le (n := 4) ⟨.mk ![0, 1, 2, 3, 3] (by decide +kernel)⟩).antisymm ?_
    apply le_chromaticNumber_of_pairwise_adj (by simp) Fin.castSucc
    unfold Pairwise
    decide +kernel
  obtain ⟨he, hG, hC, hZ, hAZ⟩ := witness_forms (s := s) (by omega)
  refine ⟨hc, ⟨0, 1, by decide, ?_⟩, bridgeGraph_connected (by omega), bridgeGraph_free s, he, ?_⟩
  · rw [hc]
    exact (Colorable.chromaticNumber_le (n := 3) ⟨.mk ![0, 0, 1, 2, 2] (by decide +kernel)⟩).trans_lt (by decide)
  have hx : (3 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast [he]
  generalize (s : ℝ) = x at hx hG hC hZ hAZ ⊢
  have hd : 0 < 37 * x - 1 := by linarith
  -- Rational lower bounds from the peak vector and the two-dimensional test space.
  let a := (24 * x ^ 4 + 4 * x) / (12 * x ^ 3 + 1)
  let b := (114 * x - 9) / (37 * x - 1)
  have hsA := (bridgeGraph s).isHermitian_adjMatrix ℝ
  have ha : a ≤ BN.lambda1 (bridgeGraph s) := eigenvalue_lower Fintype.card_pos hsA (W := peakWitness s)
    (hZ.symm ▸ .diagonal fun _ => by positivity) (by
    intro u
    simp [hZ, hAZ, mulVec, dotProduct, a]
    field_simp
    nlinarith)
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hd.le
  have hb1 : b ≤ 2 * x - 1 := (div_le_iff₀ hd).2 (by nlinarith)
  have hbd : (37 * x - 1) * b = 114 * x - 9 := mul_div_cancel₀ _ hd.ne'
  have hb : b ≤ BN.lambda2 (bridgeGraph s) := eigenvalue_lower Fintype.one_lt_card hsA (W := witnesses s)
    (hG.symm ▸ .diagonal (by intro i; fin_cases i <;> simp <;> positivity)) (by
    intro u
    simp [hG, hC, mulVec, dotProduct, Fin.sum_univ_two]
    -- The shift makes the second diagonal equal the mixed entry, so complete the square.
    linear_combination 3 * x * sq_nonneg (u 0 + u 1) + 3 * x * (u 0) ^ 2 * hb1 + x * (u 1) ^ 2 * hbd)
  refine (and_iff_left_of_imp fun h => sub_pos.mp ((div_pos (by nlinarith) (by positivity)).trans_le h)).2 ?_
  rw [le_sub_iff_add_le]
  calc
    _ ≤ a^2 + b^2 := by
      dsimp [a, b]
      field_simp (disch := first | positivity | linarith)
      -- Expansion about x = 3 leaves only nonnegative coefficients.
      obtain ⟨y, hy, rfl⟩ := exists_nonneg_add_of_le hx
      apply sub_nonneg.mp
      ring_nf
      positivity
    _ ≤ _ := by gcongr

/-- Connected counterexamples exist above any given edge threshold. -/
theorem unbounded_connected_counterexamples (B : ℕ) :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ edgeCount s ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      spectralBound s < spectralMass s := by
  obtain ⟨_, _, hc, hf, he, _, hx⟩ := connected_counterexample_family (B + 3) (by omega)
  exact ⟨B + 3, by omega, by rw [he]; nlinarith, hc, hf, hx⟩
end KKP
