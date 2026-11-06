module
public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

namespace BN
noncomputable section
variable {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def adjacencyEigenvalues := (G.isHermitian_adjMatrix ℝ).eigenvalues
def adjacencyEigenvalues₀ := (G.isHermitian_adjMatrix ℝ).eigenvalues₀
def lambda1 [Nonempty V] := adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩
def lambda2 [Nontrivial V] := adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
end
end BN

namespace KKP
variable (s : ℕ)
abbrev BridgeVertex := (Fin 3 × Fin s) ⊕ Fin 4
def bridgeAdj : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
def bridgeGraph : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun
    | .inl (_, _), .inl (_, _) | .inr _, .inr _ => (·.symm)
    | .inl (_, _), .inr _ | .inr _, .inl (_, _) => fun h => h⟩
  loopless := ⟨fun | .inl (_, _) | .inr _ => (· rfl)⟩
instance bridgeAdjDecidable : DecidableRel (bridgeGraph s).Adj
  | .inl (_, _), .inl (_, _) | .inr _, .inr _ => inferInstanceAs (Decidable (_ ≠ _))
  | .inl (_, _), .inr _ | .inr _, .inl (_, _) => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

open SimpleGraph Matrix Module WithLp Finset
open scoped InnerProductSpace

attribute [local simp] mulVec dotProduct Fintype.sum_sum_type Fintype.sum_prod_type
  adjMatrix bridgeGraph bridgeAdj Fin.sum_univ_three Fin.sum_univ_four
  sub_mul mul_sub ite_and

theorem connected_counterexample_family (hs : 3 ≤ s) :
    forbiddenGraph.chromaticNumber = 4 ∧
      (∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
        (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber) ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 ∧
      (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
          (3 * (37 * (s : ℝ) - 1) ^ 2) ≤
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 -
          (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  have : NeZero s := ⟨by omega⟩
  have hr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hchr : forbiddenGraph.chromaticNumber = 4 :=
    le_antisymm (Colorable.chromaticNumber_le
      ⟨.mk (.predAbove (3 : Fin 4)) (by decide)⟩)
      (le_chromaticNumber_of_pairwise_adj (by simp)
        Fin.castSucc (by unfold Pairwise; decide))
  have hconn : (bridgeGraph s).Connected := by
    refine (connected_iff_exists_forall_reachable _).mpr ⟨.inr 0, ?_⟩
    have adj {u v} (h : (bridgeGraph s).Adj u v := by simp) := h.reachable
    rintro (⟨i, b⟩ | b)
    · refine (adj (v := .inl (0, 0))).trans ?_
      obtain rfl | hi := eq_or_ne i 0
      · exact (adj (v := .inl (1, 0))).trans adj
      · exact adj hi.symm
    · obtain rfl | hb := eq_or_ne b 0
      · rfl
      · exact adj hb.symm
  have hfree : forbiddenGraph.Free (bridgeGraph s) := by
    rintro ⟨f, hf⟩
    have e (i j) (h : forbiddenGraph.Adj i j := by decide) := f.map_rel h
    have := e 0 1; have := e 0 2; have := e 1 2
    have := e 0 3; have := e 1 3; have := e 2 3
    have := e 0 4; have := e 1 4; have := e 2 4
    have : f 3 ≠ f 4 := hf.ne (by decide)
    revert f; intro f _ _
    rcases f 0 with ⟨⟩ | _ <;> rcases f 1 with ⟨⟩ | _ <;>
      rcases f 2 with ⟨⟩ | _ <;> rcases f 3 with ⟨⟩ | _ <;>
      rcases f 4 with ⟨⟩ | _ <;>
      simp only [bridgeGraph, bridgeAdj, Sum.inr.injEq, ne_eq, Fin.ext_iff] <;> omega
  have hedge : (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 := by
    have := (bridgeGraph s).sum_degrees_eq_twice_card_edges
    simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter] at this
    simp [sum_add_distrib, sq] at this ⊢; omega
  let u : BridgeVertex s → ℝ := fun | .inl _ => 1 | .inr _ => 0
  let v : BridgeVertex s → ℝ := fun
    | .inl (i, a) => if i = 0 then (if a.val = 0 then s else 0) - 1 else 0
    | .inr _ => 3 * s
  let A := (bridgeGraph s).adjMatrix ℝ
  set d : ℝ := 37 * s - 1
  let c := 3 * s * d
  let a := 2 * s * d
  let b : ℝ := 114 * s - 6
  have hd : 0 < d := by linarith
  have hb_pos : 0 < b := by linarith
  have huv : v ⬝ᵥ u = 0 := by simp [u, v]
  have hu : u ⬝ᵥ u = 3 * s := by simp [u]
  have hv : v ⬝ᵥ v = s * d := by simp [v]; ring
  let hA := (bridgeGraph s).isHermitian_adjMatrix ℝ
  let hT := isSymmetric_toEuclideanLin_iff.mpr hA
  let eb := hT.eigenvectorBasis finrank_euclideanSpace
  set x := fun i => ⟪eb i, toLp 2 u⟫_ℝ
  set y := fun i => ⟪eb i, toLp 2 v⟫_ℝ
  dsimp only [BN.lambda1, BN.lambda2, BN.adjacencyEigenvalues₀]
  set lam := hA.eigenvalues₀
  set i0 : Fin (Fintype.card (BridgeVertex s)) := ⟨0, Fintype.card_pos⟩
  have hsum (w₁ w₂ : _ → ℝ) : ∑ i, ⟪eb i, toLp 2 w₁⟫_ℝ * ⟪eb i, toLp 2 w₂⟫_ℝ = w₂ ⬝ᵥ w₁ := by
    simpa [real_inner_comm (toLp 2 w₁), EuclideanSpace.inner_toLp_toLp] using
      eb.sum_inner_mul_inner (toLp 2 w₁) (toLp 2 w₂)
  have hquad (w₁ w₂ : _ → ℝ) : ∑ i, lam i * ⟪eb i, toLp 2 w₁⟫_ℝ * ⟪eb i, toLp 2 w₂⟫_ℝ = w₂ ⬝ᵥ A *ᵥ w₁ := by
    rw [← hsum]; refine sum_congr rfl fun i _ => ?_
    erw [← hT (eb i), hT.apply_eigenvectorBasis, real_inner_smul_left]; rfl
  set l0 := lam i0
  set l1 := lam ⟨1, Fintype.one_lt_card⟩
  have hlam : Antitone lam := hA.eigenvalues₀_antitone
  have hlam01 : 0 ≤ l0 - l1 := sub_nonneg.mpr (hlam (Fin.zero_le _))
  let p := d * x i0 ^ 2
  let q := 3 * y i0 ^ 2
  let S := a ^ 2 + b ^ 2 + 6 * d
  let W := fun i => x i * x i * (a * d) + y i * y i * (3 * b) + x i * y i * (6 * d)
  let P := c * (a + b)
  let Q := 2 * W i0 - (a + b) * (p + q)
  let M := P * (l0 + l1) + Q * (l0 - l1) - 6 * s * S
  have hsumW : ∑ i, W i = P := by
    simp only [W, sum_add_distrib, ← sum_mul, x, y, hsum, hu, hv, huv]; ring
  have hquadW : ∑ i, lam i * W i = 3 * s * S := by
    simp only [W, mul_add, ← mul_assoc, sum_add_distrib, ← sum_mul, x, y, hquad]
    simp [u, v, A]; ring
  have hb0 : 0 ≤ c - p - q := by
    have hz := real_inner_self_nonneg
      (x := c • eb i0 - (d * x i0) • toLp 2 u - (3 * y i0) • toLp 2 v)
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (eb i0), EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm u v,
      eb.inner_eq_one, hu, hv, huv] at hz
    refine nonneg_of_mul_nonneg_right ?_ (show 0 < c by positivity)
    linarith
  have hdet' : 0 ≤ 2 * s * b - 3 := by nlinarith
  have hW_nonneg (i) : 0 ≤ W i := by
    refine nonneg_of_mul_nonneg_right ((show 0 ≤ d * ((a * x i + 3 * y i) ^ 2 +
      3 * (2 * s * b - 3) * y i ^ 2) by positivity).trans_eq ?_) (show 0 < a by positivity)
    ring
  have hsum_ineq : 3 * s * S ≤ l1 * P + (l0 - l1) * W i0 := by
    simpa only [← mul_sum, sum_add_distrib, sum_ite_eq', mem_univ, ite_true, hsumW, hquadW] using
      sum_le_sum (s := univ) fun i _ =>
        show lam i * W i ≤ l1 * W i + if i = i0 then (l0 - l1) * W i0 else 0 by
          split_ifs with hi
          · subst i; linarith
          · simpa using mul_le_mul_of_nonneg_right
              (hlam (Nat.pos_of_ne_zero (Fin.val_ne_of_ne hi))) (hW_nonneg i)
  clear_value x y l0 l1 i0
  clear hsumW hquadW huv hu hv
  have hM1 : 0 ≤ M := by
    have : 0 ≤ (l0 - l1) * (a + b) * (c - p - q) := by positivity
    linarith
  have hS_le : 0 ≤ d ^ 2 * (l0 ^ 2 + l1 ^ 2) - S := by
    refine nonneg_of_mul_nonneg_right ((show 0 ≤
      2 * (((a - b) ^ 2 + 12 * d) * (c - p - q) * (c + p + q) +
        12 * d * ((a - b) * x i0 * y i0 - p + q) ^ 2) * (l0 ^ 2 + l1 ^ 2) +
      (P * (l1 - l0) + Q * (l0 + l1)) ^ 2 + M * (M + 12 * s * S) by positivity).trans_eq ?_)
      (show 0 < 36 * s ^ 2 * S by positivity)
    ring
  refine ⟨hchr, ⟨0, 1, by decide, hchr.symm ▸ lt_of_le_of_lt (Colorable.chromaticNumber_le
    ⟨.mk (.predAbove (0 : Fin 3) ∘ .predAbove 3) (by decide)⟩) (by decide)⟩,
    hconn, hfree, hedge, (fun hgap => ⟨hgap, ?_⟩) ?_⟩
  · rw [hedge, div_le_iff₀ (by positivity)]
    push_cast
    linarith
  · have : 0 < (656 * s ^ 2 - 1366 * s + 62) / (3 * d ^ 2) := div_pos (by nlinarith) (by positivity)
    linarith

theorem unbounded_connected_counterexamples (B : ℕ) :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ (bridgeGraph s).edgeFinset.card ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  obtain ⟨_, _, hconn, hfree, hedge, _, hexcess⟩ :=
    connected_counterexample_family (B + 3) (by omega)
  exact ⟨B + 3, by omega, by rw [hedge]; nlinarith, hconn, hfree, hexcess⟩

end KKP
