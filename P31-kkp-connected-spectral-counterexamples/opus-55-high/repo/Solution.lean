module
public import Mathlib
@[expose] public section

namespace BN
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def adjacencyEigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues
noncomputable def adjacencyEigenvalues₀ (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (Fintype.card V) → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues₀
noncomputable def lambda1 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩
noncomputable def lambda2 (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
end BN

namespace KKP
abbrev BridgeVertex (s : ℕ) := (Fin 3 × Fin s) ⊕ Fin 4
def bridgeAdj (s : ℕ) : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
  | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
def bridgeGraph (s : ℕ) : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun v w => match v, w with
    | .inl (_, _), .inl (_, _) => fun h => Ne.symm h
    | .inr _, .inr _ => fun h => Ne.symm h
    | .inl (_, _), .inr _ => fun h => h
    | .inr _, .inl (_, _) => fun h => h⟩
  loopless := ⟨fun v => match v with
    | .inl (_, _) => fun h => h rfl
    | .inr _ => fun h => h rfl⟩
instance bridgeAdjDecidable (s : ℕ) : DecidableRel (bridgeGraph s).Adj :=
  fun v w => match v, w with
    | .inl (i, _), .inl (j, _) => inferInstanceAs (Decidable (i ≠ j))
    | .inr a, .inr b => inferInstanceAs (Decidable (a ≠ b))
    | .inl (i, a), .inr b =>
      inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))
    | .inr b, .inl (i, a) =>
      inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun i j h => ⟨Ne.symm h.1, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩
instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)))

open scoped RealInnerProductSpace
open Matrix SimpleGraph
attribute [local simp] bridgeGraph bridgeAdj
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = N)

theorem ray (h : ∀ i < k, ⟪hT.eigenvectorBasis hn i, x⟫ = 0) :
    ⟪T x, x⟫ ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).sum_sq_inner_right, Finset.mul_sum,
    ← (hT.eigenvectorBasis hn).sum_inner_mul_inner]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hT, hT.apply_eigenvectorBasis, real_inner_smul_right, real_inner_comm, mul_assoc, ← sq]
  by_cases i < k
  simp_all
  gcongr
  apply hT.eigenvalues_antitone hn
  simp_all

theorem quad {Q N O : ℝ → ℝ → ℝ} (hc0 : 0 < c) (hc : c^2 ≤ a*d) (hd : 0 < d)
    (H1 : ∀ x z, O x z = 0 → Q x z ≤ l1 * N x z) (H0 : ∀ x z, Q x z ≤ l0 * N x z)
    (hQ : ∀ x z, Q x z = x^2*a + 2*x*z*c + z^2*d ∧ N x z = x^2+z^2) (hO : O (O 0 1) (-O 1 0) = 0) :
    a^2 + d^2 + 2*c^2 ≤ l0^2 + l1^2 := by
  simp_all only
  have : c^2 ≤ (l0-a)*(l0-d) := by nlinarith [H0 c (l0-a), H0 (l0-d) c, H0 1 1]
  have : a+d-l0 ≤ l1 := by
    by_cases hα : O 1 0 = 0
    nlinarith [H1 1 0 hα, H0 0 1]
    nlinarith [H1 (O 0 1) (-O 1 0) hO, H0 (O 1 0) (O 0 1), sq_pos_of_ne_zero hα]
  cases le_total 0 (a+d-l0) <;> nlinarith

theorem key (h1 : 1 < N) (U V : E)
    (hU : U ≠ 0) (hV : V ≠ 0) (hUV : ⟪U, V⟫ = 0) (ha : 0 < ⟪T V, V⟫) (hd : 0 < ⟪T U, V⟫)
    (hc : ⟪T U, V⟫ ^ 2 ≤ ⟪T U, U⟫ * ⟪T V, V⟫) :
    (⟪T U, U⟫ / ‖U‖ ^ 2) ^ 2 + (⟪T V, V⟫ / ‖V‖ ^ 2) ^ 2 + 2 * (⟪T U, V⟫ / ‖U‖ / ‖V‖) ^ 2 ≤
      hT.eigenvalues hn ⟨0, h1.pos⟩ ^ 2 + hT.eigenvalues hn ⟨1, h1⟩ ^ 2 := by
  refine quad ?_ (by field_simp; nlinarith) ?_
    (fun x z (hxz : ⟪hT.eigenvectorBasis hn ⟨0, h1.pos⟩, (x / ‖U‖) • U + (z / ‖V‖) • V⟫ = 0) => ray hT hn fun ⟨0, _⟩ _ => hxz)
    (fun x z => ray hT hn nofun) ?_ ?_ <;> simp_all [norm_add_sq_real, norm_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hT _ U, real_inner_comm _ V] <;> grind


set_option maxHeartbeats 2000000 in
theorem connected_counterexample_family (s : ℕ) (hs : 3 ≤ s) :
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
  obtain _ | n := s
  omega
  rify at hs
  have χ : forbiddenGraph.chromaticNumber = 4 :=
    le_antisymm (Colorable.chromaticNumber_le ⟨.mk ![0, 1, 2, 3, 3] (by decide)⟩)
      (le_chromaticNumber_of_pairwise_adj (by simp) Fin.castSucc (by unfold Pairwise; decide))
  refine ⟨χ, ⟨0, 1, by decide, χ ▸ (Colorable.chromaticNumber_le (n := 3) ⟨.mk ![0, 0, 1, 2, 2] (by decide)⟩).trans_lt (by decide)⟩, ?_, ?_, ?_⟩
  refine (connected_iff_exists_forall_reachable _).2 ⟨.inl (0, 0), ?_⟩
  rintro (⟨i, a⟩ | i) <;> fin_cases i <;> first | apply Adj.reachable; simpa | refine .trans (v := .inl (1, 0)) ?_ ?_ <;> apply Adj.reachable <;> simpa | refine .trans (v := .inr 0) ?_ ?_ <;> apply Adj.reachable <;> simp
  rintro ⟨f, hf⟩
  have := @f.map_rel
  simp_all [forbiddenGraph, Fin.forall_fin_succ]
  grind (splits := 100)
  have hm := (bridgeGraph (n+1)).two_mul_card_edgeFinset
  have := key (isSymmetric_toEuclideanLin_iff.mpr ((bridgeGraph (n+1)).isHermitian_adjMatrix ℝ))
    finrank_euclideanSpace Fintype.one_lt_card (.toLp 2 (Sum.elim 1 0))
    (.toLp 2 (Sum.elim (fun p => if p.1 = 0 then if p.2 = 0 then n else -1 else 0)
      (3 * n + 3))) ?_ ?_ ?_ ?_ ?_ ?_
  generalize (bridgeGraph _).edgeFinset.card = m at *
  all_goals simp only [Finset.card_filter, toLpLin_apply, div_pow, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct, mulVec, adjMatrix_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ] at *
  all_goals simp_all [funext_iff] <;> intros
  simp [show m = 3 * (n+1) ^ 2 + 7 by linarith]
  refine (and_iff_left_of_imp fun h => sub_pos.1 (h.trans_lt' (by apply div_pos <;> nlinarith))).2 (le_sub_iff_add_le.2 (this.trans_eq' ?_))
  ring_nf
  field_simp
  ring
  all_goals nlinarith

theorem unbounded_connected_counterexamples (B : ℕ) :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ (bridgeGraph s).edgeFinset.card ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  have := connected_counterexample_family (B + 3)
  grind
end KKP
