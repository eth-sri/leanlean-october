/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Mathlib
@[expose] public section

/-! Connected forbidden-free spectral counterexamples.

The graph and eigenvalue conventions below are the protected definitions. The proof uses
one finite quotient for freeness and one shared Rayleigh bound for a positive two-dimensional
compression. All witness identities are calculated together, directly in normalized coordinates.
-/

namespace BN

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def adjacencyEigenvalues := (G.isHermitian_adjMatrix ℝ).eigenvalues
noncomputable def adjacencyEigenvalues₀ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀
noncomputable def lambda1 [Nonempty V] := adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩
noncomputable def lambda2 [Nontrivial V] := adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
end BN

namespace KKP

/-- Vertices of the graph `K_{s,s,s}` joined to `K₄`. -/
abbrev BridgeVertex s := (Fin 3 × Fin s) ⊕ Fin 4

/-- The literal adjacency relation: tripartite edges, clique edges, and one bridge. -/
def bridgeAdj s : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0

/-- The connected counterexample family, with a single bridge between its components. -/
def bridgeGraph s : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun v w => match v, w with
    | .inl (_, _), .inl (_, _) | .inr _, .inr _ => fun h => Ne.symm h
    | .inl (_, _), .inr _ | .inr _, .inl (_, _) => fun h => h⟩
  loopless := ⟨fun v => match v with
    | .inl (_, _) | .inr _ => fun h => h rfl⟩

instance bridgeAdjDecidable s : DecidableRel (bridgeGraph s).Adj
  | .inl (_, _), .inl (_, _) | .inr _, .inr _ => inferInstanceAs (Decidable (_ ≠ _))
  | .inl (_, _), .inr _ | .inr _, .inl (_, _) => inferInstanceAs (Decidable (_ ∧ _))

/-- The forbidden graph `K₅` with just the edge between vertices 3 and 4 removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun i j h => ⟨Ne.symm h.1, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 100000 in
/-- A finite quotient forces the two nonadjacent forbidden vertices to coincide on the clique. -/
lemma finite_hom : ∀ g : forbiddenGraph →g bridgeGraph 1, (g 3).isRight ∧ g 3 = g 4 := by
  rintro ⟨⟩
  decide +revert +kernel

open Matrix

/-- A positive two-dimensional compression is controlled by the first two ordered eigenvalues. -/
theorem positive_compression_le {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} [Nontrivial n] (hA : B.IsHermitian)
    {Q : Matrix n (Fin 2) ℝ} (hQ : Qᵀ * Q = 1) {a b c}
    (hComp : Qᵀ * B * Q = !![a, c; c, b])
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < a * b - c ^ 2) :
    a ^ 2 + b ^ 2 + 2 * c ^ 2 ≤ hA.eigenvalues₀ 0 ^ 2 + hA.eigenvalues₀ ⟨1,Fintype.one_lt_card⟩ ^ 2 := by
  -- Parseval in the ordered eigenbasis gives a shared Rayleigh estimate.
  let basis := (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace
  have rayleigh u k
      (ho : ∀ i < k, basis i ⬝ᵥ u = 0) :
      (B *ᵥ u) ⬝ᵥ u ≤ hA.eigenvalues₀ k * (u ⬝ᵥ u) := by
    let x := WithLp.toLp 2 u
    change inner ℝ x (B.toEuclideanLin x) ≤ hA.eigenvalues₀ k * inner ℝ x x
    rw [← basis.repr.inner_map_map, ← basis.repr.inner_map_map]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      basis, LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply]
    simp [OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct,
      x, dotProduct_comm u, mul_assoc, ← pow_two, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i < k
    · rw [ho i hi]; simp
    · gcongr
      exact hA.eigenvalues₀_antitone (le_of_not_gt hi)
  have hR z k ho := rayleigh (Q *ᵥ z) k ho
  simp only [← dotProduct_transpose_mulVec Q, mulVec_mulVec, ← Matrix.mul_assoc,
    hComp, hQ, one_mulVec] at hR
  let δ := Real.sqrt ((a - b) ^ 2 + 4 * c ^ 2)
  set α := (a + b + δ) / 2 with haDef
  set β := (a + b - δ) / 2 with hbDef
  have hδ : δ ^ 2 = _ := Real.sq_sqrt (by positivity)
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hb : 0 < b := by nlinarith
  have ⟨hβ,haβ⟩ : 0 ≤ β ∧ 0 < a - β := by
    constructor <;> nlinarith
  have htop : α ≤ hA.eigenvalues₀ 0 := by
    let w := ![c, α - a]
    have heig : !![a, c; c, b] *ᵥ w = α • w := by
      ext i
      fin_cases i <;> simp [w, Matrix.mulVec] <;> nlinarith
    have hn : 0 < w ⬝ᵥ w := by
      simp [w, ← pow_two]
      positivity
    have h := hR w 0 (by simp)
    rw [heig, dotProduct_smul, smul_eq_mul] at h
    nlinarith
  -- The compression plane meets the orthogonal complement of the top eigenvector.
  obtain ⟨z, hz, ho⟩ := exists_ne_zero_dotProduct_eq_zero
    (Qᵀ *ᵥ basis 0)
  have hp : 0 < z ⬝ᵥ z := dotProduct_self_star_pos_iff.mpr hz
  have h := hR z ⟨1,Fintype.one_lt_card⟩ (by
    simpa [Fin.lt_def, ← dotProduct_transpose_mulVec Q] using ho)
  have hsecond : β ≤ hA.eigenvalues₀ ⟨1,Fintype.one_lt_card⟩ := by
    apply (mul_le_mul_iff_left₀ hp).mp
    refine le_trans ?_ h
    have := sq_nonneg ((a - β) * z 0 + c * z 1)
    dsimp [β] at *
    simp [dotProduct, Matrix.mulVec]
    nlinarith [congr($hδ * z 1 ^ 2)]
  calc
    _ = α ^ 2 + β ^ 2 := by nlinarith
    _ ≤ _ := by gcongr

attribute [local simp] bridgeGraph bridgeAdj Fintype.sum_sum_type Fintype.sum_prod_type Fin.sum_univ_succ SimpleGraph.adjMatrix Matrix.mul_apply

/-- Squared spectral mass in the two largest ordered eigenvalues. -/
local notation:max "energy " s:max => BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2

/-- The complete combinatorial and ordered-spectral certificate. -/
theorem connected_counterexample_family s (hs : 3 ≤ s) :
    forbiddenGraph.chromaticNumber = 4 ∧
      (∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
        (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber) ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 ∧
      (656 * ↑s ^ 2 - 1366 * ↑s + 62) /
          (3 * (37 * ↑s - 1) ^ 2) ≤
        energy s -
          4 / 3 * ↑(bridgeGraph s).edgeFinset.card ∧
      4 / 3 * ↑(bridgeGraph s).edgeFinset.card <
        energy s := by
  obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  have hr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have he : (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 := by
    subst s
    have h := (bridgeGraph (t + 1)).sum_degrees_eq_twice_card_edges
    simp_rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter] at h
    conv_lhs at h =>
      simp [Finset.sum_add_distrib, -Finset.sum_boole]
    nlinarith
  have hχ : forbiddenGraph.chromaticNumber = 4 := by
    refine (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable (n := 3)).2 ⟨⟨![(0 : Fin 4), 1, 2, 3, 3], by decide⟩, ?_⟩
    rintro ⟨c,hc⟩
    revert c
    decide +kernel
  refine ⟨hχ, ?_, ?_, ?_, he, ?_⟩
  · refine ⟨0, 1, by decide, ?_⟩
    rw [hχ]
    exact lt_of_le_of_lt
      (SimpleGraph.Colorable.chromaticNumber_le ⟨![(0 : Fin 3), 0, 1, 2, 2], by decide⟩) (by norm_num)
  · let : NeZero s := ⟨by omega⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨.inl (0, 0), ?_⟩
    rintro (⟨i,b⟩ | j)
    · apply SimpleGraph.Reachable.trans (v := .inl (if i = 1 then 2 else 1,0)) <;>
        apply SimpleGraph.Adj.reachable <;> fin_cases i <;> simp
    · have h : (bridgeGraph s).Reachable (.inl (0,0)) (.inr 0) :=
        SimpleGraph.Adj.reachable (by simp)
      by_cases hj : j = 0
      · subst j; exact h
      · exact h.trans (SimpleGraph.Adj.reachable (Ne.symm hj))
  · rintro ⟨f⟩
    let p : bridgeGraph s →g bridgeGraph 1 := ⟨(fun
      | .inl (i, _) => .inl (i, 0)
      | .inr b => .inr b), by
        intro v w h
        cases v <;> cases w <;> simp_all⟩
    have hh := finite_hom (p.comp f.toHom)
    suffices f 3 = f 4 by have := f.injective this; contradiction
    cases h3 : f 3 <;> cases h4 : f 4 <;> simp_all [p, -bridgeGraph]
  · refine (and_iff_left_of_imp fun h => ?_).mpr ?_
    · exact sub_pos.mp (lt_of_lt_of_le (by apply div_pos <;> nlinarith) h)
    · set d : ℝ := 37 * s - 1 with hdef
      have hd : 0 < d := by linarith
      let x := Real.sqrt (3 * s)
      let y := Real.sqrt (s * d)
      let Q := of fun
        | (.inl (i,a) : BridgeVertex s) => ![x⁻¹, (if i.val = 0 then (if a.val = 0 then (s : ℝ) else 0) - 1 else 0) / y]
        | .inr _ => ![0, 3 * s / y]
      let c := 3 * s / (x * y)
      -- Compute the Gram and adjacency forms together, already normalized.
      obtain ⟨hQ, hComp, hc⟩ : Qᵀ * Q = 1 ∧
          Qᵀ * (bridgeGraph s).adjMatrix ℝ * Q =
            !![2 * (s : ℝ), c; c, (114 * s - 6) / d] ∧
          c ^ 2 = 3 / d := by
        and_intros
        all_goals
          try
            subst s
            ext i j
            fin_cases i, j
        all_goals
          simp [Q, -Finset.sum_boole, c] <;>
            field_simp (disch := positivity) <;>
            simp (disch := positivity) only [x, y, Real.sq_sqrt] <;>
            field_simp (disch := positivity) <;> ring_nf! <;> push_cast <;> ring
      have h :=
        positive_compression_le ((bridgeGraph s).isHermitian_adjMatrix ℝ) hQ hComp
          (by positivity) (by positivity) (by
            rw [hc]
            field_simp (disch := positivity)
            nlinarith)
      rw [hc] at h
      rw [he, le_sub_iff_add_le]
      push_cast
      convert! h using 1
      field_simp (disch := linarith)
      ring!

/-- Connected forbidden-free counterexamples occur above every prescribed edge threshold. -/
theorem unbounded_connected_counterexamples B :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ (bridgeGraph s).edgeFinset.card ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      4 / 3 * ↑(bridgeGraph s).edgeFinset.card <
        energy s := by
  obtain ⟨_, _, hc, hf, he, _, hg⟩ := connected_counterexample_family (B + 3) (by omega)
  refine ⟨B + 3, by omega, ?_, hc, hf, hg⟩
  nlinarith
end KKP
