module
public import BN.Spectral
public import Mathlib
@[expose] public section

open Matrix

namespace KKP

/-- Vertices of the graph `K_{s,s,s}` joined to `K₄`. -/
abbrev BridgeVertex (s : ℕ) := (Fin 3 × Fin s) ⊕ Fin 4

/-- The literal adjacency relation: tripartite edges, clique edges, and one bridge. -/
def bridgeAdj (s : ℕ) : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
  | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0

/-- The connected counterexample family, with a single bridge between its components. -/
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

/-- The forbidden graph `K₅` with just the edge between vertices 3 and 4 removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun i j h => ⟨Ne.symm h.1, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)))

/-- The first integer witness, equal to one on the tripartite component. -/
def witnessU (s : ℕ) : BridgeVertex s → ℝ
  | .inl _ => 1
  | .inr _ => 0

/-- The second integer witness, balanced on the first part and constant on the clique. -/
def witnessV (s : ℕ) : BridgeVertex s → ℝ
  | .inl (i, a) => if i.val = 0 then (if a.val = 0 then (s : ℝ) - 1 else -1) else 0
  | .inr _ => 3 * (s : ℝ)

/-! ### Basic counting lemmas -/

theorem sum_zero_coordinate {M : Type*} [AddCommMonoid M] (s : ℕ) (hs : 0 < s) (t : M) :
    (∑ a : Fin s, if a.val = 0 then t else 0) = t := by
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · exact if_pos rfl
  · intro a _ ha
    exact if_neg fun h => ha (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma zero_coordinate_card (s : ℕ) (hs : 0 < s) :
    ((Finset.univ : Finset (Fin s)).filter (fun x => x.val = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  exact ⟨⟨0, hs⟩, by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩⟩

lemma zero_pair_card (s : ℕ) (hs : 0 < s) :
    ((Finset.univ : Finset (Fin 3 × Fin s)).filter (fun x =>
      x.1 = 0 ∧ x.2.val = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(0, ⟨0, hs⟩), ?_⟩
  ext ⟨i, a⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff]

lemma balanced_part_sum (s : ℕ) (hs : 0 < s) :
    (∑ a : Fin s, if a.val = 0 then (s : ℝ) - 1 else -1) = 0 := by
  have heq (a : Fin s) :
      (if a.val = 0 then (s : ℝ) - 1 else -1) =
        (if a.val = 0 then (s : ℝ) else 0) - 1 := by split_ifs <;> ring
  simp_rw [heq, Finset.sum_sub_distrib, sum_zero_coordinate s hs]
  simp

/-! ### Connectivity -/

theorem bridgeGraph_connected (s : ℕ) (hs : 0 < s) : (bridgeGraph s).Connected := by
  let a : Fin s := ⟨0, hs⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨.inr 0, ?_⟩
  have hb : (bridgeGraph s).Reachable (.inr 0) (.inl (0, a)) :=
    SimpleGraph.Adj.reachable (by simp [bridgeGraph, bridgeAdj, a])
  have h1 : (bridgeGraph s).Adj (.inl (0, a)) (.inl (1, a)) := by simp [bridgeGraph, bridgeAdj]
  have h2 (b : Fin s) : (bridgeGraph s).Adj (.inl (1, a)) (.inl (0, b)) := by
    simp [bridgeGraph, bridgeAdj]
  intro w
  cases w with
  | inr k =>
    by_cases hk : k = 0
    · subst hk; exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable (by simpa [bridgeGraph, bridgeAdj] using Ne.symm hk)
  | inl p =>
    rcases p with ⟨i, b⟩
    rcases eq_or_ne i 0 with rfl | hi
    · exact hb.trans (h1.reachable.trans (h2 b).reachable)
    · exact hb.trans (SimpleGraph.Adj.reachable (by simpa [bridgeGraph, bridgeAdj] using Ne.symm hi))

/-! ### The witnesses and their exact quadratic forms -/

theorem witnessU_norm (s : ℕ) : witnessU s ⬝ᵥ witnessU s = 3 * (s : ℝ) := by
  simp [dotProduct, Fintype.sum_sum_type, witnessU, Fintype.card_prod]

theorem witnesses_orthogonal (s : ℕ) (hs : 0 < s) : witnessU s ⬝ᵥ witnessV s = 0 := by
  simp [dotProduct, Fintype.sum_sum_type, witnessU, witnessV, Fintype.sum_prod_type,
    balanced_part_sum s hs]

theorem witnessV_norm (s : ℕ) (hs : 0 < s) :
    witnessV s ⬝ᵥ witnessV s = (s : ℝ) * (37 * (s : ℝ) - 1) := by
  have hsum : (∑ a : Fin s, if a.val = 0 then ((s : ℝ) - 1) ^ 2 else 1) =
      (s : ℝ) ^ 2 - (s : ℝ) := by
    have heq (a : Fin s) : (if a.val = 0 then ((s : ℝ) - 1) ^ 2 else 1) =
        (if a.val = 0 then (s : ℝ) ^ 2 - 2 * (s : ℝ) else 0) + 1 := by
      split_ifs <;> ring
    simp_rw [heq, Finset.sum_add_distrib, sum_zero_coordinate s hs]
    simp
    ring
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, witnessV]
  simp only [← pow_two, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  norm_num [Fin.sum_univ_succ, hsum]
  ring

/-- The adjacency action on the second integer vector. -/
theorem adjacency_witnessV (s : ℕ) (hs : 0 < s) (v : BridgeVertex s) :
    ((bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s) v =
      match v with
      | .inl (i, a) => if i.val = 0 ∧ a.val = 0 then 3 * (s : ℝ) else 0
      | .inr b => 9 * (s : ℝ) + if b.val = 0 then (s : ℝ) - 1 else 0 := by
  cases v with
  | inl p =>
    rcases p with ⟨i, a⟩
    fin_cases i <;> by_cases ha : a.val = 0 <;>
      simp [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessV, Fin.sum_univ_succ, ha,
        balanced_part_sum s hs]
    all_goals ring
  | inr b =>
    fin_cases b <;>
      simp +contextual [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessV, Fin.sum_univ_succ,
        sum_zero_coordinate s hs]
    all_goals ring

theorem witnessU_quadratic (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessU s = 6 * (s : ℝ) ^ 2 := by
  simp [dotProduct, mulVec, SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessU,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ,
    sum_zero_coordinate s hs, zero_coordinate_card s hs, zero_pair_card s hs]
  ring

theorem witnesses_mixed (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s = 3 * (s : ℝ) := by
  simp [dotProduct, mulVec, SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessU, witnessV,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ,
    sum_zero_coordinate s hs, zero_pair_card s hs, balanced_part_sum s hs]

theorem witnessV_quadratic (s : ℕ) (hs : 0 < s) :
    witnessV s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s =
      (s : ℝ) * (114 * (s : ℝ) - 6) := by
  simp only [dotProduct, adjacency_witnessV s hs, Fintype.sum_sum_type,
    Fintype.sum_prod_type, witnessV, Fin.sum_univ_succ, mul_ite, ite_mul,
    sum_zero_coordinate s hs, ite_pow]
  norm_num
  simp +contextual [ite_mul, mul_ite, sum_zero_coordinate s hs]
  ring

/-- The graph has exactly `3s²+7` unordered edges. -/
theorem bridgeGraph_edge_count (s : ℕ) (hs : 0 < s) :
    (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 := by
  have hsum : (∑ v : BridgeVertex s, ∑ w : BridgeVertex s,
      if (bridgeGraph s).Adj v w then (1 : ℕ) else 0) = 6 * s ^ 2 + 14 := by
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_add_distrib,
      bridgeGraph, bridgeAdj, Fin.sum_univ_succ, sum_zero_coordinate s hs]
    rw [zero_coordinate_card s hs, zero_pair_card s hs]
    ring
  have h := (bridgeGraph s).sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter] at h
  rw [hsum] at h
  omega

/-! ### `K₅ − e` has chromatic number four and is edge-critical -/

/-- Every edge of the forbidden graph lies in a triangle. -/
theorem forbidden_edge_triangle {i j : Fin 5} (h : forbiddenGraph.Adj i j) :
    ∃ k : Fin 5, forbiddenGraph.Adj i k ∧ forbiddenGraph.Adj j k := by
  revert i j
  decide +kernel

/-- A triangle cannot cross the bridge. -/
theorem triangle_same_side {s : ℕ} {x y z : BridgeVertex s}
    (hxy : (bridgeGraph s).Adj x y) (hxz : (bridgeGraph s).Adj x z)
    (hyz : (bridgeGraph s).Adj y z) : x.isLeft = y.isLeft := by
  rcases x with ⟨i, a⟩ | b <;> rcases y with ⟨j, c⟩ | d <;> rcases z with ⟨k, e⟩ | f <;>
    simp only [bridgeGraph, bridgeAdj] at hxy hxz hyz ⊢
  all_goals first | rfl | (exfalso; omega)

/-- A proper four-coloring of `K₅−e`. -/
def forbiddenColoring : forbiddenGraph.Coloring (Fin 4) :=
  .mk (fun i => ⟨min i.val 3, by omega⟩) (by decide +kernel)

/-- Its chromatic number is exactly four, witnessed by a four-clique and a coloring. -/
theorem forbidden_chromaticNumber : forbiddenGraph.chromaticNumber = 4 := by
  apply le_antisymm (SimpleGraph.Colorable.chromaticNumber_le ⟨forbiddenColoring⟩)
  refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (n := 4) (by simp)
    (fun i : Fin 4 => i.castLE (by decide)) ?_
  have hf : ∀ i j : Fin 4, i ≠ j →
      forbiddenGraph.Adj (i.castLE (by decide)) (j.castLE (by decide)) := by decide +kernel
  simpa [Pairwise] using hf

/-- Deleting the core edge `{0,1}` permits a proper three-coloring. -/
def forbiddenDeletedColoring :
    (forbiddenGraph.deleteEdges {s(0, 1)}).Coloring (Fin 3) :=
  .mk (fun i => ⟨if i.val ≤ 1 then 0 else if i.val = 2 then 1 else 2, by
    split_ifs <;> omega⟩) (by decide +kernel)

/-- The forbidden graph is color-critical in the edge-deletion sense. -/
theorem forbidden_color_critical :
    ∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
      (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber := by
  refine ⟨0, 1, by decide, ?_⟩
  rw [forbidden_chromaticNumber]
  exact lt_of_le_of_lt
    (SimpleGraph.Colorable.chromaticNumber_le ⟨forbiddenDeletedColoring⟩) (by norm_num)

/-- No injective, edge-preserving copy of `K₅−e` exists in the bridge graph. -/
theorem bridgeGraph_free (s : ℕ) : forbiddenGraph.Free (bridgeGraph s) := by
  classical
  rintro ⟨f⟩
  have hside (i : Fin 5) : (f i).isLeft = (f 0).isLeft := by
    rcases eq_or_ne i 0 with rfl | hi
    · rfl
    have ha : forbiddenGraph.Adj i 0 := by simp [forbiddenGraph, hi]
    obtain ⟨k, h1, h2⟩ := forbidden_edge_triangle ha
    exact triangle_same_side (f.toHom.map_rel ha) (f.toHom.map_rel h1) (f.toHom.map_rel h2)
  cases hf0 : f 0 with
  | inl p =>
    have hl (i : Fin 5) : ∃ p : Fin 3 × Fin s, f i = .inl p := by
      cases hfi : f i with
      | inl q => exact ⟨q, rfl⟩
      | inr b => have h := hside i; simp [hf0, hfi] at h
    choose p hp using hl
    have hcol : forbiddenGraph.Colorable 3 :=
      ⟨SimpleGraph.Coloring.mk (fun i => (p i).1) (by
        intro i j hij
        have h := f.toHom.map_rel hij
        change (bridgeGraph s).Adj (f i) (f j) at h
        rw [hp, hp] at h
        exact h)⟩
    have hle := hcol.chromaticNumber_le
    rw [forbidden_chromaticNumber] at hle
    exact absurd hle (by norm_num)
  | inr b =>
    have hr (i : Fin 5) : ∃ b : Fin 4, f i = .inr b := by
      cases hfi : f i with
      | inr c => exact ⟨c, rfl⟩
      | inl p => have h := hside i; simp [hf0, hfi] at h
    choose c hc using hr
    have hinj : Function.Injective c := by
      intro i j heq
      apply f.injective
      change f i = f j
      rw [hc, hc, heq]
    exact absurd (Fintype.card_le_of_injective _ hinj) (by norm_num)

/-! ### The explicit two-dimensional compression and the exact spectral bound -/

open scoped Matrix

/-- Normalize a nonzero coordinate vector by the square root of its squared norm. -/
noncomputable def normalizeVector {n : Type*} [Fintype n] (u : n → ℝ) : n → ℝ :=
  (Real.sqrt (u ⬝ᵥ u))⁻¹ • u

lemma normalizeVector_norm {n : Type*} [Fintype n] (u : n → ℝ) (hu : 0 < u ⬝ᵥ u) :
    normalizeVector u ⬝ᵥ normalizeVector u = 1 := by
  simp only [normalizeVector, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hu.le, inv_mul_cancel₀ (ne_of_gt hu)]

lemma normalizeVector_bilinear {n : Type*} [Fintype n] (A : Matrix n n ℝ) (u v : n → ℝ) :
    normalizeVector u ⬝ᵥ A *ᵥ normalizeVector v =
      (u ⬝ᵥ A *ᵥ v) / (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) := by
  simp only [normalizeVector, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    div_eq_mul_inv, _root_.mul_inv_rev]
  ring

lemma normalizeVector_quadratic {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (u : n → ℝ) (hu : 0 ≤ u ⬝ᵥ u) :
    normalizeVector u ⬝ᵥ A *ᵥ normalizeVector u = (u ⬝ᵥ A *ᵥ u) / (u ⬝ᵥ u) := by
  rw [normalizeVector_bilinear, ← pow_two, Real.sq_sqrt hu]

/-- The exact off-diagonal compression entry. -/
noncomputable def compC (s : ℕ) : ℝ :=
  3 * (s : ℝ) / (Real.sqrt (3 * (s : ℝ)) * Real.sqrt ((s : ℝ) * (37 * (s : ℝ) - 1)))

theorem compC_sq (s : ℕ) (hs : 3 ≤ s) : compC s ^ 2 = 3 / (37 * (s : ℝ) - 1) := by
  have hsr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  simp only [compC, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3 * (s : ℝ)),
    Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ (s : ℝ) * (37 * (s : ℝ) - 1))]
  field_simp

/-- The quadratic form at a vector of the plane spanned by two orthonormal vectors. -/
lemma quad_form_span {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) {u v : n → ℝ}
    (hsym : v ⬝ᵥ A *ᵥ u = u ⬝ᵥ A *ᵥ v) (x : ℝ) :
    (x • u + v) ⬝ᵥ A *ᵥ (x • u + v) =
      x ^ 2 * (u ⬝ᵥ A *ᵥ u) + 2 * x * (u ⬝ᵥ A *ᵥ v) + v ⬝ᵥ A *ᵥ v := by
  simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hsym, Pi.add_apply, Pi.smul_apply]
  ring

/-- The squared norm at a vector of the plane spanned by two orthonormal vectors. -/
lemma norm_span {n : Type*} [Fintype n] [DecidableEq n] {u v : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) (x : ℝ) :
    (x • u + v) ⬝ᵥ (x • u + v) = x ^ 2 + 1 := by
  have h := quad_form_span (u := u) (v := v) (1 : Matrix n n ℝ)
    (by simp [Matrix.one_mulVec, dotProduct_comm]) x
  simpa [Matrix.one_mulVec, huv, hu, hv] using h

/-- The exact lower bound on the two largest ordered adjacency eigenvalues. -/
theorem bridgeGraph_spectral_bound (s : ℕ) (hs : 3 ≤ s) :
    4 * (s : ℝ) ^ 2 + ((114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) ^ 2 +
      6 / (37 * (s : ℝ) - 1) ≤
      BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  have hs0 : 0 < s := by omega
  have hsr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hu0 : 0 < witnessU s ⬝ᵥ witnessU s := by rw [witnessU_norm]; positivity
  have hv0 : 0 < witnessV s ⬝ᵥ witnessV s := by
    rw [witnessV_norm s hs0]; exact mul_pos (by positivity) (by nlinarith)
  set u := normalizeVector (witnessU s) with huu
  set v := normalizeVector (witnessV s) with hvv
  have hu : u ⬝ᵥ u = 1 := normalizeVector_norm _ hu0
  have hv : v ⬝ᵥ v = 1 := normalizeVector_norm _ hv0
  have huv : u ⬝ᵥ v = 0 := by
    simp [huu, hvv, normalizeVector, smul_dotProduct, dotProduct_smul, witnesses_orthogonal s hs0]
  set A := (bridgeGraph s).adjMatrix ℝ with hAdef
  have hA : A.IsHermitian := (bridgeGraph s).isHermitian_adjMatrix ℝ
  have hval1 : u ⬝ᵥ A *ᵥ u = 2 * (s : ℝ) := by
    rw [hAdef, huu, normalizeVector_quadratic _ _ hu0.le, witnessU_quadratic s hs0, witnessU_norm]
    field_simp
    ring
  have hval2 : v ⬝ᵥ A *ᵥ v = (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1) := by
    rw [hAdef, hvv, normalizeVector_quadratic _ _ hv0.le, witnessV_quadratic s hs0,
      witnessV_norm s hs0]
    field_simp
  have hsym : v ⬝ᵥ A *ᵥ u = u ⬝ᵥ A *ᵥ v := by
    simpa using (hA.star_dotProduct_mulVec_comm u v).symm
  have hval3 : u ⬝ᵥ A *ᵥ v = compC s := by
    rw [huu, hvv, normalizeVector_bilinear, witnesses_mixed s hs0, witnessU_norm, witnessV_norm s hs0]
    rfl
  have hquad : ∀ x : ℝ,
      0 ≤ (BN.lambda1 (bridgeGraph s) - 2 * (s : ℝ)) * x ^ 2 - 2 * compC s * x +
        (BN.lambda1 (bridgeGraph s) - (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) := by
    intro x
    have h3 := BN.rayleigh_le hA (x • u + v)
    rw [quad_form_span (u := u) (v := v) _ hsym x, norm_span hu hv huv x] at h3
    simp only [hval1, hval2, hval3, BN.lambda1, BN.adjacencyEigenvalues₀] at h3 ⊢
    linarith
  have haL : 2 * (s : ℝ) ≤ BN.lambda1 (bridgeGraph s) := by
    have h := BN.rayleigh_le hA u
    rw [hu, mul_one] at h
    simpa only [hval1, BN.lambda1, BN.adjacencyEigenvalues₀] using h
  have htr : 2 * (s : ℝ) + (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1) ≤
      BN.lambda1 (bridgeGraph s) + BN.lambda2 (bridgeGraph s) := by
    have h := BN.sum_pair_le hA hu hv huv
    simpa only [hval1, hval2, BN.lambda1, BN.lambda2, BN.adjacencyEigenvalues₀] using h
  have hdet : (compC s) ^ 2 ≤ (BN.lambda1 (bridgeGraph s) - 2 * (s : ℝ)) *
      (BN.lambda1 (bridgeGraph s) - (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) := by
    rcases lt_or_eq_of_le haL with hlt | heq
    · have hp : 0 < BN.lambda1 (bridgeGraph s) - 2 * (s : ℝ) := by linarith
      have h := hquad (compC s / (BN.lambda1 (bridgeGraph s) - 2 * (s : ℝ)))
      have h2 : (compC s) ^ 2 / (BN.lambda1 (bridgeGraph s) - 2 * (s : ℝ)) ≤
          BN.lambda1 (bridgeGraph s) - (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1) := by
        field_simp at h ⊢
        nlinarith [h]
      rw [div_le_iff₀ hp] at h2
      linarith
    · have hc0 : compC s = 0 := by
        by_contra hc
        have h := hquad ((2 * (s : ℝ) - (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1) + 1) /
          (2 * compC s))
        rw [← heq] at h
        simp only [sub_self, zero_mul, zero_add] at h
        field_simp at h
        linarith
      rw [hc0, ← heq]
      simp
  have ha0 : 0 ≤ 2 * (s : ℝ) := by positivity
  have hb0 : 0 ≤ (114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1) := by
    have hd : (0 : ℝ) < 37 * (s : ℝ) - 1 := by linarith [hsr]
    exact div_nonneg (by linarith) hd.le
  have hpsd : (compC s) ^ 2 ≤ 2 * (s : ℝ) * ((114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) := by
    have hd : (0 : ℝ) < 37 * (s : ℝ) - 1 := by linarith
    rw [← sub_nonneg]
    have heq : 2 * (s : ℝ) * ((114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) - (compC s) ^ 2 =
        (228 * (s : ℝ) ^ 2 - 12 * (s : ℝ) - 3) / (37 * (s : ℝ) - 1) := by
      rw [compC_sq s hs]
      field_simp
      ring
    rw [heq]
    exact div_nonneg (by nlinarith) hd.le
  have h := BN.sq_add_sq_add_two_mul_sq_le ha0 hb0 hpsd haL htr hdet
  have h2 : (BN.lambda1 (bridgeGraph s)) ^ 2 + (BN.lambda2 (bridgeGraph s)) ^ 2 =
      (hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩) ^ 2 +
        (hA.eigenvalues₀ ⟨1, Fintype.one_lt_card⟩) ^ 2 := rfl
  rw [h2, compC_sq s hs] at h
  refine le_trans (le_of_eq ?_) h
  ring

/-- The exact rational excess certificate in the ordered-eigenvalue convention. -/
theorem bridgeGraph_spectral_gap (s : ℕ) (hs : 3 ≤ s) :
    (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
        (3 * (37 * (s : ℝ) - 1) ^ 2) ≤
      BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 -
        (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) := by
  have hs0 : 0 < s := by omega
  have hsr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have h := bridgeGraph_spectral_bound s hs
  rw [bridgeGraph_edge_count s hs0]
  push_cast
  have hd : (37 * (s : ℝ) - 1) ≠ 0 := by linarith
  have key : 4 * (s : ℝ) ^ 2 + ((114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) ^ 2 +
      6 / (37 * (s : ℝ) - 1) - (4 / 3 : ℝ) * (3 * (s : ℝ) ^ 2 + 7) -
      (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) / (3 * (37 * (s : ℝ) - 1) ^ 2) = 0 := by
    set t : ℝ := 37 * (s : ℝ) - 1 with ht
    have hs' : (s : ℝ) = (t + 1) / 37 := by rw [ht]; field_simp; ring
    have ht0 : t ≠ 0 := ht ▸ hd
    rw [hs']
    field_simp
    ring
  linarith

/-- The graph violates the exact `4m/3` bound, with a positive excess. -/
theorem bridgeGraph_spectral_excess (s : ℕ) (hs : 3 ≤ s) :
    (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
      BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  have hsr : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : 0 < (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
      (3 * (37 * (s : ℝ) - 1) ^ 2) := by
    refine div_pos (by nlinarith [sq_nonneg ((s : ℝ) - 3)]) ?_
    have h : (0 : ℝ) < 37 * (s : ℝ) - 1 := by linarith
    positivity
  have h := bridgeGraph_spectral_gap s hs
  linarith

/-- Connected forbidden-free counterexamples occur above every prescribed edge threshold. -/
theorem unbounded_counterexamples (B : ℕ) :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ (bridgeGraph s).edgeFinset.card ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  refine ⟨B + 3, by omega, ?_, bridgeGraph_connected _ (by omega), bridgeGraph_free _,
    bridgeGraph_spectral_excess _ (by omega)⟩
  rw [bridgeGraph_edge_count _ (by omega)]
  nlinarith [Nat.zero_le B]

end KKP
