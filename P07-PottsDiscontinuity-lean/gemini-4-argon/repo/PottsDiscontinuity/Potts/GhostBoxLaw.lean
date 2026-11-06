module

public import PottsDiscontinuity.Potts.GhostBoxContraction

/-! Exact ghost law as a marginal of the conditioned outer wired FK law. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

local instance lawBoundaryFintype (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _
local instance lawShellFintype (n : ℕ) : Fintype (OuterShellEdge n) := Fintype.ofFinite _
local instance lawOuterEdgeFintype (n : ℕ) : Fintype (OuterBoxEdge n) := Fintype.ofFinite _
local instance lawExtraFunctionsFintype (n : ℕ) :
    Fintype ((Bool × Bool → Bool) × (OuterShellEdge n → Bool)) := instFintypeProd _ _

def readLiteralBonds (n : ℕ) (Ω : OuterBoxEdge n → Bool) : LiteralBond (box n) → Bool :=
  fun b => Ω (literalBondOuterEdge n b)

def restoreOuterBonds (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (κ : Bool × Bool → Bool) (η : OuterShellEdge n → Bool) : OuterBoxEdge n → Bool :=
  fun e => ((outerBoxEdgeEquiv n hn).symm e).elim ω (fun b => b.elim κ η)

theorem restoreOuterBonds_piece (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (κ : Bool × Bool → Bool) (η : OuterShellEdge n → Bool) (b : OuterEdgePiece n) :
    restoreOuterBonds n hn ω κ η (outerEdgeFromPiece n b) = b.elim ω (fun c => c.elim κ η) := by
  change (((outerBoxEdgeEquiv n hn).symm ((outerBoxEdgeEquiv n hn) b)).elim ω
    (fun c => c.elim κ η)) = _
  rw [Equiv.symm_apply_apply]

def outerBondEquiv (n : ℕ) (hn : 0 < n) : (OuterBoxEdge n → Bool) ≃
    (LiteralBond (box n) → Bool) × ((Bool × Bool → Bool) × (OuterShellEdge n → Bool)) where
  toFun Ω := (readLiteralBonds n Ω, (fun b => Ω (cornerCutEdge n b), fun e => Ω e.val))
  invFun z := restoreOuterBonds n hn z.1 z.2.1 z.2.2
  left_inv Ω := funext fun e => by
    obtain ⟨b | b | b, rfl⟩ := outerEdgeFromPiece_surjective n hn e <;>
      dsimp only <;> rw [restoreOuterBonds_piece] <;> rfl
  right_inv := fun ⟨ω, κ, η⟩ => Prod.ext (funext fun b => restoreOuterBonds_piece n hn ω κ η (.inl b))
    (Prod.ext (funext fun b => restoreOuterBonds_piece n hn ω κ η (.inr (.inl b)))
      (funext fun e => restoreOuterBonds_piece n hn ω κ η (.inr (.inr e))))

def outerCornerClosed (n : ℕ) (Ω : OuterBoxEdge n → Bool) : Prop :=
  ∀ b : Bool × Bool, Ω (cornerCutEdge n b) = false

theorem outerCornerClosed_restore_iff (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (κ : Bool × Bool → Bool) (η : OuterShellEdge n → Bool) :
    outerCornerClosed n (restoreOuterBonds n hn ω κ η) ↔ κ = fun _ => false := by
  change (∀ b, restoreOuterBonds n hn ω κ η (outerEdgeFromPiece n (.inr (.inl b))) = false) ↔ _
  simp only [restoreOuterBonds_piece, Sum.elim_inr, Sum.elim_inl]
  exact funext_iff.symm

theorem readLiteralBonds_restore (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    readLiteralBonds n (restoreGhostBonds n hn ω η) = ω :=
  funext fun b => restoreGhostBonds_piece n hn ω η (.inl b)

theorem sum_outerCornerClosed (n : ℕ) (hn : 0 < n) (f : (OuterBoxEdge n → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then f Ω else 0) =
      ∑ ω : LiteralBond (box n) → Bool, ∑ η : OuterShellEdge n → Bool,
        f (restoreGhostBonds n hn ω η) := by
  rw [← (outerBondEquiv n hn).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Fintype.sum_prod_type]
  change (∑ κ, ∑ η, if outerCornerClosed n (restoreOuterBonds n hn ω κ η)
    then f (restoreOuterBonds n hn ω κ η) else 0) = _
  simp_rw [outerCornerClosed_restore_iff]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem bernoulliBondWeight_restoreGhost (β : ℝ) (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    bernoulliBondWeight β (restoreGhostBonds n hn ω η) =
      bernoulliBondWeight β ω * Real.exp (-β) ^ 4 * bernoulliBondWeight β η := by
  unfold bernoulliBondWeight
  rw [← (outerBoxEdgeEquiv n hn).prod_comp]
  change (∏ b : OuterEdgePiece n, if restoreGhostBonds n hn ω η (outerEdgeFromPiece n b)
    then bondProbability β else Real.exp (-β)) = _
  simp_rw [restoreGhostBonds_piece]
  rw [Fintype.prod_sum_type (α₁ := LiteralBond (box n)) (α₂ := (Bool × Bool) ⊕ OuterShellEdge n),
    Fintype.prod_sum_type (α₁ := Bool × Bool) (α₂ := OuterShellEdge n)]
  simp only [Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ite_false,
    Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
  norm_num only [Nat.reduceMul]
  rw [← mul_assoc]
  exact congrArg₂ (fun a c => a * Real.exp (-β) ^ 4 * c)
    (Finset.prod_congr (by ext; simp) fun _ _ => rfl)
    (Finset.prod_congr (by ext; simp) fun _ _ => rfl)

theorem sum_bernoulliBondWeight {E : Type*} [Fintype E] (β : ℝ) :
    ∑ ω : E → Bool, bernoulliBondWeight β ω = 1 := by
  unfold bernoulliBondWeight
  rw [← Fintype.prod_sum (fun (_ : E) (b : Bool) => if b then bondProbability β else Real.exp (-β))]
  simp [bondProbability]

theorem outer_weight_restoreGhost (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) =
      ((q : ℝ) * Real.exp (-β) ^ 4) * ghostRCWeight q (box n) β ω * bernoulliBondWeight β η := by
  have hbern : FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
      (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) =
        bernoulliBondWeight β (restoreGhostBonds n hn ω η) * (q : ℝ) ^
          FK.componentCount _ (outerBoxWiring n)
            (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) := by
    rw [bernoulliBondWeight_eq, FK.weight, FK.card_boolConfigurationEquiv,
      FK.closed_card_boolConfigurationEquiv, FK.card_boolConfigurationEquiv]; rfl
  rw [hbern, outer_componentCount_eq_ghost, bernoulliBondWeight_restoreGhost]
  have hg : ghostRCWeight q (box n) β ω * q =
      bernoulliBondWeight β ω * (q : ℝ) ^ ghostComponentCount (box n) ω :=
    (ghostRCWeight_mul_q q (box n) β ω).trans
      (congrArg (· * (q : ℝ) ^ ghostComponentCount (box n) ω)
        (Finset.prod_congr (by ext; simp) fun _ _ => rfl))
  linear_combination -Real.exp (-β) ^ 4 * bernoulliBondWeight β η * hg

/-- Integrating the free shell bonds gives the exact unnormalised ghost law. -/
theorem sum_outerCornerClosed_weight_test (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (n : ℕ) (hn : 0 < n) (f : (LiteralBond (box n) → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) * f (readLiteralBonds n Ω) else 0) =
      ((q : ℝ) * Real.exp (-β) ^ 4) * ∑ ω, ghostRCWeight q (box n) β ω * f ω := by
  rw [sum_outerCornerClosed n hn]
  simp_rw [outer_weight_restoreGhost, readLiteralBonds_restore]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [show (∑ η : OuterShellEdge n → Bool,
        (q : ℝ) * Real.exp (-β) ^ 4 * ghostRCWeight q (box n) β ω * bernoulliBondWeight β η * f ω) =
      ((q : ℝ) * Real.exp (-β) ^ 4 * (ghostRCWeight q (box n) β ω * f ω)) *
        ∑ η : OuterShellEdge n → Bool, bernoulliBondWeight β η by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring,
    show (∑ η : OuterShellEdge n → Bool, bernoulliBondWeight β η) = 1 from
      (Finset.sum_congr (by ext; simp) fun _ _ => rfl).trans
        (sum_bernoulliBondWeight (E := OuterShellEdge n) β), mul_one]

/-- The literal ghost expectation is the outer wired weight conditioned on the
four corner edges being closed. This identity includes the ghost bonds themselves. -/
theorem ghost_expectation_eq_conditioned_outer_weight
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 0 < n)
    (f : (LiteralBond (box n) → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) * f (readLiteralBonds n Ω) else 0) /
    (∑ Ω, if outerCornerClosed n Ω then
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) else 0) =
      ∑ ω, ghostRCProbability q (box n) β ω * f ω := by
  have hd := sum_outerCornerClosed_weight_test q hq β hβ n hn (fun _ => 1)
  simp only [mul_one] at hd
  rw [sum_outerCornerClosed_weight_test q hq β hβ n hn f, hd,
    mul_div_mul_left _ _ (mul_ne_zero (by exact_mod_cast (show q ≠ 0 by omega))
      (pow_ne_zero _ (Real.exp_ne_zero _)))]
  unfold ghostRCProbability ghostRCPartition
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  exact congrArg₂ (· / ·) (Finset.sum_congr (by ext; simp) fun _ _ => rfl)
    (Finset.sum_congr (by ext; simp) fun _ _ => rfl)

theorem outerCornerClosed_iff_mem (n : ℕ) (Ω : OuterBoxEdge n → Bool) :
    outerCornerClosed n Ω ↔ FK.boolConfigurationEquiv _ Ω ∈ cornerClosureEvent n := by
  change (∀ b, Ω (cornerCutEdge n b) = false) ↔
    Disjoint (cornerCutEdges n) (FK.boolConfigurationEquiv _ Ω)
  rw [Finset.disjoint_left]
  refine ⟨fun h e he heω => ?_, fun h b => ?_⟩
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
    simp [h b] at heω
  · by_contra hb
    exact h (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
      ((FK.mem_boolConfigurationEquiv _ Ω _).mpr (Bool.eq_true_of_ne_false hb))

private theorem conditional_ratio_div {E : Type*} [Fintype E]
    (w f : E → ℝ) (B : E → Prop) (Z : ℝ) (hZ : Z ≠ 0) :
    (∑ e, if B e then w e / Z * f e else 0) /
      (∑ e, if B e then w e / Z else 0) =
    (∑ e, if B e then w e * f e else 0) /
      (∑ e, if B e then w e else 0) := by
  rw [show (∑ e, if B e then w e / Z * f e else 0) = (∑ e, if B e then w e * f e else 0) / Z by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h : B e <;> simp [h, div_mul_eq_mul_div],
    show (∑ e, if B e then w e / Z else 0) = (∑ e, if B e then w e else 0) / Z by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h : B e <;> simp [h],
    div_div_div_cancel_right₀ hZ]

/-- Exact conditional expectation under the normalized, frozen wired RC law.
For observables depending only on internal bonds this is the requested edge marginal. -/
theorem ghost_expectation_eq_conditioned_wired_box
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 0 < n)
    (f : (LiteralBond (box n) → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then
      rcProb (box (n + 1)) (fkParameters q hq β hβ).toP
        (fkParameters q hq β hβ).toQ 1 Ω * f (readLiteralBonds n Ω) else 0) /
    (∑ Ω, if outerCornerClosed n Ω then
      rcProb (box (n + 1)) (fkParameters q hq β hβ).toP
        (fkParameters q hq β hβ).toQ 1 Ω else 0) =
      ∑ ω, ghostRCProbability q (box n) β ω * f ω := by
  have hp (Ω : OuterBoxEdge n → Bool) :
      rcProb (box (n + 1)) (fkParameters q hq β hβ).toP
        (fkParameters q hq β hβ).toQ 1 Ω =
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) /
      FK.partitionFunction (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))
        (fkParameters q hq β hβ) (outerBoxWiring n) := by
    rw [← FK.configurationProbability_eq_rcProb]; rfl
  simp_rw [hp]
  rw [conditional_ratio_div _ _ _ _ (FK.partitionFunction_pos (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))
    (fkParameters q hq β hβ) (outerBoxWiring n)).ne']
  exact ghost_expectation_eq_conditioned_outer_weight q hq β hβ n hn f

end
end PottsDiscontinuity.Potts
