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

private def outerBondEquiv (n : ℕ) (hn : 0 < n) : (OuterBoxEdge n → Bool) ≃
    (LiteralBond (box n) → Bool) × ((Bool × Bool → Bool) × (OuterShellEdge n → Bool)) :=
  (Equiv.arrowCongr (outerBoxEdgeEquiv n hn).symm (Equiv.refl Bool)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _)))

def outerCornerClosed (n : ℕ) (Ω : OuterBoxEdge n → Bool) : Prop :=
  ∀ b : Bool × Bool, Ω (cornerCutEdge n b) = false

section

variable (n : ℕ) (hn : 0 < n)

private theorem outerCornerClosed_restore_iff
    (ω : LiteralBond (box n) → Bool) (κ : Bool × Bool → Bool) (η : OuterShellEdge n → Bool) :
    outerCornerClosed n ((outerBondEquiv n hn).symm (ω, κ, η)) ↔ κ = fun _ => false := by
  change (∀ b, (((outerBoxEdgeEquiv n hn).symm ((outerBoxEdgeEquiv n hn) (.inr (.inl b)))).elim ω
    (fun c => c.elim κ η)) = false) ↔ _
  simp [funext_iff]

theorem sum_outerCornerClosed (f : (OuterBoxEdge n → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then f Ω else 0) =
      ∑ ω : LiteralBond (box n) → Bool, ∑ η : OuterShellEdge n → Bool,
        f (restoreGhostBonds n hn ω η) := by
  classical
  rw [← (outerBondEquiv n hn).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [outerCornerClosed_restore_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

end

theorem bernoulliBondWeight_restoreGhost (β : ℝ) (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    bernoulliBondWeight β (restoreGhostBonds n hn ω η) =
      bernoulliBondWeight β ω * Real.exp (-β) ^ 4 * bernoulliBondWeight β η := by
  unfold bernoulliBondWeight
  rw [← (outerBoxEdgeEquiv n hn).prod_comp]
  change (∏ b : OuterEdgePiece n, if restoreGhostBonds n hn ω η (outerEdgeFromPiece n b)
    then bondProbability β else Real.exp (-β)) = _
  simp_rw [restoreGhostBonds_piece]
  rw [Fintype.prod_sum_type (α₁ := LiteralBond (box n))
    (α₂ := (Bool × Bool) ⊕ OuterShellEdge n)]
  rw [Fintype.prod_sum_type (α₁ := Bool × Bool) (α₂ := OuterShellEdge n)]
  simp only [Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ite_false,
    Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
  norm_num only [Nat.reduceMul]
  rw [← mul_assoc]
  rfl

theorem sum_bernoulliBondWeight {E : Type*} [Fintype E] (β : ℝ) :
    ∑ ω : E → Bool, bernoulliBondWeight β ω = 1 := by
  unfold bernoulliBondWeight
  calc
    _ = ∏ _e : E, ∑ b : Bool, if b then bondProbability β else Real.exp (-β) := by
      exact (Fintype.prod_sum (fun (_ : E) (b : Bool) =>
        if b then bondProbability β else Real.exp (-β))).symm
    _ = 1 := by simp [bondProbability]

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
      FK.closed_card_boolConfigurationEquiv, FK.card_boolConfigurationEquiv]
    rfl
  rw [hbern, outer_componentCount_eq_ghost, bernoulliBondWeight_restoreGhost]
  have hg : ghostRCWeight q (box n) β ω * q =
      bernoulliBondWeight β ω * (q : ℝ) ^ ghostComponentCount (box n) ω := by
    calc
      _ = _ := ghostRCWeight_mul_q q (box n) β ω
      _ = _ := by
        apply congrArg (fun b : ℝ => b * (q : ℝ) ^ ghostComponentCount (box n) ω)
        unfold bernoulliBondWeight
        apply Finset.prod_congr
        · ext b; simp
        · intro b _; rfl
  calc
    _ = (Real.exp (-β) ^ 4 * bernoulliBondWeight β η) *
        (bernoulliBondWeight β ω * (q : ℝ) ^ ghostComponentCount (box n) ω) := by ring
    _ = _ := by rw [← hg]; ring

/-- Integrating out the shell bonds multiplies the ghost weights by one constant. -/
theorem sum_outerCornerClosed_weight_test (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (n : ℕ) (hn : 0 < n) (f : (OuterBoxEdge n → Bool) → ℝ) (g : (LiteralBond (box n) → Bool) → ℝ)
    (hfg : ∀ ω η, f (restoreGhostBonds n hn ω η) = g ω) :
    (∑ Ω, if outerCornerClosed n Ω then
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) * f Ω else 0) =
      ((q : ℝ) * Real.exp (-β) ^ 4) * ∑ ω, ghostRCWeight q (box n) β ω * g ω := by
  rw [sum_outerCornerClosed n hn, Finset.mul_sum]
  simp_rw [outer_weight_restoreGhost, hfg]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp_rw [mul_right_comm (_ * ghostRCWeight q (box n) β ω) _ (g ω)]
  rw [← Finset.mul_sum]
  have hs : (∑ η : OuterShellEdge n → Bool, bernoulliBondWeight β η) = 1 :=
    (Finset.sum_congr (by ext η; simp) (fun _ _ => rfl)).trans (sum_bernoulliBondWeight β)
  rw [hs, mul_one]
  ring

theorem outerCornerClosed_iff_mem (n : ℕ) (Ω : OuterBoxEdge n → Bool) :
    outerCornerClosed n Ω ↔ FK.boolConfigurationEquiv _ Ω ∈ cornerClosureEvent n := by
  classical
  change (∀ b, Ω (cornerCutEdge n b) = false) ↔
    Disjoint (cornerCutEdges n) (FK.boolConfigurationEquiv _ Ω)
  rw [Finset.disjoint_left]
  constructor
  · intro h e he heω
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
    have ht := (FK.mem_boolConfigurationEquiv _ Ω _).mp heω
    rw [h b] at ht
    cases ht
  · intro h b
    have hn : Ω (cornerCutEdge n b) ≠ true := by
      intro ht
      exact h (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
        ((FK.mem_boolConfigurationEquiv _ Ω _).mpr ht)
    grind

end
end PottsDiscontinuity.Potts
