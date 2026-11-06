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

section
variable (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool) (κ : Bool × Bool → Bool) (η : OuterShellEdge n → Bool)
def restoreOuterBonds  : OuterBoxEdge n → Bool :=
  fun e => ((outerBoxEdgeEquiv n hn).symm e).elim ω (fun b => b.elim κ η)

theorem restoreOuterBonds_piece (b : OuterEdgePiece n) :
    restoreOuterBonds n hn ω κ η (outerEdgeFromPiece n b) = b.elim ω (fun c => c.elim κ η) := by
  change (((outerBoxEdgeEquiv n hn).symm ((outerBoxEdgeEquiv n hn) b)).elim ω
    (fun c => c.elim κ η)) = _
  simp
end

section
variable (n : ℕ)
def outerBondEquiv (hn : 0 < n) : (OuterBoxEdge n → Bool) ≃
    (LiteralBond (box n) → Bool) × ((Bool × Bool → Bool) × (OuterShellEdge n → Bool)) where
  toFun Ω := (readLiteralBonds n Ω, (fun b => Ω (cornerCutEdge n b), fun e => Ω e.val))
  invFun z := restoreOuterBonds n hn z.1 z.2.1 z.2.2
  left_inv Ω := by
    funext e
    obtain ⟨b, rfl⟩ := outerEdgeFromPiece_surjective n hn e
    dsimp only
    rw [restoreOuterBonds_piece]
    cases b with
    | inl b => rfl
    | inr b => aesop
  right_inv z := by
    rcases z with ⟨ω, κ, η⟩
    apply Prod.ext
    · funext b
      exact restoreOuterBonds_piece n hn ω κ η (.inl b)
    · apply Prod.ext
      · funext b
        exact restoreOuterBonds_piece n hn ω κ η (.inr (.inl b))
      · funext e
        exact restoreOuterBonds_piece n hn ω κ η (.inr (.inr e))

def outerCornerClosed (Ω : OuterBoxEdge n → Bool) : Prop :=
  ∀ b : Bool × Bool, Ω (cornerCutEdge n b) = false
end

section
variable (n : ℕ) (hn : 0 < n)
theorem outerCornerClosed_restore_iff (ω : LiteralBond (box n) → Bool) (κ : Bool × Bool → Bool) (η : OuterShellEdge n → Bool) :
    outerCornerClosed n (restoreOuterBonds n hn ω κ η) ↔ κ = fun _ => false := by
  change (∀ b, restoreOuterBonds n hn ω κ η (outerEdgeFromPiece n (.inr (.inl b))) = false) ↔ _
  simp only [restoreOuterBonds_piece, Sum.elim_inr, Sum.elim_inl]
  grind

theorem readLiteralBonds_restore (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    readLiteralBonds n (restoreGhostBonds n hn ω η) = ω := by
  funext b
  exact restoreGhostBonds_piece n hn ω η (.inl b)

theorem sum_outerCornerClosed (f : (OuterBoxEdge n → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then f Ω else 0) =
      ∑ ω : LiteralBond (box n) → Bool, ∑ η : OuterShellEdge n → Bool,
        f (restoreGhostBonds n hn ω η) := by
  rw [← (outerBondEquiv n hn).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  change (∑ κ, ∑ η, if outerCornerClosed n (restoreOuterBonds n hn ω κ η)
    then f (restoreOuterBonds n hn ω κ η) else 0) = _
  simp_rw [outerCornerClosed_restore_iff]
  simp
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
  simp
  grind

theorem sum_bernoulliBondWeight {E : Type*} [Fintype E] (β : ℝ) :
    ∑ ω : E → Bool, bernoulliBondWeight β ω = 1 := by
  calc
    _ = ∏ _e : E, ∑ b : Bool, if b then bondProbability β else Real.exp (-β) :=
      (Fintype.prod_sum (fun (_ : E) (b : Bool) =>
        if b then bondProbability β else Real.exp (-β))).symm
    _ = 1 := by simp [bondProbability]

section
variable (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 0 < n)
include hn
theorem outer_weight_restoreGhost (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
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
        apply Finset.prod_congr <;> grind
  grind

/-- Integrating the free shell bonds gives the exact unnormalised ghost law. -/
theorem sum_outerCornerClosed_weight_test (f : (LiteralBond (box n) → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) * f (readLiteralBonds n Ω) else 0) =
      ((q : ℝ) * Real.exp (-β) ^ 4) * ∑ ω, ghostRCWeight q (box n) β ω * f ω := by
  rw [sum_outerCornerClosed n hn]
  simp_rw [outer_weight_restoreGhost, readLiteralBonds_restore]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ η : OuterShellEdge n → Bool,
        (((q : ℝ) * Real.exp (-β) ^ 4) * (ghostRCWeight q (box n) β ω * f ω)) *
          bernoulliBondWeight β η := by
      grind
    _ = _ := by
      rw [← Finset.mul_sum]
      have hs : (∑ η : OuterShellEdge n → Bool, bernoulliBondWeight β η) = 1 := by
        calc
          _ = _ := Finset.sum_congr (by grind) (fun _ _ => rfl)
          _ = 1 := sum_bernoulliBondWeight β
      simp_all

/-- The literal ghost expectation is the outer wired weight conditioned on the
four corner edges being closed. This identity includes the ghost bonds themselves. -/
theorem ghost_expectation_eq_conditioned_outer_weight
    (f : (LiteralBond (box n) → Bool) → ℝ) :
    (∑ Ω, if outerCornerClosed n Ω then
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) * f (readLiteralBonds n Ω) else 0) /
    (∑ Ω, if outerCornerClosed n Ω then
      FK.weight _ (fkParameters q hq β hβ) (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ Ω) else 0) =
      ∑ ω, ghostRCProbability q (box n) β ω * f ω := by
  have hd := sum_outerCornerClosed_weight_test q hq β hβ n hn (fun _ => 1)
  simp at hd
  rw [sum_outerCornerClosed_weight_test q hq β hβ n hn f, hd, mul_div_mul_left _ _ (by positivity)]
  unfold ghostRCProbability ghostRCPartition
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg₂ (fun (a : ℝ) (b : ℝ) => a / b)
  · rfl
  · exact Finset.sum_congr (by grind) (fun _ _ => rfl)
end

theorem outerCornerClosed_iff_mem (n : ℕ) (Ω : OuterBoxEdge n → Bool) :
    outerCornerClosed n Ω ↔ FK.boolConfigurationEquiv _ Ω ∈ cornerClosureEvent n := by
  change (∀ b, Ω (cornerCutEdge n b) = false) ↔
    Disjoint (cornerCutEdges n) (FK.boolConfigurationEquiv _ Ω)
  rw [Finset.disjoint_left]
  constructor
  · intro h e he heω
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
    have ht := (FK.mem_boolConfigurationEquiv _ Ω _).mp heω
    grind
  · intro h b
    have hn : Ω (cornerCutEdge n b) ≠ true := by
      intro ht
      exact h (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
        ((FK.mem_boolConfigurationEquiv _ Ω _).mpr ht)
    grind

theorem conditional_ratio_div {E : Type*} [Fintype E]
    (w f : E → ℝ) (B : E → Prop) (Z : ℝ) (hZ : Z ≠ 0) :
    (∑ e, if B e then w e / Z * f e else 0) /
      (∑ e, if B e then w e / Z else 0) =
    (∑ e, if B e then w e * f e else 0) /
      (∑ e, if B e then w e else 0) := by
  have hnum : (∑ e, if B e then w e / Z * f e else 0) =
      (∑ e, if B e then w e * f e else 0) / Z := by
    rw [Finset.sum_div]
    grind
  have hden : (∑ e, if B e then w e / Z else 0) =
      (∑ e, if B e then w e else 0) / Z := by
    rw [Finset.sum_div]
    grind
  rw [hnum, hden, div_div_div_cancel_right₀ hZ]

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
    rw [← FK.configurationProbability_eq_rcProb]
    rfl
  simp_rw [hp]
  rw [conditional_ratio_div _ _ _ _ (FK.partitionFunction_pos (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))
    (fkParameters q hq β hβ) (outerBoxWiring n)).ne']
  exact ghost_expectation_eq_conditioned_outer_weight q hq β hβ n hn f

end
end PottsDiscontinuity.Potts
