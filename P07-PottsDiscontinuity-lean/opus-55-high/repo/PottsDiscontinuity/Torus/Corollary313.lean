module

public import PottsDiscontinuity.Torus.OrientedLoopWeight
public import PottsDiscontinuity.Torus.WindingReorientation
public import PottsDiscontinuity.TorusTopology.UnitWindingStructure

/-!
# Sector comparisons in Corollary 3.13

The two homological turn classifications are explicit premises here; they are discharged
in `Torus/Corollary313Final.lean` by the turning classifications proved in
`TorusTopology/ZeroWindingTurning.lean` and `TorusTopology/NonzeroWindingTurning.lean`.
The `U = 1` vertical-loop structure is imported from TorusTopology.UnitWindingStructure, with no
horizontal-winding restriction.
-/

public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

abbrev LoopChoiceRest (α : Type*) (a b : α) :=
  {x : α // x ≠ a ∧ x ≠ b}

def loopChoiceSplitEquiv {α : Type*} [DecidableEq α] (a b : α) (hab : a ≠ b) :
    (α → Bool) ≃ Bool × (Bool × (LoopChoiceRest α a b → Bool)) where
  toFun F := (F a, F b, fun x => F x.val)
  invFun p x := if hx : x = a then p.1 else if hy : x = b then p.2.1 else p.2.2 ⟨x, hx, hy⟩
  left_inv F := by grind
  right_inv := fun ⟨u, v, G⟩ => by simp [hab.symm]; grind

theorem sum_boolFunctionWeight_eq_four_mul_fixed
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (f : α → Bool → ℝ)
    (ha : ∀ z, f a z = 1) (hb : ∀ z, f b z = 1) (ba bb : Bool) :
    (∑ F : α → Bool, ∏ x : α, f x (F x)) =
      4 * (∑ G : LoopChoiceRest α a b → Bool,
        ∏ x : α, f x ((loopChoiceSplitEquiv a b hab).symm (ba, bb, G) x)) := by
  have hweight (u v : Bool) (G : LoopChoiceRest α a b → Bool) :
      (∏ x : α, f x ((loopChoiceSplitEquiv a b hab).symm (u, v, G) x)) =
        ∏ x : α, f x ((loopChoiceSplitEquiv a b hab).symm (ba, bb, G) x) :=
    prod_congr rfl fun x _ => by
      by_cases hxa : x = a
      · grind
      by_cases hxb : x = b
      · grind
      simp [loopChoiceSplitEquiv, hxa, hxb]
  rw [← (loopChoiceSplitEquiv a b hab).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hweight]
  ring

/-- For a configuration with `U = 1`, fixing the two vertical loop directions to
downward leaves exactly one quarter of its equal-weight orientation assignments.
Every such assignment lies in the six-vertex sector `|ω| = N/2 - 1`. -/
theorem uOne_orientedLoopSum_le_four_mul_sectorSum
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (lam : ℝ)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A)
    (hU : rcVerticalWinding hN hM j A = 1) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
      orientedLoopWeight lam x.val (rcSmoothing A) x.property) ≤
      4 * (∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2,
        smoothingWeight lam ω (rcSmoothing A)) := by
  classical
  let s := rcSmoothing A
  let ω₀ := checkerArrows N M
  let h₀ := checkerArrows_compatible hN hM s
  obtain ⟨q₁, q₂, hqne, hchar, hv₁eq, hv₂eq⟩ :=
    PottsDiscontinuity.TorusTopology.U_one_vertical_loop_structure hN hM j A hU
  let choices (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :=
    (loopChoiceSplitEquiv q₁ q₂ hqne).symm (false, true, G)
  let arrow G := orientArrows ω₀ s h₀ (choices G)
  have hsector G : (arrow G).absUp + 1 = N / 2 := by
    let hG := orientArrows_compatible ω₀ s h₀ (choices G)
    have hterm (q : Loop hN hM s) :
        loopVertical (arrow G) s hG j (loopReorientEquiv ω₀ (arrow G) s h₀ hG q) =
          -(if q = q₁ then 1 else 0) - (if q = q₂ then 1 else 0) := by
      rw [loopVertical_reorient, loopOrientation_orientArrows]
      by_cases hq₁' : q = q₁
      · subst hq₁'; simpa [choices, loopChoiceSplitEquiv, hqne] using hv₁eq
      by_cases hq₂' : q = q₂
      · subst hq₂'; simpa [choices, loopChoiceSplitEquiv, hq₁'] using hv₂eq
      simp [show loopVertical ω₀ s h₀ j q = 0 by grind, hq₁', hq₂']
    have hflux := sum_loopVertical (arrow G) s hG j
    rw [← (loopReorientEquiv ω₀ (arrow G) s h₀ hG).sum_comp] at hflux
    simp [hterm, sum_sub_distrib] at hflux
    omega
  have hmapinj : Function.Injective arrow := fun G H hGH => by
    have hchoiceEq : choices G = choices H := by
      simpa [orientationEquiv, choices, arrow, loopOrientation_orientArrows] using congrArg (orientationEquiv ω₀ s h₀)
        (Subtype.ext hGH : (⟨arrow G, orientArrows_compatible ω₀ s h₀ (choices G)⟩ :
          {ω : ArrowConfig N M // CompatibleConfig ω s}) = ⟨arrow H, orientArrows_compatible ω₀ s h₀ (choices H)⟩)
    exact congrArg (·.2.2) ((loopChoiceSplitEquiv q₁ q₂ hqne).symm.injective hchoiceEq)
  calc
    _ = ∑ F : Loop hN hM s → Bool, chosenLoopWeight lam hN hM A F :=
      Fintype.sum_equiv (orientationEquiv ω₀ s h₀) _ _ fun x =>
        orientedLoopWeight_eq_chosenLoopWeight lam hN hM A x.val x.property
    _ = 4 * (∑ G, chosenLoopWeight lam hN hM A (choices G)) :=
      sum_boolFunctionWeight_eq_four_mul_fixed q₁ q₂ hqne (fun q b => Real.exp (lam * (if b then
        loopRotationNumber ω₀ s h₀ q else -loopRotationNumber ω₀ s h₀ q : ℤ)))
        (by simp [show loopRotationNumber ω₀ s h₀ q₁ = 0 from hnonzero q₁ (Or.inl (by grind))]) (by simp [show loopRotationNumber ω₀ s h₀ q₂ = 0 from hnonzero q₂ (Or.inl (by grind))]) _ _
    _ = 4 * ∑ ω ∈ univ.map ⟨arrow, hmapinj⟩, smoothingWeight lam ω s := by
      rw [sum_map]
      congr 1
      refine sum_congr rfl fun G _ => ?_
      rw [Function.Embedding.coeFn_mk, ← orientedLoopWeight_eq_smoothingWeight lam _ s (orientArrows_compatible ω₀ s h₀ (choices G)),
        orientedLoopWeight_eq_chosenLoopWeight, loopOrientation_orientArrows]
    _ ≤ _ := by
      gcongr <;> simp [subset_iff, hsector, smoothingWeight_nonneg]

/-- A six-vertex sector of deficit `r` lies inside the smoothing sum with `U ≥ r`.
This is the formal counting inclusion used for Corollary 3.13(iii). -/
theorem sixVertexSector_le_verticalUSmoothingSum (hN : Even N) (hM : Even M)
    (qval : ℝ) (hq : 4 < qval) (j : Fin M) (r : ℕ) :
    Z6Vr (Real.sqrt (2 + Real.sqrt qval)) N M r ≤
      (∑ s : {s : Smoothing N M //
          r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
        ∑ ω : ArrowConfig N M, smoothingWeight
          (Real.arcosh (Real.sqrt qval / 2)) ω s.val) := by
  rw [← sum_smoothingWeight_eq_Z6Vr_sqrt qval hq r, ← sum_subtype (univ.filter fun s : Smoothing N M =>
    r ≤ rcVerticalWinding hN hM j (smoothingRC s)) (by simp)
    fun s => ∑ ω, smoothingWeight _ ω s, sum_comm (t := (univ : Finset (ArrowConfig N M)))]
  refine le_trans (sum_congr rfl fun ω hω => ?_).le (sum_le_sum_of_subset_of_nonneg (filter_subset _ univ)
    fun ω _ _ => sum_nonneg fun s _ => smoothingWeight_nonneg (Real.arcosh (Real.sqrt qval / 2)) ω s)
  refine (sum_subset (filter_subset _ _) fun s _ hs => ?_).symm
  by_contra hne
  exact hs (mem_filter.2 ⟨mem_univ _, sector_le_rcVerticalWinding hN hM j _ ω (by
    simpa using not_imp_comm.1 (smoothingWeight_eq_zero_of_not_compatible _ ω s) hne) (mem_filter.1 hω).2⟩)

section
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (i : Fin N) (j : Fin M)
include hq
/-- Corollary 3.13(ii), conditional only on the two homological turn
classifications (discharged in `corollary_313_ii_final`). The corrected vertical two-loop
structure is imported from `TorusTopology.UnitWindingStructure`. -/
theorem corollary_313_ii (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    (∑ A : {A : RCConfig N M // rcVerticalWinding hN hM j A = 1},
      torusCorrectedRCWeight hN hM i j q A.val) ≤
      4 * torusNormalization q N M *
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
  rw [sum_congr rfl fun A _ => torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq A.1
    (hturn _).1 (hturn _).2, ← mul_sum, mul_comm 4, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (torusNormalization_pos q N M).le
  have h (A : {A // rcVerticalWinding hN hM j A = 1}) := uOne_orientedLoopSum_le_four_mul_sectorSum hN hM i j
    A.val (Real.arcosh (Real.sqrt q.val / 2)) (hturn A.val).2 A.property
  refine (sum_le_sum fun A _ => h A).trans ?_
  rw [← mul_sum, ← sum_smoothingWeight_eq_Z6Vr_sqrt q.val hq 1, sum_comm (t := (univ : Finset (Smoothing N M))),
    ← (rcSmoothingEquiv N M).sum_comp, ← sum_subtype (univ.filter fun A : RCConfig N M =>
      rcVerticalWinding hN hM j A = 1) (by simp) fun A => ∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2,
        smoothingWeight _ ω (rcSmoothing A)]
  gcongr
  exact sum_le_univ_sum_of_nonneg fun A => sum_nonneg fun ω _ => smoothingWeight_nonneg (Real.arcosh (Real.sqrt q.val / 2)) ω _

/-- Corollary 3.13(iii), conditional on the two homological turn classifications
(discharged in `corollary_313_iii_final`). -/
theorem corollary_313_iii (r : ℕ)
    (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    torusNormalization q N M * Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      ∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        torusCorrectedRCWeight hN hM i j q A.val := by
  rw [Fintype.sum_equiv (Equiv.subtypeEquiv (q := fun s => r ≤ rcVerticalWinding hN hM j (smoothingRC s)) (rcSmoothingEquiv N M) fun A => by simp [rcSmoothingEquiv]) _
    (fun s => torusCorrectedRCWeight hN hM i j q (smoothingRC s.val)) fun A => by simp [rcSmoothingEquiv]]
  refine (mul_le_mul_of_nonneg_left (sixVertexSector_le_verticalUSmoothingSum hN hM q.val hq j r)
    (torusNormalization_pos q N M).le).trans_eq ?_
  rw [mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq _ (hturn _).1 (hturn _).2,
    sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight, rcSmoothing_smoothingRC]
end

end PottsDiscontinuity.Torus
