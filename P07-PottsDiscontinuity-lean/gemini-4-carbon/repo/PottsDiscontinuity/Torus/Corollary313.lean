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

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

private abbrev LoopChoiceRest (α : Type*) (a b : α) := {x : α // x ≠ a ∧ x ≠ b}

private noncomputable def loopChoiceSplitEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    (α → Bool) ≃ Bool × (Bool × (LoopChoiceRest α a b → Bool)) where
  toFun F := (F a, F b, fun x => F x.val)
  invFun p x := if hx : x = a then p.1 else if hy : x = b then p.2.1 else p.2.2 ⟨x, hx, hy⟩
  left_inv F := funext fun x => by by_cases hx : x = a <;> by_cases hy : x = b <;> simp_all
  right_inv := fun ⟨ba, bb, G⟩ => Prod.ext (by simp) (Prod.ext (by simp [hab.symm]) (funext fun x => by simp [x.2.1, x.2.2]))

private theorem uOne_orientedLoopSum_le_four_mul_sectorSum
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (lam : ℝ) (hnonzero : NonzeroWindingTurnPremise hN hM i j A)
    (hU : rcVerticalWinding hN hM j A = 1) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
      orientedLoopWeight lam x.val (rcSmoothing A) x.property) ≤
      4 * (∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2,
        smoothingWeight lam ω (rcSmoothing A)) := by
  classical
  let s := rcSmoothing A; let ω₀ := checkerArrows N M; let h₀ := checkerArrows_compatible hN hM s
  obtain ⟨q₁, q₂, hqne, hchar, hv₁eq, hv₂eq⟩ :=
    PottsDiscontinuity.TorusTopology.U_one_vertical_loop_structure hN hM j A hU
  have hrot₁ : loopRotationNumber ω₀ s h₀ q₁ = 0 := hnonzero q₁ (.inl (by dsimp [ω₀, s, h₀]; omega))
  have hrot₂ : loopRotationNumber ω₀ s h₀ q₂ = 0 := hnonzero q₂ (.inl (by dsimp [ω₀, s, h₀]; omega))
  let split := loopChoiceSplitEquiv q₁ q₂ hqne
  let choices (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) := split.symm (false, true, G)
  let arrow (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) := orientArrows ω₀ s h₀ (choices G)
  have hsector (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) : (arrow G).absUp + 1 = N / 2 := by
    let hG := orientArrows_compatible ω₀ s h₀ (choices G)
    have hterm (q : Loop hN hM s) :
        loopVertical (arrow G) s hG j (loopReorientEquiv ω₀ (arrow G) s h₀ hG q) =
          (if q = q₁ then -1 else 0) + (if q = q₂ then -1 else 0) := by
      rw [loopVertical_reorient, loopOrientation_orientArrows]
      by_cases h1 : q = q₁
      · subst q; simp [choices, split, loopChoiceSplitEquiv, hqne, show loopVertical ω₀ s h₀ j q₁ = 1 from hv₁eq]
      · by_cases h2 : q = q₂
        · subst q; simp [choices, split, loopChoiceSplitEquiv, h1, show loopVertical ω₀ s h₀ j q₂ = -1 from hv₂eq]
        · have hv0 : loopVertical ω₀ s h₀ j q = 0 := by
            by_contra hnz; exact (hchar q).mp hnz |>.elim h1 h2
          simp [h1, h2, hv0]
    have hflux := sum_loopVertical (arrow G) s hG j
    rw [← (loopReorientEquiv ω₀ (arrow G) s h₀ hG).sum_comp, Finset.sum_congr rfl fun q _ => hterm q,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at hflux
    simp only [Finset.mem_univ, ↓reduceIte] at hflux
    obtain ⟨k, hk⟩ := hN; omega
  let f (q : Loop hN hM s) (b : Bool) : ℝ :=
    Real.exp (lam * (if b then loopRotationNumber ω₀ s h₀ q else -loopRotationNumber ω₀ s h₀ q : ℤ))
  have hsplitSum : (∑ F : Loop hN hM s → Bool, chosenLoopWeight lam hN hM A F) =
      4 * ∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool, chosenLoopWeight lam hN hM A (choices G) := by
    change (∑ F : Loop hN hM s → Bool, ∏ q, f q (F q)) = 4 * ∑ G, ∏ q, f q (split.symm (false, true, G) q)
    have heq1 : (∑ F : Loop hN hM s → Bool, ∏ q, f q (F q)) =
        ∑ p : Bool × (Bool × (LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool)), ∏ q, f q (split.symm p q) :=
      Fintype.sum_equiv split _ _ fun F => by simp [split]
    rw [heq1]
    simp_rw [Fintype.sum_prod_type]
    have hw (u v : Bool) (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
        (∏ q, f q (split.symm (u, v, G) q)) = ∏ q, f q (split.symm (false, true, G) q) :=
      Finset.prod_congr rfl fun q _ => by
        by_cases h1 : q = q₁
        · subst q; simp [f, hrot₁]
        · by_cases h2 : q = q₂
          · subst q; simp [f, hrot₂]
          · simp [split, loopChoiceSplitEquiv, h1, h2]
    simp_rw [hw]; rw [Fintype.sum_bool, Fintype.sum_bool]; ring
  have hmapinj : Function.Injective arrow := fun G H hGH => by
    have hF := congrArg (orientationEquiv ω₀ s h₀)
      (Subtype.ext hGH : (⟨arrow G, orientArrows_compatible ω₀ s h₀ (choices G)⟩ : {ω // CompatibleConfig ω s}) =
        ⟨arrow H, orientArrows_compatible ω₀ s h₀ (choices H)⟩)
    have hc : choices G = choices H := by simpa [orientationEquiv, arrow, loopOrientation_orientArrows] using hF
    exact congrArg (fun p : Bool × (Bool × _) => p.2.2) (split.symm.injective hc)
  have horient : (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s}, orientedLoopWeight lam x.val s x.property) =
      ∑ F : Loop hN hM s → Bool, chosenLoopWeight lam hN hM A F :=
    Fintype.sum_equiv (orientationEquiv ω₀ s h₀) _ _ fun x => orientedLoopWeight_eq_chosenLoopWeight lam hN hM A x.val x.property
  rw [horient, hsplitSum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hGsum : (∑ G, chosenLoopWeight lam hN hM A (choices G)) = ∑ ω ∈ Finset.univ.map ⟨arrow, hmapinj⟩, smoothingWeight lam ω s := by
    rw [Finset.sum_map]; refine Finset.sum_congr rfl fun G _ => ?_
    calc chosenLoopWeight lam hN hM A (choices G)
        = orientedLoopWeight lam (arrow G) s (orientArrows_compatible ω₀ s h₀ (choices G)) := by
            symm; rw [orientedLoopWeight_eq_chosenLoopWeight, loopOrientation_orientArrows]
      _ = smoothingWeight lam (arrow G) s := orientedLoopWeight_eq_smoothingWeight lam (arrow G) s _
  rw [hGsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun ω hω => by obtain ⟨G, _, rfl⟩ := Finset.mem_map.mp hω; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsector G⟩)
    fun ω _ _ => smoothingWeight_nonneg lam ω s

/-- Corollary 3.13(ii), conditional only on the two homological turn
classifications (discharged in `corollary_313_ii_final`). The corrected vertical two-loop
structure is imported from `TorusTopology.UnitWindingStructure`. -/
theorem corollary_313_ii (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (i : Fin N) (j : Fin M)
    (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    (∑ A : {A : RCConfig N M // rcVerticalWinding hN hM j A = 1},
      torusCorrectedRCWeight hN hM i j q A.val) ≤
      4 * torusNormalization q N M *
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
  classical
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  let P (A : RCConfig N M) := rcVerticalWinding hN hM j A = 1
  let sectorSum (s : Smoothing N M) := ∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2, smoothingWeight lam ω s
  have h1 : (∑ A : {A : RCConfig N M // P A}, torusCorrectedRCWeight hN hM i j q A.val) =
      torusNormalization q N M * ∑ A : {A : RCConfig N M // P A},
        ∑ x : {ω // CompatibleConfig ω (rcSmoothing A.val)}, orientedLoopWeight lam x.val (rcSmoothing A.val) x.property := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun A _ =>
      torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq A.val (hturn A.val).1 (hturn A.val).2
  have h2 : (∑ A : {A // P A}, ∑ x : {ω // CompatibleConfig ω (rcSmoothing A.val)}, orientedLoopWeight lam x.val _ x.property) ≤
      4 * ∑ A : {A // P A}, sectorSum (rcSmoothing A.val) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun A _ =>
      uOne_orientedLoopSum_le_four_mul_sectorSum hN hM i j A.val lam (hturn A.val).2 A.property
  have h3 : (∑ A : {A // P A}, sectorSum (rcSmoothing A.val)) ≤ Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter P) (fun _ => by simp) (fun A => sectorSum (rcSmoothing A))]
    refine (Finset.sum_le_univ_sum_of_nonneg fun A => Finset.sum_nonneg fun _ _ => smoothingWeight_nonneg lam _ _).trans_eq ?_
    have heqA : (∑ A : RCConfig N M, sectorSum (rcSmoothing A)) = ∑ s : Smoothing N M, sectorSum s :=
      Fintype.sum_equiv (rcSmoothingEquiv N M) _ _ fun _ => rfl
    rw [heqA]; dsimp [sectorSum]; rw [Finset.sum_comm]
    exact sum_smoothingWeight_eq_Z6Vr_sqrt q.val hq 1
  have h4 := mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 4))) (torusNormalization_pos q N M).le
  change (∑ A : {A : RCConfig N M // P A}, torusCorrectedRCWeight hN hM i j q A.val) ≤ _
  rw [h1]; linarith

/-- Corollary 3.13(iii), conditional on the two homological turn classifications
(discharged in `corollary_313_iii_final`). -/
theorem corollary_313_iii (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (i : Fin N) (j : Fin M) (r : ℕ)
    (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    torusNormalization q N M * Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      ∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        torusCorrectedRCWeight hN hM i j q A.val := by
  classical
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  let U (s : Smoothing N M) := r ≤ rcVerticalWinding hN hM j (smoothingRC s)
  let g (ω : ArrowConfig N M) := ∑ s : Smoothing N M, if U s then smoothingWeight lam ω s else 0
  have hsec : Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      ∑ s : {s : Smoothing N M // U s}, ∑ ω : ArrowConfig N M, smoothingWeight lam ω s.val := by
    rw [← sum_smoothingWeight_eq_Z6Vr_sqrt (N := N) (M := M) q.val hq r]
    have heq (ω : ArrowConfig N M) (hω : ω ∈ Finset.univ.filter fun ω : ArrowConfig N M => ω.absUp + r = N / 2) :
        (∑ s : Smoothing N M, smoothingWeight lam ω s) = g ω :=
      Finset.sum_congr rfl fun s _ => by
        by_cases hU : U s
        · simp [hU]
        · simp only [hU, ↓reduceIte]
          by_contra hne
          have hc : CompatibleConfig ω s := by by_contra hn; exact hne (smoothingWeight_eq_zero_of_not_compatible lam ω s hn)
          exact hU (sector_le_rcVerticalWinding hN hM j (smoothingRC s) ω (by simpa using hc) (Finset.mem_filter.mp hω).2)
    rw [Finset.sum_congr rfl heq]
    refine (Finset.sum_le_univ_sum_of_nonneg fun ω => Finset.sum_nonneg fun s _ => by split_ifs; exact smoothingWeight_nonneg _ _ _; exact le_rfl).trans_eq ?_
    rw [← Finset.sum_subtype (Finset.univ.filter U) (fun _ => by simp) (fun s => ∑ ω, smoothingWeight lam ω s),
      Finset.sum_filter]
    change (∑ ω, ∑ s, if U s then smoothingWeight lam ω s else 0) = _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => by dsimp [U]; by_cases hU : r ≤ rcVerticalWinding hN hM j (smoothingRC s) <;> simp [hU]
  let e : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A} ≃ {s : Smoothing N M // U s} :=
    { toFun := fun x => ⟨rcSmoothing x.val, by simpa [U] using x.property⟩
      invFun := fun x => ⟨smoothingRC x.val, x.property⟩
      left_inv := fun _ => Subtype.ext (by simp)
      right_inv := fun _ => Subtype.ext (by simp) }
  have hsum : (∑ A : {A // r ≤ rcVerticalWinding hN hM j A}, torusCorrectedRCWeight hN hM i j q A.val) =
      torusNormalization q N M * ∑ s : {s // U s}, ∑ ω, smoothingWeight lam ω s.val := by
    have he : (∑ A : {A // r ≤ rcVerticalWinding hN hM j A}, torusCorrectedRCWeight hN hM i j q A.val) =
        ∑ s : {s // U s}, torusCorrectedRCWeight hN hM i j q (smoothingRC s.val) :=
      Fintype.sum_equiv e _ _ fun x => by simp [e]
    rw [he, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq (smoothingRC s.val)
      (hturn _).1 (hturn _).2]
    exact congrArg (torusNormalization q N M * ·) (by simpa using sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight lam (rcSmoothing (smoothingRC s.val)))
  rw [hsum]; exact mul_le_mul_of_nonneg_left hsec (torusNormalization_pos q N M).le

end PottsDiscontinuity.Torus
