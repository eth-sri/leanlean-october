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

/-- Fixing independent fair loop orientations costs a factor two for each pin. -/
private theorem sum_choice_pins {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (b : α → Bool) (f : α → Bool → ℝ) (hf : ∀ x ∈ S, ∀ z, f x z = 1) :
    (∑ F : α → Bool, ∏ x, f x (F x)) =
      (2 : ℝ) ^ S.card * ∑ F : α → Bool with ∀ x ∈ S, F x = b x, ∏ x, f x (F x) := by
  classical
  let g (x : α) (z : Bool) := if x ∈ S ∧ z ≠ b x then 0 else f x z
  have hg (F : α → Bool) : (∏ x, g x (F x)) = if ∀ x ∈ S, F x = b x then ∏ x, f x (F x) else 0 := by
    split
    · grind
    · rename_i h
      push Not at h
      obtain ⟨x, hx, hf⟩ := h
      exact prod_eq_zero (mem_univ x) (by grind)
  rw [← Fintype.prod_sum]
  have hsum (x : α) : (∑ z, f x z) = (if x ∈ S then (2 : ℝ) else 1) * ∑ z, g x z := by
    by_cases hx : x ∈ S
    · cases hb : b x <;> simp [g, hx, hf x hx]
    · simp [g, hx]
  simp_rw [hsum]
  rw [prod_mul_distrib, Fintype.prod_sum, sum_filter]
  simp_rw [hg]
  simp

/-- In the unit-winding sector the two vertical orientations can be pinned
    downwards, with all other loop colours left arbitrary. -/
private theorem uOne_orientedLoopSum_le_four_mul_sectorSum
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (lam : ℝ) (hnonzero : NonzeroWindingTurnPremise hN hM i j A)
    (hU : rcVerticalWinding hN hM j A = 1) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
      orientedLoopWeight lam x.val (rcSmoothing A) x.property) ≤
      4 * (∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2,
        smoothingWeight lam ω (rcSmoothing A)) := by
  classical
  let s := rcSmoothing A
  let ω₀ := checkerArrows N M
  let h₀ := checkerArrows_compatible hN hM s
  obtain ⟨u, v, huv, hwind, hu, hv⟩ :=
    PottsDiscontinuity.TorusTopology.U_one_vertical_loop_structure hN hM j A hU
  change loopVertical ω₀ s h₀ j u = 1 at hu
  change loopVertical ω₀ s h₀ j v = -1 at hv
  let S : Finset (Loop hN hM s) := {u, v}
  let b (x : Loop hN hM s) := if x = u then false else true
  let T := (univ : Finset (Loop hN hM s → Bool)).filter (fun F => ∀ x ∈ S, F x = b x)
  let e := orientationEquiv ω₀ s h₀
  let em : (Loop hN hM s → Bool) ↪ ArrowConfig N M := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hrot (x) (hx : x ∈ S) : loopRotationNumber ω₀ s h₀ x = 0 :=
    hnonzero x (Or.inl ((hwind x).mpr (by simpa [S] using hx)))
  have hsect (F) (hF : F ∈ T) : (em F).absUp + 1 = N / 2 := by
    have hp := (mem_filter.mp hF).2
    have hFu : F u = false := by simpa [b] using hp u (by simp [S])
    have hFv : F v = true := by simpa [b, huv.symm] using hp v (by simp [S])
    let w := orientArrows ω₀ s h₀ F
    let hw := orientArrows_compatible ω₀ s h₀ F
    let er := loopReorientEquiv ω₀ w s h₀ hw
    have hterm (x : Loop hN hM s) : loopVertical w s hw j (er x) =
        (if x = u then (-1 : ℤ) else 0) + (if x = v then -1 else 0) := by
      rw [show er = loopReorientEquiv ω₀ w s h₀ hw from rfl,
        loopVertical_reorient, loopOrientation_orientArrows]
      by_cases hxu : x = u
      · simp [hxu, hu, hFu, huv]
      by_cases hxv : x = v
      · simp [hxv, hv, hFv, huv.symm]
      have hz : loopVertical ω₀ s h₀ j x = 0 := not_not.mp fun h => (hwind x).mp h |>.elim hxu hxv
      simp [hxu, hxv, hz]
    have hf := sum_loopVertical w s hw j
    rw [← er.sum_comp (loopVertical w s hw j)] at hf
    simp_rw [hterm, sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hf
    change w.absUp + 1 = N / 2
    omega
  let f (x : Loop hN hM s) (z : Bool) := Real.exp (lam *
    (if z then loopRotationNumber ω₀ s h₀ x else -loopRotationNumber ω₀ s h₀ x : ℤ))
  have hpins := sum_choice_pins S b f (fun x hx z => by simp [f, hrot x hx])
  have hcard : S.card = 2 := by simp [S, huv]
  rw [hcard, show (2 : ℝ) ^ 2 = 4 by norm_num] at hpins
  have horient : (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s}, orientedLoopWeight lam x.val s x.property) =
      ∑ F : Loop hN hM s → Bool, chosenLoopWeight lam hN hM A F :=
    Fintype.sum_equiv e _ _ (fun x => orientedLoopWeight_eq_chosenLoopWeight lam hN hM A x.val x.property)
  rw [horient]
  change (∑ F : Loop hN hM s → Bool, ∏ x, f x (F x)) ≤ _
  rw [hpins]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc
    _ = ∑ F ∈ T, smoothingWeight lam (em F) s := by
      refine sum_congr rfl fun F _ => ?_
      change chosenLoopWeight lam hN hM A F = smoothingWeight lam (orientArrows ω₀ s h₀ F) s
      rw [← orientedLoopWeight_eq_smoothingWeight _ _ _ (orientArrows_compatible ω₀ s h₀ F),
        orientedLoopWeight_eq_chosenLoopWeight, loopOrientation_orientArrows]
    _ = ∑ ω ∈ T.map em, smoothingWeight lam ω s := (sum_map T em (fun ω => smoothingWeight lam ω s)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (by intro ω hω; obtain ⟨F, hF, rfl⟩ := mem_map.mp hω; simp [hsect F hF])
      (fun ω _ _ => smoothingWeight_nonneg lam ω s)

/-- Nonzero weights in a six-vertex sector require enough vertical winding. -/
private theorem sixVertexSector_le_verticalUSmoothingSum (hN : Even N) (hM : Even M)
    (qval : ℝ) (hq : 4 < qval) (j : Fin M) (r : ℕ) :
    Z6Vr (Real.sqrt (2 + Real.sqrt qval)) N M r ≤
      ∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        ∑ ω : ArrowConfig N M, smoothingWeight (Real.arcosh (Real.sqrt qval / 2)) ω (rcSmoothing A.val) := by
  classical
  let lam := Real.arcosh (Real.sqrt qval / 2)
  let P (A : RCConfig N M) := r ≤ rcVerticalWinding hN hM j A
  let W (ω : ArrowConfig N M) (A : RCConfig N M) := smoothingWeight lam ω (rcSmoothing A)
  calc
    _ = ∑ ω : ArrowConfig N M with ω.absUp + r = N / 2, ∑ s : Smoothing N M, smoothingWeight lam ω s :=
      (sum_smoothingWeight_eq_Z6Vr_sqrt qval hq r).symm
    _ = ∑ ω : ArrowConfig N M with ω.absUp + r = N / 2, ∑ A, W ω A :=
      sum_congr rfl fun ω _ => ((rcSmoothingEquiv N M).sum_comp (smoothingWeight lam ω)).symm
    _ = ∑ ω : ArrowConfig N M with ω.absUp + r = N / 2, ∑ A with P A, W ω A := by
      refine sum_congr rfl fun ω hω => ?_
      rw [sum_filter]
      refine sum_congr rfl fun A _ => ?_
      split
      · rfl
      · rename_i hP
        apply smoothingWeight_eq_zero_of_not_compatible
        exact fun hc => hP (sector_le_rcVerticalWinding hN hM j A ω hc (mem_filter.mp hω).2)
    _ ≤ ∑ A with P A, ∑ ω : ArrowConfig N M, W ω A := by
      rw [sum_comm]
      exact sum_le_sum fun A _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun ω _ _ =>
        smoothingWeight_nonneg _ _ _)
    _ = _ := Finset.sum_subtype (univ.filter P) (by simp [P]) _

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
  let sector (s : Smoothing N M) :=
    ∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2, smoothingWeight lam ω s
  rw [sum_corrected_eq_normalization (fun A : {A : RCConfig N M // P A} => A.val) hN hM q hq i j hturn,
    mul_comm (4 : ℝ) (torusNormalization q N M), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (torusNormalization_pos q N M).le
  calc
    _ ≤ 4 * ∑ A : {A : RCConfig N M // P A}, sector (rcSmoothing A.val) := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun A _ => uOne_orientedLoopSum_le_four_mul_sectorSum
        hN hM i j A.val lam (hturn A.val).2 A.property
    _ ≤ 4 * Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ ∑ A : RCConfig N M, sector (rcSmoothing A) :=
          sum_le_sum_of_injOn Subtype.val Subtype.val_injective.injOn (subset_univ _)
            (fun _ _ => le_rfl) (fun _ _ _ => sum_nonneg (fun _ _ => smoothingWeight_nonneg _ _ _))
        _ = ∑ s, sector s := (rcSmoothingEquiv N M).sum_comp sector
        _ = _ := sum_comm.trans (sum_smoothingWeight_eq_Z6Vr_sqrt q.val hq 1)

/-- Corollary 3.13(iii), conditional on the two homological turn classifications
(discharged in `corollary_313_iii_final`). -/
theorem corollary_313_iii (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (i : Fin N) (j : Fin M) (r : ℕ)
    (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    torusNormalization q N M * Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      ∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        torusCorrectedRCWeight hN hM i j q A.val := by
  rw [sum_corrected_eq_normalization (fun A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A} => A.val)
    hN hM q hq i j hturn]
  simp_rw [sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight]
  exact mul_le_mul_of_nonneg_left (sixVertexSector_le_verticalUSmoothingSum hN hM q.val hq j r)
    (torusNormalization_pos q N M).le

end PottsDiscontinuity.Torus
