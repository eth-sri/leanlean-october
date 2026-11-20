module

public import PottsDiscontinuity.Torus.CorrectedRCWeight
public import PottsDiscontinuity.Torus.LoopRotationNumber
public import PottsDiscontinuity.Torus.OrientationEquiv
public import PottsDiscontinuity.Torus.Parameters
public import PottsDiscontinuity.TorusLoops.WindingClusterCount

/-!
# Turning weights of oriented loop configurations

The source weight is the exponential of the sum of oriented loop turns. The two
homological turning classifications are explicit premises here; they are proved in
`TorusTopology/ZeroWindingTurning.lean` and `TorusTopology/NonzeroWindingTurning.lean`
and discharged in `Torus/Corollary313Final.lean`. No theorem in this file claims them.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
open PottsDiscontinuity.TorusLoops
open Classical

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The turning classification for zero homological winding, stated on the torus loop carrier
`Loop hN hM (rcSmoothing A)`: every such loop has rotation number `±1`. It is proved by
`TorusTopology.loopRotationNumber_eq_pm_one_of_zero_winding`. -/
def ZeroWindingTurnPremise (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (A : RCConfig N M) : Prop :=
  ∀ q : Loop hN hM (rcSmoothing A),
    loopVertical j q = 0 →
    loopSum (horizontalCross i) q = 0 →
    loopRotationNumber q = 1 ∨
      loopRotationNumber q = -1

/-- The turning classification for nonzero homological winding, stated on the torus loop
carrier `Loop hN hM (rcSmoothing A)`: every such loop has rotation number `0`. It is proved by
`TorusTopology.loopRotationNumber_eq_zero_of_nonzero_winding`. -/
def NonzeroWindingTurnPremise (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (A : RCConfig N M) : Prop :=
  ∀ q : Loop hN hM (rcSmoothing A),
    (loopVertical j q ≠ 0 ∨
      loopSum (horizontalCross i) q ≠ 0) →
    loopRotationNumber q = 0

/-- Product of the exponential full-turn weights of all oriented loops. -/
noncomputable def orientedLoopWeight (lam : ℝ) {ω : ArrowConfig N M}
    {s : Smoothing N M} (h : CompatibleConfig ω s) : ℝ :=
  ∏ q, Real.exp (lam * (loopRotationNumber (s := s) (h := h) q))

/-- Loop-factor product for an explicit Boolean choice of each canonical loop direction. -/
noncomputable def chosenLoopWeight (lam : ℝ) {hN : Even N} {hM : Even M}
    {A : RCConfig N M} (F : Loop hN hM (rcSmoothing A) → Bool) : ℝ :=
  ∏ q,
    Real.exp (lam * (if F q then
      loopRotationNumber q else
      -loopRotationNumber q))

/-- The exponential loop weight agrees with the local turn product. -/
theorem orientedLoopWeight_eq_smoothingWeight (lam : ℝ) {ω : ArrowConfig N M}
    (s : Smoothing N M) (h : CompatibleConfig ω s) :
    orientedLoopWeight lam (ω := ω) (s := s) h = smoothingWeight lam ω s := by
  unfold orientedLoopWeight
  rw [← Real.exp_sum]
  have hsum :
      (∑ q,
        lam * (loopRotationNumber (s := s) (h := h) q)) =
      lam / 4 * (∑ q, (loopTurn (s := s) (h := h) q : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [loopTurn_eq_four_mul_rotationNumber]
    push_cast
    ring
  rw [hsum]
  have hturn :
      (∑ q, loopTurn (s := s) (h := h) q : ℝ) =
        (totalQuarterTurn ω s) := by
    exact_mod_cast (sum_loopTurn ω s h)
  rw [hturn]
  exact (smoothingWeight_eq_exp h lam).symm

/-- Reorientation identifies the cyclic-loop weight with the Boolean loop-factor product. -/
theorem orientedLoopWeight_eq_chosenLoopWeight (lam : ℝ) (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (ω : ArrowConfig N M)
    (h : CompatibleConfig ω (rcSmoothing A)) :
    orientedLoopWeight lam (ω := ω) (s := (rcSmoothing A)) h =
      chosenLoopWeight lam (hN := hN) (hM := hM) (A := A)
        (loopOrientation (checkerArrows N M) (rcSmoothing A)
          (checkerArrows_compatible hN hM (rcSmoothing A)) (ω := ω) h) := by
  classical
  unfold orientedLoopWeight chosenLoopWeight
  rw [← (loopReorientEquiv _ ω (rcSmoothing A) (checkerArrows_compatible hN hM (rcSmoothing A)) h).prod_comp]
  grind [loopRotationNumber_reorient]

/-- Summing the oriented loop weights gives one factor `2` per winding loop and
one factor `sqrt q` per zero-winding loop. The two global turn classifications are
explicit premises in the theorem signature. -/
theorem sum_chosenLoopWeight_eq_loopFactors (lam qval : ℝ)
    (hLam : Real.exp lam + Real.exp (-lam) = Real.sqrt qval)
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (hzero : ZeroWindingTurnPremise hN hM i j A)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A) :
    (∑ F,
      chosenLoopWeight lam (hN := hN) (hM := hM) (A := A) F) =
      2 ^ windingLoopCount hN hM i j A *
        Real.sqrt qval ^ (rcLoopCount hN hM A - windingLoopCount hN hM i j A) := by
  classical
  let W := windingLoopSet hN hM i j A
  let rot (q : Loop hN hM (rcSmoothing A)) :=
    loopRotationNumber q
  have hp :
      (∑ F : Loop hN hM (rcSmoothing A) → Bool,
        ∏ q,
          Real.exp (lam * (if F q then rot q else -rot q))) =
      ∏ q,
        ∑ b : Bool, Real.exp (lam * (if b then rot q else -rot q)) := by
    exact (Finset.sum_prod_piFinset (Finset.univ : Finset Bool) (fun q : Loop hN hM (rcSmoothing A) => fun b => Real.exp (lam * (if b then rot q else -rot q))))
  have hlocal (q : Loop hN hM (rcSmoothing A)) :
      (∑ b : Bool, Real.exp (lam * (if b then rot q else -rot q))) =
        if q ∈ W then 2 else Real.sqrt qval := by
    by_cases hW : q ∈ W
    · have hr := hnonzero q (by simpa [W, windingLoopSet] using hW)
      change rot q = 0 at hr
      simp [*]
    · have hnotwind :
          ¬ (loopVertical j q ≠ 0 ∨
              loopSum (horizontalCross i) q ≠ 0) := by
        simpa [W, windingLoopSet] using hW
      rcases hzero q (by grind) (by grind) with hr | hr
      · change rot q = 1 at hr
        simp [*]
      · change rot q = -1 at hr
        simp [ite_eq_right hW, add_comm, *]
  unfold chosenLoopWeight
  rw [hp]
  simp_rw [hlocal]
  have hsplit :
      (Finset.univ.filter fun q : Loop hN hM (rcSmoothing A) => q ∈ W).card +
          (Finset.univ.filter fun q : Loop hN hM (rcSmoothing A) => q ∉ W).card =
        Fintype.card (Loop hN hM (rcSmoothing A)) := card_filter_add_card_filter_not fun q => q ∈ W
  have hfilter :
      Finset.univ.filter (fun q : Loop hN hM (rcSmoothing A) => q ∈ W) = W := by
    simp
  have hcardcomp :
      (Finset.univ.filter fun q : Loop hN hM (rcSmoothing A) => q ∉ W).card =
        Fintype.card (Loop hN hM (rcSmoothing A)) - W.card := by
    grind
  simp [Finset.prod_ite, Finset.prod_const, W, windingLoopCount, rcLoopCount, loopCount, *]

/-- The compatible arrow fields are exactly the Boolean loop orientations, so their
oriented weight sum is the same product of loop factors. -/
theorem sum_compatibleOrientedLoopWeight_eq_loopFactors (lam qval : ℝ)
    (hLam : Real.exp lam + Real.exp (-lam) = Real.sqrt qval)
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (hzero : ZeroWindingTurnPremise hN hM i j A)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
      orientedLoopWeight lam x.property) =
      2 ^ windingLoopCount hN hM i j A *
        Real.sqrt qval ^ (rcLoopCount hN hM A - windingLoopCount hN hM i j A) := by
  classical
  calc
    _ = ∑ F, chosenLoopWeight lam F := by
      refine Fintype.sum_equiv (orientationEquiv _ (rcSmoothing A) (checkerArrows_compatible hN hM (rcSmoothing A))) _ _ ?_
      solve_by_elim [orientedLoopWeight_eq_chosenLoopWeight]
    _ = _ := sum_chosenLoopWeight_eq_loopFactors lam qval hLam hN hM i j A hzero hnonzero

/-- A failed compatibility condition forces a zero local product because one vertex
has no allowed smoothing. -/
theorem smoothingWeight_eq_zero_of_not_compatible (lam : ℝ) (ω : ArrowConfig N M)
    (s : Smoothing N M) (h : ¬ CompatibleConfig ω s) : smoothingWeight lam ω s = 0 := by
  classical
  obtain ⟨v, hv⟩ := not_forall.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  simp [turnWeight, hv]

/-- A smoothing contributes the sum of its compatible oriented-loop weights to the
six-vertex smoothing expansion. Incompatible arrow/smoothing pairs have zero local weight. -/
theorem sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight (lam : ℝ)
    (s : Smoothing N M) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s},
      orientedLoopWeight lam x.property) =
      ∑ ω, smoothingWeight lam ω s := by
  classical
  have hsub :
      (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s}, smoothingWeight lam x.val s) =
        ∑ ω, smoothingWeight lam ω s := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun ω : ArrowConfig N M => CompatibleConfig ω s) (by simp) (fun ω => smoothingWeight lam ω s), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hc : CompatibleConfig ω s
    · grind
    · simp [smoothingWeight_eq_zero_of_not_compatible lam ω s hc]
  grind [orientedLoopWeight_eq_smoothingWeight]

/-- Lemma 3.10 in the corrected-weight form: the corrected RC weight is the
normalization times the sum of all compatible oriented-loop weights. -/
theorem torusCorrectedRCWeight_eq_normalization_mul_orientedSum
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (q : Set.Ici 1) (hq : 4 < q.val) {A : RCConfig N M}
    (hzero : ZeroWindingTurnPremise hN hM i j A)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A) :
    torusCorrectedRCWeight hN hM i j q A =
      torusNormalization q N M *
        (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
          orientedLoopWeight (Real.arcosh (Real.sqrt q.val / 2)) x.property) := by
  calc
    _ =
        torusNormalization q N M *
          2 ^ windingLoopCount hN hM i j A *
            Real.sqrt q.val ^ (rcLoopCount hN hM A - windingLoopCount hN hM i j A) :=
      torusCorrectedRCWeight_eq_loopFactors hN hM i j q A
    _ = _ := by
      rw [sum_compatibleOrientedLoopWeight_eq_loopFactors
        _ q.val (exp_add_exp_neg_arcosh q.val hq) hN hM i j A hzero hnonzero]
      ring

/-- Corollary 3.13(i), conditional only on the two homological turning classifications;
the unconditional form is `corollary_313_i_final` in `Torus/Corollary313Final.lean`. -/
theorem corollary_313_i
    (hN : Even N) (hM : Even M) (q : Set.Ici 1) (hq : 4 < q.val)
    (i : Fin N) (j : Fin M)
    (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    (∑ A, torusCorrectedRCWeight hN hM i j q A) =
      torusNormalization q N M *
        Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := by
  classical
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  calc
    _ = ∑ A,
          torusNormalization q N M *
            (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
              orientedLoopWeight lam x.property) := by
      grind [torusCorrectedRCWeight_eq_normalization_mul_orientedSum]
    _ = torusNormalization q N M *
          ∑ A,
            ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
              orientedLoopWeight lam x.property := by
      rw [Finset.mul_sum]
    _ = torusNormalization q N M *
          ∑ s,
            ∑ x,
              orientedLoopWeight lam x.property := by
      exact congrArg _ (Fintype.sum_equiv (rcSmoothingEquiv N M) _ _ (by intro A; rfl))
    _ = torusNormalization q N M *
          ∑ s, ∑ ω, smoothingWeight lam ω s := congrArg (fun x => torusNormalization q N M * x) (sum_congr rfl fun s x => sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight lam s)
    _ = torusNormalization q N M *
          ∑ ω, ∑ s, smoothingWeight lam ω s := by
      rw [Finset.sum_comm]
    _ = _ := by
      rw [sum_smoothingWeight_eq_Z6V_sqrt q.val hq]

end PottsDiscontinuity.Torus
