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

abbrev LoopChoiceRest (α : Type*) (a b : α) :=
  {x : α // x ≠ a ∧ x ≠ b}

def loopChoiceSplitMap {α : Type*} (a b : α)
    (F : α → Bool) : Bool × (Bool × (LoopChoiceRest α a b → Bool)) :=
  (F a, F b, fun x => F x.val)

def loopChoiceMergeMap {α : Type*} [DecidableEq α] (a b : α)
    (p : Bool × (Bool × (LoopChoiceRest α a b → Bool))) : α → Bool :=
  fun x => if hx : x = a then p.1 else if hy : x = b then p.2.1
    else p.2.2 ⟨x, hx, hy⟩

noncomputable def loopChoiceSplitEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    (α → Bool) ≃ Bool × (Bool × (LoopChoiceRest α a b → Bool)) where
  toFun := loopChoiceSplitMap a b
  invFun := loopChoiceMergeMap a b
  left_inv F := by
    funext x
    by_cases hxa : x = a
    · subst x
      simp [loopChoiceSplitMap, loopChoiceMergeMap]
    · by_cases hxb : x = b
      · subst x
        simp [loopChoiceSplitMap, loopChoiceMergeMap, hxa]
      · simp [loopChoiceSplitMap, loopChoiceMergeMap, hxa, hxb]
  right_inv p := by
    rcases p with ⟨ba, bb, G⟩
    apply Prod.ext_iff.mpr
    constructor
    · simp [loopChoiceSplitMap, loopChoiceMergeMap]
    · apply Prod.ext_iff.mpr
      constructor
      · simp [loopChoiceSplitMap, loopChoiceMergeMap, hab.symm]
      · funext x
        simp [loopChoiceSplitMap, loopChoiceMergeMap, x.property.1, x.property.2]

@[simp] private theorem loopChoiceSplitEquiv_symm_apply {α : Type*} [Fintype α]
    [DecidableEq α] (a b : α) (hab : a ≠ b)
    (p : Bool × (Bool × (LoopChoiceRest α a b → Bool))) :
    (loopChoiceSplitEquiv hab).symm p = loopChoiceMergeMap a b p := rfl

private theorem sum_boolFunctionWeight_eq_four_mul_fixed
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (f : α → Bool → ℝ)
    (ha : ∀ z, f a z = 1) (hb : ∀ z, f b z = 1) (ba bb : Bool) :
    (∑ F : α → Bool, ∏ x, f x (F x)) =
      4 * (∑ G,
        ∏ x, f x ((loopChoiceSplitEquiv hab).symm (ba, bb, G) x)) := by
  classical
  let e := loopChoiceSplitEquiv hab
  have hweight (u v : Bool) (G : LoopChoiceRest α a b → Bool) :
      (∏ x, f x (e.symm (u, v, G) x)) =
        ∏ x, f x (e.symm (ba, bb, G) x) := by
    apply Finset.prod_congr rfl
    intro x _
    by_cases hxa : x = a
    · grind
    · by_cases hxb : x = b
      · grind
      · simp_all [e, loopChoiceSplitEquiv, loopChoiceMergeMap]
  calc
    _ = ∑ p,
          ∏ x, f x (e.symm p x) := by
      refine Fintype.sum_equiv e _ _ ?_
      simp
    _ = ∑ u, ∑ v,
          ∑ G,
            ∏ x, f x (e.symm (u, v, G) x) := by
      simp_rw [Fintype.sum_prod_type]
    _ = ∑ u, ∑ v,
          ∑ G,
            ∏ x, f x (e.symm (ba, bb, G) x) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      solve_by_elim [hweight]
    _ = _ := by
      grind [Fintype.sum_bool]

def downwardChoice (z : ℤ) : Bool := if z = 1 then false else true

private theorem downwardChoice_turn {z : ℤ} (hz : z = 1 ∨ z = -1) :
    (if downwardChoice z then z else -z) = -1 := by
  aesop

/-- For a configuration with `U = 1`, fixing the two vertical loop directions to
downward leaves exactly one quarter of its equal-weight orientation assignments.
Every such assignment lies in the six-vertex sector `|ω| = N/2 - 1`. -/
private theorem uOne_orientedLoopSum_le_four_mul_sectorSum
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (lam : ℝ)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A)
    (hU : rcVerticalWinding hN hM j A = 1) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
      orientedLoopWeight lam x.property) ≤
      4 * (∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2,
        smoothingWeight lam ω (rcSmoothing A)) := by
  classical
  let s := rcSmoothing A
  let ω₀ := checkerArrows N M
  let h₀ := checkerArrows_compatible hN hM s
  obtain ⟨q₁, q₂, hqne, hchar, hv₁eq, hv₂eq⟩ :=
    PottsDiscontinuity.TorusTopology.U_one_vertical_loop_structure hN hM j A hU
  let v₁ := loopVertical j q₁
  let v₂ := loopVertical j q₂
  have hv₁ : v₁ = 1 ∨ v₁ = -1 := Or.inl (by assumption)
  have hv₂ : v₂ = 1 ∨ v₂ = -1 := Or.inr (by assumption)
  have hv₁ne : v₁ ≠ 0 := by
    grind
  have hv₂ne : v₂ ≠ 0 := by
    grind
  have hrot₁ : loopRotationNumber q₁ = 0 := hnonzero q₁ (Or.inl hv₁ne)
  have hrot₂ : loopRotationNumber q₂ = 0 := hnonzero q₂ (Or.inl hv₂ne)
  let b₁ := downwardChoice v₁
  let b₂ := downwardChoice v₂
  let split := loopChoiceSplitEquiv hqne
  let choices (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :=
    split.symm (b₁, b₂, G)
  let arrow (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :=
    orientArrows ω₀ s h₀ (choices G)
  have hchoice₁ (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      choices G q₁ = b₁ := by
    simp [choices, split, b₁, loopChoiceSplitEquiv_symm_apply,
      loopChoiceMergeMap]
  have hchoice₂ (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      choices G q₂ = b₂ := by
    simp [choices, split, b₂, loopChoiceSplitEquiv_symm_apply,
      loopChoiceMergeMap, hqne.symm]
  have hdown₁ (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      loopVertical j
        (loopReorientEquiv ω₀ (arrow G) s h₀
          (orientArrows_compatible ω₀ s h₀ (choices G)) q₁) = -1 := by
    rw [loopVertical_reorient, loopOrientation_orientArrows, hchoice₁]
    exact downwardChoice_turn hv₁
  have hdown₂ (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      loopVertical j
        (loopReorientEquiv ω₀ (arrow G) s h₀
          (orientArrows_compatible ω₀ s h₀ (choices G)) q₂) = -1 := by
    rw [loopVertical_reorient, loopOrientation_orientArrows, hchoice₂]
    exact downwardChoice_turn hv₂
  have hsector (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      (arrow G).absUp + 1 = N / 2 := by
    let hG := orientArrows_compatible ω₀ s h₀ (choices G)
    have hterm (q : Loop hN hM s) :
        loopVertical j (loopReorientEquiv ω₀ (arrow G) s h₀ hG q) =
          if q = q₁ then -1 else if q = q₂ then -1 else 0 := by
      by_cases hq₁' : q = q₁
      · subst q
        simp [hdown₁ G]
      · by_cases hq₂' : q = q₂
        · subst q
          simp [hq₁', hdown₂ G]
        · have hvzero : loopVertical j q = 0 := by
            grind
          simp [loopVertical_reorient, hq₁', hq₂', hvzero]
    have hcanonical :
        (∑ q : Loop hN hM s,
          loopVertical j
            (loopReorientEquiv ω₀ (arrow G) s h₀ hG q)) = -2 := by
      calc
        _ = ∑ q : Loop hN hM s,
              if q = q₁ then (-1 : ℤ) else if q = q₂ then -1 else 0 := by
          grind
        _ = (∑ q : Loop hN hM s, if q = q₁ then (-1 : ℤ) else 0) +
              ∑ q : Loop hN hM s, if q = q₂ then (-1 : ℤ) else 0 := by
          rw [← Finset.sum_add_distrib]
          grind
        _ = -2 := by
          simp
    have htransport :
        (∑ q : Loop hN hM s,
          loopVertical j
            (loopReorientEquiv ω₀ (arrow G) s h₀ hG q)) =
          ∑ q : DirectedLoop hG, loopVertical j q := by
      rw [← (loopReorientEquiv ω₀ (arrow G) s h₀ hG).sum_comp]
    have hflux := sum_loopVertical (ω := (arrow G)) s hG j
    omega
  let f (q : Loop hN hM s) (b : Bool) :=
    Real.exp (lam * (if b then loopRotationNumber (ω := ω₀) (s := s) (h := h₀) q
      else -loopRotationNumber q : ℤ))
  have hf₁ (b : Bool) : f q₁ b = 1 := by simp [f, hrot₁]
  have hf₂ (b : Bool) : f q₂ b = 1 := by simp [f, hrot₂]
  have hsplitSum :
      (∑ F : Loop hN hM s → Bool, chosenLoopWeight lam F) =
        4 * (∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool,
          chosenLoopWeight lam (choices G)) := by
    exact sum_boolFunctionWeight_eq_four_mul_fixed q₁ q₂ hqne f hf₁ hf₂ b₁ b₂
  have horientation :
      (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s},
        orientedLoopWeight lam x.property) =
        ∑ F : Loop hN hM s → Bool, chosenLoopWeight lam F := by
    refine Fintype.sum_equiv (orientationEquiv ω₀ s h₀) _ _ ?_
    intro x
    exact orientedLoopWeight_eq_chosenLoopWeight lam hN hM A x.val x.property
  have hmapinj : Function.Injective arrow := by
    intro G H hGH
    have hsub : (⟨arrow G, orientArrows_compatible ω₀ s h₀ (choices G)⟩ :
        {ω : ArrowConfig N M // CompatibleConfig ω s}) =
        ⟨arrow H, orientArrows_compatible ω₀ s h₀ (choices H)⟩ := Subtype.ext hGH
    have hF := congrArg (orientationEquiv ω₀ s h₀) hsub
    have hchoiceEq : choices G = choices H := by
      simpa [orientationEquiv, choices, arrow, loopOrientation_orientArrows] using hF
    have hsplitEq := (Equiv.injective split.symm) hchoiceEq
    grind
  let arrowEmb : (LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) ↪ ArrowConfig N M :=
    ⟨arrow, hmapinj⟩
  let selected := Finset.univ.map arrowEmb
  have hselected_sector : selected ⊆
      (Finset.univ.filter fun ω : ArrowConfig N M => ω.absUp + 1 = N / 2) := by
    intro ω hω
    aesop
  have hselected_sum :
      (∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool,
        chosenLoopWeight lam (choices G)) =
      ∑ ω ∈ selected, smoothingWeight lam ω s := by
    calc
      _ = ∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool,
            smoothingWeight lam (arrow G) s := by
        apply Finset.sum_congr rfl
        intro G _
        calc
          chosenLoopWeight lam (choices G) =
              orientedLoopWeight lam
                (orientArrows_compatible ω₀ s h₀ (choices G)) := by
            rw [orientedLoopWeight_eq_chosenLoopWeight, loopOrientation_orientArrows]
          _ = smoothingWeight lam (arrow G) s :=
            orientedLoopWeight_eq_smoothingWeight lam s _
      _ = _ := by
        simp [selected, arrowEmb]
  have hselected_le :
      (∑ ω ∈ selected, smoothingWeight lam ω s) ≤
        ∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2, smoothingWeight lam ω s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hselected_sector
    intro ω _ _
    exact smoothingWeight_nonneg lam ω s
  calc
    _ = ∑ F : Loop hN hM s → Bool, chosenLoopWeight lam F := horientation
    _ = 4 * (∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool,
          chosenLoopWeight lam (choices G)) := hsplitSum
    _ ≤ 4 * (∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2,
          smoothingWeight lam ω s) := by
      grind

private theorem smoothingWeight_nonneg_of_compatible (lam : ℝ) (ω : ArrowConfig N M)
    (s : Smoothing N M) : 0 ≤ smoothingWeight lam ω s :=
  smoothingWeight_nonneg lam ω s

/-- A six-vertex sector of deficit `r` lies inside the smoothing sum with `U ≥ r`.
This is the formal counting inclusion used for Corollary 3.13(iii). -/
theorem sixVertexSector_le_verticalUSmoothingSum (hN : Even N) (hM : Even M)
    (qval : ℝ) (hq : 4 < qval) (j : Fin M) (r : ℕ) :
    Z6Vr (Real.sqrt (2 + Real.sqrt qval)) N M r ≤
      (∑ s : {s : Smoothing N M //
          r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
        ∑ ω : ArrowConfig N M, smoothingWeight
          (Real.arcosh (Real.sqrt qval / 2)) ω s.val) := by
  classical
  let lam := Real.arcosh (Real.sqrt qval / 2)
  let U (s : Smoothing N M) := r ≤ rcVerticalWinding hN hM j (smoothingRC s)
  let g (ω : ArrowConfig N M) :=
    ∑ s : Smoothing N M, if U s then smoothingWeight lam ω s else 0
  have hsectorEq (ω : ArrowConfig N M) (hω : ω.absUp + r = N / 2) :
      (∑ s : Smoothing N M, smoothingWeight lam ω s) = g ω := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hU : U s
    · grind
    · have hzero : smoothingWeight lam ω s = 0 := by
        by_contra hne
        have hcompat : CompatibleConfig ω s := by
          by_contra hn
          exact hne (smoothingWeight_eq_zero_of_not_compatible lam ω s hn)
        have hbound := sector_le_rcVerticalWinding hN hM j (A := (smoothingRC s)) (ω := ω)
          (by simpa using hcompat) hω
        grind
      grind
  have hge (ω : ArrowConfig N M) : 0 ≤ g ω := by
    apply Finset.sum_nonneg
    intro s _
    split_ifs
    · exact smoothingWeight_nonneg_of_compatible lam ω s
    · exact le_rfl
  have htotal :
      (∑ s : {s : Smoothing N M // U s},
        ∑ ω : ArrowConfig N M, smoothingWeight lam ω s.val) =
      ∑ ω : ArrowConfig N M, g ω := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun s : Smoothing N M => U s)
      (by simp) (fun s => ∑ ω : ArrowConfig N M, smoothingWeight lam ω s)]
    rw [Finset.sum_filter]
    have hswap :
        (∑ s : Smoothing N M,
          if U s then ∑ ω : ArrowConfig N M, smoothingWeight lam ω s else 0) =
        ∑ ω : ArrowConfig N M, g ω := by
      calc
        _ = ∑ s : Smoothing N M, ∑ ω : ArrowConfig N M,
              if U s then smoothingWeight lam ω s else 0 := by
          simp
        _ = ∑ ω : ArrowConfig N M, ∑ s : Smoothing N M,
              if U s then smoothingWeight lam ω s else 0 := by rw [Finset.sum_comm]
        _ = _ := rfl
    exact hswap
  have hZ := sum_smoothingWeight_eq_Z6Vr_sqrt (N := N) (M := M) qval hq r
  calc
    Z6Vr (Real.sqrt (2 + Real.sqrt qval)) N M r =
        ∑ ω : ArrowConfig N M with ω.absUp + r = N / 2,
          ∑ s : Smoothing N M, smoothingWeight lam ω s := by
      grind
    _ = ∑ ω : ArrowConfig N M with ω.absUp + r = N / 2, g ω := by
      apply Finset.sum_congr rfl
      grind
    _ ≤ ∑ ω : ArrowConfig N M, g ω := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro ω _
      by_cases hω : ω.absUp + r = N / 2
      · grind
      · simp [hω, hge ω]
    _ = _ := htotal.symm

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
  let sectorSum (s : Smoothing N M) :=
    ∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2, smoothingWeight lam ω s
  have hsum :
      (∑ A : {A : RCConfig N M // rcVerticalWinding hN hM j A = 1},
        torusCorrectedRCWeight hN hM i j q A.val) =
      torusNormalization q N M *
        (∑ A : {A : RCConfig N M // rcVerticalWinding hN hM j A = 1},
          ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A.val)},
            orientedLoopWeight lam x.property) := by
    calc
      _ = ∑ A : {A : RCConfig N M // rcVerticalWinding hN hM j A = 1},
            torusNormalization q N M *
              (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A.val)},
                orientedLoopWeight lam x.property) := by
        apply Finset.sum_congr rfl
        intro A _
        simpa [lam] using
          (torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq (hturn A.val).1 (hturn A.val).2)
      _ = _ := by rw [Finset.mul_sum]
  have hloopBound :
      (∑ A : {A : RCConfig N M // P A},
        ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A.val)},
          orientedLoopWeight lam x.property) ≤
      4 * (∑ A : {A : RCConfig N M // P A}, sectorSum (rcSmoothing A.val)) := by
    calc
      _ ≤ ∑ A : {A : RCConfig N M // P A},
            4 * sectorSum (rcSmoothing A.val) := by
        apply Finset.sum_le_sum
        intro A _
        simpa [sectorSum] using
          (uOne_orientedLoopSum_le_four_mul_sectorSum hN hM i j
            A.val lam (hturn A.val).2 A.property)
      _ = _ := by rw [Finset.mul_sum]
  have hsectorBound :
      (∑ A : {A : RCConfig N M // P A}, sectorSum (rcSmoothing A.val)) ≤
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
    have hfilter :
        (∑ A : {A : RCConfig N M // P A}, sectorSum (rcSmoothing A.val)) =
          ∑ A : RCConfig N M,
            if P A then sectorSum (rcSmoothing A) else 0 := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter fun A : RCConfig N M => P A)
        (by simp)
        (fun A => sectorSum (rcSmoothing A))]
      rw [Finset.sum_filter]
    have hnonneg (A : RCConfig N M) : 0 ≤ sectorSum (rcSmoothing A) := by
      apply Finset.sum_nonneg
      intro ω _
      exact smoothingWeight_nonneg lam ω (rcSmoothing A)
    calc
      _ = ∑ A : RCConfig N M, if P A then sectorSum (rcSmoothing A) else 0 := hfilter
      _ ≤ ∑ A : RCConfig N M, sectorSum (rcSmoothing A) := by
        apply Finset.sum_le_sum
        intro A _
        by_cases hP : P A
        · grind
        · simpa [hP] using hnonneg A
      _ = ∑ s : Smoothing N M, sectorSum s := Fintype.sum_equiv (rcSmoothingEquiv N M) _ _ (by intro A; rfl)
      _ = ∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2,
            ∑ s : Smoothing N M, smoothingWeight lam ω s := by
        rw [Finset.sum_comm]
      _ = Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
        simpa [sectorSum, lam] using
          (sum_smoothingWeight_eq_Z6Vr_sqrt (N := N) (M := M) q.val hq 1)
  have hnorm := torusNormalization_pos q N M
  have hscaled := mul_le_mul_of_nonneg_left hloopBound hnorm.le
  have hfour : 0 ≤ 4 * torusNormalization q N M := by positivity
  calc
    _ = torusNormalization q N M *
          (∑ A : {A : RCConfig N M // P A},
            ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A.val)},
              orientedLoopWeight lam x.property) := hsum
    _ ≤ torusNormalization q N M *
          (4 * (∑ A : {A : RCConfig N M // P A},
            sectorSum (rcSmoothing A.val))) := hscaled
    _ = 4 * torusNormalization q N M *
          (∑ A : {A : RCConfig N M // P A}, sectorSum (rcSmoothing A.val)) := by ring
    _ ≤ 4 * torusNormalization q N M *
          Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 :=
      mul_le_mul_of_nonneg_left hsectorBound hfour

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
  let e :
      {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A} ≃
        {s : Smoothing N M //
          r ≤ rcVerticalWinding hN hM j (smoothingRC s)} := {
    toFun := fun x => ⟨rcSmoothing x.val, by simpa using x.property⟩
    invFun := fun x => ⟨smoothingRC x.val, by simpa using x.property⟩
    left_inv := by intro x; simp
    right_inv := by intro x; simp
  }
  have hsum :
      (∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        torusCorrectedRCWeight hN hM i j q A.val) =
      torusNormalization q N M *
        (∑ s : {s : Smoothing N M //
            r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
          ∑ ω : ArrowConfig N M, smoothingWeight lam ω s.val) := by
    calc
      _ = ∑ s : {s : Smoothing N M //
            r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
            torusCorrectedRCWeight hN hM i j q (smoothingRC s.val) := by
        refine Fintype.sum_equiv e _ _ ?_
        simp [e]
      _ = ∑ s : {s : Smoothing N M //
            r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
            torusNormalization q N M *
              (∑ x : {ω : ArrowConfig N M //
                  CompatibleConfig ω (rcSmoothing (smoothingRC s.val))},
                orientedLoopWeight lam x.property) := by
        apply Finset.sum_congr rfl
        intro s _
        simpa [lam] using
          (torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq (hturn (smoothingRC s.val)).1 (hturn (smoothingRC s.val)).2)
      _ = torusNormalization q N M *
            (∑ s : {s : Smoothing N M //
                r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
              ∑ ω : ArrowConfig N M, smoothingWeight lam ω s.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        apply congrArg (fun z : ℝ => torusNormalization q N M * z)
        simpa only [rcSmoothing_smoothingRC] using
          (sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight lam
            (rcSmoothing (smoothingRC s.val)))
  have hsector := sixVertexSector_le_verticalUSmoothingSum hN hM q.val hq j r
  have hC := torusNormalization_pos q N M
  calc
    _ ≤ torusNormalization q N M *
          (∑ s : {s : Smoothing N M //
              r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
            ∑ ω : ArrowConfig N M, smoothingWeight lam ω s.val) :=
      mul_le_mul_of_nonneg_left hsector hC.le
    _ = _ := hsum.symm

end PottsDiscontinuity.Torus
