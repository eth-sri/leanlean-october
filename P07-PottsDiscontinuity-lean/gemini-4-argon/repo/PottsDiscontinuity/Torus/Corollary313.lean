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
  fun x => if hx : x = a then p.1 else if hy : x = b then p.2.1 else p.2.2 ⟨x, hx, hy⟩

noncomputable def loopChoiceSplitEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    (α → Bool) ≃ Bool × (Bool × (LoopChoiceRest α a b → Bool)) where
  toFun := loopChoiceSplitMap a b
  invFun := loopChoiceMergeMap a b
  left_inv F := by
    funext x
    by_cases hxa : x = a
    · subst x; simp [loopChoiceSplitMap, loopChoiceMergeMap]
    · by_cases hxb : x = b
      · subst x; simp [loopChoiceSplitMap, loopChoiceMergeMap, hxa]
      · simp [loopChoiceSplitMap, loopChoiceMergeMap, hxa, hxb]
  right_inv := by
    rintro ⟨ba, bb, G⟩
    refine Prod.ext (by simp [loopChoiceSplitMap, loopChoiceMergeMap])
      (Prod.ext (by simp [loopChoiceSplitMap, loopChoiceMergeMap, hab.symm]) ?_)
    funext x
    simp [loopChoiceSplitMap, loopChoiceMergeMap, x.property.1, x.property.2]

@[simp] private theorem loopChoiceSplitEquiv_symm_apply {α : Type*} [Fintype α]
    [DecidableEq α] (a b : α) (hab : a ≠ b)
    (p : Bool × (Bool × (LoopChoiceRest α a b → Bool))) :
    (loopChoiceSplitEquiv a b hab).symm p = loopChoiceMergeMap a b p := rfl

private theorem sum_boolFunctionWeight_eq_four_mul_fixed
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (f : α → Bool → ℝ)
    (ha : ∀ z, f a z = 1) (hb : ∀ z, f b z = 1) (ba bb : Bool) :
    (∑ F : α → Bool, ∏ x : α, f x (F x)) =
      4 * (∑ G : LoopChoiceRest α a b → Bool,
        ∏ x : α, f x ((loopChoiceSplitEquiv a b hab).symm (ba, bb, G) x)) := by
  classical
  let e := loopChoiceSplitEquiv a b hab
  have hweight (u v : Bool) (G : LoopChoiceRest α a b → Bool) :
      (∏ x : α, f x (e.symm (u, v, G) x)) = ∏ x : α, f x (e.symm (ba, bb, G) x) :=
    Finset.prod_congr rfl fun x _ => by
      by_cases hxa : x = a
      · subst x; simp [e, loopChoiceMergeMap, ha]
      · by_cases hxb : x = b
        · subst x; simp [e, loopChoiceMergeMap, hb]
        · simp [e, loopChoiceSplitEquiv, loopChoiceMergeMap, hxa, hxb]
  calc (∑ F : α → Bool, ∏ x : α, f x (F x))
    _ = ∑ p : Bool × (Bool × (LoopChoiceRest α a b → Bool)), ∏ x : α, f x (e.symm p x) :=
        Fintype.sum_equiv e _ _ fun F => by simp [e]
    _ = ∑ u : Bool, ∑ v : Bool, ∑ G : LoopChoiceRest α a b → Bool,
          ∏ x : α, f x (e.symm (ba, bb, G) x) := by
        simp_rw [Fintype.sum_prod_type, hweight]
    _ = _ := by rw [Fintype.sum_bool, Fintype.sum_bool]; ring

def downwardChoice (z : ℤ) : Bool := if z = 1 then false else true

private theorem downwardChoice_turn {z : ℤ} (hz : z = 1 ∨ z = -1) :
    (if downwardChoice z then z else -z) = -1 := by
  rcases hz with rfl | rfl <;> rfl

private theorem uOne_orientedLoopSum_le_four_mul_sectorSum
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
  let v₁ := loopVertical ω₀ s h₀ j q₁
  let v₂ := loopVertical ω₀ s h₀ j q₂
  have hv₁ : v₁ = 1 ∨ v₁ = -1 := Or.inl (by simpa [v₁, s, ω₀, h₀] using hv₁eq)
  have hv₂ : v₂ = 1 ∨ v₂ = -1 := Or.inr (by simpa [v₂, s, ω₀, h₀] using hv₂eq)
  have hrot₁ : loopRotationNumber ω₀ s h₀ q₁ = 0 :=
    hnonzero q₁ (Or.inl (by rcases hv₁ with h | h <;> omega))
  have hrot₂ : loopRotationNumber ω₀ s h₀ q₂ = 0 :=
    hnonzero q₂ (Or.inl (by rcases hv₂ with h | h <;> omega))
  let b₁ := downwardChoice v₁
  let b₂ := downwardChoice v₂
  let split := loopChoiceSplitEquiv q₁ q₂ hqne
  let choices (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) := split.symm (b₁, b₂, G)
  let arrow (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) := orientArrows ω₀ s h₀ (choices G)
  have hdown₁ (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      loopVertical (arrow G) s (orientArrows_compatible ω₀ s h₀ (choices G)) j
        (loopReorientEquiv ω₀ (arrow G) s h₀
          (orientArrows_compatible ω₀ s h₀ (choices G)) q₁) = -1 := by
    rw [loopVertical_reorient, loopOrientation_orientArrows,
      show choices G q₁ = b₁ by simp [choices, split, loopChoiceMergeMap]]
    exact downwardChoice_turn hv₁
  have hdown₂ (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      loopVertical (arrow G) s (orientArrows_compatible ω₀ s h₀ (choices G)) j
        (loopReorientEquiv ω₀ (arrow G) s h₀
          (orientArrows_compatible ω₀ s h₀ (choices G)) q₂) = -1 := by
    rw [loopVertical_reorient, loopOrientation_orientArrows,
      show choices G q₂ = b₂ by simp [choices, split, loopChoiceMergeMap, hqne.symm]]
    exact downwardChoice_turn hv₂
  have hsector (G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) :
      (arrow G).absUp + 1 = N / 2 := by
    let hG := orientArrows_compatible ω₀ s h₀ (choices G)
    have hterm (q : Loop hN hM s) :
        loopVertical (arrow G) s hG j (loopReorientEquiv ω₀ (arrow G) s h₀ hG q) =
          (if q = q₁ then (-1 : ℤ) else 0) + (if q = q₂ then (-1 : ℤ) else 0) := by
      by_cases hq₁' : q = q₁
      · subst q; simp [hqne, hdown₁ G]
      · by_cases hq₂' : q = q₂
        · subst q; simp [hqne.symm, hdown₂ G]
        · have hvzero : loopVertical ω₀ s h₀ j q = 0 := by
            by_contra hnz; exact (hchar q).mp hnz |>.elim hq₁' hq₂'
          rw [loopVertical_reorient]; simp [hq₁', hq₂', hvzero]
    have hflux := sum_loopVertical (arrow G) s hG j
    rw [← (loopReorientEquiv ω₀ (arrow G) s h₀ hG).sum_comp,
      Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_add_distrib,
      Finset.sum_ite_eq' univ q₁, Finset.sum_ite_eq' univ q₂] at hflux
    simp only [mem_univ, ↓reduceIte] at hflux
    rcases hN with ⟨k, rfl⟩; omega
  let f (q : Loop hN hM s) (b : Bool) : ℝ :=
    Real.exp (lam * (if b then loopRotationNumber ω₀ s h₀ q else -loopRotationNumber ω₀ s h₀ q : ℤ))
  have hsplitSum :
      (∑ F : Loop hN hM s → Bool, chosenLoopWeight lam hN hM A F) =
        4 * (∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool,
          chosenLoopWeight lam hN hM A (choices G)) :=
    sum_boolFunctionWeight_eq_four_mul_fixed q₁ q₂ hqne f
      (fun b => by simp [f, hrot₁]) (fun b => by simp [f, hrot₂]) b₁ b₂
  have hmapinj : Function.Injective arrow := fun G H hGH => by
    have hF := congrArg (orientationEquiv ω₀ s h₀)
      (Subtype.ext hGH : (⟨arrow G, orientArrows_compatible ω₀ s h₀ (choices G)⟩ :
        {ω : ArrowConfig N M // CompatibleConfig ω s}) =
        ⟨arrow H, orientArrows_compatible ω₀ s h₀ (choices H)⟩)
    have hchoiceEq : choices G = choices H := by
      simpa [orientationEquiv, choices, arrow, loopOrientation_orientArrows] using hF
    exact congrArg (fun p : Bool × (Bool × _) => p.2.2) (split.symm.injective hchoiceEq)
  let arrowEmb : (LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool) ↪ ArrowConfig N M := ⟨arrow, hmapinj⟩
  have hselected_le :
      (∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool,
        chosenLoopWeight lam hN hM A (choices G)) ≤
      ∑ ω : ArrowConfig N M with ω.absUp + 1 = N / 2, smoothingWeight lam ω s := by
    rw [show (∑ G : LoopChoiceRest (Loop hN hM s) q₁ q₂ → Bool,
        chosenLoopWeight lam hN hM A (choices G)) =
        ∑ ω ∈ Finset.univ.map arrowEmb, smoothingWeight lam ω s by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun G _ => ?_
      dsimp [arrowEmb]
      rw [← orientedLoopWeight_eq_smoothingWeight lam (arrow G) s
        (orientArrows_compatible ω₀ s h₀ (choices G)),
        orientedLoopWeight_eq_chosenLoopWeight, loopOrientation_orientArrows]]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun ω hω => by
        rcases Finset.mem_map.mp hω with ⟨G, _, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsector G⟩)
      (fun ω _ _ => smoothingWeight_nonneg lam ω s)
  rw [Fintype.sum_equiv (orientationEquiv ω₀ s h₀) _ _ fun x =>
    orientedLoopWeight_eq_chosenLoopWeight lam hN hM A x.val x.property, hsplitSum]
  exact mul_le_mul_of_nonneg_left hselected_le (by norm_num)

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
  let g (ω : ArrowConfig N M) := ∑ s : Smoothing N M, if U s then smoothingWeight lam ω s else 0
  have hsectorEq (ω : ArrowConfig N M) (hω : ω.absUp + r = N / 2) :
      (∑ s : Smoothing N M, smoothingWeight lam ω s) = g ω :=
    Finset.sum_congr rfl fun s _ => by
      by_cases hU : U s
      · simp [U, hU]
      · have hzero : smoothingWeight lam ω s = 0 := by
          by_contra hne
          exact hU (sector_le_rcVerticalWinding hN hM j (smoothingRC s) ω
            (by simpa using (show CompatibleConfig ω s by
              by_contra hn; exact hne (smoothingWeight_eq_zero_of_not_compatible lam ω s hn))) hω)
        simp [U, hU, hzero]
  have hge (ω : ArrowConfig N M) : 0 ≤ g ω :=
    Finset.sum_nonneg fun s _ => by split_ifs <;> [exact smoothingWeight_nonneg lam ω s; exact le_rfl]
  rw [← sum_smoothingWeight_eq_Z6Vr_sqrt (N := N) (M := M) qval hq r,
    Finset.sum_congr rfl fun ω hω => hsectorEq ω (Finset.mem_filter.mp hω).2,
    ← Finset.sum_subtype (Finset.univ.filter fun s : Smoothing N M => U s)
      (fun _ => Finset.mem_filter_univ _)
      (fun s => ∑ ω : ArrowConfig N M, smoothingWeight lam ω s),
    Finset.sum_filter (p := U),
    show (∑ s : Smoothing N M, if U s then ∑ ω : ArrowConfig N M, smoothingWeight lam ω s else 0) =
      ∑ ω : ArrowConfig N M, g ω by
      rw [← Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => by by_cases hU : U s <;> simp [hU],
    Finset.sum_filter]
  exact Finset.sum_le_sum fun ω _ => by split_ifs <;> [exact le_rfl; exact hge ω]

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
      (∑ A : {A : RCConfig N M // P A}, torusCorrectedRCWeight hN hM i j q A.val) =
      torusNormalization q N M *
        (∑ A : {A : RCConfig N M // P A},
          ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A.val)},
            orientedLoopWeight lam x.val (rcSmoothing A.val) x.property) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun A _ => by
      simpa [lam] using torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq
        A.val (hturn A.val).1 (hturn A.val).2
  have hloopBound :
      (∑ A : {A : RCConfig N M // P A},
        ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A.val)},
          orientedLoopWeight lam x.val (rcSmoothing A.val) x.property) ≤
      4 * (∑ A : {A : RCConfig N M // P A}, sectorSum (rcSmoothing A.val)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun A _ =>
      uOne_orientedLoopSum_le_four_mul_sectorSum hN hM i j A.val lam (hturn A.val).2 A.property
  have hsectorBound :
      (∑ A : {A : RCConfig N M // P A}, sectorSum (rcSmoothing A.val)) ≤
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun A : RCConfig N M => P A)
      (fun _ => Finset.mem_filter_univ _) (fun A => sectorSum (rcSmoothing A)),
      Finset.sum_filter (p := P),
      ← sum_smoothingWeight_eq_Z6Vr_sqrt (N := N) (M := M) q.val hq 1, ← Finset.sum_comm,
      ← Fintype.sum_equiv (rcSmoothingEquiv N M) _ (fun s => sectorSum s) (fun _ => rfl)]
    exact Finset.sum_le_sum fun A _ => by
      split_ifs <;> [exact le_rfl; exact Finset.sum_nonneg fun ω _ =>
        smoothingWeight_nonneg lam ω (rcSmoothing A)]
  have hnorm := (torusNormalization_pos q N M).le
  calc (∑ A : {A : RCConfig N M // P A}, torusCorrectedRCWeight hN hM i j q A.val)
    _ ≤ torusNormalization q N M * (4 * ∑ A : {A : RCConfig N M // P A},
          sectorSum (rcSmoothing A.val)) := hsum ▸ mul_le_mul_of_nonneg_left hloopBound hnorm
    _ = 4 * torusNormalization q N M *
          ∑ A : {A : RCConfig N M // P A}, sectorSum (rcSmoothing A.val) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsectorBound (by positivity)

theorem corollary_313_iii (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (i : Fin N) (j : Fin M) (r : ℕ)
    (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    torusNormalization q N M * Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      ∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        torusCorrectedRCWeight hN hM i j q A.val := by
  classical
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  let e : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A} ≃
      {s : Smoothing N M // r ≤ rcVerticalWinding hN hM j (smoothingRC s)} :=
    { toFun := fun x => ⟨rcSmoothing x.val, by simpa using x.property⟩
      invFun := fun x => ⟨smoothingRC x.val, by simpa using x.property⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  rw [Fintype.sum_equiv e _
    (fun s => torusCorrectedRCWeight hN hM i j q (smoothingRC s.val)) (fun x => by simp [e]),
    show (∑ s : {s : Smoothing N M // r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
        torusCorrectedRCWeight hN hM i j q (smoothingRC s.val)) =
      torusNormalization q N M *
        (∑ s : {s : Smoothing N M // r ≤ rcVerticalWinding hN hM j (smoothingRC s)},
          ∑ ω : ArrowConfig N M, smoothingWeight lam ω s.val) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq
        (smoothingRC s.val) (hturn (smoothingRC s.val)).1 (hturn (smoothingRC s.val)).2]
      exact congrArg (torusNormalization q N M * ·) (by
        simpa only [rcSmoothing_smoothingRC] using
          sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight lam
            (rcSmoothing (smoothingRC s.val)))]
  exact mul_le_mul_of_nonneg_left
    (sixVertexSector_le_verticalUSmoothingSum hN hM q.val hq j r)
    (torusNormalization_pos q N M).le

end PottsDiscontinuity.Torus
