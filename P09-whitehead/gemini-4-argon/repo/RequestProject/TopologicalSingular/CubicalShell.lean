module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic

@[expose] public section

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.TopologicalSingular

variable {d : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

def cubeFace {d : ℕ} (i : Fin (d + 1)) (a : I) : C(I^Fin d, I^Fin (d + 1)) where
  toFun t := i.insertNth a t
  continuous_toFun := continuous_pi fun j =>
    Fin.succAboveCases i (by simp [continuous_const]) (fun k => by simp [continuous_apply k]) j

@[simp]
theorem cubeFace_apply_same {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFace i a t i = a := by simp [cubeFace]

@[simp]
theorem cubeFace_apply_succAbove {d : ℕ} (i : Fin (d + 1)) (a : I)
    (t : I^Fin d) (j : Fin d) :
    cubeFace i a t (i.succAbove j) = t j := by simp [cubeFace]

def cubeCodimTwo (d : ℕ) : Set (I^Fin d) :=
  {t | ∃ i j : Fin d, i ≠ j ∧ (t i = 0 ∨ t i = 1) ∧ (t j = 0 ∨ t j = 1)}

theorem cubeFace_mem_cubeCodimTwo {d : ℕ} (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    cubeFace i a t ∈ cubeCodimTwo (d + 1) :=
  let ⟨j, hj⟩ := ht
  ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, by simpa using ha, by simpa using hj⟩

def squareBottomRight : Path ((0, 0) : I × I) (1, 1) :=
  (⟨⟨(·, 0), by fun_prop⟩, rfl, rfl⟩ : Path ((0, 0) : I × I) (1, 0)).trans
    ⟨⟨(1, ·), by fun_prop⟩, rfl, rfl⟩

def squareLeftTop : Path ((0, 0) : I × I) (1, 1) :=
  (⟨⟨(0, ·), by fun_prop⟩, rfl, rfl⟩ : Path ((0, 0) : I × I) (0, 1)).trans
    ⟨⟨(·, 1), by fun_prop⟩, rfl, rfl⟩

def squareBoundaryHomotopy : Path.Homotopy squareBottomRight squareLeftTop where
  toFun p :=
    (Set.Icc.convexComb (squareBottomRight p.2).1 (squareLeftTop p.2).1 p.1,
      Set.Icc.convexComb (squareBottomRight p.2).2 (squareLeftTop p.2).2 p.1)
  continuous_toFun := (Continuous.subtype_mk (by fun_prop) _).prodMk
    (Continuous.subtype_mk (by fun_prop) _)
  map_zero_left t := by ext <;> simp [squareBottomRight, squareLeftTop]
  map_one_left t := by ext <;> simp [squareBottomRight, squareLeftTop]
  prop' := by
    rintro s t (rfl | ht)
    · simp [squareBottomRight, squareLeftTop, Set.Icc.convexComb]
    · subst ht; simp [squareBottomRight, squareLeftTop, Set.Icc.convexComb]

@[simp]
theorem cubeFace_last_eq_snoc {m : ℕ} (a : I) (t : I^Fin m) :
    cubeFace (Fin.last m) a t = Fin.snoc t a := by simp [cubeFace]

@[simp]
theorem cubeFace_penultimate_snoc {m : ℕ} (a b : I) (t : I^Fin m) :
    cubeFace (Fin.last m).castSucc a (Fin.snoc t b) = Fin.snoc (Fin.snoc t a) b := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      rw [← show (Fin.last m).castSucc.succAbove (Fin.last m) = Fin.last (m + 1)
        from Fin.ext (by simp), cubeFace_apply_succAbove]; simp
  | cast j =>
      induction j using Fin.lastCases with
      | last => simp [cubeFace]
      | cast j => simp [cubeFace, Fin.insertNth_apply_below, Fin.snoc]

@[simp]
theorem update_last_eq_snoc_init {m : ℕ} (t : I^Fin (m + 1)) (a : I) :
    Function.update t (Fin.last m) a = Fin.snoc (Fin.init t) a := by
  conv_lhs => rw [← Fin.snoc_init_self t]
  exact Fin.update_snoc_last _ _ _

def squareSweepCube (m : ℕ) : C(I × (I^Fin (m + 1)), I^Fin (m + 2)) where
  toFun st :=
    Fin.snoc (Fin.snoc (Fin.init st.2) (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).1)
      (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).2
  continuous_toFun := by
    have hc : Continuous (fun st : I × (I^Fin (m + 1)) =>
        squareBoundaryHomotopy (st.1, st.2 (Fin.last m))) :=
      squareBoundaryHomotopy.continuous.comp (by fun_prop)
    refine continuous_pi fun j => Fin.lastCases (by simp [hc.snd]) (fun k => ?_) j
    simp only [Fin.snoc_castSucc]
    exact Fin.lastCases (by simp [hc.fst]) (fun _ => by simp [Fin.init_def]; fun_prop) k

theorem genLoop_transAt_apply_path {N : Type*} [DecidableEq N] (i : N)
    (f g : Ω^ N X x) (t : I^N) :
    (GenLoop.transAt i f g).val t =
      if h : (t i : ℝ) ≤ 1 / 2 then
        f (Function.update t i
          ⟨2 * t i, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t i).2.1, h⟩⟩)
      else
        g (Function.update t i
          ⟨2 * t i - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, (t i).2.2⟩⟩) := by
  change (if (t i : ℝ) ≤ 1 / 2 then
      f (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i)))
    else g (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i - 1)))) = _
  split_ifs with h
  · rw [Set.projIcc_of_mem _ ((unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t i).2.1, h⟩)]
  · rw [Set.projIcc_of_mem _ (unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, (t i).2.2⟩)]

structure CubicalShell (d : ℕ) (X : Type*) [TopologicalSpace X] (x : X) where
  map : C(I^Fin (d + 1), X)
  codimTwo (t : I^Fin (d + 1)) (ht : t ∈ cubeCodimTwo (d + 1)) : map t = x

namespace CubicalShell

def faceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) : Ω^ (Fin d) X x :=
  ⟨S.map.comp (cubeFace i a), fun t ht ↦ S.codimTwo _
    (cubeFace_mem_cubeCodimTwo i a ha t ht)⟩

def lowerFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) : Ω^ (Fin d) X x :=
  S.faceLoop i 0 (.inl rfl)

def upperFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) : Ω^ (Fin d) X x :=
  S.faceLoop i 1 (.inr rfl)

def IsConstantFace (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I) : Prop :=
  ∀ t : I^Fin (d + 1), t i = a → S.map t = x

def LeadingFacesConstant {m : ℕ} (S : CubicalShell (m + 1) X x) : Prop :=
  ∀ i : Fin m,
    S.IsConstantFace i.castSucc.castSucc 0 ∧ S.IsConstantFace i.castSucc.castSucc 1

def lowerFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.lowerFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

def upperFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.upperFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

theorem lowerFaceClass_eq_zero [Nonempty (Fin d)] (S : CubicalShell d X x)
    (i : Fin (d + 1)) (h : S.IsConstantFace i 0) :
    S.lowerFaceClass i = 0 := by
  have hc : S.lowerFaceLoop i = GenLoop.const := by ext t; exact h _ (by simp)
  rw [lowerFaceClass, hc, ← HomotopyGroup.one_def]; rfl

theorem lastTwoFaceClass_relation {m : ℕ} [Nontrivial (Fin (m + 1))]
    (S : CubicalShell (m + 1) X x) (h : S.LeadingFacesConstant) :
    S.upperFaceClass (Fin.last m).castSucc + S.lowerFaceClass (Fin.last (m + 1)) =
      S.upperFaceClass (Fin.last (m + 1)) + S.lowerFaceClass (Fin.last m).castSucc := by
  have hhtpy : GenLoop.Homotopic
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
        (S.upperFaceLoop (Fin.last m).castSucc))
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last m).castSucc)
        (S.upperFaceLoop (Fin.last (m + 1)))) := by
    refine ⟨{
      toFun := fun st ↦ S.map (squareSweepCube m st)
      continuous_toFun := S.map.continuous.comp (squareSweepCube m).continuous
      map_zero_left := fun t => by
        change S.map (Fin.snoc (Fin.snoc (Fin.init t)
          (squareBoundaryHomotopy (0, t (Fin.last m))).1)
          (squareBoundaryHomotopy (0, t (Fin.last m))).2) = _
        rw [ContinuousMap.HomotopyWith.apply_zero, squareBottomRight]
        simp only [Path.coe_toContinuousMap, Path.trans_apply, genLoop_transAt_apply_path]
        split_ifs with h
        · change S.map _ = S.map (cubeFace (Fin.last (m + 1)) 0 _)
          rw [cubeFace_last_eq_snoc, update_last_eq_snoc_init]; rfl
        · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 1 _)
          rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]; rfl
      map_one_left := fun t => by
        change S.map (Fin.snoc (Fin.snoc (Fin.init t)
          (squareBoundaryHomotopy (1, t (Fin.last m))).1)
          (squareBoundaryHomotopy (1, t (Fin.last m))).2) = _
        rw [ContinuousMap.HomotopyWith.apply_one, squareLeftTop]
        simp only [Path.coe_toContinuousMap, Path.trans_apply, genLoop_transAt_apply_path]
        split_ifs with h
        · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 0 _)
          rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]; rfl
        · change S.map _ = S.map (cubeFace (Fin.last (m + 1)) 1 _)
          rw [cubeFace_last_eq_snoc, update_last_eq_snoc_init]; rfl
      prop' := fun s t ht ↦ ?_ }⟩
    refine Eq.trans ?_ ((GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
      (S.upperFaceLoop (Fin.last m).castSucc)).property t ht).symm
    obtain ⟨j, hj⟩ := ht
    obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · rcases h i with ⟨hi0, hi1⟩
      rcases hj with hj | hj
      · exact hi0 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
      · exact hi1 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
    · rcases hj with hj | hj
      · exact S.codimTwo _ ⟨(Fin.last m).castSucc, Fin.last (m + 1),
          Fin.castSucc_ne_last _, .inl (by simp [squareSweepCube, hj]),
          .inl (by simp [squareSweepCube, hj])⟩
      · exact S.codimTwo _ ⟨(Fin.last m).castSucc, Fin.last (m + 1),
          Fin.castSucc_ne_last _, .inr (by simp [squareSweepCube, hj]),
          .inr (by simp [squareSweepCube, hj])⟩
  have hq :
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last m).castSucc⟧ ⟦S.lowerFaceLoop (Fin.last (m + 1))⟧ =
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last (m + 1))⟧ ⟦S.lowerFaceLoop (Fin.last m).castSucc⟧ := by
    rw [HomotopyGroup.mul_spec (i := Fin.last m), HomotopyGroup.mul_spec (i := Fin.last m)]
    exact Quotient.sound hhtpy
  exact congrArg Additive.ofMul hq
