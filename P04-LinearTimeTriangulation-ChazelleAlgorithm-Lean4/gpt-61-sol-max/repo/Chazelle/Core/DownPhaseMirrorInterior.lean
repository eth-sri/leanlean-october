module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseMirrorModel
public import Chazelle.Core.FactsInterior

/-!
# Mirror symmetry (F-D7), part 5: the interior model of the mirrored polygon

For a simple polygon `Q`, the interior model of `Q.mir` is the mirror image of the interior model
of `Q`, the walk traversed backwards with shift `n - 1` (`modelMir_interior`): the orientation
flips (`leftInside_mir`), so exactly one of the two interior walks is reversed.  The horizontal
chords and the vertex chords (`Visibility.chords`) of `Q.mir` are the mirrored ones, the
direction `σ` of a vertex chord becoming `-σ`.
-/

namespace Chazelle.Core

namespace Mir

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (IsHChordIn)
open Chazelle.Visibility (hseg rayPt)

variable {Q : Polygon}

/-- The interior of the mirrored polygon. -/
theorem mir_interior (Q : Polygon) :
    Q.mir.filled \ Q.mir.boundary = mir '' (Q.filled \ Q.boundary) := by
  rw [mir_filled, mir_boundary, image_sdiff mir_injective]

theorem hitSet_mir (Q : Polygon) (p : Point) (σ : ℝ) :
    Visibility.hitSet Q.mir (mir p) (-σ) = Visibility.hitSet Q p σ := by
  core_grind [mem_ofPred_eq, mir_rayPt, mir_boundary, mem_image_mir, mir_mir]

theorem chordSet_mir (Q : Polygon) (i : ℕ) (σ : ℝ) :
    Visibility.chordSet Q.mir i (-σ) = mir '' Visibility.chordSet Q i σ := by
  unfold Visibility.chordSet Visibility.chordEnd Visibility.chordParam Visibility.hitParam
  rw [mir_vtx, hitSet_mir, mir_segment, mir_rayPt]

theorem dirInterior_mir (Q : Polygon) (i : ℕ) (σ : ℝ) :
    Visibility.DirInterior Q.mir i (-σ) ↔ Visibility.DirInterior Q i σ := by
  grind [Visibility.DirInterior, mir_vtx, mir_rayPt, mir_interior, mem_image_mir, mir_mir]

/-- **The vertex chords of the mirrored polygon.** -/
theorem chords_mir (Q : Polygon) : Visibility.chords Q.mir = mirF (Visibility.chords Q) := by
  ext c
  rw [mem_mirF]
  constructor
  · rintro ⟨i, σ, hi, hσ, hD, rfl⟩
    rw [mir_n] at hi
    refine ⟨i, -σ, hi, by grind, ?_, ?_⟩
    all_goals (grind [dirInterior_mir, neg_neg, chordSet_mir, image_mir_image_mir])
  · rintro ⟨i, σ, hi, hσ, hD, hc⟩
    refine ⟨i, -σ, by simp_all, by grind,
      (dirInterior_mir Q i σ).2 hD, ?_⟩
    grind [chordSet_mir, image_mir_image_mir]

/-- **The horizontal chords of the mirrored interior.** -/
theorem adm_mir (D : Set Point) :
    {c | ∃ y a b : ℝ, IsHChordIn (mir '' D) y a b ∧ c = hseg y a b} =
      mirF {c | ∃ y a b : ℝ, IsHChordIn D y a b ∧ c = hseg y a b} := by
  ext c
  rw [mem_mirF]
  constructor
  · rintro ⟨y, a, b, hch, rfl⟩
    refine ⟨y, -b, -a, ?_, hseg_mir y a b⟩
    grind [isHChordIn_mir, neg_neg]
  · rintro ⟨y, a, b, hch, hc⟩
    refine ⟨y, -b, -a, isHChordIn_mir.2 hch, ?_⟩
    grind [hseg_mir, image_mir_image_mir]

theorem interiorWalk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  unfold interiorWalk; split_ifs
  · rfl
  · exact FactsInterior.rev_n Q

/-- **The interior walk of the mirrored polygon.** -/
theorem walkMir_interior (hQ : Q.Simple) :
    WalkMir (interiorWalk Q) (interiorWalk Q.mir) (Q.n - 1) := by
  have h3 := Chazelle.Jordan.simple_three_le hQ
  have hL := leftInside_mir Q hQ
  have hWn := interiorWalk_n Q
  refine ⟨by core_grind, by omega, fun j hj => ?_⟩
  rw [hWn] at hj ⊢
  have hidx : (Q.n - 1 + Q.n - j) % Q.n = Q.n - 1 - j := by
    rw [show Q.n - 1 + Q.n - j = (Q.n - 1 - j) + Q.n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  rw [hidx]
  unfold interiorWalk
  by_cases hQL : Mountain.LeftInside Q
  · have hM : ¬ Mountain.LeftInside Q.mir := fun h => hL.1 h hQL
    rw [ite_eq_right hM, ite_eq_left hQL, FactsInterior.rev_vtx _ j (by simp_all), mir_n,
      mir_vtx]
  · have hM : Mountain.LeftInside Q.mir := hL.2 hQL
    rw [ite_eq_left hM, ite_eq_right hQL, FactsInterior.rev_vtx _ _ (by omega), mir_vtx,
      show Q.n - 1 - (Q.n - 1 - j) = j by omega]

/-- **The interior model of the mirrored polygon is the mirrored interior model.** -/
theorem modelMir_interior (hQ : Q.Simple) :
    ModelMir (interiorModel Q) (interiorModel Q.mir) (Q.n - 1) where
  D := mir_interior Q
  walk := walkMir_interior hQ
  counted _ _ := Iff.rfl
  Adm := by
    show {c | ∃ y a b : ℝ, IsHChordIn (Q.mir.filled \ Q.mir.boundary) y a b ∧ c = hseg y a b} = _
    rw [mir_interior]; exact adm_mir _
  Full := chords_mir Q

end

end Mir

end Chazelle.Core
