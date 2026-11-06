
import VaughtConjecture.Knight.PointwiseLabels
import VaughtConjecture.Knight.GradeSplice
import VaughtConjecture.Knight.SemScheme
namespace VaughtConjecture.Knight.GradeTailRestoration
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D L : CellScheme A}
  {sem : Semantics D} {low : Semantics L} {BJ : GradedIndex ι} {j : ℕ}
/-- Transport a lower lifting clause through a literal equivalence and splice
its result into an owner-bounded upper section. -/
theorem restore_map {X Y : Type*} (hj : j ≤ BJ.2)
    (e : L.below (BJ.1, j) ≃ D.below (BJ.1, j))
    (he : ∀ v, RespectsSemanticsBelow low (BJ.1, j) v ↔
      RespectsSemanticsBelow sem (BJ.1, j) (v ∘ e.symm))
    (inc : Y → X) (f : X → D.below BJ) (g : Y → L.below (BJ.1, j))
    (hmap : ∀ a, lowerIncl hj (e (g a)) = f (inc a))
    (hcover : ∀ d, D.grade (f d).1 ≤ j → ∃ a, inc a = d)
    {p : X → ExtOrd} {u : BelowLabels D BJ} {M : ExtOrd}
    (hu : RespectsSemanticsBelow sem BJ u)
    (hread : ∀ d, u (f d) = min (p d) M) (hbound : BoundedBy u M)
    (hhigh : ∀ d, ¬D.grade (f d).1 ≤ j → p d ≤ M)
    (hlift : ∀ q, RespectsSemanticsBelow low (BJ.1, j) q →
      (∀ a, min (q (g a)) M = min (p (inc a)) M) →
      ∃ v, RespectsSemanticsBelow low (BJ.1, j) v ∧
        (∀ a, v (g a) = p (inc a)) ∧ CappedEq v q M) :
    ∃ r, RespectsSemanticsBelow sem BJ r ∧
      (∀ d, r (f d) = p d) ∧ CappedEq r u M := by
  let q := fun d => u (lowerIncl hj (e d))
  have hq : RespectsSemanticsBelow low (BJ.1, j) q := by
    apply (he q).mpr
    simpa only [q, Function.comp_def, Equiv.apply_symm_apply,
      lowerIncl, CellScheme.below.mono] using hu.mono (show GradedLe (BJ.1, j) BJ from ⟨Finset.Subset.refl _, hj⟩)
  obtain ⟨v, hv, hvr, hvc⟩ := hlift q hq (fun a => by
    simp  [q, hmap, hread,  ])
  let w := v ∘ e.symm
  have hw := (he v).mp hv
  have hag d : min (w d) M = min (u (lowerIncl hj d)) M := by
    simpa only [w, q, Function.comp_def, Equiv.apply_symm_apply] using hvc (e.symm d)
  refine ⟨splice u w, splice_respects hj hu hw (fun d _ => hbound d) hag,
    ?_, splice_cap hj hag⟩
  intro d
  by_cases hd : D.grade (f d).1 ≤ j
  · obtain ⟨a, rfl⟩ := hcover d hd
    rw [splice_low u w _ hd]
    have hh : (⟨(f (inc a)).1, (f (inc a)).2.1, hd⟩) =
        e (g a) := Subtype.ext (congrArg Subtype.val (hmap a)).symm
    change v (e.symm _) = _
    rw [hh, Equiv.symm_apply_apply]
    exact hvr a
  · rw [splice_high u w hd, hread, min_eq_left (hhigh d hd)]
