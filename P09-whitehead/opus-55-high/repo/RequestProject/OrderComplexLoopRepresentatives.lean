import RequestProject.OrderComplexFreeFace
import RequestProject.OrderCxNatHtpy


/-! Constructed loop representatives under the first elementary collapse deletion. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

/-- Every loop based in `B` has a representative in `B` under an increasing order map
from `C` to `B`. The connecting germs at its base are included explicitly. -/
theorem loop_representative_of_monotone_map {C B}
    (hBC : ∀ x, B x → C x) (r : {x : P // C x} → P) (hr : Monotone r)
    (hrB : ∀ x, B (r x)) (hle : ∀ x, x.1 ≤ r x)
    {a : P} {p} (ha : B a)
    (hp : IsPathX (orderCx P) p a a) (hC : PathIn C p) :
    ∃ l, IsPathX (orderCx P) l a a ∧ PathIn B l ∧
      Htpy (orderCx P) a a p l := by
  let aC : {x : P // C x} := by tauto
  let l := mapPath (orderCxMap r hr) (liftPathIn p hC)
  have hl :=
    isPath_mapPath (orderCxMap r hr) (isPath_liftPathIn p hC aC.2 aC.2 hp)
  have hlB : PathIn B l := by
    intro e he
    obtain ⟨eb, _, rfl⟩ := List.mem_map.mp he
    tauto
  let e := [ordPos (hle aC)]
  let en := [ordNeg (hle aC)]
  have he : IsPathX (orderCx P) e a (r aC) := isPath_ordPos _
  have hen : IsPathX (orderCx P) en (r aC) a := isPath_ordNeg _
  have heB : PathIn B e := pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)
  have henB : PathIn B en := pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)
  have hnat := htpy_mapPath_le monotone_subtypeVal hr hle
    _ (isPath_liftPathIn p hC aC.2 aC.2 hp)
  change Htpy _ a (r aC)
    (mapPath (subposetHom C) (liftPathIn p hC) ++ e) (e ++ l) at hnat
  rw [mapPath_liftPathIn] at hnat
  have hpush := hnat.congr_append (show IsPathX (orderCx P) [] a a from rfl) hen
  have hkill := (htpy_ordPos_ordNeg (hle aC)).congr_append hp
    (show IsPathX (orderCx P) [] a a from rfl)
  refine ⟨e ++ l ++ en, (he.append hl).append hen,
    pathIn_append (pathIn_append heB hlB) henB, ?_⟩
  have hstrip : Htpy _ a a p ((p ++ e) ++ en) := by
    simpa [e, en, List.append_assoc] using hkill.symm
  exact hstrip.trans (by simp_all)

/-- Deleting an actual free face preserves representatives of all loops based away from it. -/
theorem loop_representative_delete_free_face {f t a : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t)
    {p} (ha : C a ∧ a ≠ f)
    (hp : IsPathX (orderCx P) p a a) (hC : PathIn C p) :
    ∃ l, IsPathX (orderCx P) l a a ∧
      PathIn (fun x => C x ∧ x ≠ f) l ∧ Htpy (orderCx P) a a p l := by
  classical
  let r : {x : P // C x} → P := fun x => if x.1 = f then t else x.1
  have hr : Monotone r := by
    intro x y hxy
    by_cases hx : x.1 = f
    · aesop
    · by_cases hy : y.1 = f
      · have hxf : x.1 ≤ f := hy ▸ hxy
        grind
      aesop
  apply loop_representative_of_monotone_map (by simp_all) r hr ?_ ?_ ha hp hC
  · grind
  grind
