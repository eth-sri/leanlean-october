module

public import RequestProject.OrderComplexFreeFace
public import RequestProject.OrderReflexiveConjugation
public import RequestProject.OrderComplexPi1Transfer

@[expose] public section

/-! Constructed loop representatives under the first elementary collapse deletion. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

/-- Deleting an actual free face preserves representatives of all loops based away from it. -/
theorem loop_representative_delete_free_face {C : P → Prop} {f t a : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t)
    {p : List ((orderCx P).E × Bool)} (ha : C a ∧ a ≠ f)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a a ∧
      PathIn (fun x => C x ∧ x ≠ f) l ∧ Htpy (orderCx P) a a p l := by
  obtain ⟨r, hr, hle, hne, hfix⟩ := exists_freeFace_upper_retraction ht hft hne hunique
  let aa : {x : P // C x} := ⟨a, ha.1⟩
  have hbase : (r aa).1 = a := congrArg Subtype.val (hfix aa ha.2)
  have hl := isPath_liftPathIn p hC aa.2 aa.2 hp
  have hm := monotone_subtypeVal.comp hr
  refine ⟨_, ?_, pathIn_mapPath_of_image hm (fun x => ⟨(r x).2, hne x⟩) (liftPathIn p hC), ?_⟩
  · have h := isPath_mapPath (orderCxMap _ hm) hl
    change IsPath _ _ _ (r aa).1 (r aa).1 at h
    rwa [hbase] at h
  · have h := htpy_loop_mapPath_le_fixed (g := Subtype.val ∘ r) monotone_subtypeVal hm hle
        hbase.symm _ hl
    change Htpy (orderCx P) a a (mapPath (subposetHom C) (liftPathIn p hC)) _ at h
    rwa [mapPath_liftPathIn] at h

end FiniteChains.Comb
