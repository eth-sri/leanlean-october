import RequestProject.PresConeStrictExcursionReplacement
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Every strict lower vertex of an actual relator apex belongs to the actual cylinder. -/
theorem presCone_lower_mem_cylinder j x (hx : x < apexOf w j) :
    x ∈ coneAdjBaseSet (S := circSet w) := by
  obtain ⟨k, t, _, he⟩ := (presPos_lt_apex_iff w j x).mp hx
  exact ⟨cylOuter _ (TCirc.pt w j k t), he.symm⟩

/-- An included strict germ with cylinder endpoints lies in the actual cylinder. -/
theorem presStrictGerm_in_cylinder e
    (hs : gSrcX (strictOrderCx (PresPos w)) e ∈ coneAdjBaseSet (S := circSet w))
    (ht : gTgtX (strictOrderCx (PresPos w)) e ∈ coneAdjBaseSet (S := circSet w)) :
    PathIn (· ∈ coneAdjBaseSet (S := circSet w))
      (mapPath (strictOrderIncl (PresPos w)) [e]) := by
  cases' e with e b
  cases b <;> exact pathIn_cons (by tauto) (pathIn_nil _)

/-- Every actual strict presentation path with cylinder endpoints reduces to an actual cylinder path. -/
theorem exists_presStrictPath_cylinder_reduction (hpos : ∀ j, 0 < (w j).length)
    p
    (a b : PresPos w) (ha : a ∈ coneAdjBaseSet (S := circSet w)) (hb : b ∈ coneAdjBaseSet (S := circSet w))
    (hp : IsPathX (strictOrderCx (PresPos w)) p a b) :
    ∃ q,
      IsPathX (orderCx (PresPos w)) q a b ∧
      PathIn (· ∈ coneAdjBaseSet (S := circSet w)) q ∧
      Htpy (orderCx (PresPos w)) a b (mapPath (strictOrderIncl (PresPos w)) p) q := by
  induction p using (measure List.length).wf.induction generalizing a b with
  | h p ih =>
    cases p with
    | nil =>
      subst b
      exact ⟨[], rfl, pathIn_nil _, Htpy.refl _⟩
    | cons e p =>
      cases' hp with hea hp
      have hsingle : IsPathX (strictOrderCx (PresPos w))
          [e] a (gTgtX (strictOrderCx (PresPos w)) e) := by simp_all
      cases ht : gTgtX (strictOrderCx (PresPos w)) e with
      | inl t =>
        have hm : gTgtX (strictOrderCx (PresPos w)) e ∈ coneAdjBaseSet (S := circSet w) :=
          by tauto
        obtain ⟨q, hq, hqc, hh⟩ := ih p (by tauto) _ b hm hb hp
        have hec := presStrictGerm_in_cylinder w e (hea ▸ ha) hm
        refine ⟨mapPath (strictOrderIncl _) [e] ++ q,
          by tauto, pathIn_append hec hqc, ?_⟩
        simpa [mapPath, List.map_cons, List.map_nil, List.singleton_append, strictOrderIncl, id_eq] using
          Htpy.append_congr (isPath_mapPath _ hsingle)
            (isPath_mapPath (strictOrderIncl (PresPos w)) hp) (Htpy.refl _) hh
      | inr j =>
        cases p with
        | nil =>
          have hbe := hp.symm.trans ht
          cases' hb with t htb
          have hn := htb.trans hbe
          cases hn
        | cons d p =>
          cases' hp with hds hp
          have hed := presCone_strictGerm_to_apex w j e ht
          have hdd := presCone_strictGerm_from_apex w j d (hds.symm.trans ht)
          cases' e with e es
          cases' d with d ds
          obtain ⟨rfl, he⟩ := hed
          obtain ⟨rfl, hd⟩ := hdd
          have hdc := presCone_lower_mem_cylinder w j d.val.1 (hd ▸ d.property)
          obtain ⟨q, hq, hqc, hh⟩ := ih p (by tauto) d.val.1 b hdc hb hp
          obtain ⟨r, hr, hrc, hhr⟩ := exists_presCone_strictEdge_excursion_replacement w j (hpos j) e d he hd
          subst a
          refine ⟨r ++ q, hr.append hq, pathIn_append hrc hqc, ?_⟩
          simpa [mapPath, List.map_cons, List.map_nil, List.cons_append, List.nil_append, strictOrderIncl, strictOrderCx, germSrc, if_true, id_eq] using
            Htpy.append_congr
              (by tauto)
              (isPath_mapPath (strictOrderIncl (PresPos w)) hp) hhr hh

/-- Every actual weak presentation path with cylinder endpoints reduces to an actual cylinder path. -/
theorem exists_presPath_cylinder_reduction (hpos : ∀ j, 0 < (w j).length)
    p
    (a b : PresPos w) (ha : a ∈ coneAdjBaseSet (S := circSet w))
    (hb : b ∈ coneAdjBaseSet (S := circSet w))
    (hp : IsPathX (orderCx (PresPos w)) p a b) :
    ∃ q,
      IsPathX (orderCx (PresPos w)) q a b ∧
      PathIn (· ∈ coneAdjBaseSet (S := circSet w)) q ∧
      Htpy (orderCx (PresPos w)) a b p q := by
  obtain ⟨q, hq, hc, hh⟩ := exists_presStrictPath_cylinder_reduction w hpos
    _ a b ha hb (normalizeOrdPath_isPath hp)
  exact ⟨q, hq, hc, (normalizeOrdPath_htpy hp).symm.trans hh⟩
