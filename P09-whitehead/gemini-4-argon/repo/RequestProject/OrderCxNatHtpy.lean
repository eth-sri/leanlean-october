module

public import RequestProject.OrderCxMonodromy

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

theorem htpy_mapPath_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) :
    ∀ (p : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt p u v →
      Htpy (orderCx Q) (f u) (g v)
        (mapPath (orderCxMap f hf) p ++ [ordPos (hfg v)])
        ([ordPos (hfg u)] ++ mapPath (orderCxMap g hg) p) := by
  have hsq_pos {a b : P} (h : a ≤ b) :
      Htpy (orderCx Q) (f a) (g b) [ordPos (hf h), ordPos (hfg b)]
        [ordPos (hfg a), ordPos (hg h)] :=
    (htpy_orderCx_tri (hf h) (hfg b)).trans (htpy_orderCx_tri (hfg a) (hg h)).symm
  have hsq_neg {a b : P} (h : a ≤ b) :
      Htpy (orderCx Q) (f b) (g a) [ordNeg (hf h), ordPos (hfg a)]
        [ordPos (hfg b), ordNeg (hg h)] := by
    have h1 := (hsq_pos h).congr_append (isPath_ordNeg (hf h)) (isPath_ordNeg (hg h))
    have h2 := (htpy_ordNeg_ordPos (hf h)).congr_append (isPath_nil' (f b))
      (show IsPath (orderCx Q).src (orderCx Q).tgt [ordPos (hfg b), ordNeg (hg h)] (f b) (g a)
        from ⟨rfl, rfl, rfl⟩)
    have h3 := (htpy_ordPos_ordNeg (hg h)).congr_append
      (show IsPath (orderCx Q).src (orderCx Q).tgt [ordNeg (hf h), ordPos (hfg a)] (f b) (g a)
        from ⟨rfl, rfl, rfl⟩) (isPath_nil' (g a))
    simp only [List.nil_append, List.cons_append, List.append_nil] at h1 h2 h3 ⊢
    exact (h3.symm.trans h1.symm).trans h2
  intro p; induction p with
  | nil => intro u v hp; cases hp; exact Htpy.refl _
  | cons eb p ih =>
      rintro u v ⟨hu, hrest⟩
      rcases eb with ⟨⟨⟨a, b⟩, hab⟩, _ | _⟩
      · have hub : u = b := hu; subst hub
        have h1 := Htpy.append_congr (isPath_ordNeg (hf hab))
          (isPath_append_iff.mpr ⟨f v, isPath_mapPath (orderCxMap f hf) hrest,
            isPath_ordPos (hfg v)⟩) (Htpy.refl _) (ih hrest)
        have h2 := Htpy.append_congr
          (show IsPath (orderCx Q).src (orderCx Q).tgt
            [ordNeg (hf hab), ordPos (hfg a)] (f u) (g a) from ⟨rfl, rfl, rfl⟩)
          (isPath_mapPath (orderCxMap g hg) hrest)
          (hsq_neg hab) (Htpy.refl _)
        simpa [mapPath, orderCxMap, ordPos, ordNeg, List.append_assoc] using h1.trans h2
      · have hua : u = a := hu; subst hua
        have h1 := Htpy.append_congr (isPath_ordPos (hf hab))
          (isPath_append_iff.mpr ⟨f v, isPath_mapPath (orderCxMap f hf) hrest,
            isPath_ordPos (hfg v)⟩) (Htpy.refl _) (ih hrest)
        have h2 := Htpy.append_congr
          (show IsPath (orderCx Q).src (orderCx Q).tgt
            [ordPos (hf hab), ordPos (hfg b)] (f u) (g b) from ⟨rfl, rfl, rfl⟩)
          (isPath_mapPath (orderCxMap g hg) hrest)
          (hsq_pos hab) (Htpy.refl _)
        simpa [mapPath, orderCxMap, ordPos, ordNeg, List.append_assoc] using h1.trans h2

theorem htpy_loop_mapPath_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {u : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p u u) :
    Htpy (orderCx Q) (g u) (g u) (mapPath (orderCxMap g hg) p)
      ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p ++ [ordPos (hfg u)]) := by
  have h1 := (htpy_mapPath_le hf hg hfg p hp).congr_append
    (isPath_ordNeg (hfg u)) (isPath_nil' (g u))
  have h2 := (htpy_ordNeg_ordPos (hfg u)).congr_append (isPath_nil' (g u))
    (isPath_mapPath (orderCxMap g hg) hp)
  simp only [List.nil_append, List.append_nil, List.cons_append] at h1 h2 ⊢
  exact h2.symm.trans h1.symm

end FiniteChains.Comb
