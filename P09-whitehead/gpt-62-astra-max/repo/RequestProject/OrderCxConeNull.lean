module


public import RequestProject.OrderCxNatHtpy

@[expose] public section

/-!
# Loops dominated by a monotone map into a cone

`FiniteChains.Comb.htpy_nil_of_pathIn_le_top` kills a loop that lies inside a subposet *with a
largest element*.  The subposets used to fill the polygon of a surface are not of that kind: a
chain of cells of a triangle can be enlarged by the triangle itself, but no chain contains all
of them.  What is available there is a monotone map `g` above the inclusion and above a constant,
and that is enough:

* `FiniteChains.Comb.htpy_nil_mapPath_of_const_le` — if `f ≤ g` and `c ≤ g` for monotone maps
  `f g : P → Q` and a constant `c`, then the image under `f` of every loop of `orderCx P` is
  null-homotopic in `orderCx Q`;
* `FiniteChains.Comb.htpy_nil_of_pathIn_cone` — the form used in practice: a loop of `orderCx P`
  all of whose edges lie in a subposet `A` which carries a monotone map `g` above the inclusion
  and above a fixed element is null-homotopic in `orderCx P`.
-/

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- The image of a path under a constant map is null-homotopic: all its edges lie in the
subposet `{c}`, which has a largest element. -/
theorem htpy_nil_mapPath_const (c : Q) {u : P} {p : List _}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p u u) :
    Htpy _ c c
      (mapPath (orderCxMap (fun _ : P => c) monotone_const) p) [] := by
  refine htpy_nil_of_pathIn_le_top (A := fun x : Q => x = c) rfl
    (fun x hx => le_of_eq hx) rfl (isPath_mapPath (orderCxMap (fun _ : P => c) monotone_const) hp) ?_
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨e', -, rfl⟩ := he <;> aesop

/-- **Loops dominated by a cone die.**  If the monotone map `g` lies above the monotone map `f`
and above a constant, then the image under `f` of every loop is null-homotopic. -/
theorem htpy_nil_mapPath_of_const_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) (c : Q) (hcg : ∀ x, c ≤ g x) {u : P}
    {p : List _}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p u u) :
    Htpy _ (f u) (f u) (mapPath (orderCxMap f hf) p) [] := by
  have hfp :=
    isPath_mapPath (orderCxMap f hf) hp
  have hcp :=
    isPath_mapPath (orderCxMap (fun _ : P => c) monotone_const) hp
  -- both images are conjugate to the image under `g`
  have h2 := htpy_loop_mapPath_le monotone_const hg hcg hp
  -- the image under the constant map is trivial
  have h4 :=
    htpy_ordNeg_ordPos (hcg u)
  have hgnil : Htpy _ (g u) (g u) (mapPath (orderCxMap g hg) p) [] := by
    refine h2.trans (((htpy_nil_mapPath_const c hp).congr_append (isPath_ordNeg (hcg u)) (isPath_ordPos (hcg u))).trans ?_)
    assumption
  -- hence the conjugate of the image under `f` is trivial
  have hconj := (htpy_loop_mapPath_le hf hg hfg hp).symm.trans hgnil
  -- peel the conjugation off
  have hcancel :=
    htpy_ordPos_ordNeg (hfg u)
  have hleft : Htpy _ (f u) (f u)
      ([ordPos (hfg u)] ++ ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p
        ++ [ordPos (hfg u)]) ++ [ordNeg (hfg u)]) [] := by
    refine (hconj.congr_append (isPath_ordPos (hfg u)) (isPath_ordNeg (hfg u))).trans ?_
    assumption
  -- the left hand side is homotopic to the image itself
  have hid : Htpy _ (f u) (f u) (mapPath (orderCxMap f hf) p)
      ([ordPos (hfg u)] ++ ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p
        ++ [ordPos (hfg u)]) ++ [ordNeg (hfg u)]) := by
    have hA : Htpy _ _ (f u)
        _
        ([] ++ (mapPath (orderCxMap f hf) p ++ [ordPos (hfg u), ordNeg (hfg u)])) :=
      hcancel.congr_append (isPath_nil' (f u))
        (isPath_append_iff.mpr ⟨f u, hfp, ⟨rfl, rfl, rfl⟩⟩)
    have hB :=
      Htpy.append_congr hfp
        (show IsPath (orderCx Q).src (orderCx Q).tgt [ordPos (hfg u), ordNeg (hfg u)]
          (f u) (f u) from ⟨rfl, rfl, rfl⟩)
        (Htpy.refl _) hcancel
    have : Htpy _ (f u) (f u)
        ([ordPos (hfg u), ordNeg (hfg u)] ++ (mapPath (orderCxMap f hf) p
          ++ [ordPos (hfg u), ordNeg (hfg u)]))
        (mapPath (orderCxMap f hf) p) := by
      refine hA.trans ?_
      simp_all
    simpa [List.append_assoc] using this.symm
  exact hid.trans hleft

/-- **A loop inside a subposet carrying a cone is null-homotopic.**  The subposet `A` need not
have a largest element: it is enough to have a monotone map `g` on `A`, with values in the
ambient poset, which lies above the inclusion and above one fixed element. -/
theorem htpy_nil_of_pathIn_cone {A : P → Prop} (g : {x : P // A x} → P) (hg : Monotone g)
    (hfg : ∀ x : {x : P // A x}, x ≤ g x) (d : P) (hdg : ∀ x : {x : P // A x}, d ≤ g x)
    {v : P} (hv : A v) {l : List _}
    (hp : IsPath (orderCx P).src (orderCx P).tgt l v v) (hl : PathIn A l) :
    Htpy _ v v l [] := by
  have h := htpy_nil_mapPath_of_const_le
    monotone_subtypeVal hg hfg d hdg (isPath_liftPathIn l hl hv hv hp)
  rw [show mapPath (orderCxMap (fun x : {x : P // A x} => (x : P)) monotone_subtypeVal)
      _ = l from mapPath_liftPathIn l hl] at h <;> assumption

end Comb
end FiniteChains
