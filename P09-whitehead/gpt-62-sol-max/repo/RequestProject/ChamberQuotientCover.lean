module

public import RequestProject.ChamberQuotient
public import RequestProject.OrderPosetCovering

@[expose] public section

/-!
# The projection `Z → Q = Z/Γ` is a covering

`RequestProject/ChamberQuotient.lean` builds the quotient poset `Q` and the projection `zProj`.
Here the covering property is proved by **explicit unique lifts**: for every cell `z` of `Z` the
projection identifies the cells above `z` with the cells above `zProj z`, and likewise below.

* `FiniteChains.Davis.existsUnique_isGamma_inChamber` — a coset all of whose signs outside its
  type vanish contains exactly one element of `Γ` (this is the lift of the mixed order relation
  between the copy of the base and an old cell);
* `existsUnique_up_old`, `existsUnique_up_inChamber`, `existsUnique_down_old` — the unique lifts
  of the cofaces and the faces of an old cell, from the parity description of `W_T`;
* `FiniteChains.Davis.zProj_isPosetCover` and
  `FiniteChains.Davis.isCovering_orderCxMap_zProj` — the resulting combinatorial covering of the
  order complexes;
* `FiniteChains.Davis.pi1Map_qNew_injective` — **the conclusion**: the inclusion of the base
  poset `X` in the quotient `Q` is injective on fundamental groups.  The covering datum is
  supplied by the construction, not assumed.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {att : NeSpx A →o X}

/-! ### The unique element of `Γ` in a coset with vanishing outer signs -/

omit [Fintype V] in
/-- The sign map is an affine bijection on each spherical coset, with the outer signs fixed. -/
theorem existsUnique_inChamber_phi {p : Sph A} (t : V → ZMod 2)
    (h : ∀ v, v ∉ p.spx → t v = phi A p.rep v) :
    ∃! g : CayGroup A, InChamber g p ∧ phi A g = t := by
  obtain ⟨u, hu, hφ⟩ := exists_mem_specialSub_phi_eq A p.spx (t - phi A p.rep)
    (fun v hv => sub_eq_zero.mpr (h v hv))
  have hgu : InChamber (p.rep * u) p := by simpa [InChamber]
  have hgt : phi A (p.rep * u) = t := by rw [phi_mul, hφ]; abel
  refine ⟨p.rep * u, ⟨hgu, hgt⟩, fun g hg => ?_⟩
  apply mul_left_cancel (a := p.rep⁻¹)
  apply phi_injOn_specialSub A (commuting_of_isSimplex p.isSimplex) hg.1 hgu
  rw [phi_mul, phi_mul, hg.2, hgt]

omit [Fintype V] in
theorem existsUnique_isGamma_inChamber {p : Sph A}
    (h : ∀ v, v ∉ p.spx → phi A p.rep v = 0) :
    ∃! g : CayGroup A, IsGamma A g ∧ InChamber g p :=
  (existsUnique_congr fun _ => and_comm).mp (existsUnique_inChamber_phi 0 fun v hv => (h v hv).symm)

omit [Fintype V] in
private theorem qProj_chamberPt (g : CayGroup A) (c : QCube A)
    (h : ∀ v, v ∉ c.spx → phi A g v = c.sgn v) : qProjCube (chamberPt g c.isSimplex) = c :=
  qProjCube_eq_iff.2 ⟨rfl, fun v hv => (phi_rep_eq_of_inChamber (chamberPt_inChamber _ _) hv).trans (h v hv)⟩

omit [Fintype V] in
private theorem existsUnique_chamber_lift {g : CayGroup A} {c : QCube A}
    (h : ∀ v, v ∉ c.spx → phi A g v = c.sgn v) :
    ∃! r : Sph A, InChamber g r ∧ qProjCube r = c :=
  ⟨chamberPt g c.isSimplex, ⟨chamberPt_inChamber _ _, qProj_chamberPt _ _ h⟩,
    fun r hr => eq_of_inChamber_spx_eq hr.1 (chamberPt_inChamber _ _) (qProjCube_eq_iff.1 hr.2).1⟩

omit [Fintype V] in
theorem existsUnique_up_old {p : Sph A} {c : QCube A} (hle : qProjCube p ≤ c) :
    ∃! r : Sph A, p ≤ r ∧ qProjCube r = c := by
  have h := existsUnique_chamber_lift (g := p.rep) (c := c) fun v hv =>
    (qProjCube_sgn_of_not_mem (fun hp => hv (hle.1 hp))).symm.trans (hle.2 v hv)
  refine (existsUnique_congr fun r => ?_).mp h
  constructor
  · rintro ⟨hr, hc⟩
    exact ⟨le_of_inChamber (inChamber_rep p) hr ((qProjCube_eq_iff.1 hc).1.symm ▸ hle.1), hc⟩
  · rintro ⟨hr, hc⟩
    exact ⟨inChamber_rep_of_le hr, hc⟩

omit [Fintype V] in
theorem existsUnique_up_inChamber {w : CayGroup A} (hw : IsGamma A w) {c : QCube A}
    (hsgn : c.sgn = 0) : ∃! r : Sph A, InChamber w r ∧ qProjCube r = c :=
  existsUnique_chamber_lift fun v _ => congrFun ((show phi A w = 0 from hw).trans hsgn.symm) v

omit [Fintype V] in
theorem existsUnique_down_old {p : Sph A} {c : QCube A} (hle : c ≤ qProjCube p) :
    ∃! r : Sph A, r ≤ p ∧ qProjCube r = c := by
  obtain ⟨g, ⟨hg, hgt⟩, huniq⟩ := existsUnique_inChamber_phi (p := p) c.sgn
    (fun v hv => (hle.2 v hv).trans (qProjCube_sgn_of_not_mem hv))
  obtain ⟨r, ⟨hr, hrc⟩, hruniq⟩ := existsUnique_chamber_lift (c := c) (g := g) fun v _ => congrFun hgt v
  refine ⟨r, ⟨le_of_inChamber hr hg ((qProjCube_eq_iff.1 hrc).1.symm ▸ hle.1), hrc⟩, ?_⟩
  rintro r' ⟨hrp, hr'c⟩
  obtain ⟨g', ⟨hg', hgt'⟩, -⟩ := existsUnique_inChamber_phi (p := r') c.sgn
    (fun v hv => ((qProjCube_eq_iff.1 hr'c).2 v ((qProjCube_eq_iff.1 hr'c).1 ▸ hv)).symm)
  have he : g' = g := huniq g' ⟨inChamber_of_le hrp hg', hgt'⟩
  exact hruniq r' ⟨he ▸ hg', hr'c⟩

/-! ### The projection is a covering of posets -/

omit [Fintype V] in
private theorem lift_old {c : QCube A} (hc : ¬ (c.spx = ∅ ∧ c.sgn = 0))
    (P : Zpos A X (IsGamma A) att → Prop) (R : Sph A → Prop)
    (h : ∀ r hr, qProjCube r = c → (R r ↔ P (zOld r hr)))
    (hu : ∃! r, R r ∧ qProjCube r = c) :
    ∃! b, P b ∧ zProj b = qOld c hc := by
  obtain ⟨r, ⟨hr, he⟩, huniq⟩ := hu
  let hr' := not_isMarkedApex_of_qProjCube_eq hc he
  refine ⟨zOld r hr', ⟨(h r hr' he).1 hr, congrArg Sum.inl (Subtype.ext he)⟩, ?_⟩
  rintro (s | _) ⟨hs, hp⟩
  · have he' := congrArg Subtype.val (Sum.inl.inj hp)
    exact congrArg Sum.inl (Subtype.ext (huniq s.1 ⟨(h s.1 s.2 he').2 hs, he'⟩))
  · cases hp

omit [Fintype V] in
private theorem lift_new (y : X) (P : Zpos A X (IsGamma A) att → Prop)
    (hu : ∃! w, P (zNew w y)) : ∃! b, P b ∧ zProj b = qNew y := by
  obtain ⟨w, hw, huniq⟩ := hu
  refine ⟨zNew w y, ⟨hw, rfl⟩, ?_⟩
  rintro (_ | ⟨v, x⟩) ⟨hv, he⟩
  · cases he
  · have hxy : x = y := Sum.inr.inj he
    subst x
    exact congrArg (fun w => zNew w y) (huniq _ hv)

omit [Fintype V] in
/-- **Unique lifting of the cells above a cell of `Z`.** -/
theorem zProj_up (z : Zpos A X (IsGamma A) att) (q : Qpos A X att)
    (h : zProj z ≤ q) : ∃! b : Zpos A X (IsGamma A) att, z ≤ b ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl c => exact lift_old c.2 _ _ (fun _ _ _ => Iff.rfl) (existsUnique_up_old h)
      | inr _ => exact h.elim
  | inr wx =>
      cases q with
      | inl c =>
          obtain ⟨hsgn, hne, hx⟩ := h
          refine lift_old c.2 _ _ (fun r _ he => ?_)
            (existsUnique_up_inChamber wx.1.2 hsgn)
          have hs := (qProjCube_eq_iff.1 he).1
          exact ⟨fun hw => ⟨hw, hs.symm ▸ hne, hx.trans
            (le_of_eq (congrArg att (Subtype.ext hs.symm)))⟩, And.left⟩
      | inr y =>
          exact lift_new y _ ⟨wx.1, ⟨rfl, h⟩, fun _ hw => hw.1.symm⟩

omit [Fintype V] in
/-- **Unique lifting of the cells below a cell of `Z`.** -/
theorem zProj_down (z : Zpos A X (IsGamma A) att) (q : Qpos A X att)
    (h : q ≤ zProj z) : ∃! b : Zpos A X (IsGamma A) att, b ≤ z ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl c => exact lift_old c.2 _ _ (fun _ _ _ => Iff.rfl) (existsUnique_down_old h)
      | inr y =>
          obtain ⟨hsgn, hne, hy⟩ := h
          obtain ⟨g, ⟨hg, hgp⟩, huniq⟩ := existsUnique_isGamma_inChamber (p := p.1) fun v hv =>
            (qProjCube_sgn_of_not_mem hv).symm.trans (congrFun hsgn v)
          exact lift_new y _ ⟨⟨g, hg⟩, ⟨hgp, hne, hy⟩,
            fun w hw => Subtype.ext (huniq w.1 ⟨w.2, hw.1⟩)⟩
  | inr wx =>
      cases q with
      | inl _ => exact h.elim
      | inr y => exact lift_new y _ ⟨wx.1, ⟨rfl, h⟩, fun _ hw => hw.1⟩

/-- **The projection `Z → Q` is a covering of posets.** -/
theorem zProj_isPosetCover :
    Comb.IsPosetCover (zProj (A := A) (X := X) (att := att)) where
  mono := zProj_monotone
  surj := zProj_surjective
  up := zProj_up
  down := zProj_down

/-- **The projection induces a combinatorial covering of the order complexes.** -/
theorem isCovering_orderCxMap_zProj :
    Comb.IsCovering (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone) :=
  Comb.isCovering_orderCxMap zProj_isPosetCover

/-! ### The copy of the base is injective in `π₁(Q)` -/

omit [Fintype V] in
/-- The inclusion of the base in the quotient factors as the inclusion of a copy of the base in
`Z` followed by the covering projection. -/
theorem pi1Map_qNew_eq_comp (w : {w : CayGroup A // IsGamma A w}) (x : X) :
    Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x
      = (Comb.pi1Map (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
          (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
          (zNew_monotone w)) x) := by
  ext g
  exact Comb.pi1Map_comp_apply (orderCxMap _ (zNew_monotone (att := att) w))
    (orderCxMap _ zProj_monotone) x g

/-- **The inclusion of the base poset in the quotient is injective on fundamental groups.**
The covering datum comes from the construction: `Z → Q` is the covering
`isCovering_orderCxMap_zProj`, and a copy of the base is injective in `π₁(Z)` by
`pi1Map_zNew_injective_uncond`. -/
theorem pi1Map_qNew_injective (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x) := by
  rw [pi1Map_qNew_eq_comp ⟨1, isGamma_one⟩ x]
  exact pi1Map_zNew_covering_injective
    (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
    isCovering_orderCxMap_zProj ⟨1, isGamma_one⟩ x

end Davis
end FiniteChains
