import Mathlib.Tactic

import RequestProject.ChamberQuotient
import RequestProject.OrderPosetCovering

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

namespace FiniteChains.Davis


open RACG Mirror Comb


variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {att : NeSpx A →o X}

/-! ### The unique element of `Γ` in a coset with vanishing outer signs -/

section
omit [Fintype V]
variable {p : Sph A}
/-- **A coset whose signs outside its type vanish contains exactly one element of `Γ`.** -/
theorem existsUnique_isGamma_inChamber 
    (h : ∀ v, v ∉ p.spx → phi A p.rep v = 0) :
    ∃! g : CayGroup A, IsGamma A g ∧ InChamber g p := by
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then phi A p.rep v else 0) (fun v hv => by simp [hv])
  refine ⟨p.rep * u, ⟨?_, ?_⟩, ?_⟩
  · show phi A (p.rep * u) = 0
    funext v
    simp only [phi_mul, Pi.add_apply, Pi.zero_apply, hphiu]
    by_cases hv : v ∈ p.spx
    · rw [if_pos hv, zmod2_add_self]
    · rw [if_neg hv, add_zero, h v hv]
  · show p.rep⁻¹ * (p.rep * u) ∈ specialSub A (p.spx : Set V)
    rw [inv_mul_cancel_left]
    exact hu
  · rintro g ⟨hg, hgp⟩
    have hmem : (p.rep * u)⁻¹ * g ∈ specialSub A (p.spx : Set V) := by
      have h1 : (p.rep * u)⁻¹ * g = u⁻¹ * (p.rep⁻¹ * g) := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hgp
    have hzero : phi A ((p.rep * u)⁻¹ * g) = 0 := by
      funext v
      have hpu : phi A (p.rep * u) = 0 := by
        funext w
        simp only [phi_mul, Pi.add_apply, Pi.zero_apply, hphiu]
        by_cases hw : w ∈ p.spx
        · rw [if_pos hw, zmod2_add_self]
        · rw [if_neg hw, add_zero, h w hw]
      simp only [phi_mul, phi_inv, Pi.add_apply, Pi.zero_apply, hpu,
        show phi A g = 0 from hg]
      simp
    have := eq_one_of_mem_specialSub_of_phi_eq_zero A
      (commuting_of_isSimplex p.isSimplex) hmem hzero
    exact (inv_mul_eq_one.mp this).symm

/-! ### Unique lifts of the cofaces and the faces of an old cell -/

/-- **Unique lift of a coface of an old cell.** -/
theorem existsUnique_up_old  {c : QCube A} (hle : qProjCube p ≤ c) :
    ∃! r : Sph A, p ≤ r ∧ qProjCube r = c := by
  refine ⟨chamberPt p.rep c.isSimplex, ⟨⟨hle.1, ?_⟩, ?_⟩, ?_⟩
  · have hin  :=
      chamberPt_inChamber p.rep c.isSimplex
    have := Subgroup.inv_mem _ hin
    rw [mul_inv_rev, inv_inv] at this
    exact this
  · rw [qProjCube_eq_iff]
    refine ⟨rfl, fun v hv => ?_⟩
    have hv' : v ∉ (chamberPt p.rep c.isSimplex).spx := by simpa using hv
    rw [phi_rep_eq_of_inChamber (chamberPt_inChamber p.rep c.isSimplex) hv']
    have hvp  := fun hc => hv (hle.1 hc)
    rw [← qProjCube_sgn_of_not_mem hvp]
    exact hle.2 v hv
  · aesop (add unsafe apply [FiniteChains.Davis.eq_of_inChamber_spx_eq, FiniteChains.Davis.inChamber_rep_of_le, FiniteChains.Davis.chamberPt_inChamber])

/-- **Unique lift of a cube inside a chamber**: a cube of the quotient with vanishing signs has
exactly one lift in the chamber of a given element of `Γ`. -/
theorem existsUnique_up_inChamber {w : CayGroup A} (hw : IsGamma A w) {c : QCube A}
    (hsgn : c.sgn = 0) :
    ∃! r : Sph A, InChamber w r ∧ qProjCube r = c := by
  refine ⟨chamberPt w c.isSimplex, ⟨chamberPt_inChamber w c.isSimplex, ?_⟩, ?_⟩
  · rw [qProjCube_eq_iff]
    refine ⟨rfl, fun v hv => ?_⟩
    have hv' : v ∉ (chamberPt w c.isSimplex).spx := by simpa using hv
    rw [phi_rep_eq_of_inChamber (chamberPt_inChamber w c.isSimplex) hv']
    rw [show phi A w v = 0 from by simpa using congrFun (show phi A w = 0 from hw) v]
    exact (congrFun hsgn v).symm
  · aesop (add unsafe apply [FiniteChains.Davis.eq_of_inChamber_spx_eq, FiniteChains.Davis.chamberPt_inChamber])

/-- **Unique lift of a face of an old cell.**  The face directions fix the element of `W_T`
modulo the special subgroup of the face, by the parity description of `W_T`. -/
theorem existsUnique_down_old  {c : QCube A} (hle : c ≤ qProjCube p) :
    ∃! r : Sph A, r ≤ p ∧ qProjCube r = c := by
  classical
  have hUT  := hle.1
  have hout : ∀ v, v ∉ p.spx → c.sgn v = phi A p.rep v := by
    intro v hv
    rw [hle.2 v hv, qProjCube_sgn_of_not_mem hv]
  -- the element of `W_T` correcting the parities inside `T`
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then c.sgn v + phi A p.rep v else 0) (fun v hv => by simp [hv])
  set r : Sph A := chamberPt (p.rep * u) c.isSimplex with hrdef
  have hinr : InChamber (p.rep * u) r := chamberPt_inChamber _ _
  have hrspx : r.spx = c.spx := rfl
  have hrc : qProjCube r = c := by
    rw [qProjCube_eq_iff]
    refine ⟨hrspx, fun v hv => ?_⟩
    have hv' : v ∉ r.spx := by rw [hrspx]; exact hv
    rw [phi_rep_eq_of_inChamber hinr hv']
    simp only [phi_mul, Pi.add_apply, hphiu]
    by_cases hvT : v ∈ p.spx
    · grind
    · rw [if_neg hvT, add_zero, hout v hvT]
  have hrp : r ≤ p := by
    refine ⟨by rw [hrspx]; exact hUT, ?_⟩
    have h1  := hinr
    have h2  :=
      specialSub_mono (by assumption) h1
    have h3 : r.rep⁻¹ * p.rep = (r.rep⁻¹ * (p.rep * u)) * u⁻¹ := by group
    rw [h3]
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hu)
  refine ⟨r, ⟨hrp, hrc⟩, ?_⟩
  rintro r' ⟨hr'p, hr'c⟩
  have hspx : r.spx = r'.spx := by rw [hrspx, (qProjCube_eq_iff.1 hr'c).1]
  -- the two lifts differ by an element of `W_T` with parity supported in the face
  set k : CayGroup A := r.rep⁻¹ * r'.rep with hkdef
  have hkT : k ∈ specialSub A (p.spx : Set V) := by
    have h1  := hrp.2
    have h2 : p.rep⁻¹ * r'.rep ∈ specialSub A (p.spx : Set V) := by
      have := Subgroup.inv_mem _ hr'p.2
      rwa [mul_inv_rev, inv_inv] at this
    have h3 : k = (r.rep⁻¹ * p.rep) * (p.rep⁻¹ * r'.rep) := by rw [hkdef]; group
    rw [h3]
    exact Subgroup.mul_mem _ h1 h2
  have hkout : ∀ v, v ∉ c.spx → phi A k v = 0 := by
    classical simp_all [FiniteChains.Davis.qProjCube_eq_iff, FiniteChains.RACG.phi_mul, FiniteChains.RACG.phi_inv, Pi.add_apply, FiniteChains.RACG.zmod2_add_self]
  obtain ⟨k0, hk0U, hk0⟩ := exists_mem_specialSub_phi_eq A c.spx (phi A k)
    (fun v hv => hkout v hv)
  have hk0T  :=
    specialSub_mono (by exact_mod_cast hUT) hk0U
  have hkk0  :=
    phi_injOn_specialSub A (commuting_of_isSimplex p.isSimplex) hkT hk0T hk0.symm
  have hinr' : InChamber r'.rep r := by
    aesop
  exact (eq_of_inChamber_spx_eq (x := r'.rep) hinr' (inChamber_rep r') hspx).symm

/-! ### The projection is a covering of posets -/

variable (z : Zpos A X (IsGamma A) att)
/-- **Unique lifting of the cells above a cell of `Z`.** -/
theorem zProj_up  (q : Qpos A X att)
    (h : zProj z ≤ q) : ∃! b : Zpos A X (IsGamma A) att, z ≤ b ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨r, ⟨hpr, hrc⟩, huniq⟩ := existsUnique_up_old (p := p.1) (c := c) h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨hpr, ?_⟩, ?_⟩
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have hr'c  := congrArg Subtype.val (Sum.inl.inj hproj)
              have  := huniq r'.1 ⟨hle, hr'c⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y => exact h.elim
  | inr wx =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨hsgn, hne, hx⟩ := h
          obtain ⟨r, ⟨hwr, hrc⟩, huniq⟩ :=
            existsUnique_up_inChamber (w := wx.1.1) wx.1.2 (c := c) hsgn
          have hspx  := (qProjCube_eq_iff.1 hrc).1
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨⟨hwr, ?_⟩, ?_⟩, ?_⟩
          · simp_all
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have hr'c  := congrArg Subtype.val (Sum.inl.inj hproj)
              have  := huniq r'.1 ⟨hle.1, hr'c⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · have hy  := Sum.inr.inj hproj
            refine congrArg Sum.inr (Prod.ext ?_ hy)
            exact hle.1.symm

/-- **Unique lifting of the cells below a cell of `Z`.** -/
theorem zProj_down  (q : Qpos A X att)
    (h : q ≤ zProj z) : ∃! b : Zpos A X (IsGamma A) att, b ≤ z ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨r, ⟨hrp, hrc⟩, huniq⟩ := existsUnique_down_old (p := p.1) (c := c) h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨hrp, ?_⟩, ?_⟩
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have hr'c  := congrArg Subtype.val (Sum.inl.inj hproj)
              have  := huniq r'.1 ⟨hle, hr'c⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y =>
          obtain ⟨hsgn, hne, hy⟩ := h
          have hzero : ∀ v, v ∉ p.1.spx → phi A p.1.rep v = 0 := by
            intro v hv
            rw [← qProjCube_sgn_of_not_mem hv]
            simpa using congrFun hsgn v
          obtain ⟨g, ⟨hg, hgp⟩, huniq⟩ := existsUnique_isGamma_inChamber hzero
          refine ⟨zNew ⟨g, hg⟩ y, ⟨⟨hgp, hne, hy⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · have hy'  := Sum.inr.inj hproj
            refine congrArg Sum.inr (Prod.ext (Subtype.ext ?_) hy')
            exact huniq v.1 ⟨v.2, hle.1⟩
  | inr wx =>
      cases q with
      | inl cc => exact h.elim
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · have hy  := Sum.inr.inj hproj
            refine congrArg Sum.inr (Prod.ext ?_ hy)
            exact hle.1
end

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

section
omit [Fintype V]
variable (w : {w : CayGroup A // IsGamma A w})
theorem mapPath_zProj_zNew 
    (l : List ((orderCx X).E × Bool)) :
    Comb.mapPath (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
        (Comb.mapPath (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
          (zNew_monotone w)) l)
      = Comb.mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) l := by
  aesop (add simp [Comb.mapPath])

/-- The inclusion of the base in the quotient factors as the inclusion of a copy of the base in
`Z` followed by the covering projection. -/
theorem pi1Map_qNew_eq_comp  (x : X) :
    Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x
      = (Comb.pi1Map (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
          (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
          (zNew_monotone w)) x) := by
  ext g
  induction g using Quotient.inductionOn with
  | h l =>
      refine Quotient.sound ?_
      simp_all [FiniteChains.Davis.mapPath_zProj_zNew]
end

/-- **The inclusion of the base poset in the quotient is injective on fundamental groups.**
The covering datum comes from the construction: `Z → Q` is the covering
`isCovering_orderCxMap_zProj`, and a copy of the base is injective in `π₁(Z)` by
`pi1Map_zNew_injective_uncond`. -/
abbrev pi1Map_qNew_injective (x : X)  :=
  Eq.mpr
    (id
      (congrArg
        (fun
            (_a :
              FiniteChains.Comb.Pi1 (FiniteChains.Comb.orderCx X) x →*
                FiniteChains.Comb.Pi1 (FiniteChains.Comb.orderCx (FiniteChains.Davis.Qpos A X att))
                  ((FiniteChains.Comb.orderCxMap FiniteChains.Davis.qNew FiniteChains.Davis.qNew_monotone).onV x)) =>
          Function.Injective ⇑_a)
        (FiniteChains.Davis.pi1Map_qNew_eq_comp ⟨1, FiniteChains.Davis.isGamma_one⟩ x)))
    (FiniteChains.Davis.pi1Map_zNew_covering_injective
      (FiniteChains.Comb.orderCxMap FiniteChains.Davis.zProj FiniteChains.Davis.zProj_monotone)
      FiniteChains.Davis.isCovering_orderCxMap_zProj ⟨1, FiniteChains.Davis.isGamma_one⟩ x)

end FiniteChains.Davis

