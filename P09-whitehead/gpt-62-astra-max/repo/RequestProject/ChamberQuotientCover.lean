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
/-- **A coset whose signs outside its type vanish contains exactly one element of `Γ`.** -/
theorem existsUnique_isGamma_inChamber {p : Sph A}
    (h : ∀ v, v ∉ p.spx → phi A p.rep v = 0) :
    ∃! g : CayGroup A, IsGamma A g ∧ InChamber g p := by
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then phi A p.rep v else 0) (fun v hv => by simp [hv])
  refine ⟨p.rep * u, ⟨?_, ?_⟩, ?_⟩
  · funext v
    simp only [phi_mul, Pi.add_apply, Pi.zero_apply, hphiu] <;> grind
  · show p.rep⁻¹ * (p.rep * u) ∈ specialSub A p.spx
    simp_all
  · rintro g ⟨hg, hgp⟩
    have hmem : (p.rep * u)⁻¹ * g ∈ specialSub A p.spx := by
      have h1 : (p.rep * u)⁻¹ * g = u⁻¹ * (p.rep⁻¹ * g) := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hgp
    have hzero : phi A ((p.rep * u)⁻¹ * g) = 0 := by
      have hpu : phi A (p.rep * u) = 0 := by
        funext w
        simp only [phi_mul, Pi.add_apply, Pi.zero_apply, hphiu]
        by_cases hw : w ∈ p.spx
        · simp_all [if_pos, zmod2_add_self]
        · simp_all
      simp only [phi_mul, phi_inv, Pi.add_apply, Pi.zero_apply, hpu,
        show phi A g = 0 from hg]
      simp
    have := eq_one_of_mem_specialSub_of_phi_eq_zero A
      (commuting_of_isSimplex p.isSimplex) hmem hzero
    exact (inv_mul_eq_one.mp this).symm

/-! ### Unique lifts of the cofaces and the faces of an old cell -/

omit [Fintype V] in
/-- **Unique lift of a coface of an old cell.** -/
theorem existsUnique_up_old {p : Sph A} {c : QCube A} (hle : qProjCube p ≤ c) :
    ∃! r : Sph A, p ≤ r ∧ qProjCube r = c := by
  refine ⟨chamberPt p.rep c.isSimplex, ⟨⟨hle.1, ?_⟩, ?_⟩, ?_⟩
  · have := Subgroup.inv_mem _ (chamberPt_inChamber p.rep c.isSimplex)
    assumption
  · rw [qProjCube_eq_iff]
    refine ⟨rfl, fun v hv => ?_⟩
    rw [phi_rep_eq_of_inChamber (chamberPt_inChamber p.rep c.isSimplex) (by simpa using hv)]
    rw [← qProjCube_sgn_of_not_mem (fun hc => hv (hle.1 hc))]
    apply hle.2 <;> assumption
  · rintro r ⟨hpr, hrc⟩
    refine eq_of_inChamber_spx_eq (inChamber_rep_of_le hpr)
      (chamberPt_inChamber p.rep c.isSimplex) ?_ <;> aesop

omit [Fintype V] in
/-- **Unique lift of a cube inside a chamber**: a cube of the quotient with vanishing signs has
exactly one lift in the chamber of a given element of `Γ`. -/
theorem existsUnique_up_inChamber {w : CayGroup A} (hw : IsGamma A w) {c : QCube A}
    (hsgn : c.sgn = 0) :
    ∃! r : Sph A, InChamber w r ∧ qProjCube r = c := by
  refine ⟨chamberPt w c.isSimplex, ⟨chamberPt_inChamber w c.isSimplex, ?_⟩, ?_⟩
  · rw [qProjCube_eq_iff]
    refine ⟨rfl, fun v hv => ?_⟩
    rw [phi_rep_eq_of_inChamber (chamberPt_inChamber w c.isSimplex) (by simpa using hv)]
    rw [show phi A w v = 0 from by solve_by_elim]
    simp_all
  · rintro r ⟨hwr, hrc⟩
    refine eq_of_inChamber_spx_eq hwr (chamberPt_inChamber w c.isSimplex) ?_ <;> aesop

omit [Fintype V] in
/-- **Unique lift of a face of an old cell.**  The face directions fix the element of `W_T`
modulo the special subgroup of the face, by the parity description of `W_T`. -/
theorem existsUnique_down_old {p : Sph A} {c : QCube A} (hle : c ≤ qProjCube p) :
    ∃! r : Sph A, r ≤ p ∧ qProjCube r = c := by
  classical
  have hUT := hle.1
  have hout : ∀ v, v ∉ p.spx → c.sgn v = phi A p.rep v := by
    simp_all [hle.2, qProjCube_sgn_of_not_mem]
  -- the element of `W_T` correcting the parities inside `T`
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then c.sgn v + phi A p.rep v else 0) (fun v hv => by simp [hv])
  set r : Sph A := chamberPt _ c.isSimplex with hrdef
  have hinr : InChamber (p.rep * u) r := chamberPt_inChamber _ _
  have hrc : qProjCube r = c := by
    rw [qProjCube_eq_iff]
    refine ⟨rfl, fun v hv => ?_⟩
    rw [phi_rep_eq_of_inChamber hinr (hv)]
    simp only [phi_mul, Pi.add_apply, hphiu]
    by_cases hvT : v ∈ p.spx
    · rw [if_pos hvT]
      have hre : phi A p.rep v + (c.sgn v + phi A p.rep v)
          = c.sgn v + (phi A p.rep v + phi A p.rep v) := by ring
      rw [hre, zmod2_add_self, add_zero]
    · simp_all
  have hrp : r ≤ p := by
    refine ⟨by assumption, ?_⟩
    have h2 :=
      specialSub_mono (by assumption) hinr
    have h3 : r.rep⁻¹ * p.rep = (r.rep⁻¹ * (p.rep * u)) * u⁻¹ := by group
    rw [h3]
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hu)
  refine ⟨r, ⟨hrp, hrc⟩, ?_⟩
  rintro r' ⟨hr'p, hr'c⟩
  have hspx : r.spx = r'.spx := by simp_all [qProjCube_eq_iff]
  -- the two lifts differ by an element of `W_T` with parity supported in the face
  set k : CayGroup A := r.rep⁻¹ * r'.rep with hkdef
  have hkT : k ∈ specialSub A p.spx := by
    have h1 := hrp.2
    have h2 : p.rep⁻¹ * r'.rep ∈ specialSub A p.spx := by
      have := Subgroup.inv_mem _ hr'p.2
      assumption
    have h3 : k = (r.rep⁻¹ * p.rep) * (p.rep⁻¹ * r'.rep) := by rw [hkdef]; group
    rw [h3]
    apply Subgroup.mul_mem <;> assumption
  have hkout : ∀ v, v ∉ c.spx → phi A k v = 0 := by
    simp_all [qProjCube_eq_iff, phi_mul, phi_inv, zmod2_add_self]
  obtain ⟨k0, hk0U, hk0⟩ := exists_mem_specialSub_phi_eq A c.spx _
    (fun v hv => hkout v hv)
  have hkk0 :=
    phi_injOn_specialSub A (commuting_of_isSimplex p.isSimplex) hkT (specialSub_mono (by assumption) hk0U) hk0.symm
  have hinr' : InChamber r'.rep r := by
    show r.rep⁻¹ * r'.rep ∈ specialSub A r.spx
    simp_all
  exact (eq_of_inChamber_spx_eq hinr' (inChamber_rep r') hspx).symm

/-! ### The projection is a covering of posets -/

variable (z : Zpos A X (IsGamma A) att) (q : Qpos A X att)

omit [Fintype V] in
/-- **Unique lifting of the cells above a cell of `Z`.** -/
theorem zProj_up
    (h : zProj z ≤ q) : ∃! b : Zpos A X _ att, z ≤ b ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨r, ⟨hpr, hrc⟩, huniq⟩ := existsUnique_up_old h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨hpr, ?_⟩, ?_⟩
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have := huniq r'.1 ⟨hle, (congrArg Subtype.val (Sum.inl.inj hproj))⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · solve_by_elim
      | inr y => exact h.elim
  | inr wx =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨hsgn, hne, hx⟩ := h
          obtain ⟨r, ⟨hwr, hrc⟩, huniq⟩ :=
            existsUnique_up_inChamber wx.1.2 hsgn
          have hspx := (qProjCube_eq_iff.1 hrc).1
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨⟨hwr, ?_⟩, ?_⟩, ?_⟩
          · simp_all
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have := huniq r'.1 ⟨hle.1, (congrArg Subtype.val (Sum.inl.inj hproj))⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · refine congrArg Sum.inr (Prod.ext ?_ (Sum.inr.inj hproj))
            apply hle.1.symm

omit [Fintype V] in
/-- **Unique lifting of the cells below a cell of `Z`.** -/
theorem zProj_down
    (h : q ≤ zProj z) : ∃! b : Zpos A X _ att, b ≤ z ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨c, hc⟩ := cc
          obtain ⟨r, ⟨hrp, hrc⟩, huniq⟩ := existsUnique_down_old h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq hc hrc), ⟨hrp, ?_⟩, ?_⟩
          · exact congrArg Sum.inl (Subtype.ext hrc)
          · rintro (r' | ⟨v, y⟩) ⟨hle, hproj⟩
            · have := huniq r'.1 ⟨hle, (congrArg Subtype.val (Sum.inl.inj hproj))⟩
              exact congrArg Sum.inl (Subtype.ext this)
            · exact absurd hproj (fun hcon => by cases hcon)
      | inr y =>
          obtain ⟨hsgn, hne, hy⟩ := h
          have hzero : ∀ v, v ∉ p.1.spx → phi A p.1.rep v = 0 := by
            intro v hv
            rw [← qProjCube_sgn_of_not_mem hv]
            simp_all
          obtain ⟨g, ⟨hg, hgp⟩, huniq⟩ := existsUnique_isGamma_inChamber hzero
          refine ⟨zNew ⟨g, hg⟩ y, ⟨⟨hgp, hne, hy⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · exact absurd hproj (fun hcon => by cases hcon)
          · refine congrArg Sum.inr (Prod.ext (Subtype.ext ?_) (Sum.inr.inj hproj))
            exact huniq v.1 ⟨v.2, hle.1⟩
  | inr wx =>
      cases q with
      | inl cc => exact h.elim
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (r' | ⟨v, y'⟩) ⟨hle, hproj⟩
          · solve_by_elim
          · refine congrArg Sum.inr (Prod.ext ?_ (Sum.inr.inj hproj))
            exact hle.1

/-- **The projection `Z → Q` is a covering of posets.** -/
theorem zProj_isPosetCover :
    Comb.IsPosetCover (zProj (att := att)) where
  mono := zProj_monotone
  surj := zProj_surjective
  up := zProj_up
  down := zProj_down

/-- **The projection induces a combinatorial covering of the order complexes.** -/
theorem isCovering_orderCxMap_zProj :
    Comb.IsCovering (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone) :=
  Comb.isCovering_orderCxMap zProj_isPosetCover

/-! ### The copy of the base is injective in `π₁(Q)` -/

variable (w : {w : CayGroup A // IsGamma A w})

omit [Fintype V] in
theorem mapPath_zProj_zNew
    (l : List _) :
    Comb.mapPath (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
        (Comb.mapPath (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
          (zNew_monotone w)) l)
      = Comb.mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [Comb.mapPath, List.map_cons] at ih ⊢
      congr 1

omit [Fintype V] in
/-- The inclusion of the base in the quotient factors as the inclusion of a copy of the base in
`Z` followed by the covering projection. -/
theorem pi1Map_qNew_eq_comp (x : X) :
    Comb.pi1Map (orderCxMap _ qNew_monotone) x
      = (Comb.pi1Map (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
          (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap _
          (zNew_monotone w)) x) := by
  ext g
  induction g using Quotient.inductionOn with
  | h l =>
      refine Quotient.sound ?_
      simp [mapPath_zProj_zNew]

/-- **The inclusion of the base poset in the quotient is injective on fundamental groups.**
The covering datum comes from the construction: `Z → Q` is the covering
`isCovering_orderCxMap_zProj`, and a copy of the base is injective in `π₁(Z)` by
`pi1Map_zNew_injective_uncond`. -/
theorem pi1Map_qNew_injective (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x) := by
  rw [pi1Map_qNew_eq_comp ⟨1, isGamma_one⟩ x]
  solve_by_elim [pi1Map_zNew_covering_injective, zProj_monotone, isCovering_orderCxMap_zProj, isGamma_one]

end Davis
end FiniteChains
