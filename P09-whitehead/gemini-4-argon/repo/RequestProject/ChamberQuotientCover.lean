module

public import RequestProject.ChamberQuotient
public import RequestProject.OrderPosetCovering

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]
  {att : NeSpx A →o X}

theorem existsUnique_isGamma_inChamber {p : Sph A}
    (h : ∀ v, v ∉ p.spx → phi A p.rep v = 0) :
    ∃! g : CayGroup A, IsGamma A g ∧ InChamber g p := by
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then phi A p.rep v else 0) (fun v hv => by simp [hv])
  have hpu : phi A (p.rep * u) = 0 := funext fun v => by
    simp only [phi_mul, Pi.add_apply, Pi.zero_apply, hphiu]
    by_cases hv : v ∈ p.spx
    · rw [if_pos hv, zmod2_add_self]
    · rw [if_neg hv, add_zero, h v hv]
  refine ⟨p.rep * u, ⟨hpu, by show p.rep⁻¹ * (p.rep * u) ∈ _; rwa [inv_mul_cancel_left]⟩, ?_⟩
  rintro g ⟨hg, hgp⟩
  have hmem : (p.rep * u)⁻¹ * g ∈ specialSub A (p.spx : Set V) := by
    rw [show (p.rep * u)⁻¹ * g = u⁻¹ * (p.rep⁻¹ * g) by group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hgp
  have hzero : phi A ((p.rep * u)⁻¹ * g) = 0 := funext fun v => by
    simp only [phi_mul, phi_inv, Pi.add_apply, Pi.zero_apply, hpu, show phi A g = 0 from hg, add_zero]
  exact (inv_mul_eq_one.mp (eq_one_of_mem_specialSub_of_phi_eq_zero A
    (commuting_of_isSimplex p.isSimplex) hmem hzero)).symm

theorem existsUnique_up_old {p : Sph A} {c : QCube A} (hle : qProjCube p ≤ c) :
    ∃! r : Sph A, p ≤ r ∧ qProjCube r = c := by
  have hin : InChamber p.rep (chamberPt p.rep c.isSimplex) :=
    chamberPt_inChamber p.rep c.isSimplex
  refine ⟨chamberPt p.rep c.isSimplex, ⟨⟨hle.1, by
    simpa [mul_inv_rev] using Subgroup.inv_mem _ hin⟩,
    qProjCube_eq_iff.mpr ⟨rfl, fun v hv => ?_⟩⟩, fun r ⟨hpr, hrc⟩ => ?_⟩
  · rw [phi_rep_eq_of_inChamber hin (by simpa using hv),
      ← qProjCube_sgn_of_not_mem fun hc => hv (hle.1 hc)]
    exact hle.2 v hv
  · exact eq_of_inChamber_spx_eq (inChamber_rep_of_le hpr) hin (qProjCube_eq_iff.1 hrc).1

theorem existsUnique_up_inChamber {w : CayGroup A} (hw : IsGamma A w) {c : QCube A}
    (hsgn : c.sgn = 0) :
    ∃! r : Sph A, InChamber w r ∧ qProjCube r = c := by
  have hin := chamberPt_inChamber w c.isSimplex
  refine ⟨chamberPt w c.isSimplex, ⟨hin, qProjCube_eq_iff.mpr ⟨rfl, fun v hv => ?_⟩⟩,
    fun r ⟨hwr, hrc⟩ => eq_of_inChamber_spx_eq hwr hin (qProjCube_eq_iff.1 hrc).1⟩
  rw [phi_rep_eq_of_inChamber hin (by simpa using hv),
    show phi A w v = 0 from congrFun hw v]
  exact (congrFun hsgn v).symm

theorem existsUnique_down_old {p : Sph A} {c : QCube A} (hle : c ≤ qProjCube p) :
    ∃! r : Sph A, r ≤ p ∧ qProjCube r = c := by
  classical
  obtain ⟨u, hu, hphiu⟩ := exists_mem_specialSub_phi_eq A p.spx
    (fun v => if v ∈ p.spx then c.sgn v + phi A p.rep v else 0) (fun v hv => by simp [hv])
  set r : Sph A := chamberPt (p.rep * u) c.isSimplex with hrdef
  have hinr : InChamber (p.rep * u) r := chamberPt_inChamber _ _
  have hrspx : r.spx = c.spx := rfl
  have hrc : qProjCube r = c := by
    refine qProjCube_eq_iff.mpr ⟨hrspx, fun v hv => ?_⟩
    rw [phi_rep_eq_of_inChamber hinr (hrspx ▸ hv)]
    simp only [phi_mul, Pi.add_apply, hphiu]
    by_cases hvT : v ∈ p.spx
    · rw [if_pos hvT, show phi A p.rep v + (c.sgn v + phi A p.rep v) =
        c.sgn v + (phi A p.rep v + phi A p.rep v) by ring, zmod2_add_self, add_zero]
    · rw [if_neg hvT, add_zero, hle.2 v hvT, qProjCube_sgn_of_not_mem hvT]
  have hrp : r ≤ p := ⟨hrspx ▸ hle.1, by
    have h2 : r.rep⁻¹ * (p.rep * u) ∈ specialSub A (p.spx : Set V) :=
      specialSub_mono (by exact_mod_cast (hrspx ▸ hle.1 : r.spx ⊆ p.spx)) hinr
    rw [show r.rep⁻¹ * p.rep = (r.rep⁻¹ * (p.rep * u)) * u⁻¹ by group]
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hu)⟩
  refine ⟨r, ⟨hrp, hrc⟩, ?_⟩
  rintro r' ⟨hr'p, hr'c⟩
  set k : CayGroup A := r.rep⁻¹ * r'.rep with hkdef
  have hkT : k ∈ specialSub A (p.spx : Set V) := by
    rw [show k = (r.rep⁻¹ * p.rep) * (p.rep⁻¹ * r'.rep) by rw [hkdef]; group]
    exact Subgroup.mul_mem _ hrp.2 (by simpa [mul_inv_rev] using Subgroup.inv_mem _ hr'p.2)
  obtain ⟨k0, hk0U, hk0⟩ := exists_mem_specialSub_phi_eq A c.spx (phi A k) fun v hv => by
    rw [hkdef]
    simp only [phi_mul, phi_inv, Pi.add_apply,
      (qProjCube_eq_iff.1 hrc).2 v hv, (qProjCube_eq_iff.1 hr'c).2 v hv, zmod2_add_self]
  have hkk0 : k = k0 := phi_injOn_specialSub A (commuting_of_isSimplex p.isSimplex)
    hkT (specialSub_mono (by exact_mod_cast hle.1) hk0U) hk0.symm
  have hinr' : InChamber r'.rep r := by
    show r.rep⁻¹ * r'.rep ∈ specialSub A (r.spx : Set V)
    rw [← hkdef, hkk0, hrspx]; exact hk0U
  exact (eq_of_inChamber_spx_eq (x := r'.rep) hinr'
    (inChamber_rep r') (hrspx.trans (qProjCube_eq_iff.1 hr'c).1.symm)).symm

theorem zProj_up (z : Zpos A X (IsGamma A) att) (q : Qpos A X att)
    (h : zProj z ≤ q) : ∃! b : Zpos A X (IsGamma A) att, z ≤ b ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨r, ⟨hpr, hrc⟩, huniq⟩ := existsUnique_up_old (p := p.1) (c := cc.1) h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq cc.2 hrc),
            ⟨hpr, congrArg Sum.inl (Subtype.ext hrc)⟩, ?_⟩
          rintro (r' | _) ⟨hle, hproj⟩
          · exact congrArg Sum.inl (Subtype.ext
              (huniq r'.1 ⟨hle, congrArg Subtype.val (Sum.inl.inj hproj)⟩))
          · nomatch hproj
      | inr _ => exact h.elim
  | inr wx =>
      cases q with
      | inl cc =>
          obtain ⟨hsgn, hne, hx⟩ := h
          obtain ⟨r, ⟨hwr, hrc⟩, huniq⟩ :=
            existsUnique_up_inChamber (w := wx.1.1) wx.1.2 (c := cc.1) hsgn
          have hspx : r.spx = cc.1.spx := (qProjCube_eq_iff.1 hrc).1
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq cc.2 hrc),
            ⟨⟨hwr, hspx ▸ hne, hx.trans (le_of_eq (congrArg att (Subtype.ext hspx.symm)))⟩,
              congrArg Sum.inl (Subtype.ext hrc)⟩, ?_⟩
          rintro (r' | _) ⟨hle, hproj⟩
          · exact congrArg Sum.inl (Subtype.ext
              (huniq r'.1 ⟨hle.1, congrArg Subtype.val (Sum.inl.inj hproj)⟩))
          · nomatch hproj
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (_ | ⟨_, y'⟩) ⟨hle, hproj⟩
          · nomatch hproj
          · exact congrArg Sum.inr (Prod.ext hle.1.symm (Sum.inr.inj hproj))

theorem zProj_down (z : Zpos A X (IsGamma A) att) (q : Qpos A X att)
    (h : q ≤ zProj z) : ∃! b : Zpos A X (IsGamma A) att, b ≤ z ∧ zProj b = q := by
  cases z with
  | inl p =>
      cases q with
      | inl cc =>
          obtain ⟨r, ⟨hrp, hrc⟩, huniq⟩ := existsUnique_down_old (p := p.1) (c := cc.1) h
          refine ⟨zOld r (not_isMarkedApex_of_qProjCube_eq cc.2 hrc),
            ⟨hrp, congrArg Sum.inl (Subtype.ext hrc)⟩, ?_⟩
          rintro (r' | _) ⟨hle, hproj⟩
          · exact congrArg Sum.inl (Subtype.ext
              (huniq r'.1 ⟨hle, congrArg Subtype.val (Sum.inl.inj hproj)⟩))
          · nomatch hproj
      | inr y =>
          obtain ⟨hsgn, hne, hy⟩ := h
          obtain ⟨g, ⟨hg, hgp⟩, huniq⟩ := existsUnique_isGamma_inChamber (p := p.1) fun v hv => by
            rw [← qProjCube_sgn_of_not_mem hv]; exact congrFun hsgn v
          refine ⟨zNew ⟨g, hg⟩ y, ⟨⟨hgp, hne, hy⟩, rfl⟩, ?_⟩
          rintro (_ | ⟨v, y'⟩) ⟨hle, hproj⟩
          · nomatch hproj
          · exact congrArg Sum.inr (Prod.ext (Subtype.ext (huniq v.1 ⟨v.2, hle.1⟩))
              (Sum.inr.inj hproj))
  | inr wx =>
      cases q with
      | inl _ => exact h.elim
      | inr y =>
          refine ⟨zNew wx.1 y, ⟨⟨rfl, h⟩, rfl⟩, ?_⟩
          rintro (_ | ⟨_, y'⟩) ⟨hle, hproj⟩
          · nomatch hproj
          · exact congrArg Sum.inr (Prod.ext hle.1 (Sum.inr.inj hproj))

variable [Fintype V]

theorem isCovering_orderCxMap_zProj :
    Comb.IsCovering (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone) :=
  Comb.isCovering_orderCxMap ⟨zProj_monotone, zProj_surjective, zProj_up, zProj_down⟩

theorem pi1Map_qNew_injective (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x) := by
  let w : {w : CayGroup A // IsGamma A w} := ⟨1, isGamma_one⟩
  have hcomp : Comb.pi1Map (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone) x =
      (Comb.pi1Map (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
          (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w x)).comp
        (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := IsGamma A) (att := att) w)
          (zNew_monotone w)) x) := by
    ext g
    induction g using Quotient.inductionOn with | h l =>
    apply Quotient.sound
    show Comb.Htpy (orderCx (Qpos A X att)) (qNew (att := att) x) (qNew (att := att) x)
      (Comb.mapPath (orderCxMap (qNew (att := att)) qNew_monotone) l.1)
      (Comb.mapPath (orderCxMap (zProj (att := att)) zProj_monotone)
        (Comb.mapPath (orderCxMap (zNew (att := att) w) (zNew_monotone w)) l.1))
    have hmap : ∀ m : List ((orderCx X).E × Bool),
        Comb.mapPath (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
          (Comb.mapPath (orderCxMap (zNew (att := att) w) (zNew_monotone w)) m) =
          Comb.mapPath (orderCxMap (qNew (att := att)) qNew_monotone) m := by
      intro m; induction m with | nil => rfl | cons _ _ ih => exact congrArg (List.cons _) ih
    rw [hmap l.1]
  rw [hcomp]
  exact pi1Map_zNew_covering_injective
    (orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone)
    isCovering_orderCxMap_zProj w x
