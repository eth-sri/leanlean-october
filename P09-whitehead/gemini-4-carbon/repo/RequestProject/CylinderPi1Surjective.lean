module

public import RequestProject.GenusCollapseIteration
public import RequestProject.CombPi1
public import RequestProject.GenusLoops
public import Mathlib.GroupTheory.PushoutI
public import RequestProject.PresPosetReading
public import Mathlib

@[expose] public section
noncomputable section
section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_free_face_loop_representative
    (C : GenusTruncatedCell q → Prop) (S : Finset (Cube (GenusVertex q)))
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hf : truncatedCellDimension f = 2) (ht : t.1.spx.card = 3)
    (htC : C (Sum.inl t))
    (hactive : ∀ d : QOld (cmpRel (GenusVertex q)), C (Sum.inl d) →
      d.1.spx.card = 3 → qCubeToCoordinate d.1 ∈ S)
    (hfree : Collapse.IsFree (spineInc (ASC.orderComplex (GenusVertex q))) S
      (truncatedFaceIndex f) (qCubeToCoordinate t.1))
    (a : GenusTruncatedCell q) (p : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : C a ∧ a ≠ f)
    (hp : IsPath (orderCx (GenusTruncatedCell q)).src (orderCx (GenusTruncatedCell q)).tgt p a a)
    (hC : PathIn C p) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (fun x => C x ∧ x ≠ f) l ∧ Htpy (orderCx (GenusTruncatedCell q)) a a p l := by
  have hinc : qCubeToCoordinate t.1 ∈
      spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) ∩ S := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have hft := truncatedCell_le_of_inc f t hinc
  have hne : (Sum.inl t) ≠ f := by
    intro he
    have hh := congrArg truncatedCellDimension he
    change t.1.spx.card = truncatedCellDimension f at hh
    omega
  apply loop_representative_delete_free_face htC hft hne ?_ ha hp hC
  intro x hx hfx hxf
  have hdim : truncatedCellDimension x = 3 := by
    have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hfx hxf.symm)
    have hmax := genusTruncatedCell_dimension_le_three q x
    omega
  cases x with
  | inr σ =>
    have hh := genus_cutCell_dimension_le_two q σ
    omega
  | inl d =>
    have hd  := hdim
    have hL : d.1.spx ∈ (ASC.orderComplex (GenusVertex q)).faces := by
      intro a ha b hb _
      exact (isSimplex_cmpRel_iff.mp d.1.isSimplex) a ha b hb
    have hi := truncatedCell_inc_of_le f d hfx hf hd hL
    have hm := Finset.mem_inter.mpr ⟨hi, hactive d hx hd⟩
    rw [hfree] at hm
    have he  :=
      Finset.mem_singleton.mp hm
    have hc  := qCubeCoordinateEquiv.injective (Subtype.ext he)
    exact congrArg Sum.inl (Subtype.ext hc)

theorem genus_ordinary_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hf : f.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) hsplit
  have hfree := hc.2.1
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inl (qCubeToCoordinate f.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inl (qCubeToCoordinate f.1)) ∩
          Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) hsplit
        (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have ha' := (genusCollapseStage_ordinary_step_iff q left f t a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := genus_free_face_loop_representative q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inl f) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree a loop ha'.1 hpath hC
  have hJ x :
      x ≠ Sum.inl f ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inl f) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · simp_all
  have hconn := connectedIn_congr hJ (ordinaryTruncatedBoundary_connectedIn hordinary hi)
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (C := fun x => genusCollapseStage q left x ∧ x ≠ Sum.inl f)
    (t := Sum.inl t) (fun x _ htx => genus_top_cell_maximal q t ht x htx)
    hconn l ha' ha' hl hlf
  exact ⟨r, hr, pathIn_mono
    (fun x hx => (genusCollapseStage_ordinary_step_iff q left f t x).mpr hx) hrB,
    hhl.trans hhr⟩

theorem genus_cut_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q)))
    (hne : t.1.spx.Nonempty) (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) hsplit
  have hfree := hc.2.1
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr t.1.spx) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inr t.1.spx) ∩
          Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) hsplit
        (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have hf : truncatedCellDimension (Sum.inr (fullCutCell t hne)) = 2 := by
    change t.1.spx.card - 1 = 2
    omega
  have ha' := (genusCollapseStage_cut_step_iff q left t hne a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := genus_free_face_loop_representative q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inr (fullCutCell t hne)) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree a loop ha'.1 hpath hC
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne)) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · simp_all
  have hconn := connectedIn_congr hJ (positiveCutPuncturedBoundary_connectedIn t hne hpositive ht)
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (C := fun x => genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne))
    (t := Sum.inl t) (fun x _ htx => genus_top_cell_maximal q t ht x htx)
    hconn l ha' ha' hl hlf
  exact ⟨r, hr, pathIn_mono
    (fun x hx => (genusCollapseStage_cut_step_iff q left t hne x).mpr hx) hrB,
    hhl.trans hhr⟩


theorem genus_recorded_cut_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++ ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  have hp : (qCubeToCoordinate t.1, Sum.inr σ.1) ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ht  := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inr σ.1), hp, rfl⟩)
  have hc := genusCollapseStage_suffix_certificate q left
    ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr σ.1) := by
    have hm : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
        (Sum.inr σ.1) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hc.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    simp only [spineInc] at hi
    split at hi
    · simp_all
    · simp at hi
  have hs : t.1.spx = σ.1 := by
    have hh := congrArg freeSet he
    simpa using hh
  have hpositive : t.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity t.1 v
    rw [he] at hh
    by_cases hv : v ∈ σ.1
    · simpa [posCube, hv] using hh.symm
    · simpa [posCube, hv] using hh.symm
  have hne := hs.symm ▸ σ.2.1
  have hstep := genus_cut_pair_loop_representative q left right t hne ht hpositive
    (by simpa only [hs] using hsplit) a loop
    (by simpa only [hs] using ha) hpath hC
  simpa only [hs] using hstep


/-- Construct a loop in the terminal stage of any actual suffix of the chosen collapse. -/
theorem genus_collapse_suffix_loop_representative
    (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right)
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ right) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ right)) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  induction right generalizing left loop with
  | nil => exact ⟨loop, hpath, by simpa using hC, Htpy.refl _⟩
  | cons p right ih =>
    have haTail : genusCollapseStage q ((left ++ [p]) ++ right) a := by
      simpa using ha
    have haFirst := genusCollapseStage_append_subset q (left ++ [p]) right a haTail
    obtain ⟨l, hl, hlC, hhl⟩ := (show ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [p])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l by
      have hp : p ∈ genusChainCollapse q := by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      obtain ⟨t, f, ht, hf⟩ := genus_pair_cells q p hp
      have he : p = (qCubeToCoordinate t.1, truncatedFaceIndex f) := Prod.ext ht.symm hf.symm
      rw [he] at hsplit haFirst ⊢
      cases f with
      | inl f => exact (by
        have hp : (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) ∈ genusChainCollapse q := by
          rw [hsplit]
          exact List.mem_append.mpr (Or.inr List.mem_cons_self)
        have hf  := genus_removedFace_dimension q (Sum.inl f)
          (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)), hp, rfl⟩)
        have ht  := (genus_oldCell_removed_iff_dimension_three q t).mp
          (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)), hp, rfl⟩)
        have hordinary : t.1.sgn ≠ 0 := by
          intro hs
          apply genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1)
            (qCubeToCoordinate f.1) hp
          simpa using qCubeToCoordinate_sgn_zero t.1 hs
        exact genus_ordinary_pair_loop_representative q left right f t hf ht hordinary hsplit a loop haFirst hpath hC)
      | inr σ => exact genus_recorded_cut_pair_loop_representative q left right σ t hsplit a loop haFirst hpath hC)
    obtain ⟨r, hr, hrC, hhr⟩ := ih (left ++ [p])
      (by simpa using hsplit)
      l haTail hl hlC
    exact ⟨r, hr, by simpa using hrC,
      hhl.trans hhr⟩

/-- Every loop of the truncated block based in its surviving spine is represented in that spine. -/
theorem genusSpine_loop_representative (a : GenusTruncatedCell q)
    (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : a ∈ genusSpineCellSet q)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (fun c => c ∈ genusSpineCellSet q) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  obtain ⟨l, hl, hC, hh⟩ := genus_collapse_suffix_loop_representative q
    (genusChainCollapse q) [] (by simp) a loop
    ((genusCollapseStage_final_iff q a).mpr ha) hpath
    (fun e _ => ⟨genusCollapseStage_nil q e.1.1.1, genusCollapseStage_nil q e.1.1.2⟩)
  exact ⟨l, hl, pathIn_mono (fun c hc => (genusCollapseStage_final_iff q c).mp hc) hC, hh⟩

theorem genusSpineToTruncated_pi1_factor_weak
    (z : Pi1 (genusSpineCx q) (spineBase q)) :
    pi1Map (genusSpineToTruncated q) (spineBase q) z =
      pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
        (spineBase q) (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q) z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    apply congrArg Pi1.mk
    apply Subtype.ext
    simp [genusSpineToTruncated, mapPath, Hom.comp, List.map_map, Function.comp_def]

theorem genusSpineToTruncated_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  rintro ⟨p⟩
  obtain ⟨r, hr, hrB, hh⟩ := genusSpine_loop_representative q
    (spineBase q).1 p.1 (spineBase q).2 p.2
  let lifted : Loop (orderCx (GenusSpineCell q)) (spineBase q) :=
    ⟨liftPathIn r hrB, isPath_liftPathIn r hrB (spineBase q).2 (spineBase q).2 hr⟩
  refine ⟨(strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q)).symm (Pi1.mk lifted), ?_⟩
  rw [genusSpineToTruncated_pi1_factor_weak, MulEquiv.apply_symm_apply]
  apply Quotient.sound
  change Htpy (orderCx (GenusTruncatedCell q)) (spineBase q).1 (spineBase q).1
    (mapPath (subposetHom (fun c => c ∈ genusSpineCellSet q)) (liftPathIn r hrB)) p.1
  rw [mapPath_liftPathIn]
  exact hh.symm


def genusSpineToOldPi1Equiv :
    Pi1 (genusSpineCx q) (spineBase q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) ((genusSpineToOld q).onV (spineBase q)) :=
  MulEquiv.ofBijective (pi1Map (genusSpineToOld q) (spineBase q))
    ⟨genusSpineToOld_pi1_injective q, (by
      intro z
      obtain ⟨v, hv⟩ := truncatedRetraction_pi1_surjective_at
        ((genusSpineToTruncated q).onV (spineBase q)) z
      obtain ⟨w, hw⟩ := genusSpineToTruncated_pi1_surjective q v
      exact ⟨w, by rw [genusSpine_pi1_factor, hw]; exact hv⟩)⟩

end FiniteChains.Davis.Genus
end

namespace FiniteChains

variable {α : Type*} [DecidableEq α]

def foxGradient (w : FreeGroup α) : α →₀ FreeGroupRing α :=
  Finsupp.ofSupportFinite (fun i => fox i w) (fox_generator_support_finite w)

@[simp] theorem foxGradient_apply (w : FreeGroup α) (i : α) :
    foxGradient w i = fox i w := rfl

@[simp] theorem foxGradient_one : foxGradient (1 : FreeGroup α) = 0 := by
  ext i
  simp

@[simp] theorem foxGradient_of (i : α) :
    foxGradient (FreeGroup.of i) = Finsupp.single i 1 := by
  ext j
  simp [fox_of, Finsupp.single_apply, eq_comm]


theorem foxGradient_inv (a : FreeGroup α) :
    foxGradient a⁻¹ = -(grp a⁻¹ • foxGradient a) := by
  ext i
  simp [fox_inv]

def freeFirstBoundary :
    (α →₀ FreeGroupRing α) →ₗ[FreeGroupRing α] FreeGroupRing α :=
  Finsupp.linearCombination _ (fun i => grp (FreeGroup.of i) - 1)

/-- The fundamental Fox identity without a finite-generator hypothesis. -/
theorem fox_fundamental_finsupp (w : FreeGroup α) :
    freeFirstBoundary (foxGradient w) = grp w - 1 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp [freeFirstBoundary]
  | inv_of k hk =>
      rw [foxGradient_inv, map_neg, map_smul, hk]
      change -(grp (FreeGroup.of k)⁻¹ * (grp (FreeGroup.of k) - 1)) = _
      rw [mul_sub, grp_inv_mul_grp, mul_one]
      noncomm_ring
  | mul a b ha hb =>
      rw [(show foxGradient (a * b) = foxGradient a + grp a • foxGradient b by
        ext i
        simp [fox_mul]), map_add, map_smul, ha, hb, grp_mul]
      change (grp a - 1) + grp a * (grp b - 1) = _
      noncomm_ring

variable (N : Subgroup (FreeGroup α)) [N.Normal]

def coverFoxGradient (w : FreeGroup α) : α →₀ CoverRing N :=
  (foxGradient w).mapRange (proj N) (map_zero _)

def coverFirstBoundary :
    (α →₀ CoverRing N) →ₗ[CoverRing N] CoverRing N :=
  Finsupp.linearCombination _ (fun i => qgrp N (FreeGroup.of i) - 1)

omit [DecidableEq α] in
/-- Projection of the group ring commutes with the finitely supported first boundary. -/
theorem coverFirstBoundary_mapRange (c : α →₀ FreeGroupRing α) :
    coverFirstBoundary N (c.mapRange (proj N) (map_zero _)) =
      proj N (freeFirstBoundary c) := by
  simp only [coverFirstBoundary, freeFirstBoundary, Finsupp.linearCombination_apply,
    smul_eq_mul]
  rw [Finsupp.sum_mapRange_index (fun i => zero_mul _), map_finsuppSum]
  apply Finsupp.sum_congr
  intro i ci
  simp only [map_mul, map_sub, map_one, proj_grp]


theorem coverFoxGradient_isCycle {w : FreeGroup α} (hw : w ∈ N) :
    coverFirstBoundary N (coverFoxGradient N w) = 0 := by
  rw [(show coverFirstBoundary N (coverFoxGradient N w) = qgrp N w - 1 by
    rw [coverFoxGradient, coverFirstBoundary_mapRange, fox_fundamental_finsupp,
      map_sub, proj_grp, map_one]), qgrp_eq_one_of_mem N hw, sub_self]

def coverSecondBoundary {J : Type*} (ρ : J → FreeGroup α) :
    (J →₀ CoverRing N) →ₗ[CoverRing N] (α →₀ CoverRing N) :=
  Finsupp.linearCombination _ (fun j => coverFoxGradient N (ρ j))

/-- The finitely supported cover boundaries form a chain complex, with no finite-cell
assumptions on either the generators or relators. -/
theorem coverFirstBoundary_coverSecondBoundary {J : Type*} (ρ : J → FreeGroup α)
    (hρ : ∀ j, ρ j ∈ N) (c : J →₀ CoverRing N) :
    coverFirstBoundary N (coverSecondBoundary N ρ c) = 0 := by simp_all [coverSecondBoundary, Finsupp.linearCombination_apply, map_finsuppSum, map_smul, coverFoxGradient_isCycle, smul_zero, Finset.sum_eq_zero]



end FiniteChains

namespace FiniteChains

variable {α : Type*} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

@[simp] theorem coe_coverFoxGradient (w : FreeGroup α) :
    (coverFoxGradient N w : α → CoverRing N) = foxVec N w := rfl

theorem coverFoxGradient_mul {v : FreeGroup α} (hv : v ∈ N) (w : FreeGroup α) :
    coverFoxGradient N (v * w) = coverFoxGradient N v + coverFoxGradient N w := by
  apply Finsupp.ext
  intro i
  exact congrFun (foxVec_mul hv w) i

theorem coverFoxGradient_inv {v : FreeGroup α} (hv : v ∈ N) :
    coverFoxGradient N v⁻¹ = -coverFoxGradient N v := by
  apply Finsupp.ext
  intro i
  exact congrFun (foxVec_inv hv) i

theorem coverFoxGradient_zpow {v : FreeGroup α} (hv : v ∈ N) (n : ℤ) :
    coverFoxGradient N (v ^ n) = n • coverFoxGradient N v := by
  apply Finsupp.ext
  intro i
  exact congrFun (foxVec_zpow hv n) i

theorem coverFoxGradient_conj {r : FreeGroup α} (hr : r ∈ N) (f : FreeGroup α) :
    coverFoxGradient N (f * r * f⁻¹) = qgrp N f • coverFoxGradient N r := by
  apply Finsupp.ext
  intro i
  change foxVec N (f * r * f⁻¹) i = qgrp N f * foxVec N r i
  simpa only [proj_grp, Pi.smul_apply, smul_eq_mul] using congrFun (foxVec_conj hr f) i

@[simp] theorem coverFoxGradient_one : coverFoxGradient N (1 : FreeGroup α) = 0 := by
  ext i
  simp [coverFoxGradient]

theorem coverFoxGradient_eq_zero_iff {w : FreeGroup α} (hw : w ∈ N) :
    coverFoxGradient N w = 0 ↔ w ∈ ⁅N, N⁆ := by
  rw [← foxVec_eq_zero_iff N hw]
  exact ⟨fun h => congrArg (fun c : α →₀ CoverRing N => (c : α → CoverRing N)) h,
    fun h => Finsupp.ext (congrFun h)⟩

/-- Every finite one-cycle of a cover is the Fox vector of a word in its defining subgroup.
There is no assumption that the set of generators is finite. -/
theorem exists_mem_of_coverFirstBoundary_eq_zero (c : α →₀ CoverRing N)
    (hc : coverFirstBoundary N c = 0) :
    ∃ r ∈ N, c = coverFoxGradient N r := by
  let a  := fun i => liftQ N (c i)
  let b  := ∑ i ∈ c.support, a i * (grp (FreeGroup.of i) - 1)
  have hproja : ∀ i, proj N (a i) = c i := fun i => proj_liftQ N (c i)
  have hprojb : proj N b = 0 := by
    rw [map_sum]
    have he : ∑ i ∈ c.support, proj N (a i * (grp (FreeGroup.of i) - 1)) =
        coverFirstBoundary N c := by
      change _ = ∑ i ∈ c.support, c i * (qgrp N (FreeGroup.of i) - 1)
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, map_sub, proj_grp, map_one, hproja]
    rw [he, hc]
  have hfoxb : foxProj N b = c := by
    funext j
    have hterm : ∀ i, foxLin j (a i * (grp (FreeGroup.of i) - 1)) =
        a i * (if j = i then 1 else 0) := by
      intro i
      rw [foxLin_mul, map_sub, aug_grp, map_one, sub_self,
        zero_smul, zero_add, map_sub]
      have h1 : foxLin j 1 = 0 := by
        rw [← grp_one, foxLin_grp, fox_one]
      rw [h1, foxLin_grp, fox_of, sub_zero]
    change proj N (foxLin j b) = c j
    dsimp only [b]
    rw [map_sum]
    change proj N (∑ i ∈ c.support, foxLin j (a i * (grp (FreeGroup.of i) - 1))) = c j
    simp_rw [hterm]
    by_cases hj : j ∈ c.support
    · simp_all
    · simp_all
  obtain ⟨r, hr, he⟩ := foxProj_mem_foxMod N b hprojb
  refine ⟨r, hr, ?_⟩
  apply Finsupp.ext
  intro i
  exact congrFun (hfoxb.symm.trans he) i

variable {J : Type*} (ρ : J → FreeGroup α)

@[simp] theorem coverSecondBoundary_single (j : J) (x : CoverRing N) :
    coverSecondBoundary N ρ (Finsupp.single j x) = x • coverFoxGradient N (ρ j) :=
  Finsupp.linearCombination_single _ x j

/-- The Fox vector of every consequence of the relators is a finite two-boundary. -/
theorem exists_coverSecondBoundary_of_mem_normalClosure (hρ : ∀ j, ρ j ∈ N)
    {w : FreeGroup α} (hw : w ∈ Subgroup.normalClosure (Set.range ρ)) :
    ∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w := by
  let T : Subgroup (FreeGroup α) :=
    { carrier := {v | v ∈ N ∧ ∃ c : J →₀ CoverRing N,
        coverSecondBoundary N ρ c = coverFoxGradient N v}
      one_mem' := ⟨N.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro v w ⟨hv, c, hc⟩ ⟨hw, d, hd⟩
        exact ⟨N.mul_mem hv hw, c + d, by
          rw [map_add, hc, hd, coverFoxGradient_mul N hv]⟩
      inv_mem' := by
        rintro w ⟨hw, c, hc⟩
        exact ⟨N.inv_mem hw, -c, by rw [map_neg, hc, coverFoxGradient_inv N hw]⟩ }
  haveI : T.Normal := by
    constructor
    rintro w ⟨hw, c, hc⟩ f
    refine ⟨Subgroup.Normal.conj_mem ‹N.Normal› w hw f, qgrp N f • c, ?_⟩
    rw [map_smul, hc, coverFoxGradient_conj N hw]
  have hrange : Set.range ρ ⊆ T := by
    rintro _ ⟨j, rfl⟩
    exact ⟨hρ j, Finsupp.single j 1, by rw [coverSecondBoundary_single, one_smul]⟩
  exact ((Subgroup.normalClosure_le_normal hrange) hw).2

/-- Every finite two-boundary is the Fox vector of a consequence of the relators. -/
theorem exists_mem_normalClosure_of_coverSecondBoundary (hρ : ∀ j, ρ j ∈ N)
    (c : J →₀ CoverRing N) :
    ∃ w ∈ Subgroup.normalClosure (Set.range ρ),
      coverSecondBoundary N ρ c = coverFoxGradient N w := by
  have hRle : Subgroup.normalClosure (Set.range ρ) ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact hρ j
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | add c d hc hd =>
      obtain ⟨v, hv, he⟩ := hc
      obtain ⟨w, hw, hf⟩ := hd
      exact ⟨v * w, Subgroup.mul_mem _ hv hw, by
        rw [map_add, he, hf, coverFoxGradient_mul N (hRle hv)]⟩
  | single j x =>
      obtain ⟨w, hw, he⟩ := exists_mem_smul_foxVec hRle
        (Subgroup.subset_normalClosure (Set.mem_range_self j)) x
      refine ⟨w, hw, ?_⟩
      rw [coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      exact congrFun he i

/-- The integral Hurewicz membership calculation for arbitrary presentations. -/
theorem coverFoxGradient_mem_range_iff (hρ : ∀ j, ρ j ∈ N)
    {w : FreeGroup α} (hw : w ∈ N) :
    (∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w) ↔
      w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have hRle : Subgroup.normalClosure (Set.range ρ) ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact hρ j
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r, hr, he⟩ := exists_mem_normalClosure_of_coverSecondBoundary N ρ hρ c
    have hh : coverFoxGradient N (w * r⁻¹) = 0 := by
      rw [coverFoxGradient_mul N hw, coverFoxGradient_inv N (hRle hr), ← hc, ← he]
      exact add_neg_cancel _
    have hm := (coverFoxGradient_eq_zero_iff N (N.mul_mem hw (N.inv_mem (hRle hr)))).mp hh
    have hw' : w = (w * r⁻¹) * r := by group
    rw [hw']
    exact Subgroup.mul_mem _
      ((le_sup_right : ⁅N, N⁆ ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) hm)
      ((le_sup_left : Subgroup.normalClosure (Set.range ρ) ≤
        Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) hr)
  · intro hw'
    obtain ⟨r, hr, t, ht, he⟩ := Subgroup.mem_sup_of_normal_right.mp hw'
    obtain ⟨c, hc⟩ := exists_coverSecondBoundary_of_mem_normalClosure N ρ hρ hr
    refine ⟨c, ?_⟩
    rw [← he, coverFoxGradient_mul N (hRle hr),
      (coverFoxGradient_eq_zero_iff N (Subgroup.commutator_le_left N N ht)).mpr ht, add_zero]
    exact hc

/-- Perfectness of the quotient covering subgroup gives exactness in degree one,
without any finite-presentation restriction. -/
theorem exists_coverSecondBoundary_preimage (hρ : ∀ j, ρ j ∈ N)
    (hperfect : N ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆)
    (c : α →₀ CoverRing N) (hc : coverFirstBoundary N c = 0) :
    ∃ d : J →₀ CoverRing N, coverSecondBoundary N ρ d = c := by
  obtain ⟨w, hw, rfl⟩ := exists_mem_of_coverFirstBoundary_eq_zero N c hc
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mpr (hperfect hw)

end FiniteChains

namespace FiniteChains

variable {α J : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal] (ρ : J → FreeGroup α)





/-- The prime-by-prime lifting condition excludes torsion in the covering subgroup's
abelianization, with arbitrary cell-index sets. -/
theorem fs_mem_relComm_of_pow_mem (hρ : ∀ j, ρ j ∈ N)
    (hmod : ∀ p : ℕ, p.Prime →
      LiftsMod (coverSecondBoundary N ρ).toAddMonoidHom p)
    {w : FreeGroup α} (hw : w ∈ N) {n : ℕ} (hn : n ≠ 0)
    (hpow : w ^ n ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) :
    w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have he : coverFoxGradient N (w ^ n) = n • coverFoxGradient N w := by
    simpa using coverFoxGradient_zpow N hw n
  obtain ⟨c, hc⟩ := (coverFoxGradient_mem_range_iff N ρ hρ (N.pow_mem hw n)).mpr hpow
  have hr : n • coverFoxGradient N w ∈ (coverSecondBoundary N ρ).toAddMonoidHom.range :=
    ⟨c, hc.trans he⟩
  have hmem := mem_range_of_nsmul_mem_range (coverSecondBoundary N ρ).toAddMonoidHom
    hmod n hn (coverFoxGradient N w) hr
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mp hmem

end FiniteChains

namespace FiniteChains

variable {α J : Type*} [DecidableEq α] (ρ : J → FreeGroup α)
  (Nt : Subgroup (FreeGroup α)) [Nt.Normal] (hR : relSub ρ ≤ Nt)

include hR in
theorem fs_bdry2_ringEquivPres
    (c : J →₀ MonoidAlgebra ℤ (PresGroup ρ ⧸ presSub ρ Nt)) (i : α) :
    coverSecondBoundary Nt ρ (c.mapRange (ringEquivPres ρ Nt hR) (map_zero _)) i =
      ringEquivPres ρ Nt hR
        (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) (presSub ρ Nt) c i) := by
  rw [coverSecondBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (fun j =>
      zero_smul (CoverRing Nt) (coverFoxGradient Nt (ρ j)))]
  rw [boundaryMap_apply_coord, map_sum]
  rw [Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  change (∑ j ∈ c.support,
      ringEquivPres ρ Nt hR (c j) * proj Nt (fox i (ρ j))) = _
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  congr 1
  exact (ringEquivPres_quot ρ Nt hR (fox i (ρ j))).symm


include hR in
theorem fs_injective_boundary_of_foxSat
    (h : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSat (foxMatrixPres ρ) v (presSub ρ Nt)) :
    Function.Injective (coverSecondBoundary Nt ρ) := by
  let E := ringEquivPres ρ Nt hR
  let EC := Finsupp.mapRange.addEquiv (ι := J) E.toAddEquiv
  let ED := Finsupp.mapRange.addEquiv (ι := α) E.toAddEquiv
  have hcomm : ∀ c, coverSecondBoundary Nt ρ (EC c) =
      ED (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) (presSub ρ Nt) c) := by
    intro c
    apply Finsupp.ext
    intro i
    exact fs_bdry2_ringEquivPres ρ Nt hR c i
  have hinj := (forall_foxSat_iff_injective (foxMatrixPres ρ)
    (foxMatrixPres_col_finite ρ) (presSub ρ Nt)).mp h
  intro c d he
  obtain ⟨x, rfl⟩ := EC.surjective c
  obtain ⟨y, rfl⟩ := EC.surjective d
  apply congrArg EC
  apply hinj
  apply ED.injective
  rw [← hcomm, ← hcomm]
  exact he


/-- The required torsion-freeness follows from all prime cycle tests for an arbitrary
presentation. Neither the generator set nor the relator set is assumed finite. -/
theorem fs_isMulTorsionFree_of_foxSatMod_pres (N : Subgroup (PresGroup ρ)) [N.Normal]
    (hmod : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v N) :
    IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  let Nt := N.comap (QuotientGroup.mk' (relSub ρ))
  have hR : relSub ρ ≤ Nt := by
    intro r hr
    change (QuotientGroup.mk' (relSub ρ)) r ∈ N
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff r).mpr hr]
    exact N.one_mem
  have hNeq : presSub ρ Nt = N :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N
  have hρ := fun j =>
    hR (Subgroup.subset_normalClosure (Set.mem_range_self j))
  have hm : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v (presSub ρ Nt) := by
    rw [hNeq]
    exact hmod
  have hk := (show ∀ g ∈ presSub ρ Nt, ∀ n : ℕ, n ≠ 0 →
      g ^ n ∈ ⁅presSub ρ Nt, presSub ρ Nt⁆ → g ∈ ⁅presSub ρ Nt, presSub ρ Nt⁆ by
    have hlift  :=
      fun p hp => (show LiftsMod (coverSecondBoundary Nt ρ).toAddMonoidHom p by
        let E := ringEquivPres ρ Nt hR
        apply liftsMod_of_addEquiv
          (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) (presSub ρ Nt))
          (coverSecondBoundary Nt ρ).toAddMonoidHom
          (Finsupp.mapRange.addEquiv E.toAddEquiv) (Finsupp.mapRange.addEquiv E.toAddEquiv)
          ?_ p (liftsMod_of_foxSatMod (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ)
            (presSub ρ Nt) p (hm p hp))
        intro c
        apply Finsupp.ext
        intro i
        exact fs_bdry2_ringEquivPres ρ Nt hR c i)
    rintro _ ⟨w, hw, rfl⟩ n hn hpow
    have hcommmap : ⁅presSub ρ Nt, presSub ρ Nt⁆ =
        ⁅Nt, Nt⁆.map (QuotientGroup.mk' (relSub ρ)) := by
      rw [presSub, ← Subgroup.map_commutator]
    have hcomap : w ^ n ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nt, Nt⁆ := by
      have hmem : (QuotientGroup.mk' (relSub ρ)) (w ^ n) ∈
          ⁅Nt, Nt⁆.map (QuotientGroup.mk' (relSub ρ)) := by
        rw [← hcommmap, map_pow]
        exact hpow
      have hh : w ^ n ∈ ⁅Nt, Nt⁆ ⊔ (QuotientGroup.mk' (relSub ρ)).ker := by
        rw [← Subgroup.comap_map_eq]
        exact hmem
      rw [QuotientGroup.ker_mk', relSub, sup_comm] at hh
      exact hh
    have hw' := fs_mem_relComm_of_pow_mem Nt ρ hρ hlift hw hn hcomap
    have hh : w ∈ ⁅Nt, Nt⁆ ⊔ (QuotientGroup.mk' (relSub ρ)).ker := by
      rw [QuotientGroup.ker_mk', relSub, sup_comm]
      exact hw'
    rw [← Subgroup.comap_map_eq] at hh
    rw [hcommmap]
    exact hh)
  apply isMulTorsionFree_map_commutator_of_pow N
  rwa [hNeq] at hk

section Compactness

universe u

/-- The algebraic necessity conclusion for an arbitrary presentation, with the homological
torsion-freeness input discharged by the finitely supported Hurewicz calculation. -/
theorem fs_exists_perfect_normal_of_cellChains
    {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α)
    (hchains : HasCellChainsLift (foxMatrixPres ρ)) :
    ∃ N : Subgroup (PresGroup ρ), N.Normal ∧
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
        FoxSatMod p (foxMatrixPres ρ) v N) ∧
      (∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v N) ∧
      ⁅N, N⁆ = N :=
  exists_perfect_normal_foxSatMod_of_finite_columns (foxMatrixPres ρ) hchains
    (foxMatrixPres_col_finite ρ) (fun N _ h => fs_isMulTorsionFree_of_foxSatMod_pres ρ N h)

end Compactness

end FiniteChains

namespace FiniteChains.Comb

open MonoidAlgebra
universe u

variable {α J : Type u} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

def fsCoords (β : Type u) :
    (((FreeGroup α ⧸ N) × β) →₀ ℤ) ≃ₗ[ℤ] (β →₀ CoverRing N) :=
  (Finsupp.domLCongr (Equiv.prodComm (FreeGroup α ⧸ N) β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm))

omit [DecidableEq α] in
theorem fsCoords_apply (β : Type u) (c : ((FreeGroup α ⧸ N) × β) →₀ ℤ)
    (i : β) (q : FreeGroup α ⧸ N) : (fsCoords N β c i).coeff q = c (q, i) := rfl

omit [DecidableEq α] in
theorem fsCoords_single (β : Type u) (q : FreeGroup α ⧸ N) (i : β) (n : ℤ) :
    fsCoords N β (Finsupp.single (q, i) n) =
      Finsupp.single i (MonoidAlgebra.single q n : CoverRing N) := by
  apply Finsupp.ext
  intro j
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro r
  rw [fsCoords_apply]
  by_cases hj : j = i <;> by_cases hr : r = q <;>
    simp [hj, hr]

theorem fsCoords_pathChain_liftPath_apply (L : List (α × Bool))
    (q : FreeGroup α ⧸ N) (i : α) :
    fsCoords N α (pathChain (liftPath L q)) i =
      (MonoidAlgebra.single q (1 : ℤ) : CoverRing N) * proj N (fox i (FreeGroup.mk L)) := by
  induction L generalizing q with
  | nil =>
      rw [show FreeGroup.mk [] = 1 from rfl]
      simp
  | cons a L ih =>
      obtain ⟨k, b⟩ := a
      cases b
      · have hq : (MonoidAlgebra.single (q * (qof N k)⁻¹) 1) =
            (MonoidAlgebra.single q 1) * proj N (grp (FreeGroup.of k)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp
        rw [ih, fsCoords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg,
          ← mul_assoc, ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = k <;> simp [fox_of, h]
      · have hq : (MonoidAlgebra.single (q * qof N k) 1) =
            (MonoidAlgebra.single q 1) * proj N (grp (FreeGroup.of k)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp
        rw [ih, fsCoords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = k <;> simp [fox_of, h]

variable (ρ : J → FreeGroup α) (hρ : ∀ j, ρ j ∈ N)

include hρ in
theorem fs_coverComplex_bdry2 (c : ((FreeGroup α ⧸ N) × J) →₀ ℤ) :
    coverSecondBoundary N ρ (fsCoords N J c) =
      fsCoords N α (bdry2 (coverComplex N ρ hρ) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single f n =>
      obtain ⟨q, j⟩ := f
      rw [fsCoords_single, bdry2_single, map_smul, coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [fsCoords_pathChain_liftPath_apply, FreeGroup.mk_toWord]
      change (MonoidAlgebra.single q n) * proj N (fox i (ρ j)) =
        n • ((MonoidAlgebra.single q 1) * proj N (fox i (ρ j)))
      rw [show (MonoidAlgebra.single q n) =
          n • (MonoidAlgebra.single q 1) by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], smul_mul_assoc]

end FiniteChains.Comb

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-- The deck group of the cover: the presented group of the collapse modulo `N`. -/
abbrev CovQ : Type u := FreeGroup (NonTree T) ⧸ N

/-- The translation of the cover attached to an oriented edge: trivial for a tree edge, the
class of the generator otherwise. -/
def germQ (g : K.E × Bool) : CovQ T N := QuotientGroup.mk (germWord T g)

/-- The translation attached to an edge path. -/
def wordQ (p : List (K.E × Bool)) : CovQ T N :=
  QuotientGroup.mk (pathWord T p)

variable {T N}

@[simp] theorem wordQ_nil : wordQ T N ([] : List (K.E × Bool)) = 1 := rfl

theorem wordQ_cons (g : K.E × Bool) (p : List (K.E × Bool)) :
    wordQ T N (g :: p) = germQ T N g * wordQ T N p := rfl

theorem wordQ_append (p p' : List (K.E × Bool)) :
    wordQ T N (p ++ p') = wordQ T N p * wordQ T N p' := by
  unfold wordQ
  rw [pathWord_append, QuotientGroup.mk_mul]

theorem germQ_revGerm (g : K.E × Bool) : germQ T N (revGerm g) = (germQ T N g)⁻¹ := by
  unfold germQ
  rw [germWord_revGerm, QuotientGroup.mk_inv]

theorem germQ_false_eq_inv (e : K.E) :
    germQ T N (e, false) = (germQ T N (e, true))⁻¹ := by
  simpa [revGerm] using germQ_revGerm (e, true)


@[simp] theorem wordQ_treePath (a : K.V) : wordQ T N (T.treePath a) = 1 := by
  unfold wordQ
  rw [pathWord_treePath]
  rfl

variable (T N)

/-! ### The vertices, the edges and their endpoints -/

/-- The source of an edge of the cover. -/
def covSrc (x : CovQ T N × K.E) : CovQ T N × K.V := (x.1, K.src x.2)

/-- The target of an edge of the cover. -/
def covTgt (x : CovQ T N × K.E) : CovQ T N × K.V :=
  (x.1 * germQ T N (x.2, true), K.tgt x.2)

/-- The lift at the vertex `q` of an oriented edge of `K`. -/
def liftGerm (q : CovQ T N) (g : K.E × Bool) : (CovQ T N × K.E) × Bool :=
  if g.2 then ((q, g.1), true) else ((q * germQ T N g, g.1), false)

/-- The lift at the vertex `q` of an edge path of `K`. -/
def liftK : List (K.E × Bool) → CovQ T N → List ((CovQ T N × K.E) × Bool)
  | [], _ => []
  | g :: L, q => liftGerm T N q g :: liftK L (q * germQ T N g)

variable {T N}

@[simp] theorem liftK_nil (q : CovQ T N) : liftK T N [] q = [] := rfl

@[simp] theorem liftK_cons (g : K.E × Bool) (L : List (K.E × Bool)) (q : CovQ T N) :
    liftK T N (g :: L) q = liftGerm T N q g :: liftK T N L (q * germQ T N g) := rfl

@[simp] theorem liftGerm_fst_snd (q : CovQ T N) (g : K.E × Bool) :
    ((liftGerm T N q g).1.2, (liftGerm T N q g).2) = g := by
  obtain ⟨e, b⟩ := g
  cases b <;> simp [liftGerm]



/-- The projection of a lifted path is the path itself. -/
theorem map_liftK (L : List (K.E × Bool)) (q : CovQ T N) :
    (liftK T N L q).map (fun eb => (eb.1.2, eb.2)) = L := by
  induction L generalizing q with
  | nil => rfl
  | cons g L ih => simp_all

/-- The lift at `q` of a path from `a` to `b` is a path from `(q, a)` to `(q · w, b)`, where
`w` is the word spelled by the path. -/
theorem liftK_isPath {L : List (K.E × Bool)} {a b : K.V} (hL : IsPath K.src K.tgt L a b)
    (q : CovQ T N) :
    IsPath (covSrc T N) (covTgt T N) (liftK T N L q) (q, a) (q * wordQ T N L, b) := by
  induction L generalizing a q with
  | nil => simp_all
  | cons g L ih =>
      obtain ⟨ha, hrest⟩ := hL
      subst ha
      refine ⟨?_, ?_⟩
      · rw [(show germSrc (covSrc T N) (covTgt T N) (liftGerm T N q g) = (q, germSrc K.src K.tgt g) by
        obtain ⟨e, b⟩ := g
        cases b
        · show covTgt T N (q * germQ T N (e, false), e) = (q, K.tgt e)
          show (q * germQ T N (e, false) * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
          rw [mul_assoc, (show germQ T N (e, false) * germQ T N (e, true) = 1 by
            rw [germQ_false_eq_inv]
            group), mul_one]
        · rfl)]
      · rw [(show germTgt (covSrc T N) (covTgt T N) (liftGerm T N q g) =
      (q * germQ T N g, germTgt K.src K.tgt g) by
        obtain ⟨e, b⟩ := g
        cases b
        · rfl
        · rfl), wordQ_cons, ← mul_assoc]
        exact ih hrest (q * germQ T N g)

/-! ### The cover -/

variable (T N)

/-- **The cover of `K` attached to `N ◁ F(E ∖ T)`**: vertices `Q × V`, edges `Q × E`,
two-cells `Q × F`, with the two-cell `(q, f)` attached along the lift at `q` of the attaching
path of `f`. -/
def treeCover (hN : ∀ f, treeRel T f ∈ N) : Complex2.{u} where
  V := CovQ T N × K.V
  E := CovQ T N × K.E
  F := CovQ T N × K.F
  src := covSrc T N
  tgt := covTgt T N
  base f := (f.1, K.base f.2)
  att f := liftK T N (K.att f.2) f.1
  att_isLoop f := by
    have h := liftK_isPath (T := T) (N := N) (K.att_isLoop f.2) f.1
    have hw : wordQ T N (K.att f.2) = 1 := by
      show QuotientGroup.mk (pathWord T (K.att f.2)) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hN f.2
    rwa [hw, mul_one] at h

variable {T N}

@[simp] theorem treeCover_src (hN : ∀ f, treeRel T f ∈ N) (x : CovQ T N × K.E) :
    (treeCover T N hN).src x = covSrc T N x := rfl

@[simp] theorem treeCover_tgt (hN : ∀ f, treeRel T f ∈ N) (x : CovQ T N × K.E) :
    (treeCover T N hN).tgt x = covTgt T N x := rfl

variable (T N)

/-- The projection of the cover onto `K`. -/
def treeCoverProj (hN : ∀ f, treeRel T f ∈ N) : Hom (treeCover T N hN) K where
  onV x := x.2
  onE x := x.2
  onF x := x.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    show K.att f.2 = ((treeCover T N hN).att f).map (fun eb => (eb.1.2, eb.2))
    exact (map_liftK (T := T) (N := N) (K.att f.2) f.1).symm

/-! ### The projection is a covering -/

/-! ### The deck action -/

/-! ### Connectedness -/

/-- Every element of the free group on the non-tree edges is spelled by a loop of `K` at the
root. -/
theorem exists_loop_spelling (w : FreeGroup (NonTree T)) :
    ∃ p : List (K.E × Bool), IsPath K.src K.tgt p T.root T.root ∧ pathWord T p = w := by
  induction w using FreeGroup.induction_on with
  | one => exact ⟨[], rfl, rfl⟩
  | of e =>
      refine ⟨conjPath T [(e, true)] (K.src e) (K.tgt e), ?_, ?_⟩
      · exact conjPath_isLoop T (isPath_single _)
      · rw [conjPath, pathWord_append, pathWord_append, pathWord_treePath, pathWord_revPath,
          pathWord_treePath]
        simp [pathWord, germWord, dif_neg e.2]
  | inv_of e ih =>
      obtain ⟨p, hp, hw⟩ := ih
      exact ⟨revPath p, isPath_revPath hp, by rw [pathWord_revPath, hw]⟩
  | mul x y hx hy =>
      obtain ⟨p, hp, hpw⟩ := hx
      obtain ⟨p', hp', hpw'⟩ := hy
      exact ⟨p ++ p', hp.append hp', by rw [pathWord_append, hpw, hpw']⟩

end SpanningTree
end Comb
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]

/-! ### The letters of a path outside the tree -/

open Classical in
/-- The word in the non-tree edges spelled by an edge path, as a list of letters. -/
def letters : List (K.E × Bool) → List (NonTree T × Bool)
  | [] => []
  | g :: L => if h : T.isTree g.1 then letters L else (⟨g.1, h⟩, g.2) :: letters L

variable {T}

@[simp] theorem letters_nil : letters T [] = [] := rfl

theorem letters_cons_tree {g : K.E × Bool} (h : T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = letters T L := by
  simp [letters, h]

theorem letters_cons_nontree {g : K.E × Bool} (h : ¬ T.isTree g.1) (L : List (K.E × Bool)) :
    letters T (g :: L) = (⟨g.1, h⟩, g.2) :: letters T L := by
  simp [letters, h]

/-- The list of non-tree letters spells the word of the path. -/
theorem mk_letters (L : List (K.E × Bool)) :
    FreeGroup.mk (letters T L) = pathWord T L := by
  classical
  induction L with
  | nil => rfl
  | cons g L ih =>
      by_cases h : T.isTree g.1
      · rw [letters_cons_tree h, ih, pathWord_cons, germWord_of_isTree T h, one_mul]
      · rw [letters_cons_nontree h, pathWord_cons]
        obtain ⟨e, b⟩ := g
        cases b
        · rw [mk_cons_false, ih, show germWord T (e, false)
            = (FreeGroup.of (⟨e, h⟩ : NonTree T))⁻¹ by simp [germWord, h]]
        · rw [mk_cons_true, ih, show germWord T (e, true)
            = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h]]

/-! ### The comparison maps on chains -/

theorem germQ_eq_one_of_isTree {g : K.E × Bool} (h : T.isTree g.1) : germQ T N g = 1 := by
  show QuotientGroup.mk (germWord T g) = 1
  rw [germWord_of_isTree T h]
  rfl

omit [N.Normal] in
theorem germQ_true_eq_qof {e : K.E} (h : ¬ T.isTree e) :
    germQ T N (e, true) = qof N (⟨e, h⟩ : NonTree T) := by
  show QuotientGroup.mk (germWord T (e, true)) = _
  rw [show germWord T (e, true) = FreeGroup.of (⟨e, h⟩ : NonTree T) by simp [germWord, h]]
  rfl

theorem germQ_false_eq_qof_inv {e : K.E} (h : ¬ T.isTree e) :
    germQ T N (e, false) = (qof N (⟨e, h⟩ : NonTree T))⁻¹ := by simp_all [germQ_false_eq_inv, germQ_true_eq_qof]

variable (T)

open Classical in
/-- Deleting the tree edges: the comparison map on one-chains. -/
def piE : ((CovQ T N × K.E) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × NonTree T) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × K.E =>
    if h : T.isTree x.2 then 0 else Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) (1 : ℤ))

/-- Forgetting the vertex of `K`: the comparison map on zero-chains. -/
def piV : ((CovQ T N × K.V) →₀ ℤ) →ₗ[ℤ] ((CovQ T N) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.fst

/-- Putting a vertex of the presentation cover at the root of its tree. -/
def iotaV : ((CovQ T N) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.V) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun q => (q, T.root))

variable {T}

omit [N.Normal] in
theorem piE_single_tree {x : CovQ T N × K.E} (h : T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = 0 := by
  rw [piE, Finsupp.linearCombination_single]
  simp [h]

omit [N.Normal] in
theorem piE_single_nontree {x : CovQ T N × K.E} (h : ¬ T.isTree x.2) (n : ℤ) :
    piE T N (Finsupp.single x n) = Finsupp.single (x.1, (⟨x.2, h⟩ : NonTree T)) n := by
  rw [piE, Finsupp.linearCombination_single]
  simp_all

omit [N.Normal] in
@[simp] theorem piV_single (x : CovQ T N × K.V) (n : ℤ) :
    piV T N (Finsupp.single x n) = Finsupp.single x.1 n := by
  rw [piV]
  simp [Finsupp.lmapDomain_apply]

omit [N.Normal] in
@[simp] theorem iotaV_single (q : CovQ T N) (n : ℤ) :
    iotaV T N (Finsupp.single q n) = Finsupp.single (q, T.root) n := by
  rw [iotaV]
  simp [Finsupp.lmapDomain_apply]

/-- **Deleting the tree edges from a lifted path** gives the lift of the word it spells. -/
theorem piE_pathChain_liftK (L : List (K.E × Bool)) (q : CovQ T N) :
    piE T N (pathChain (liftK T N L q)) = pathChain (liftPath (letters T L) q) := by
  induction L generalizing q with
  | nil => rfl
  | cons g L ih =>
      obtain ⟨e, b⟩ := g
      by_cases h : T.isTree e
      · have hq : q * germQ T N (e, b) = q := by
          rw [germQ_eq_one_of_isTree (N := N) h, mul_one]
        have hsnd : (liftGerm T N q (e, b)).2 = b := by cases b <;> rfl
        have hfst : (liftGerm T N q (e, b)).1.2 = e := by cases b <;> rfl
        have hz  :=
          piE_single_tree (N := N) (x := (liftGerm T N q (e, b)).1) (by rw [hfst]; exact h) 1
        rw [liftK_cons, pathChain_cons, map_add, letters_cons_tree (g := (e, b)) h, hq, ih q,
          hsnd]
        cases b
        · simp_all
        · simp_all
      · rw [liftK_cons, pathChain_cons, map_add, letters_cons_nontree (g := (e, b)) h]
        cases b
        · have hlift : liftGerm T N q (e, false) =
              ((q * germQ T N (e, false), e), false) := rfl
          rw [hlift]
          simp only [Bool.false_eq_true, if_false, map_neg]
          rw [piE_single_nontree (N := N) (x := (q * germQ T N (e, false), e)) h 1,
            ih (q * germQ T N (e, false)), germQ_false_eq_qof_inv (N := N) h,
            liftPath_cons_false, pathChain_cons]
          simp
        · have hlift : liftGerm T N q (e, true) = ((q, e), true) := rfl
          rw [hlift]
          simp only [if_true]
          rw [piE_single_nontree (N := N) (x := (q, e)) h 1,
            germQ_true_eq_qof (N := N) h, ih (q * qof N ⟨e, h⟩)]
          rw [liftPath_cons_true, pathChain_cons]
          simp

/-! ### The comparison maps are chain maps -/

variable [Fintype (NonTree T)] [DecidableEq (NonTree T)]

omit [Fintype (NonTree T)] in
/-- The chain of a lifted word depends only on the free-group element it spells. -/
theorem pathChain_liftPath_congr {L L' : List (NonTree T × Bool)}
    (h : FreeGroup.mk L = FreeGroup.mk L') (q : CovQ T N) :
    pathChain (liftPath (Nsub := N) L q) = pathChain (liftPath (Nsub := N) L' q) := by
  apply (fsCoords N (NonTree T)).injective
  apply Finsupp.ext
  intro i
  rw [fsCoords_pathChain_liftPath_apply, fsCoords_pathChain_liftPath_apply, h]

variable (hN : ∀ f, treeRel T f ∈ N)

omit [Fintype (NonTree T)] in
/-- **The comparison map is a chain map in degree two**: the two covers have the same
two-cells, and deleting the tree edges from the attaching path of a two-cell of the cover of
`K` gives the attaching path of the corresponding two-cell of the cover of the presentation
complex. -/
theorem piE_bdry2 (u : (CovQ T N × K.F) →₀ ℤ) :
    piE T N (bdry2 (treeCover T N hN) u) = bdry2 (coverComplex N (treeRel T) hN) u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp_all
  | single x n =>
      obtain ⟨q, f⟩ := x
      rw [bdry2_single, bdry2_single, map_smul]
      show n • piE T N (pathChain (liftK T N (K.att f) q)) = _
      rw [piE_pathChain_liftK]
      congr 1
      refine pathChain_liftPath_congr (N := N) ?_ q
      rw [mk_letters, FreeGroup.mk_toWord]
      rfl

omit [Fintype (NonTree T)] in
/-- **The comparison map is a chain map in degree one.** -/
theorem piV_bdry1 (c : (CovQ T N × K.E) →₀ ℤ) :
    piV T N (bdry1 (treeCover T N hN) c) = bdry1 (coverComplex N (treeRel T) hN) (piE T N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp_all
  | single x n =>
      obtain ⟨q, e⟩ := x
      rw [bdry1_single]
      by_cases h : T.isTree e
      · rw [piE_single_tree (N := N) (x := (q, e)) h n, map_zero]
        have hg  := germQ_eq_one_of_isTree (N := N) (g := (e, true)) h
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (q * germQ T N (e, true)) (1 : ℤ)
          - Finsupp.single q (1 : ℤ)) = 0
        rw [hg, mul_one, sub_self, smul_zero]
      · rw [piE_single_nontree (N := N) (x := (q, e)) h n, bdry1_single]
        rw [map_smul, map_sub, piV_single, piV_single]
        show n • (Finsupp.single (q * germQ T N (e, true)) (1 : ℤ)
          - Finsupp.single q (1 : ℤ)) = _
        rw [germQ_true_eq_qof (N := N) h]

omit [Fintype (NonTree T)] in
/-- The augmentations agree. -/
theorem augC_piV (c : (CovQ T N × K.V) →₀ ℤ) :
    augC (coverComplex N (treeRel T) hN) (piV T N c) = augC (treeCover T N hN) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp_all
  | single x n =>
      obtain ⟨q, a⟩ := x
      rw [piV_single]
      rw [augC_single, augC_single]

/-! ### Contracting the tree and lifting the generators -/

variable (T)

/-- The loop of `K` at the root carried by a non-tree edge. -/
def loopPath (ε : NonTree T) : List (K.E × Bool) :=
  conjPath T [((ε : K.E), true)] (K.src (ε : K.E)) (K.tgt (ε : K.E))

/-- Lifting the loops of the generators: a section of the comparison map on one-chains. -/
def sectionE :
    ((CovQ T N × NonTree T) →₀ ℤ) →ₗ[ℤ] ((CovQ T N × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x : CovQ T N × NonTree T =>
    pathChain (liftK T N (loopPath T x.2) x.1))

variable {T}

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem isPath_loopPath (ε : NonTree T) :
    IsPath K.src K.tgt (loopPath T ε) T.root T.root :=
  conjPath_isLoop T (isPath_single _)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem pathWord_loopPath (ε : NonTree T) : pathWord T (loopPath T ε) = FreeGroup.of ε := by
  rw [loopPath, conjPath, pathWord_append, pathWord_append, pathWord_treePath,
    pathWord_revPath, pathWord_treePath]
  simp [pathWord, germWord, dif_neg ε.2]

omit [N.Normal] [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem wordQ_loopPath (ε : NonTree T) : wordQ T N (loopPath T ε) = qof N ε := by
  show QuotientGroup.mk (pathWord T (loopPath T ε)) = _
  rw [pathWord_loopPath]
  rfl

variable (hN : ∀ f, treeRel T f ∈ N)

omit [Fintype (NonTree T)] in
/-- **Lifting the generators**: the section is a chain homotopy inverse in degree one. -/
theorem bdry1_sectionE (u : (CovQ T N × NonTree T) →₀ ℤ) :
    bdry1 (treeCover T N hN) (sectionE T N u)
      = iotaV T N (bdry1 (coverComplex N (treeRel T) hN) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp_all
  | single x n =>
      obtain ⟨q, ε⟩ := x
      have hpath := liftK_isPath (T := T) (N := N) (isPath_loopPath ε) q
      rw [wordQ_loopPath (N := N)] at hpath
      rw [sectionE, Finsupp.linearCombination_single, map_smul, bdry1_single]
      have hb  :=
        bdry1_pathChain_of_isPath (X := treeCover T N hN) hpath
      rw [hb, map_smul, map_sub, iotaV_single, iotaV_single]

/-! ### One-cycles supported on the tree vanish -/

/-- The coefficient of a boundary at a vertex. -/
theorem bdry1_apply (X : Complex2.{u}) (z : X.E →₀ ℤ) (w : X.V) :
    bdry1 X z w = ∑ x ∈ z.support, z x *
      ((Finsupp.single (X.tgt x) (1 : ℤ)) w - (Finsupp.single (X.src x) (1 : ℤ)) w) := by
  rw [bdry1, Finsupp.linearCombination_apply, Finsupp.sum]
  simp

/-- The non-root vertex whose tree edge is the given tree edge. -/
def treeTop {e : K.E} (he : T.isTree e) : K.V :=
  ((T.isTree_iff e).1 he).choose

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem treeTop_ne_root {e : K.E} (he : T.isTree e) : treeTop he ≠ T.root :=
  ((T.isTree_iff e).1 he).choose_spec.choose


omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- The vertex of a tree edge farther from the root is unique. -/
theorem up_edge_unique {a b : K.V} (ha : a ≠ T.root) (hb : b ≠ T.root)
    (h : (T.up a ha).1 = (T.up b hb).1) : a = b := by
  by_cases hs : (T.up a ha).2 = (T.up b hb).2
  · have huv  := Prod.ext h hs
    have h1  := T.up_src a ha
    have h2  := T.up_src b hb
    rw [huv, h2] at h1
    exact h1.symm
  · exfalso
    have huv : T.up b hb = revGerm (T.up a ha) := by
      refine Prod.ext h.symm ?_
      show (T.up b hb).2 = !(T.up a ha).2
      cases hx : (T.up a ha).2 <;> cases hy : (T.up b hb).2 <;> simp_all
    have hb' : b = T.parent a ha := by
      have h2  := T.up_src b hb
      rw [huv] at h2
      rw [← h2]
      simp [parent]
    have ha' : T.parent b hb = a := by
      show germTgt K.src K.tgt (T.up b hb) = a
      rw [huv]
      simpa using T.up_src a ha
    have h1 : T.ht (T.parent a ha) + 1 = T.ht a := T.ht_parent ha
    have h2 : T.ht (T.parent b hb) + 1 = T.ht b := T.ht_parent hb
    rw [← hb'] at h1
    rw [ha'] at h2
    omega

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem treeTop_eq {e : K.E} (he : T.isTree e) {a : K.V} (ha : a ≠ T.root)
    (h : (T.up a ha).1 = e) : treeTop he = a :=
  up_edge_unique (treeTop_ne_root he) ha ((((T.isTree_iff e).1 he).choose_spec.choose_spec).trans h.symm)

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- The endpoints of a tree edge are the vertex it belongs to and its parent. -/
theorem tree_edge_endpoints {e : K.E} {a : K.V} (ha : a ≠ T.root) (hup : (T.up a ha).1 = e) :
    (K.src e = a ∧ K.tgt e = T.parent a ha) ∨ (K.src e = T.parent a ha ∧ K.tgt e = a) := by
  have hsrc  := T.up_src a ha
  have htgt : germTgt K.src K.tgt (T.up a ha) = T.parent a ha := rfl
  cases hb : (T.up a ha).2
  · right
    have hg : T.up a ha = (e, false) := Prod.ext hup hb
    rw [hg] at hsrc htgt
    simp at hsrc htgt
    exact ⟨htgt, hsrc⟩
  · left
    have hg : T.up a ha = (e, true) := Prod.ext hup hb
    rw [hg] at hsrc htgt
    simp only [germSrc_true, germTgt_true] at hsrc htgt
    exact ⟨hsrc, htgt⟩

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem parent_ne_self {a : K.V} (ha : a ≠ T.root) : T.parent a ha ≠ a := by
  intro h
  have := T.ht_parent ha
  rw [h] at this
  omega

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
theorem covTgt_of_isTree {e : K.E} (he : T.isTree e) (q : CovQ T N) :
    covTgt T N (q, e) = (q, K.tgt e) := by
  show (q * germQ T N (e, true), K.tgt e) = (q, K.tgt e)
  rw [germQ_eq_one_of_isTree (N := N) (g := (e, true)) he, mul_one]

omit [Fintype (NonTree T)] [DecidableEq (NonTree T)] in
/-- **A one-cycle of the cover supported on the tree edges vanishes**: the tree edges of each
sheet form a tree, so they carry no cycle. -/
theorem treeChain_eq_zero {z : (CovQ T N × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : bdry1 (treeCover T N hN) z = 0) : z = 0 := by
  classical
  by_contra hzne
  have hne  := Finsupp.support_nonempty_iff.2 hzne
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := z.support.exists_max_image
    (fun x => if h : T.isTree x.2 then T.ht (treeTop h) else 0) hne
  have he₀ := hsupp x₀ hx₀mem
  obtain ⟨a₀, ha₀ne, ha₀up⟩ := (T.isTree_iff x₀.2).1 he₀
  have hg : ∀ x ∈ z.support, ∀ a ha, (T.up a ha).1 = x.2 →
      (if h : T.isTree x.2 then T.ht (treeTop h) else 0) = T.ht a := by
    intro x hx a ha hup
    have hex  := hsupp x hx
    rw [dif_pos hex, treeTop_eq hex ha hup]
  have hg₀ : (if h : T.isTree x₀.2 then T.ht (treeTop h) else 0) = T.ht a₀ :=
    hg x₀ hx₀mem a₀ ha₀ne ha₀up
  -- all terms but the one of `x₀` vanish at the vertex `(x₀.1, a₀)`
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single ((treeCover T N hN).tgt x) 1) (x₀.1, a₀)
        - (Finsupp.single ((treeCover T N hN).src x) 1) (x₀.1, a₀)) = 0 := by
    intro x hx hxne
    have hex  := hsupp x hx
    obtain ⟨a, hane, haup⟩ := (T.isTree_iff x.2).1 hex
    have hle : T.ht a ≤ T.ht a₀ := by
      have hmax := hx₀max x hx
      rw [hg x hx a hane haup, hg₀] at hmax
      exact hmax
    have key : ∀ v : K.V, (v = K.src x.2 ∨ v = K.tgt x.2) → (x.1, v) ≠ (x₀.1, a₀) := by
      intro v hv hc
      rw [Prod.mk.injEq] at hc
      obtain ⟨hq, hva⟩ := hc
      have hvertex : a = a₀ → False := by
        intro haa
        subst haa
        have hxe  := haup.symm.trans ha₀up
        exact hxne (Prod.ext hq hxe)
      have hparent : T.parent a hane = a₀ → False := by
        intro hp
        have hht := T.ht_parent hane
        rw [hp] at hht
        omega
      rcases tree_edge_endpoints hane haup with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · grind
      · grind
    have h1 : (treeCover T N hN).tgt x ≠ (x₀.1, a₀) := by
      rw [treeCover_tgt, show x = (x.1, x.2) from rfl, covTgt_of_isTree (N := N) hex]
      exact key (K.tgt x.2) (Or.inr rfl)
    have h2 : (treeCover T N hN).src x ≠ (x₀.1, a₀) := by
      rw [treeCover_src]
      exact key (K.src x.2) (Or.inl rfl)
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), Finsupp.single_eq_of_ne (Ne.symm h2)]
    ring
  -- evaluate the boundary at the vertex `(x₀.1, a₀)`
  have hzero : 0 = z x₀ *
      ((Finsupp.single ((treeCover T N hN).tgt x₀) 1) (x₀.1, a₀)
        - (Finsupp.single ((treeCover T N hN).src x₀) 1) (x₀.1, a₀)) := by
    have h := bdry1_apply (treeCover T N hN) z (x₀.1, a₀)
    rw [hz] at h
    have h2 := h.trans (Finset.sum_eq_single_of_mem x₀ hx₀mem hterm)
    convert h2 using 1 <;> congr 2
  have hzx₀ : z x₀ ≠ 0 := Finsupp.mem_support_iff.1 hx₀mem
  have hsrc : (treeCover T N hN).src x₀ = (x₀.1, K.src x₀.2) := rfl
  have htgt : (treeCover T N hN).tgt x₀ = (x₀.1, K.tgt x₀.2) := by
    rw [treeCover_tgt, show x₀ = (x₀.1, x₀.2) from rfl, covTgt_of_isTree (N := N) he₀]
  have hpne : T.parent a₀ ha₀ne ≠ a₀ := parent_ne_self (T := T) ha₀ne
  rcases tree_edge_endpoints ha₀ne ha₀up with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have h1 : (treeCover T N hN).tgt x₀ ≠ (x₀.1, a₀) := by
      rw [htgt, ht]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    have h2 : (treeCover T N hN).src x₀ = (x₀.1, a₀) := by rw [hsrc, hs]
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), h2, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega
  · have h1 : (treeCover T N hN).tgt x₀ = (x₀.1, a₀) := by rw [htgt, ht]
    have h2 : (treeCover T N hN).src x₀ ≠ (x₀.1, a₀) := by
      rw [hsrc, hs]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    rw [Finsupp.single_eq_of_ne (Ne.symm h2), h1, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega

/-! ### Acyclicity -/

omit [Fintype (NonTree T)] [N.Normal] in
/-- The coefficient of the comparison map at a non-tree edge. -/
theorem piE_apply (z : (CovQ T N × K.E) →₀ ℤ) (q : CovQ T N) (ε : NonTree T) :
    piE T N z (q, ε) = z (q, (ε : K.E)) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => simp_all
  | single x n =>
      by_cases h : T.isTree x.2
      · rw [piE_single_tree (N := N) h n]
        have hne : x ≠ (q, (ε : K.E)) := by
          intro hc
          exact ε.2 (by rw [hc] at h; exact h)
        simp [hne]
      · rw [piE_single_nontree (N := N) h n, Finsupp.single_apply, Finsupp.single_apply]
        congr 1
        simp only [Prod.ext_iff, Subtype.ext_iff]

omit [Fintype (NonTree T)] [N.Normal] in
theorem support_isTree_of_piE_eq_zero {z : (CovQ T N × K.E) →₀ ℤ} (h : piE T N z = 0) :
    ∀ x ∈ z.support, T.isTree x.2 := by
  intro x hx
  by_contra hnt
  have hval := piE_apply (N := N) z x.1 ⟨x.2, hnt⟩
  simp_all

end SpanningTree
end Comb
end FiniteChains
end

namespace FiniteChains
variable {α : Type*} [DecidableEq α]

/-- The group element read by one oriented letter. -/
def foxWordLetter (p : α × Bool) : FreeGroup α :=
  if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹

/-- The signed contribution of an oriented generator edge to its Fox coordinate. -/
def foxWordIncidence (i : α) (p : α × Bool) : FreeGroupRing α :=
  if i = p.1 then (if p.2 then 1 else -grp (FreeGroup.of p.1)⁻¹) else 0

omit [DecidableEq α] in
theorem fox_mk_single_letter (p : α × Bool) :
    FreeGroup.mk [p] = foxWordLetter p := by
  obtain ⟨a, b⟩ := p
  cases b
  · rfl
  · rfl


/-- The actual signed edge sum of a word path, starting at the translate `g`.
Negative letters contribute at the terminal generator coordinate. -/
def foxWordPathBoundary (i : α) (g : FreeGroup α) :
    List (α × Bool) → FreeGroupRing α
  | [] => 0
  | p :: l => grp g * foxWordIncidence i p +
      foxWordPathBoundary i (g * foxWordLetter p) l

/-- The signed edge sum equals the translated Fox derivative of the actual word. -/
theorem foxWordPathBoundary_eq (i : α) (g : FreeGroup α) (l : List (α × Bool)) :
    foxWordPathBoundary i g l = grp g * fox i (FreeGroup.mk l) := by
  induction l generalizing g with
  | nil => simp [foxWordPathBoundary, ← FreeGroup.one_eq_mk]
  | cons p l ih =>
    have hm : FreeGroup.mk (p :: l) = foxWordLetter p * FreeGroup.mk l := by
      rw [← fox_mk_single_letter, FreeGroup.mul_mk]
      rfl
    rw [foxWordPathBoundary, ih, hm, fox_mul, (show fox i (foxWordLetter p) = foxWordIncidence i p by
      obtain ⟨a, b⟩ := p
      cases b <;> by_cases h : i = a <;>
        simp [foxWordLetter, foxWordIncidence, fox_inv, h]), grp_mul,
      mul_add, mul_assoc]

/-- At the identity vertex, the word edge sum is exactly the Fox boundary entry. -/
theorem foxWordPathBoundary_one (i : α) (l : List (α × Bool)) :
    foxWordPathBoundary i 1 l = fox i (FreeGroup.mk l) := by
  rw [foxWordPathBoundary_eq, grp_one, one_mul]

end FiniteChains

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

def germValue (e : K.E × Bool) : G :=
  φ (QuotientGroup.mk (germWord T e))

def wordValue (p : List (K.E × Bool)) : G :=
  φ (QuotientGroup.mk (pathWord T p))

@[simp] theorem wordValue_nil : wordValue T φ [] = 1 := by
  simp [wordValue, pathWord_nil]

theorem wordValue_cons (e : K.E × Bool) (p : List (K.E × Bool)) :
    wordValue T φ (e :: p) = germValue T φ e * wordValue T φ p := by
  rw [wordValue, pathWord_cons, QuotientGroup.mk_mul, map_mul]
  rfl





theorem wordValue_att (f : K.F) : wordValue T φ (K.att f) = 1 := by
  have h : (QuotientGroup.mk (treeRel T f) : PresGroup (treeRel T)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_range_self f))
  change φ (QuotientGroup.mk (treeRel T f)) = 1
  rw [h, map_one]

def src (x : G × K.E) : G × K.V := (x.1, K.src x.2)

def tgt (x : G × K.E) : G × K.V :=
  (x.1 * germValue T φ (x.2, true), K.tgt x.2)

def liftGerm (g : G) (e : K.E × Bool) : (G × K.E) × Bool :=
  if e.2 then ((g, e.1), true) else ((g * germValue T φ e, e.1), false)

def liftPath : List (K.E × Bool) → G → List ((G × K.E) × Bool)
  | [], _ => []
  | e :: p, g => liftGerm T φ g e :: liftPath p (g * germValue T φ e)

@[simp] theorem liftPath_nil (g : G) : liftPath T φ [] g = [] := rfl

@[simp] theorem liftPath_cons (e : K.E × Bool) (p : List (K.E × Bool)) (g : G) :
    liftPath T φ (e :: p) g = liftGerm T φ g e :: liftPath T φ p (g * germValue T φ e) := rfl

@[simp] theorem liftGerm_projection (g : G) (e : K.E × Bool) :
    ((liftGerm T φ g e).1.2, (liftGerm T φ g e).2) = e := by grind [liftGerm]



theorem liftPath_projection (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun eb => (eb.1.2, eb.2)) = p := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih => simp_all

theorem liftPath_translate (p : List (K.E × Bool)) (h g : G) :
    liftPath T φ p (h * g) =
      (liftPath T φ p g).map (fun eb => ((h * eb.1.1, eb.1.2), eb.2)) := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih =>
    have he : liftGerm T φ (h * g) e =
        ((h * (liftGerm T φ g e).1.1, (liftGerm T φ g e).1.2), (liftGerm T φ g e).2) := by
      obtain ⟨e, b⟩ := e
      cases b <;> simp [liftGerm, mul_assoc]
    rw [liftPath_cons, liftPath_cons, he, mul_assoc, ih]
    rfl

theorem liftPath_isPath {p : List (K.E × Bool)} {a b : K.V}
    (hp : IsPath K.src K.tgt p a b) (g : G) :
    IsPath (src (K := K)) (tgt T φ) (liftPath T φ p g)
      (g, a) (g * wordValue T φ p, b) := by
  induction p generalizing a g with
  | nil => simp_all
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    subst a
    refine ⟨?_, ?_⟩
    · rw [(show germSrc (src) (tgt T φ) (liftGerm T φ g e) = (g, germSrc K.src K.tgt e) by
      obtain ⟨e, b⟩ := e
      cases b
      · change (g * germValue T φ (e, false) * germValue T φ (e, true), K.tgt e) = _
        rw [mul_assoc, (show germValue T φ (e, false) * germValue T φ (e, true) = 1 by
          rw [(show germValue T φ (e, false) = (germValue T φ (e, true))⁻¹ by
            simpa [revGerm] using (show germValue T φ (revGerm (e, true)) = (germValue T φ (e, true))⁻¹ by
              rw [germValue, germWord_revGerm, QuotientGroup.mk_inv, map_inv]
              rfl)), inv_mul_cancel]), mul_one]
        rfl
      · rfl)]
    · rw [(show germTgt (src) (tgt T φ) (liftGerm T φ g e) =
      (g * germValue T φ e, germTgt K.src K.tgt e) by
      obtain ⟨e, b⟩ := e
      cases b <;> rfl), wordValue_cons, ← mul_assoc]
      exact ih hp (g * germValue T φ e)

end FiniteChains.Comb.ReceivedTree

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

/-- This cover has precisely the coefficient group's sheets. It can be
disconnected when the receiver is not surjective; no connectedness is asserted. -/
def cover : Complex2.{u} where
  V := G × K.V
  E := G × K.E
  F := G × K.F
  src := src
  tgt := tgt T φ
  base f := (f.1, K.base f.2)
  att f := liftPath T φ (K.att f.2) f.1
  att_isLoop f := by
    have h := liftPath_isPath T φ (K.att_isLoop f.2) f.1
    rwa [wordValue_att, mul_one] at h

def projection : Hom (cover T φ) K where
  onV := Prod.snd
  onE := Prod.snd
  onF := Prod.snd
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (liftPath_projection T φ (K.att f.2) f.1).symm

def deck : DeckAction (cover T φ) G where
  smulV h x := (h * x.1, x.2)
  smulE h x := (h * x.1, x.2)
  smulF h x := (h * x.1, x.2)
  one_smulV _ := by simp
  mul_smulV _ _ _ := by simp [mul_assoc]
  one_smulE _ := by simp
  mul_smulE _ _ _ := by simp [mul_assoc]
  one_smulF _ := by simp
  mul_smulF _ _ _ := by simp [mul_assoc]
  src_smul _ _ := rfl
  tgt_smul h x := by
    change (h * x.1 * germValue T φ (x.2, true), K.tgt x.2) =
      (h * (x.1 * germValue T φ (x.2, true)), K.tgt x.2)
    rw [mul_assoc]
  base_smul _ _ := rfl
  att_smul h f := liftPath_translate T φ (K.att f.2) h f.1

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
open scoped Classical
universe u
variable {G : Type u} [Group G]

/-- Read one cell coordinate while retaining its full group-ring coefficient. -/
def cellCoefficient {E : Type u} (e : E) :
    ((G × E) →₀ ℤ) →ₗ[ℤ] MonoidAlgebra ℤ G := by
  classical
  exact Finsupp.linearCombination ℤ (fun x =>
    if x.2 = e then MonoidAlgebra.single x.1 1 else 0)

theorem cellCoefficient_single {E : Type u} (e : E) (g : G) (j : E) (n : ℤ) :
    cellCoefficient e (Finsupp.single (g, j) n) =
      if j = e then MonoidAlgebra.single g n else 0 := by
  rw [cellCoefficient, Finsupp.linearCombination_single]
  simp

theorem cellCoefficient_apply {E : Type u} (e : E) (c : (G × E) →₀ ℤ) (g : G) :
    (cellCoefficient e c).coeff g = c (g, e) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
    obtain ⟨h, j⟩ := x
    rw [cellCoefficient_single]
    by_cases hj : j = e <;> by_cases hg : h = g <;> simp [hj, hg]

/-- Assemble arbitrary group-ring coefficients into the actual finite cell chain. -/
def cellCoordinates (E : Type u) [Fintype E] :
    ((G × E) →₀ ℤ) ≃ₗ[ℤ] (E → MonoidAlgebra ℤ G) :=
  (Finsupp.domLCongr (Equiv.prodComm G E)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      ((Finsupp.linearEquivFunOnFinite ℤ (G →₀ ℤ) E).trans
        (LinearEquiv.piCongrRight (fun _ => (MonoidAlgebra.coeffLinearEquiv ℤ).symm))))

omit [Group G] in
theorem cellCoordinates_apply (E : Type u) [Fintype E]
    (c : (G × E) →₀ ℤ) (e : E) (g : G) :
    (cellCoordinates E c e).coeff g = c (g, e) := rfl

theorem cellCoefficient_eq_coordinates (E : Type u) [Fintype E]
    (c : (G × E) →₀ ℤ) (e : E) :
    cellCoefficient e c = cellCoordinates E c e := by
  ext g
  rw [cellCoefficient_apply, cellCoordinates_apply]

theorem cellCoefficient_coordinates_symm (E : Type u) [Fintype E]
    (v : E → MonoidAlgebra ℤ G) (e : E) :
    cellCoefficient e ((cellCoordinates E).symm v) = v e := by
  rw [cellCoefficient_eq_coordinates, LinearEquiv.apply_symm_apply]

variable {K : Complex2.{u}} (T : SpanningTree K)
  (φ : PresGroup (treeRel T) →* G)

def coefficientMap : FreeGroupRing (NonTree T) →+* MonoidAlgebra ℤ G :=
  (MonoidAlgebra.mapDomainRingHom ℤ φ).comp (quotRingHom ℤ (relSub (treeRel T)))

theorem coefficientMap_grp (w : FreeGroup (NonTree T)) :
    coefficientMap T φ (grp w) = MonoidAlgebra.single (φ (QuotientGroup.mk w)) 1 := by
  change MonoidAlgebra.mapDomain φ
    (quotRingHom ℤ (relSub (treeRel T)) (MonoidAlgebra.single w 1)) = _
  simp

variable [DecidableEq (NonTree T)]

/-- The signed contribution of one genuinely lifted oriented edge. -/
theorem cellCoefficient_liftGerm (i : NonTree T) (g : G) (e : K.E × Bool) :
    cellCoefficient (G := G) i.1 (pathChain [liftGerm T φ g e]) =
      MonoidAlgebra.single g 1 * coefficientMap T φ (fox i (germWord T e)) := by
  obtain ⟨e, b⟩ := e
  by_cases ht : T.isTree e
  · have hne : e ≠ i.1 := fun h => i.2 (h ▸ ht)
    cases b <;>
      simp [liftGerm, germValue, germWord, ht, pathChain, cellCoefficient_single, hne]
  · by_cases hi : e = i.1
    · subst e
      cases b <;>
        simp [liftGerm, germValue, germWord, ht, pathChain, cellCoefficient_single,
          fox_inv, coefficientMap_grp, MonoidAlgebra.single_mul_single]
    · have hni : i ≠ ⟨e, ht⟩ := fun h => hi (congrArg Subtype.val h).symm
      cases b <;>
        simp [liftGerm, germValue, germWord, ht, pathChain, cellCoefficient_single,
          fox_inv, hni, hi]

/-- The whole lifted marked path has the translated Fox coefficient of its
actual tree word. No quotient of G or augmentation is taken. -/
theorem cellCoefficient_liftPath (i : NonTree T) (g : G) (p : List (K.E × Bool)) :
    cellCoefficient (G := G) i.1 (pathChain (liftPath T φ p g)) =
      MonoidAlgebra.single g 1 * coefficientMap T φ (fox i (pathWord T p)) := by
  induction p generalizing g with
  | nil => simp
  | cons e p ih =>
    rw [liftPath_cons]
    have hc : pathChain (liftGerm T φ g e :: liftPath T φ p (g * germValue T φ e)) =
        pathChain [liftGerm T φ g e] + pathChain (liftPath T φ p (g * germValue T φ e)) :=
      by simp [pathChain]
    rw [hc, map_add, cellCoefficient_liftGerm, ih, pathWord_cons, fox_mul,
      map_add, map_mul, coefficientMap_grp, mul_add, ← mul_assoc,
      MonoidAlgebra.single_mul_single, mul_one]
    rfl

variable [Fintype K.F]

/-- The actual cellular two-boundary has exactly the received Fox coordinates. -/
theorem cellCoefficient_bdry2 (i : NonTree T) (c : (G × K.F) →₀ ℤ) :
    cellCoefficient (G := G) i.1 (bdry2 (cover T φ) c) =
      ∑ t : K.F, cellCoefficient t c * coefficientMap T φ (fox i (treeRel T t)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, hc, hd, add_mul, Finset.sum_add_distrib]
  | single x n =>
    obtain ⟨g, t⟩ := x
    rw [bdry2_single, map_smul]
    change n • cellCoefficient i.1 (pathChain (liftPath T φ (K.att t) g)) = _
    rw [cellCoefficient_liftPath]
    rw [← smul_mul_assoc, MonoidAlgebra.smul_single]
    simp [cellCoefficient_single, treeRel]

end FiniteChains.Comb.ReceivedTree
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

theorem cover_src (x : G × K.E) : (cover T φ).src x = (x.1, K.src x.2) := rfl

theorem cover_tgt_of_isTree {e : K.E} (h : T.isTree e) (g : G) :
    (cover T φ).tgt (g, e) = (g, K.tgt e) := by
  simp [cover, tgt, germValue, germWord, h]

/-- A finite chain supported on the tree cannot have boundary only at the
root in each sheet. The maximal-height argument is independent of the receiver. -/
theorem treeChain_eq_zero_off_root {z : (G × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : ∀ g v, v ≠ T.root → bdry1 (cover T φ) z (g, v) = 0) : z = 0 := by
  classical
  by_contra hzne
  have hne  := Finsupp.support_nonempty_iff.2 hzne
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := z.support.exists_max_image
    (fun x => if h : T.isTree x.2 then T.ht (treeTop h) else 0) hne
  have he₀ := hsupp x₀ hx₀mem
  obtain ⟨a₀, ha₀ne, ha₀up⟩ := (T.isTree_iff x₀.2).1 he₀
  have hg : ∀ x ∈ z.support, ∀ a ha, (T.up a ha).1 = x.2 →
      (if h : T.isTree x.2 then T.ht (treeTop h) else 0) = T.ht a := by
    intro x hx a ha hup
    have hex  := hsupp x hx
    rw [dif_pos hex, treeTop_eq hex ha hup]
  have hg₀ : (if h : T.isTree x₀.2 then T.ht (treeTop h) else 0) = T.ht a₀ :=
    hg x₀ hx₀mem a₀ ha₀ne ha₀up
  -- all terms but the one of `x₀` vanish at the vertex `(x₀.1, a₀)`
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single ((cover T φ).tgt x) 1) (x₀.1, a₀)
        - (Finsupp.single ((cover T φ).src x) 1) (x₀.1, a₀)) = 0 := by
    intro x hx hxne
    have hex  := hsupp x hx
    obtain ⟨a, hane, haup⟩ := (T.isTree_iff x.2).1 hex
    have hle : T.ht a ≤ T.ht a₀ := by
      have hmax := hx₀max x hx
      rw [hg x hx a hane haup, hg₀] at hmax
      exact hmax
    have key : ∀ v : K.V, (v = K.src x.2 ∨ v = K.tgt x.2) → (x.1, v) ≠ (x₀.1, a₀) := by
      intro v hv hc
      rw [Prod.mk.injEq] at hc
      obtain ⟨hq, hva⟩ := hc
      have hvertex : a = a₀ → False := by
        intro haa
        subst haa
        have hxe  := haup.symm.trans ha₀up
        exact hxne (Prod.ext hq hxe)
      have hparent : T.parent a hane = a₀ → False := by
        intro hp
        have hht := T.ht_parent hane
        rw [hp] at hht
        omega
      rcases tree_edge_endpoints hane haup with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · grind
      · grind
    have h1 : (cover T φ).tgt x ≠ (x₀.1, a₀) := by
      rw [cover_tgt_of_isTree T φ hex x.1]
      exact key (K.tgt x.2) (Or.inr rfl)
    have h2 : (cover T φ).src x ≠ (x₀.1, a₀) := by
      rw [cover_src]
      exact key (K.src x.2) (Or.inl rfl)
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), Finsupp.single_eq_of_ne (Ne.symm h2)]
    ring
  -- evaluate the boundary at the vertex `(x₀.1, a₀)`
  have hzero : 0 = z x₀ *
      ((Finsupp.single ((cover T φ).tgt x₀) 1) (x₀.1, a₀)
        - (Finsupp.single ((cover T φ).src x₀) 1) (x₀.1, a₀)) := by
    have h := bdry1_apply (cover T φ) z (x₀.1, a₀)
    rw [hz x₀.1 a₀ ha₀ne] at h
    have h2 := h.trans (Finset.sum_eq_single_of_mem x₀ hx₀mem hterm)
    convert h2 using 1
  have hzx₀ : z x₀ ≠ 0 := Finsupp.mem_support_iff.1 hx₀mem
  have hsrc : (cover T φ).src x₀ = (x₀.1, K.src x₀.2) := rfl
  have htgt : (cover T φ).tgt x₀ = (x₀.1, K.tgt x₀.2) := by
    rw [cover_tgt_of_isTree T φ he₀ x₀.1]
  have hpne : T.parent a₀ ha₀ne ≠ a₀ := parent_ne_self (T := T) ha₀ne
  rcases tree_edge_endpoints ha₀ne ha₀up with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have h1 : (cover T φ).tgt x₀ ≠ (x₀.1, a₀) := by
      rw [htgt, ht]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    have h2 : (cover T φ).src x₀ = (x₀.1, a₀) := by rw [hsrc, hs]
    rw [Finsupp.single_eq_of_ne (Ne.symm h1), h2, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega
  · have h1 : (cover T φ).tgt x₀ = (x₀.1, a₀) := by rw [htgt, ht]
    have h2 : (cover T φ).src x₀ ≠ (x₀.1, a₀) := by
      rw [hsrc, hs]
      intro hc
      rw [Prod.mk.injEq] at hc
      exact hpne hc.2
    rw [Finsupp.single_eq_of_ne (Ne.symm h2), h1, Finsupp.single_eq_same] at hzero
    simp at hzero
    omega

theorem edgeChain_eq_zero_of_nonTree_coordinates (c : (G × K.E) →₀ ℤ)
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = 0)
    (hb : ∀ g v, v ≠ T.root → bdry1 (cover T φ) c (g, v) = 0) : c = 0 := by
  apply treeChain_eq_zero_off_root T φ _ hb
  intro x hx
  by_contra ht
  have h := congrArg (fun a : MonoidAlgebra ℤ G => a.coeff x.1) (hc ⟨x.2, ht⟩)
  rw [cellCoefficient_apply] at h
  exact (Finsupp.mem_support_iff.mp hx) h

/-- In particular, one-chains with boundary supported over the root are
determined by their non-tree Fox coordinates, even if they are not cycles. -/
theorem edgeChains_eq_of_nonTree_coordinates (c d : (G × K.E) →₀ ℤ)
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = cellCoefficient i.1 d)
    (hb : ∀ g v, v ≠ T.root →
      bdry1 (cover T φ) c (g, v) = bdry1 (cover T φ) d (g, v)) : c = d := by
  apply sub_eq_zero.mp
  apply edgeChain_eq_zero_of_nonTree_coordinates T φ
  · simp_all
  · simp_all

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
open scoped Classical
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G) {I : Type u}

/-- The actual sum of the lifted marked paths, before choosing coordinates. -/
def markedChainMap (p : I → List (K.E × Bool)) :
    ((G × I) →₀ ℤ) →ₗ[ℤ] ((G × K.E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (liftPath T φ (p x.2) x.1))

theorem markedChainMap_single (p : I → List (K.E × Bool)) (g : G) (i : I) (n : ℤ) :
    markedChainMap T φ p (Finsupp.single (g, i) n) =
      n • pathChain (liftPath T φ (p i) g) :=
  Finsupp.linearCombination_single ℤ n (g, i)

/-- A lifted root loop may end on another sheet, but its chain boundary is
supported entirely over the root. No closedness assumption is needed. -/
theorem markedChainMap_boundary_off_root (p : I → Loop K T.root)
    (c : (G × I) →₀ ℤ) (g : G) (v : K.V) (hv : v ≠ T.root) :
    bdry1 (cover T φ) (markedChainMap T φ (fun i => (p i).1) c) (g, v) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
    obtain ⟨h, i⟩ := x
    rw [markedChainMap_single, map_smul,
      bdry1_pathChain_of_isPath (liftPath_isPath T φ (p i).2 h)]
    have h₁ : (g, v) ≠ (h * wordValue T φ (p i).1, T.root) :=
      fun he => hv (congrArg Prod.snd he)
    have h₂ : (g, v) ≠ (h, T.root) := fun he => hv (congrArg Prod.snd he)
    rw [Finsupp.smul_apply, Finsupp.sub_apply]
    change n • ((Finsupp.single (h * wordValue T φ (p i).1, T.root) 1) (g, v) -
      (Finsupp.single (h, T.root) 1) (g, v)) = 0
    rw [Finsupp.single_eq_of_ne h₁,
      Finsupp.single_eq_of_ne h₂, sub_self, smul_zero]

variable [Fintype I] [DecidableEq (NonTree T)]

theorem cellCoefficient_markedChainMap (p : I → List (K.E × Bool))
    (c : (G × I) →₀ ℤ) (z : NonTree T) :
    cellCoefficient z.1 (markedChainMap T φ p c) =
      ∑ i, cellCoefficient i c * coefficientMap T φ (fox z (pathWord T (p i))) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, add_mul, Finset.sum_add_distrib]
  | single x n =>
    obtain ⟨g, i⟩ := x
    rw [markedChainMap_single, map_smul, cellCoefficient_liftPath,
      ← smul_mul_assoc, MonoidAlgebra.smul_single]
    simp [cellCoefficient_single]

/-- Assemble the full group-ring marked coefficients into genuine edge chains. -/
def markedChain (p : I → Loop K T.root) (γ : I → MonoidAlgebra ℤ G) :
    (G × K.E) →₀ ℤ :=
  markedChainMap T φ (fun i => (p i).1) ((cellCoordinates I).symm γ)

theorem cellCoefficient_markedChain (p : I → Loop K T.root)
    (γ : I → MonoidAlgebra ℤ G) (z : NonTree T) :
    cellCoefficient z.1 (markedChain T φ p γ) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1)) := by
  rw [markedChain, cellCoefficient_markedChainMap]
  simp only [cellCoefficient_coordinates_symm]

omit [DecidableEq (NonTree T)] in
theorem markedChain_boundary_off_root (p : I → Loop K T.root)
    (γ : I → MonoidAlgebra ℤ G) (g : G) (v : K.V) (hv : v ≠ T.root) :
    bdry1 (cover T φ) (markedChain T φ p γ) (g, v) = 0 :=
  markedChainMap_boundary_off_root T φ p _ g v hv

/-- Equality of the non-tree Fox coordinates of a two-boundary and a marked
chain implies exact equality of the edge chains, including every tree edge. -/
theorem bdry2_eq_markedChain_of_coordinates (p : I → Loop K T.root)
    (γ : I → MonoidAlgebra ℤ G) (c : (G × K.F) →₀ ℤ)
    (hc : ∀ z : NonTree T, cellCoefficient z.1 (bdry2 (cover T φ) c) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1))) :
    bdry2 (cover T φ) c = markedChain T φ p γ := by
  apply edgeChains_eq_of_nonTree_coordinates T φ
  · intro z
    rw [cellCoefficient_markedChain]
    exact hc z
  · intro g v hv
    rw [bdry1_bdry2, Finsupp.zero_apply, markedChain_boundary_off_root T φ p γ g v hv]

end FiniteChains.Comb.ReceivedTree
end

namespace FiniteChains.BlockFamily

universe u v

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  {ρ : Jr ⊕ Sx → FreeGroup α}
  {bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)}

/-- Simultaneous substitution is injective when each block has its own marked receiver.
No common geometric attaching map, or finiteness of the family, is required. -/
theorem injective_substHomF_of_separate_receivers
    (hfill : FilledF ρ bsub) {G : Sx → Type v} [∀ s, Group (G s)]
    (j : ∀ s, PresGroup ρ →* G s) (hj : ∀ s, Function.Injective (j s))
    (b : ∀ s, FreeGroup (α ⊕ Zt s) →* G s)
    (hmark : ∀ s a, b s (FreeGroup.of (Sum.inl a)) =
      j s (QuotientGroup.mk (FreeGroup.of a)))
    (hrel : ∀ s m, b s (bsub s m) = 1) :
    Function.Injective (substHomF ρ bsub hfill) := by
  let B : BlockMaps ρ bsub (Monoid.PushoutI.base j) :=
    { b := fun s => (Monoid.PushoutI.of s).comp (b s)
      mark := fun s a => by
        rw [MonoidHom.comp_apply, hmark s a, Monoid.PushoutI.of_apply_eq_base]
      rel := fun s m => by rw [MonoidHom.comp_apply, hrel s m, map_one] }
  exact B.injective_substHomF hfill (Monoid.PushoutI.base_injective hj)

end FiniteChains.BlockFamily

namespace FiniteChains.BlockFamily

variable {α Jr Sx : Type} {Zt Mt : Sx → Type}
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

/-- Fillings using only the relators of their own block give simultaneous fillings. -/
theorem filledF_of_block_consequences
    (h : ∀ s, FreeGroup.map (Sum.inl (β := Zt s)) (ρ (Sum.inr s)) ∈
      Subgroup.normalClosure (Set.range (bsub s))) : FilledF ρ bsub := by
  intro s
  have hm : (FreeGroup.map (genEmb (Zt := Zt) s)).comp
      (FreeGroup.map (Sum.inl (β := Zt s))) =
      FreeGroup.map (Sum.inl (α := α)) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  rw [← DFunLike.congr_fun hm (ρ (Sum.inr s))]
  apply Davis.map_mem_normalClosure (FreeGroup.map (genEmb s)) ?_ (h s)
  rintro w ⟨m, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩

/-- Reindex the source so that just the selected entry is replaced. -/
def oneRel (s : Sx) : (Jr ⊕ {t : Sx // t ≠ s}) ⊕ PUnit.{1} → FreeGroup α :=
  Sum.elim (Sum.elim (fun r => ρ (Sum.inl r)) (fun t => ρ (Sum.inr t.val)))
    (fun _ => ρ (Sum.inr s))


/-- The reindexing preserves the group and every old word. -/
def oneEquiv (s : Sx) : PresGroup ρ ≃* PresGroup (oneRel ρ s) :=
  QuotientGroup.congr _ _ (MulEquiv.refl _) (by
    rw [MulEquiv.coe_monoidHom_refl, Subgroup.map_id]
    simp only [relSub, (show Set.range (oneRel ρ s) = Set.range ρ by
      ext w
      constructor
      · rintro ⟨((r | t) | p), rfl⟩
        · exact ⟨Sum.inl r, rfl⟩
        · exact ⟨Sum.inr t.val, rfl⟩
        · exact ⟨Sum.inr s, rfl⟩
      · rintro ⟨(r | t), rfl⟩
        · exact ⟨Sum.inl (Sum.inl r), rfl⟩
        · by_cases h : t = s
          · subst t; exact ⟨Sum.inr PUnit.unit, rfl⟩
          · exact ⟨Sum.inl (Sum.inr ⟨t, h⟩), rfl⟩)])

@[simp] theorem oneEquiv_mk (s : Sx) (w : FreeGroup α) :
    oneEquiv ρ s (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

/-- Injectivity of every individual substitution implies injectivity of their simultaneous
substitution, even for an infinite or empty family of entries. -/
theorem injective_substHomF_of_individual
    (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (hinj : ∀ s, Function.Injective
      (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s))) :
    Function.Injective (substHomF ρ bsub hfill) := by
  let G s := PresGroup (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
  let j  := fun s =>
    (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)).comp
      (oneEquiv ρ s).toMonoidHom
  let b : ∀ s, FreeGroup (α ⊕ Zt s) →* G s := fun s =>
    (QuotientGroup.mk' _).comp
      (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit))
  apply injective_substHomF_of_separate_receivers hfill j
    (fun s => (hinj s).comp (oneEquiv ρ s).injective) b
  · intro s a
    rfl
  · intro s m
    apply (QuotientGroup.eq_one_iff _).2
    exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨PUnit.unit, m⟩, rfl⟩

end FiniteChains.BlockFamily

namespace FiniteChains
namespace Comb

universe u

variable {α : Type u} [DecidableEq α] {J : Type u}

/-! ### From edge loops to the presented group -/

section

variable (ρ : J → FreeGroup α)

/-- The class in `G = F/R` of the word spelled by an edge path of the presentation
complex. -/
def presWord (l : List (α × Bool)) : PresGroup ρ := QuotientGroup.mk (FreeGroup.mk l)

omit [DecidableEq α] in
@[simp] theorem presWord_nil : presWord ρ [] = 1 := rfl

omit [DecidableEq α] in
theorem presWord_append (l l' : List (α × Bool)) :
    presWord ρ (l ++ l') = presWord ρ l * presWord ρ l' := rfl


/-- Elementary cancellations of edge paths do not change the class of the spelled word. -/
theorem presWord_cancels {l l' : List (α × Bool)} (h : Cancels (presComplex ρ) l l') :
    presWord ρ l = presWord ρ l' := by
  rcases h with ⟨p, q, eb, hl, hl'⟩ | ⟨p, q, j, hl, hl'⟩
  · obtain ⟨x, b⟩ := eb
    subst hl; subst hl'
    unfold presWord
    exact congrArg QuotientGroup.mk (Quot.sound FreeGroup.Red.Step.not)
  · subst hl; subst hl'
    rw [presWord_append, presWord_append, presWord_append, (show presWord ρ ((presComplex ρ).att j) = 1 by
      have h : presWord ρ ((presComplex ρ).att j) = QuotientGroup.mk (ρ j) := by
        unfold presWord
        rw [show (presComplex ρ).att j = (ρ j).toWord from rfl, FreeGroup.mk_toWord]
      rw [h, QuotientGroup.eq_one_iff]
      exact Subgroup.subset_normalClosure ⟨j, rfl⟩), mul_one]

/-- Homotopic edge paths spell the same element of `G`. -/
theorem presWord_htpy {a b : (presComplex ρ).V} {l l' : List (α × Bool)}
    (h : Htpy (presComplex ρ) a b l l') : presWord ρ l = presWord ρ l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (presWord_cancels ρ hs.2.2)
      · exact ih.trans (presWord_cancels ρ hs.2.2).symm

/-- The homomorphism `π₁(K) → G` reading off the word spelled by an edge loop. -/
def pi1ToPres : Pi1 (presComplex ρ) PUnit.unit →* PresGroup ρ where
  toFun := Quotient.lift (fun p => presWord ρ p.1) (fun _ _ h => presWord_htpy ρ h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    exact presWord_append ρ p.1 q.1

/-! ### From the presented group to edge loops -/

/-- The class of an arbitrary word, read as an edge loop of the presentation complex. -/
def loopClass (l : List (α × Bool)) : Pi1 (presComplex ρ) PUnit.unit :=
  Pi1.mk ⟨l, isPath_of_subsingleton _ _ _ _ _⟩

theorem loopClass_append (l l' : List (α × Bool)) :
    loopClass ρ (l ++ l') = loopClass ρ l * loopClass ρ l' := rfl

@[simp] theorem loopClass_nil : loopClass ρ [] = 1 := rfl

/-- The edge loop of a generator. -/
def genLoop (i : α) : Pi1 (presComplex ρ) PUnit.unit := loopClass ρ [(i, true)]


/-- Attaching words are null-homotopic, so they give the trivial loop class. -/
theorem loopClass_att (j : J) : loopClass ρ ((presComplex ρ).att j) = 1 := by
  refine Quotient.sound ?_
  refine Htpy.of_step ⟨isPath_of_subsingleton _ _ _ _ _, isPath_of_subsingleton _ _ _ _ _, ?_⟩
  exact Or.inr ⟨[], [], j, by simp, rfl⟩

/-- The homomorphism `F → π₁(K)` sending a generator to its edge loop. -/
def freeToPi1 : FreeGroup α →* Pi1 (presComplex ρ) PUnit.unit := FreeGroup.lift (genLoop ρ)

theorem freeToPi1_mk (l : List (α × Bool)) :
    freeToPi1 ρ (FreeGroup.mk l) = loopClass ρ l := by
  induction l with
  | nil => rfl
  | cons eb l ih =>
      obtain ⟨i, b⟩ := eb
      have hsplit : ((i, b) :: l) = [(i, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih, loopClass_append]
      congr 1
      cases b
      · rfl
      · rfl


theorem relSub_le_ker_freeToPi1 : relSub ρ ≤ (freeToPi1 ρ).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨j, rfl⟩
  exact (show freeToPi1 ρ (ρ j) = 1 by
    have h : freeToPi1 ρ (ρ j) = loopClass ρ ((presComplex ρ).att j) := by
      conv_lhs => rw [← FreeGroup.mk_toWord (x := ρ j)]
      rw [freeToPi1_mk]
    rw [h, loopClass_att])

/-- The homomorphism `G → π₁(K)` induced by `F → π₁(K)`. -/
def presToPi1 : PresGroup ρ →* Pi1 (presComplex ρ) PUnit.unit :=
  QuotientGroup.lift (relSub ρ) (freeToPi1 ρ) (fun _ hx => relSub_le_ker_freeToPi1 ρ hx)

@[simp] theorem presToPi1_mk (w : FreeGroup α) :
    presToPi1 ρ (QuotientGroup.mk w) = freeToPi1 ρ w := rfl

/-! ### The isomorphism -/

theorem presToPi1_pi1ToPres (x : Pi1 (presComplex ρ) PUnit.unit) :
    presToPi1 ρ (pi1ToPres ρ x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
      obtain ⟨l, hl⟩ := p
      show presToPi1 ρ (presWord ρ l) = loopClass ρ l
      rw [show presWord ρ l = QuotientGroup.mk (FreeGroup.mk l) from rfl, presToPi1_mk,
        freeToPi1_mk]

theorem pi1ToPres_presToPi1 (g : PresGroup ρ) : pi1ToPres ρ (presToPi1 ρ g) = g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      rw [presToPi1_mk, ← FreeGroup.mk_toWord (x := w), freeToPi1_mk]
      show presWord ρ w.toWord = _
      rw [show presWord ρ w.toWord = QuotientGroup.mk (FreeGroup.mk w.toWord) from rfl,
        FreeGroup.mk_toWord]

/-- **The fundamental group of a presentation complex is the presented group**: the edge-path
group of `presComplex ρ` at its unique vertex is `F/⟪r_j⟫`. -/
def pi1PresEquiv : Pi1 (presComplex ρ) PUnit.unit ≃* PresGroup ρ where
  toFun := pi1ToPres ρ
  invFun := presToPi1 ρ
  left_inv := presToPi1_pi1ToPres ρ
  right_inv := pi1ToPres_presToPi1 ρ
  map_mul' := (pi1ToPres ρ).map_mul

end

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {α : Type u} [DecidableEq α] {J : Type u}

/-! ### The exponent-sum homomorphism -/

/-- The exponent-sum vector of a word in the free group. -/
def expVec : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  FreeGroup.lift fun a => Multiplicative.ofAdd (Finsupp.single a (1 : ℤ))


omit [DecidableEq α] in
theorem pathChain_append (l l' : List (α × Bool)) :
    pathChain (l ++ l') = pathChain l + pathChain l' := by
  simp [pathChain]


omit [DecidableEq α] in
/-- The exponent-sum vector of a word is the one-chain carried by the edge path spelling
it. -/
theorem expVec_pathChain (L : List (α × Bool)) :
    expVec (FreeGroup.mk L) = Multiplicative.ofAdd (pathChain L) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      rw [show (x :: L) = [x] ++ L from rfl, ← FreeGroup.mul_mk, map_mul, ih,
        pathChain_append, (show expVec (FreeGroup.mk [x]) = Multiplicative.ofAdd (pathChain [x]) by
          obtain ⟨a, b⟩ := x
          cases b
          · rfl
          · rfl)]
      rfl

/-! ### The presentation complex -/

variable (ρ : J → FreeGroup α)

@[simp] theorem bdry1_presComplex (c : α →₀ ℤ) : bdry1 (presComplex ρ) c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp_all
  | single a n => simp [bdry1]

theorem bdry2_pres_single (j : J) :
    bdry2 (presComplex ρ) (Finsupp.single j (1 : ℤ))
      = Multiplicative.toAdd (expVec (ρ j)) := by
  rw [bdry2_single, one_smul]
  have h : (presComplex ρ).att j = (ρ j).toWord := rfl
  rw [h]
  conv_rhs => rw [← FreeGroup.mk_toWord (x := ρ j)]
  rw [expVec_pathChain]
  rfl

/-! ### The Hurewicz isomorphism -/

end Comb
end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def normalizeOrdEdge (e : OrdEdge P) : StrictOrdEdge P →₀ ℤ := by
  classical
  exact if h : e.1.1 = e.1.2 then 0 else
    Finsupp.single ⟨e.1, lt_of_le_of_ne e.2 h⟩ 1

def normalizeOrdChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdEdge P →₀ ℤ) :=
  Finsupp.linearCombination ℤ normalizeOrdEdge

def normalizeOrdTriangle (t : OrdTri P) : StrictOrdTri P →₀ ℤ := by
  classical
  exact if h : t.1.1 < t.1.2.1 ∧ t.1.2.1 < t.1.2.2 then
    Finsupp.single ⟨t.1, h⟩ 1 else 0

def normalizeOrdChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ normalizeOrdTriangle

@[simp] theorem normalizeOrdChain1_single (e : OrdEdge P) (n : ℤ) :
    normalizeOrdChain1 (Finsupp.single e n) = n • normalizeOrdEdge e := by
  simp [normalizeOrdChain1]

@[simp] theorem normalizeOrdChain2_single (t : OrdTri P) (n : ℤ) :
    normalizeOrdChain2 (Finsupp.single t n) = n • normalizeOrdTriangle t := by
  simp [normalizeOrdChain2]

theorem normalizeOrdChain1_pathChain (p : List ((orderCx P).E × Bool)) :
    normalizeOrdChain1 (pathChain p) = pathChain (normalizeOrdPath p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rw [pathChain_cons, map_add, ih]
    change _ = pathChain (normalizeOrdGerm e ++ normalizeOrdPath p)
    rw [pathChain_append]
    congr 1
    rcases e with ⟨e, b⟩
    cases b <;> by_cases h : e.1.1 = e.1.2 <;>
      simp [normalizeOrdGerm, normalizeOrdEdge, h, pathChain, map_neg]


/-- Normalization commutes with the first cellular boundary. -/
theorem bdry1_normalizeOrdChain1 (c : OrdEdge P →₀ ℤ) :
    bdry1 (strictOrderCx P) (normalizeOrdChain1 c) = bdry1 (orderCx P) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [normalizeOrdChain1_single, map_smul, (show bdry1 (strictOrderCx P) (normalizeOrdEdge e) =
      Finsupp.single e.1.2 1 - Finsupp.single e.1.1 1 by
      by_cases h : e.1.1 = e.1.2
      · simp [normalizeOrdEdge, h]
      · simp [normalizeOrdEdge, h, strictOrderCx, bdry1]), bdry1_single]
    rfl

/-- Degenerate triangles normalize to zero; genuine triangles retain their boundary. -/
theorem bdry2_normalizeOrdTriangle (t : OrdTri P) :
    bdry2 (strictOrderCx P) (normalizeOrdTriangle t) =
      pathChain (normalizeOrdPath ((orderCx P).att t)) := by
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  by_cases heab : a = b
  · subst b
    by_cases hac : a = c <;> simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx,
      pathChain, bdry2, Finsupp.linearCombination_apply, strictOrderCx, hac]
  · by_cases hebc : b = c
    · subst c
      simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx,
        pathChain, bdry2, Finsupp.linearCombination_apply, strictOrderCx, heab]
    · have hab'  := lt_of_le_of_ne hab heab
      have hbc'  := lt_of_le_of_ne hbc hebc
      simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx,
        pathChain, bdry2, Finsupp.linearCombination_apply, strictOrderCx, bdry2, hab', hbc', hab'.ne, hbc'.ne, (hab'.trans hbc').ne]

/-- Normalization commutes with the second cellular boundary. -/
theorem bdry2_normalizeOrdChain2 (c : OrdTri P →₀ ℤ) :
    bdry2 (strictOrderCx P) (normalizeOrdChain2 c) =
      normalizeOrdChain1 (bdry2 (orderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    rw [normalizeOrdChain2_single, map_smul, bdry2_normalizeOrdTriangle,
      bdry2_single, map_smul, normalizeOrdChain1_pathChain]

/-- Normalization is a retraction of the inclusion on one-chains. -/
theorem normalizeOrdChain1_inclusion (c : StrictOrdEdge P →₀ ℤ) :
    normalizeOrdChain1 (Finsupp.mapDomain (strictOrderIncl P).onE c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single e n =>
    simp [normalizeOrdEdge, strictOrderIncl, e.2.ne]

/-- Normalization is a retraction of the inclusion on two-chains. -/
theorem normalizeOrdChain2_inclusion (c : StrictOrdTri P →₀ ℤ) :
    normalizeOrdChain2 (Finsupp.mapDomain (strictOrderIncl P).onF c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single t n =>
    simp [normalizeOrdTriangle, strictOrderIncl, t.2.1, t.2.2]

/-- Every weak cellular two-cycle has a normalized strict cellular two-cycle. -/
theorem normalizeOrdChain2_cycle (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    bdry2 (strictOrderCx P) (normalizeOrdChain2 c) = 0 := by
  rw [bdry2_normalizeOrdChain2, hc, map_zero]

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictTriangleEdge01 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.1.1, t.1.2.1), t.2.1⟩
def strictTriangleEdge12 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
def strictTriangleEdge02 (t : StrictOrdTri P) : StrictOrdEdge P :=
  ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩

/-- The genuine cellular boundary of a strict triangle, with its actual orientations. -/
theorem strictTriangle_bdry2_single (t : StrictOrdTri P) (n : ℤ) :
    bdry2 (strictOrderCx P) (Finsupp.single t n) =
      Finsupp.single (strictTriangleEdge01 t) n +
      Finsupp.single (strictTriangleEdge12 t) n -
      Finsupp.single (strictTriangleEdge02 t) n := by
  rw [bdry2_single]
  simp only [strictOrderCx, pathChain_cons, pathChain_nil, if_true, Bool.false_eq_true,
    if_false, add_zero]
  rw [smul_add, smul_add, smul_neg]
  simp
  rw [sub_eq_add_neg, add_assoc]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictBelow (v : P) := {p : P // p < v}

instance (v : P) : PartialOrder (StrictBelow v) := Subtype.partialOrder _

def strictRayEdge (v : P) (e : StrictOrdEdge P) : StrictBelow v →₀ ℤ := by
  classical
  exact if h : e.1.2 = v then Finsupp.single ⟨e.1.1, h ▸ e.2⟩ 1 else 0

def strictRayChain (v : P) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictBelow v →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictRayEdge v)

def strictTopLinkTriangle (v : P) (t : StrictOrdTri P) :
    StrictOrdEdge (StrictBelow v) →₀ ℤ := by
  classical
  exact if h : t.1.2.2 = v then Finsupp.single
    ⟨(⟨t.1.1, h ▸ t.2.1.trans t.2.2⟩, ⟨t.1.2.1, h ▸ t.2.2⟩), t.2.1⟩ 1 else 0

def strictTopLinkChain (v : P) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (StrictBelow v) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictTopLinkTriangle v)

/-- At a maximal vertex, extracting cone rays from the actual triangle boundary
is the actual boundary of the extracted link edge chain. -/
theorem strictTopLink_boundary (v : P) (hm : ∀ p, v ≤ p → p = v)
    (c : StrictOrdTri P →₀ ℤ) :
    strictRayChain v (bdry2 (strictOrderCx P) c) =
      bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    have hmid : t.1.2.1 ≠ v := by
      intro he
      have ht := hm t.1.2.2 (he ▸ t.2.2.le)
      exact (ne_of_lt t.2.2) (he.trans ht.symm)
    rw [strictTriangle_bdry2_single, map_sub, map_add]
    by_cases ht : t.1.2.2 = v
    · simp [strictRayChain, strictRayEdge, strictTopLinkChain, strictTopLinkTriangle,
        strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, hmid, ht,
        bdry1, strictOrderCx, smul_sub]
    · simp [strictRayChain, strictRayEdge, strictTopLinkChain, strictTopLinkTriangle,
        strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, hmid, ht]

/-- Genuine cover two-cycles give genuine one-cycles in the link of each maximal apex. -/
theorem strictTopLink_cycle (v : P) (hm : ∀ p, v ≤ p → p = v)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) = 0 := by
  rw [← strictTopLink_boundary v hm, hc, map_zero]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- A comparability interval lifts inside the specified interval upstairs. -/
theorem exists_interval_lift {a b : P} (hab : a ≤ b) (q : Q)
    (haq : f a ≤ q) (hqb : q ≤ f b) :
    ∃ c : P, a ≤ c ∧ c ≤ b ∧ f c = q := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a q haq
  obtain ⟨d, ⟨hcd, hfd⟩, _⟩ := hf.up c (f b) (hfc ▸ hqb)
  have hd  := hf.up_inj (hac.trans hcd) hab hfd
  grind

def downTransform (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) : P :=
  Classical.choose (hf.down a (g (f a)) (hg (f a)))

theorem downTransform_spec (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) :
    hf.downTransform g hg a ≤ a ∧ f (hf.downTransform g hg a) = g (f a) :=
  (Classical.choose_spec (hf.down a (g (f a)) (hg (f a)))).1

/-- The canonical downward lift is monotone; uniqueness of interval lifts supplies
the comparison between its values, without any choice-coherence hypothesis. -/
theorem downTransform_monotone (g : Q → Q) (hmono : Monotone g) (hg : ∀ q, g q ≤ q) :
    Monotone (hf.downTransform g hg) := by
  intro a b hab
  have ha := hf.downTransform_spec g hg a
  have hb := hf.downTransform_spec g hg b
  obtain ⟨c, hxc, hcb, hfc⟩ := hf.exists_interval_lift (ha.1.trans hab) (g (f b))
    (ha.2 ▸ hmono (hf.mono hab)) (hg (f b))
  have he  := hf.down_inj hcb hb.1 (hfc.trans hb.2.symm)
  exact he ▸ hxc

/-- The lifted transformation lies below the identity, exactly as its original does. -/
theorem downTransform_le (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) :
    hf.downTransform g hg a ≤ a := (hf.downTransform_spec g hg a).1

end IsPosetCover
end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- Canonical lift of an upward order homotopy through an actual poset cover. -/
def upTransform (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) : P :=
  Classical.choose (hf.up a (g (f a)) (hg (f a)))

theorem upTransform_spec (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) :
    a ≤ hf.upTransform g hg a ∧ f (hf.upTransform g hg a) = g (f a) :=
  (Classical.choose_spec (hf.up a (g (f a)) (hg (f a)))).1

theorem upTransform_monotone (g : Q → Q) (hm : Monotone g) (hg : ∀ q, q ≤ g q) :
    Monotone (hf.upTransform g hg) := by
  intro a b hab
  obtain ⟨c, hac, hcb, hfc⟩ := hf.exists_interval_lift
    (hab.trans (hf.upTransform_spec g hg b).1) (g (f a)) (hg (f a))
    (by rw [(hf.upTransform_spec g hg b).2]; exact hm (hf.mono hab))
  have hc  := hf.up_inj hac
    (hf.upTransform_spec g hg a).1 (hfc.trans (hf.upTransform_spec g hg a).2.symm)
  exact hc ▸ hcb

theorem le_upTransform (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) :
    a ≤ hf.upTransform g hg a := (hf.upTransform_spec g hg a).1

theorem upTransform_fixed (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P)
    (ha : g (f a) = f a) : hf.upTransform g hg a = a :=
  hf.up_inj (hf.le_upTransform g hg a) (le_refl a)
    ((hf.upTransform_spec g hg a).2.trans ha)

theorem strictMono : StrictMono f := by
  intro a b h
  apply lt_of_le_of_ne (hf.mono h.le)
  intro he
  have hb  := hf.up_inj h.le (le_refl a) he.symm
  simp_all

end IsPosetCover
end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
def strictBelowCongr {a b : P} (h : a = b) : StrictBelow a ≃o StrictBelow b := by
  cases h
  exact OrderIso.refl _

namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- The order in a common lower interval is reflected by an actual covering projection. -/
theorem le_of_le_below {a b v : P} (ha : a ≤ v) (hb : b ≤ v) (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hcb, hfc⟩, _⟩ := hf.down b (f a) h
  have hc  := hf.down_inj (hcb.trans hb) ha hfc
  exact hc ▸ hcb

def lowerIntervalLift (v : P) (q : StrictBelow (f v)) : StrictBelow v := by
  let a := Classical.choose (hf.down v q.1 q.2.le)
  have hs : a ≤ v ∧ f a = q.1 := (Classical.choose_spec (hf.down v q.1 q.2.le)).1
  exact ⟨a, lt_of_le_of_ne hs.1 (by
    intro he
    exact (ne_of_lt q.2) (hs.2.symm.trans (congrArg f he)))⟩

theorem lowerIntervalLift_projection (v : P) (q : StrictBelow (f v)) :
    f (hf.lowerIntervalLift v q).1 = q.1 :=
  (Classical.choose_spec (hf.down v q.1 q.2.le)).1.2

/-- Genuine lower intervals of a poset cover are isomorphic to their projected intervals. -/
def lowerIntervalOrderIso (v : P) : StrictBelow v ≃o StrictBelow (f v) where
  toFun p := ⟨f p.1, hf.strictMono p.2⟩
  invFun := hf.lowerIntervalLift v
  left_inv p := Subtype.ext (hf.down_inj (hf.lowerIntervalLift v _).2.le p.2.le
    (hf.lowerIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.lowerIntervalLift_projection v q)
  map_rel_iff' {a b} := ⟨fun h => hf.le_of_le_below a.2.le b.2.le h, fun h => hf.mono h⟩

end IsPosetCover
end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def OrdTet (P : Type u) [PartialOrder P] :=
  {t : P × P × P × P // t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2}

def ordTetBoundary (t : OrdTet P) : OrdTri P →₀ ℤ :=
  Finsupp.single ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩ 1 +
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩ 1

def ordBoundary3 : (OrdTet P →₀ ℤ) →ₗ[ℤ] (OrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ ordTetBoundary

/-- The alternating three-simplex boundary is a genuine cellular two-cycle. -/

theorem bdry2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    bdry2 (orderCx P) (ordBoundary3 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    simp only [ordBoundary3, Finsupp.linearCombination_single, map_smul,
      (show bdry2 (orderCx P) (ordTetBoundary t) = 0 by
        simp only [ordTetBoundary, map_sub, map_add, bdry2_single (X := orderCx P), one_smul]
        simp [orderCx, pathChain]
        all_goals abel), smul_zero]

def ordNormalizationHomotopy1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ]
    (OrdTri P →₀ ℤ) := by
  classical
  exact Finsupp.linearCombination ℤ (fun e =>
    if e.1.1 = e.1.2 then
      Finsupp.single ⟨(e.1.1, e.1.1, e.1.1), le_rfl, le_rfl⟩ 1 else 0)

def ordNormalizationTriangleHomotopy (t : OrdTri P) : OrdTet P →₀ ℤ := by
  classical
  exact if h : t.1.1 = t.1.2.1 then
    Finsupp.single ⟨(t.1.1, t.1.1, t.1.1, t.1.2.2), le_rfl, le_rfl,
      h ▸ t.2.2⟩ 1 else if h' : t.1.2.1 = t.1.2.2 then
    -Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.1, t.1.2.1), t.2.1, le_rfl, le_rfl⟩ 1
    else 0

def ordNormalizationHomotopy2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    (OrdTet P →₀ ℤ) :=
  Finsupp.linearCombination ℤ ordNormalizationTriangleHomotopy

/-- The discrepancy on a triangle is an explicit three-boundary plus the homotopy of
its edge boundary. This includes triangles with coinciding vertices. -/
theorem ordNormalization_triangle_identity (t : OrdTri P) :
    Finsupp.single t (1 : ℤ) -
      (Finsupp.mapDomain (strictOrderIncl P).onF (normalizeOrdTriangle t) : OrdTri P →₀ ℤ) =
    ordNormalizationHomotopy1 (pathChain ((orderCx P).att t)) +
      ordBoundary3 (ordNormalizationTriangleHomotopy t) := by
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  by_cases heab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary]
    · simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary]
  · by_cases hebc : b = c
    · subst c
      simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary, heab]
    · have hab'  := lt_of_le_of_ne hab heab
      have hbc'  := lt_of_le_of_ne hbc hebc
      simp [normalizeOrdTriangle, strictOrderIncl, ordNormalizationHomotopy1,
        pathChain, orderCx, ordNormalizationTriangleHomotopy, ordBoundary3,
        hab', hbc', heab, hebc, (hab'.trans hbc').ne]

/-- The inclusion on strict two-chains, as an integer-linear map. -/
def ordStrictInclusion2 : (StrictOrdTri P →₀ ℤ) →ₗ[ℤ]
    (OrdTri P →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (strictOrderIncl P).onF

/-- The explicit normalization homotopy on arbitrary finitely supported two-chains. -/
theorem ordNormalization_chain_identity (c : OrdTri P →₀ ℤ) :
    c - ordStrictInclusion2 (normalizeOrdChain2 c) =
    ordNormalizationHomotopy1 (bdry2 (orderCx P) c) +
      ordBoundary3 (ordNormalizationHomotopy2 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp
    rw [add_sub_add_comm, hc, hd]
    abel
  | single t n =>
    rw [bdry2_single]
    have h := congrArg (fun x : OrdTri P →₀ ℤ => n • x)
      (ordNormalization_triangle_identity t)
    simpa [ordStrictInclusion2, ordNormalizationHomotopy2, smul_sub,
      smul_add, Finsupp.smul_single] using h

/-- A cellular two-cycle differs from its normalized image by an explicit three-boundary
in the full order nerve. No identification of the truncated second homotopy groups is used. -/
theorem ordNormalization_cycle_boundary (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    c - ordStrictInclusion2 (normalizeOrdChain2 c) =
      ordBoundary3 (ordNormalizationHomotopy2 c) := by
  rw [ordNormalization_chain_identity, hc, map_zero, zero_add]

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def ordNerveChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun e => FreeAbelianGroup.of [e.1.1, e.1.2])

def ordNerveChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun t => FreeAbelianGroup.of [t.1.1, t.1.2.1, t.1.2.2])

def ordNerveChain3 : (OrdTet P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun t =>
    FreeAbelianGroup.of [t.1.1, t.1.2.1, t.1.2.2.1, t.1.2.2.2])

/-- A triangle's attaching edge chain is its alternating simplicial boundary. -/
theorem ordNerveChain1_bdry2 (c : OrdTri P →₀ ℤ) :
    ordNerveChain1 (bdry2 (orderCx P) c) = Nerve.bdry (ordNerveChain2 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    rw [bdry2_single]
    simp [ordNerveChain1, ordNerveChain2, pathChain, orderCx, Nerve.bdryOn,
      Nerve.consMap_of, smul_add, smul_sub]
    abel

/-- The cellular three-boundary is exactly the full nerve three-boundary. -/
theorem ordNerveChain2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    ordNerveChain2 (ordBoundary3 c) = Nerve.bdry (ordNerveChain3 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    simp [ordNerveChain2, ordNerveChain3, ordBoundary3, ordTetBoundary,
      Nerve.bdryOn, Nerve.consMap_of, smul_add, smul_sub]
    abel

/-- The normalized image of every weak two-cycle represents the same full-nerve class. -/
theorem ordNerve_normalization_cycle (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    ordNerveChain2 c - ordNerveChain2 (ordStrictInclusion2 (normalizeOrdChain2 c)) =
      Nerve.bdry (ordNerveChain3 (ordNormalizationHomotopy2 c)) := by
  rw [← map_sub, ordNormalization_cycle_boundary c hc, ordNerveChain2_ordBoundary3]

end FiniteChains.Comb
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u} [PartialOrder P]

def decodeOrdEdgeList : List P → OrdEdge P →₀ ℤ
  | [a, b] => by
    classical
    exact if h : a ≤ b then Finsupp.single ⟨(a, b), h⟩ 1 else 0
  | _ => 0

def decodeOrdNerve1 : Nerve.Ch P →+ (OrdEdge P →₀ ℤ) := lift decodeOrdEdgeList

@[simp] theorem decodeOrdNerve1_of (l : List P) :
    decodeOrdNerve1 (of l) = decodeOrdEdgeList l := lift_apply_of _ _

theorem decodeOrdNerve1_encode (c : OrdEdge P →₀ ℤ) :
    decodeOrdNerve1 (ordNerveChain1 c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n => simp [ordNerveChain1, decodeOrdEdgeList, e.2]

theorem ordNerveChain1_injective : Function.Injective (ordNerveChain1 (P := P)) := by
  intro c d h
  simpa only [decodeOrdNerve1_encode] using congrArg decodeOrdNerve1 h

def decodeOrdTriList : List P → OrdTri P →₀ ℤ
  | [a, b, c] => by
    classical
    exact if h : a ≤ b ∧ b ≤ c then Finsupp.single ⟨(a, b, c), h⟩ 1 else 0
  | _ => 0

def decodeOrdTetList : List P → OrdTet P →₀ ℤ
  | [a, b, c, d] => by
    classical
    exact if h : a ≤ b ∧ b ≤ c ∧ c ≤ d then Finsupp.single ⟨(a, b, c, d), h⟩ 1 else 0
  | _ => 0

def decodeOrdNerve2 : Nerve.Ch P →+ (OrdTri P →₀ ℤ) := lift decodeOrdTriList
def decodeOrdNerve3 : Nerve.Ch P →+ (OrdTet P →₀ ℤ) := lift decodeOrdTetList

@[simp] theorem decodeOrdNerve2_of (l : List P) :
    decodeOrdNerve2 (of l) = decodeOrdTriList l := lift_apply_of _ _
@[simp] theorem decodeOrdNerve3_of (l : List P) :
    decodeOrdNerve3 (of l) = decodeOrdTetList l := lift_apply_of _ _

/-- Cellular coordinates are recovered exactly, including every integer coefficient. -/
theorem decodeOrdNerve2_encode (c : OrdTri P →₀ ℤ) :
    decodeOrdNerve2 (ordNerveChain2 c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    simp [ordNerveChain2, decodeOrdTriList, t.2.1, t.2.2]

/-- On an increasing basis list, decoding followed by encoding retains its degree-two part. -/
theorem ordNerveChain2_decode_of {l : List P} (hl : List.IsChain (· ≤ ·) l) :
    ordNerveChain2 (decodeOrdTriList l) = Nerve.lengthProjection 3 (of l) := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdTriList]
    | cons b l =>
      cases l with
      | nil => simp [decodeOrdTriList]
      | cons c l =>
        cases l with
        | nil =>
          have h : a ≤ b ∧ b ≤ c := by simpa [List.isChain_cons] using hl
          simp [decodeOrdTriList, h, ordNerveChain2]
        | cons d l => simp [decodeOrdTriList]

/-- Every increasing homogeneous degree-two nerve chain is an actual cellular two-chain. -/
theorem ordNerveChain2_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain2 (decodeOrdNerve2 c) = Nerve.lengthProjection 3 c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve2_of]
    exact ordNerveChain2_decode_of hl
  | zero => simp
  | add x y _ _ hx hy => simp_all
  | neg x _ hx => simp_all


theorem ordNerveChain3_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain3 (decodeOrdNerve3 c) = Nerve.lengthProjection 4 c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve3_of]
    exact (by
      cases l with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => rfl
        | cons b l =>
          cases l with
          | nil => simp [decodeOrdTetList]
          | cons c l =>
            cases l with
            | nil => simp [decodeOrdTetList]
            | cons d l =>
              cases l with
              | nil =>
                have h : a ≤ b ∧ b ≤ c ∧ c ≤ d := by simpa [List.isChain_cons] using hl
                simp [decodeOrdTetList, h, ordNerveChain3]
              | cons e l => simp [decodeOrdTetList])
  | zero => simp
  | add x y _ _ hx hy => simp_all
  | neg x _ hx => simp_all

theorem ordNerveChain2_injective : Function.Injective (ordNerveChain2 (P := P)) := by
  intro c d h
  simpa only [decodeOrdNerve2_encode] using congrArg decodeOrdNerve2 h

/-- Zero nerve boundary is equivalent to the actual zero cellular boundary. -/
theorem ordNerveChain2_cycle_iff (c : OrdTri P →₀ ℤ) :
    Nerve.bdry (ordNerveChain2 c) = 0 ↔ bdry2 (orderCx P) c = 0 := by
  rw [← ordNerveChain1_bdry2]
  exact ⟨fun h => ordNerveChain1_injective (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

theorem ordNerveChain2_lengthProjection (c : OrdTri P →₀ ℤ) :
    Nerve.lengthProjection 3 (ordNerveChain2 c) = ordNerveChain2 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n => simp [ordNerveChain2]

theorem ordNerveChain2_mem_inc (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using AddSubgroup.add_mem _ hc hd
  | single t n =>
    simp only [ordNerveChain2, Finsupp.linearCombination_single]
    apply AddSubgroup.zsmul_mem
    apply Nerve.of_mem_inc
    simpa [List.isChain_cons] using t.2

/-- Triangles lying in a subposet, with all three vertices required to lie in it. -/
def ordTriOn (A : P → Prop) : Set (OrdTri P) :=
  {t | A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2}


theorem decodeOrdNerve2_supported {A : P → Prop} {c : Nerve.Ch P}
    (hc : c ∈ Nerve.IncOn A) :
    decodeOrdNerve2 c ∈ Finsupp.supported ℤ ℤ (ordTriOn A) := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve2_of]
    exact (by
      cases l with
      | nil => simp [decodeOrdTriList]
      | cons a l =>
        cases l with
        | nil => simp [decodeOrdTriList]
        | cons b l =>
          cases l with
          | nil => simp [decodeOrdTriList]
          | cons c l =>
            cases l with
            | nil =>
              have h : a ≤ b ∧ b ≤ c := by simpa [List.isChain_cons] using (hl.1)
              simp only [decodeOrdTriList, dif_pos h]
              exact Finsupp.single_mem_supported ℤ 1
                ⟨(hl.2) a (by simp), (hl.2) b (by simp), (hl.2) c (by simp)⟩
            | cons d l => simp [decodeOrdTriList])
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | neg x _ hx => simp_all

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The three-cell map of the full nerve, without truncating at the two-skeleton. -/
def ordTetMap (f : P → Q) (hf : Monotone f) (t : OrdTet P) : OrdTet Q :=
  ⟨(f t.1.1, f t.1.2.1, f t.1.2.2.1, f t.1.2.2.2),
    hf t.2.1, hf t.2.2.1, hf t.2.2.2⟩

namespace IsPosetCover
variable {f : P → Q} (hf : IsPosetCover f)

/-- Every full-nerve three-cell lifts uniquely from a specified lift of its first vertex. -/
theorem existsUnique_tetLift (s : OrdTet Q) (a : P) (ha : f a = s.1.1) :
    ∃! t : OrdTet P, t.1.1 = a ∧ ordTetMap f hf.mono t = s := by
  obtain ⟨b, ⟨hab, hfb⟩, -⟩ := hf.up a s.1.2.1 (by rw [ha]; exact s.2.1)
  obtain ⟨c, ⟨hbc, hfc⟩, -⟩ := hf.up b s.1.2.2.1 (by rw [hfb]; exact s.2.2.1)
  obtain ⟨d, ⟨hcd, hfd⟩, -⟩ := hf.up c s.1.2.2.2 (by rw [hfc]; exact s.2.2.2)
  refine ⟨⟨(a, b, c, d), hab, hbc, hcd⟩, ⟨rfl, ?_⟩, ?_⟩
  · exact Subtype.ext (Prod.ext ha (Prod.ext hfb (Prod.ext hfc hfd)))
  · intro t ht
    have hb  := hf.up_inj (by rw [← ht.1]; exact t.2.1) hab
      ((congrArg (fun s : OrdTet Q => s.1.2.1) ht.2).trans hfb.symm)
    have hc  := hf.up_inj
      (by rw [← ht.1]; exact t.2.1.trans t.2.2.1) (hab.trans hbc)
      ((congrArg (fun s : OrdTet Q => s.1.2.2.1) ht.2).trans hfc.symm)
    have hd  := hf.up_inj
      (by rw [← ht.1]; exact (t.2.1.trans t.2.2.1).trans t.2.2.2)
      ((hab.trans hbc).trans hcd)
      ((congrArg (fun s : OrdTet Q => s.1.2.2.2) ht.2).trans hfd.symm)
    exact Subtype.ext (Prod.ext ht.1 (Prod.ext hb (Prod.ext hc hd)))

end IsPosetCover

/-- The full-nerve three-cell map commutes with the actual cellular three-boundary. -/
theorem ordTetMap_boundary (f : P → Q) (hf : Monotone f) (t : OrdTet P) :
    Finsupp.mapDomain (orderCxMap f hf).onF (ordTetBoundary t) =
      ordTetBoundary (ordTetMap f hf t) := by
  have hsub (x y : OrdTri P →₀ ℤ) :
      Finsupp.mapDomain (orderCxMap f hf).onF (x - y) =
        Finsupp.mapDomain (orderCxMap f hf).onF x -
          Finsupp.mapDomain (orderCxMap f hf).onF y :=
    (Finsupp.lmapDomain ℤ ℤ (orderCxMap f hf).onF).map_sub x y
  simp only [ordTetBoundary, hsub, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem ordNerveChain2_chain2 (f : P → Q) (hf : Monotone f) (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 (chain2 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain2 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single t n =>
      change ordNerveChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
        (Finsupp.single t n)) = _
      rw [Finsupp.mapDomain_single]
      simp [ordNerveChain2, Nerve.cmap_of, orderCxMap]

/-- The full cellular three-boundary is natural under actual monotone maps. -/
theorem chain2_ordBoundary3 (f : P → Q) (hf : Monotone f) (c : OrdTet P →₀ ℤ) :
    chain2 (orderCxMap f hf) (ordBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (ordTetMap f hf) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
      rw [ordBoundary3, Finsupp.linearCombination_single, map_smul,
        Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single]
      congr 1
      exact ordTetMap_boundary f hf t

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictOrdTet (P : Type u) [PartialOrder P] :=
  {t : P × P × P × P // t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2}

def strictOrdTetBoundary (t : StrictOrdTet P) : StrictOrdTri P →₀ ℤ :=
  Finsupp.single ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩ 1 +
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩ 1

def strictOrdBoundary3 : (StrictOrdTet P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTri P →₀ ℤ) := Finsupp.linearCombination ℤ strictOrdTetBoundary

def normalizeOrdTetrahedron (t : OrdTet P) : StrictOrdTet P →₀ ℤ := by
  classical
  exact if h : t.1.1 < t.1.2.1 ∧ t.1.2.1 < t.1.2.2.1 ∧ t.1.2.2.1 < t.1.2.2.2 then
    Finsupp.single ⟨t.1, h⟩ 1 else 0

def normalizeOrdChain3 : (OrdTet P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTet P →₀ ℤ) := Finsupp.linearCombination ℤ normalizeOrdTetrahedron

/-- Repeated-vertex tetrahedra normalize compatibly with every boundary face. -/
theorem normalizeOrdTetBoundary (t : OrdTet P) :
    normalizeOrdChain2 (ordTetBoundary t) =
      strictOrdBoundary3 (normalizeOrdTetrahedron t) := by
  obtain ⟨⟨a, b, c, d⟩, hab, hbc, hcd⟩ := t
  by_cases he1 : a = b
  · subst b
    simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
      normalizeOrdTetrahedron]
  · by_cases he2 : b = c
    · subst c
      simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
        normalizeOrdTetrahedron]
    · by_cases he3 : c = d
      · subst d
        simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
          normalizeOrdTetrahedron]
      · have hab'  := lt_of_le_of_ne hab he1
        have hbc'  := lt_of_le_of_ne hbc he2
        have hcd'  := lt_of_le_of_ne hcd he3
        simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
          normalizeOrdTetrahedron, strictOrdBoundary3, strictOrdTetBoundary,
          hab', hbc', hcd', hab'.trans hbc', hbc'.trans hcd']

/-- Normalization commutes with the full three-boundary on arbitrary finite chains. -/
theorem normalizeOrdChain2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    normalizeOrdChain2 (ordBoundary3 c) = strictOrdBoundary3 (normalizeOrdChain3 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
      rw [ordBoundary3, Finsupp.linearCombination_single, map_smul,
        normalizeOrdTetBoundary, normalizeOrdChain3, Finsupp.linearCombination_single,
        map_smul]

/-- A full weak-nerve boundary normalizes to an actual strict three-boundary. -/
theorem normalized_boundary3 (c : OrdTri P →₀ ℤ)
    (h : ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = normalizeOrdChain2 c := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨normalizeOrdChain3 y, (normalizeOrdChain2_ordBoundary3 y).symm⟩

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem normalizeOrdChain2_support (z : OrdTri P →₀ ℤ) (t : StrictOrdTri P)
    (ht : t ∈ (normalizeOrdChain2 z).support) :
    ∃ a ∈ z.support, a.1 = t.1 := by
  classical
  change t ∈ (∑ a ∈ z.support, z a • normalizeOrdTriangle a).support at ht
  obtain ⟨a, ha, hta⟩ := Finsupp.mem_support_finset_sum t ht
  have hn : normalizeOrdTriangle a t ≠ 0 := by
    intro he
    have h := Finsupp.mem_support_iff.mp hta
    rw [Finsupp.smul_apply, he, smul_zero] at h
    exact h rfl
  unfold normalizeOrdTriangle at hn
  split_ifs at hn with h
  · grind
  · simp at hn

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def normalizedStrictChain2 (f : P → Q) (hf : Monotone f) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdTri Q →₀ ℤ) :=
  normalizeOrdChain2.comp ((chain2 (orderCxMap f hf)).comp (chain2 (strictOrderIncl P)))

/-- Mapping a weak two-chain and then normalizing agrees with first normalizing its
source and applying the actual normalized strict chain map. -/
theorem normalizeOrdChain2_map (f : P → Q) (hf : Monotone f) (z : OrdTri P →₀ ℤ) :
    normalizeOrdChain2 (chain2 (orderCxMap f hf) z) =
      normalizedStrictChain2 f hf (normalizeOrdChain2 z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single t n =>
      obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
      by_cases he1 : a = b
      · subst b
        simp [normalizedStrictChain2, chain2, orderCxMap, normalizeOrdChain2,
          normalizeOrdTriangle]
      · by_cases he2 : b = c
        · subst c
          simp [normalizedStrictChain2, chain2, orderCxMap, normalizeOrdChain2,
            normalizeOrdTriangle]
        · have hab'  := lt_of_le_of_ne hab he1
          have hbc'  := lt_of_le_of_ne hbc he2
          have hs : normalizeOrdChain2
              (Finsupp.single ⟨(a, b, c), hab, hbc⟩ n) =
              Finsupp.single ⟨(a, b, c), hab', hbc'⟩ n := by
            simp [normalizeOrdChain2, normalizeOrdTriangle, hab', hbc']
          rw [hs]
          change normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
              (Finsupp.single ⟨(a, b, c), hab, hbc⟩ n)) =
            normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
              (Finsupp.mapDomain (strictOrderIncl P).onF
                (Finsupp.single ⟨(a, b, c), hab', hbc'⟩ n)))
          simp only [Finsupp.mapDomain_single]
          rfl

theorem normalizedStrictChain2_single (f : P → Q) (hf : Monotone f)
    (t : StrictOrdTri P) (n : ℤ) :
    normalizedStrictChain2 f hf (Finsupp.single t n) =
      n • normalizeOrdTriangle ((orderCxMap f hf).onF ((strictOrderIncl P).onF t)) := by
  change normalizeOrdChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
    (Finsupp.mapDomain (strictOrderIncl P).onF (Finsupp.single t n))) = _
  simp

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def downwardOrdTriangleMap (g : P → P) (hg : Monotone g) : OrdTri P → OrdTri P :=
  fun t => ⟨(g t.1.1, g t.1.2.1, g t.1.2.2), hg t.2.1, hg t.2.2⟩

theorem ordCycle_downward_boundary (g : P → P) (hg : Monotone g)
    (hgle : ∀ x, g x ≤ x) (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c -
      Finsupp.mapDomain (downwardOrdTriangleMap g hg) c := by
  let p := Nerve.prism g id (ordNerveChain2 c)
  have hp  :=
    Nerve.prism_mem_inc hg monotone_id hgle (ordNerveChain2_mem_inc c)
  have hd := (ordNerveChain2_cycle_iff c).mpr hc
  have hb : Nerve.bdry p = ordNerveChain2 c - Nerve.cmap g (ordNerveChain2 c) := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry g id (ordNerveChain2 c)
  let b := Nerve.lengthProjection 4 p
  have hbi : b ∈ Nerve.Inc P := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 4 b = b := Nerve.lengthProjection_idempotent _ _
  have hbdry : Nerve.bdry b = ordNerveChain2 c -
      Nerve.lengthProjection 3 (Nerve.cmap g (ordNerveChain2 c)) := by
    dsimp only [b]
    rw [← Nerve.lengthProjection_bdry, hb, map_sub, ordNerveChain2_lengthProjection]
  refine ⟨decodeOrdNerve3 b, ?_⟩
  apply ordNerveChain2_injective
  rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hbi, hdeg, map_sub, hbdry]
  rw [← ordNerveChain2_chain2 g hg, ordNerveChain2_lengthProjection]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem normalizedStrictChain2_zero_of_comparable_equal (g : P → P) (hg : Monotone g)
    (he : ∀ {a b : P}, a ≤ b → g a = g b) (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 g hg c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => simp_all
  | single t n =>
    rw [normalizedStrictChain2_single]
    have ht  := he t.2.1.le
    simp [normalizeOrdTriangle, orderCxMap, strictOrderIncl, ht]

/-- A downward monotone map that identifies comparable vertices gives genuine finite
strict three-fillings of all strict two-cycles, even when the poset is disconnected. -/
theorem strict_cycle_boundary_of_downward_collapse (g : P → P) (hg : Monotone g)
    (hle : ∀ x, g x ≤ x) (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c := by
  let w := chain2 (strictOrderIncl P) c
  have hw : bdry2 (orderCx P) w = 0 := by
    rw [bdry2_chain2, hc, map_zero]
  obtain ⟨y, hy⟩ := ordCycle_downward_boundary g hg hle w hw
  have hn : normalizeOrdChain2 w = c := normalizeOrdChain2_inclusion c
  have hz : normalizeOrdChain2 (Finsupp.mapDomain (downwardOrdTriangleMap g hg) w) = 0 := by
    exact normalizedStrictChain2_zero_of_comparable_equal g hg he c
  have h := congrArg normalizeOrdChain2 hy
  rw [normalizeOrdChain2_ordBoundary3, map_sub, hn, hz, sub_zero] at h
  exact ⟨normalizeOrdChain3 y, h⟩

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem strict_cycle_comparable_boundary (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgh : ∀ x, g x ≤ h x)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ,
      strictOrdBoundary3 y = normalizedStrictChain2 h hh c -
        normalizedStrictChain2 g hg c := by
  let w := chain2 (strictOrderIncl P) c
  have hw : bdry2 (orderCx P) w = 0 := by
    rw [bdry2_chain2, hc, map_zero]
  let p := Nerve.prism g h (ordNerveChain2 w)
  have hp  :=
    Nerve.prism_mem_inc hg hh hgh (ordNerveChain2_mem_inc w)
  have hd := (ordNerveChain2_cycle_iff w).mpr hw
  have hb : Nerve.bdry p = Nerve.cmap h (ordNerveChain2 w) -
      Nerve.cmap g (ordNerveChain2 w) := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry g h (ordNerveChain2 w)
  let b := Nerve.lengthProjection 4 p
  have hbi : b ∈ Nerve.Inc P := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 4 b = b := Nerve.lengthProjection_idempotent _ _
  have hy : ordBoundary3 (decodeOrdNerve3 b) =
      chain2 (orderCxMap h hh) w - chain2 (orderCxMap g hg) w := by
    apply ordNerveChain2_injective
    rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hbi, hdeg, map_sub]
    dsimp only [b]
    rw [← Nerve.lengthProjection_bdry, hb, map_sub,
      ← ordNerveChain2_chain2 h hh, ← ordNerveChain2_chain2 g hg,
      ordNerveChain2_lengthProjection, ordNerveChain2_lengthProjection]
  refine ⟨normalizeOrdChain3 (decodeOrdNerve3 b), ?_⟩
  have hn := congrArg normalizeOrdChain2 hy
  rw [normalizeOrdChain2_ordBoundary3, map_sub] at hn
  exact hn

theorem normalizedStrictChain2_id (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 id monotone_id c = c := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => simp_all
  | single t n =>
    rw [normalizedStrictChain2_single]
    simp [normalizeOrdTriangle, orderCxMap, strictOrderIncl, t.2.1, t.2.2]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u

instance cylP_partialOrder {X S : Type u} [PartialOrder X] [PartialOrder S]
    (a : S →o X) : PartialOrder (CylP a) :=
  { (inferInstance : Preorder (CylP a)) with
    le_antisymm := by
      intro p q hpq hqp
      cases p <;> cases q
      · exact congrArg Sum.inl (le_antisymm hpq hqp)
      · exact False.elim hpq
      · exact False.elim hqp
      · exact congrArg Sum.inr (le_antisymm hpq hqp) }

instance coneAdj_partialOrder {P T : Type u} [PartialOrder P] (S : T → P → Prop) :
    PartialOrder (ConeAdj S) :=
  { (inferInstance : Preorder (ConeAdj S)) with
    le_antisymm := by
      intro p q hpq hqp
      cases p <;> cases q
      · exact congrArg Sum.inl (le_antisymm hpq hqp)
      · exact False.elim hqp
      · exact False.elim hpq
      · exact congrArg Sum.inr hpq }

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

instance rose_partialOrder : PartialOrder (Rose α) :=
  { (inferInstance : Preorder (Rose α)) with
    le_antisymm := by
      intro x y hxy hyx
      change Rose.le x y at hxy
      change Rose.le y x at hyx
      cases x <;> cases y <;> simp_all [Rose.le] }

instance tCirc_partialOrder (w : J → List (α × Bool)) : PartialOrder (TCirc w) :=
  { (inferInstance : Preorder (TCirc w)) with
    le_antisymm := by
      intro x y hxy hyx
      rcases hxy with h | h
      · exact h
      rcases hyx with h' | h'
      · exact h'.symm
      have hl := TCirc.lt_left_tag w h
      have hr := TCirc.lt_right_tag w h'
      rcases hl with hl | hl <;> rcases hr with hr | hr <;> simp_all }

instance presPos_partialOrder (w : J → List (α × Bool)) : PartialOrder (PresPos w) :=
  inferInstanceAs (PartialOrder (ConeAdj (circSet w)))

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Valid attaching-circle positions are downward closed in the actual circle order. -/
theorem tCirc_valid_down {x y : TCirc w} (hxy : x ≤ y)
    (hy : y.2.1 < (w y.1).length) :
    x.1 = y.1 ∧ x.2.1 < (w y.1).length := by
  rcases hxy with rfl | hxy
  · simp_all
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', htags⟩ := hxy
  subst j'
  refine ⟨rfl, ?_⟩
  rcases htags with ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
  · simp_all
  · simp_all
  · simp_all
  · rw [hk]
    exact Nat.mod_lt _ (by omega)

/-- The strict old interval below a relator apex consists exactly of its genuine
valid attaching-circle cells; no rose cell lies in that interval. -/
theorem presPos_le_apex_iff (j : J) (p : PresPos w) :
    p ≤ apexOf w j ↔ p = apexOf w j ∨
      ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    cases p with
    | inr j' => exact Or.inl (congrArg Sum.inr h)
    | inl p =>
      obtain ⟨r, ⟨k, t, hk, rfl⟩, hpr⟩ := h
      cases p with
      | inl r => exact hpr.elim
      | inr c =>
        have hc := tCirc_valid_down w hpr hk
        obtain ⟨j', k', t'⟩ := c
        obtain ⟨rfl, hc⟩ := hc
        exact Or.inr ⟨k', t', hc, rfl⟩
  · rintro (rfl | ⟨k, t, hk, rfl⟩)
    · exact le_refl _
    · exact iCirc_le_apexOf w t hk

theorem presPos_lt_apex_iff (j : J) (p : PresPos w) :
    p < apexOf w j ↔ ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    rcases (presPos_le_apex_iff w j p).mp h.le with he | he
    · exact ((ne_of_lt h) he).elim
    · exact he
  · rintro ⟨k, t, hk, rfl⟩
    apply lt_of_le_of_ne (iCirc_le_apexOf w t hk)
    exact Sum.inl_ne_inr

theorem iCirc_strictMono : StrictMono (iCirc w) := by
  intro x y h
  apply lt_of_le_of_ne ((iCirc_monotone w) h.le)
  intro he
  exact (ne_of_lt h) (Sum.inr.inj (Sum.inl.inj he))

/-- The only strict circle edges are the four incidences for a valid letter position. -/
theorem tCirc_strict_edge_cases (e : StrictOrdEdge (TCirc w)) :
    ∃ j k, k < (w j).length ∧
      (e.1 = (TCirc.pt w j k CPos.cor, TCirc.pt w j k CPos.cedgL) ∨
       e.1 = (TCirc.pt w j k CPos.cmid, TCirc.pt w j k CPos.cedgL) ∨
       e.1 = (TCirc.pt w j k CPos.cmid, TCirc.pt w j k CPos.cedgR) ∨
       e.1 = (TCirc.pt w j (TCirc.csucc w j k) CPos.cor, TCirc.pt w j k CPos.cedgR)) := by
  rcases e with ⟨⟨⟨j, k, s⟩, ⟨j', k', s'⟩⟩, h⟩
  have hn := ne_of_lt h
  have hl := h.le
  rcases hl with he | hl
  · grind
  obtain ⟨hj, hk', htags⟩ := hl
  subst j'
  refine ⟨j, k', hk', ?_⟩
  rcases htags with ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def RelatorCircle := {x : TCirc w // x.1 = j ∧ x.2.1 < (w j).length}
instance : PartialOrder (RelatorCircle w j) := Subtype.partialOrder _

def relatorCircleToBelow (x : RelatorCircle w j) : StrictBelow (apexOf w j) :=
  ⟨iCirc w x.1, (presPos_lt_apex_iff w j _).mpr
    ⟨x.1.2.1, x.1.2.2, x.2.2, by
      rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
      change j' = j at hj
      subst j'
      rfl⟩⟩


theorem relatorCircleToBelow_surjective : Function.Surjective (relatorCircleToBelow w j) := by
  intro p
  obtain ⟨k, t, hk, he⟩ := (presPos_lt_apex_iff w j p.1).mp p.2
  refine ⟨⟨TCirc.pt w j k t, rfl, hk⟩, ?_⟩
  exact Subtype.ext he.symm

/-- The actual lower interval of a relator apex is its valid attaching circle. -/
def relatorCircleOrderIso : RelatorCircle w j ≃o StrictBelow (apexOf w j) where
  toEquiv := Equiv.ofBijective (relatorCircleToBelow w j)
    ⟨(by
      intro a b h
      apply Subtype.ext
      exact Sum.inr.inj (Sum.inl.inj (congrArg Subtype.val h))), relatorCircleToBelow_surjective w j⟩
  map_rel_iff' := by
    intro a b
    change iCirc w a.1 ≤ iCirc w b.1 ↔ a.1 ≤ b.1
    rfl

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem tCirc_strict_of_lt_relation {x y : TCirc w} (h : TCirc.lt w x y) : x < y := by
  apply lt_of_le_of_ne (Or.inr h)
  intro he
  have hl := TCirc.lt_left_tag w h
  have hr := TCirc.lt_right_tag w h
  grind

def relatorCirclePoint (k : Fin (w j).length) (s : CPos) : RelatorCircle w j :=
  ⟨TCirc.pt w j k s, rfl, k.isLt⟩

def relatorCircleNext (k : Fin (w j).length) : Fin (w j).length :=
  ⟨TCirc.csucc w j k, Nat.mod_lt _ (by have := k.isLt; omega)⟩

def relatorCircleEdge0 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cor, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩

def relatorCircleEdge1 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩⟩

def relatorCircleEdge2 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdge3 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor,
      relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdgeForget (e : StrictOrdEdge (RelatorCircle w j)) : StrictOrdEdge (TCirc w) :=
  ⟨(e.1.1.1, e.1.2.1), e.2⟩

theorem relatorCircleEdgeForget_injective : Function.Injective (relatorCircleEdgeForget w j) := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun e : StrictOrdEdge (TCirc w) => e.1.1) h
  · exact congrArg (fun e : StrictOrdEdge (TCirc w) => e.1.2) h

/-- The four explicit incidences exhaust the actual valid attaching-circle edges. -/
theorem relatorCircle_edge_cases (e : StrictOrdEdge (RelatorCircle w j)) :
    ∃ k : Fin (w j).length, e = relatorCircleEdge0 w j k ∨
      e = relatorCircleEdge1 w j k ∨ e = relatorCircleEdge2 w j k ∨
      e = relatorCircleEdge3 w j k := by
  let e' := relatorCircleEdgeForget w j e
  obtain ⟨j', k, hk, he⟩ := tCirc_strict_edge_cases w e'
  have hj' : e'.1.2.1 = j' := by
    rcases he with he | he | he | he <;> rw [he] <;> rfl
  have hj  := hj'.symm.trans e.1.2.2.1
  rw [hj] at hk he
  refine ⟨⟨k, hk⟩, ?_⟩
  rcases he with he | he | he | he
  · left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; right; left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; right; right
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he




end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem relatorCircle_boundary_left
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgL) =
        c (relatorCircleEdge0 w j k) + c (relatorCircleEdge1 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

theorem relatorCircle_boundary_mid
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cmid) =
        -c (relatorCircleEdge1 w j k) - c (relatorCircleEdge2 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

theorem relatorCircle_boundary_right
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgR) =
        c (relatorCircleEdge2 w j k) + c (relatorCircleEdge3 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
    all_goals
      by_cases h : l = k
      · subst l
        simp
      · omega

theorem relatorCircleNext_injective : Function.Injective (relatorCircleNext w j) := by
  intro k l he
  have he' := congrArg Fin.val he
  change (k.val + 1) % (w j).length = (l.val + 1) % (w j).length at he'
  have hk := k.isLt
  have hl := l.isLt
  ext
  by_cases hks : k.val + 1 < (w j).length <;>
    by_cases hls : l.val + 1 < (w j).length
  · rw [Nat.mod_eq_of_lt hks, Nat.mod_eq_of_lt hls] at he'
    omega
  · have hs : l.val + 1 = (w j).length := by omega
    rw [Nat.mod_eq_of_lt hks, hs, Nat.mod_self] at he'
    omega
  · have hs : k.val + 1 = (w j).length := by omega
    rw [hs, Nat.mod_self, Nat.mod_eq_of_lt hls] at he'
    omega
  · omega

theorem relatorCircle_boundary_corner
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
        -c (relatorCircleEdge0 w j (relatorCircleNext w j k)) -
          c (relatorCircleEdge3 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
    by_cases h : l = k
    · subst l
      simp
    · have hn : (relatorCircleNext w j l).val ≠ (relatorCircleNext w j k).val := by
        intro he
        exact h (relatorCircleNext_injective w j (Fin.ext he))
      simp [hn]

theorem relatorCircle_cycle_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (k : Fin (w j).length) :
    c (relatorCircleEdge1 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge2 w j k) = c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge3 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge0 w j (relatorCircleNext w j k)) =
      c (relatorCircleEdge0 w j k) := by
  have hl := relatorCircle_boundary_left w j c k
  have hm := relatorCircle_boundary_mid w j c k
  have hr := relatorCircle_boundary_right w j c k
  have hk := relatorCircle_boundary_corner w j c k
  grind

theorem relatorCircle_successor_invariant_constant
    (a : Fin (w j).length → ℤ)
    (ha : ∀ k, a (relatorCircleNext w j k) = a k)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    a k = a ⟨0, hpos⟩ := by
  have hi : ∀ n hn, a ⟨n, hn⟩ = a ⟨0, hpos⟩ := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn
      have hp : n < (w j).length := by omega
      have hs : relatorCircleNext w j ⟨n, hp⟩ = ⟨n + 1, hn⟩ := by
        ext
        exact Nat.mod_eq_of_lt hn
      rw [← hs, ha]
      exact ih hp
  simp_all


theorem relatorCircle_cycle_all_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    let a := c (relatorCircleEdge0 w j ⟨0, hpos⟩)
    c (relatorCircleEdge0 w j k) = a ∧
    c (relatorCircleEdge1 w j k) = -a ∧
    c (relatorCircleEdge2 w j k) = a ∧
    c (relatorCircleEdge3 w j k) = -a := by
  dsimp only
  have h := relatorCircle_cycle_coefficients w j c hc k
  have h0 := (by
    apply relatorCircle_successor_invariant_constant w j
      (fun l => c (relatorCircleEdge0 w j l)) _ hpos k
    intro l
    exact (relatorCircle_cycle_coefficients w j c hc l).2.2.2)
  exact ⟨h0, h.1.trans (congrArg Neg.neg h0), h.2.1.trans h0,
    h.2.2.1.trans (congrArg Neg.neg h0)⟩

/-- Agreement at one genuine circle edge determines an entire one-cycle. -/
theorem relatorCircle_cycle_ext
    (c d : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) d = 0)
    (hpos : 0 < (w j).length)
    (he : c (relatorCircleEdge0 w j ⟨0, hpos⟩) =
      d (relatorCircleEdge0 w j ⟨0, hpos⟩)) : c = d := by
  ext e
  obtain ⟨k, hk⟩ := relatorCircle_edge_cases w j e
  have hck := relatorCircle_cycle_all_coefficients w j c hc hpos k
  have hdk := relatorCircle_cycle_all_coefficients w j d hd hpos k
  grind

end FiniteChains.PresModel
end

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}}

theorem pathChain_revPath (p : List (X.E × Bool)) :
    pathChain (revPath p) = -pathChain p := by
  induction p with
  | nil => simp
  | cons e p ih =>
    rw [revPath_cons, pathChain_append, ih, pathChain_cons]
    obtain ⟨e, b⟩ := e
    cases b <;> simp [revGerm, pathChain_cons]

/-- An elementary path cancellation has an explicit cellular two-chain witness. -/
theorem Cancels.exists_boundary {p q : List (X.E × Bool)} (h : Cancels X p q) :
    ∃ c : X.F →₀ ℤ, bdry2 X c = pathChain p - pathChain q := by
  rcases h with ⟨l, r, e, rfl, rfl⟩ | ⟨l, r, f, rfl, rfl⟩
  · refine ⟨0, ?_⟩
    obtain ⟨e, b⟩ := e
    cases b <;> simp [pathChain_append, pathChain_cons, revGerm]
  · refine ⟨Finsupp.single f 1, ?_⟩
    rw [bdry2_single, one_smul, pathChain_append, pathChain_append, pathChain_append]
    abel

/-- Homotopic paths differ by the boundary of a finitely supported integral two-chain. -/
theorem Htpy.exists_boundary {a b : X.V} {p q : List (X.E × Bool)}
    (h : Htpy X a b p q) :
    ∃ c : X.F →₀ ℤ, bdry2 X c = pathChain p - pathChain q := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail q r h hstep ih =>
    obtain ⟨c, hc⟩ := ih
    have hs : ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain q - pathChain r := by
      rcases hstep with hs | hs
      · exact hs.2.2.exists_boundary
      · obtain ⟨d, hd⟩ := hs.2.2.exists_boundary
        exact ⟨-d, by rw [map_neg, hd]; abel⟩
    obtain ⟨d, hd⟩ := hs
    refine ⟨c + d, ?_⟩
    rw [map_add, hc, hd]
    abel

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}} (a : X.V) (f : Hom X Y)

/-- Projection of an actual lifted two-chain agrees with the ordinary cellular image. -/
theorem hurewicz_univLift_chain2 (d : (uCover X a).F →₀ ℤ) :
    hurewicz Y (f.onV a) (chain2 (univLift X f a) d) =
      chain2 f (hurewicz X a d) := by
  change Finsupp.mapDomain (univProj Y (f.onV a)).onF
    (Finsupp.mapDomain (univLift X f a).onF d) =
      Finsupp.mapDomain f.onF (Finsupp.mapDomain (univProj X a).onF d)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

/-- A homotopy lifts to a finite chain correction, whose cellular image has the exact boundary. -/
theorem exists_mapped_lifted_homotopy_chain {v : UV X a} {p q : List (X.E × Bool)} {b : X.V}
    (hp : IsPath X.src X.tgt p (endV v) b) (h : Htpy X (endV v) b p q) :
    ∃ d : (uCover X a).F →₀ ℤ,
      bdry2 (uCover Y (f.onV a)) (chain2 (univLift X f a) d) =
        pathChain (uLiftPath (mapPath f p) (univLiftV a f v)) -
          pathChain (uLiftPath (mapPath f q) (univLiftV a f v)) := by
  obtain ⟨d, hd⟩ := (htpy_uLiftPath hp h).exists_boundary
  refine ⟨d, ?_⟩
  rw [bdry2_chain2, hd, map_sub]
  have key r (hr : IsPath X.src X.tgt r (endV v) b) :
      chain1 (univLift X f a) (pathChain (uLiftPath r v)) =
        pathChain (uLiftPath (mapPath f r) (univLiftV a f v)) := by
    change Finsupp.mapDomain (univLift X f a).onE (pathChain _) = _
    rw [← pathChain_map]
    exact congrArg pathChain (uLiftPath_univLiftV a f r v b hr).symm
  rw [key p hp, key q (h.isPath hp)]

end FiniteChains.Comb
end

namespace FiniteChains.PresModel
universe u
variable {α J : Type u}

/-- Nonempty attaching-word representatives, using a cancelling pair. -/
def presNonemptyWords (ρ : J → FreeGroup α) (a : α) (j : J) :
    List (α × Bool) := presWords ρ j ++ [(a, true), (a, false)]

theorem presNonemptyWords_ne_nil (ρ : J → FreeGroup α) (a : α) (j : J) :
    presNonemptyWords ρ a j ≠ [] := by
  simp [presNonemptyWords]

theorem mk_presNonemptyWords (ρ : J → FreeGroup α) (a : α) (j : J) :
    FreeGroup.mk (presNonemptyWords ρ a j) = ρ j := by
  have hc : FreeGroup.mk [(a, true), (a, false)] = 1 := by
    change FreeGroup.of a * (FreeGroup.of a)⁻¹ = 1
    exact mul_inv_cancel _
  rw [presNonemptyWords, ← FreeGroup.mul_mk, hc, mul_one, mk_presWords]

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

variable {A X Y Z : Complex2.{u}}

/-! ### Reachable cells -/

/-- `Reach X x₀ v` : the vertex `v` is joined to `x₀` by an edge path. -/
def Reach (X : Complex2.{u}) (x₀ v : X.V) : Prop := ∃ p, IsPath X.src X.tgt p x₀ v

theorem reach_self (X : Complex2.{u}) (x₀ : X.V) : Reach X x₀ x₀ := ⟨[], rfl⟩

theorem Reach.trans_path {x₀ a b : X.V} (h : Reach X x₀ a) {p : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p a b) : Reach X x₀ b := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q ++ p, hq.append hp⟩


theorem Reach.tgt_of_src {x₀ : X.V} {e : X.E} (h : Reach X x₀ (X.src e)) :
    Reach X x₀ (X.tgt e) :=
  h.trans_path (p := [(e, true)]) ⟨rfl, rfl⟩


theorem Reach.src_of_germSrc {x₀ : X.V} {eb : X.E × Bool}
    (h : Reach X x₀ (germSrc X.src X.tgt eb)) : Reach X x₀ (X.src eb.1) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => exact h
  | false => exact (h.trans_path (p := [(e, false)]) ⟨rfl, rfl⟩)

theorem Reach.germSrc_of_src {x₀ : X.V} {eb : X.E × Bool}
    (h : Reach X x₀ (X.src eb.1)) : Reach X x₀ (germSrc X.src X.tgt eb) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => exact h
  | false => exact Reach.tgt_of_src h

/-- Every edge of a path issued from a reachable vertex is reachable. -/
theorem reach_of_mem_path {x₀ : X.V} :
    ∀ {l : List (X.E × Bool)} {a b : X.V}, IsPath X.src X.tgt l a b → Reach X x₀ a →
      ∀ eb ∈ l, Reach X x₀ (X.src eb.1)
  | [], _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | eb :: t, a, b, hl, ha, eb', hm => by
      have ha' : Reach X x₀ (germSrc X.src X.tgt eb) := hl.1 ▸ ha
      have htail : Reach X x₀ (germTgt X.src X.tgt eb) :=
        ha'.trans_path (p := [eb]) ⟨rfl, rfl⟩
      rcases List.mem_cons.mp hm with h | h
      · subst h; exact ha'.src_of_germSrc
      · exact reach_of_mem_path hl.2 htail eb' h

/-! ### The cells of the component -/

variable (X) in
/-- The vertices of the component of `x₀`. -/
def CV (x₀ : X.V) : Type u := {v : X.V // Reach X x₀ v}

variable (X) in
/-- The edges of the component of `x₀`. -/
def CE (x₀ : X.V) : Type u := {e : X.E // Reach X x₀ (X.src e)}

variable (X) in
/-- The two-cells of the component of `x₀`. -/
def CF (x₀ : X.V) : Type u := {f : X.F // Reach X x₀ (X.base f)}

variable {x₀ : X.V}

/-- The initial vertex of an edge of the component. -/
def cSrc (e : CE X x₀) : CV X x₀ := ⟨X.src e.1, e.2⟩

/-- The terminal vertex of an edge of the component. -/
def cTgt (e : CE X x₀) : CV X x₀ := ⟨X.tgt e.1, e.2.tgt_of_src⟩

open Classical in
/-- The list of oriented edges of the component carried by a list of oriented edges of the
ambient complex: unreachable edges are dropped (they never occur in the lists we lift). -/
def liftGerms (X : Complex2.{u}) (x₀ : X.V) (l : List (X.E × Bool)) :
    List (CE X x₀ × Bool) :=
  l.filterMap fun eb => if h : Reach X x₀ (X.src eb.1) then some (⟨eb.1, h⟩, eb.2) else none

@[simp] theorem liftGerms_nil (X : Complex2.{u}) (x₀ : X.V) : liftGerms X x₀ [] = [] := rfl

@[simp] theorem liftGerms_append (X : Complex2.{u}) (x₀ : X.V) (l l' : List (X.E × Bool)) :
    liftGerms X x₀ (l ++ l') = liftGerms X x₀ l ++ liftGerms X x₀ l' := by
  simp [liftGerms, List.filterMap_append]

theorem liftGerms_cons {eb : X.E × Bool} (h : Reach X x₀ (X.src eb.1))
    (l : List (X.E × Bool)) :
    liftGerms X x₀ (eb :: l) = ((⟨eb.1, h⟩ : CE X x₀), eb.2) :: liftGerms X x₀ l := by
  simp [liftGerms, h]

/-- The forgetful map on oriented edges of the component. -/
def cForget (eb : CE X x₀ × Bool) : X.E × Bool := (eb.1.1, eb.2)

@[simp] theorem liftGerms_map_cForget (L : List (CE X x₀ × Bool)) :
    liftGerms X x₀ (L.map cForget) = L := by
  induction L with
  | nil => rfl
  | cons eb L ih =>
      rw [List.map_cons, liftGerms_cons eb.1.2, ih]
      rfl

theorem map_cForget_liftGerms {l : List (X.E × Bool)}
    (h : ∀ eb ∈ l, Reach X x₀ (X.src eb.1)) :
    (liftGerms X x₀ l).map cForget = l := by
  induction l with
  | nil => rfl
  | cons eb l ih =>
      rw [liftGerms_cons (h eb List.mem_cons_self), List.map_cons,
        ih fun e he => h e (List.mem_cons_of_mem _ he)]
      rfl

@[simp] theorem cGermSrc (eb : CE X x₀ × Bool) :
    germSrc cSrc cTgt eb = ⟨germSrc X.src X.tgt (cForget eb), (eb.1.2).germSrc_of_src⟩ := by
  obtain ⟨e, b⟩ := eb
  cases b <;> rfl

@[simp] theorem cGermTgt (eb : CE X x₀ × Bool) :
    germTgt cSrc cTgt eb = ⟨germTgt X.src X.tgt (cForget eb), by
      obtain ⟨e, b⟩ := eb
      cases b
      · exact e.2
      · exact e.2.tgt_of_src⟩ := by
  obtain ⟨e, b⟩ := eb
  cases b <;> rfl

/-- A path of the ambient complex issued from a reachable vertex lifts to a path of the
component. -/
theorem isPath_liftGerms :
    ∀ {l : List (X.E × Bool)} {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b),
      IsPath X.src X.tgt l a b →
        IsPath (cSrc (X := X) (x₀ := x₀)) cTgt (liftGerms X x₀ l) ⟨a, ha⟩ ⟨b, hb⟩
  | [], a, b, ha, hb, hl => by
      show (⟨a, ha⟩ : CV X x₀) = ⟨b, hb⟩
      exact Subtype.ext hl
  | eb :: t, a, b, ha, hb, hl => by
      have hsrc : Reach X x₀ (X.src eb.1) := (hl.1 ▸ ha).src_of_germSrc
      have htgt : Reach X x₀ (germTgt X.src X.tgt eb) :=
        (hl.1 ▸ ha).trans_path (p := [eb]) ⟨rfl, rfl⟩
      rw [liftGerms_cons hsrc]
      refine ⟨?_, ?_⟩
      · rw [cGermSrc]
        exact Subtype.ext hl.1
      · have := isPath_liftGerms htgt hb hl.2
        rw [cGermTgt]
        exact this

/-! ### The component -/

variable (X) in
/-- **The connected component** of a vertex: the subcomplex of all cells reachable from
`x₀`. -/
def component (x₀ : X.V) : Complex2.{u} where
  V := CV X x₀
  E := CE X x₀
  F := CF X x₀
  src := cSrc
  tgt := cTgt
  base f := ⟨X.base f.1, f.2⟩
  att f := liftGerms X x₀ (X.att f.1)
  att_isLoop f := isPath_liftGerms f.2 f.2 (X.att_isLoop f.1)

@[simp] theorem component_V (x₀ : X.V) : (component X x₀).V = CV X x₀ := rfl
@[simp] theorem component_E (x₀ : X.V) : (component X x₀).E = CE X x₀ := rfl
@[simp] theorem component_F (x₀ : X.V) : (component X x₀).F = CF X x₀ := rfl
@[simp] theorem component_src (x₀ : X.V) : (component X x₀).src = cSrc := rfl
@[simp] theorem component_tgt (x₀ : X.V) : (component X x₀).tgt = cTgt := rfl
@[simp] theorem component_att (x₀ : X.V) (f : CF X x₀) :
    (component X x₀).att f = liftGerms X x₀ (X.att f.1) := rfl

instance (x₀ : X.V) [Finite X.E] : Finite (component X x₀).E := by
  show Finite (CE X x₀); unfold CE; infer_instance

instance (x₀ : X.V) [Finite X.F] : Finite (component X x₀).F := by
  show Finite (CF X x₀); unfold CF; infer_instance

/-- The component is connected. -/
theorem component_isConnected (x₀ : X.V) : IsConnected (component X x₀) := by
  rintro ⟨a, p, hp⟩ ⟨b, q, hq⟩
  refine ⟨liftGerms X x₀ (revPath p ++ q), ?_⟩
  exact isPath_liftGerms _ _ ((isPath_revPath hp).append hq)

variable (X) in
/-- The inclusion of the component into the complex. -/
def componentIncl (x₀ : X.V) : Hom (component X x₀) X where
  onV := Subtype.val
  onE := Subtype.val
  onF := Subtype.val
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    refine (map_cForget_liftGerms ?_).symm
    exact reach_of_mem_path (X.att_isLoop f.1) f.2

@[simp] theorem componentIncl_onV (x₀ : X.V) (v : (component X x₀).V) :
    (componentIncl X x₀).onV v = v.1 := rfl

@[simp] theorem componentIncl_onE (x₀ : X.V) (e : (component X x₀).E) :
    (componentIncl X x₀).onE e = e.1 := rfl

@[simp] theorem componentIncl_onF (x₀ : X.V) (f : (component X x₀).F) :
    (componentIncl X x₀).onF f = f.1 := rfl

theorem componentIncl_injective_onF (x₀ : X.V) :
    Function.Injective (componentIncl X x₀).onF := fun _ _ h => Subtype.ext h

/-! ### Corestriction of a cellular map to a component -/

/-- Two cellular maps agreeing on cells of every dimension are equal. -/
theorem Hom.ext' {f g : Hom X Y} (hV : f.onV = g.onV) (hE : f.onE = g.onE)
    (hF : f.onF = g.onF) : f = g := by
  cases f; cases g; cases hV; cases hE; cases hF; rfl

/-! ### Homotopies take place inside the component -/

/-- An elementary homotopy of the ambient complex between paths issued from a reachable
vertex lifts to the component. -/
theorem step_liftGerms {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b)
    {l l' : List (X.E × Bool)} (hstep : Step X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  obtain ⟨hl, hl', hc⟩ := hstep
  have hPl  := isPath_liftGerms ha hb hl
  have hPl'  := isPath_liftGerms ha hb hl'
  rcases hc with ⟨p, q, eb, hlEq, hl'Eq⟩ | ⟨p, q, f, hlEq, hl'Eq⟩
  · have hmem : eb ∈ l := by
      rw [hlEq]; exact List.mem_append_right _ List.mem_cons_self
    have hsrc  := reach_of_mem_path hl ha eb hmem
    refine Htpy.of_step ⟨hPl, hPl', Or.inl ⟨liftGerms X x₀ p, liftGerms X x₀ q,
      (⟨eb.1, hsrc⟩, eb.2), ?_, ?_⟩⟩
    · rw [hlEq, liftGerms_append, liftGerms_cons hsrc,
        liftGerms_cons (eb := revGerm eb) hsrc]
      rfl
    · simp_all
  · by_cases hatt : X.att f = []
    · have : liftGerms X x₀ l = liftGerms X x₀ l' := by
        rw [hlEq, hl'Eq, hatt]
        simp
      rw [this]
      exact Htpy.refl _
    · obtain ⟨eb, t, hsplit⟩ : ∃ eb t, X.att f = eb :: t := by
        cases hx : X.att f with
        | nil => simp_all
        | cons eb t => simp
      have hmem : eb ∈ l := by
        rw [hlEq, hsplit]
        simp
      have hsrc  := reach_of_mem_path hl ha eb hmem
      have hbase : Reach X x₀ (X.base f) := by
        have hloop := X.att_isLoop f
        rw [hsplit] at hloop
        rw [hloop.1]
        exact hsrc.germSrc_of_src
      refine Htpy.of_step ⟨hPl, hPl', Or.inr ⟨liftGerms X x₀ p, liftGerms X x₀ q,
        ⟨f, hbase⟩, ?_, ?_⟩⟩
      · rw [hlEq, liftGerms_append, liftGerms_append]
        rfl
      · simp_all

/-- **A homotopy of the ambient complex between paths issued from a reachable vertex already
takes place inside the component.** -/
theorem htpy_liftGerms {a b : X.V} (ha : Reach X x₀ a) (hb : Reach X x₀ b)
    {l l' : List (X.E × Bool)} (h : Htpy X a b l l') :
    Htpy (component X x₀) ⟨a, ha⟩ ⟨b, hb⟩ (liftGerms X x₀ l) (liftGerms X x₀ l') := by
  induction h with
  | refl => exact Htpy.refl _
  | tail _ hstep ih =>
      refine (ih).trans ?_
      rcases hstep with hs | hs
      · exact step_liftGerms ha hb hs
      · exact (step_liftGerms ha hb hs).symm

/-! ### The universal cover of a component -/

theorem mapPath_componentIncl (x₀ : X.V) (l : List ((component X x₀).E × Bool)) :
    mapPath (componentIncl X x₀) l = l.map cForget := rfl

/-! ### Functoriality of the lift to universal covers -/


theorem univLiftF_comp (g : Hom Y Z) (f : Hom X Y) (x₀ : X.V) (F : UF X x₀) :
    univLiftF (f.onV x₀) g (univLiftF x₀ f F) = univLiftF x₀ (g.comp f) F :=
  Subtype.ext (Prod.ext (show univLiftV (f.onV x₀) g (univLiftV x₀ f (F.1.1)) = univLiftV x₀ (g.comp f) (F.1.1) by
    induction (F.1.1) using UV.ind with
    | h p =>
        refine Quotient.sound ?_
        have hlist : mapPath g (mapPath f p.1) = mapPath (g.comp f) p.1 := by
          simp only [mapPath, List.map_map]
          rfl
        show Htpy Z (g.onV (f.onV x₀)) _ (mapPath g (mapPath f p.1)) (mapPath (g.comp f) p.1)
        rw [hlist]
        exact Htpy.refl _) rfl)

/-! ### Zero on `π₂` passes to components -/

/-- **Precomposition preserves being zero on `π₂`.** -/
theorem zeroPi2_comp_right (g : Hom Y Z) (f : Hom X Y) (hz : ZeroPi2 g) :
    ZeroPi2 (g.comp f) := by
  intro x₀ c hc
  have hcycle  :=
    mem_pi2_chain2_univLift f hc
  have hg := hz (f.onV x₀) (chain2 (univLift X f x₀) c) hcycle
  have hfun  := fun F => univLiftF_comp g f x₀ F
  have : Finsupp.mapDomain (univLift X (g.comp f) x₀).onF c
      = Finsupp.mapDomain (univLift Y g (f.onV x₀)).onF
        (Finsupp.mapDomain (univLift X f x₀).onF c) := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun F _ => (hfun F).symm
  show Finsupp.mapDomain (univLift X (g.comp f) x₀).onF c = 0
  rw [this]
  exact hg

end Comb
end FiniteChains
end

namespace FiniteChains.Comb
universe u
variable (P : Type u) [Preorder P]

def orderComponentSetoid : Setoid P where
  r := Reach (orderCx P)
  iseqv := ⟨reach_self (orderCx P), fun ⟨p, hp⟩ => ⟨revPath p, isPath_revPath hp⟩,
    fun hab ⟨_, hp⟩ => hab.trans_path hp⟩

def OrderComponent := Quotient (orderComponentSetoid P)

def orderComponentLabel (p : P) : OrderComponent P := Quotient.mk _ p

variable {P}

theorem orderComponentLabel_eq_iff (a b : P) :
    orderComponentLabel P a = orderComponentLabel P b ↔ Reach (orderCx P) a b :=
  Quotient.eq_iff_equiv

theorem orderComponentLabel_eq_of_le {a b : P} (h : a ≤ b) :
    orderComponentLabel P a = orderComponentLabel P b :=
  Quotient.sound ⟨[ordPos h], isPath_ordPos h⟩

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u

 theorem cylP_isConnected {X S : Type u} [Preorder X] [Preorder S]
    (a : S →o X) (hc : IsConnected (orderCx X)) : IsConnected (orderCx (CylP a)) := by
  intro p q
  obtain ⟨l, hl⟩ := hc (cylRetr (X := X) a p) (cylRetr (X := X) a q)
  have hm : Reach (orderCx (CylP a)) (cylCollapse a p) (cylCollapse a q) :=
    ⟨_, isPath_mapPath (orderCxMap (cylIn a) (cylIn_monotone a)) hl⟩
  exact (orderComponentLabel_eq_iff _ _).mp
    ((orderComponentLabel_eq_of_le (le_cylIn_cylRetr (X := X) a p)).trans
      (((orderComponentLabel_eq_iff _ _).mpr hm).trans
        (orderComponentLabel_eq_of_le (le_cylIn_cylRetr (X := X) a q)).symm))

theorem coneAdj_isConnected {P T : Type u} [Preorder P] (S : T → P → Prop)
    (hc : IsConnected (orderCx P)) (hs : ∀ t, ∃ p, S t p) :
    IsConnected (orderCx (ConeAdj S)) := by
  have hv : ∀ v : ConeAdj S, ∃ p : P,
      orderComponentLabel _ v = orderComponentLabel _ (ConeAdj.inc p) := by
    intro v
    cases v with
    | inl p => exact ⟨p, rfl⟩
    | inr t =>
      obtain ⟨p, hp⟩ := hs t
      exact ⟨p, (orderComponentLabel_eq_of_le (ConeAdj.inc_le_apex_of_mem hp)).symm⟩
  intro v w
  obtain ⟨p, hp⟩ := hv v
  obtain ⟨q, hq⟩ := hv w
  obtain ⟨l, hl⟩ := hc p q
  have hm : Reach (orderCx (ConeAdj S)) (ConeAdj.inc (S := S) p) (ConeAdj.inc (S := S) q) :=
    ⟨_, isPath_mapPath (orderCxMap (ConeAdj.inc) (ConeAdj.inc_monotone)) hl⟩
  exact (orderComponentLabel_eq_iff _ _).mp
    (hp.trans (((orderComponentLabel_eq_iff _ _).mpr hm).trans hq.symm))

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}


/-- Nonempty attaching words give connected genuine presentation poset models. -/
theorem presPos_isConnected (w : J → List (α × Bool)) (hw : ∀ j, w j ≠ []) :
    IsConnected (orderCx (PresPos w)) := by
  apply coneAdj_isConnected (circSet w)
    (cylP_isConnected (aHom w) (by
      have h : ∀ x : Rose α, orderComponentLabel _ x = orderComponentLabel _ Rose.base := by
        intro x
        cases x with
        | base => rfl
        | mid i =>
            exact (orderComponentLabel_eq_of_le (Rose.mid_le_edg i false)).trans
              (orderComponentLabel_eq_of_le (Rose.base_le_edg i false)).symm
        | edg i b => exact (orderComponentLabel_eq_of_le (Rose.base_le_edg i b)).symm
      intro x y
      exact (orderComponentLabel_eq_iff _ _).mp ((h x).trans (h y).symm)))
  intro j
  exact ⟨cylOuter (aHom w) (TCirc.pt w j 0 CPos.cor),
    0, CPos.cor, List.length_pos_iff.mpr (hw j), rfl⟩

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace PresModel

open Comb

universe u

variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

include hw

/-- **The marked comparison homomorphism** of the presentation `ρ` with the model built on the
prescribed relator words `w`. -/
def alphaHomW : PresGroup ρ →* Pi1 (orderCx (PresPos w)) (ptBase w) :=
  QuotientGroup.lift _ (alphaFree w) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    have h := alphaFree_relator w j
    rwa [hw j] at h)

@[simp] theorem alphaHomW_mk (x : FreeGroup α) :
    alphaHomW ρ w hw (QuotientGroup.mk x) = alphaFree w x := rfl

theorem alphaHomW_gen (i : α) :
    alphaHomW ρ w hw (QuotientGroup.mk (FreeGroup.of i)) = genClass w i := rfl

/-- The reading homomorphism of the model with values in the presentation group. -/
def readingPresW : Pi1 (orderCx (PresPos w)) (ptBase w) →* PresGroup ρ :=
  reading w (fun i => QuotientGroup.mk (FreeGroup.of i)) (by
    intro j
    have hlift : (FreeGroup.lift fun i : α => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
        = QuotientGroup.mk' (relSub ρ) := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp
    show FreeGroup.lift _ (FreeGroup.mk (w j)) = 1
    rw [hlift, hw j]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure (Set.mem_range.2 ⟨j, rfl⟩)))

theorem readingPresW_alphaHomW (x : PresGroup ρ) :
    readingPresW ρ w hw (alphaHomW ρ w hw x) = x := by
  induction x using QuotientGroup.induction_on with
  | _ y =>
      have key : ((readingPresW ρ w hw).comp (alphaHomW ρ w hw)).comp
          (QuotientGroup.mk' (relSub ρ)) = QuotientGroup.mk' (relSub ρ) := by
        refine FreeGroup.ext_hom _ _ fun i => ?_
        show readingPresW ρ w hw (alphaHomW ρ w hw (QuotientGroup.mk (FreeGroup.of i)))
          = QuotientGroup.mk (FreeGroup.of i)
        rw [alphaHomW_gen]
        exact reading_genClass _ _ _ i
      exact DFunLike.congr_fun key y

/-- **The presentation group embeds into the fundamental group of the model built on the
prescribed relator words.** -/
theorem alphaHomW_injective : Function.Injective (alphaHomW ρ w hw) :=
  Function.LeftInverse.injective (readingPresW_alphaHomW ρ w hw)

end PresModel
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The comparison of the source presentation with the quotient**, over the model built on the
prescribed relator words. -/
def baseToQuotientW {α J : Type u} (ρ : J → FreeGroup α)
    (w : J → List (α × Bool)) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx A →o PresPos w) :
    PresGroup ρ →*
      Comb.Pi1 (orderCx (Qpos A (PresPos w) att)) (qNew (A := A) (att := att) (ptBase w)) :=
  (Comb.pi1Map (orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone)
      (ptBase w)).comp (alphaHomW ρ w hw)

/-- **The comparison is injective.** -/
theorem baseToQuotientW_injective {α J : Type u} (ρ : J → FreeGroup α)
    (w : J → List (α × Bool)) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx A →o PresPos w) :
    Function.Injective (baseToQuotientW (A := A) ρ w hw att) := by
  intro x y h
  exact alphaHomW_injective ρ w hw
    (pi1Map_qNew_injective (ptBase w) h)

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

section SpineW

variable {α J : Type u} (w : J → List (α × Bool)) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
  (cb : List ((orderCx (PresPos w)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))

/-- The cellular map of the inclusion of the base copy in the quotient. -/
abbrev qInclCxW : Hom (orderCx (PresPos w)) (orderCx (Qpos A (PresPos w) att)) :=
  orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone

/-- The base point of the quotient. -/
abbrev qBasePtW : (orderCx (Qpos A (PresPos w) att)).V :=
  qNew (A := A) (att := att) (ptBase w)

/-- The cut surface, mapped into the quotient through the block. -/
abbrev surfQW : (NeSpx A) → Qpos A (PresPos w) att :=
  fun σ => qOldIncl (X := PresPos w) (att := att) (posQCube σ)

omit [Fintype V] in
theorem surfQW_monotone : Monotone (surfQW w att) :=
  qOldIncl_monotone.comp posQCube_monotone

/-- The cut surface, mapped into the quotient through the copy of the base. -/
abbrev surfBaseW : (NeSpx A) → Qpos A (PresPos w) att :=
  fun σ => qNew (att σ)

omit [Fintype V] in
theorem surfBaseW_monotone : Monotone (surfBaseW w att) :=
  qNew_monotone.comp att.monotone

/-- The path from the base point of the copy of the base to the block. -/
def cylPathW : List ((orderCx (Qpos A (PresPos w) att)).E × Bool) :=
  mapPath (qInclCxW w att) cb ++ [ordPos (qNew_att_le_qOldIncl (att := att) σ₀)]

omit [Fintype V] in
theorem isPath_cylPathW (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
    cb (ptBase w) (att σ₀)) :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (cylPathW w att σ₀ cb) (qBasePtW w att) (surfQW w att σ₀) :=
  isPath_append_iff.mpr ⟨_, isPath_mapPath (qInclCxW w att) hcb, isPath_ordPos _⟩

/-- The path from the base point of the copy of the base to the root of the spanning tree. -/
def rootPathW : List ((orderCx (Qpos A (PresPos w) att)).E × Bool) :=
  cylPathW w att σ₀ cb ++
    revPath (mapPath (blockCx A (PresPos w) att) (T.treePath (posQCube σ₀)))

omit [Fintype V] in
theorem isPath_rootPathW (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
    cb (ptBase w) (att σ₀)) :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (rootPathW w att σ₀ cb T) (qBasePtW w att)
      (qOldIncl (X := PresPos w) (att := att) T.root) :=
  (isPath_cylPathW w att σ₀ cb hcb).append
    (isPath_revPath (isPath_mapPath _ (T.treePath_isPath (posQCube σ₀))))

/-- **The geometric loops of the block.** -/
def blockToQW (hcb : IsPath (orderCx (PresPos w)).src
    (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀)) :
    Pi1 (orderCx (QOld A)) T.root →*
      Pi1 (orderCx (Qpos A (PresPos w) att)) (qBasePtW w att) :=
  (pi1Conj (isPath_rootPathW w att σ₀ cb T hcb)).comp
    (pi1Map (blockCx A (PresPos w) att) T.root)

omit [Fintype V] in
/-- **The cylinder computation.** -/
theorem blockToQW_surfLoop
    (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀))
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ₀ σ₀) :
    blockToQW w att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Map (qInclCxW w att) (ptBase w)
          (pi1Conj hcb (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p,
            isPath_mapPath _ hp⟩)) := by
  have htp : IsPath (orderCx (QOld A)).src (orderCx (QOld A)).tgt (T.treePath (posQCube σ₀))
      T.root (posQCube σ₀) := T.treePath_isPath _
  have hmtp := isPath_mapPath (blockCx A (PresPos w) att) htp
  have hcyl := isPath_cylPathW w att σ₀ cb hcb
  set X : Pi1 (orderCx (QOld A)) (posQCube σ₀) :=
    Pi1.mk ⟨mapPath (surfCx A) p, isPath_mapPath (surfCx A) hp⟩ with hX
  set Y : Pi1 (orderCx (PresPos w)) (att σ₀) :=
    Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p, isPath_mapPath _ hp⟩ with hY
  set Z : Pi1 (orderCx (Qpos A (PresPos w) att)) (surfBaseW w att σ₀) :=
    Pi1.mk ⟨mapPath (orderCxMap (surfBaseW w att) (surfBaseW_monotone w att)) p,
      isPath_mapPath _ hp⟩ with hZ
  have hcancel : Htpy (orderCx (Qpos A (PresPos w) att)) (qBasePtW w att) (surfQW w att σ₀)
      (rootPathW w att σ₀ cb T ++ mapPath (blockCx A (PresPos w) att)
        (T.treePath (posQCube σ₀))) (cylPathW w att σ₀ cb) := by
    have h := (htpy_revPath_append hmtp).congr_append hcyl (isPath_nil' (surfQW w att σ₀))
    simpa [rootPathW, List.append_assoc] using h
  have hback : Htpy (orderCx (Qpos A (PresPos w) att)) (qBasePtW w att) (surfBaseW w att σ₀)
      (cylPathW w att σ₀ cb ++ [ordNeg (qNew_att_le_qOldIncl σ₀)])
      (mapPath (qInclCxW w att) cb) := by
    have h := (htpy_ordPos_ordNeg (qNew_att_le_qOldIncl σ₀)).congr_append
      (isPath_mapPath (qInclCxW w att) hcb) (isPath_nil' (surfBaseW w att σ₀))
    simpa [cylPathW, List.append_assoc] using h
  have hnat := htpy_loop_mapPath_le (surfBaseW_monotone w att) (surfQW_monotone w att)
    (fun σ => qNew_att_le_qOldIncl σ) hp
  have hE : pi1Map (blockCx A (PresPos w) att) (posQCube σ₀) X
      = pi1Conj (isPath_ordNeg (qNew_att_le_qOldIncl σ₀)) Z := by
    refine Quotient.sound ?_
    show Htpy (orderCx (Qpos A (PresPos w) att)) (surfQW w att σ₀) (surfQW w att σ₀)
      (mapPath (blockCx A (PresPos w) att) (mapPath (surfCx A) p))
      ([ordNeg (qNew_att_le_qOldIncl σ₀)] ++
        mapPath (orderCxMap (surfBaseW w att) (surfBaseW_monotone w att)) p ++
        [ordPos (qNew_att_le_qOldIncl σ₀)])
    have hlist : mapPath (blockCx A (PresPos w) att) (mapPath (surfCx A) p)
        = mapPath (orderCxMap (surfQW w att) (surfQW_monotone w att)) p := by
      simp [mapPath, blockCx, surfCx, orderCxMap, List.map_map, Function.comp_def]
    rw [hlist]
    exact hnat
  have hH : Z = pi1Map (qInclCxW w att) (att σ₀) Y := by
    refine Quotient.sound ?_
    show Htpy (orderCx (Qpos A (PresPos w) att)) (surfBaseW w att σ₀) (surfBaseW w att σ₀)
      (mapPath (orderCxMap (surfBaseW w att) (surfBaseW_monotone w att)) p)
      (mapPath (qInclCxW w att) (mapPath (orderCxMap att att.monotone) p))
    have hlist : mapPath (qInclCxW w att) (mapPath (orderCxMap att att.monotone) p)
        = mapPath (orderCxMap (surfBaseW w att) (surfBaseW_monotone w att)) p := by
      simp [mapPath, orderCxMap, List.map_map, Function.comp_def]
    rw [hlist]
    exact Htpy.refl _
  calc blockToQW w att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Conj (isPath_rootPathW w att σ₀ cb T hcb)
          (pi1Map (blockCx A (PresPos w) att) T.root (pi1Conj htp X)) := rfl
    _ = pi1Conj (isPath_rootPathW w att σ₀ cb T hcb)
          (pi1Conj hmtp (pi1Map (blockCx A (PresPos w) att) (posQCube σ₀) X)) :=
        congrArg _ (pi1Map_pi1Conj (blockCx A (PresPos w) att) htp X)
    _ = pi1Conj ((isPath_rootPathW w att σ₀ cb T hcb).append hmtp)
          (pi1Map (blockCx A (PresPos w) att) (posQCube σ₀) X) :=
        pi1Conj_pi1Conj _ hmtp _
    _ = pi1Conj hcyl (pi1Map (blockCx A (PresPos w) att) (posQCube σ₀) X) :=
        pi1Conj_congr _ hcyl hcancel _
    _ = pi1Conj hcyl (pi1Conj (isPath_ordNeg (qNew_att_le_qOldIncl σ₀)) Z) :=
        congrArg _ hE
    _ = pi1Conj (hcyl.append (isPath_ordNeg (qNew_att_le_qOldIncl σ₀))) Z :=
        pi1Conj_pi1Conj _ _ _
    _ = pi1Conj (isPath_mapPath (qInclCxW w att) hcb) Z :=
        pi1Conj_congr _ (isPath_mapPath (qInclCxW w att) hcb) hback _
    _ = pi1Conj (isPath_mapPath (qInclCxW w att) hcb)
          (pi1Map (qInclCxW w att) (att σ₀) Y) := congrArg _ hH
    _ = pi1Map (qInclCxW w att) (ptBase w) (pi1Conj hcb Y) :=
        (pi1Map_pi1Conj (qInclCxW w att) hcb Y).symm

end SpineW

section ApplicationW

variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
  (cb : List ((orderCx (PresPos w)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))
  {Su : Type u}

include hw

end ApplicationW

end Davis
end FiniteChains
end

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

namespace Genus

variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α) (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- The words of the presentation: the chosen words of the retained relators, and the surface
word of genus `q` for the relator of the block. -/
def genusW : Jr ⊕ PUnit → List (α × Bool) :=
  Sum.elim (fun jr => presWords ρ (Sum.inl jr)) (fun _ => surfWord a b q)

omit [NeZero q] in
theorem genusW_inr (s : PUnit) : genusW ρ a b q (Sum.inr s) = surfWord a b q := rfl

omit [NeZero q] in
theorem mk_genusW (hrho : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q)) :
    ∀ j, FreeGroup.mk (genusW ρ a b q j) = ρ j := by simp_all [mk_presWords, genusW]

/-- **The attaching map of the block**: the marking of the surface of genus `q`, which sends the
boundary of the polygon onto the attaching circle of the relator of the block. -/
abbrev genusAtt :
    NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) →o PresPos (genusW ρ a b q) :=
  surfAtt (w := genusW ρ a b q) (j₀ := Sum.inr PUnit.unit) (genus_hM a b q)
    (genus_hvlab a b q) (genus_helb a b q) (gc q)

/-- The word read by the loop of the distinguished generator `x = (h, i)`: the letter `a_h` for
`i = false`, the letter `b_h` for `i = true`. -/
def genusLw (_ : PUnit) (x : ℕ × Bool) : List (α × Bool) :=
  [sLet a b (4 * (x.1 % q) + (if x.2 then 1 else 0))]

/-! ### The base point -/


theorem genus_hcb :
    IsPath (orderCx (PresPos (genusW ρ a b q))).src (orderCx (PresPos (genusW ρ a b q))).tgt []
      (ptBase (genusW ρ a b q)) (genusAtt ρ a b q (gBase q)) :=
  (show genusAtt ρ a b q (gBase q) = ptBase (genusW ρ a b q) by
    erw [gBase, att_V, vertLab_of_even (by rw [cyc_mod_two])]
    rfl).symm

/-! ### The reading -/

omit [NeZero q] in
theorem genus_index (x : ℕ × Bool) :
    8 * (x.1 % q) + (if x.2 then 2 else 0)
      = 2 * (4 * (x.1 % q) + (if x.2 then 1 else 0)) := by grind

theorem genus_index_lt (x : ℕ × Bool) :
    4 * (x.1 % q) + (if x.2 then 1 else 0) < (surfWord a b q).length := by
  have hq : x.1 % q < q := Nat.mod_lt _ (Nat.pos_of_neZero q)
  rw [surfWord_length]
  grind

/-- **The loop of the distinguished generator reads its letter.** -/
theorem genus_hread (s : PUnit) (x : ℕ × Bool) :
    Htpy (orderCx (PresPos (genusW ρ a b q))) (ptBase (genusW ρ a b q))
      (ptBase (genusW ρ a b q))
      ([] ++ mapPath (orderCxMap (genusAtt ρ a b q) (genusAtt ρ a b q).monotone) (gSig q x)
        ++ revPath [])
      (wordLoop (genusW ρ a b q) (genusLw a b q s x)) := by
  set k : ℕ := 4 * (x.1 % q) + (if x.2 then 1 else 0) with hkdef
  have hk  := genus_index_lt a b q x
  -- the loop of the generator is the side of the polygon carrying the letter `k`
  have hsig : gSig q x
      = bdEdge (gc q) (cyc (8 * q) (2 * k)) ++ bdEdge (gc q) (cyc (8 * q) (2 * k + 1)) := by
    have h1 : gSig q x = gPath q (2 * k) := by
      rw [gSig_eq, genus_index]
    rw [h1]
    exact pPath_eq (gc q) (2 * k)
  -- the letter read is the letter `k` of the surface word
  have hlet : (genusW ρ a b q (Sum.inr PUnit.unit))[k]'hk = sLet a b k := by
    have h := surfWord_getElem? a b q k (by
      have := genus_index_lt a b q x
      rw [surfWord_length] at this
      exact this)
    have h'  := h
    rw [List.getElem?_eq_getElem hk] at h'
    exact Option.some.inj h'
  have hmain := htpy_mapPath_letter (w := genusW ρ a b q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM a b q) (genus_hvlab a b q) (genus_helb a b q) (gc q) k hk
  rw [hlet] at hmain
  rw [hsig]
  have hword : wordLoop (genusW ρ a b q) (genusLw a b q s x)
      = letterLoop (genusW ρ a b q) (sLet a b k) := by
    simp [genusLw, wordLoop, hkdef]
  rw [hword]
  simpa using hmain

/-! ### The relator of the block -/

/-! ### The theorem applied to the block -/

/-! ### Simultaneous substitutions for an arbitrary family of relators -/

end Genus

end Davis
end FiniteChains

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
  (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- Nonempty representatives retaining the prescribed genus surface word. -/
def genusNonemptyW : Jr ⊕ PUnit → List (α × Bool) :=
  Sum.elim (fun j => presNonemptyWords ρ (a 0) (Sum.inl j)) (fun _ => surfWord a b q)

theorem genusNonemptyW_ne_nil (j : Jr ⊕ PUnit) : genusNonemptyW ρ a b q j ≠ [] := by
  cases j with
  | inl j => exact presNonemptyWords_ne_nil ρ (a 0) (Sum.inl j)
  | inr s =>
    intro h
    have hl := congrArg List.length h
    change (surfWord a b q).length = 0 at hl
    erw [surfWord_length] at hl
    have := Nat.pos_of_neZero q
    omega

omit [NeZero q] in
theorem mk_genusNonemptyW
    (hr : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q)) :
    ∀ j, FreeGroup.mk (genusNonemptyW ρ a b q j) = ρ j := by simp_all [mk_presNonemptyWords, genusNonemptyW]

theorem genusNonemptyW_isConnected :
    IsConnected (orderCx (PresPos (genusNonemptyW ρ a b q))) :=
  presPos_isConnected _ (genusNonemptyW_ne_nil ρ a b q)

abbrev genusNonemptyAtt :
    NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) →o PresPos (genusNonemptyW ρ a b q) :=
  surfAtt (w := genusNonemptyW ρ a b q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM a b q) (genus_hvlab a b q) (genus_helb a b q) (gc q)

theorem genusNonemptyAtt_base :
    genusNonemptyAtt ρ a b q (gBase q) = ptBase (genusNonemptyW ρ a b q) := by
  erw [gBase, att_V, vertLab_of_even (by erw [cyc_mod_two])]
  rfl

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
  (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- Adding cancelling letters to empty retained relators leaves the actual
surface marking and its reading unchanged. -/
theorem genusNonempty_hread (s : PUnit) (x : ℕ × Bool) :
    Htpy (orderCx (PresPos (genusNonemptyW ρ a b q)))
      (ptBase (genusNonemptyW ρ a b q)) (ptBase (genusNonemptyW ρ a b q))
      ([] ++ mapPath (orderCxMap (genusNonemptyAtt ρ a b q)
        (genusNonemptyAtt ρ a b q).monotone) (gSig q x) ++ revPath [])
      (wordLoop (genusNonemptyW ρ a b q) (genusLw a b q s x)) := by
  set k : ℕ := 4 * (x.1 % q) + (if x.2 then 1 else 0) with hkdef
  have hk  :=
    genus_index_lt a b q x
  have hsig : gSig q x = bdEdge (gc q) (cyc (8 * q) (2 * k)) ++
      bdEdge (gc q) (cyc (8 * q) (2 * k + 1)) := by
    have h1 : gSig q x = gPath q (2 * k) := by
      rw [gSig_eq, genus_index]
    rw [h1]
    exact pPath_eq (gc q) (2 * k)
  have hlet : (genusNonemptyW ρ a b q (Sum.inr PUnit.unit))[k]'hk = sLet a b k := by
    have h := surfWord_getElem? a b q k (by
      have := genus_index_lt a b q x
      rw [surfWord_length] at this
      exact this)
    have h'  := h
    rw [List.getElem?_eq_getElem hk] at h'
    exact Option.some.inj h'
  have hmain := htpy_mapPath_letter (w := genusNonemptyW ρ a b q)
    (j₀ := Sum.inr PUnit.unit) (genus_hM a b q) (genus_hvlab a b q)
    (genus_helb a b q) (gc q) k hk
  rw [hlet] at hmain
  rw [hsig]
  have hword : wordLoop (genusNonemptyW ρ a b q) (genusLw a b q s x) =
      letterLoop (genusNonemptyW ρ a b q) (sLet a b k) := by
    simp [genusLw, wordLoop, hkdef]
  rw [hword]
  simpa using hmain

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (a b : ℕ → α)
  (q : ℕ) [NeZero q]

abbrev finiteSig (x : Fin q × Bool) := gSig q (x.1.val, x.2)

def finitePairs (q : ℕ) : List ((Fin q × Bool) × (Fin q × Bool)) :=
  (List.finRange q).map fun h => ((h, false), (h, true))

omit [NeZero q] in
/-- Reindexing the surface word by the finite set of its handles. -/
theorem commWord_finitePairs {G : Type} [Group G] (f : ℕ × Bool → G) :
    commWord (fun x : Fin q × Bool => f (x.1.val, x.2)) (finitePairs q) =
      commWord f (genPairs q) := by
  simp only [finitePairs, genPairs, commWord, List.map_map]
  have h := List.map_coe_finRange_eq_range (n := q)
  rw [← h, List.map_map]
  rfl

local instance genusPi1Group : Group
    (Pi1 (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)) :=
  @Pi1.instGroup (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)

/-- The finite list of marked loops bounds the canonical surface polygon. -/
theorem finite_hfilling :
    commWord (fun x : Fin q × Bool =>
      Pi1.mk (⟨finiteSig q x, isPath_gSig q (x.1.val, x.2)⟩ :
        Loop (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)))
      (finitePairs q) = 1 := (commWord_finitePairs q _).trans (genus_hfilling q)

abbrev finiteLw (_ : PUnit.{1}) (x : Fin q × Bool) : List (α × Bool) :=
  genusLw a b q (PUnit.unit.{1} : PUnit.{1}) (x.1.val, x.2)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- Named generators for the two loops of a handle, extended periodically. -/
def namedA (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩, false)

def namedB (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩, true)

abbrev namedPres := SurfaceWordExpansion.expandedRel ρ u (finitePairs q)

 theorem namedPres_surface : namedPres ρ q u (Sum.inr PUnit.unit) =
    FreeGroup.mk (surfWord (namedA (α := α) q) (namedB (α := α) q) q) := by
  change commWord (fun x => FreeGroup.of (Sum.inr x)) (finitePairs q) = _
  have h : (fun x : Fin q × Bool =>
      FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) (x.1.val, x.2))) =
        (fun x => FreeGroup.of (Sum.inr x)) := by
    funext x
    obtain ⟨h, b⟩ := x
    have hm : h.val % q = h.val := Nat.mod_eq_of_lt h.isLt
    cases b <;> simp [genLw, namedA, namedB, hm] <;> rfl
  rw [← h, commWord_finitePairs q (fun x =>
    FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) x))]
  exact (mk_surfWord (namedA (α := α) q) (namedB (α := α) q) q).symm

 theorem namedLw_eq (s : PUnit.{1}) (x : Fin q × Bool) :
    finiteLw (namedA (α := α) q) (namedB (α := α) q) q s x = [(Sum.inr x, true)] := by
  obtain ⟨h, b⟩ := x
  have hm : h.val % q = h.val := Nat.mod_eq_of_lt h.isLt
  cases b
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 0)] = _
    rw [hm]
    rw [sLet, if_pos (by omega), show (4 * h.val + 0) / 4 = h.val from by omega]
    simp [namedA, hm]
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 1)] = _
    rw [hm]
    rw [sLet, if_neg (by omega), if_pos (by omega),
      show (4 * h.val + 1) / 4 = h.val from by omega]
    simp [namedB, hm]

variable (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q))))))

variable (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis
open Comb
universe u
variable {X : Complex2.{u}} {a : X.V} {ι : Type u}

/-- The edge path spelling a product of commutators of marked loops. -/
def surfacePath (f : ι → Loop X a) : List (ι × ι) → List (X.E × Bool)
  | [] => []
  | p :: ps => (f p.1).1 ++ (f p.2).1 ++ revPath (f p.1).1 ++
      revPath (f p.2).1 ++ surfacePath f ps

theorem surfacePath_isLoop (f : ι → Loop X a) (ps : List (ι × ι)) :
    IsPath X.src X.tgt (surfacePath f ps) a a := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    exact ((((f p.1).2.append (f p.2).2).append (isPath_revPath (f p.1).2)).append
      (isPath_revPath (f p.2).2)).append ih

theorem surfacePath_class (f : ι → Loop X a) (ps : List (ι × ι)) :
    Pi1.mk ⟨surfacePath f ps, surfacePath_isLoop f ps⟩ =
      commWord (fun i => Pi1.mk (f i)) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [commWord_cons, ← ih]
    rfl

/-- The canonical surface word bounds by its proved edge-path relation. -/
theorem surfacePath_nullhomotopic (f : ι → Loop X a) (ps : List (ι × ι))
    (hf : commWord (fun i => Pi1.mk (f i)) ps = 1) :
    Htpy X a a (surfacePath f ps) [] := by
  have he  := (surfacePath_class f ps).trans hf
  exact Quotient.exact he

namespace Genus
variable (q : ℕ) [NeZero q]

def finiteMarkedLoops (x : Fin q × Bool) :
    Loop (sdCx (gc q)) (gBase q) :=
  ⟨finiteSig q x, isPath_gSig q (x.1.val, x.2)⟩

end Genus
end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem spineMarkedLoop_hfilling :
    commWord (fun x : Fin q × Bool => Pi1.mk (spineMarkedLoop q x))
      (finitePairs q) = 1 := by
  apply genusSpineToOld_pi1_injective q
  rw [map_one, map_commWord]
  rw [commWord_congr (spineMarkedLoop_toOld_class q)]
  have h := congrArg (pi1Map (surfCx (cmpRel (GenusVertex q))) (gBase q))
    (finite_hfilling q)
  rw [map_one, map_commWord] at h
  exact h

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

def markedSpineCx : Complex2 := component (genusSpineCx q) (spineBase q)

def markedSpineBase : (markedSpineCx q).V :=
  ⟨spineBase q, reach_self _ _⟩


instance : Finite (markedSpineCx q).E := by
  unfold markedSpineCx
  infer_instance

instance : Finite (markedSpineCx q).F := by
  unfold markedSpineCx
  infer_instance


def markedSpineLoop (x : Fin q × Bool) :
    Loop (markedSpineCx q) (markedSpineBase q) :=
  ⟨liftGerms (genusSpineCx q) (spineBase q) (spineMarkedLoop q x).1,
    isPath_liftGerms (reach_self _ _) (reach_self _ _) (spineMarkedLoop q x).2⟩

theorem markedSpineLoop_inclusion (x : Fin q × Bool) :
    mapPath (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineLoop q x).1 =
      (spineMarkedLoop q x).1 := by
  exact map_cForget_liftGerms
    (reach_of_mem_path (spineMarkedLoop q x).2 (reach_self _ _))

theorem markedSpineLoop_inclusion_class (x : Fin q × Bool) :
    pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (Pi1.mk (markedSpineLoop q x)) = Pi1.mk (spineMarkedLoop q x) := by
  apply congrArg Pi1.mk
  apply Subtype.ext
  exact markedSpineLoop_inclusion q x

theorem markedSpine_exists_tree :
    ∃ T : SpanningTree (markedSpineCx q), T.root = markedSpineBase q :=
  SpanningTree.exists_of_isConnected (component_isConnected (spineBase q)) (markedSpineBase q)

/-- Passing to the actual component loses no based homotopies. -/
theorem markedSpine_inclusion_pi1_injective :
    Function.Injective
      (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)) := by
  erw [injective_iff_map_eq_one]
  rintro ⟨p⟩ hp
  have h : Htpy (genusSpineCx q) (spineBase q) (spineBase q)
      (mapPath (componentIncl (genusSpineCx q) (spineBase q)) p.1) [] :=
    Quotient.exact hp
  have hl := htpy_liftGerms (reach_self (genusSpineCx q) (spineBase q))
    (reach_self (genusSpineCx q) (spineBase q)) h
  erw [mapPath_componentIncl, liftGerms_map_cForget] at hl
  exact Quotient.sound hl


/-- The marked component has precisely the fundamental group of the full spine at its base. -/
def markedSpinePi1Equiv :
    Pi1 (markedSpineCx q) (markedSpineBase q) ≃* Pi1 (genusSpineCx q) (spineBase q) :=
  MulEquiv.ofBijective
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q))
    ⟨markedSpine_inclusion_pi1_injective q, (by
      rintro ⟨p⟩
      let lp : Loop (markedSpineCx q) (markedSpineBase q) :=
        ⟨liftGerms (genusSpineCx q) (spineBase q) p.1,
          isPath_liftGerms (reach_self _ _) (reach_self _ _) p.2⟩
      refine ⟨Pi1.mk lp, ?_⟩
      apply congrArg Pi1.mk
      apply Subtype.ext
      exact map_cForget_liftGerms (reach_of_mem_path p.2 (reach_self _ _)))⟩

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]



def markedSpineTree : SpanningTree (markedSpineCx q) :=
  Classical.choose (markedSpine_exists_tree q)

theorem markedSpineTree_root : (markedSpineTree q).root = markedSpineBase q :=
  Classical.choose_spec (markedSpine_exists_tree q)

abbrev SpinePresentationGen := SpanningTree.NonTree (markedSpineTree q)
abbrev SpinePresentationRel := (markedSpineCx q).F

instance : Finite (SpinePresentationGen q) := inferInstance
instance : Finite (SpinePresentationRel q) := inferInstance

def spinePresentation : SpinePresentationRel q → FreeGroup (SpinePresentationGen q) :=
  SpanningTree.treeRel (markedSpineTree q)

def spinePresentationPi1Equiv :
    Pi1 (markedSpineCx q) (markedSpineTree q).root ≃* PresGroup (spinePresentation q) :=
  SpanningTree.pi1EquivPres (markedSpineTree q)

def spinePresentationMarkedWord (x : Fin q × Bool) :
    FreeGroup (SpinePresentationGen q) :=
  SpanningTree.pathWord (markedSpineTree q) (markedSpineLoop q x).1

/-- Reading a surface path in the genuine spanning-tree presentation preserves its word. -/
theorem pathWord_surfacePath {X : Complex2} {a : X.V} {ι : Type}
    (T : SpanningTree X) (f : ι → Loop X a) (ps : List (ι × ι)) :
    SpanningTree.pathWord T (surfacePath f ps) =
      commWord (fun i => SpanningTree.pathWord T (f i).1) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [surfacePath, SpanningTree.pathWord_append, SpanningTree.pathWord_revPath,
      ih, commWord_cons]

/-- The marked relation holds in this actual finite cell presentation. -/
theorem spinePresentationMarkedWord_hfilling :
    commWord (fun x => (QuotientGroup.mk' (relSub (spinePresentation q)))
      (spinePresentationMarkedWord q x)) (finitePairs q) = 1 := by
  have h := SpanningTree.wordClass_htpy (markedSpineTree q)
    (surfacePath_nullhomotopic _ _ (by
      apply markedSpine_inclusion_pi1_injective q
      rw [map_one, map_commWord,
        commWord_congr (markedSpineLoop_inclusion_class q)]
      exact spineMarkedLoop_hfilling q))
  change (QuotientGroup.mk' (relSub (spinePresentation q)))
      (SpanningTree.pathWord (markedSpineTree q)
        (surfacePath (markedSpineLoop q) (finitePairs q))) = 1 at h
  rw [pathWord_surfacePath, map_commWord] at h
  exact h

/-- Attach a disk along each of the genuine marked words. -/
def cappedSpinePresentation :
    SpinePresentationRel q ⊕ (Fin q × Bool) → FreeGroup (SpinePresentationGen q)
  | .inl f => spinePresentation q f
  | .inr x => spinePresentationMarkedWord q x

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev NamedSpineGen := SpinePresentationGen q ⊕ (Fin q × Bool)
abbrev NamedSpineRel := SpinePresentationRel q ⊕ (Fin q × Bool)

instance : Finite (NamedSpineRel q) := inferInstance

def namedSpinePresentation : NamedSpineRel q → FreeGroup (NamedSpineGen q) :=
  NamedPresentation.rel (spinePresentation q) (spinePresentationMarkedWord q)

def namedSpineGroupEquiv :
    PresGroup (spinePresentation q) ≃* PresGroup (namedSpinePresentation q) :=
  NamedPresentation.groupEquiv (spinePresentation q) (spinePresentationMarkedWord q)

/-- Each distinguished generator represents its actual geometric marking word. -/
theorem namedSpine_generator (x : Fin q × Bool) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)) =
      namedSpineGroupEquiv q
        (QuotientGroup.mk (spinePresentationMarkedWord q x)) :=
  NamedPresentation.name_eq_word (spinePresentation q) (spinePresentationMarkedWord q) x

/-- The formal surface word fills in the genuine finite marked block presentation. -/
theorem namedSpine_surface_filling :
    commWord (fun x : Fin q × Bool =>
      (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)))
      (finitePairs q) = 1 := by
  rw [commWord_congr (namedSpine_generator q)]
  change commWord (fun x => (namedSpineGroupEquiv q).toMonoidHom
    (QuotientGroup.mk (spinePresentationMarkedWord q x))) (finitePairs q) = 1
  rw [← map_commWord]
  exact (congrArg (namedSpineGroupEquiv q).toMonoidHom
    (spinePresentationMarkedWord_hfilling q)).trans (map_one _)

def namedSpinePi1Equiv :
    Pi1 (markedSpineCx q) (markedSpineTree q).root ≃* PresGroup (namedSpinePresentation q) :=
  (spinePresentationPi1Equiv q).trans (namedSpineGroupEquiv q)

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
variable {X : Complex2} {a b : X.V}

 def pi1BaseEqEquiv (h : a = b) : Pi1 X a ≃* Pi1 X b := by
  subst b
  exact MulEquiv.refl _

 theorem pi1BaseEqEquiv_mk (h : a = b) (p : Loop X a) (q : Loop X b)
    (hpq : p.1 = q.1) : pi1BaseEqEquiv h (Pi1.mk p) = Pi1.mk q := by
  subst b
  have he : p = q := Subtype.ext hpq
  subst q
  rfl
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def namedSpineToOldEquiv :
    PresGroup (namedSpinePresentation q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
        ((genusSpineToOld q).onV (spineBase q)) :=
  (namedSpinePi1Equiv q).symm.trans
    ((pi1BaseEqEquiv (markedSpineTree_root q)).trans
      ((markedSpinePi1Equiv q).trans (genusSpineToOldPi1Equiv q)))

def treeMarkedSpineLoop (x : Fin q × Bool) :
    Loop (markedSpineCx q) (markedSpineTree q).root :=
  ⟨(markedSpineLoop q x).1, by rw [markedSpineTree_root]; exact (markedSpineLoop q x).2⟩

theorem namedSpinePi1Equiv_marked (x : Fin q × Bool) :
    namedSpinePi1Equiv q (Pi1.mk (treeMarkedSpineLoop q x)) =
      (QuotientGroup.mk (FreeGroup.of (Sum.inr x)) : PresGroup (namedSpinePresentation q)) := (namedSpine_generator q x).symm

/-- The distinguished names correspond exactly to the verified old block marking. -/
theorem namedSpineToOld_marked (x : Fin q × Bool) :
    namedSpineToOldEquiv q (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) := by
  rw [← namedSpinePi1Equiv_marked q x]
  change (genusSpineToOldPi1Equiv q)
    ((markedSpinePi1Equiv q)
      (pi1BaseEqEquiv (markedSpineTree_root q)
        ((namedSpinePi1Equiv q).symm
          ((namedSpinePi1Equiv q) (Pi1.mk (treeMarkedSpineLoop q x)))))) = _
  rw [MulEquiv.symm_apply_apply,
    pi1BaseEqEquiv_mk (markedSpineTree_root q) (treeMarkedSpineLoop q x)
      (markedSpineLoop q x) rfl]
  change pi1Map (genusSpineToOld q) (spineBase q)
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (Pi1.mk (markedSpineLoop q x))) = _
  rw [markedSpineLoop_inclusion_class]

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev MarkedSpineGen := (Fin q × Bool) ⊕ SpinePresentationGen q

def markedSpineBeta (m : NamedSpineRel q) : FreeGroup (MarkedSpineGen q) :=
  FreeGroup.map Sum.swap (namedSpinePresentation q m)

theorem freeGroup_map_swap_swap {α β : Type} (z : FreeGroup (α ⊕ β)) :
    FreeGroup.map Sum.swap (FreeGroup.map Sum.swap z) = z := by
  have h : (FreeGroup.map (Sum.swap : β ⊕ α → α ⊕ β)).comp
      (FreeGroup.map Sum.swap) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    rintro (a | b) <;> simp
  exact DFunLike.congr_fun h z

def markedSpineToOldHom :
    FreeGroup (MarkedSpineGen q) →*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
        ((genusSpineToOld q).onV (spineBase q)) :=
  (namedSpineToOldEquiv q).toMonoidHom.comp
    ((QuotientGroup.mk' (relSub (namedSpinePresentation q))).comp (FreeGroup.map Sum.swap))

/-- All genuine marked block relators die under the constructed geometric block map. -/
theorem markedSpineToOldHom_rel (m : NamedSpineRel q) :
    markedSpineToOldHom q (markedSpineBeta q m) = 1 := by
  change (namedSpineToOldEquiv q).toMonoidHom
    (QuotientGroup.mk (FreeGroup.map Sum.swap
      (FreeGroup.map Sum.swap (namedSpinePresentation q m)))) = 1
  rw [freeGroup_map_swap_swap]
  have h : (QuotientGroup.mk (namedSpinePresentation q m) :
      PresGroup (namedSpinePresentation q)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩)
  rw [h, map_one]

/-- The distinguished generators have exactly the actual geometric marking. -/
theorem markedSpineToOldHom_mark (x : Fin q × Bool) :
    markedSpineToOldHom q (FreeGroup.of (Sum.inl x)) =
      pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) := by
  change namedSpineToOldEquiv q
    (QuotientGroup.mk (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inl x)))) = _
  simp
  exact namedSpineToOld_marked q x

/-- The surface word is a consequence of the actual reordered finite spine relators. -/
theorem markedSpine_surface_mem :
    commWord (fun x : Fin q × Bool => FreeGroup.of (Sum.inl x : MarkedSpineGen q))
      (finitePairs q) ∈ relSub (markedSpineBeta q) := by
  have h : commWord (fun x : Fin q × Bool =>
      FreeGroup.of (Sum.inr x)) (finitePairs q) ∈
      relSub (namedSpinePresentation q) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (relSub (namedSpinePresentation q)))
      (commWord (fun x => FreeGroup.of (Sum.inr x)) (finitePairs q)) = 1
    rw [map_commWord]
    exact namedSpine_surface_filling q
  have hm := map_mem_normalClosure (FreeGroup.map Sum.swap)
    (N := Set.range (markedSpineBeta q)) (fun z hz => by
      obtain ⟨m, rfl⟩ := hz
      exact Subgroup.subset_normalClosure ⟨m, rfl⟩) h
  simpa only [relSub, map_commWord, FreeGroup.map.of, Sum.swap_inr] using hm

/-- Simultaneous replacement by genuine finite spine relators fills each replaced word. -/
theorem markedSpine_filled {α Jr Sx : Type}
    (ρ : Jr ⊕ Sx → FreeGroup α) (u : Sx → Fin q × Bool → FreeGroup α)
    (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs q)) :
    BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s
        (markedSpineBeta q m)) := by
  apply BlockFamily.filledF_of_block_consequences
  intro s
  have h := map_mem_normalClosure
    (BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s)
    (N := Set.range (fun m => BlockFamily.blockSubst
      (Zt := fun _ => SpinePresentationGen q) u s (markedSpineBeta q m)))
    (fun z hz => by
      obtain ⟨m, rfl⟩ := hz
      exact Subgroup.subset_normalClosure ⟨m, rfl⟩) (markedSpine_surface_mem q)
  rw [map_commWord] at h
  simp at h
  rw [hrho s, map_commWord]
  exact h

/-- The actual geometric block map supplies the relator checks for substitution.
Only the receiver inclusion and the reading of the prescribed words remain inputs. -/
theorem markedSpine_substitution_injective {α Jr Sx H : Type} [Group H]
    (ρ : Jr ⊕ Sx → FreeGroup α) (u : Sx → Fin q × Bool → FreeGroup α)
    (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs q))
    (j : PresGroup ρ →* H) (hj : Function.Injective j)
    (receiver : Sx → Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
      ((genusSpineToOld q).onV (spineBase q)) →* H)
    (hread : ∀ s x, receiver s
      (pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x))) =
        j (QuotientGroup.mk (u s x))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s
        (markedSpineBeta q m)) (markedSpine_filled q ρ u hrho)) := by
  apply BlockFamily.injective_substHomF_of_markedBlock u
    (fun _ => markedSpineBeta q) (markedSpine_filled q ρ u hrho) j hj
    (fun s => (receiver s).comp (markedSpineToOldHom q))
  · intro s x
    rw [MonoidHom.comp_apply, markedSpineToOldHom_mark]
    exact hread s x
  · intro s m
    rw [MonoidHom.comp_apply, markedSpineToOldHom_rel, map_one]

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- Genuine finite spine relators with arbitrary prescribed old words substituted. -/
def finiteSpineWordBlock (s : PUnit.{1}) (m : NamedSpineRel q) :
    FreeGroup (α ⊕ SpinePresentationGen q) :=
  blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen q) (fun _ => u) s
    (markedSpineBeta q m)

variable (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

include hrho in
theorem finiteSpineWordBlock_filled : FilledF ρ (finiteSpineWordBlock q u) :=
  markedSpine_filled q ρ (fun _ => u) (fun s => by cases s; exact hrho)

/-- The structural inclusion is injective for the actual finite spine and arbitrary words. -/
theorem finiteSpineWordBlock_injective :
    Function.Injective (substHomF ρ (finiteSpineWordBlock q u)
      (finiteSpineWordBlock_filled ρ q u hrho)) := by
  let ep := namedPres ρ q u
  let aa := namedA (α := α) q
  let bb := namedB (α := α) q
  have he  :=
    namedPres_surface ρ q u
  let ww := genusW ep aa bb q
  let att := genusAtt ep aa bb q
  let hh := mk_genusW ep aa bb q he
  let base := baseToQuotientW ep ww hh att
  let incl := SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho
  let j := base.comp incl
  have hj  :=
    (baseToQuotientW_injective ep ww hh att).comp
      (SurfaceWordExpansion.groupEquiv ρ u (finitePairs q) hrho).injective
  letI : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩
  obtain ⟨T, _⟩ := exists_spanningTree_qOld
    (posQCube (gBase q))
  let recv := (blockToQW ww att (gBase q) [] T (genus_hcb ep aa bb q)).comp
    (pi1Conj (T.treePath_isPath (posQCube (gBase q))))
  apply markedSpine_substitution_injective q ρ (fun _ => u)
    (fun s => by cases s; exact hrho) j hj (fun _ => recv)
  intro s x
  rw [spineMarkedLoop_toOld_class]
  change blockToQW ww att (gBase q) [] T (genus_hcb ep aa bb q)
    (SpanningTree.loopOf T (isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2)))) = _
  rw [blockToQW_surfLoop ww att (gBase q) [] T (genus_hcb ep aa bb q)
    (isPath_gSig q (x.1.val, x.2))]
  let lw := finiteLw aa bb q PUnit.unit
  have hbase : pi1Conj (genus_hcb ep aa bb q)
      (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) (gSig q (x.1.val, x.2)),
        isPath_mapPath _ (isPath_gSig q (x.1.val, x.2))⟩) =
      alphaHomW ep ww hh (QuotientGroup.mk (FreeGroup.mk (lw x))) := by
    rw [alphaHomW_mk, alphaFree_mk]
    exact Quotient.sound (genus_hread ep aa bb q PUnit.unit.{1} (x.1.val, x.2))
  rw [hbase]
  have hnames : FreeGroup.mk (lw x) = FreeGroup.of (Sum.inr x) := by
    rw [show lw x = [(Sum.inr x, true)] from namedLw_eq q PUnit.unit x]
    rfl
  rw [hnames]
  exact congrArg base (SurfaceWordExpansion.name_eq_word ρ u (finitePairs q) x)

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)

def familyFiniteSpineWordBlock (s : Sx) :
    NamedSpineRel (q s) → FreeGroup (α ⊕ SpinePresentationGen (q s)) :=
  finiteSpineWordBlock (q s) (u s) PUnit.unit

variable (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

include hrho in
/-- Each replaced word follows from its own genuine finite spine relators. -/
theorem familyFiniteSpineWordBlock_consequence (s : Sx) :
    FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s))) (ρ (Sum.inr s)) ∈
      Subgroup.normalClosure (Set.range (familyFiniteSpineWordBlock q u s)) := by
  let φ := blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
    (fun _ => u s) PUnit.unit
  have hv : φ (commWord (fun x => FreeGroup.of (Sum.inl x)) (finitePairs (q s))) =
      FreeGroup.map (Sum.inl) (ρ (Sum.inr s)) := by
    rw [map_commWord]
    simp only [φ, blockSubst_of_inl]
    rw [← map_commWord, hrho s]
  rw [← hv]
  apply map_mem_normalClosure φ ?_ (markedSpine_surface_mem (q s))
  rintro v ⟨m, rfl⟩
  exact Subgroup.subset_normalClosure ⟨m, rfl⟩

include hrho in
theorem familyFiniteSpineWordBlock_filled : FilledF ρ (familyFiniteSpineWordBlock q u) :=
  filledF_of_block_consequences ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_consequence ρ q u hrho)

/-- The actual finite-spine structural inclusion is injective for every family,
including infinite families and independently varying genera. -/
theorem familyFiniteSpineWordBlock_injective : Function.Injective
    (substHomF ρ (familyFiniteSpineWordBlock q u)
      (familyFiniteSpineWordBlock_filled ρ q u hrho)) := by
  apply injective_substHomF_of_individual ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho)
    (fun s => finiteSpineWordBlock_filled (oneRel ρ s) (q s) (u s) (hrho s))
  intro s
  exact finiteSpineWordBlock_injective (oneRel ρ s) (q s) (u s) (hrho s)

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def cappedSpineCx : Complex2 where
  V := (markedSpineCx q).V
  E := (markedSpineCx q).E
  F := (markedSpineCx q).F ⊕ (Fin q × Bool)
  src := (markedSpineCx q).src
  tgt := (markedSpineCx q).tgt
  base := Sum.elim (markedSpineCx q).base (fun _ => markedSpineBase q)
  att := Sum.elim (markedSpineCx q).att (fun x => (markedSpineLoop q x).1)
  att_isLoop := by
    rintro (f | x)
    · exact (markedSpineCx q).att_isLoop f
    · exact (markedSpineLoop q x).2


def cappedSpineTree : SpanningTree (cappedSpineCx q) where
  root := (markedSpineTree q).root
  ht := (markedSpineTree q).ht
  isTree := (markedSpineTree q).isTree
  up := (markedSpineTree q).up
  ht_root := (markedSpineTree q).ht_root
  ht_eq_zero := (markedSpineTree q).ht_eq_zero
  up_src := (markedSpineTree q).up_src
  up_ht := (markedSpineTree q).up_ht
  isTree_iff := (markedSpineTree q).isTree_iff

/-- The capped presentation is precisely the cell presentation of the capped complex. -/
theorem cappedSpineTree_rel :
    SpanningTree.treeRel (cappedSpineTree q) = cappedSpinePresentation q := by
  funext f
  cases f <;> rfl

def cappedSpineIncl : Hom (markedSpineCx q) (cappedSpineCx q) where
  onV := id
  onE := id
  onF := Sum.inl
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    change (markedSpineCx q).att f = List.map (fun eb : (markedSpineCx q).E × Bool => (eb.1, eb.2))
      ((markedSpineCx q).att f)
    simp

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P → Q) (S : Set Q)

def posetCoverRestriction : {p : P // f p ∈ S} → S := fun p => ⟨f p.1, p.2⟩

theorem IsPosetCover.restriction (hf : IsPosetCover f) :
    IsPosetCover (posetCoverRestriction f S) := by
  refine ⟨fun _ _ h => hf.mono h, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨p, hp⟩ := hf.surj q.1
    refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
    rw [hp]
    exact q.2
  · intro a q h
    obtain ⟨b, ⟨hab, hfb⟩, huniq⟩ := hf.up a.1 q.1 h
    have hb : f b ∈ S := by rw [hfb]; exact q.2
    refine ⟨⟨b, hb⟩, ⟨hab, Subtype.ext hfb⟩, ?_⟩
    intro c hc
    exact Subtype.ext (huniq c.1 ⟨hc.1, congrArg Subtype.val hc.2⟩)
  · intro a q h
    obtain ⟨b, ⟨hba, hfb⟩, huniq⟩ := hf.down a.1 q.1 h
    have hb : f b ∈ S := by rw [hfb]; exact q.2
    refine ⟨⟨b, hb⟩, ⟨hba, Subtype.ext hfb⟩, ?_⟩
    intro c hc
    exact Subtype.ext (huniq c.1 ⟨hc.1, congrArg Subtype.val hc.2⟩)

end FiniteChains.Comb

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]
  {f : P → Q}

theorem postcompose_orderIso (hf : IsPosetCover f) (e : Q ≃o R) :
    IsPosetCover (fun p => e (f p)) where
  mono := e.monotone.comp hf.mono
  surj := e.surjective.comp hf.surj
  up a r har := by
    have ha : f a ≤ e.symm r := by
      simpa only [OrderIso.symm_apply_apply] using e.symm.monotone har
    obtain ⟨b, ⟨hab, hfb⟩, hu⟩ := hf.up a (e.symm r) ha
    refine ⟨b, ⟨hab, by rw [hfb, e.apply_symm_apply]⟩, ?_⟩
    rintro c ⟨hac, hec⟩
    apply hu c
    exact ⟨hac, by simpa only [OrderIso.symm_apply_apply] using congrArg e.symm hec⟩
  down a r hra := by
    have ha : e.symm r ≤ f a := by
      simpa only [OrderIso.symm_apply_apply] using e.symm.monotone hra
    obtain ⟨b, ⟨hba, hfb⟩, hu⟩ := hf.down a (e.symm r) ha
    refine ⟨b, ⟨hba, by rw [hfb, e.apply_symm_apply]⟩, ?_⟩
    rintro c ⟨hca, hec⟩
    apply hu c
    exact ⟨hca, by simpa only [OrderIso.symm_apply_apply] using congrArg e.symm hec⟩

end FiniteChains.Comb.IsPosetCover

namespace FiniteChains.Comb
universe u
variable {P T R : Type u} [PartialOrder P] [PartialOrder R] {S : T → P → Prop}

def coneAdjBaseSet : Set (ConeAdj S) := Set.range (ConeAdj.inc (S := S))

theorem coneAdjBaseSet_down_closed {p q : ConeAdj S}
    (hq : q ∈ coneAdjBaseSet) (hpq : p ≤ q) : p ∈ coneAdjBaseSet := by
  obtain ⟨r, rfl⟩ := hq
  cases p with
  | inl p => exact ⟨p, rfl⟩
  | inr t => exact hpq.elim

def coneAdjBaseOrderIso : coneAdjBaseSet (S := S) ≃o P where
  toFun q := Classical.choose q.2
  invFun p := ⟨ConeAdj.inc p, ⟨p, rfl⟩⟩
  left_inv q := Subtype.ext (Classical.choose_spec q.2)
  right_inv p := Sum.inl.inj (Classical.choose_spec
    (show ConeAdj.inc (S := S) p ∈ coneAdjBaseSet from ⟨p, rfl⟩))
  map_rel_iff' {q r} := by
    change Classical.choose q.2 ≤ Classical.choose r.2 ↔ q.1 ≤ r.1
    have h : ConeAdj.inc (S := S) (Classical.choose q.2) ≤
        ConeAdj.inc (S := S) (Classical.choose r.2) ↔ q.1 ≤ r.1 := by
      rw [Classical.choose_spec q.2, Classical.choose_spec r.2]
    exact h

def coneAdjCoverBaseEnd (f : R → ConeAdj S) :
    {r : R // f r ∈ coneAdjBaseSet} → P :=
  fun r => coneAdjBaseOrderIso ⟨f r.1, r.2⟩

theorem coneAdjCoverBaseEnd_isPosetCover (f : R → ConeAdj S) (hf : IsPosetCover f) :
    IsPosetCover (coneAdjCoverBaseEnd f) :=
  (hf.restriction f coneAdjBaseSet).postcompose_orderIso coneAdjBaseOrderIso

omit [PartialOrder R] in
theorem coneAdjCoverBaseEnd_spec (f : R → ConeAdj S)
    (r : {r : R // f r ∈ coneAdjBaseSet}) :
    ConeAdj.inc (coneAdjCoverBaseEnd f r) = f r.1 := Classical.choose_spec r.2

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}

def chain0 (f : Hom X Y) : (X.V →₀ ℤ) →ₗ[ℤ] (Y.V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ f.onV

/-- Actual cellular maps commute with the edge-to-vertex boundary. -/
theorem bdry1_chain1 (f : Hom X Y) (z : X.E →₀ ℤ) :
    bdry1 Y (chain1 f z) = chain0 f (bdry1 X z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single e n =>
      change bdry1 Y (Finsupp.mapDomain f.onE (Finsupp.single e n)) = _
      rw [Finsupp.mapDomain_single, bdry1_single, bdry1_single, map_smul, map_sub]
      simp [chain0, f.src_onE, f.tgt_onE]

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : StrictMono f) (c : Q) (hc : ∀ x, f x < c)

def strictTopConeEdgeTriangle (e : (strictOrderCx P).E) : (strictOrderCx Q).F :=
  ⟨(f e.1.1, f e.1.2, c), hf e.2, hc _⟩

def strictTopConeEdgeChain : ((strictOrderCx P).E →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx Q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (strictTopConeEdgeTriangle f hf c hc e) 1)

def strictTopConeRadialEdge (x : P) : (strictOrderCx Q).E := ⟨(f x, c), hc x⟩

def strictTopConeRadialChain : (P →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx Q).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => Finsupp.single (strictTopConeRadialEdge f c hc x) 1)


theorem strictTopConeEdgeChain_boundary (z : (strictOrderCx P).E →₀ ℤ) :
    bdry2 (strictOrderCx Q) (strictTopConeEdgeChain f hf c hc z) =
      chain1 (strictOrderCxMap f hf) z +
        strictTopConeRadialChain f c hc (bdry1 (strictOrderCx P) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add, map_add]; abel
  | single e n =>
      rw [strictTopConeEdgeChain, Finsupp.linearCombination_single, map_smul,
        (show bdry2 (strictOrderCx Q) (Finsupp.single (strictTopConeEdgeTriangle f hf c hc e) 1) =
      Finsupp.single ((strictOrderCxMap f hf).onE e) 1 +
        Finsupp.single (strictTopConeRadialEdge f c hc e.1.2) 1 -
        Finsupp.single (strictTopConeRadialEdge f c hc e.1.1) 1 by
          simp [bdry2, strictTopConeEdgeTriangle, strictTopConeRadialEdge,
            strictOrderCx, strictOrderCxMap, pathChain]
          abel)]
      change _ = Finsupp.mapDomain (strictOrderCxMap f hf).onE (Finsupp.single e n) + _
      rw [Finsupp.mapDomain_single]
      simp [strictTopConeRadialChain, bdry1, smul_add, smul_sub]
      abel

/-- Every mapped strict edge cycle has an explicit nondegenerate upper-cone filling. -/
theorem strictTopConeEdgeChain_cycle_boundary (z : (strictOrderCx P).E →₀ ℤ)
    (hz : bdry1 (strictOrderCx P) z = 0) :
    bdry2 (strictOrderCx Q) (strictTopConeEdgeChain f hf c hc z) =
      chain1 (strictOrderCxMap f hf) z := by
  rw [strictTopConeEdgeChain_boundary, hz, map_zero, add_zero]

/-- Every triangle of the upper fan ends at its actual cone vertex. -/
theorem strictTopConeEdgeChain_eq_zero_off_top (z : (strictOrderCx P).E →₀ ℤ)
    (t : (strictOrderCx Q).F) (ht : t.1.2.2 ≠ c) :
    strictTopConeEdgeChain f hf c hc z t = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single e n =>
      have hne : strictTopConeEdgeTriangle f hf c hc e ≠ t := by
        intro h
        exact ht (congrArg (fun a : (strictOrderCx Q).F => a.1.2.2) h).symm
      simp [strictTopConeEdgeChain, hne]

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : StrictMono f) (c : Q) (hc : ∀ x, f x < c)

def strictTopConeTriangleTetrahedron (t : (strictOrderCx P).F) : StrictOrdTet Q :=
  ⟨(f t.1.1, f t.1.2.1, f t.1.2.2, c), hf t.2.1, hf t.2.2, hc _⟩

def strictTopConeTriangleChain : ((strictOrderCx P).F →₀ ℤ) →ₗ[ℤ] (StrictOrdTet Q →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (strictTopConeTriangleTetrahedron f hf c hc)

/-- The sign of the upper cone is fixed by the actual alternating tetrahedron boundary. -/

theorem strictTopConeTriangleChain_boundary (z : (strictOrderCx P).F →₀ ℤ) :
    strictOrdBoundary3 (strictTopConeTriangleChain f hf c hc z) =
      strictTopConeEdgeChain f hf c hc (bdry2 (strictOrderCx P) z) - chain2 (strictOrderCxMap f hf) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add, map_add]; abel
  | single t n =>
      change strictOrdBoundary3 (Finsupp.mapDomain (strictTopConeTriangleTetrahedron f hf c hc)
        (Finsupp.single t n)) = _
      rw [Finsupp.mapDomain_single, strictOrdBoundary3, Finsupp.linearCombination_single,
        (show strictOrdTetBoundary (strictTopConeTriangleTetrahedron f hf c hc t) =
      strictTopConeEdgeChain f hf c hc (bdry2 (strictOrderCx P) (Finsupp.single t 1)) -
        Finsupp.single ((strictOrderCxMap f hf).onF t) 1 by
          rw [bdry2_single]
          simp
          simp only [pathChain, strictOrderCx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          simp [map_add, map_neg, Finsupp.linearCombination_single, strictOrdTetBoundary, strictTopConeTriangleTetrahedron, strictTopConeEdgeChain, strictTopConeEdgeTriangle,
            bdry2, strictOrderCx, strictOrderCxMap, pathChain]
          erw [map_add, map_add, map_neg]
          erw [Finsupp.linearCombination_single,
            Finsupp.linearCombination_single, Finsupp.linearCombination_single]
          simp
          abel), smul_sub]
      change _ = _ - Finsupp.mapDomain (strictOrderCxMap f hf).onF (Finsupp.single t n)
      rw [Finsupp.mapDomain_single]
      simp [bdry2]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : StrictMono f) (c : Q) (hc : ∀ x, f x < c) (hfi : Function.Injective f)

include hfi in
theorem strictTopConeEdgeTriangle_injective :
    Function.Injective (strictTopConeEdgeTriangle f hf c hc) := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext
  · exact hfi (congrArg (fun t : (strictOrderCx Q).F => t.1.1) h)
  · exact hfi (congrArg (fun t : (strictOrderCx Q).F => t.1.2.1) h)

theorem strictTopConeEdgeChain_eq_mapDomain (z : (strictOrderCx P).E →₀ ℤ) :
    strictTopConeEdgeChain f hf c hc z =
      Finsupp.mapDomain (strictTopConeEdgeTriangle f hf c hc) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, Finsupp.mapDomain_add, hz, hw]
  | single e n => simp [strictTopConeEdgeChain]

include hfi in
theorem strictTopConeEdgeChain_injective :
    Function.Injective (strictTopConeEdgeChain f hf c hc) := by
  intro z w h
  rw [strictTopConeEdgeChain_eq_mapDomain, strictTopConeEdgeChain_eq_mapDomain] at h
  exact Finsupp.mapDomain_injective (strictTopConeEdgeTriangle_injective f hf c hc hfi) h

include hfi in
theorem strictTopConeTriangleTetrahedron_injective :
    Function.Injective (strictTopConeTriangleTetrahedron f hf c hc) := by
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact hfi (congrArg (fun a : StrictOrdTet Q => a.1.1) h)
  · apply Prod.ext
    · exact hfi (congrArg (fun a : StrictOrdTet Q => a.1.2.1) h)
    · exact hfi (congrArg (fun a : StrictOrdTet Q => a.1.2.2.1) h)

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- The actual triangle over an actual edge in the strict lower interval. -/
def strictConeTriangle (v : P) (e : StrictOrdEdge (StrictBelow v)) : StrictOrdTri P :=
  ⟨(e.1.1.val, e.1.2.val, v), e.2, e.1.2.property⟩

/-- Extracting a link preserves each genuine cone-triangle coefficient. -/
theorem strictTopLinkChain_apply (v : P) (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictBelow v)) :
    strictTopLinkChain v c e = c (strictConeTriangle v e) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    rcases t with ⟨⟨a, b, z⟩, hab, hbz⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · subst z
      simp [strictTopLinkChain, strictTopLinkTriangle, strictConeTriangle,
        Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictBelow,
        Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictTopLinkChain, strictTopLinkTriangle, ht, strictConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictBelow]

theorem strictOrderCxMap_onE_injective {Q : Type u} [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f) :
    Function.Injective (strictOrderCxMap f hf).onE := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext
  · apply hi
    exact congrArg (fun t : StrictOrdEdge Q => t.1.1) h
  · apply hi
    exact congrArg (fun t : StrictOrdEdge Q => t.1.2) h

/-- An actual injective strict cellular map preserves its edge coefficients. -/
theorem strictOrderCxMap_chain1_apply {Q : Type u} [PartialOrder Q]
    (f : P → Q) (hf : StrictMono f) (hi : Function.Injective f)
    (c : StrictOrdEdge P →₀ ℤ) (e : StrictOrdEdge P) :
    chain1 (strictOrderCxMap f hf) c ((strictOrderCxMap f hf).onE e) = c e := Finsupp.mapDomain_apply_of_injective (strictOrderCxMap_onE_injective f hf hi) c e

/-- An actual order isomorphism induces an equivalence of actual strict edges. -/
def strictOrderEdgeEquiv {Q : Type u} [PartialOrder Q] (e : P ≃o Q) :
    StrictOrdEdge P ≃ StrictOrdEdge Q where
  toFun := (strictOrderCxMap e e.strictMono).onE
  invFun := (strictOrderCxMap e.symm e.symm.strictMono).onE
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [strictOrderCxMap]
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [strictOrderCxMap]

end FiniteChains.Comb
end

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (S : Set P)

def strictSubposetIncl : Hom (strictOrderCx S) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

theorem strictSubposetIncl_onE_injective :
    Function.Injective (strictSubposetIncl S).onE := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun e : StrictOrdEdge P => e.1.1) h
  · exact congrArg (fun e : StrictOrdEdge P => e.1.2) h

theorem strictSubposetIncl_onF_injective :
    Function.Injective (strictSubposetIncl S).onF := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun t : StrictOrdTri P => t.1.1) h
  · apply Prod.ext <;> ext
    · exact congrArg (fun t : StrictOrdTri P => t.1.2.1) h
    · exact congrArg (fun t : StrictOrdTri P => t.1.2.2) h

/-- A triangle is in the induced subcomplex exactly when its three vertices lie in it. -/
theorem strictSubposetIncl_onF_range (t : StrictOrdTri P) :
    t ∈ Set.range (strictSubposetIncl S).onF ↔
      t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1.1.2, a.1.2.1.2, a.1.2.2.2⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨(⟨t.1.1, ha⟩, ⟨t.1.2.1, hb⟩, ⟨t.1.2.2, hc⟩), t.2⟩,
      Subtype.ext rfl⟩

/-- Every finite chain supported on the actual subcomplex is the image of a finite
chain on that subcomplex. If it is a cycle, its unique lift is a cycle too. -/
theorem exists_strictSubposet_cycle (c : StrictOrdTri P →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri S →₀ ℤ,
      chain2 (strictSubposetIncl S) d = c ∧ bdry2 (strictOrderCx S) d = 0 := by
  let d := Finsupp.comapDomain (strictSubposetIncl S).onF c
    (strictSubposetIncl_onF_injective S).injOn
  have hd : chain2 (strictSubposetIncl S) d = c :=
    Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onF_injective S) c
      (fun t ht => (strictSubposetIncl_onF_range S t).mpr (hs t ht))
  refine ⟨d, hd, ?_⟩
  apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective S)
  change chain1 (strictSubposetIncl S) (bdry2 (strictOrderCx S) d) =
    Finsupp.mapDomain _ 0
  rw [Finsupp.mapDomain_zero, ← bdry2_chain2, hd, hc]

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))

theorem presPos_apex_maximal (j : J) (p : PresPos w) (hp : apexOf w j ≤ p) :
    p = apexOf w j := by
  cases p with
  | inl p => exact hp.elim
  | inr k => exact congrArg Sum.inr hp.symm

theorem presCover_apex_maximal (f : P → PresPos w) (hf : IsPosetCover f)
    (v : P) (j : J) (hv : f v = apexOf w j) : ∀ p, v ≤ p → p = v := by
  intro p hp
  have hfp := hf.mono hp
  rw [hv] at hfp
  have he := presPos_apex_maximal w j (f p) hfp
  exact hf.up_inj hp (le_refl v) (he.trans hv.symm)

/-- The actual coefficients around every lifted relator apex form a genuine link one-cycle. -/
theorem presCover_cone_link_cycle (f : P → PresPos w) (hf : IsPosetCover f)
    (v : P) (j : J) (hv : f v = apexOf w j)
    (c : StrictOrdTri P →₀ ℤ) (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    Comb.bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) = 0 :=
  strictTopLink_cycle v (presCover_apex_maximal w f hf v j hv) c hc

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (v : P) (j : J) (hv : f v = apexOf w j)

/-- The actual attaching circle is the lower interval of each lifted relator apex. -/
def presCoverConeCircleOrderIso : StrictBelow v ≃o RelatorCircle w j :=
  (hf.lowerIntervalOrderIso v).trans
    ((strictBelowCongr hv).trans (relatorCircleOrderIso w j).symm)

def presCoverConeCircleHom :
    Hom (strictOrderCx (StrictBelow v)) (strictOrderCx (RelatorCircle w j)) :=
  strictOrderCxMap (presCoverConeCircleOrderIso w f hf v j hv)
    (presCoverConeCircleOrderIso w f hf v j hv).strictMono

def presCoverConeCircleChain (c : StrictOrdTri P →₀ ℤ) :
    StrictOrdEdge (RelatorCircle w j) →₀ ℤ :=
  chain1 (presCoverConeCircleHom w f hf v j hv) (strictTopLinkChain v c)

/-- Actual presentation-cover two-cycles yield actual finite attaching-circle one-cycles. -/
theorem presCoverConeCircleChain_cycle (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j))
      (presCoverConeCircleChain w f hf v j hv c) = 0 := by grind [bdry1_chain1, presCover_cone_link_cycle, map_zero, presCoverConeCircleChain]

/-- The transported circle coefficient is the coefficient of the genuine lifted triangle. -/
theorem presCoverConeCircleChain_apply (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictBelow v)) :
    presCoverConeCircleChain w f hf v j hv c
      ((presCoverConeCircleHom w f hf v j hv).onE e) =
        c (strictConeTriangle v e) := by
  exact (strictOrderCxMap_chain1_apply
    (presCoverConeCircleOrderIso w f hf v j hv)
    (presCoverConeCircleOrderIso w f hf v j hv).strictMono
    (presCoverConeCircleOrderIso w f hf v j hv).injective
    (strictTopLinkChain v c) e).trans (strictTopLinkChain_apply v c e)

/-- One actual coefficient determines all triangles at a lifted relator apex in a two-cycle. -/
theorem presCoverConeTriangles_eq_of_first_coefficient
    (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (hpos : 0 < (w j).length)
    (he : presCoverConeCircleChain w f hf v j hv c
      (relatorCircleEdge0 w j ⟨0, hpos⟩) =
        presCoverConeCircleChain w f hf v j hv d
          (relatorCircleEdge0 w j ⟨0, hpos⟩))
    (e : StrictOrdEdge (StrictBelow v)) :
    c (strictConeTriangle v e) = d (strictConeTriangle v e) := by
  have hcd := relatorCircle_cycle_ext w j
    (presCoverConeCircleChain w f hf v j hv c)
    (presCoverConeCircleChain w f hf v j hv d)
    (presCoverConeCircleChain_cycle w f hf v j hv c hc)
    (presCoverConeCircleChain_cycle w f hf v j hv d hd) hpos he
  have heq := congrArg
    (fun z => z ((presCoverConeCircleHom w f hf v j hv).onE e)) hcd
  simpa only [presCoverConeCircleChain_apply] using heq

end FiniteChains.PresModel
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

def roseDimension : Rose α → ℕ
  | Rose.base => 1
  | Rose.mid _ => 1
  | Rose.edg _ _ => 2

theorem roseDimension_monotone : Monotone (roseDimension (α := α)) := by
  intro x y h
  change Rose.le x y at h
  cases x <;> cases y <;> simp_all [Rose.le, roseDimension]

theorem roseDimension_strictMono : StrictMono (roseDimension (α := α)) := by
  intro x y h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  change Rose.le x y at hl
  cases x <;> cases y <;> simp_all [Rose.le, roseDimension]

def circleDimension (w : J → List (α × Bool)) (x : TCirc w) : ℕ := by
  classical
  exact if x.2.1 < (w x.1).length ∧
    (x.2.2 = CPos.cedgL ∨ x.2.2 = CPos.cedgR) then 1 else 0

theorem circleDimension_le_one (w : J → List (α × Bool)) (x : TCirc w) :
    circleDimension w x ≤ 1 := by
  unfold circleDimension
  split <;> omega

theorem circleDimension_strictMono (w : J → List (α × Bool)) :
    StrictMono (circleDimension w) := by
  intro x y h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  rcases hl with he | hl
  · simp_all
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk, htags⟩ := hl
  subst j'
  rcases htags with ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ <;>
    subst t <;> subst t' <;> simp [circleDimension, hk]


def cylinderDimension (w : J → List (α × Bool)) : CylBase w → ℕ :=
  Sum.elim roseDimension (circleDimension w)

theorem cylinderDimension_strictMono (w : J → List (α × Bool)) :
    StrictMono (cylinderDimension w) := by
  intro p q h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      exact roseDimension_strictMono (lt_of_le_of_ne hl (by
        intro he; exact hn (congrArg Sum.inl he)))
    | inr q => exact hl.elim
  | inr p =>
    cases q with
    | inl q =>
      exact (show circleDimension w p < roseDimension (aFun w p) by
        obtain ⟨j, k, t⟩ := p
        by_cases hk : k < (w j).length
        · obtain ⟨p, hp⟩ := exists_get_of_lt w hk
          cases t <;> simp_all [circleDimension, aFun, roseDimension]
        · have hp : (w j)[k]? = none := List.getElem?_eq_none (by omega)
          cases t <;> simp_all [circleDimension, aFun, roseDimension]).trans_le (roseDimension_monotone hl)
    | inr q =>
      exact circleDimension_strictMono w (lt_of_le_of_ne hl (by
        intro he; exact hn (congrArg Sum.inr he)))

def presPosDimension (w : J → List (α × Bool)) : PresPos w → ℕ :=
  Sum.elim (cylinderDimension w) (fun _ => 2)

theorem presPosDimension_le_two (w : J → List (α × Bool)) (p : PresPos w) :
    presPosDimension w p ≤ 2 := by
  cases p with
  | inl p =>
    cases p with
    | inl r => cases r <;> simp [presPosDimension, cylinderDimension, roseDimension]
    | inr c => exact (circleDimension_le_one w c).trans (by decide)
  | inr j => exact le_refl _

theorem presPosDimension_strictMono (w : J → List (α × Bool)) :
    StrictMono (presPosDimension w) := by
  intro p q h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      exact cylinderDimension_strictMono w (lt_of_le_of_ne hl (by
        intro he; exact hn (congrArg Sum.inl he)))
    | inr j =>
      obtain ⟨r, hr, hpr⟩ := hl
      obtain ⟨k, t, _, he⟩ := hr
      subst r
      have hm := (cylinderDimension_strictMono w).monotone hpr
      have hb := circleDimension_le_one w (TCirc.pt w j k t)
      change cylinderDimension w p < 2
      change cylinderDimension w p ≤ circleDimension w (TCirc.pt w j k t) at hm
      omega
  | inr j =>
    cases q with
    | inl q => exact hl.elim
    | inr k => exact (hn (congrArg Sum.inr hl)).elim

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

theorem rose_strict_triangles_empty : IsEmpty (StrictOrdTri (Rose α)) := by
  refine ⟨fun t => ?_⟩
  have h01 := roseDimension_strictMono t.2.1
  have h12 := roseDimension_strictMono t.2.2
  have hlo : 1 ≤ roseDimension t.1.1 := by cases t.1.1 <;> simp [roseDimension]
  have hhi : roseDimension t.1.2.2 ≤ 2 := by cases t.1.2.2 <;> simp [roseDimension]
  omega

theorem cylinder_strict_three_flags_empty (w : J → List (α × Bool)) :
    IsEmpty (StrictOrdTet (CylBase w)) := by
  refine ⟨fun t => ?_⟩
  have h01 := cylinderDimension_strictMono w t.2.1
  have h12 := cylinderDimension_strictMono w t.2.2.1
  have h23 := cylinderDimension_strictMono w t.2.2.2
  have hb := presPosDimension_le_two w (ConeAdj.inc t.1.2.2.2)
  change cylinderDimension w t.1.2.2.2 ≤ 2 at hb
  omega

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  {f : P → CylBase w} (hf : IsPosetCover f)
include hf

def cylinderCoverCollapse : P → P :=
  hf.upTransform (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w))

theorem cylinderCoverCollapse_monotone : Monotone (cylinderCoverCollapse w hf) :=
  hf.upTransform_monotone _ (cylCollapse_monotone (aHom w)) _

theorem cylinderCoverCollapse_projection (p : P) :
    f (cylinderCoverCollapse w hf p) = cylCollapse (aHom w) (f p) :=
  (hf.upTransform_spec _ _ p).2


theorem cylinderCover_normalized_collapse_triangle_zero (t : OrdTri P) :
    normalizeOrdTriangle
      ((orderCxMap (cylinderCoverCollapse w hf)
        (cylinderCoverCollapse_monotone w hf)).onF t) = 0 := by
  unfold normalizeOrdTriangle
  split
  · rename_i h
    have h01 := hf.strictMono h.1
    have h12 := hf.strictMono h.2
    change f (cylinderCoverCollapse w hf t.1.1) <
      f (cylinderCoverCollapse w hf t.1.2.1) at h01
    change f (cylinderCoverCollapse w hf t.1.2.1) <
      f (cylinderCoverCollapse w hf t.1.2.2) at h12
    rw [cylinderCoverCollapse_projection w hf, cylinderCoverCollapse_projection w hf] at h01 h12
    exact False.elim ((rose_strict_triangles_empty).false ⟨(cylRetr (aHom w) (f t.1.1),
      cylRetr (aHom w) (f t.1.2.1), cylRetr (aHom w) (f t.1.2.2)), h01, h12⟩)
  · rfl

theorem cylinderCover_normalized_collapse_zero (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 (cylinderCoverCollapse w hf)
      (cylinderCoverCollapse_monotone w hf) c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => simp_all
  | single t n =>
    rw [normalizedStrictChain2_single, cylinderCover_normalized_collapse_triangle_zero,
      smul_zero]

/-- The genuine preimage of the presentation cylinder has no strict two-cycles
in any actual covering poset. -/
theorem cylinderCover_two_cycle_zero (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) : c = 0 := by
  obtain ⟨y, hy⟩ := strict_cycle_comparable_boundary id (cylinderCoverCollapse w hf)
    monotone_id (cylinderCoverCollapse_monotone w hf)
    (hf.le_upTransform (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w))) c hc
  haveI := (show IsEmpty (StrictOrdTet P) by
    refine ⟨fun t => ?_⟩
    exact (cylinder_strict_three_flags_empty w).false ⟨(f t.1.1, f t.1.2.1, f t.1.2.2.1, f t.1.2.2.2),
      hf.strictMono t.2.1, hf.strictMono t.2.2.1, hf.strictMono t.2.2.2⟩)
  have hy0 : y = 0 := by
    ext t
    exact isEmptyElim t
  rw [hy0, map_zero, cylinderCover_normalized_collapse_zero, normalizedStrictChain2_id,
    zero_sub] at hy
  exact neg_eq_zero.mp hy.symm

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)
include hf

/-- The actual preimage of the cylinder has no strict two-cycles. -/
theorem presCover_cylinder_preimage_cycle_zero
    (c : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hc : Comb.bdry2
      (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) c = 0) : c = 0 :=
  cylinderCover_two_cycle_zero w (coneAdjCoverBaseEnd_isPosetCover f hf) c hc

/-- A genuine presentation-cover cycle whose triangles avoid the relator cone
vertices is zero. Thus relator-cone triangles detect every actual two-cycle. -/
theorem presCover_cycle_zero_of_cylinder_support (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hs : ∀ t ∈ c.support, f t.1.2.2 ∈ coneAdjBaseSet (S := circSet w)) : c = 0 := by
  let S  := {p | f p ∈ coneAdjBaseSet}
  have hsup : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have hlast := hs t ht
    exact ⟨coneAdjBaseSet_down_closed hlast (hf.mono (t.2.1.le.trans t.2.2.le)),
      coneAdjBaseSet_down_closed hlast (hf.mono t.2.2.le), hlast⟩
  obtain ⟨d, hd, hdc⟩ := exists_strictSubposet_cycle S c hsup hc
  have hz  := presCover_cylinder_preimage_cycle_zero w f hf d hdc
  erw [hz, map_zero] at hd
  exact hd.symm

/-- Equality of relator-cone triangle coefficients detects equality of actual cover cycles. -/
theorem presCover_cycles_eq_of_cone_coefficients (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (he : ∀ t, f t.1.2.2 ∉ coneAdjBaseSet (S := circSet w) → c t = d t) : c = d := by
  have hcd : Comb.bdry2 (strictOrderCx P) (c - d) = 0 := by
    erw [map_sub, hc, hd, sub_self]
  have hs : ∀ t ∈ (c - d).support, f t.1.2.2 ∈ coneAdjBaseSet := by
    intro t ht
    by_contra hn
    have hz : (c - d) t = 0 := by simp only [Finsupp.sub_apply, he t hn, sub_self]
    exact (Finsupp.mem_support_iff.mp ht) hz
  exact sub_eq_zero.mp (presCover_cycle_zero_of_cylinder_support w f hf (c - d) hcd hs)

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Actual two-cycles are detected by one genuine coefficient at each lifted relator apex. -/
theorem presCover_cycles_eq_of_first_coefficients
    (hpos : ∀ j, 0 < (w j).length) (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (he : ∀ (v : P) (j : J) (hv : f v = apexOf w j),
      presCoverConeCircleChain w f hf v j hv c
        (relatorCircleEdge0 w j ⟨0, hpos j⟩) =
      presCoverConeCircleChain w f hf v j hv d
        (relatorCircleEdge0 w j ⟨0, hpos j⟩)) : c = d := by
  apply presCover_cycles_eq_of_cone_coefficients w f hf c d hc hd
  intro t ht
  cases hft : f t.1.2.2 with
  | inl x =>
    exfalso
    apply ht
    exact ⟨x, hft.symm⟩
  | inr j =>
    let e : StrictOrdEdge (StrictBelow t.1.2.2) :=
      ⟨(⟨t.1.1, t.2.1.trans t.2.2⟩, ⟨t.1.2.1, t.2.2⟩), t.2.1⟩
    exact presCoverConeTriangles_eq_of_first_coefficient w f hf t.1.2.2 j hft
      c d hc hd (hpos j) (he _ j hft) e

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- Actual lifted relator apices, with their actual relator label. -/
def PresCoverRelator := {p : P × J // f p.1 = apexOf w p.2}

/-- The distinguished actual cone triangle over the first left attaching-circle incidence. -/
def presCoverRelatorTriangle (p : PresCoverRelator w f) : StrictOrdTri P :=
  strictConeTriangle p.1.1
    ((strictOrderEdgeEquiv
      (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)).symm
      (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))

theorem presCoverRelatorTriangle_injective :
    Function.Injective (presCoverRelatorTriangle w f hf hpos) := by
  intro p q he
  have hv  := congrArg (fun t : StrictOrdTri P => t.1.2.2) he
  have hj : p.1.2 = q.1.2 := by
    apply Sum.inr_injective
    exact p.2.symm.trans ((congrArg f hv).trans q.2)
  apply Subtype.ext
  exact Prod.ext hv hj

/-- A genuine finite triangle chain yields a genuine finitely supported relator chain. -/
def presCoverRelatorChain :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (PresCoverRelator w f →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom
    (presCoverRelatorTriangle_injective w f hf hpos)).toIntLinearMap

theorem presCoverRelatorChain_apply (c : StrictOrdTri P →₀ ℤ)
    (p : PresCoverRelator w f) :
    presCoverRelatorChain w f hf hpos c p = c (presCoverRelatorTriangle w f hf hpos p) := rfl

theorem presCoverRelatorChain_circle (c : StrictOrdTri P →₀ ℤ)
    (p : PresCoverRelator w f) :
    presCoverRelatorChain w f hf hpos c p =
      presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c
        (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩) := by
  let e := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)
  have he := presCoverConeCircleChain_apply w f hf p.1.1 p.1.2 p.2 c
    (e.symm (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))
  change _ = c (presCoverRelatorTriangle w f hf hpos p) at he
  rw [presCoverRelatorChain_apply]
  rw [← he]
  change presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c
    (e (e.symm (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))) = _
  rw [e.apply_symm_apply]

/-- The actual relator coordinates detect genuine two-cycles. -/
theorem presCoverRelatorChain_cycle_injective (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (he : presCoverRelatorChain w f hf hpos c = presCoverRelatorChain w f hf hpos d) :
    c = d := by
  apply presCover_cycles_eq_of_first_coefficients w f hf hpos c d hc hd
  intro v j hv
  have h := congrArg (fun z => z (⟨(v, j), hv⟩ : PresCoverRelator w f)) he
  simpa only [presCoverRelatorChain_circle] using h

/-- The genuine strict two-cycle module embeds linearly in actual lifted-relator chains. -/
def presCoverCycleRelatorLinear :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) →ₗ[ℤ] (PresCoverRelator w f →₀ ℤ) :=
  (presCoverRelatorChain w f hf hpos).comp
    (LinearMap.ker (Comb.bdry2 (strictOrderCx P))).subtype

theorem presCoverCycleRelatorLinear_injective :
    Function.Injective (presCoverCycleRelatorLinear w f hf hpos) := by
  intro c d he
  apply Subtype.ext
  exact presCoverRelatorChain_cycle_injective w f hf hpos c.val d.val
    (LinearMap.mem_ker.mp c.property) (LinearMap.mem_ker.mp d.property) he

end FiniteChains.PresModel
end

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem strictBelowCongr_val {a b : P} (h : a = b) (p : StrictBelow a) :
    (strictBelowCongr h p).val = p.val := by
  cases h
  rfl
end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (v : P) (j : J) (hv : f v = apexOf w j)

/-- The actual inverse circle coordinates project to the actual attaching-circle vertex. -/
theorem presCoverConeCircleOrderIso_symm_projection (x : RelatorCircle w j) :
    f ((presCoverConeCircleOrderIso w f hf v j hv).symm x).val = iCirc w x.val := by
  have hx := congrArg (fun y => (relatorCircleOrderIso w j y).val)
    ((presCoverConeCircleOrderIso w f hf v j hv).apply_symm_apply x)
  change (relatorCircleOrderIso w j
    ((relatorCircleOrderIso w j).symm
      (strictBelowCongr hv (hf.lowerIntervalOrderIso v
        ((presCoverConeCircleOrderIso w f hf v j hv).symm x))))).val =
    (relatorCircleOrderIso w j x).val at hx
  rw [OrderIso.apply_symm_apply, strictBelowCongr_val] at hx
  exact hx

/-- The actual first incidence triangle of a nonempty presentation relator. -/
def presRelatorFirstTriangle (hpos : ∀ j, 0 < (w j).length) (j : J) :
    StrictOrdTri (PresPos w) :=
  strictConeTriangle (apexOf w j)
    ((strictOrderEdgeEquiv (relatorCircleOrderIso w j))
      (relatorCircleEdge0 w j ⟨0, hpos j⟩))

/-- The coordinate triangle lies over the genuine first relator incidence triangle. -/
theorem presCoverRelatorTriangle_projection (hpos : ∀ j, 0 < (w j).length)
    (p : PresCoverRelator w f) :
    (strictOrderCxMap f hf.strictMono).onF (presCoverRelatorTriangle w f hf hpos p) =
      presRelatorFirstTriangle w hpos p.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · exact presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2
      (relatorCirclePoint w p.1.2 ⟨0, hpos p.1.2⟩ CPos.cor)
  · apply Prod.ext
    · exact presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2
        (relatorCirclePoint w p.1.2 ⟨0, hpos p.1.2⟩ CPos.cedgL)
    · exact p.2

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- The actual presentation reading homomorphism is surjective by its proved marked section. -/
theorem readingPresW_surjective : Function.Surjective (readingPresW ρ w hw) := by
  intro x
  exact ⟨alphaHomW ρ w hw x, readingPresW_alphaHomW ρ w hw x⟩

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains
namespace Comb

universe u

variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α)

/-! ### The vertices: homotopy classes of edge paths are elements of `G` -/

/-- The class in `G = F/R` of the word spelled by (any representative of) a vertex of the
homotopy-theoretic universal cover. -/
def uvWord : UV (presComplex ρ) PUnit.unit → PresGroup ρ :=
  Quotient.lift (fun p : PathFrom (presComplex ρ) PUnit.unit => presWord ρ p.1)
    (fun _ _ h => presWord_htpy ρ h)

@[simp] theorem uvWord_mk (p : PathFrom (presComplex ρ) PUnit.unit) :
    uvWord ρ (UV.mk p) = presWord ρ p.1 := rfl

/-- Every list of oriented edges is a path of the presentation complex. -/

theorem uvWord_surjective : Function.Surjective (uvWord ρ) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      refine ⟨UV.mk (⟨(w.toWord), isPath_of_subsingleton _ _ _ _ _⟩), ?_⟩
      show presWord ρ w.toWord = _
      unfold presWord
      rw [FreeGroup.mk_toWord]

theorem uvWord_injective : Function.Injective (uvWord ρ) := by
  intro c d h
  induction c using UV.ind with
  | h p =>
    induction d using UV.ind with
    | h q =>
      have hl  := h
      have hpi : (Pi1.mk ⟨p.1, isPath_of_subsingleton _ _ _ _ _⟩)
          = Pi1.mk ⟨q.1, isPath_of_subsingleton _ _ _ _ _⟩ :=
        (pi1PresEquiv ρ).injective hl
      exact Quotient.sound (Quotient.exact hpi)

/-! ### Extending a class by an edge multiplies its word by a generator -/

theorem uvWord_extend_true (i : α) (c : UV (presComplex ρ) PUnit.unit) :
    uvWord ρ (extend (i, true) c) = uvWord ρ c * qof (relSub ρ) i := by
  induction c using UV.ind with
  | h p =>
      have h : endpt (presComplex ρ) PUnit.unit p.1
          = germSrc (presComplex ρ).src (presComplex ρ).tgt (i, true) := Subsingleton.elim _ _
      rw [extend_mk, uvWord_mk, extendP_pos h, uvWord_mk, presWord_append]
      rfl

theorem uvWord_extend_false (i : α) (c : UV (presComplex ρ) PUnit.unit) :
    uvWord ρ (extend (i, false) c) = uvWord ρ c * (qof (relSub ρ) i)⁻¹ := by
  induction c using UV.ind with
  | h p =>
      have h : endpt (presComplex ρ) PUnit.unit p.1
          = germSrc (presComplex ρ).src (presComplex ρ).tgt (i, false) := Subsingleton.elim _ _
      rw [extend_mk, uvWord_mk, extendP_pos h, uvWord_mk, presWord_append]
      congr 1

/-! ### The isomorphism of complexes -/

/-- The map of edges: an edge of the homotopy-theoretic cover is a class `c` together with a
generator, and it goes to the edge `(uvWord c, i)` of the algebraic cover. -/
def uvEdge (E : UE (presComplex ρ) PUnit.unit) : (univCover ρ).E := (uvWord ρ E.1.1, E.1.2)

/-- The map of two-cells. -/
def uvFace (F : UF (presComplex ρ) PUnit.unit) : (univCover ρ).F := (uvWord ρ F.1.1, F.1.2)

/-- **The lift of a word in the two models agree.** -/
theorem map_uLiftPath_pres : ∀ (L : List (α × Bool)) (c : UV (presComplex ρ) PUnit.unit),
    (uLiftPath L c).map (fun Eb => (uvEdge ρ Eb.1, Eb.2)) = liftPath L (uvWord ρ c) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons eb t ih =>
      intro c
      obtain ⟨i, b⟩ := eb
      have h : endV c = germSrc (presComplex ρ).src (presComplex ρ).tgt (i, b) :=
        Subsingleton.elim _ _
      rw [uLiftPath_cons h]
      cases b
      · rw [liftPath_cons_false, List.map_cons, ih (extend (i, false) c),
          uvWord_extend_false]
        have hhead : (uvEdge ρ (liftGerm c (i, false) h).1, (liftGerm c (i, false) h).2)
            = ((uvWord ρ c * (qof (relSub ρ) i)⁻¹, i), false) := by
          show ((uvWord ρ (extend (i, false) c), i), false) = _
          rw [uvWord_extend_false]
        rw [hhead]
      · rw [liftPath_cons_true, List.map_cons, ih (extend (i, true) c), uvWord_extend_true]
        rfl

/-- **The homotopy-theoretic universal cover of a presentation complex is the algebraic
one.**  The cellular map sending the class of a path to the element of `G = F/R` it spells. -/
def presUnivHom : Hom (uCover (presComplex ρ) PUnit.unit) (univCover ρ) where
  onV := uvWord ρ
  onE := uvEdge ρ
  onF := uvFace ρ
  src_onE _ := rfl
  tgt_onE E := by
    show uvWord ρ E.1.1 * qof (relSub ρ) E.1.2 = uvWord ρ (extend (E.1.2, true) E.1.1)
    rw [uvWord_extend_true]
  base_onF _ := rfl
  att_onF F := by
    show liftPath (FreeGroup.toWord (ρ F.1.2)) (uvWord ρ F.1.1)
      = (uLiftPath ((presComplex ρ).att F.1.2) F.1.1).map (fun Eb => (uvEdge ρ Eb.1, Eb.2))
    rw [map_uLiftPath_pres]

/-! ### The cellular map is an isomorphism -/


theorem uvFace_bijective : Function.Bijective (uvFace ρ) := by
  constructor
  · rintro ⟨⟨c, j⟩, hc⟩ ⟨⟨d, j'⟩, hd⟩ hEq
    have h1  := congrArg Prod.fst hEq
    have h2  := congrArg Prod.snd hEq
    subst h2
    exact Subtype.ext (Prod.ext (uvWord_injective ρ h1) rfl)
  · rintro ⟨q, j⟩
    obtain ⟨c, hc⟩ := uvWord_surjective ρ q
    exact ⟨⟨(c, j), Subsingleton.elim _ _⟩, by simp [uvFace, hc]⟩

/-- The two-chains of the two models are identified. -/
theorem chain2_presUnivHom_surjective :
    Function.Surjective (chain2 (presUnivHom ρ)) := by
  intro v
  obtain ⟨u, hu⟩ := Finsupp.mapDomain_surjective (uvFace_bijective ρ).2 v
  exact ⟨u, hu⟩

/-- **A two-chain of the homotopy-theoretic universal cover is a cycle exactly when its image
in the algebraic model is.** -/
theorem mem_pi2_iff_bdry2_eq_zero (u : (uCover (presComplex ρ) PUnit.unit).F →₀ ℤ) :
    u ∈ Pi2 (presComplex ρ) PUnit.unit ↔ bdry2 (univCover ρ) (chain2 (presUnivHom ρ) u) = 0 := by
  rw [bdry2_chain2]
  constructor
  · intro hu
    have : bdry2 (uCover (presComplex ρ) PUnit.unit) u = 0 := hu
    rw [this, map_zero]
  · intro hu
    have hinj : Function.Injective (chain1 (presUnivHom ρ)) :=
      Finsupp.mapDomain_injective (show Function.Bijective (uvEdge ρ) by
        constructor
        · rintro ⟨⟨c, i⟩, hc⟩ ⟨⟨d, i'⟩, hd⟩ hEq
          have h1  := congrArg Prod.fst hEq
          have h2  := congrArg Prod.snd hEq
          subst h2
          exact Subtype.ext (Prod.ext (uvWord_injective ρ h1) rfl)
        · rintro ⟨q, i⟩
          obtain ⟨c, hc⟩ := uvWord_surjective ρ q
          exact ⟨⟨(c, i), Subsingleton.elim _ _⟩, by simp [uvEdge, hc]⟩).1
    exact hinj (by rw [hu, map_zero])

@[simp] theorem presUnivHom_onV : (presUnivHom ρ).onV = uvWord ρ := rfl
@[simp] theorem presUnivHom_onE : (presUnivHom ρ).onE = uvEdge ρ := rfl
@[simp] theorem presUnivHom_onF : (presUnivHom ρ).onF = uvFace ρ := rfl

/-! ### Naturality in an inclusion of presentations -/

section Incl

variable {β K : Type u} [DecidableEq β] {σ : K → FreeGroup β}
variable (f : α → β) (hf : Function.Injective f) (g : J → K)
  (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j))

/-- The word spelled by the image of a path is the image of the word it spells. -/
theorem uvWord_univLiftV (c : UV (presComplex ρ) PUnit.unit) :
    uvWord σ (univLiftV PUnit.unit (presInclHom f hf ρ σ g hg) c)
      = presInclGroupHom f ρ σ g hg (uvWord ρ c) := by
  induction c using UV.ind with
  | h p => rfl

/-- The identification of the two models is natural: it carries the lift of an inclusion of
presentation complexes to the universal covers to the algebraic one. -/
theorem uvFace_univLiftF (F : UF (presComplex ρ) PUnit.unit) :
    uvFace σ (univLiftF (x₀ := PUnit.unit) (presInclHom f hf ρ σ g hg) F)
      = (univCoverInclHom f hf ρ σ g hg).onF (uvFace ρ F) := by
  show (uvWord σ (univLiftV PUnit.unit (presInclHom f hf ρ σ g hg) F.1.1), g F.1.2) = Prod.map (presInclGroupHom f ρ σ g hg) g (uvWord ρ F.1.1, F.1.2)
  rw [uvWord_univLiftV]
  rfl

/-- The two lifts agree on two-chains. -/
theorem chain2_presUnivHom_square (u : (uCover (presComplex ρ) PUnit.unit).F →₀ ℤ) :
    chain2 (presUnivHom σ)
        (chain2 (univLift (presComplex ρ) (presInclHom f hf ρ σ g hg) PUnit.unit) u)
      = chain2 (univCoverInclHom f hf ρ σ g hg) (chain2 (presUnivHom ρ) u) := by
  show Finsupp.mapDomain (uvFace σ)
      (Finsupp.mapDomain ((univLift (presComplex ρ) (presInclHom f hf ρ σ g hg) PUnit.unit).onF) u)
    = Finsupp.mapDomain (univCoverInclHom f hf ρ σ g hg).onF
      (Finsupp.mapDomain (uvFace ρ) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  refine congrArg (fun h => Finsupp.mapDomain h u) ?_
  funext F
  exact uvFace_univLiftF ρ f hf g hg F

/-- **The topological and the algebraic readings of "the inclusion is zero on `π₂`" agree.**
On the left the definition used by the interface of Theorem A (the induced map of two-chains of
the homotopy-theoretic universal covers kills every two-cycle); on the right the condition
carried by `FiniteChains.PresChain`, stated in the algebraic model whose chain complex is the
Fox complex. -/
theorem zeroPi2_presInclHom_iff :
    ZeroPi2 (presInclHom f hf ρ σ g hg) ↔
      ∀ v : (univCover ρ).F →₀ ℤ, bdry2 (univCover ρ) v = 0 →
        chain2 (univCoverInclHom f hf ρ σ g hg) v = 0 := by
  constructor
  · intro hzero v hv
    obtain ⟨u, rfl⟩ := chain2_presUnivHom_surjective ρ v
    have hu  := (mem_pi2_iff_bdry2_eq_zero ρ u).2 hv
    rw [← chain2_presUnivHom_square ρ f hf g hg u, hzero PUnit.unit u hu, map_zero]
  · intro hzero x₀ u hu
    have hinj : Function.Injective (chain2 (presUnivHom σ)) :=
      Finsupp.mapDomain_injective (uvFace_bijective σ).1
    refine hinj ?_
    rw [map_zero, chain2_presUnivHom_square ρ f hf g hg u]
    exact hzero _ ((mem_pi2_iff_bdry2_eq_zero ρ u).1 hu)

/-! ### The same for the fundamental group -/

/-- The word spelled by the image of an edge path. -/
theorem presWord_mapPath (l : List (α × Bool)) :
    presWord σ (mapPath (presInclHom f hf ρ σ g hg) l)
      = presInclGroupHom f ρ σ g hg (presWord ρ l) := rfl

/-- An edge loop of a presentation complex spelling the trivial element of the presented group
is null-homotopic. -/
theorem htpy_of_presWord_eq_one {l : List (β × Bool)} (h : presWord σ l = 1) :
    Htpy (presComplex σ) PUnit.unit PUnit.unit l [] := by
  have hone :
      (Pi1.mk ⟨l, isPath_of_subsingleton _ _ _ _ _⟩ : Pi1 (presComplex σ) PUnit.unit) = 1 := by
    refine (pi1PresEquiv σ).injective ?_
    rw [map_one]
    exact h
  exact Quotient.exact hone

/-- **The topological and the algebraic readings of "the inclusion kills `π₁`" agree.**  The
inclusion of presentation complexes is trivial on fundamental groups exactly when the induced
homomorphism of presented groups is trivial. -/
theorem pi1Trivial_presInclHom_iff :
    Pi1Trivial (presInclHom f hf ρ σ g hg) ↔
      ∀ w : PresGroup ρ, presInclGroupHom f ρ σ g hg w = 1 := by
  constructor
  · intro hpi w
    induction w using QuotientGroup.induction_on with
    | H x =>
        have hht := hpi PUnit.unit x.toWord (isPath_of_subsingleton _ _ _ _ _)
        have hw := presWord_htpy σ hht
        rw [presWord_mapPath, presWord_nil] at hw
        rw [← hw]
        congr 1
        show (QuotientGroup.mk x) = QuotientGroup.mk (FreeGroup.mk x.toWord)
        rw [FreeGroup.mk_toWord]
  · intro hw _ p _
    refine htpy_of_presWord_eq_one ?_
    rw [presWord_mapPath]
    exact hw _

end Incl

end Comb
end FiniteChains
end

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- The reversed actual reflexive order edge is null-homotopic. -/
theorem htpy_ordNegSelf_nil (a : P) :
    Htpy (orderCx P) a a [ordNeg (le_refl a)] [] := by
  have h := htpy_revPath (isPath_ordPos (le_refl a)) (htpy_ordSelf_nil a)
  simp_all

/-- Reflexive edge conjugation does not alter the actual based loop class. -/
theorem htpy_reflexive_conjugation {a : P} (p : List ((orderCx P).E × Bool))
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy (orderCx P) a a ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) p := by
  have h1 := (htpy_ordNegSelf_nil a).congr_append (isPath_nil' a)
    (hp.append (isPath_ordPos (le_refl a)))
  have h2 := (htpy_ordSelf_nil a).congr_append hp (isPath_nil' a)
  have h1' : Htpy (orderCx P) a a
      ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) (p ++ [ordPos (le_refl a)]) := by
    simpa using h1
  have h2' : Htpy (orderCx P) a a (p ++ [ordPos (le_refl a)]) p := by
    simpa using h2
  exact h1'.trans h2'

/-- Order-homotopic actual maps agreeing at the basepoint induce homotopic based loops. -/
theorem htpy_loop_mapPath_le_fixed {Q : Type u} [PartialOrder Q]
    {f g : P → Q} (hf : Monotone f) (hg : Monotone g) (hfg : ∀ x, f x ≤ g x)
    {a : P} (hfix : f a = g a) (p : List ((orderCx P).E × Bool))
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy (orderCx Q) (f a) (f a) (mapPath (orderCxMap f hf) p)
      (mapPath (orderCxMap g hg) p) := by
  have hn := htpy_loop_mapPath_le hf hg hfg hp
  have he : (⟨(f a, g a), hfg a⟩ : OrdEdge Q) = ⟨(f a, f a), le_refl (f a)⟩ :=
    Subtype.ext (Prod.ext rfl hfix.symm)
  change Htpy (orderCx Q) (g a) (g a) (mapPath (orderCxMap g hg) p)
    ([(⟨(f a, g a), hfg a⟩, false)] ++ mapPath (orderCxMap f hf) p ++
      [(⟨(f a, g a), hfg a⟩, true)]) at hn
  rw [he, ← hfix] at hn
  exact (hn.trans (htpy_reflexive_conjugation _ (isPath_mapPath (orderCxMap f hf) hp))).symm

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {X S : Type u} [PartialOrder X] [PartialOrder S] (a : S →o X)

/-- Every actual based cylinder loop is homotopic to its retraction onto the base. -/
theorem cylinder_loop_retraction (x : X)
    (p : List ((orderCx (CylP a)).E × Bool))
    (hp : IsPath (orderCx (CylP a)).src (orderCx (CylP a)).tgt p (cylIn a x) (cylIn a x)) :
    Htpy (orderCx (CylP a)) (cylIn a x) (cylIn a x) p
      (mapPath (orderCxMap (cylIn a) (cylIn_monotone a))
        (mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p)) := by
  have h := htpy_loop_mapPath_le_fixed monotone_id (cylCollapse_monotone a)
    (le_cylIn_cylRetr a) rfl p hp
  have hid : mapPath (orderCxMap id monotone_id) p = p := by
    clear hp h
    induction p with
    | nil => rfl
    | cons e p ih =>
      simp only [mapPath, List.map_cons] at ih ⊢
      exact congrArg (List.cons e) ih
  rw [hid] at h
  simpa only [mapPath, List.map_map, Function.comp_def, orderCxMap, cylCollapse, cylIn, cylRetr, id] using h

/-- The actual base inclusion surjects onto the cylinder fundamental group. -/
theorem cylinder_pi1_surjective (x : X) :
    Function.Surjective (pi1Map (orderCxMap (cylIn a) (cylIn_monotone a)) x) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    refine ⟨Pi1.mk ⟨mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p.val,
      isPath_mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p.property⟩,
      Quotient.sound ?_⟩
    exact (cylinder_loop_retraction a x p.val p.property).symm

end FiniteChains.Comb
