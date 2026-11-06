import RequestProject.PushoutRelativeCopyLabels
import RequestProject.PushoutUniversalCellEmbedding
import RequestProject.PushoutOldCoverHomology
import RequestProject.AcyclicLiftedSubcomplex
import RequestProject.Tac


/-! Actual regular-cover descent in degree two. Every universal-cover
two-cycle is a finite sum of images of genuine cycles in copies of the
universal cover of L. The component filters, fillings and old H2 vanishing
are all constructed in the imported files. Unverified source. -/

noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Comb.PushoutRelativeCopies
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hDconn : IsConnected D) (hL : IsConnected L)
  (d₀ : D.V) (ht : Pi1Trivial i) (hD : IsAcyclic D)
  (hT : IsConnected (target p i hiV hiE))

def oldFaceChains : Submodule ℤ
    (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) where
  carrier := {c | ∀ f, ¬ oldFace p i hiV hiE hiF (i.onV d₀) f → c f = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' hc hd f hf := by simp_all
  smul_mem' n c hc f hf := by simp_all

include hp hr he hf hDconn ht hD hT in
theorem oldFaceChains_cycle_zero
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : c ∈ oldFaceChains p i hiV hiE hiF d₀)
    (hz : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0) : c = 0 := by
  have hzero : ∀ z : UF (target p i hiV hiE)
      (pushV p i (i.onV d₀)) →₀ ℤ,
      (∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k) →
        bdry2 (uCover (target p i hiV hiE) (pushV p i (i.onV d₀))) z = 0 → z = 0 := by
    rw [pushV_of_mem p hiV]
    exact PushoutOldCover.old_two_cycle_zero p hp a hr he hf i hiV hiE hiF
      hDconn d₀ ht hT hD
  apply hzero c _ hz
  intro f hf'
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hf') (hc f hn)

set_option maxHeartbeats 800000 in
include hp hr he hDconn hL ht hD hT in
theorem copy_filter_completion
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0)
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) :
    ∃ z : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ,
      z ∈ Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀)) ∧
      bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) z = 0 ∧
      c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) (i.onV d₀) g) - z ∈
          oldFaceChains p i hiV hiE hiF d₀ := by
  let φ := UniversalCopy.map _ _ g
  let φ2 : (UF L (i.onV d₀) →₀ ℤ) →ₗ[ℤ]
      (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := chain2 φ
  let s := UniversalCopy.vertices _ _ g
  let d := c.filter (faceLabel p i hiV hiE hiF _ · = s)
  have hφE := UniversalCopy.map_injective_E
    _ _
    (PushoutSheets.univLift_edges_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  have hφF := UniversalCopy.map_injective_F
    _ _
    (PushoutSheets.univLift_faces_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  have hd : ∀ f ∉ Set.range φ.onF, d f = 0 := by
    intro f hf'
    have hn := fun hl =>
      hf' (face_range_of_label p i hiV hiE hiF _ hT hL g f hl)
    aesop
  cases' (Finsupp.mem_range_mapDomain_iff φ.onF hφF d).mpr hd with b hb
  change UF L (i.onV d₀) →₀ ℤ at b
  have hb' : φ2 b = d := hb
  have hdr : relativeBoundary p i hiV hiE hiF _ d = 0 := by
    rw [relative_boundary_filter p i hiV hiE hiF _ hT hL]
    have hcr : relativeBoundary p i hiV hiE hiF _ c = 0 := by
      change (bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c).filter _ = 0
      rw [hc, Finsupp.filter_zero]
    rw [hcr, Finsupp.filter_zero]
  have hbs : ∀ e ∈ (Comb.bdry2 (uCover L (i.onV d₀)) b).support, e.val.2 ∈ Set.range i.onE := by
    intro e he'
    by_contra hn
    have hnot :=
      fun hh => hn ((oldEdge_map_iff p i hiV hiE hiF _ g e).mp hh)
    have hcoeff : Comb.bdry2 _ b e = 0 := by
      have hh := congrArg (· (φ.onE e)) hdr
      have hbd := (congrArg (bdry2 (uCover (target p i hiV hiE)
          (root p i hiV hiE hiF (i.onV d₀)))) hb'.symm).trans (bdry2_chain2 φ b)
      change ((bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) d).filter
        (¬ oldEdge p i hiV hiE hiF _ ·))
        (φ.onE e) = 0 at hh
      rw [Finsupp.filter_apply, if_pos hnot, hbd] at hh
      exact (Finsupp.mapDomain_apply_of_injective hφE _ e).symm.trans hh
    simp_all
  obtain ⟨w, hw, hwb⟩ := AcyclicLiftedSubcomplex.one_cycle_filling i hiV hiE hDconn d₀ ht hL hD
    _ hbs (bdry1_bdry2 (X := uCover L (i.onV d₀)) b)
  have hcycle : bdry2 (uCover L (i.onV d₀)) (b - w) = 0 := by simp_all
  refine ⟨φ2 (b - w), UniversalCopy.cycle_image_mem
    (pushoutMap p i hiV hiE hiF) _ g _ hcycle, ?_, ?_⟩
  · change bdry2 _
      (chain2 φ (b - w)) = 0
    rw [bdry2_chain2, hcycle, map_zero]
  · have heq : d - φ2 (b - w) = φ2 w := by simp_all
    rw [heq]
    intro f hf'
    by_contra hn
    have hm := Finsupp.mem_support_iff.mpr hn
    obtain ⟨t, ht', htf⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
    apply hf'
    rw [← htf]
    exact (oldFace_map_iff p i hiV hiE hiF _ g t).mpr (hw t ht')

include hp hr he hf hDconn hL ht hD hT in
/-- The actual finite-support spherical generation statement at the core
base point. No `Pi2GeneratedByUpstairs` or exactness input remains. -/
theorem cycle_mem_span_at_core
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0) :
    c ∈ Submodule.span ℤ
      (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀))) := by
  let label := faceLabel p i hiV hiE hiF (i.onV d₀)
  let S := c.support.image label
  let W := oldFaceChains p i hiV hiE hiF d₀
  let P : Submodule ℤ (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := Submodule.span ℤ
    (Pi2FromSub (pushoutMap p i hiV hiE hiF) _)
  have hpiece (s : {s // s ∈ S}) :
      ∃ z, z ∈ P ∧ bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) z = 0 ∧
        c.filter (label · = s.val) - z ∈ W := by
    by_cases hs : s.val = ∅
    · refine ⟨0, P.zero_mem, map_zero _, ?_⟩
      intro f hf'
      have hn : label f ≠ s.val := by
        rw [hs]
        exact fun hh => hf' ((faceLabel_empty_iff p i hiV hiE hiF _ hT hL f).mp hh)
      simp_all
    · obtain ⟨f, hf', hfs⟩ := Finset.mem_image.mp s.property
      have hfoff : ¬ oldFace p i hiV hiE hiF _ f := by
        intro hh
        exact hs (hfs.symm.trans (faceLabel_empty_of_old p i hiV hiE hiF _ f hh))
      cases' faceLabel_of_not_old p i hiV hiE hiF _ hT hL f hfoff with g hg
      obtain ⟨z, hz, hzc, hzd⟩ := copy_filter_completion p hp a hr he i hiV hiE hiF
        hDconn hL d₀ ht hD hT c hc g
      refine ⟨z, Submodule.subset_span hz, hzc, ?_⟩
      aesop
  choose z hz hzc hzd using hpiece
  let zsum := ∑ s : {s // s ∈ S}, z s
  have hzp : zsum ∈ P := P.sum_mem (fun s _ => hz s)
  have hzb : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) zsum = 0 := by
    simp [zsum, map_sum, hzc, Finset.sum_const_zero]
  have hdiff : c - zsum ∈ W := by
    have hh := W.sum_mem (fun s (_ : s ∈ (Finset.univ : Finset {s // s ∈ S})) => hzd s)
    rw [Finset.sum_sub_distrib] at hh
    have hsum := (S.sum_coe_sort (fun s => c.filter (label · = s))).trans
        (finsupp_sum_label_filters label c)
    grind
  have hzero := oldFaceChains_cycle_zero p hp a hr he hf i hiV hiE hiF
    hDconn d₀ ht hD hT _ hdiff (by simp_all)
  rw [sub_eq_zero.mp hzero]
  exact hzp
