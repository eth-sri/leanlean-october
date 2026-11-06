module

public import RequestProject.PushoutRelativeCopyLabels
public import RequestProject.PushoutUniversalCellEmbedding
public import RequestProject.PushoutOldCoverHomology
public import RequestProject.AcyclicLiftedSubcomplex

@[expose] public section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

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
  zero_mem' _ _ := rfl
  add_mem' hc hd f hf := by simp [hc f hf, hd f hf]
  smul_mem' _ _ hc f hf := by simp [hc f hf]

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
  let φ := UniversalCopy.map (pushoutMap p i hiV hiE hiF) (i.onV d₀) g
  let φ2 : (UF L (i.onV d₀) →₀ ℤ) →ₗ[ℤ]
      (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := chain2 φ
  let s := UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) (i.onV d₀) g
  let d := c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f = s)
  have hφE : Function.Injective φ.onE := UniversalCopy.map_injective_E
    (pushoutMap p i hiV hiE hiF) (i.onV d₀)
    (PushoutSheets.univLift_edges_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  have hφF : Function.Injective φ.onF := UniversalCopy.map_injective_F
    (pushoutMap p i hiV hiE hiF) (i.onV d₀)
    (PushoutSheets.univLift_faces_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff φ.onF hφF d).mpr fun f hf' => by
    simp [d, show faceLabel p i hiV hiE hiF (i.onV d₀) f ≠ s from fun hl =>
      hf' (face_range_of_label p i hiV hiE hiF (i.onV d₀) hT hL g f hl)]
  change UF L (i.onV d₀) →₀ ℤ at b
  have hb' : φ2 b = d := hb
  have hdr : relativeBoundary p i hiV hiE hiF (i.onV d₀) d = 0 := by
    rw [show d = c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f = s) from rfl,
      relative_boundary_filter p i hiV hiE hiF (i.onV d₀) hT hL,
      show relativeBoundary p i hiV hiE hiF (i.onV d₀) c = 0 by
        change (bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c).filter _ = 0
        rw [hc, Finsupp.filter_zero],
      Finsupp.filter_zero]
  have hbs (e) (he' : e ∈ (Comb.bdry2 (uCover L (i.onV d₀)) b).support) :
      e.val.2 ∈ Set.range i.onE := by
    by_contra hn
    have hnot : ¬ oldEdge p i hiV hiE hiF (i.onV d₀) (φ.onE e) :=
      fun hh => hn ((oldEdge_map_iff p i hiV hiE hiF (i.onV d₀) g e).mp hh)
    have hh := congrArg (· (φ.onE e)) hdr
    have hbd : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) d =
        chain1 φ (bdry2 (uCover L (i.onV d₀)) b) :=
      (congrArg (bdry2 (uCover (target p i hiV hiE)
        (root p i hiV hiE hiF (i.onV d₀)))) hb'.symm).trans (bdry2_chain2 φ b)
    change ((bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) d).filter
      (fun e => ¬ oldEdge p i hiV hiE hiF (i.onV d₀) e)) (φ.onE e) = 0 at hh
    rw [Finsupp.filter_apply, if_pos hnot, hbd] at hh
    exact (Finsupp.mem_support_iff.mp he')
      ((Finsupp.mapDomain_apply_of_injective hφE _ e).symm.trans hh)
  obtain ⟨w, hw, hwb⟩ := AcyclicLiftedSubcomplex.one_cycle_filling i hiV hiE hDconn d₀ ht hL hD
    (bdry2 (uCover L (i.onV d₀)) b) hbs (bdry1_bdry2 (X := uCover L (i.onV d₀)) b)
  have hcycle : bdry2 (uCover L (i.onV d₀)) (b - w) = 0 := by rw [map_sub, hwb, sub_self]
  refine ⟨φ2 (b - w), UniversalCopy.cycle_image_mem
    (pushoutMap p i hiV hiE hiF) (i.onV d₀) g (b - w) hcycle,
    by change bdry2 _ (chain2 φ (b - w)) = 0; rw [bdry2_chain2, hcycle, map_zero], ?_⟩
  change d - φ2 (b - w) ∈ oldFaceChains p i hiV hiE hiF d₀
  rw [show d - φ2 (b - w) = φ2 w by rw [map_sub, hb']; abel]
  intro f hf'; by_contra hn
  obtain ⟨t, ht', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hn))
  exact hf' ((oldFace_map_iff p i hiV hiE hiF (i.onV d₀) g t).mpr (hw t ht'))

include hp hr he hf hDconn hL ht hD hT in
theorem cycle_mem_span_at_core
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0) :
    c ∈ Submodule.span ℤ
      (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀))) := by
  let label := faceLabel p i hiV hiE hiF (i.onV d₀)
  let S := c.support.image label
  let W := oldFaceChains p i hiV hiE hiF d₀
  let P : Submodule ℤ (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := Submodule.span ℤ
    (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀)))
  have hpiece (s : {s // s ∈ S}) :
      ∃ z, z ∈ P ∧ bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) z = 0 ∧
        c.filter (fun f => label f = s.val) - z ∈ W := by
    by_cases hs : s.val = ∅
    · refine ⟨0, P.zero_mem, map_zero _, ?_⟩
      rw [sub_zero]; intro f hf'
      simp [show label f ≠ s.val by
        rw [hs]; exact fun hh => hf' ((faceLabel_empty_iff p i hiV hiE hiF (i.onV d₀) hT hL f).mp hh)]
    · obtain ⟨f, hf', hfs⟩ := Finset.mem_image.mp s.property
      obtain ⟨g, hg⟩ := faceLabel_of_not_old p i hiV hiE hiF (i.onV d₀) hT hL f fun hh =>
        hs (hfs.symm.trans (faceLabel_empty_of_old p i hiV hiE hiF (i.onV d₀) f hh))
      obtain ⟨z, hz, hzc, hzd⟩ := copy_filter_completion p hp a hr he i hiV hiE hiF
        hDconn hL d₀ ht hD hT c hc g
      exact ⟨z, Submodule.subset_span hz, hzc, by simpa only [hfs.symm.trans hg] using hzd⟩
  choose z hz hzc hzd using hpiece
  let zsum := ∑ s : {s // s ∈ S}, z s
  have hzb : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) zsum = 0 := by
    simp only [zsum, map_sum, hzc, Finset.sum_const_zero]
  have hdiff : c - zsum ∈ W := by
    have hh := W.sum_mem (fun s (_ : s ∈ (Finset.univ : Finset {s // s ∈ S})) => hzd s)
    rwa [Finset.sum_sub_distrib, (Finset.sum_coe_sort S (fun s => c.filter (fun f => label f = s))).trans
      (finsupp_sum_label_filters label c)] at hh
  have hzero : c - zsum = 0 := by
    have h0 : ∀ z : UF (target p i hiV hiE) (pushV p i (i.onV d₀)) →₀ ℤ,
        (∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k) →
          bdry2 (uCover (target p i hiV hiE) (pushV p i (i.onV d₀))) z = 0 → z = 0 := by
      rw [pushV_of_mem p hiV]
      exact PushoutOldCover.old_two_cycle_zero p hp a hr he hf i hiV hiE hiF hDconn d₀ ht hT hD
    exact h0 _ (fun f hf' => by by_contra hn; exact (Finsupp.mem_support_iff.mp hf') (hdiff f hn))
      (by erw [map_sub, hc, hzb, sub_self])
  rw [sub_eq_zero.mp hzero]
  exact P.sum_mem fun s _ => hz s
