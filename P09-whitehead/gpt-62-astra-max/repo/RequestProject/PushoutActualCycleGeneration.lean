module

public import RequestProject.PushoutRelativeCopyLabels
public import RequestProject.PushoutUniversalCellEmbedding
public import RequestProject.PushoutOldCoverHomology
public import RequestProject.AcyclicLiftedSubcomplex

@[expose] public section

/-! Actual regular-cover descent in degree two. Every universal-cover
two-cycle is a finite sum of images of genuine cycles in copies of the
universal cover of L. The component filters, fillings and old H2 vanishing
are all constructed in the imported files. Unverified source. -/

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
    (UF _ (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) where
  carrier := {c | ∀ f, ¬ oldFace p i hiV hiE hiF _ f → c f = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' hc hd f hf := by simp only [Finsupp.add_apply, hc f hf, hd f hf, add_zero]
  smul_mem' n c hc f hf := by simp only [Finsupp.smul_apply, hc f hf, smul_zero]

variable (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)

include hp hr he hf hDconn ht hD hT in
theorem oldFaceChains_cycle_zero
    (hc : c ∈ oldFaceChains p i hiV hiE hiF d₀)
    (hz : bdry2 (uCover _ _) c = 0) : c = 0 := by
  have hzero : ∀ z : UF (target p i hiV hiE)
      _ →₀ ℤ,
      (∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k) →
        bdry2 (uCover (target p i hiV hiE) (pushV p i (i.onV d₀))) z = 0 → z = 0 := by
    rw [pushV_of_mem p hiV]
    exact PushoutOldCover.old_two_cycle_zero p hp a hr he hf i hiV hiE hiF
      hDconn d₀ ht hT hD
  apply hzero c _ hz
  intro f hf'
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hf') (hc f hn)

variable (hc : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0)
include hc

set_option maxHeartbeats 800000 in
include hp hr he hDconn hL ht hD hT in
theorem copy_filter_completion
    (g : Pi1 _ _) :
    ∃ z : UF _ _ →₀ ℤ,
      z ∈ Pi2FromSub (pushoutMap p i hiV hiE hiF) _ ∧
      bdry2 (uCover _ _) z = 0 ∧
      c.filter (fun f => faceLabel p i hiV hiE hiF _ f =
        UniversalCopy.vertices _ _ g) - z ∈
          oldFaceChains p i hiV hiE hiF d₀ := by
  let φ := UniversalCopy.map _ _ g
  let φ2 : (UF L _ →₀ ℤ) →ₗ[ℤ]
      (UF _ _ →₀ ℤ) := chain2 φ
  let s := UniversalCopy.vertices _ _ g
  let d := c.filter (fun f => faceLabel p i hiV hiE hiF _ f = s)
  have hφE := UniversalCopy.map_injective_E
    _ _
    (PushoutSheets.univLift_edges_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  have hφF := UniversalCopy.map_injective_F
    _ _
    (PushoutSheets.univLift_faces_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  have hd : ∀ f ∉ Set.range φ.onF, d f = 0 := by
    intro f hf'
    have hn := fun hl =>
      hf' (face_range_of_label p i hiV hiE hiF (i.onV d₀) hT hL g f hl)
    aesop
  obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff φ.onF hφF d).mpr hd
  change UF L _ →₀ ℤ at b
  have hb' : φ2 b = d := hb
  have hdr : relativeBoundary p i hiV hiE hiF _ d = 0 := by
    rw [show d = c.filter (fun f => faceLabel p i hiV hiE hiF _ f = s) from rfl,
      relative_boundary_filter p i hiV hiE hiF _ hT hL]
    have hcr : relativeBoundary p i hiV hiE hiF _ c = 0 := by
      change (bdry2 (uCover _ _) c).filter _ = 0
      rw [hc, Finsupp.filter_zero]
    rw [hcr, Finsupp.filter_zero]
  have hbs : ∀ e ∈ (Comb.bdry2 (uCover L _) b).support, e.val.2 ∈ Set.range i.onE := by
    intro e he'
    by_contra hn
    have hcoeff : Comb.bdry2 _ b e = 0 := by
      have hh := congrArg (fun z => z (φ.onE e)) hdr
      have hbd := (congrArg _ hb'.symm).trans (bdry2_chain2 φ b)
      change ((bdry2 (uCover _ _) d).filter
        (fun e => ¬ oldEdge p i hiV hiE hiF _ e))
        _ = 0 at hh
      rw [Finsupp.filter_apply, if_pos (fun hh => hn ((oldEdge_map_iff p i hiV hiE hiF (i.onV d₀) g e).mp hh)), hbd] at hh
      exact (Finsupp.mapDomain_apply_of_injective hφE _ e).symm.trans hh
    exact (Finsupp.mem_support_iff.mp he') hcoeff
  obtain ⟨w, hw, hwb⟩ := AcyclicLiftedSubcomplex.one_cycle_filling i hiV hiE hDconn d₀ ht hL hD
    _ hbs (bdry1_bdry2 (X := uCover L (i.onV d₀)) b)
  have hcycle : bdry2 (uCover L (i.onV d₀)) (b - w) = 0 := by rw [map_sub, hwb, sub_self]
  refine ⟨φ2 _, UniversalCopy.cycle_image_mem
    _ _ g _ hcycle, ?_, ?_⟩
  · change bdry2 _
      (chain2 φ (b - w)) = 0
    rw [bdry2_chain2, hcycle, map_zero]
  · have heq : d - φ2 (b - w) = φ2 w := by rw [map_sub, hb']; abel
    rw [heq]
    intro f hf'
    by_contra hn
    obtain ⟨t, ht', htf⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hn))
    apply hf'
    rw [← htf]
    exact (oldFace_map_iff p i hiV hiE hiF _ g t).mpr (hw t ht')

include hp hr he hf hDconn hL ht hD hT in
/-- The actual finite-support spherical generation statement at the core
base point. No `Pi2GeneratedByUpstairs` or exactness input remains. -/
theorem cycle_mem_span_at_core :
    c ∈ Submodule.span ℤ
      (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀))) := by
  let label := faceLabel p i hiV hiE hiF (i.onV d₀)
  let S := c.support.image label
  let W := oldFaceChains p i hiV hiE hiF d₀
  let P : Submodule ℤ (UF _ _ →₀ ℤ) := Submodule.span ℤ
    (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀)))
  have hpiece (s : {s // s ∈ S}) :
      ∃ z, z ∈ P ∧ bdry2 (uCover _ _) z = 0 ∧
        c.filter (fun f => label f = s.val) - z ∈ W := by
    by_cases hs : s.val = ∅
    · refine ⟨0, P.zero_mem, map_zero _, ?_⟩
      intro f hf'
      have hn : label f ≠ s.val := by
        grind [faceLabel_empty_iff]
      simp [hn]
    · obtain ⟨f, hf', hfs⟩ := Finset.mem_image.mp s.property
      have hfoff : ¬ oldFace p i hiV hiE hiF _ f := by
        grind [faceLabel_empty_of_old]
      obtain ⟨g, hg⟩ := faceLabel_of_not_old p i hiV hiE hiF _ hT hL f hfoff
      obtain ⟨z, hz, hzc, hzd⟩ := copy_filter_completion p hp a hr he i hiV hiE hiF
        hDconn hL d₀ ht hD hT c hc g
      aesop
  choose z hz hzc hzd using hpiece
  let zsum := ∑ s : {s // s ∈ S}, z s
  have hzb : bdry2 (uCover _ _) zsum = 0 := by
    simp only [zsum, map_sum, hzc, Finset.sum_const_zero]
  have hdiff : c - zsum ∈ W := by
    have hh := W.sum_mem (fun s (_ : s ∈ (Finset.univ : Finset {s // s ∈ S})) => hzd s)
    rw [Finset.sum_sub_distrib] at hh
    have hsum := (Finset.sum_coe_sort S (fun s => c.filter (fun f => label f = s))).trans
        (finsupp_sum_label_filters label c)
    rw [hsum] at hh
    exact hh
  have hzero := oldFaceChains_cycle_zero p hp a hr he hf i hiV hiE hiF
    hDconn d₀ ht hD hT _ hdiff (by rw [map_sub, hc, hzb, sub_self])
  rw [sub_eq_zero.mp hzero]
  exact P.sum_mem (fun s _ => hz s)

end FiniteChains.Comb.PushoutRelativeCopies
