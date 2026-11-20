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
  (diag : Diagram D K L)
  (hp : IsCovering diag.p) (a : DeckAction D Q) (hr : IsRegular diag.p a)
  (he : ∀ q e, diag.p.onE (a.smulE q e) = diag.p.onE e)
  (hf : ∀ q f, diag.p.onF (a.smulF q f) = diag.p.onF f)
  (hDconn : IsConnected D) (hL : IsConnected L)
  (d₀ : D.V) (ht : Pi1Trivial diag.i) (hD : IsAcyclic D) (hT : IsConnected diag.target)

local notation "base" => diag.i.onV d₀

def oldFaceChains : Submodule ℤ
    (diag.Face base →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {f | oldFace diag base f}

include hp hr he hf hDconn ht hD hT in
theorem oldFaceChains_cycle_zero
    (c : diag.Face base →₀ ℤ)
    (hc : c ∈ oldFaceChains diag d₀)
    (hz : bdry2 (diag.cover base) c = 0) : c = 0 := by
  have hzero : ∀ z : UF diag.target
      (pushV diag.p diag.i base) →₀ ℤ,
      (∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k) →
        bdry2 (uCover diag.target (pushV diag.p diag.i base)) z = 0 → z = 0 := by
    rw [pushV_of_mem diag.p diag.injV]
    exact PushoutOldCover.old_two_cycle_zero diag.p hp a hr he hf diag.i diag.injV diag.injE diag.injF
      hDconn d₀ ht hT hD
  exact hzero c ((Finsupp.mem_supported ℤ c).mp hc) hz

set_option maxHeartbeats 800000 in
include hp hr he hDconn hL ht hD hT in
theorem copy_filter_completion
    (c : diag.Face base →₀ ℤ)
    (hc : bdry2 (diag.cover base) c = 0)
    (g : diag.CopyGroup base) :
    ∃ z : diag.Face base →₀ ℤ,
      z ∈ Pi2FromSub diag.toTarget (diag.root base) ∧
      bdry2 (diag.cover base) z = 0 ∧
      c.filter (fun f => faceLabel diag base f =
        diag.copyVertices base g) - z ∈
          oldFaceChains diag d₀ := by
  let φ := diag.copyMap base g
  let φ2 : (UF L base →₀ ℤ) →ₗ[ℤ]
      (diag.Face base →₀ ℤ) := chain2 φ
  let s := diag.copyVertices base g
  let d := c.filter (fun f => faceLabel diag base f = s)
  have hφE  := UniversalCopy.map_injective_E
    diag.toTarget base
    (PushoutSheets.univLift_edges_injective diag.p hp a hr he diag.i diag.injV diag.injE diag.injF hDconn hL d₀ ht) g
  have hφF  := UniversalCopy.map_injective_F
    diag.toTarget base
    (PushoutSheets.univLift_faces_injective diag.p hp a hr he diag.i diag.injV diag.injE diag.injF hDconn hL d₀ ht) g
  have hd : ∀ f ∉ Set.range φ.onF, d f = 0 := by
    intro f hf'
    have hn : faceLabel diag base f ≠ s := fun hl =>
      hf' (face_range_of_label diag base hT hL g f hl)
    simp [d, hn]
  obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff φ.onF hφF d).mpr hd
  change UF L base →₀ ℤ at b
  have hb' : φ2 b = d := hb
  have hcr : relativeBoundary diag base c = 0 := by simp [relativeBoundary, hc, Finsupp.filter_zero]
  have hdr : relativeBoundary diag base d = 0 := by
    dsimp only [d]
    rw [relative_boundary_filter diag base hT hL, hcr, Finsupp.filter_zero]
  change (bdry2 (diag.cover base) d).filter _ = 0 at hdr
  erw [← hb', show φ2 = chain2 φ from rfl, bdry2_chain2] at hdr
  have hbs : ∀ e ∈ (Comb.bdry2 (uCover L base) b).support, e.val.2 ∈ Set.range diag.i.onE := by
    intro e he'
    by_contra hn
    have hnot := fun he => hn ((oldEdge_map_iff diag base g e).mp he)
    have hh := DFunLike.congr_fun hdr (φ.onE e)
    erw [Finsupp.filter_apply, if_pos hnot, Finsupp.zero_apply, chain1, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_apply_of_injective hφE] at hh
    exact (Finsupp.mem_support_iff.mp he') hh
  obtain ⟨w, hw, hwb⟩ := AcyclicLiftedSubcomplex.one_cycle_filling diag.i diag.injV diag.injE hDconn d₀ ht hL hD
    (bdry2 (uCover L base) b) hbs (bdry1_bdry2 (X := uCover L base) b)
  have hcycle : bdry2 (uCover L base) (b - w) = 0 := by rw [map_sub, hwb, sub_self]
  refine ⟨φ2 (b - w), UniversalCopy.cycle_image_mem
    diag.toTarget base g (b - w) hcycle, ?_, ?_⟩
  · change bdry2 (diag.cover base)
      (chain2 φ (b - w)) = 0
    exact chain2_cycle _ hcycle
  · have heq : d - φ2 (b - w) = φ2 w := by rw [map_sub, hb']; abel
    change d - φ2 (b - w) ∈ oldFaceChains diag d₀
    rw [heq]
    apply (Finsupp.mem_supported ℤ (φ2 w)).mpr
    intro f hf
    obtain ⟨t, ht', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hf)
    exact (oldFace_map_iff diag base g t).mpr (hw t ht')

include hp hr he hf hDconn hL ht hD hT in
/-- The actual finite-support spherical generation statement at the core
base point. No `Pi2GeneratedByUpstairs` or exactness input remains. -/
theorem cycle_mem_span_at_core
    (c : diag.Face base →₀ ℤ)
    (hc : bdry2 (diag.cover base) c = 0) :
    c ∈ Submodule.span ℤ
      (Pi2FromSub diag.toTarget (diag.root base)) := by
  let label := faceLabel diag base
  let S := c.support.image label
  let W := oldFaceChains diag d₀
  let P : Submodule ℤ (diag.Face base →₀ ℤ) := Submodule.span ℤ
    (Pi2FromSub diag.toTarget (diag.root base))
  have hpiece (s : {s // s ∈ S}) :
      ∃ z, z ∈ P ∧ bdry2 (diag.cover base) z = 0 ∧
        c.filter (fun f => label f = s.val) - z ∈ W := by
    by_cases hs : s.val = ∅
    · refine ⟨0, P.zero_mem, map_zero _, ?_⟩
      rw [sub_zero]
      apply (Finsupp.mem_supported' ℤ _).mpr
      intro f hf'
      have hn : label f ≠ s.val := by
        rw [hs]
        exact fun hh => hf' ((faceLabel_empty_iff diag base hT hL f).mp hh)
      simp [hn]
    · obtain ⟨f, hf', hfs⟩ := Finset.mem_image.mp s.property
      have hfoff : ¬ oldFace diag base f := by
        intro hh
        exact hs (hfs.symm.trans (faceLabel_empty_of_old diag base f hh))
      obtain ⟨g, hg⟩ := faceLabel_of_not_old diag base hT hL f hfoff
      obtain ⟨z, hz, hzc, hzd⟩ := copy_filter_completion diag hp a hr he
        hDconn hL d₀ ht hD hT c hc g
      refine ⟨z, Submodule.subset_span hz, hzc, ?_⟩
      have hsg  :=
        hfs.symm.trans hg
      simpa only [hsg] using hzd
  choose z hz hzc hzd using hpiece
  let zsum := ∑ s : {s // s ∈ S}, z s
  have hzp : zsum ∈ P := P.sum_mem (fun s _ => hz s)
  have hzb : bdry2 (diag.cover base) zsum = 0 := by
    simp only [zsum, map_sum, hzc, Finset.sum_const_zero]
  have hdiff : c - zsum ∈ W := by
    have hh := W.sum_mem (fun s (_ : s ∈ (Finset.univ : Finset {s // s ∈ S})) => hzd s)
    rw [Finset.sum_sub_distrib] at hh
    have hsum := (Finset.sum_coe_sort S (fun s => c.filter (fun f => label f = s))).trans
        (finsupp_sum_label_filters label c)
    rw [hsum] at hh
    exact hh
  have hzero  := oldFaceChains_cycle_zero diag hp a hr he hf
    hDconn d₀ ht hD hT _ hdiff (by rw [map_sub, hc, hzb, sub_self])
  rw [sub_eq_zero.mp hzero]
  exact hzp

end FiniteChains.Comb.PushoutRelativeCopies
