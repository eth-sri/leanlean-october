module

public import RequestProject.PushoutOldCoverAcyclic
public import RequestProject.SupportedLabelChains

@[expose] public section

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.AcyclicCopies
universe u v
variable {D X : Complex2.{u}} {G : Type v} (φ : G → Hom D X)
  (hV : ∀ g, Function.Injective (φ g).onV)
  (hE : ∀ g, Function.Injective (φ g).onE)
  (hF : ∀ g, Function.Injective (φ g).onF)
  (hD : IsAcyclic D)
  (hmeet : ∀ g h d e, (φ g).onV d = (φ h).onV e →
    Set.range (φ g).onV = Set.range (φ h).onV ∧
    Set.range (φ g).onE = Set.range (φ h).onE ∧
    Set.range (φ g).onF = Set.range (φ h).onF)

def vertexSet (g : G) : Set X.V := Set.range (φ g).onV
def oldEdge (e : X.E) : Prop := ∃ g, e ∈ Set.range (φ g).onE
def oldFace (f : X.F) : Prop := ∃ g, f ∈ Set.range (φ g).onF

def label (v : X.V) : Set X.V :=
  {w | ∃ g, v ∈ vertexSet φ g ∧ w ∈ vertexSet φ g}

include hmeet in
theorem label_on_vertex (g : G) (d : D.V) :
    label φ ((φ g).onV d) = vertexSet φ g := by
  ext w
  exact ⟨fun ⟨h, ⟨e, he⟩, hw⟩ => by change w ∈ Set.range (φ g).onV; rwa [(hmeet g h d e he.symm).1],
    fun hw => ⟨g, ⟨d, rfl⟩, hw⟩⟩

include hmeet in
theorem label_on_edge (g : G) (e : D.E) :
    label φ (X.src ((φ g).onE e)) = vertexSet φ g := by
  rw [(φ g).src_onE]; exact label_on_vertex φ hmeet g (D.src e)

include hmeet in
theorem label_on_face (g : G) (f : D.F) :
    label φ (X.base ((φ g).onF f)) = vertexSet φ g := by
  rw [(φ g).base_onF]; exact label_on_vertex φ hmeet g (D.base f)

include hmeet in
theorem face_range_of_label (g : G) (f : X.F) (hf : oldFace φ f)
    (hl : label φ (X.base f) = vertexSet φ g) : f ∈ Set.range (φ g).onF := by
  obtain ⟨h, d, rfl⟩ := hf
  obtain ⟨v, hvg⟩ : (φ h).onV (D.base d) ∈ vertexSet φ g :=
    (label_on_face φ hmeet h d).symm.trans hl ▸ ⟨D.base d, rfl⟩
  rw [← (hmeet h g (D.base d) v hvg.symm).2.2]
  exact ⟨d, rfl⟩

include hV hE hD hmeet in
theorem one_cycle_filling (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (hz : bdry1 X c = 0) :
    ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧ bdry2 X y = c := by
  let S := c.support.image (fun e => label φ (X.src e))
  have hfill (s : Set X.V) (hs : s ∈ S) :
      ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧
        bdry2 X y = c.filter (fun e => label φ (X.src e) = s) := by
    obtain ⟨e, he, hes⟩ := Finset.mem_image.mp hs
    obtain ⟨g, d, hd⟩ := hc e he
    have hsg : s = vertexSet φ g := hes.symm.trans (hd ▸ label_on_edge φ hmeet g d)
    have hsupp (e) (hn : e ∉ Set.range (φ g).onE) :
        (c.filter (fun e => label φ (X.src e) = s)) e = 0 := by
      by_cases he : c e = 0
      · simp [Finsupp.filter_apply, he]
      · have hl : label φ (X.src e) ≠ s := fun hl => hn <| by
          obtain ⟨h, d', rfl⟩ := hc e (Finsupp.mem_support_iff.mpr he)
          obtain ⟨v, hvg⟩ : (φ h).onV (D.src d') ∈ vertexSet φ g :=
            (label_on_edge φ hmeet h d').symm.trans (hl.trans hsg) ▸ ⟨D.src d', rfl⟩
          rw [← (hmeet h g (D.src d') v hvg.symm).2.1]; exact ⟨d', rfl⟩
        simp [hl]
    have hcycle : bdry1 X (c.filter (fun e => label φ (X.src e) = s)) = 0 := by
      erw [supported_label_boundary (bdry1 X) (fun e => label φ (X.src e)) (label φ)
        (oldEdge φ) (by
          rintro e ⟨g', d', rfl⟩ v hv
          by_cases ht : v = X.tgt ((φ g').onE d')
          · rw [ht, (φ g').tgt_onE, label_on_vertex φ hmeet, label_on_edge φ hmeet]
          · by_cases hs' : v = X.src ((φ g').onE d')
            · rw [hs']
            · exact False.elim (hv (by simp [bdry1_single, Ne.symm ht, Ne.symm hs']))) c hc s,
        hz, Finsupp.filter_zero]
    obtain ⟨y, hy, hb⟩ := embedded_one_cycle_filling (φ g) (hV g) (hE g) hD _ hsupp hcycle
    exact ⟨y, fun f hf => ⟨g, by by_contra hn; exact (Finsupp.mem_support_iff.mp hf) (hy f hn)⟩, hb⟩
  choose y hy hb using fun s : {s : Set X.V // s ∈ S} => hfill s.1 s.2
  refine ⟨∑ s : {s : Set X.V // s ∈ S}, y s, fun f hf => ?_, ?_⟩
  · by_contra hn
    refine Finsupp.mem_support_iff.mp hf ?_
    simp only [Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun s _ => by by_contra hs; exact hn (hy s f (Finsupp.mem_support_iff.mpr hs))
  · rw [map_sum]; simp_rw [hb]
    exact (Finset.sum_coe_sort S (fun s : Set X.V =>
      c.filter (fun e => label φ (X.src e) = s))).trans
        (finsupp_sum_label_filters (fun e => label φ (X.src e)) c)

include hE hF hD hmeet in
theorem two_cycle_zero (c : X.F →₀ ℤ)
    (hc : ∀ f ∈ c.support, oldFace φ f) (hz : bdry2 X c = 0) : c = 0 := by
  ext f
  by_cases hf : c f = 0
  · exact hf
  · obtain ⟨g, d, hd⟩ := hc f (Finsupp.mem_support_iff.mpr hf)
    let c' := c.filter (fun f => label φ (X.base f) = vertexSet φ g)
    have hsupp (f') (hn : f' ∉ Set.range (φ g).onF) : c' f' = 0 := by
      by_cases hf' : c f' = 0
      · simp [c', Finsupp.filter_apply, hf']
      · have hl : label φ (X.base f') ≠ vertexSet φ g :=
          fun hl => hn (face_range_of_label φ hmeet g f' (hc f' (Finsupp.mem_support_iff.mpr hf')) hl)
        simp [c', hl]
    have hcycle : bdry2 X c' = 0 := by
      erw [supported_label_boundary (bdry2 X) (fun f => label φ (X.base f))
          (fun e => label φ (X.src e)) (oldFace φ) (by
            rintro f' ⟨g', d', rfl⟩ e he
            have hm : e ∈ Set.range (φ g').onE := by
              by_contra hn; apply he
              rw [bdry2_single, one_smul, (φ g').att_onF, pathChain_map]
              exact Finsupp.mapDomain_notin_range (pathChain (D.att d')) e hn
            obtain ⟨l, rfl⟩ := hm
            rw [label_on_edge φ hmeet, label_on_face φ hmeet]) c hc (vertexSet φ g),
        hz, Finsupp.filter_zero]
    have hc' := embedded_two_cycle_zero (φ g) (hE g) (hF g) hD c' hsupp hcycle
    have hl : label φ (X.base f) = vertexSet φ g := hd ▸ label_on_face φ hmeet g d
    simpa [c', Finsupp.filter_apply, hl] using congrArg (fun z : X.F →₀ ℤ => z f) hc'
