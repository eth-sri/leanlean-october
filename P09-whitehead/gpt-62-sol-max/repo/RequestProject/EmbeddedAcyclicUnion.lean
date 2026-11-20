module

public import RequestProject.PushoutOldCoverAcyclic
public import RequestProject.SupportedLabelChains

@[expose] public section

/-! Homology of the actual union of embedded acyclic copies.  Copies may
have many different names, but copies meeting at a vertex have identical
cell images.  Finite-support label filters give global H1 fillings and H2
vanishing without assuming a decomposition of cycles. Unverified source. -/

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

/-- A component label is the literal vertex set of its copy.  This removes
duplicate names for copies without choosing representatives. -/
def label (v : X.V) : Set X.V :=
  {w | ∃ g, v ∈ vertexSet φ g ∧ w ∈ vertexSet φ g}

include hmeet in
theorem label_on_vertex (g : G) (d : D.V) :
    label φ ((φ g).onV d) = vertexSet φ g := by
  grind +locals

include hmeet in
theorem label_on_edge (g : G) (e : D.E) :
    label φ (X.src ((φ g).onE e)) = vertexSet φ g := by
  rw [(φ g).src_onE]
  exact label_on_vertex φ hmeet g (D.src e)

include hmeet in
theorem label_on_face (g : G) (f : D.F) :
    label φ (X.base ((φ g).onF f)) = vertexSet φ g := by
  rw [(φ g).base_onF]
  exact label_on_vertex φ hmeet g (D.base f)

include hmeet in
private theorem ranges_eq_of_vertexSet {g h : G} (hv : vertexSet φ g = vertexSet φ h)
    (d : D.V) : Set.range (φ g).onE = Set.range (φ h).onE ∧
      Set.range (φ g).onF = Set.range (φ h).onF := by
  obtain ⟨e, he⟩ := hv ▸ (show (φ g).onV d ∈ vertexSet φ g from ⟨d, rfl⟩)
  exact (hmeet g h d e he.symm).2

include hmeet in
theorem edge_range_of_label (g : G) (e : X.E) (he : oldEdge φ e)
    (hl : label φ (X.src e) = vertexSet φ g) : e ∈ Set.range (φ g).onE := by
  obtain ⟨h, d, rfl⟩ := he
  rw [label_on_edge φ hmeet] at hl
  exact (ranges_eq_of_vertexSet φ hmeet hl (D.src d)).1 ▸ Set.mem_range_self d

include hmeet in
theorem face_range_of_label (g : G) (f : X.F) (hf : oldFace φ f)
    (hl : label φ (X.base f) = vertexSet φ g) : f ∈ Set.range (φ g).onF := by
  obtain ⟨h, d, rfl⟩ := hf
  rw [label_on_face φ hmeet] at hl
  exact (ranges_eq_of_vertexSet φ hmeet hl (D.base d)).2 ▸ Set.mem_range_self d

include hmeet in
theorem boundary1_label (e : X.E) (he : oldEdge φ e) (v : X.V)
    (hv : bdry1 X (Finsupp.single e 1) v ≠ 0) :
    label φ v = label φ (X.src e) := by
  obtain ⟨g, d, rfl⟩ := he
  by_cases ht : v = X.tgt ((φ g).onE d)
  · rw [ht, (φ g).tgt_onE, label_on_vertex φ hmeet,
      label_on_edge φ hmeet]
  simp_all <;> grind

include hmeet in
theorem boundary2_label (f : X.F) (hf : oldFace φ f) (e : X.E)
    (he : bdry2 X (Finsupp.single f 1) e ≠ 0) :
    label φ (X.src e) = label φ (X.base f) := by
  obtain ⟨g, d, rfl⟩ := hf
  have hm : e ∈ Set.range (φ g).onE := by
    by_contra hn
    apply he
    exact bdry2_single_image_zero (φ g) d e hn
  obtain ⟨l, rfl⟩ := hm
  rw [label_on_edge φ hmeet, label_on_face φ hmeet]

include hmeet in
theorem boundary1_filter (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (s : Set X.V) :
    bdry1 X (c.filter (fun e => label φ (X.src e) = s)) =
      (bdry1 X c).filter (fun v => label φ v = s) :=
  supported_label_boundary (bdry1 X) (fun e => label φ (X.src e)) (label φ)
    (oldEdge φ) (boundary1_label φ hmeet) c hc s

include hmeet in
theorem boundary2_filter (c : X.F →₀ ℤ)
    (hc : ∀ f ∈ c.support, oldFace φ f) (s : Set X.V) :
    bdry2 X (c.filter (fun f => label φ (X.base f) = s)) =
      (bdry2 X c).filter (fun e => label φ (X.src e) = s) :=
  supported_label_boundary (bdry2 X) (fun f => label φ (X.base f))
    (fun e => label φ (X.src e)) (oldFace φ) (boundary2_label φ hmeet) c hc s

include hV hE hD hmeet in
/-- The support of every nonzero labelled summand lies in one actual copy. -/
theorem edge_filter_filling (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (hz : bdry1 X c = 0)
    (s : Set X.V) (hs : s ∈ c.support.image (fun e => label φ (X.src e))) :
    ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧
      bdry2 X y = c.filter (fun e => label φ (X.src e) = s) := by
  obtain ⟨e, he, hes⟩ := Finset.mem_image.mp hs
  obtain ⟨g, d, hd⟩ := hc e he
  have hsg : s = vertexSet φ g := by
    rw [← hes, ← hd]
    exact label_on_edge φ hmeet g d
  have hsupp := filter_supported (p := fun e => label φ (X.src e) = s) c hc (fun e he hl =>
    edge_range_of_label φ hmeet g e he (hl.trans hsg))
  have hcycle : bdry1 X (c.filter (fun e => label φ (X.src e) = s)) = 0 := by
    rw [boundary1_filter φ hmeet c hc, hz, Finsupp.filter_zero]
  obtain ⟨y, hy, hb⟩ := embedded_one_cycle_filling (φ g) (hV g) (hE g) hD _ hsupp hcycle
  refine ⟨y, ?_, hb⟩
  intro f hf
  refine ⟨g, ?_⟩
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hf) (hy f hn)

include hV hE hD hmeet in
/-- Exact H1 filling in the union. The family of copies can be arbitrary;
only the finitely many labels met by the given chain are summed. -/
theorem one_cycle_filling (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (hz : bdry1 X c = 0) :
    ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧ bdry2 X y = c := by
  let S := c.support.image (fun e => label φ (X.src e))
  choose y hy hb using fun s : {s : Set X.V // s ∈ S} =>
    edge_filter_filling φ hV hE hD hmeet c hc hz s.1 s.2
  refine ⟨∑ s : {s : Set X.V // s ∈ S}, y s, ?_, ?_⟩
  · intro f hf
    obtain ⟨s, _, hsf⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hf)
    exact hy s f hsf
  · rw [map_sum]
    simp_rw [hb]
    exact (Finset.sum_coe_sort S (fun s  =>
      c.filter (fun e => label φ (X.src e) = s))).trans
        (finsupp_sum_label_filters (fun e => label φ (X.src e)) c)

include hE hF hD hmeet in
/-- H2 vanishes in the same actual union, coefficient by coefficient. -/
theorem two_cycle_zero (c : X.F →₀ ℤ)
    (hc : ∀ f ∈ c.support, oldFace φ f) (hz : bdry2 X c = 0) : c = 0 := by
  ext f
  by_cases hf : c f = 0
  · exact hf
  · obtain ⟨g, d, hd⟩ := hc f (Finsupp.mem_support_iff.mpr hf)
    let c' := c.filter (fun f => label φ (X.base f) = vertexSet φ g)
    have hsupp := filter_supported (p := fun f => label φ (X.base f) = vertexSet φ g)
      c hc (face_range_of_label φ hmeet g)
    have hcycle : bdry2 X c' = 0 := by
      simp [c', boundary2_filter φ hmeet c hc, hz, Finsupp.filter_zero]
    have hc' := embedded_two_cycle_zero (φ g) (hE g) (hF g) hD c' hsupp hcycle
    have hl : label φ (X.base f) = vertexSet φ g := by
      rw [← hd]
      exact label_on_face φ hmeet g d
    have hcoeff := congrArg (fun z  => z f) hc'
    simpa [c', Finsupp.filter_apply, hl] using hcoeff

end FiniteChains.Comb.AcyclicCopies
