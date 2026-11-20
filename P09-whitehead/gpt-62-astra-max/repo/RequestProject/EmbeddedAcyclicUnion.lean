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

def vertexSet (g : G) := Set.range (φ g).onV
def oldEdge (e : X.E) := ∃ g, e ∈ Set.range (φ g).onE
def oldFace (f : X.F) := ∃ g, f ∈ Set.range (φ g).onF

/-- A component label is the literal vertex set of its copy.  This removes
duplicate names for copies without choosing representatives. -/
def label (v : X.V) :=
  {w | ∃ g, v ∈ vertexSet φ g ∧ w ∈ vertexSet φ g}

variable (g : G)

include hmeet in
theorem label_on_vertex (d : D.V) :
    label φ ((φ g).onV d) = vertexSet φ g := by
  ext w
  constructor
  · rintro ⟨h, ⟨e, he⟩, hw⟩
    change w ∈ Set.range _
    rw [(hmeet g h d e he.symm).1]
    exact hw
  · intro hw
    exact ⟨g, ⟨d, rfl⟩, hw⟩

include hmeet in
theorem label_on_edge (e : D.E) :
    label φ (X.src ((φ g).onE e)) = vertexSet φ g := by
  rw [(φ g).src_onE]
  apply label_on_vertex <;> assumption

include hmeet in
theorem label_on_face (f : D.F) :
    label φ (X.base ((φ g).onF f)) = vertexSet φ g := by
  rw [(φ g).base_onF]
  apply label_on_vertex <;> assumption

include hmeet in
theorem edge_range_of_label (e : X.E) (he : oldEdge φ e)
    (hl : label φ (X.src e) = vertexSet φ g) : e ∈ Set.range (φ g).onE := by
  obtain ⟨h, d, rfl⟩ := he
  have hm : (φ h).onV (D.src d) ∈ vertexSet φ g := by
    rw [← ((label_on_edge φ hmeet h d).symm.trans hl)]
    exact ⟨D.src d, rfl⟩
  obtain ⟨v, hvg⟩ := hm <;> grind

include hmeet in
theorem face_range_of_label (f : X.F) (hf : oldFace φ f)
    (hl : label φ (X.base f) = vertexSet φ g) : f ∈ Set.range (φ g).onF := by
  obtain ⟨h, d, rfl⟩ := hf
  have hm : (φ h).onV (D.base d) ∈ vertexSet φ g := by
    rw [← ((label_on_face φ hmeet h d).symm.trans hl)]
    exact ⟨D.base d, rfl⟩
  obtain ⟨v, hvg⟩ := hm <;> grind

include hmeet in
theorem boundary1_label (e : X.E) (he : oldEdge φ e) (v : X.V)
    (hv : bdry1 X (Finsupp.single e 1) v ≠ 0) :
    label φ v = label φ (X.src e) := by
  obtain ⟨g, d, rfl⟩ := he
  by_cases ht : v = X.tgt ((φ g).onE d)
  · rw [ht, (φ g).tgt_onE, label_on_vertex φ hmeet,
      label_on_edge φ hmeet]
  · by_cases hs : v = X.src ((φ g).onE d)
    · simp [hs]
    · simp_all

include hmeet in
theorem boundary2_label (f : X.F) (hf : oldFace φ f) (e : X.E)
    (he : bdry2 X (Finsupp.single f 1) e ≠ 0) :
    label φ (X.src e) = label φ (X.base f) := by
  obtain ⟨g, d, rfl⟩ := hf
  have hm : e ∈ Set.range (φ g).onE := by
    by_contra hn
    apply he
    rw [bdry2_single, one_smul, (φ g).att_onF, pathChain_map]
    apply Finsupp.mapDomain_notin_range <;> assumption
  obtain ⟨l, rfl⟩ := hm
  rw [label_on_edge φ hmeet, label_on_face φ hmeet]

include hmeet in
theorem boundary1_filter (c : X.E →₀ ℤ)
    (hc : ∀ e ∈ c.support, oldEdge φ e) (s : Set X.V) :
    bdry1 X (c.filter (fun e => label φ (X.src e) = s)) =
      (bdry1 X c).filter (fun v => label φ v = s) :=
  supported_label_boundary _ _ _
    _ (boundary1_label φ hmeet) c hc s

include hmeet in
theorem boundary2_filter (c : X.F →₀ ℤ)
    (hc : ∀ f ∈ c.support, oldFace φ f) (s : Set X.V) :
    bdry2 X (c.filter (fun f => label φ (X.base f) = s)) =
      (bdry2 X c).filter (fun e => label φ (X.src e) = s) :=
  supported_label_boundary _ _
    _ _ (boundary2_label φ hmeet) c hc s

section

variable (c : X.E →₀ ℤ) (hc : ∀ e ∈ c.support, oldEdge φ e) (hz : bdry1 X c = 0)
include hc hz

include hV hE hD hmeet in
/-- The support of every nonzero labelled summand lies in one actual copy. -/
theorem edge_filter_filling
    (s : Set X.V) (hs : s ∈ c.support.image (fun e => label φ (X.src e))) :
    ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧
      bdry2 X y = c.filter (fun e => label φ (X.src e) = s) := by
  obtain ⟨e, he, hes⟩ := Finset.mem_image.mp hs
  obtain ⟨g, d, hd⟩ := hc e he
  have hsg : s = vertexSet φ g := by
    rw [← hes, ← hd]
    apply label_on_edge <;> assumption
  have hsupp : ∀ e ∉ Set.range (φ g).onE,
      (c.filter (fun e => label φ (X.src e) = s)) e = 0 := by
    intro e hn
    by_cases he : c e = 0
    · simp [Finsupp.filter_apply, he]
    · have hl : label φ (X.src e) ≠ s := by
        intro hl
        exact hn (edge_range_of_label φ hmeet g e (hc e (Finsupp.mem_support_iff.mpr he)) (hl.trans hsg))
      simp [hl]
  have hcycle : bdry1 X (c.filter (fun e => label φ (X.src e) = s)) = 0 := by
    rw [boundary1_filter φ hmeet c hc, hz, Finsupp.filter_zero]
  obtain ⟨y, hy, hb⟩ := embedded_one_cycle_filling _ (hV g) (hE g) hD _ hsupp hcycle
  refine ⟨y, ?_, hb⟩
  intro f hf
  refine ⟨g, ?_⟩ <;> grind

include hV hE hD hmeet in
/-- Exact H1 filling in the union. The family of copies can be arbitrary;
only the finitely many labels met by the given chain are summed. -/
theorem one_cycle_filling :
    ∃ y : X.F →₀ ℤ, (∀ f ∈ y.support, oldFace φ f) ∧ bdry2 X y = c := by
  let S := c.support.image (fun e => label φ (X.src e))
  choose y hy hb using fun s : {s : Set X.V // s ∈ S} =>
    edge_filter_filling φ hV hE hD hmeet c hc hz s.1 s.2
  refine ⟨∑ s : {s : Set X.V // s ∈ S}, y s, ?_, ?_⟩
  · intro f hf
    by_contra hn
    have hz' : (∑ s : {s : Set X.V // s ∈ S}, y s) f = 0 := by
      simp only [Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero <;> grind
    grind
  · rw [map_sum]
    simp_rw [hb]
    exact (Finset.sum_coe_sort S (fun s : Set X.V =>
      c.filter (fun e => label φ _ = s))).trans
        (finsupp_sum_label_filters (fun e => label φ (X.src e)) c)

end

include hE hF hD hmeet in
/-- H2 vanishes in the same actual union, coefficient by coefficient. -/
theorem two_cycle_zero (c : X.F →₀ ℤ)
    (hc : ∀ f ∈ c.support, oldFace φ f) (hz : bdry2 X c = 0) : c = 0 := by
  ext f
  by_cases hf : c f = 0
  · exact hf
  · obtain ⟨g, d, hd⟩ := hc f (Finsupp.mem_support_iff.mpr hf)
    let c' := c.filter (fun f => label φ (X.base f) = vertexSet φ g)
    have hsupp : ∀ f ∉ Set.range (φ g).onF, c' f = 0 := by
      intro f hn
      by_cases hf : c f = 0
      · simp [c', Finsupp.filter_apply, hf]
      · have hl : label φ _ ≠ vertexSet φ g :=
          fun hl => hn (face_range_of_label φ hmeet g f (hc f (Finsupp.mem_support_iff.mpr hf)) hl)
        simp [c', hl]
    have hcycle : bdry2 X c' = 0 := by
      rw [show c' = c.filter (fun f => label φ _ = vertexSet φ g) from rfl,
        boundary2_filter φ hmeet c hc, hz, Finsupp.filter_zero]
    have hl : label φ (X.base f) = vertexSet φ g := by
      rw [← hd]
      apply label_on_face <;> assumption
    have hcoeff := congrArg (fun z : X.F →₀ ℤ => z f) (embedded_two_cycle_zero (φ g) (hE g) (hF g) hD c' hsupp hcycle)
    simpa [c', Finsupp.filter_apply, hl] using hcoeff

end FiniteChains.Comb.AcyclicCopies
