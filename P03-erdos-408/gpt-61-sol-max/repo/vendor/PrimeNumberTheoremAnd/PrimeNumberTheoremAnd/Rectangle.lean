module
public import Mathlib.Tactic

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.Interval.Set.Monotone

@[expose] public section

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]

end Rectangle

/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ)  :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

def Square (p : ℂ) (c : ℝ)  := Rectangle (-c - c * I + p) (c + c * I + p)

section
variable (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) {a b : ℝ}

@[simp]
theorem preimage_equivRealProdCLM_reProdIm  s t  :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl

include zRe_lt_wRe zIm_lt_wIm in
lemma mem_Rect         :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

lemma square_neg    c  : Square p (-c) = Square p c := by
  simpa [Square] using! Rectangle.symm

theorem Set.left_not_mem_uIoo   : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo   : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

end

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

section
variable (z) (w)

lemma left_mem_rect   : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma right_mem_rect   : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩

end

section
variable {z' : ℂ} {w' : ℂ} {z₀ : ℂ} {z₁ : ℂ} {z₂ : ℂ} {z₃ : ℂ} {p : ℂ} (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)

lemma rect_subset_iff   :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x
    ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · grind
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  grind

set_option linter.style.multiGoal false in
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁)
    (x₁_le_x₂ : x₁ ≤ x₂) (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁)
    (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆
      Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith

lemma RectSubRect'   (x₀_le_x₁ : z₀.re ≤ z₁.re)
    (x₁_le_x₂ : z₁.re ≤ z₂.re) (x₂_le_x₃ : z₂.re ≤ z₃.re)
    (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  grind [RectSubRect]

lemma rectangleBorder_subset_rectangle  z w  : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

/-- Note: try using `by simp` for `h`. -/
lemma rectangle_disjoint_singleton  
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
  obtain h | h | h | h := h
  · exact Or.inl (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inl (notMem_uIcc_of_gt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_gt h.1 h.2)

lemma rectangleBorder_disjoint_singleton  
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

include hz in
lemma rectangle_subset_punctured_rect  
     
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨by apply RectSubRect' <;> tauto, rectangle_disjoint_singleton hp⟩

include hz in
lemma rectangleBorder_subset_punctured_rect  
     
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨
    (rectangleBorder_subset_rectangle _ _).trans (by apply RectSubRect' <;> tauto),
    rectangleBorder_disjoint_singleton hp⟩

lemma rectangle_mem_nhds_iff   :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

end

section
variable (z) (w) (p : ℂ)

lemma mapsTo_rectangleBorder_left_re   :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re   :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im   :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im   :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

theorem not_mem_rectangleBorder_of_rectangle_mem_nhds  {z w p} 
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

theorem Complex.nhds_hasBasis_square   : (𝓝 p).HasBasis (0 < ·) (Square p ·) := by
  suffices
      (𝓝 p.re ×ˢ 𝓝 p.im).HasBasis (0 < ·)
        (equivRealProdCLM.symm.toHomeomorph ⁻¹' Square p ·)
    by simpa only [← nhds_prod_eq, Homeomorph.map_nhds_eq, Homeomorph.image_preimage]
      using! this.map equivRealProdCLM.symm.toHomeomorph
  apply ((nhds_basis_Icc_pos p.re).prod_same_index_mono (nhds_basis_Icc_pos p.im) ?_ ?_).congr
  · intro; rfl
  · intros
    rw [← uIcc_of_lt (by linarith), ← uIcc_of_lt (by linarith)]
    simpa [Square, Rectangle] using by ring_nf
  all_goals exact (antitone_const_tsub.Icc (monotone_id.const_add _)).monotoneOn _

lemma square_mem_nhds    {c}  (hc : c ≠ 0) :
    Square p c ∈ 𝓝 p := by
  wlog hc_pos : 0 < c generalizing c with h
  · rw [← square_neg]
    grind
  exact (nhds_hasBasis_square p).mem_of_mem hc_pos

end

lemma square_subset_square  {p}   {c₁ c₂}  (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    Square p c₁ ⊆ Square p c₂ := by
  apply RectSubRect' <;> simpa using by linarith
