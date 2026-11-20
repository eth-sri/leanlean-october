module
public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import PottsDiscontinuity.Duality.RectangleCurl
public import Mathlib.Algebra.Ring.Periodic

/-! A divergence-free rectangular flow has a stream function. Extend both
components by zero to the whole grid and integrate the vertical flow along
rows. The divergence equation says that the remaining horizontal discrepancy
is constant along a row; to the left of the box it vanishes. -/
@[expose] public section
open Finset
namespace PottsDiscontinuity.FK
open Medial
variable {a : LatticeVertex} {w h : ℕ}
abbrev RectanglePrimalFlow (a : LatticeVertex) (w h : ℕ) := RectanglePrimalBond a w h → ℝ
noncomputable instance rectangularBondFintype : Fintype (RectanglePrimalBond a w h) :=
  letI : Fintype (rectanglePrimalEdgeCarrier a w h) := Fintype.ofFinite _
  Fintype.ofEquiv _ (rectanglePrimalEdgeBondEquiv a w h)
variable (F : RectanglePrimalFlow a w h)

def rectangleExtendedPrimalFlow (b : LatticeBond) : ℝ :=
  if h : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h then F ⟨b,h⟩ else 0
abbrev hor (x y : ℤ) := rectangleExtendedPrimalFlow F ⟨(x,y),.horizontal⟩
abbrev vert (x y : ℤ) := rectangleExtendedPrimalFlow F ⟨(x,y),.vertical⟩
noncomputable def rectanglePrimalFlowDivergence (v : LatticeVertex) : ℝ :=
  ∑ b, ((if b.val.source = v then F b else 0) - (if b.val.target = v then F b else 0))

private lemma bond_sum (z : LatticeBond) : (∑ b, if b.val = z then F b else 0) = rectangleExtendedPrimalFlow F z := by
  unfold rectangleExtendedPrimalFlow; split <;> rename_i hz
  · let i : RectanglePrimalBond a w h := ⟨z,hz⟩
    simpa only [← show i.val = z from rfl,Subtype.val_inj,mem_univ,ite_true] using (sum_ite_eq' univ i F)
  · apply sum_eq_zero; intro b _; apply ite_eq_right; intro he; exact hz (he ▸ b.property)

lemma divergence_stencil (x y : ℤ) : rectanglePrimalFlowDivergence F (x,y) =
    hor F x y - hor F (x-1) y + vert F x y - vert F x (y-1) := by
  simp only [hor,vert,← bond_sum,rectanglePrimalFlowDivergence,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl; rintro ⟨⟨⟨i,j⟩,ax⟩,hb⟩ _; cases ax <;>
    simp [LatticeBond.source,LatticeBond.target,LatticeBond.mk.injEq,Prod.mk.injEq] <;> split_ifs <;> grind

lemma period_one_const {f : ℤ → ℝ} (hf : ∀ x, f x - f (x-1) = 0) (x y : ℤ) : f x = f y := by
  have hp : Function.Periodic f 1 := fun i => by simpa using sub_eq_zero.mp (hf (i+1))
  simpa using hp.int_mul (x-y) y

private lemma Hzero (x y : ℤ) (hbad : ¬(a.1 ≤ x ∧ x < a.1+w ∧ a.2 ≤ y ∧ y ≤ a.2+h)) : hor F x y = 0 := by
  apply dite_eq_right; simp [mem_latticeRectangle,LatticeBond.source,LatticeBond.target]; omega
private lemma Vzero (x y : ℤ) (hbad : ¬(a.1 ≤ x ∧ x ≤ a.1+w ∧ a.2 ≤ y ∧ y < a.2+h)) : vert F x y = 0 := by
  apply dite_eq_right; simp [mem_latticeRectangle,LatticeBond.source,LatticeBond.target]; omega

def stream (x y : ℤ) := -∑ k ∈ Icc a.1 x, vert F k y
private lemma stream_dx (x y : ℤ) : stream F (x-1) y - stream F x y = vert F x y := by
  by_cases h : a.1 ≤ x
  · have he : Icc a.1 x = insert x (Icc a.1 (x-1)) := by ext k; simp; omega
    simp [stream,he,show x ∉ Icc a.1 (x-1) by simp]
  · simp [stream,Icc_eq_empty_of_lt (show x-1 < a.1 by omega),Icc_eq_empty_of_lt (by omega : x < a.1),Vzero F x y (by omega)]

variable (hF : ∀ z ∈ latticeRectangle a w h, rectanglePrimalFlowDivergence F z = 0)
include hF in
private lemma stream_dy (x y : ℤ) : stream F x y - stream F x (y-1) = hor F x y := by
  have div (i : ℤ) : hor F i y - hor F (i-1) y + vert F i y - vert F i (y-1) = 0 := by
    by_cases hm : (i,y) ∈ latticeRectangle a w h
    · rw [←divergence_stencil,hF _ hm]
    · simp [mem_latticeRectangle] at hm
      rw [Hzero F _ _ (by omega),Hzero F _ _ (by omega),Vzero F _ _ (by omega),Vzero F _ _ (by omega)]; ring
  let g i := stream F i y - stream F i (y-1) - hor F i y
  have he : g x = g (a.1-1) := period_one_const (fun i => by dsimp [g]; linarith [stream_dx F i y,stream_dx F i (y-1),div i]) _ _
  simpa [g,stream,Icc_eq_empty_of_lt (show a.1-1 < a.1 by omega),Hzero F (a.1-1) y (by omega),sub_eq_zero] using he

include hF in
lemma stream_outside {x y : ℤ} (ho : (x,y) ∉ rectangleDualInterior a w h) : stream F x y = 0 := by
  have hy (i j : ℤ) (hj : ¬(a.2 ≤ j ∧ j < a.2+h)) : stream F i j = 0 := by simp [stream,fun k => Vzero F k j (by omega)]
  by_cases hj : a.2 ≤ y ∧ y < a.2+h
  · by_cases hx : x < a.1
    · simp [stream,Icc_eq_empty_of_lt hx]
    · have hr : a.1+w ≤ x := by
        simp [rectangleDualInterior,rectangleDualExpanded,mem_latticeRectangle] at ho; omega
      have he := period_one_const (f := stream F x) (fun j => (stream_dy F hF x j).trans (Hzero F _ _ (by omega))) y (a.2-1)
      exact he.trans (hy _ _ (by omega))
  · exact hy _ _ hj

noncomputable def flowPotential : RectangleExteriorPotential a w h :=
  ⟨fun z => stream F z.val.1 z.val.2, fun _ hz => stream_outside F hF (mem_filter.mp hz).2⟩
private lemma extended_stream (x y : ℤ) : rectangleExtendedPotential (flowPotential F hF) (x,y) = stream F x y := by
  unfold rectangleExtendedPotential; split <;> rename_i he
  · rfl
  · exact (stream_outside F hF (fun h => he (mem_filter.mp h).1)).symm

theorem curl_flowPotential (b : RectanglePrimalBond a w h) : rectangleCurlFlow (flowPotential F hF) b.val = F b := by
  rcases b with ⟨⟨⟨x,y⟩,ax⟩,hb⟩; cases ax
  · exact (by simpa only [rectangleCurlFlow,LatticeBond.faceBase,extended_stream] using stream_dy F hF x y |>.trans (dite_eq_left hb))
  · exact (by simpa only [rectangleCurlFlow,LatticeBond.faceBase,extended_stream] using stream_dx F x y |>.trans (dite_eq_left hb))

lemma extended_curl (φ : RectangleExteriorPotential a w h) (b : LatticeBond) :
    rectangleExtendedPrimalFlow (fun i : RectanglePrimalBond a w h => rectangleCurlFlow φ i.val) b = rectangleCurlFlow φ b := by
  unfold rectangleExtendedPrimalFlow; split <;> rename_i hb
  · rfl
  · exact (curl_zero_outside φ hb).symm
end PottsDiscontinuity.FK
