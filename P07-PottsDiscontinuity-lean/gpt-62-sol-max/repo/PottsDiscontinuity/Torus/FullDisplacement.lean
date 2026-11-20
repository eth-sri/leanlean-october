module

public import PottsDiscontinuity.Torus.DiamondDisplacement
public import PottsDiscontinuity.Torus.RibbonHomology

/-! Translating the white faces down one row identifies their boundary operator
with a primal coboundary, after a checkerboard sign change. The resulting pairing
sees only displacement on the torus. -/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Finset Module PottsDiscontinuity.SixVertex

variable {N M : ℕ}

abbrev FullEdge (N M : ℕ) := OpenDiamondEdge (openRCConfig N M)

abbrev FullCycle (hN : Even N) (hM : Even M) := diamondCycleSpace hN hM (openRCConfig N M)

def fullFlowAt (f : FullEdge N M → ℚ) (v : Fin N × Fin M) : ℚ := f ⟨v, rfl⟩

private def fullUp : Equiv.Perm (FullEdge N M) :=
  (fullDiamondEdgeEquiv N M).trans <|
    ((Equiv.refl (Fin N)).prodCongr (finRotate M)).trans (fullDiamondEdgeEquiv N M).symm

def fullIntersectionCoefficient (f : FullEdge N M → ℚ) (e : FullEdge N M) : ℚ :=
  (if checker e.val then -1 else 1) * fullFlowAt f (e.val.1, prv e.val.2)

def fullIntersection (hN : Even N) (hM : Even M) (f : FullCycle hN hM) : FullCycle hN hM →ₗ[ℚ] ℚ where
  toFun g := ∑ e, fullIntersectionCoefficient f.val e * g.val e
  map_add' f g := by simp [mul_add, sum_add_distrib]
  map_smul' c g := by simp [mul_left_comm, Finset.mul_sum]

section

variable (hN : Even N) (hM : Even M)

private def whiteAbove (v : FaceVertex N M true) : FaceVertex N M false :=
  ⟨(v.val.1, nxt v.val.2), by rw [checker_nxt_y hM, v.property]; rfl⟩

private theorem boundaryEnd_eq_whiteAbove (e : FullEdge N M) (b : Bool) :
    openBoundaryFaceEquiv hN hM
        (ribbonBoundaryOf hN hM _ (ribbonEndEquiv hN hM (e.val, b))) =
      whiteAbove hM (faceEndpoint hN hM true (e.val.1, prv e.val.2) (b ^^ checker e.val)) := by
  apply Subtype.ext
  change leftFace (edgeReverse (ribbonEnd e.val b)) = _
  obtain ⟨⟨x,y⟩,_⟩ := e
  cases hc : checker (x,y) <;> cases b <;>
    simp only [ribbonEnd, hc, edgeReverse, leftFace, faceEndpoint, faceEndpointRaw,
      whiteAbove, checker_prv_y hM, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      Bool.xor_false, Bool.xor_true, ite_true, ite_false, Subtype.coe_mk, nxt, prv,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]

private theorem fullIntersection_boundary (f b : FullCycle hN hM)
    (hb : b ∈ ribbonBoundarySpace hN hM (openRCConfig N M)) :
    fullIntersection hN hM f b = 0 := by
  obtain ⟨F, hF⟩ := hb
  let p := fun u => F ((openBoundaryFaceEquiv hN hM).symm (whiteAbove hM u))
  have he (e : FullEdge N M) (a : Bool) :
      F (ribbonBoundaryOf hN hM _ (ribbonEndEquiv hN hM (e.val, a))) =
        p (faceEndpoint hN hM true (e.val.1, prv e.val.2) (a ^^ checker e.val)) := by
    dsimp only [p]
    rw [← boundaryEnd_eq_whiteAbove, Equiv.symm_apply_apply]
  have hm (e : FullEdge N M) :
      fullIntersectionCoefficient f.val e * b.val e =
        diamondCoboundary hN hM _ p (fullUp.symm e) * f.val (fullUp.symm e) := by
    rw [← congrFun (congrArg Subtype.val hF) e]
    change (_ * _) * (F _ - F _) = _
    rw [he, he, diamondCoboundary_apply]
    change _ = (p (faceEndpoint hN hM true (e.val.1, prv e.val.2) true) -
      p (faceEndpoint hN hM true (e.val.1, prv e.val.2) false)) * fullFlowAt f.val (e.val.1, prv e.val.2)
    cases checker e.val <;> simp <;> ring
  change (∑ e, fullIntersectionCoefficient f.val e * b.val e) = 0
  simp_rw [hm]
  rw [Equiv.sum_comp fullUp.symm (fun e => diamondCoboundary hN hM _ p e * f.val e),
    ← diamondBoundary_pairing, f.property]
  simp

private theorem fullIntersection_vertical_left (g : FullCycle hN hM) :
    fullIntersection hN hM (verticalDiamondCycle hN hM) g = diamondHorizontalDisplacement _ g.val := by
  change (∑ e : FullEdge N M, (_ * 1) * g.val e) = _
  simp [diamondHorizontalDisplacement]

private theorem fullIntersection_horizontal_left (g : FullCycle hN hM) :
    fullIntersection hN hM (horizontalDiamondCycle hN hM) g = -diamondVerticalDisplacement _ g.val := by
  change (∑ e : FullEdge N M, _ * g.val e) = _
  rw [diamondVerticalDisplacement, neg_neg]
  apply sum_congr rfl
  intro e _
  unfold fullIntersectionCoefficient fullFlowAt
  change ((_ : ℚ) * (if checker (e.val.1, prv e.val.2) then 1 else -1)) * _ = _
  rw [checker_prv_y hM]
  cases checker e.val <;> simp

private theorem fullIntersection_horizontal_right (f : FullCycle hN hM) :
    fullIntersection hN hM f (horizontalDiamondCycle hN hM) = diamondVerticalDisplacement _ f.val := by
  change (∑ e : FullEdge N M, fullIntersectionCoefficient f.val e * (if checker e.val then 1 else -1)) = _
  unfold diamondVerticalDisplacement
  rw [← sum_neg_distrib, ← Equiv.sum_comp fullUp.symm (fun e => -f.val e)]
  apply sum_congr rfl
  intro e _
  unfold fullIntersectionCoefficient
  change ((if checker e.val then (-1 : ℚ) else 1) * f.val (fullUp.symm e)) * _ = _
  cases checker e.val <;> simp

include hM in
private theorem full_sign_sum : (∑ e : FullEdge N M, if checker e.val then (1 : ℚ) else -1) = 0 := by
  let s : FullEdge N M → ℚ := fun e => if checker e.val then 1 else -1
  have hx (e : FullEdge N M) : s (fullUp e) = -s e := by
    change (if checker (e.val.1, nxt e.val.2) then (1 : ℚ) else -1) = _
    rw [checker_nxt_y hM]
    cases hc : checker e.val <;> grind
  have h := Equiv.sum_comp fullUp s
  simp only [hx, sum_neg_distrib] at h
  linarith

private theorem displacement_vertical : diamondDisplacementMap hN hM _ (verticalDiamondCycle hN hM) =
    (0, -(N * M : ℚ)) := by
  rw [diamondDisplacementMap_apply]
  apply Prod.ext
  · change (∑ e : FullEdge N M, (if checker e.val then (-1 : ℚ) else 1) * 1) = 0
    have he (e : FullEdge N M) : (if checker e.val then (-1 : ℚ) else 1) * 1 =
        -(if checker e.val then 1 else -1) := by cases checker e.val <;> norm_num
    simp_rw [he, sum_neg_distrib, full_sign_sum hM, neg_zero]
  · change -(∑ _ : FullEdge N M, (1 : ℚ)) = _
    simp [card_openDiamondEdge, openCount_open]

private theorem displacement_horizontal : diamondDisplacementMap hN hM _ (horizontalDiamondCycle hN hM) =
    (-(N * M : ℚ), 0) := by
  rw [diamondDisplacementMap_apply]
  apply Prod.ext
  · change (∑ e : FullEdge N M, (if checker e.val then (-1 : ℚ) else 1) *
        (if checker e.val then 1 else -1)) = _
    calc
      _ = ∑ _ : FullEdge N M, (-1 : ℚ) := sum_congr rfl fun e _ => by split <;> simp_all
      _ = _ := by simp [card_openDiamondEdge, openCount_open]
  · simpa [diamondVerticalDisplacement, horizontalDiamondCycle, horizontalDiamondFlow] using
      congrArg Neg.neg (full_sign_sum (N := N) hM)

/-- Zero displacement is exactly the cellular boundary space of the full torus. -/
theorem fullDiamondDisplacement_eq_zero_iff (hNp : 0 < N) (hMp : 0 < M) (f : FullCycle hN hM) :
    diamondDisplacementMap hN hM _ f = 0 ↔ f ∈ ribbonBoundarySpace hN hM (openRCConfig N M) := by
  let B := ribbonBoundarySpace hN hM (openRCConfig N M)
  let D := diamondDisplacementMap hN hM (openRCConfig N M)
  have hb : B ≤ LinearMap.ker D := by
    intro g hg
    apply LinearMap.mem_ker.mpr
    have hx := fullIntersection_boundary hN hM (verticalDiamondCycle hN hM) g hg
    have hy := fullIntersection_boundary hN hM (horizontalDiamondCycle hN hM) g hg
    rw [fullIntersection_vertical_left] at hx
    rw [fullIntersection_horizontal_left, neg_eq_zero] at hy
    exact Prod.ext hx hy
  let Q := B.liftQ D hb
  have hdim : finrank ℚ (CappedRibbonHomology hN hM (openRCConfig N M)) = finrank ℚ (ℚ × ℚ) := by
    rw [finrank_cappedRibbonHomology_open hN hM hNp hMp, Module.finrank_prod, finrank_self]
  have hn : (N * M : ℚ) ≠ 0 := by positivity
  have hq : Function.Injective Q := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    rintro ⟨x,y⟩
    refine ⟨B.mkQ ((-x / (N * M : ℚ)) • horizontalDiamondCycle hN hM +
      (-y / (N * M : ℚ)) • verticalDiamondCycle hN hM), ?_⟩
    change D _ = _
    rw [map_add, map_smul, map_smul, show D _ = (-(N * M : ℚ), 0) from displacement_horizontal hN hM,
      show D _ = (0, -(N * M : ℚ)) from displacement_vertical hN hM]
    simp [hn]
  exact ⟨fun hf => (Submodule.Quotient.mk_eq_zero B).mp (hq (show Q (B.mkQ f) = Q 0 by rw [map_zero]; exact hf)),
    fun hf => LinearMap.mem_ker.mp (hb hf)⟩

/-- A vertical flow intersects any nonzero horizontal displacement. -/
theorem horizontalDisplacement_zero_of_intersection_zero (hNp : 0 < N) (hMp : 0 < M)
    (f g : FullCycle hN hM) (hf : diamondVerticalDisplacement _ f.val ≠ 0)
    (hg : diamondVerticalDisplacement _ g.val = 0) (hi : fullIntersection hN hM f g = 0) :
    diamondHorizontalDisplacement _ g.val = 0 := by
  let c := diamondHorizontalDisplacement _ g.val / (N * M : ℚ)
  have hn : (N * M : ℚ) ≠ 0 := by positivity
  have hb : g + c • horizontalDiamondCycle hN hM ∈ ribbonBoundarySpace hN hM (openRCConfig N M) := by
    apply (fullDiamondDisplacement_eq_zero_iff hN hM hNp hMp _).mp
    rw [map_add, map_smul, displacement_horizontal, diamondDisplacementMap_apply]
    ext <;> simp [c, hg, hn]
  have := fullIntersection_boundary hN hM f _ hb
  rw [map_add, map_smul, hi, fullIntersection_horizontal_right] at this
  simpa [c, hn, hf] using this

end
end PottsDiscontinuity.Torus
