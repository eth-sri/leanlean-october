module
public import Mathlib

public import PottsDiscontinuity.Torus.DiamondCounts
public import PottsDiscontinuity.Torus.RibbonBoundary

/-!
# Boundary components of the fully open primal torus

The complementary white faces are exactly the clockwise boundary cycles. This
counts them directly, without using the Euler relation to define a face count.
-/

@[expose] public section



namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The configuration with every indexed primal edge open. -/
def openRCConfig (N M : ℕ) : RCConfig N M := fun _ => true

@[simp] theorem edgeReverse_twice (d : Dart N M) : edgeReverse (edgeReverse d) = d :=
  edgeReverse_involutive d

/-- White-face boundary corners oriented with the white face on the right. -/
def whiteCornerEquiv (hN : Even N) (hM : Even M) :
    FaceVertex N M false × Port ≃ DirectedDart (checkerArrows N M) where
  toFun x := ⟨edgeReverse (faceCorner x.1.val x.2), by
    rw [dartOut_edgeReverse, dartOut_checker_eq_leftFace hN hM,
      leftFace_faceCorner, x.1.property]
    rfl⟩
  invFun d := (⟨leftFace (edgeReverse d.val), by
    rw [← dartOut_checker_eq_leftFace hN hM, dartOut_edgeReverse, d.property]
    rfl⟩, (edgeReverse d.val).2)
  left_inv x := by
    apply Prod.ext
    · simp_all
    · change (edgeReverse (edgeReverse (faceCorner x.1.val x.2))).2 = x.2
      rw [edgeReverse_twice]
      cases x.2 <;> rfl
  right_inv d := Subtype.ext (by
    simp_all)

section

variable (hN : Even N) (hM : Even M) (v : FaceVertex N M false) (p : Port)


@[simp] theorem whiteCornerEquiv_val  :
    (whiteCornerEquiv hN hM (v, p)).val = edgeReverse (faceCorner v.val p) := rfl

theorem ribbonBoundary_open_corner  :
    ribbonBoundary hN hM (openRCConfig N M) (whiteCornerEquiv hN hM (v, p)) =
      whiteCornerEquiv hN hM (v, cwPort p) := by
  rw [ribbonBoundary_eq_directedStep]
  apply Subtype.ext
  change strandReverse (rcSmoothing (openRCConfig N M))
    (edgeReverse (edgeReverse (faceCorner v.val p))) = edgeReverse (faceCorner v.val (cwPort p))
  
  rcases v with ⟨⟨i, j⟩, hv⟩
  cases p <;> simp only [faceCorner, strandReverse, rcSmoothing, openRCConfig, Bool.xor_true, checker_nxt_x hN, checker_nxt_y hM, hv, Bool.not_false, Bool.not_true, pairedPort, edgeReverse, cwPort, Equiv.symm_apply_apply]

theorem ribbonBoundary_open_pow_corner  (n : ℕ) :
    (ribbonBoundary hN hM (openRCConfig N M) ^ n) (whiteCornerEquiv hN hM (v, p)) =
      whiteCornerEquiv hN hM (v, (ccwPortPerm.symm ^ n) p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, ribbonBoundary_open_corner, pow_succ']
    rfl

end

theorem sameCycle_ribbonBoundary_open (hN : Even N) (hM : Even M)
    (d e : DirectedDart (checkerArrows N M)) :
    (ribbonBoundary hN hM (openRCConfig N M)).SameCycle d e ↔
      leftFace (edgeReverse d.val) = leftFace (edgeReverse e.val) := by
  constructor
  · apply sameCycle_invariant (ribbonBoundary hN hM (openRCConfig N M))
       fun d  => leftFace (edgeReverse d.val) 
    intro x
    obtain ⟨⟨v, p⟩, rfl⟩ := (whiteCornerEquiv hN hM).surjective x
    rw [ribbonBoundary_open_corner]
    simp_all
  · intro hde
    obtain ⟨⟨v, p⟩, rfl⟩ := (whiteCornerEquiv hN hM).surjective d
    obtain ⟨⟨w, q⟩, rfl⟩ := (whiteCornerEquiv hN hM).surjective e
    have hvw : v = w := Subtype.ext (by
      simp_all)
    subst w
    have hc : ∀ p q , ∃ n : Fin 4, (ccwPortPerm.symm ^ n.val) p = q := by decide
    obtain ⟨n, hn⟩ := hc p q
    refine ⟨n.val, ?_⟩
    rw [zpow_natCast, ribbonBoundary_open_pow_corner, hn]

/-- Each full-primal boundary component is a specific white face. -/
def openBoundaryFaceEquiv (hN : Even N) (hM : Even M) :
    RibbonBoundaryComponent hN hM (openRCConfig N M) ≃ FaceVertex N M false where
  toFun := Quotient.lift (fun d => ⟨leftFace (edgeReverse d.val), by
    rw [← dartOut_checker_eq_leftFace hN hM, dartOut_edgeReverse, d.property]
    rfl⟩)  fun _ _ h => Subtype.ext ((sameCycle_ribbonBoundary_open hN hM _ _).mp h) 
  invFun v := Quotient.mk _ (whiteCornerEquiv hN hM (v, .east))
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro d
    apply Quotient.sound
    apply (sameCycle_ribbonBoundary_open hN hM _ _).mpr
    all_goals simp_all
  right_inv v := Subtype.ext (by
    simp_all)

theorem rcLoopCount_open (hN : Even N) (hM : Even M) :
    rcLoopCount hN hM (openRCConfig N M) = N * M / 2 := by
  rw [← card_ribbonBoundaryComponent,
    Nat.card_congr (openBoundaryFaceEquiv hN hM), Nat.card_eq_fintype_card, card_faceVertex hN]

@[simp] theorem openCount_open : openCount (openRCConfig N M) = N * M := by
  simp only [openCount, openRCConfig, Finset.filter_true, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]

end PottsDiscontinuity.Torus
