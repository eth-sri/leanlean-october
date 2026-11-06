import RequestProject.QCubeSquareFlags


/-! Faithful indexing of the actual square flags by their signs and endpoints. -/

namespace FiniteChains.Davis
open RACG Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareEndpointFlag (c : QCube A) a b (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : ZMod 2 × Bool) :=
  if i.2 then squarePositiveFlag c a b hne hs i.1 else squareNegativeFlag c a b hne hs i.1

theorem squareEndpointFlag_injective (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareEndpointFlag c a b hne hs) := by
  intro ⟨s, e⟩ ⟨t, f⟩ h
  have hm := congrArg (·.1.2.1.sgn a) h
  have hv := congrArg (·.1.1.sgn b) h
  have hb (r : ZMod 2) :=
    (qCubeFacet c a r).sgn_eq_zero b (by grind [squareFacet_w_spx c hne hs r])
  cases e <;> cases f
  · have hst : s = t := by simpa [squareEndpointFlag, squareNegativeFlag] using hm
    simp_all
  · simp [squareEndpointFlag, squareNegativeFlag, squarePositiveFlag,
      cubeNegativeVertex, cubePositiveVertex, hb] at hv
  · simp [squareEndpointFlag, squareNegativeFlag, squarePositiveFlag,
      cubeNegativeVertex, cubePositiveVertex, hb] at hv
  · have hst : s = t := by simpa [squareEndpointFlag, squarePositiveFlag] using hm
    simp_all

theorem squareEndpointFlag_middle (c : QCube A) a b hne
    hs i :
    (squareEndpointFlag c a b hne hs i).1.2.1 = qCubeFacet c a i.1 := by
  cases' i with s e
  cases e <;> rfl

/-- A finite index for all eight actual flags: facet direction, fixed sign, endpoint. -/
def squareFlag (c : QCube A) a b (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :=
  if i.1 then squareEndpointFlag c a b hne hs i.2 else
    squareEndpointFlag c b a hne.symm (by grind) i.2

theorem squareFlag_injective (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareFlag c a b hne hs) := by
  intro ⟨e, i⟩ ⟨f, j⟩ h
  have hcross (i j : ZMod 2 × Bool) :
      squareEndpointFlag c a b hne hs i ≠
        squareEndpointFlag c b a hne.symm (by grind) j := by
    intro he
    have hm := congrArg (·.1.2.1.spx) he
    grind [squareEndpointFlag_middle, squareFacet_w_spx c hne hs, squareFacet_v_spx c hne hs]
  cases e <;> cases f
  · have hij := squareEndpointFlag_injective c b a hne.symm
      _ h
    simp_all
  · tauto
  · tauto
  · exact Prod.ext rfl (squareEndpointFlag_injective c a b hne hs h)

/-- The finite index covers every strict triangle topped by the chosen square. -/
theorem squareFlag_surjective_on_top c a b hne
    hs (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 = c) :
    ∃ i, squareFlag c a b hne hs i = t := by
  obtain ⟨s, hp | hn | hp | hn⟩ := squareFlags_exhaustive c a b hne hs t ht
  · exact ⟨(true, s, true), hp.symm⟩
  · exact ⟨(true, s, false), hn.symm⟩
  · exact ⟨(false, s, true), hp.symm⟩
  · exact ⟨(false, s, false), hn.symm⟩

/-- Extract the eight actual integer flag coefficients of a square. -/
noncomputable def squareFlagCoordinates (c : QCube A) a b (hne : a ≠ b)
    (hs : c.spx = {a, b}) : ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ]
      ((Bool × ZMod 2 × Bool) →₀ ℤ) :=
  Finsupp.lcomapDomain _ (squareFlag_injective c a b hne hs)

theorem squareFlagCoordinates_apply c a b hne
    hs (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    i :
    squareFlagCoordinates c a b hne hs z i = z (squareFlag c a b hne hs i) := rfl

/-- Every actual chain supported on this square is recovered from its eight coefficients. -/
theorem squareFlagCoordinates_reconstruct c a b hne
    hs (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2 = c) :
    Finsupp.mapDomain (squareFlag c a b hne hs)
      (squareFlagCoordinates c a b hne hs z) = z := by
  apply Finsupp.mapDomain_comapDomain _ (squareFlag_injective c a b hne hs)
  intro t ht
  exact squareFlag_surjective_on_top c a b hne hs t (hz t ht)

theorem squareFlagCoordinates_single (c : QCube A) a b hne
    hs i n :
    squareFlagCoordinates c a b hne hs (Finsupp.single (squareFlag c a b hne hs i) n) =
      Finsupp.single i n :=
  Finsupp.comapDomain_single _ _ _ _

/-- The signed coefficient vector of the genuine square subdivision. -/
theorem squareFlagCoordinates_subdivision (c : QCube A) a b hne
    hs :
    squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs) =
      Finsupp.single (false, 0, false) 1 - Finsupp.single (false, 0, true) 1 -
      (Finsupp.single (false, 1, false) 1 - Finsupp.single (false, 1, true) 1) -
      (Finsupp.single (true, 0, false) 1 - Finsupp.single (true, 0, true) 1) +
      (Finsupp.single (true, 1, false) 1 - Finsupp.single (true, 1, true) 1) := by
  rw [cubeSquareSubdivision_flags]
  change squareFlagCoordinates c a b hne hs
    (Finsupp.single (squareFlag c a b hne hs (false, 0, false)) 1 -
     Finsupp.single (squareFlag c a b hne hs (false, 0, true)) 1 -
     (Finsupp.single (squareFlag c a b hne hs (false, 1, false)) 1 -
      Finsupp.single (squareFlag c a b hne hs (false, 1, true)) 1) -
     (Finsupp.single (squareFlag c a b hne hs (true, 0, false)) 1 -
      Finsupp.single (squareFlag c a b hne hs (true, 0, true)) 1) +
     (Finsupp.single (squareFlag c a b hne hs (true, 1, false)) 1 -
      Finsupp.single (squareFlag c a b hne hs (true, 1, true)) 1)) = _
  simp [map_add, map_sub, squareFlagCoordinates_single]
