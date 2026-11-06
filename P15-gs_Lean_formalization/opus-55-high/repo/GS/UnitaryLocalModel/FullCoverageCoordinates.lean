module

public import GS.UnitaryLocalModel.DephasedEuclidean
public import GS.UnitaryLocalModel.FactorDephasing
public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryLocalModel.AxisConjugation

@[expose] public section


/-!
# Small coordinate neighbourhoods and full factor normalization

The inverse dephased chart supplies genuinely small coordinates for both
middle factors. Their midpoint and half-difference belong to the compact
parameter box, and anchor normalization gives the exact full matrix image.
-/
noncomputable section
open Matrix GS GS.UnitaryNonmanifold GS.NonmanifoldCompletion Set
namespace GS.UnitaryLocalModel
variable {q : ℕ}

section
variable (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ)
def smallDephasedSource : Set (DephasedUnitary Q o) :=
  {A | A ∈ dephasedChartSource Q o hQ ∧
    localEnergy (euclideanDephasedCoordinates Q o hQ A) < r^2}

theorem smallDephasedSource_open : IsOpen (smallDephasedSource Q o hQ r) :=
  ContinuousOn.isOpen_inter_preimage (f := euclideanDephasedCoordinates Q o hQ) (t := {x | localEnergy x < r^2})
    (continuousOn_iff_continuous_domRestrict.2
    ((dephasedCoordinateEquiv Q o hQ).continuous.comp (continuous_snd.comp ((unitaryConstraintChart Q o hQ).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun A => A.2))))
    (dephasedChartSource_open Q o hQ) (isOpen_lt (continuous_localEnergy _) continuous_const)

theorem base_mem_smallDephasedSource (hr : 0<r) :
    dephasedBase Q o hQ ∈ smallDephasedSource Q o hQ r := by
  refine ⟨base_mem_unitaryConstraintChart_source Q o hQ, ?_⟩
  simpa [euclideanDephasedCoordinates, dephasedCoordinates, dephasedBase,
    unitaryConstraintChart_base, localEnergy] using sq_pos_of_pos hr

/-- All anchor-good factors with sufficiently small dephased inverse coordinates. -/
def smallAnchorFactors : Set (anchorFactorSet Q o) :=
  {p | dephasedFirst Q o p ∈ smallDephasedSource Q o hQ r ∧
    dephasedSecond Q o p ∈ smallDephasedSource Q o hQ r}

def smallFullFactors : Set (SmallFactorSpace q) :=
  Subtype.val '' smallAnchorFactors Q o hQ r

theorem smallFullFactors_open : IsOpen (smallFullFactors Q o hQ r) := by
  apply (anchorFactorSet_open Q o).isOpenMap_subtype_val
  exact ((smallDephasedSource_open Q o hQ r).preimage (continuous_dephased Q o).1).inter
    ((smallDephasedSource_open Q o hQ r).preimage (continuous_dephased Q o).2)

/-- The phase-normalized blocks reconstruct the original matrix exactly. -/
theorem smallFullFactors_map_mem (p : SmallFactorSpace q)
    (hp : p ∈ smallFullFactors Q o hQ r) :
    smallFactorValue q p ∈ FullCompactImage (euclideanDephasedParametrization Q o hQ) o r := by
  obtain ⟨p,hp,rfl⟩ := hp
  let a := euclideanDephasedCoordinates Q o hQ (dephasedFirst Q o p)
  let b := euclideanDephasedCoordinates Q o hQ (dephasedSecond Q o p)
  have key (s : ℝ) (hs : s^2 = 1) : localEnergy (fun i => (a i+s*b i)/2) ≤ r^2 := by
    have := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      show ((a i+s*b i)/2)^2 ≤ ((a i)^2+(b i)^2)/2 by nlinarith [sq_nonneg (a i-s*b i), congrArg (· * b i ^ 2) hs]
    have := hp.1.2; have := hp.2.2
    simp only [localEnergy, ← Finset.sum_div, Finset.sum_add_distrib] at *
    linarith
  let c : Fin ((q-1)^2) → ℝ := fun i => (a i+1*b i)/2
  let z : Fin ((q-1)^2) → ℝ := fun i => (a i+-1*b i)/2
  have hca : c+z=a := by ext i; simp; ring
  have hcb : c-z=b := by ext i; simp; ring
  have hea := euclideanDephasedParametrization_coordinates Q o hQ _ hp.1.1
  have heb := euclideanDephasedParametrization_coordinates Q o hQ _ hp.2.1
  let U := p.val.val.1
  let V := p.val.val.2.2.2
  let A := p.val.val.2.1
  let B := p.val.val.2.2.1
  have hU := p.val.property.1
  have hV := p.val.property.2.2.2
  let L := phaseGaugeLeft U V Q.val A B o
  let R := phaseGaugeRight V Q.val A B o
  have hL := phaseGaugeLeft_unitary U V Q.val A B o hU hV p.property.1 p.property.2
  have hR := phaseGaugeRight_unitary V Q.val A B o hV p.property.1 p.property.2
  have hRo : R o = 1 := by
    simp only [R, phaseGaugeRight, colPhaseDiagonal_anchor]
    rw [Matrix.mul_assoc (V o)ᴴ, (rowPhaseDiagonal_unitary (A := A) (B := B) p.property.1 p.property.2 o).1, Matrix.mul_one, (hV o).1]
  obtain ⟨u,hu,hdiag⟩ := exists_axis_of_unitary (V o) (hV o)
  let g : OuterFactors q o := outerOfMatrices L R hL hR
  let t : localParameterBox ((q-1)^2) r := ⟨(c,z,u),key 1 (by norm_num),key (-1) (by norm_num),hu⟩
  refine ⟨(g,t),?_⟩
  apply (blockFamilyHomeomorph q).symm.injective
  change extractBlockFamily (fullCompactMiddle _ o r (g,t)) =
    extractBlockFamily (smallFactorValue q p.val)
  rw [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily]
  funext i j
  have hn := phase_normalization_block U V Q.val A B o i j (hU i) (hV j)
  have he : L i * middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u * R j =
      U i * diagTwo (A i j) (B i j) * V j := by
    calc
      _ = (L i * (L i)ᴴ) * (U i * diagTwo (A i j) (B i j) * V j) *
          ((R j)ᴴ * R j) := by grind
      _ = _ := by rw [(hL i).2,(hR j).1]; simp
  rw [show outerLeft g = L from rfl, outerRight_ofMatrices L R hL hR hRo]
  have hmiddle : chartBlockFamily (euclideanDephasedParametrization Q o hQ) t.val i j =
      middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u := by
    change middleBlock (euclideanDephasedParametrization Q o hQ (c+z) i j)
      (euclideanDephasedParametrization Q o hQ (c-z) i j) u = _
    aesop
  simp_all
  ext k l
  exact (smallFactorMap_block p.val.val i j k l).symm

end

end GS.UnitaryLocalModel
