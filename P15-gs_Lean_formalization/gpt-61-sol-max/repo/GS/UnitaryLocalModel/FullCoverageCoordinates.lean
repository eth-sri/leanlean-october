
import GS.UnitaryLocalModel.DephasedEuclidean
import GS.UnitaryLocalModel.FactorDephasing
import GS.UnitaryLocalModel.TopologyOuter
import GS.UnitaryLocalModel.AxisConjugation



/-!
# Small coordinate neighbourhoods and full factor normalization

The inverse dephased chart supplies genuinely small coordinates for both
middle factors. Their midpoint and half-difference belong to the compact
parameter box, and anchor normalization gives the exact full matrix image.
-/
open Matrix GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

variable (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)

private theorem midpoint_energy_le {d : ℕ} (a b : Fin d → ℝ) :
    localEnergy (fun i => (a i+b i)/2) ≤ (localEnergy a+localEnergy b)/2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show ((a i+b i)/2)^2 ≤ ((a i)^2+(b i)^2)/2 by nlinarith [sq_nonneg (a i-b i)])
  simpa only [localEnergy, ← Finset.sum_div, Finset.sum_add_distrib] using h

@[simp] theorem euclideanDephasedCoordinates_base :
    euclideanDephasedCoordinates Q o hQ (dephasedBase Q o hQ) = 0 := by
  simp [euclideanDephasedCoordinates, dephasedCoordinates, dephasedBase,
    unitaryConstraintChart_base]

variable (r : ℝ)

def smallDephasedSource  : Set (DephasedUnitary Q o) :=
  {A | A ∈ dephasedChartSource Q o hQ ∧
    localEnergy (euclideanDephasedCoordinates Q o hQ A) < r^2}

theorem smallDephasedSource_open  : IsOpen (smallDephasedSource Q o hQ r) := by
  have hc :=
    continuous_subtype_val.comp (euclideanDephasedChartHomeomorph Q o hQ).continuous
  change IsOpen (dephasedChartSource Q o hQ ∩
    {A | localEnergy (euclideanDephasedCoordinates Q o hQ A) < r^2})
  rw [← Subtype.image_preimage_val]
  exact (dephasedChartSource_open Q o hQ).isOpenMap_subtype_val _
    (isOpen_lt ((continuous_localEnergy _).comp hc) continuous_const)

theorem base_mem_smallDephasedSource  (hr : 0<r) :
    dephasedBase Q o hQ ∈ smallDephasedSource Q o hQ r := by
  refine ⟨base_mem_dephasedChartSource Q o hQ, ?_⟩
  simpa [euclideanDephasedCoordinates_base, localEnergy] using sq_pos_of_pos hr

/-- All anchor-good factors with sufficiently small dephased inverse coordinates. -/
def smallAnchorFactors  : Set (anchorFactorSet Q o) :=
  {p | dephasedFirst Q o p ∈ smallDephasedSource Q o hQ r ∧
    dephasedSecond Q o p ∈ smallDephasedSource Q o hQ r}

def smallFullFactors  : Set (SmallFactorSpace q) :=
  Subtype.val '' smallAnchorFactors Q o hQ r

theorem smallFullFactors_open  : IsOpen (smallFullFactors Q o hQ r) := by
  apply (anchorFactorSet_open Q o).isOpenMap_subtype_val
  exact ((smallDephasedSource_open Q o hQ r).preimage (continuous_dephasedFirst Q o)).inter
    ((smallDephasedSource_open Q o hQ r).preimage (continuous_dephasedSecond Q o))

/-- The phase-normalized blocks reconstruct the original matrix exactly. -/
theorem smallFullFactors_map_mem  (p : SmallFactorSpace q)
    (hp : p ∈ smallFullFactors Q o hQ r) :
    smallFactorValue q p ∈ FullCompactImage (euclideanDephasedParametrization Q o hQ) o r := by
  obtain ⟨p,hp,rfl⟩ := hp
  let a := euclideanDephasedCoordinates Q o hQ (dephasedFirst Q o p)
  let b := euclideanDephasedCoordinates Q o hQ (dephasedSecond Q o p)
  let c := (a+b)/2
  let z := (a-b)/2
  have hca : c+z=a := by ext i; dsimp [c,z]; ring
  have hcb : c-z=b := by ext i; dsimp [c,z]; ring
  have ha := hp.1.2
  have hb := hp.2.2
  have hc : localEnergy c ≤ r^2 := (midpoint_energy_le a b).trans (by linarith)
  have hz : localEnergy z ≤ r^2 := by
    have h : localEnergy z ≤ (localEnergy a+localEnergy b)/2 := by
      simpa [z,localEnergy,sub_eq_add_neg] using midpoint_energy_le a (-b)
    linarith
  have hea := euclideanDephasedParametrization_coordinates Q o hQ
    (dephasedFirst Q o p) hp.1.1
  have heb := euclideanDephasedParametrization_coordinates Q o hQ
    (dephasedSecond Q o p) hp.2.1
  let U := p.val.val.1
  let V := p.val.val.2.2.2
  let A := p.val.val.2.1
  let B := p.val.val.2.2.1
  have hU := p.val.property.1
  have hV := p.val.property.2.2.2
  let L := phaseGaugeLeft U V Q.val A B o
  let R := phaseGaugeRight V Q.val A B o
  have hL : ∀ i, Unitary (L i) := fun i =>
    ((hU i).mul (rowPhaseDiagonal_unitary p.property.1 p.property.2 i)).mul (hV o)
  have hR : ∀ j, Unitary (R j) := fun j =>
    ((((hV o).conjTranspose).mul (rowPhaseDiagonal_unitary p.property.1 p.property.2 o).conjTranspose).mul
      (by
        apply diagonal_unitary_of_norm_one
        intro k
        fin_cases k
        · exact norm_phase (div_ne_zero (p.property.1.2 j).2 (p.property.1.2 j).1)
        · exact norm_phase (div_ne_zero (p.property.2.2 j).2 (p.property.2.2 j).1))).mul (hV j)
  have hRo : R o=1 := by
    dsimp only [R,phaseGaugeRight]
    rw [colPhaseDiagonal_anchor]
    have hE := rowPhaseDiagonal_unitary p.property.1 p.property.2 o
    calc
      _ = (V o)ᴴ * ((rowPhaseDiagonal Q.val A B o o)ᴴ *
          rowPhaseDiagonal Q.val A B o o) * V o := by grind
      _ = 1 := by rw [hE.1, Matrix.mul_one, (hV o).1]
  obtain ⟨u,hu,hdiag⟩ := exists_axis_of_unitary (V o) (hV o)
  let g : OuterFactors q o := outerOfMatrices L R hL hR
  let t : localParameterBox ((q-1)^2) r := ⟨(c,z,u),hc,hz,hu⟩
  refine ⟨(g,t),?_⟩
  apply (blockFamilyHomeomorph q).symm.injective
  change extractBlockFamily (fullCompactMiddle _ o r (g,t)) =
    extractBlockFamily (smallFactorValue q p.val)
  rw [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily]
  funext i j
  have hn := phase_normalization_block U V Q.val A B o i j (hU i) (hV j)
  have he : L i * middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u * R j =
      U i * diagTwo (A i j) (B i j) * V j := by
    rw [← hdiag, ← hn]
    calc
      _ = (L i * (L i)ᴴ) * (U i * diagTwo (A i j) (B i j) * V j) *
          ((R j)ᴴ * R j) := by grind
      _ = _ := by rw [(hL i).2,(hR j).1]; simp
  have hright : outerRight g = R := by
    grind [asFullUnitary,outerOfMatrices,outerRight]
  rw [show outerLeft g = L from rfl, hright]
  have hmiddle : chartBlockFamily (euclideanDephasedParametrization Q o hQ) t.val i j =
      middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u := by
    change middleBlock (euclideanDephasedParametrization Q o hQ (c+z) i j)
      (euclideanDephasedParametrization Q o hQ (c-z) i j) u = _
    rw [hca,hcb,hea,heb]
    rfl
  rw [hmiddle,he]
  ext k l
  exact (smallFactorMap_block p.val.val i j k l).symm

end GS.UnitaryLocalModel
