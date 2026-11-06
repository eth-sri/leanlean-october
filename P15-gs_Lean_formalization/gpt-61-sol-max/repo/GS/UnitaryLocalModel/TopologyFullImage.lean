import Mathlib.Tactic

import GS.UnitaryLocalModel.TopologyOuter
import GS.UnitaryLocalModel.NormalizedPositivity




/-!
# The full compact unitary local model

The actual matrix image, including all outer factors, is homeomorphic to the
product of the anchored outer unitary group and the bounded rank-one cone.
The proof uses positive-anchor uniqueness and compact equal-fibre maps.
-/
open scoped ComplexOrder
namespace GS.UnitaryLocalModel

variable (Q : CMat q)

variable (o : Fin q)

/-- The positivity properties of the dephased chart needed by outer recovery. -/
def PositiveChartAnchors  
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ U, (∀ i, ∃ a : ℝ, 0 < a ∧ ψ x i o / Q i o = a) ∧
    (∀ j, ∃ a : ℝ, 0 < a ∧ ψ x o j / Q o j = a)

theorem chartBlockFamily_positive  
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hpos : PositiveChartAnchors Q o ψ U) (p : LocalParameters d)
    (hp : p.1+p.2.1 ∈ U) (hm : p.1-p.2.1 ∈ U) (hu : OnSphere p.2.2) :
    NormalizedPositiveAnchors Q o (chartBlockFamily ψ p) := by
  constructor
  · intro i
    exact middleBlock_ratio_posDef _ _ _ _ hu ((hpos _ hp).1 i) ((hpos _ hm).1 i)
  · intro j
    exact middleBlock_ratio_posDef _ _ _ _ hu ((hpos _ hp).2 j) ((hpos _ hm).2 j)

/-- The full compact parametrization has precisely the outer-plus-cone fibres. -/
theorem fullCompactMiddle_fibres  
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψ : Set.InjOn ψ U) (hpos : PositiveChartAnchors Q o ψ U) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U)
    (p p' : FullCompactParameters q o d r) :
    fullCompactMiddle ψ o r p = fullCompactMiddle ψ o r p' ↔
      p.1 = p'.1 ∧ parameterCone p.2.val = parameterCone p'.2.val := by
  rcases p with ⟨g,⟨⟨c,z,u⟩,hp⟩⟩
  rcases p' with ⟨g',⟨⟨c',z',v⟩,hp'⟩⟩
  let L := outerLeft g
  let R := outerRight g
  let L' := outerLeft g'
  let R' := outerRight g'
  let N := chartBlockFamily ψ (c,z,u)
  let N' := chartBlockFamily ψ (c',z',v)
  have hN := chartBlockFamily_positive Q o ψ U hpos (c,z,u)
    (hargs _ hp).1 (hargs _ hp).2 hp.2.2
  have hN' := chartBlockFamily_positive Q o ψ U hpos (c',z',v)
    (hargs _ hp').1 (hargs _ hp').2 hp'.2.2
  let φ := fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2
  have hφ : Set.InjOn φ U := by
    simpa only [φ,Set.InjOn,funext_iff,Prod.forall,← Matrix.ext_iff] using hψ
  obtain ⟨hcp,hcm⟩ := hargs _ hp
  obtain ⟨hcp',hcm'⟩ := hargs _ hp'
  have hu := hp.2.2
  have hv := hp'.2.2
  have hm : N = N' ↔ c = c' ∧ sphereOuter u z = sphereOuter v z' := by
    constructor
    · intro h
      have hs : φ (c+z)+φ (c-z) = φ (c'+z')+φ (c'-z') := by
        funext j
        simpa only [φ,N,N',chartBlockFamily,parameterMiddle,chartMiddle,middleBlock_trace,Pi.add_apply]
          using congrArg Matrix.trace (congrFun (congrFun h j.1) j.2)
      have ho : sphereOuter u (realify (φ (c+z)-φ (c-z))) =
          sphereOuter v (realify (φ (c'+z')-φ (c'-z'))) := by
        ext i j
        have hh := congrFun (congrArg axisCoefficient (congrFun (congrFun h j.1.1) j.1.2)) i
        simp only [N,N',chartBlockFamily,parameterMiddle,chartMiddle,middleBlock_axisCoefficient] at hh
        by_cases hj : j.2 = 0
        · simpa [φ,sphereOuter,realify,hj] using congrArg Complex.re hh
        · simpa [φ,sphereOuter,realify,hj] using congrArg Complex.im hh
      have hd := (sphereOuter_fibres hu hv).mp ho
      simp only [← map_zero realify,← map_neg realify,realify_injective.eq_iff] at hd
      have h₃ := hφ hcp hcp'
      have h₄ := hφ hcm hcm'
      have h₅ := hφ hcp hcm'
      have h₆ := hφ hcm hcp'
      rw [sphereOuter_fibres hu hv]
      grind
    · aesop (add norm [chartMiddle,sphereOuter_fibres,middleBlock_equal,middleBlock_simultaneous_swap,parameterMiddle,chartBlockFamily])
  unfold fullCompactMiddle fullBlockImage
  rw [(Function.LeftInverse.injective (@extract_flattenBlockFamily q)).eq_iff]
  simp only [parameterCone, Prod.mk.injEq, Subtype.mk.injEq]
  change (fun i j => L i * N i j * R j) = (fun i j => L' i * N' i j * R' j) ↔
    g = g' ∧ c = c' ∧ sphereOuter u z = sphereOuter v z'
  constructor
  · intro he
    have hblocks (i j : Fin q) :=
      congrFun (congrFun he i) j
    have hLL : L = L' := by
      funext i
      have hi : L i * N i o = L' i * N' i o := by grind [outerRight_anchor]
      have hscaled : L i * ((Q i o)⁻¹ • N i o) =
          L' i * ((Q i o)⁻¹ • N' i o) := by simp_all
      exact (positive_polar_unique _ _ _ _ (outerLeft_unitary g i) (outerLeft_unitary g' i) (hN.1 i) (hN'.1 i) hscaled).1
    have hRR : R = R' := by
      funext j
      have hj : N o j * R j = N' o j * R' j := by
        apply (_root_.Unitary.mul_right_inj ⟨L o,outerLeft_unitary g o⟩).mp
        simpa only [Matrix.mul_assoc, hLL] using hblocks o j
      have hscaled : ((Q o j)⁻¹ • N o j) * R j =
          ((Q o j)⁻¹ • N' o j) * R' j := by simp_all
      apply Matrix.conjTranspose_injective
      apply (positive_polar_unique _ _ _ _ (outerRight_unitary g j).conjTranspose
        (outerRight_unitary g' j).conjTranspose (hN.2 j) (hN'.2 j) ?_).1
      simpa only [N,N',R,R',Matrix.conjTranspose_mul, (hN.2 j).isHermitian.eq,
        (hN'.2 j).isHermitian.eq] using congrArg Matrix.conjTranspose hscaled
    have hNN : N = N' := by
      funext i j
      apply (_root_.Unitary.mul_left_inj ⟨R j,outerRight_unitary g j⟩).mp
      apply (_root_.Unitary.mul_right_inj ⟨L i,outerLeft_unitary g i⟩).mp
      simpa only [Matrix.mul_assoc, hLL, hRR] using hblocks i j
    refine ⟨?_,(hm.mp hNN).1,(hm.mp hNN).2⟩
    apply Prod.ext
    · funext i
      exact Subtype.ext (congrFun hLL i)
    · funext j
      apply Subtype.ext
      simpa [R,R',outerRight,j.property] using congrFun hRR j.val
  · rintro ⟨rfl,hc,hz⟩
    rw [hm.mpr ⟨hc,hz⟩]

def fullCompactCone {o : Fin q} {r : ℝ}
    (p : FullCompactParameters q o d r) : OuterFactors q o × boundedConeCoordinates d r :=
  (p.1, ⟨parameterCone p.2.val, by grind [parameterCone_image]⟩)

theorem fullCompactCone_surjective (q d : ℕ) (o : Fin q) (r : ℝ) :
    Function.Surjective (@fullCompactCone q d o r) := by
  rintro ⟨g,w⟩
  have hw : w.val ∈ parameterCone '' localParameterBox d r := by simp_all [parameterCone_image]
  obtain ⟨p,hp,he⟩ := hw
  refine ⟨(g,⟨p,hp⟩),?_⟩
  refine Prod.ext ?_ ?_
  · rfl
  · exact Subtype.ext he



end GS.UnitaryLocalModel
