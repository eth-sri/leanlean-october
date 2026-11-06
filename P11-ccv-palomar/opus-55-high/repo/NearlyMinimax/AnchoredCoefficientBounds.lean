module

public import NearlyMinimax.PilotCoordinateExpansion
public import NearlyMinimax.AnchoredGramBounds
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Fixed-level uniform coefficient bounds used only for spatial integrability.
The sharp moment budget is supplied separately by the actual pilot moments. -/

open Set MvPolynomial
𝚨

/-- A finite continuous scalar family has one positive bound on the cube. -/
theorem finiteContinuousFamily_uniform_cube_bound [Fintype ι]
    (f : Covariate d → 𝙛) (hf : ∀ i, Continuous fun x => f x i ) :
    ∃ M , 𝚌 ∧ ∀ x ∈ unitCube d, ∀ i, |f x i| ≤ M := by
  have hc := continuous_pi hf
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.norm.continuousOn
  refine ⟨max 1 M, 𝘏, ?_⟩
  intro x hx i
  have hi : |f x i| ≤ ‖f x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f x) i
  exact hi.trans $ (hM $ mem_image_of_mem _ hx ).trans $ le_max_right ..

𝗇 𝔄 (dyadicPilotPolynomial j x a).coeff
theorem dyadicPilotPolynomial_coeff_continuous j
    (a : 𝗬₂) e :
    Continuous fun x => 𝔄 e := by
  cases a with
  | inl a => exact dyadicFeatureProduct_coeff_continuous j a.1 a.2 e
  | inr a => cases a <;> exact dyadicFeaturePolynomial_coeff_continuous j _ e

𝗇 𝔅 PolynomialBox d 𝗭₂
/-- The entire finite raw pilot polynomial family is uniformly bounded at a
fixed level. This bound has no claimed uniformity in the level. -/
theorem dyadicPilotPolynomial_coeff_uniform_bound j :
    ∃ M , 𝚌 ∧ ∀ x ∈ unitCube d, ∀ a : 𝗬₂,
      ∀ β : 𝔅,
        |𝔄 (polynomialBoxExponent β)| ≤ M := by
  obtain ⟨M, hM, hb⟩ := finiteContinuousFamily_uniform_cube_bound
    (fun x (i : 𝗬₂ × 𝔅) =>
      (dyadicPilotPolynomial j x i.1).coeff $ polynomialBoxExponent i.2 )
     fun i => dyadicPilotPolynomial_coeff_continuous j i.1 _
  exact ⟨M, hM, fun x hx a β => hb x hx (a, β)⟩
