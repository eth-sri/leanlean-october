module

public import Mathlib

public import DedekindZetaZeroFree.Analysis.QuadraticForms.ClosedGradientForm
public import DedekindZetaZeroFree.Analysis.QuadraticForms.EnergyRieszResolvent
public import DedekindZetaZeroFree.Analysis.OperatorTheory.SelfAdjointOperators.RecoveryFromBoundedInverse

@[expose] public section


noncomputable section
namespace DedekindZetaZeroFree

section
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V)
include H V D
def closedGradientResolvent
      (hclosable : D.IsClosable) : H →L[ℂ] H :=
  letI : CompleteSpace (ClosedGradientSpace D) := closedGradientSpace_complete D hclosable
  energyRieszResolvent (closedGradientEmbedding D)

def closedGradientFriedrichsOperator
      (hdense : Dense (D.domain : Set H))
    (hclosable : D.IsClosable) : H →ₗ.[ℂ] H :=
  letI : CompleteSpace (ClosedGradientSpace D) := closedGradientSpace_complete D hclosable
  let hj := closedGradientEmbedding_properties D hdense hclosable
  ResolventOperator.fromBoundedInverse (closedGradientResolvent D hclosable)
    (energyRieszResolvent_properties (closedGradientEmbedding D)
      hj.2.1 hj.2.2.1 hj.1).2.2.1
end


section
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V)
include H V D
def ClosedGradientVariationalAssociation
      (T : H →ₗ.[ℂ] H) : Prop :=
  ∀ (u h : H),
    (∃ hu : u ∈ T.domain, T ⟨u, hu⟩ = h) ↔
      ∃ hu : u ∈ D.closure.domain,
        ∀ v : D.closure.domain, closedGradientForm D ⟨u, hu⟩ v = inner ℂ h (v : H)

 def graphElem
      (u : D.closure.domain) : ClosedGradientSpace D :=
  ⟨WithLp.toLp 2 ((u : H), D.closure u), by
    rw [closedGradientGraph, Submodule.mem_comap]
    simpa using LinearPMap.mem_graph D.closure u⟩
end


private lemma fromBoundedInverse_eq_of_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (hB : Function.Injective B) {u : H}
    (hu : u ∈ (ResolventOperator.fromBoundedInverse B hB).domain) {f : H} (hf : B f = u) :
    (ResolventOperator.fromBoundedInverse B hB) ⟨u, hu⟩ = f - u := by
  have heq : (⟨u, hu⟩ : (ResolventOperator.fromBoundedInverse B hB).domain) =
      ⟨B f, ⟨f, rfl⟩⟩ := Subtype.ext hf.symm
  rw [heq, ResolventOperator.fromBoundedInverse_apply, hf]

private lemma graphElem_embedding
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (u : D.closure.domain) :
    closedGradientEmbedding D (graphElem D u) = (u : H) := rfl


private lemma graphElem_inner
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (u : D.closure.domain) (z : ClosedGradientSpace D) :
    inner ℂ (graphElem D u) z =
      inner ℂ (u : H) (closedGradientEmbedding D z) +
        inner ℂ (D.closure u) (closedGradientCoordinate D z) := rfl

private lemma exists_domain_of_graph
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) (z : ClosedGradientSpace D) :
    ∃ u : D.closure.domain, (u : H) = closedGradientEmbedding D z ∧
      D.closure u = closedGradientCoordinate D z := by
  have hmem : ((WithLp.linearEquiv 2 ℂ (H × V)) z.1) ∈ D.closure.graph := z.2
  have hval : ((WithLp.linearEquiv 2 ℂ (H × V)) z.1) =
      (closedGradientEmbedding D z, closedGradientCoordinate D z) := by
    simp only [closedGradientEmbedding, closedGradientCoordinate, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, WithLp.coe_linearEquiv, WithLp.fstL_apply, WithLp.sndL_apply]
    rfl
  rw [hval, LinearPMap.mem_graph_iff] at hmem
  exact hmem

private lemma closure_eq_coordinate
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (D : H →ₗ.[ℂ] V) {z : ClosedGradientSpace D} {v : D.closure.domain}
    (hz : (v : H) = closedGradientEmbedding D z) :
    D.closure v = closedGradientCoordinate D z := by
  obtain ⟨u, hu1, hu2⟩ := exists_domain_of_graph D z
  have huv : u = v := Subtype.ext (hu1.trans hz.symm)
  rw [← huv, hu2]

theorem closedGradientFriedrichsOperator_domain_subset
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hdense : Dense (D.domain : Set H))
    (hclosable : D.IsClosable) :
    (closedGradientFriedrichsOperator D hdense hclosable).domain ≤ D.closure.domain := by
  letI  := closedGradientSpace_complete D hclosable
  have hj := closedGradientEmbedding_properties D hdense hclosable
  have hBd : (closedGradientFriedrichsOperator D hdense hclosable).domain
      = LinearMap.range (closedGradientResolvent D hclosable).toLinearMap := by
    unfold closedGradientFriedrichsOperator
    exact ResolventOperator.fromBoundedInverse_domain _ _
  intro u hu
  rw [hBd, LinearMap.mem_range] at hu
  change u ∈ (D.closure.domain : Set H)
  rw [← hj.2.2.2, Set.mem_range]
  obtain ⟨f, hf⟩ := hu
  exact ⟨(closedGradientEmbedding D).adjoint f, by
    rw [← hf]
    simp only [closedGradientResolvent, energyRieszResolvent]
    rfl⟩

theorem closedGradientFriedrichsOperator_variational
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hdense : Dense (D.domain : Set H))
    (hclosable : D.IsClosable) (u : D.closure.domain) (h : H) :
    (∃ hu : (u : H) ∈ (closedGradientFriedrichsOperator D hdense hclosable).domain,
      closedGradientFriedrichsOperator D hdense hclosable ⟨(u : H), hu⟩ = h) ↔
    ∀ v : D.closure.domain, inner ℂ (D.closure u) (D.closure v) = inner ℂ h (v : H) := by
  letI  := closedGradientSpace_complete D hclosable
  let B := closedGradientResolvent D hclosable
  let hB : Function.Injective B :=
    (energyRieszResolvent_properties (closedGradientEmbedding D)
      (closedGradientEmbedding_properties D hdense hclosable).2.1
      (closedGradientEmbedding_properties D hdense hclosable).2.2.1
      (closedGradientEmbedding_properties D hdense hclosable).1).2.2.1
  
  have hj := closedGradientEmbedding_properties D hdense hclosable
  have hL : (∃ hu : (u : H) ∈ (closedGradientFriedrichsOperator D hdense hclosable).domain,
      closedGradientFriedrichsOperator D hdense hclosable ⟨(u : H), hu⟩ = h) ↔ B ((u : H) + h) = u := by
    constructor
    · rintro ⟨hu, hval⟩
      have huB : (u : H) ∈ (ResolventOperator.fromBoundedInverse B hB).domain := hu
      rw [ResolventOperator.fromBoundedInverse_domain, LinearMap.mem_range] at huB
      obtain ⟨f, hf⟩ := huB
      have hfeq  :=
        fromBoundedInverse_eq_of_eq B hB hu hf
      have hval' : (ResolventOperator.fromBoundedInverse B hB) ⟨(u : H), hu⟩ = h := hval
      have hfu : f = (u : H) + h := by
        have h1 : f - u = h := by rw [← hfeq]; exact hval'
        have h2 : f = h + u := sub_eq_iff_eq_add.mp h1
        rw [h2, add_comm]
      have h1 : B ((u : H) + h) = ↑u := by
        rw [hfu] at hf
        exact hf
      exact h1
    · intro hBuh
      have huB : (u : H) ∈ (ResolventOperator.fromBoundedInverse B hB).domain := by
        rw [ResolventOperator.fromBoundedInverse_domain, LinearMap.mem_range]
        exact ⟨(u : H) + h, hBuh⟩
      refine ⟨huB, ?_⟩
      have hfeq  :=
        fromBoundedInverse_eq_of_eq B hB huB hBuh
      change (ResolventOperator.fromBoundedInverse B hB) ⟨(u : H), huB⟩ = h
      rw [hfeq]
      abel
  have hR : (∀ v : D.closure.domain, inner ℂ (D.closure u) (D.closure v) = inner ℂ h (v : H)) ↔
      B ((u : H) + h) = u := by
    constructor
    · intro hRHS
      let wu := graphElem D u
      have hinner : ∀ z : ClosedGradientSpace D,
          inner ℂ wu z = inner ℂ ((u : H) + h) (closedGradientEmbedding D z) := by
        intro z
        rw [graphElem_inner D u z, inner_add_left]
        congr 1
        obtain ⟨v, hv1, hv2⟩ := exists_domain_of_graph D z
        rw [← hv2, ← hv1]
        exact hRHS v
      have huniq := (energyRieszResolvent_variational (closedGradientEmbedding D) ((u : H) + h)).2.1 wu hinner
      have h2 : closedGradientEmbedding D ((closedGradientEmbedding D).adjoint ((u : H) + h)) =
          closedGradientEmbedding D wu := by rw [huniq]
      have h3 : closedGradientEmbedding D ((closedGradientEmbedding D).adjoint ((u : H) + h)) =
          B ((u : H) + h) := rfl
      rw [h3] at h2
      rw [h2, graphElem_embedding D u]
    · intro hBuh v
      let wu := graphElem D u
      have hjstar : (closedGradientEmbedding D).adjoint ((u : H) + h) = wu := by
        apply hj.2.1
        have h3 : closedGradientEmbedding D ((closedGradientEmbedding D).adjoint ((u : H) + h)) =
            B ((u : H) + h) := rfl
        rw [h3, hBuh, graphElem_embedding D u]
      obtain ⟨z, hz⟩ : ∃ z, closedGradientEmbedding D z = (v : H) := by
        have : (v : H) ∈ Set.range (closedGradientEmbedding D) := by
          rw [hj.2.2.2]; exact v.property
        simpa using this
      have hkz : D.closure v = closedGradientCoordinate D z := closure_eq_coordinate D hz.symm
      have hRiesz := (energyRieszResolvent_variational (closedGradientEmbedding D) ((u : H) + h)).1 z
      rw [hjstar] at hRiesz
      rw [graphElem_inner D u z, inner_add_left] at hRiesz
      have hcancel : inner ℂ (D.closure u) (closedGradientCoordinate D z) = inner ℂ h (closedGradientEmbedding D z) :=
        (add_left_cancel_iff).mp hRiesz
      rw [hkz, ← hz]
      exact hcancel
  rw [hL, hR]

theorem closedGradientFriedrichsOperator_riesz_estimate
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (hdense : Dense (D.domain : Set H))
    (hclosable : D.IsClosable) (f : H) :
    letI : CompleteSpace (ClosedGradientSpace D) := closedGradientSpace_complete D hclosable
    ‖(closedGradientEmbedding D).adjoint f‖ ≤ ‖f‖ := by
  letI  := closedGradientSpace_complete D hclosable
  have hj := closedGradientEmbedding_properties D hdense hclosable
  have hnorm : ‖(closedGradientEmbedding D).adjoint‖ = ‖closedGradientEmbedding D‖ :=
    LinearIsometryEquiv.norm_map (ContinuousLinearMap.adjoint (𝕜 := ℂ)
      (E := ClosedGradientSpace D) (F := H)) (closedGradientEmbedding D)
  calc ‖(closedGradientEmbedding D).adjoint f‖
      ≤ ‖(closedGradientEmbedding D).adjoint‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖closedGradientEmbedding D‖ * ‖f‖ := by rw [hnorm]
    _ ≤ 1 * ‖f‖ := by gcongr; exact hj.1
    _ = ‖f‖ := one_mul _

end DedekindZetaZeroFree

end
