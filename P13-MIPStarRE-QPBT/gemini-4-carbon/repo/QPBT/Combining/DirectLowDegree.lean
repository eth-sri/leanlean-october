module

public import QPBT.Combining.DirectLowDegreeCore
public import QPBT.Combining.Defs
public import QPBT.Games.Sandwich.Support
public import QPBT.Games.Sandwich.Pasting.Assembly
public import QPBT.Games.Sandwich.Pasting.SchmidtMirror
public import QPBT.Games.DistanceTheorems.Calculus
public import QPBT.Games.MeasurementCompression
public import QPBT.Games.ErrorFunctions
public import MIPStarRE.LDT.Preliminaries.Polynomials
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore

/-! # Consolidated simultaneity reduction, direct low-degree soundness, and coefficient collision -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum DistanceCalculus SandwichProduct

noncomputable section

/-! ## Section 1: Polynomial combining, coefficients, exact linearity, and recovery bounds -/

def combinedPointVar (m k : ℕ) (j : Fin m) : Fin (m + k) := finSumFinEquiv (Sum.inl j)
def combinedCoefficientVar (m k : ℕ) (r : Fin k) : Fin (m + k) := finSumFinEquiv (Sum.inr r)

theorem combinedPointVar_injective (m k : ℕ) : Function.Injective (combinedPointVar m k) :=
  fun _ _ h => by simpa using finSumFinEquiv.injective h

theorem combinedCoefficientVar_injective (m k : ℕ) : Function.Injective (combinedCoefficientVar m k) :=
  fun _ _ h => by simpa using finSumFinEquiv.injective h

theorem combinedCoefficientVar_ne_combinedPointVar (m k : ℕ) (r : Fin k) (j : Fin m) :
    combinedCoefficientVar m k r ≠ combinedPointVar m k j := fun h => by
  simpa using finSumFinEquiv.injective h

theorem combinedVar_cases {m k : ℕ} (i : Fin (m + k)) :
    (∃ j : Fin m, i = combinedPointVar m k j) ∨ ∃ r : Fin k, i = combinedCoefficientVar m k r := by
  rcases h : finSumFinEquiv.symm i with j | r
  · exact Or.inl ⟨j, by rw [combinedPointVar, ← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨r, by rw [combinedCoefficientVar, ← h, Equiv.apply_symm_apply]⟩

@[simp] theorem combinedPointVar_val (m k : ℕ) (j : Fin m) : (combinedPointVar m k j).val = j.val := by
  simp [combinedPointVar]

@[simp] theorem combinedCoefficientVar_val (m k : ℕ) (r : Fin k) :
    (combinedCoefficientVar m k r).val = m + r.val := by simp [combinedCoefficientVar]

def combinedPointPart {K : Type*} {m k : ℕ} (z : Fin (m + k) → K) : Fin m → K :=
  fun j => z (combinedPointVar m k j)

def combinedCoefficientPart {K : Type*} {m k : ℕ} (z : Fin (m + k) → K) : Fin k → K :=
  fun r => z (combinedCoefficientVar m k r)

def combinedPoint {K : Type*} {m k : ℕ} (u : Fin m → K) (α : Fin k → K) : Fin (m + k) → K :=
  fun i => Sum.elim u α (finSumFinEquiv.symm i)

@[simp] theorem combinedPointPart_combinedPoint {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) : combinedPointPart (combinedPoint u α) = u := by
  funext j; simp [combinedPointPart, combinedPoint, combinedPointVar]

@[simp] theorem combinedCoefficientPart_combinedPoint {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) : combinedCoefficientPart (combinedPoint u α) = α := by
  funext r; simp [combinedCoefficientPart, combinedPoint, combinedCoefficientVar]

@[simp] theorem combinedPoint_combinedPointVar {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (j : Fin m) :
    combinedPoint u α (combinedPointVar m k j) = u j := by simp [combinedPoint, combinedPointVar]

@[simp] theorem combinedPoint_combinedCoefficientVar {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (r : Fin k) :
    combinedPoint u α (combinedCoefficientVar m k r) = α r := by
  simp [combinedPoint, combinedCoefficientVar]

@[simp] theorem combinedPoint_combinedPointPart_combinedCoefficientPart {K : Type*} {m k : ℕ}
    (z : Fin (m + k) → K) :
    combinedPoint (combinedPointPart z) (combinedCoefficientPart z) = z := by
  funext i; rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;> simp [combinedPointPart, combinedCoefficientPart]

def combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) : MvPolynomial (Fin (m + k)) K :=
  ∑ r : Fin k, MvPolynomial.X (combinedCoefficientVar m k r) *
    MvPolynomial.rename (combinedPointVar m k) (g r)

theorem combinePolyTuple_eval_combinedPoint {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (u : Fin m → K) (α : Fin k → K) :
    MvPolynomial.eval (combinedPoint u α) (combinePolyTuple g) =
      ∑ r : Fin k, α r * MvPolynomial.eval u (g r) := by
  simp only [combinePolyTuple, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_rename,
    combinedPoint_combinedCoefficientVar]
  exact Finset.sum_congr rfl fun r _ => congrArg (α r * MvPolynomial.eval · (g r))
    (combinedPointPart_combinedPoint u α)

theorem mem_polyFunc_of_degreeOf_le {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (h : ∀ i, p.degreeOf i ≤ d) : p ∈ polyFunc m K d := by
  rw [MvPolynomial.mem_restrictDegree]
  exact fun s hs i => MvPolynomial.degreeOf_le_iff.mp (h i) s hs

theorem combinePolyTuple_mem_polyFunc {K : Type*} [CommSemiring K] {m k d : ℕ}
    (hd : 1 ≤ d) (g : Fin k → MvPolynomial (Fin m) K) (hg : ∀ r, g r ∈ polyFunc m K d) :
    combinePolyTuple g ∈ polyFunc (m + k) K d := by
  classical
  refine Submodule.sum_mem _ fun r _ => mem_polyFunc_of_degreeOf_le fun i => ?_
  refine (MvPolynomial.degreeOf_mul_le i _ _).trans ?_
  rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r', rfl⟩
  · rw [MvPolynomial.degreeOf_X_of_ne (combinedCoefficientVar_ne_combinedPointVar m k r j).symm, zero_add]
    rw [MvPolynomial.degreeOf_le_iff]; intro s hs
    rw [MvPolynomial.support_rename_of_injective (combinedPointVar_injective m k)] at hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rw [Finsupp.mapDomain_apply_of_injective (combinedPointVar_injective m k)]
    exact (MvPolynomial.le_degreeOf_of_mem_support j ht).trans (degreeOf_le_of_mem_polyFunc (hg r) j)
  · have h0 : (MvPolynomial.rename (combinedPointVar m k) (g r)).degreeOf (combinedCoefficientVar m k r') = 0 := by
      rw [← Nat.le_zero, MvPolynomial.degreeOf_le_iff]; intro s hs
      rw [MvPolynomial.support_rename_of_injective (combinedPointVar_injective m k)] at hs
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
      exact le_of_eq (Finsupp.mapDomain_of_notMem_range t _ fun ⟨j, hj⟩ =>
        combinedCoefficientVar_ne_combinedPointVar m k r' j hj.symm)
    have hX : (MvPolynomial.X (combinedCoefficientVar m k r) : MvPolynomial _ K).degreeOf
        (combinedCoefficientVar m k r') ≤ 1 := by
      rw [MvPolynomial.degreeOf_le_iff]; intro s hs
      have hs' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)
      subst hs'; by_cases h : combinedCoefficientVar m k r = combinedCoefficientVar m k r' <;> simp [h]
    rw [h0, add_zero]; exact hX.trans hd

def combinedPointExp {m k : ℕ} (s : Fin (m + k) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.comapDomain (combinedPointVar m k) s (combinedPointVar_injective m k).injOn

def combinedCoefExp {m k : ℕ} (s : Fin (m + k) →₀ ℕ) : Fin k →₀ ℕ :=
  Finsupp.comapDomain (combinedCoefficientVar m k) s (combinedCoefficientVar_injective m k).injOn

def combinedCoefSubstitution (K : Type*) [CommSemiring K] (m k : ℕ) :
    Fin (m + k) → MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  fun i => Sum.elim (fun j : Fin m => MvPolynomial.C (MvPolynomial.X j))
    (fun r : Fin k => MvPolynomial.X r) (finSumFinEquiv.symm i)

def combinedCoefAlgHom (K : Type*) [CommSemiring K] (m k : ℕ) :
    MvPolynomial (Fin (m + k)) K →ₐ[K] MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  MvPolynomial.aeval (combinedCoefSubstitution K m k)

theorem combinedCoefAlgHom_monomial {K : Type*} [CommSemiring K] {m k : ℕ}
    (s : Fin (m + k) →₀ ℕ) (a : K) :
    combinedCoefAlgHom K m k (MvPolynomial.monomial s a) =
      MvPolynomial.monomial (combinedCoefExp s) (MvPolynomial.monomial (combinedPointExp s) a) := by
  classical
  set A := MvPolynomial (Fin k) (MvPolynomial (Fin m) K)
  have hsp (f : Fin (m + k) → A) :
      ∏ i, f i = (∏ j, f (combinedPointVar m k j)) * ∏ r, f (combinedCoefficientVar m k r) := by
    rw [← Fintype.prod_equiv finSumFinEquiv (fun x => f (finSumFinEquiv x)) f fun _ => rfl,
      Fintype.prod_sum_type]; rfl
  have hC : combinedCoefAlgHom K m k (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := by
    rw [combinedCoefAlgHom, MvPolynomial.aeval_C]; simp [MvPolynomial.algebraMap_eq]
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_mul, map_prod, hC,
    MvPolynomial.monomial_eq (s := combinedCoefExp s), Finsupp.prod_fintype _ _ fun _ => pow_zero _,
    MvPolynomial.monomial_eq (s := combinedPointExp s), Finsupp.prod_fintype _ _ fun _ => pow_zero _,
    map_mul, map_prod]
  simp only [combinedCoefAlgHom, MvPolynomial.aeval_X, map_pow]
  rw [hsp (fun i => combinedCoefSubstitution K m k i ^ s i)]
  simp only [combinedCoefSubstitution, combinedPointVar, combinedCoefficientVar, Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr, combinedPointExp, combinedCoefExp, Finsupp.comapDomain_apply]
  ring

theorem combinedCoefAlgHom_injective {K : Type*} [CommSemiring K] {m k : ℕ} :
    Function.Injective (combinedCoefAlgHom K m k) := by
  let inv : MvPolynomial (Fin k) (MvPolynomial (Fin m) K) →+* MvPolynomial (Fin (m + k)) K :=
    MvPolynomial.eval₂Hom (MvPolynomial.rename (combinedPointVar m k)).toRingHom
      (fun r => MvPolynomial.X (combinedCoefficientVar m k r))
  refine Function.LeftInverse.injective (g := inv) fun p => ?_
  have h : inv.comp (combinedCoefAlgHom K m k).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [inv, combinedCoefAlgHom, MvPolynomial.algebraMap_eq]
    · intro i; rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;>
        simp [inv, combinedCoefAlgHom, combinedCoefSubstitution, combinedPointVar, combinedCoefficientVar]
  exact RingHom.congr_fun h p

def combinedCoef {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) : MvPolynomial (Fin m) K :=
  (combinedCoefAlgHom K m k p).coeff μ

def combinedRestrict {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) : MvPolynomial (Fin k) K :=
  MvPolynomial.aeval (fun i => Sum.elim (fun j => MvPolynomial.C (u j)) MvPolynomial.X
    (finSumFinEquiv.symm i)) p

theorem eval_combinedRestrict {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) (α : Fin k → K) :
    MvPolynomial.eval α (combinedRestrict p u) = MvPolynomial.eval (combinedPoint u α) p := by
  have h : (MvPolynomial.aeval (R := K) α).comp
      (MvPolynomial.aeval (fun i => Sum.elim (fun j => MvPolynomial.C (u j)) MvPolynomial.X
        (finSumFinEquiv.symm i))) = MvPolynomial.aeval (combinedPoint u α) := by
    apply MvPolynomial.algHom_ext; intro i
    rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;>
      simp [combinedPoint, combinedPointVar, combinedCoefficientVar]
  exact AlgHom.congr_fun h p

theorem eval_combinedCoef {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) (μ : Fin k →₀ ℕ) :
    MvPolynomial.eval u (combinedCoef p μ) = (combinedRestrict p u).coeff μ := by
  have h : (MvPolynomial.mapAlgHom (MvPolynomial.aeval u)).comp (combinedCoefAlgHom K m k) =
      MvPolynomial.aeval (fun i => Sum.elim (fun j => MvPolynomial.C (u j)) MvPolynomial.X
        (finSumFinEquiv.symm i)) := by
    apply MvPolynomial.algHom_ext; intro i
    rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;>
      simp [combinedCoefAlgHom, combinedCoefSubstitution, combinedPointVar, combinedCoefficientVar]
  have hp := AlgHom.congr_fun h p
  simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.mapAlgHom_apply] at hp
  rw [combinedRestrict, ← hp, combinedCoef, MvPolynomial.coeff_map]; rfl

theorem eq_sum_monomial_single {B : Type*} [CommSemiring B] {k : ℕ} (q : MvPolynomial (Fin k) B)
    (h : ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) → q.coeff μ = 0) :
    q = ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (q.coeff (Finsupp.single r 1)) := by
  classical
  have hsub : q.support ⊆ Finset.univ.image fun r : Fin k => Finsupp.single r 1 := fun μ hμ => by
    by_contra hc
    exact MvPolynomial.mem_support_iff.mp hμ (h μ fun r hr => hc (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr.symm⟩))
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_subset hsub (fun μ _ hμ => by rw [MvPolynomial.notMem_support_iff.mp hμ, map_zero]),
    Finset.sum_image fun _ _ _ _ h' => Finsupp.single_left_injective one_ne_zero h']

theorem combinedCoefAlgHom_combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) :
    combinedCoefAlgHom K m k (combinePolyTuple g) =
      ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (g r) := by
  have hren (h : MvPolynomial (Fin m) K) :
      combinedCoefAlgHom K m k (MvPolynomial.rename (combinedPointVar m k) h) = MvPolynomial.C h := by
    induction h using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.rename_C, combinedCoefAlgHom, MvPolynomial.aeval_C]; simp [MvPolynomial.algebraMap_eq]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp =>
        rw [map_mul, map_mul, hp, MvPolynomial.rename_X]
        simp [combinedCoefAlgHom, combinedCoefSubstitution, combinedPointVar]
  rw [combinePolyTuple, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, hren, mul_comm, ← MvPolynomial.C_mul_X_eq_monomial]
  simp [combinedCoefAlgHom, combinedCoefSubstitution, combinedCoefficientVar]

theorem combinedCoef_combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (r : Fin k) :
    combinedCoef (combinePolyTuple g) (Finsupp.single r 1) = g r := by
  classical
  rw [combinedCoef, combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum, Finset.sum_eq_single r]
  · simp
  · intro s _ hs; rw [MvPolynomial.coeff_monomial, if_neg fun h => hs (Finsupp.single_left_injective one_ne_zero h)]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem combinePolyTuple_injective {K : Type*} [CommSemiring K] {m k : ℕ} :
    Function.Injective (combinePolyTuple (K := K) (m := m) (k := k)) := fun g g' h =>
  funext fun r => by rw [← combinedCoef_combinePolyTuple g r, h, combinedCoef_combinePolyTuple]

theorem combinePolyTuple_combinedCoef_iff {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) :
    (∃ g : Fin k → MvPolynomial (Fin m) K, p = combinePolyTuple g) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) → combinedCoef p μ = 0 := by
  classical
  constructor
  · rintro ⟨g, rfl⟩ μ hμ
    rw [combinedCoef, combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum]
    exact Finset.sum_eq_zero fun r _ => by rw [MvPolynomial.coeff_monomial, if_neg fun h => hμ r h.symm]
  · intro h
    refine ⟨fun r => combinedCoef p (Finsupp.single r 1), combinedCoefAlgHom_injective ?_⟩
    rw [combinedCoefAlgHom_combinePolyTuple]; exact eq_sum_monomial_single _ h

theorem combinedCoef_eq_sum {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) :
    combinedCoef p μ = ∑ s ∈ p.support,
      if combinedCoefExp s = μ then MvPolynomial.monomial (combinedPointExp s) (p.coeff s) else 0 := by
  classical
  rw [combinedCoef]; conv_lhs => rw [p.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [combinedCoefAlgHom_monomial, MvPolynomial.coeff_monomial]

theorem degreeOf_combinedCoef_le {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : ∀ i, p.degreeOf i ≤ d)
    (μ : Fin k →₀ ℕ) (j : Fin m) : (combinedCoef p μ).degreeOf j ≤ d := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]; intro ν hν
  rw [combinedCoef_eq_sum] at hν
  obtain ⟨s, hs, hνs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hν)
  by_cases hc : combinedCoefExp s = μ
  · rw [if_pos hc] at hνs
    have hνeq : ν = combinedPointExp s := by simpa using MvPolynomial.support_monomial_subset hνs
    subst hνeq; exact MvPolynomial.degreeOf_le_iff.mp (hp (combinedPointVar m k j)) s hs
  · rw [if_neg hc] at hνs; simp at hνs

@[reducible] def DirectLdParams.combined (D : DirectLdParams) : DirectLdParams where
  q := D.q
  m := D.m + D.k
  d := D.d
  k := 1
  hm := D.hm.trans (Nat.le_add_right D.m D.k)
  hd := D.hd
  hk := le_rfl
  hq := D.hq

theorem card_directScalarQ (D : DirectLdParams) : Fintype.card (DirectScalarQ D) = D.q := by
  rw [Fintype.card_congr (binaryRepresentation D.model), Fintype.card_fin]

instance instUniqueFinKCombined (D : DirectLdParams) : Unique (Fin D.combined.k) :=
  show Unique (Fin 1) from inferInstance

def directCombinedPolynomial (D : DirectLdParams) (g : DirectPolyTuple D) :
    PolyIndex D.combined.m (DirectScalarQ D) D.d :=
  ⟨combinePolyTuple fun r => (g r).1, combinePolyTuple_mem_polyFunc D.hd _ fun r => (g r).2⟩

def IsDirectCombined (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) : Prop :=
  ∃ g : DirectPolyTuple D, directCombinedPolynomial D g = p

def directTupleOfCombined (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) : DirectPolyTuple D := by
  classical exact if h : IsDirectCombined D p then h.choose else fun _ => 0

@[simp] theorem directTupleOfCombined_directCombinedPolynomial (D : DirectLdParams)
    (g : DirectPolyTuple D) : directTupleOfCombined D (directCombinedPolynomial D g) = g := by
  classical
  have hex : IsDirectCombined D (directCombinedPolynomial D g) := ⟨g, rfl⟩
  rw [directTupleOfCombined, dif_pos hex]
  have hcomp := combinePolyTuple_injective (congrArg Subtype.val hex.choose_spec)
  exact funext fun r => Subtype.ext (congrFun hcomp r)

def directTupleOfCombinedTuple (D : DirectLdParams)
    (p : DirectPolyTuple D.combined) : DirectPolyTuple D :=
  directTupleOfCombined D (p default)

def combiningLinearForm {K : Type*} [CommSemiring K] {k : ℕ} (c : Fin k → K) :
    MvPolynomial (Fin k) K :=
  ∑ r : Fin k, MvPolynomial.C (c r) * MvPolynomial.X r

@[simp] theorem combiningLinearForm_eval {K : Type*} [CommSemiring K] {k : ℕ}
    (c α : Fin k → K) : MvPolynomial.eval α (combiningLinearForm c) = ∑ r, c r * α r := by
  simp [combiningLinearForm]

theorem combiningLinearForm_totalDegree_le_one {K : Type*} [CommSemiring K] [Nontrivial K]
    {k : ℕ} (c : Fin k → K) : (combiningLinearForm c).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_finsetSum _ _).trans <| Finset.sup_le fun r _ =>
    (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])

theorem combiningLinearForm_injective {K : Type*} [CommSemiring K] {k : ℕ} :
    Function.Injective (combiningLinearForm (K := K) (k := k)) := by
  classical
  have hcf (c : Fin k → K) (r : Fin k) : (combiningLinearForm c).coeff (Finsupp.single r 1) = c r := by
    rw [combiningLinearForm, MvPolynomial.coeff_sum, Finset.sum_eq_single r]
    · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    · intro s _ hs; rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
        if_neg fun h => hs (Finsupp.single_left_injective one_ne_zero h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact fun c c' h => funext fun r => by rw [← hcf c r, h, hcf]

theorem polynomialAgreement_avg_eq_agreementProbability {m : ℕ} {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] (g h : MvPolynomial (Fin m) K) :
    avgOver (uniformDistribution (Fin m → K))
        (fun u => if MvPolynomial.eval u g = MvPolynomial.eval u h then (1 : Error) else 0) =
      (polynomialAgreementProbability m K g h : Error) := by
  classical
  simp only [avgOver, uniformDistribution, Distribution.uniformOnFinset_support,
    Distribution.uniformOnFinset_weight, Finset.mem_univ, ↓reduceIte, Finset.card_univ,
    Fintype.card_pi, Finset.prod_const, Finset.card_fin, mul_ite, mul_one, mul_zero,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, polynomialAgreementProbability]
  push_cast; simp [div_eq_mul_inv, mul_comm]

theorem exists_eq_combiningLinearForm_iff {K : Type*} [CommSemiring K] {k : ℕ}
    (P : MvPolynomial (Fin k) K) :
    (∃ c : Fin k → K, P = combiningLinearForm c) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) → P.coeff μ = 0 := by
  classical
  have hmon (c : Fin k → K) : combiningLinearForm c = ∑ r, MvPolynomial.monomial (Finsupp.single r 1) (c r) :=
    Finset.sum_congr rfl fun _ _ => MvPolynomial.C_mul_X_eq_monomial
  constructor
  · rintro ⟨c, rfl⟩ μ hμ
    rw [hmon, MvPolynomial.coeff_sum]
    exact Finset.sum_eq_zero fun r _ => by rw [MvPolynomial.coeff_monomial, if_neg fun e => hμ r e.symm]
  · intro h
    refine ⟨fun r => P.coeff (Finsupp.single r 1), ?_⟩
    rw [hmon]; exact eq_sum_monomial_single P h

open scoped Classical in
def directCombinedRecoveryLocalBound (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) (u : Fin D.m → DirectScalarQ D) : Error :=
  if IsDirectCombined D p then (1 : Error) / D.q
  else (if ∃ c : Fin D.k → DirectScalarQ D, combinedRestrict p.1 u = combiningLinearForm c
      then (1 : Error) else 0) + ((D.k * D.d : ℕ) : Error) / D.q

open scoped Classical in
theorem directCombinedRecoveryEvent_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d)
    (u : Fin D.m → DirectScalarQ D) (b : Fin D.k → DirectScalarQ D) :
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D)) (fun α =>
        if evalDirectPolyTupleAt u (directTupleOfCombined D p) ≠ b ∧
            MvPolynomial.eval (combinedPoint u α) p.1 = ∑ r : Fin D.k, α r * b r
          then (1 : Error) else 0) ≤
      directCombinedRecoveryLocalBound D p u := by
  have hq : (0 : ℝ) < D.q := by
    have : 0 < Fintype.card (DirectScalarQ D) := Fintype.card_pos
    rw [card_directScalarQ] at this; exact_mod_cast this
  have hsc (c α : Fin D.k → DirectScalarQ D) : ∑ r, α r * c r = ∑ r, c r * α r :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [directCombinedRecoveryLocalBound]
  by_cases hc : IsDirectCombined D p
  · rw [if_pos hc]; obtain ⟨g, rfl⟩ := hc
    rw [directTupleOfCombined_directCombinedPolynomial]
    by_cases hub : evalDirectPolyTupleAt u g = b
    · rw [avgOver_congr _ _ (fun _ => 0) fun α => if_neg fun ⟨hne, _⟩ => hne hub, avgOver_zero]
      positivity
    · refine (avgOver_mono _ _ (fun α => if MvPolynomial.eval α (combiningLinearForm (evalDirectPolyTupleAt u g)) =
          MvPolynomial.eval α (combiningLinearForm b) then (1 : Error) else 0) fun α => ?_).trans ?_
      · simp only [combiningLinearForm_eval, ← hsc _ α]
        by_cases hev : evalDirectPolyTupleAt u g ≠ b ∧
            MvPolynomial.eval (combinedPoint u α) (directCombinedPolynomial D g).1 = ∑ r, α r * b r
        · have h2 := hev.2
          rw [directCombinedPolynomial, combinePolyTuple_eval_combinedPoint] at h2
          change ∑ r, α r * evalDirectPolyTupleAt u g r = ∑ r, α r * b r at h2
          rw [if_pos hev, if_pos h2]
        · rw [if_neg hev]; split_ifs <;> norm_num
      · rw [polynomialAgreement_avg_eq_agreementProbability]
        have hsz := schwartzZippel_totalDegree (d := 1) (fun h => hub (combiningLinearForm_injective h))
          (combiningLinearForm_totalDegree_le_one _) (combiningLinearForm_totalDegree_le_one _)
        have hszR : (polynomialAgreementProbability D.k (DirectScalarQ D)
            (combiningLinearForm (evalDirectPolyTupleAt u g)) (combiningLinearForm b) : Error) ≤
            ((((1 : ℕ) : ℚ≥0) / Fintype.card (DirectScalarQ D) : ℚ≥0) : Error) := by exact_mod_cast hsz
        exact hszR.trans_eq (by rw [card_directScalarQ]; push_cast; ring)
  · rw [if_neg hc]
    by_cases hu : ∃ c : Fin D.k → DirectScalarQ D, combinedRestrict p.1 u = combiningLinearForm c
    · rw [if_pos hu]
      refine (avgOver_mono _ _ (fun _ => (1 : Error)) fun _ => by split_ifs <;> norm_num).trans ?_
      rw [avgOver_uniform_const]; have : (0 : ℝ) ≤ ((D.k * D.d : ℕ) : ℝ) / D.q := by positivity
      linarith
    · rw [if_neg hu, zero_add]; push Not at hu
      have hkd : 1 ≤ D.k * D.d := Nat.mul_pos D.hk D.hd
      have hdeg : (combinedRestrict p.1 u).totalDegree ≤ D.k * D.d := by
        refine totalDegree_le_mul_of_degreeOf_le fun r => ?_
        rw [MvPolynomial.degreeOf_le_iff]; intro μ hμ
        have hne : combinedCoef p.1 μ ≠ 0 := fun h0 => MvPolynomial.mem_support_iff.mp hμ
          (by rw [← eval_combinedCoef, h0, map_zero])
        have hex : ∃ s ∈ p.1.support, combinedCoefExp s = μ := by
          by_contra hcon; push Not at hcon
          exact hne ((combinedCoef_eq_sum p.1 μ).trans (Finset.sum_eq_zero fun s hs => if_neg (hcon s hs)))
        obtain ⟨s, hs, rfl⟩ := hex
        exact MvPolynomial.degreeOf_le_iff.mp (degreeOf_le_of_mem_polyFunc p.2 (combinedCoefficientVar D.m D.k r)) s hs
      refine (avgOver_mono _ _ (fun α => if MvPolynomial.eval α (combinedRestrict p.1 u) =
          MvPolynomial.eval α (combiningLinearForm b) then (1 : Error) else 0) fun α => ?_).trans ?_
      · rw [eval_combinedRestrict, combiningLinearForm_eval, ← hsc b α]
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd h1.2 h2
        · norm_num
        · exact le_rfl
      · rw [polynomialAgreement_avg_eq_agreementProbability]
        have hsz := schwartzZippel_totalDegree (hu b) hdeg
          ((combiningLinearForm_totalDegree_le_one b).trans hkd)
        have hszR : (polynomialAgreementProbability D.k (DirectScalarQ D)
            (combinedRestrict p.1 u) (combiningLinearForm b) : Error) ≤
            ((((D.k * D.d : ℕ) : ℚ≥0) / Fintype.card (DirectScalarQ D) : ℚ≥0) : Error) := by exact_mod_cast hsz
        exact hszR.trans_eq (by rw [card_directScalarQ]; push_cast; ring)

open scoped Classical in
theorem directCombinedRecoveryLocalBound_avg_le (D : DirectLdParams)
    (p : PolyIndex D.combined.m (DirectScalarQ D) D.d) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (directCombinedRecoveryLocalBound D p) ≤
      ((D.combined.m * D.d : ℕ) : Error) / D.q := by
  have hq : (0 : ℝ) < D.q := by
    have : 0 < Fintype.card (DirectScalarQ D) := Fintype.card_pos
    rw [card_directScalarQ] at this; exact_mod_cast this
  by_cases hc : IsDirectCombined D p
  · rw [avgOver_congr _ _ (fun _ => (1 : Error) / D.q) fun u => by rw [directCombinedRecoveryLocalBound, if_pos hc],
      avgOver_uniform_const]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast (Nat.mul_pos D.combined.hm D.combined.hd : 1 ≤ D.combined.m * D.d)) hq.le
  · have hnc : ∀ g : Fin D.k → MvPolynomial (Fin D.m) (DirectScalarQ D), p.1 ≠ combinePolyTuple g :=
      fun g hg => hc ⟨fun r => ⟨g r, by
        have h := mem_polyFunc_of_degreeOf_le (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc p.2) (Finsupp.single r 1))
        rwa [hg, combinedCoef_combinePolyTuple] at h⟩, Subtype.ext hg.symm⟩
    obtain ⟨μ, hμ, hne⟩ : ∃ μ, (∀ r, μ ≠ Finsupp.single r 1) ∧ combinedCoef p.1 μ ≠ 0 := by
      by_contra hcon; push Not at hcon
      obtain ⟨g, hg⟩ := (combinePolyTuple_combinedCoef_iff p.1).mpr hcon
      exact hnc g hg
    have hlin : avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => if ∃ c, combinedRestrict p.1 u = combiningLinearForm c then (1 : Error) else 0) ≤
        ((D.m * D.d : ℕ) : Error) / D.q := by
      refine (avgOver_mono _ _ (fun u => if MvPolynomial.eval u (combinedCoef p.1 μ) =
          MvPolynomial.eval u (0 : MvPolynomial (Fin D.m) (DirectScalarQ D)) then (1 : Error) else 0) fun u => ?_).trans ?_
      · by_cases hu : ∃ c, combinedRestrict p.1 u = combiningLinearForm c
        · have h0 : MvPolynomial.eval u (combinedCoef p.1 μ) = 0 := by
            rw [eval_combinedCoef]; exact (exists_eq_combiningLinearForm_iff _).mp hu μ hμ
          rw [if_pos hu, map_zero, if_pos h0]
        · rw [if_neg hu]; split_ifs <;> norm_num
      · rw [polynomialAgreement_avg_eq_agreementProbability]
        have hdeg : (combinedCoef p.1 μ).totalDegree ≤ D.m * D.d :=
          totalDegree_le_mul_of_degreeOf_le (degreeOf_combinedCoef_le (degreeOf_le_of_mem_polyFunc p.2) μ)
        have hsz := schwartzZippel_totalDegree hne hdeg (by simp)
        have hszR : (polynomialAgreementProbability D.m (DirectScalarQ D)
            (combinedCoef p.1 μ) 0 : Error) ≤
            ((((D.m * D.d : ℕ) : ℚ≥0) / Fintype.card (DirectScalarQ D) : ℚ≥0) : Error) := by exact_mod_cast hsz
        exact hszR.trans_eq (by rw [card_directScalarQ]; push_cast; ring)
    have heq (u) : directCombinedRecoveryLocalBound D p u =
        (if ∃ c, combinedRestrict p.1 u = combiningLinearForm c then (1 : Error) else 0) +
        ((D.k * D.d : ℕ) : Error) / D.q := by rw [directCombinedRecoveryLocalBound, if_neg hc]
    have hsp : ((D.combined.m * D.d : ℕ) : Error) / D.q =
        ((D.m * D.d : ℕ) : Error) / D.q + ((D.k * D.d : ℕ) : Error) / D.q := by
      change (((D.m + D.k) * D.d : ℕ) : Error) / D.q = _
      rw [Nat.add_mul]; push_cast; ring
    rw [avgOver_congr _ _ _ heq, avgOver_add, avgOver_uniform_const, hsp]
    linarith

/-! ## Section 2: Combined strategy, question law, win transport, and value bound -/

def coefficientsOfPolynomial {K : Type*} [Semiring K] (n : ℕ) (p : _root_.Polynomial K) :
    Fin (n + 1) → K := fun i => p.coeff i.val

theorem evalCoefficient_coefficientsOfPolynomial {K : Type*} [Semiring K] {n : ℕ}
    {p : _root_.Polynomial K} (hp : p.natDegree ≤ n) (t : K) :
    evalCoefficient (coefficientsOfPolynomial n p) t = p.eval t := by
  rw [_root_.Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp) t,
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (n + 1)]; rfl

def shiftedLinePolynomial {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s : K) : _root_.Polynomial K :=
  (linePolynomialOfCoefficients f).comp (_root_.Polynomial.X + _root_.Polynomial.C s)

theorem shiftedLinePolynomial_natDegree_le {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s : K) : (shiftedLinePolynomial f s).natDegree ≤ n := by
  refine _root_.Polynomial.natDegree_comp_le.trans ?_
  have h1 : (_root_.Polynomial.X + _root_.Polynomial.C s : _root_.Polynomial K).natDegree ≤ 1 :=
    (_root_.Polynomial.natDegree_add_le _ _).trans (by simp [_root_.Polynomial.natDegree_X_le])
  exact (Nat.mul_le_mul (linePolynomialOfCoefficients_natDegree_le f) h1).trans_eq (mul_one n)

theorem shiftedLinePolynomial_eval {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s t : K) :
    (shiftedLinePolynomial f s).eval t = evalCoefficient f (t + s) := by
  rw [shiftedLinePolynomial, _root_.Polynomial.eval_comp]
  simpa using linePolynomialOfCoefficients_eval f (t + s)

def combinedAxisPolynomial {K : Type*} [CommSemiring K] {k n : ℕ}
    (α : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) : _root_.Polynomial K :=
  ∑ r, _root_.Polynomial.C (α r) * shiftedLinePolynomial (f r) s

def combinedDiagonalPolynomial {K : Type*} [CommSemiring K] {k n : ℕ}
    (α w : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) : _root_.Polynomial K :=
  ∑ r, (_root_.Polynomial.C (α r) + _root_.Polynomial.C (w r) * _root_.Polynomial.X) *
    shiftedLinePolynomial (f r) s

def fiberLinePolynomial {K : Type*} [CommSemiring K] {k : ℕ}
    (α w b : Fin k → K) : _root_.Polynomial K :=
  _root_.Polynomial.C (∑ r, α r * b r) + _root_.Polynomial.C (∑ r, w r * b r) * _root_.Polynomial.X

def directCombinedIndexSplit (D : DirectLdParams) (i : Fin D.combined.m) : Fin D.m ⊕ Fin D.k :=
  finSumFinEquiv.symm i

@[simp] theorem directCombinedIndexSplit_combinedPointVar (D : DirectLdParams) (j : Fin D.m) :
    directCombinedIndexSplit D (combinedPointVar D.m D.k j) = Sum.inl j := by
  simp [directCombinedIndexSplit, combinedPointVar]

@[simp] theorem directCombinedIndexSplit_combinedCoefficientVar (D : DirectLdParams) (r : Fin D.k) :
    directCombinedIndexSplit D (combinedCoefficientVar D.m D.k r) = Sum.inr r := by
  simp [directCombinedIndexSplit, combinedCoefficientVar]

def directCombinedQuestionDirection (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) : Fin D.combined.m → DirectScalarQ D :=
  match q.1 with
  | .point => 0
  | .aline => coordinateDirection q.2.index
  | .dline => q.2.direction

def directCombinedMeasuredDirection (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) : Fin D.m → DirectScalarQ D :=
  match q.1, directCombinedIndexSplit D q.2.index with
  | .aline, .inl j => coordinateDirection j
  | .dline, .inl j => directPrefixProjection j (combinedPointPart (m := D.m) (k := D.k) q.2.direction)
  | _, _ => 0

def directCombinedRebaseParameter (D : DirectLdParams) (q : DirectLdQuestion D.combined) : DirectScalarQ D :=
  directLineRepParameter (directCombinedMeasuredDirection D q)
    (combinedPointPart (m := D.m) (k := D.k) q.2.point)

def directCombinedMeasuredQuestion (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) : DirectLdQuestion D :=
  match q.1, directCombinedIndexSplit D q.2.index with
  | .aline, .inl j => (.aline, directLdMap D .aline ⟨combinedPointPart (m := D.m) (k := D.k) q.2.point, j, 0⟩)
  | .dline, .inl j => (.dline, directLdMap D .dline
      ⟨combinedPointPart (m := D.m) (k := D.k) q.2.point, j,
       combinedPointPart (m := D.m) (k := D.k) q.2.direction⟩)
  | _, _ => directLdPointQuestionOf D (combinedPointPart (m := D.m) (k := D.k) q.2.point)

def directCombinedAnswerMap (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) (a : DirectLdAnswer D) : DirectLdAnswer D.combined :=
  let α := combinedCoefficientPart (m := D.m) (k := D.k) q.2.point
  let w := combinedCoefficientPart (m := D.m) (k := D.k) (directCombinedQuestionDirection D q)
  let s := directCombinedRebaseParameter D q
  match q.1, directCombinedIndexSplit D q.2.index with
  | .point, _ => .pointVals fun _ => match a with
      | .pointVals b => ∑ r, α r * b r | _ => 0
  | .aline, .inl _ => .alinePolys fun _ => match a with
      | .alinePolys f => coefficientsOfPolynomial D.combined.d (combinedAxisPolynomial α s f) | _ => 0
  | .aline, .inr _ => .alinePolys fun _ => match a with
      | .pointVals b => coefficientsOfPolynomial D.combined.d (fiberLinePolynomial α w b) | _ => 0
  | .dline, .inl _ => .dlinePolys fun _ => match a with
      | .dlinePolys f => coefficientsOfPolynomial (D.combined.m * D.combined.d) (combinedDiagonalPolynomial α w s f) | _ => 0
  | .dline, .inr _ => .dlinePolys fun _ => match a with
      | .pointVals b => coefficientsOfPolynomial (D.combined.m * D.combined.d) (fiberLinePolynomial α w b) | _ => 0

def directCombinedStrategy (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    Strategy (directLdGame D.combined) where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A q := (S.A (directCombinedMeasuredQuestion D q)).postprocess (directCombinedAnswerMap D q)
  B q := (S.B (directCombinedMeasuredQuestion D q)).postprocess (directCombinedAnswerMap D q)

theorem directCombinedStrategy_isProjective (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (hS : S.IsProjective) :
    (directCombinedStrategy D S).IsProjective :=
  ⟨fun _ => postprocess_isProjective _ (hS.1 _) _, fun _ => postprocess_isProjective _ (hS.2 _) _⟩

theorem lineRepMap_combinedPointPart_lineRepMap (D : DirectLdParams)
    (V z : Fin D.combined.m → DirectScalarQ D) :
    lineRepMap (combinedPointPart (m := D.m) (k := D.k) V)
        (combinedPointPart (m := D.m) (k := D.k) (lineRepMap V z)) =
      lineRepMap (combinedPointPart (m := D.m) (k := D.k) V)
        (combinedPointPart (m := D.m) (k := D.k) z) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span V z)
  have hz : lineRepMap V z = z + (-c) • V := by rw [neg_smul, hc]; abel
  rw [hz]; exact lineRepMap_add_smul _ _ (-c)

theorem combinedPointPart_lineRepMap_of_eq_zero (D : DirectLdParams)
    (V z : Fin D.combined.m → DirectScalarQ D)
    (hV : combinedPointPart (m := D.m) (k := D.k) V = 0) :
    combinedPointPart (m := D.m) (k := D.k) (lineRepMap V z) =
      combinedPointPart (m := D.m) (k := D.k) z := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span V z)
  have hz : lineRepMap V z = z - c • V := by rw [hc]; abel
  rw [hz]; change combinedPointPart z - c • combinedPointPart V = _
  rw [hV, smul_zero, sub_zero]

theorem combinedPointPart_coordDir_pt (D : DirectLdParams) (j : Fin D.m) :
    combinedPointPart (m := D.m) (k := D.k)
      (coordinateDirection (combinedPointVar D.m D.k j) : Fin D.combined.m → DirectScalarQ D) =
    coordinateDirection j := by
  funext j'; by_cases h : j' = j
  · subst h; simp [combinedPointPart, coordinateDirection]
  · simp only [combinedPointPart, coordinateDirection]
    rw [Pi.single_eq_of_ne (M := fun _ => DirectScalarQ D) fun hc => h (combinedPointVar_injective D.m D.k hc),
      Pi.single_eq_of_ne (M := fun _ => DirectScalarQ D) h]

theorem combinedPointPart_coordDir_cf (D : DirectLdParams) (r : Fin D.k) :
    combinedPointPart (m := D.m) (k := D.k)
      (coordinateDirection (combinedCoefficientVar D.m D.k r) : Fin D.combined.m → DirectScalarQ D) = 0 := by
  funext j; simp only [combinedPointPart, coordinateDirection, Pi.zero_apply]
  exact Pi.single_eq_of_ne (M := fun _ => DirectScalarQ D)
    (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j).symm 1

theorem combinedPointPart_prefix_pt (D : DirectLdParams) (j : Fin D.m)
    (w : Fin D.combined.m → DirectScalarQ D) :
    combinedPointPart (m := D.m) (k := D.k)
      (directPrefixProjection (combinedPointVar D.m D.k j) w) =
    directPrefixProjection j (combinedPointPart (m := D.m) (k := D.k) w) := by
  funext j'
  change (if (combinedPointVar D.m D.k j').val < (combinedPointVar D.m D.k j).val then 0 else _) =
    if j'.val < j.val then 0 else _
  rw [combinedPointVar_val, combinedPointVar_val]; rfl

theorem combinedPointPart_prefix_cf (D : DirectLdParams) (r : Fin D.k)
    (w : Fin D.combined.m → DirectScalarQ D) :
    combinedPointPart (m := D.m) (k := D.k)
      (directPrefixProjection (combinedCoefficientVar D.m D.k r) w) = 0 := by
  funext j'
  change (if (combinedPointVar D.m D.k j').val < (combinedCoefficientVar D.m D.k r).val then 0 else _) = 0
  rw [combinedPointVar_val, combinedCoefficientVar_val, if_pos (by omega)]

theorem directCombined_measuredQuestion_of_pointVar (D : DirectLdParams)
    (t : LdType) (j : Fin D.m) (s : DirectLdSpace D.combined)
    (hidx : s.index = combinedPointVar D.m D.k j) :
    directCombinedMeasuredQuestion D (t, directLdMap D.combined t s) =
      (t, directLdMap D t ⟨combinedPointPart s.point, j, combinedPointPart s.direction⟩) := by
  cases t
  · rfl
  · have hb := lineRepMap_combinedPointPart_lineRepMap D (coordinateDirection (combinedPointVar D.m D.k j)) s.point
    rw [combinedPointPart_coordDir_pt] at hb
    simp only [directLdMap, directCombinedMeasuredQuestion, hidx, directCombinedIndexSplit_combinedPointVar]
    exact congrArg (fun x : Fin D.m → DirectScalarQ D => ((LdType.aline, ⟨x, j, 0⟩) : DirectLdQuestion D)) hb
  · have hb := lineRepMap_combinedPointPart_lineRepMap D
      (directPrefixProjection (combinedPointVar D.m D.k j) s.direction) s.point
    rw [combinedPointPart_prefix_pt] at hb
    simp only [directLdMap, directCombinedMeasuredQuestion, hidx, directCombinedIndexSplit_combinedPointVar]
    rw [combinedPointPart_prefix_pt D j s.direction, directPrefixProjection_idem]
    exact congrArg (fun x : Fin D.m → DirectScalarQ D =>
      ((LdType.dline, ⟨x, j, directPrefixProjection j (combinedPointPart s.direction)⟩) : DirectLdQuestion D)) hb

theorem directCombined_measuredQuestion_of_coefficientVar (D : DirectLdParams)
    (t : LdType) (r : Fin D.k) (s : DirectLdSpace D.combined)
    (hidx : s.index = combinedCoefficientVar D.m D.k r) :
    directCombinedMeasuredQuestion D (t, directLdMap D.combined t s) =
      directLdPointQuestionOf D (combinedPointPart s.point) := by
  cases t
  · rfl
  · simp only [directLdMap, directCombinedMeasuredQuestion, hidx, directCombinedIndexSplit_combinedCoefficientVar]
    exact congrArg (directLdPointQuestionOf D)
      (combinedPointPart_lineRepMap_of_eq_zero D _ _ (combinedPointPart_coordDir_cf D r))
  · simp only [directLdMap, directCombinedMeasuredQuestion, hidx, directCombinedIndexSplit_combinedCoefficientVar]
    exact congrArg (directLdPointQuestionOf D)
      (combinedPointPart_lineRepMap_of_eq_zero D _ _ (combinedPointPart_prefix_cf D r s.direction))

theorem directLdBranchRejectionProbability_point_point_eq
    (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    directLdBranchRejectionProbability D S (.point, .point) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun u =>
        directRejectedMass D S (directLdPointQuestionOf D u) (directLdPointQuestionOf D u) := by
  rw [directLdBranchRejectionProbability_eq_avgOver, avgOver_uniform_equiv_prod (directLdSpaceIndexEquiv D)]
  have h1 (i : Fin D.m) :
      avgOver (uniformDistribution ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
        (fun pd => directRejectedMass D S (directLdPointQuestionOf D pd.1) (directLdPointQuestionOf D pd.1)) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) fun u =>
        directRejectedMass D S (directLdPointQuestionOf D u) (directLdPointQuestionOf D u) := by
    rw [avgOver_uniform_prod (fun u _ => directRejectedMass D S (directLdPointQuestionOf D u) (directLdPointQuestionOf D u))]
    exact avgOver_congr _ _ _ fun _ => avgOver_uniform_const _
  exact (avgOver_congr _ _ _ h1).trans (avgOver_uniform_const _)

def DirectCombinedWinTransport (D : DirectLdParams) (t₁ t₂ : LdType)
    (s : DirectLdSpace D.combined) : Prop :=
  ∀ a b : DirectLdAnswer D,
    directLdWinPredicate D
        (directCombinedMeasuredQuestion D (t₁, directLdMap D.combined t₁ s))
        (directCombinedMeasuredQuestion D (t₂, directLdMap D.combined t₂ s)) a b = true →
      directLdWinPredicate D.combined
        (t₁, directLdMap D.combined t₁ s) (t₂, directLdMap D.combined t₂ s)
        (directCombinedAnswerMap D (t₁, directLdMap D.combined t₁ s) a)
        (directCombinedAnswerMap D (t₂, directLdMap D.combined t₂ s) b) = true

theorem DirectCombinedWinTransport.symm {D : DirectLdParams} {t₁ t₂ : LdType}
    {s : DirectLdSpace D.combined} (h : DirectCombinedWinTransport D t₁ t₂ s) :
    DirectCombinedWinTransport D t₂ t₁ s := fun a b hw => by
  rw [directLdWinPredicate_symm] at hw ⊢; exact h b a hw

set_option maxHeartbeats 800000 in
-- All nine transport branches are discharged in one combined theorem.
theorem directCombinedWinTransport_all (D : DirectLdParams) (t₁ t₂ : LdType)
    (s : DirectLdSpace D.combined) : DirectCombinedWinTransport D t₁ t₂ s := by
  have hspPt {i : Fin D.combined.m} {j : Fin D.m} (h : directCombinedIndexSplit D i = Sum.inl j) :
      i = combinedPointVar D.m D.k j := by
    have hi := congrArg finSumFinEquiv h
    rwa [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  have hspCf {i : Fin D.combined.m} {r : Fin D.k} (h : directCombinedIndexSplit D i = Sum.inr r) :
      i = combinedCoefficientVar D.m D.k r := by
    have hi := congrArg finSumFinEquiv h
    rwa [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  have hval (q : DirectLdQuestion D.combined) (a : DirectLdAnswer D) :
      validDirectLdAnswer q.1 (directCombinedAnswerMap D q a) = true := by
    obtain ⟨t, xq⟩ := q
    cases t
    · rfl
    · rcases hs : directCombinedIndexSplit D xq.index with _ | _ <;> simp [directCombinedAnswerMap, hs, validDirectLdAnswer]
    · rcases hs : directCombinedIndexSplit D xq.index with _ | _ <;> simp [directCombinedAnswerMap, hs, validDirectLdAnswer]
  have hself (q : DirectLdQuestion D) {a b} (hw : directLdWinPredicate D q q a b = true) : a = b := by
    obtain ⟨t, _⟩ := q
    cases t <;> cases a <;> cases b <;>
      simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self, Bool.and_false,
        Bool.false_and, Bool.true_and, ↓reduceIte, Bool.false_eq_true, decide_eq_true_eq] at hw
    all_goals exact congrArg _ hw
  have hfib (n : ℕ) (hn : 1 ≤ n) (z base dirn : Fin D.combined.m → DirectScalarQ D)
      (b : Fin D.k → DirectScalarQ D) (T : DirectScalarQ D) (hT : z = base + T • dirn) :
      evalCoefficient (coefficientsOfPolynomial n
        (fiberLinePolynomial (combinedCoefficientPart base) (combinedCoefficientPart dirn) b)) T =
      ∑ r, combinedCoefficientPart (m := D.m) (k := D.k) z r * b r := by
    have hnd : (fiberLinePolynomial (combinedCoefficientPart (m := D.m) (k := D.k) base)
        (combinedCoefficientPart dirn) b).natDegree ≤ 1 :=
      (_root_.Polynomial.natDegree_add_le _ _).trans <| max_le
        ((_root_.Polynomial.natDegree_C _).le.trans (Nat.zero_le 1))
        ((_root_.Polynomial.natDegree_C_mul_le _ _).trans _root_.Polynomial.natDegree_X_le)
    rw [evalCoefficient_coefficientsOfPolynomial (hnd.trans hn), fiberLinePolynomial]
    simp only [_root_.Polynomial.eval_add, _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C,
      _root_.Polynomial.eval_X, Finset.sum_mul, ← Finset.sum_add_distrib, hT]
    exact Finset.sum_congr rfl fun r _ => by change _ = (combinedCoefficientPart base r + T * combinedCoefficientPart dirn r) * b r; ring
  have hal_pt : DirectCombinedWinTransport D .aline .point s := fun a b hwin => by
    rcases hsp : directCombinedIndexSplit D s.index with j | r₀
    · have hidx := hspPt hsp
      rw [directCombined_measuredQuestion_of_pointVar D .aline j s hidx,
        directCombined_measuredQuestion_of_pointVar D .point j s hidx] at hwin
      cases a with
      | pointVals _ | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | alinePolys f =>
        cases b with
        | alinePolys _ | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
        | pointVals c =>
          have hcond : directAlinePointCondition D
              (directLdMap D .aline ⟨combinedPointPart s.point, j, combinedPointPart s.direction⟩)
              (directLdMap D .point ⟨combinedPointPart s.point, j, combinedPointPart s.direction⟩) f c := by
            simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
          have hspL : directCombinedIndexSplit D (directLdMap D.combined .aline s).index = Sum.inl j := hsp
          have hmA : directCombinedAnswerMap D (.aline, directLdMap D.combined .aline s) (.alinePolys f) =
              .alinePolys fun _ => coefficientsOfPolynomial D.combined.d
                (combinedAxisPolynomial (combinedCoefficientPart (directLdMap D.combined .aline s).point)
                  (directCombinedRebaseParameter D (.aline, directLdMap D.combined .aline s)) f) := by
            simp only [directCombinedAnswerMap, hspL]
          have hmB : directCombinedAnswerMap D (.point, directLdMap D.combined .point s) (.pointVals c) =
              .pointVals fun _ => ∑ r, combinedCoefficientPart s.point r * c r := rfl
          rw [hmA, hmB]
          suffices hg : directAlinePointCondition D.combined
              (directLdMap D.combined .aline s) (directLdMap D.combined .point s) _ _ by
            simpa [directLdWinPredicate, validDirectLdAnswer] using hg
          intro T hT _
          change s.point = _ at hT
          have hcf0 : combinedCoefficientPart (m := D.m) (k := D.k)
              (coordinateDirection s.index : Fin D.combined.m → DirectScalarQ D) = 0 := by
            rw [hidx]; funext r; simp only [combinedCoefficientPart, coordinateDirection, Pi.zero_apply]
            exact Pi.single_eq_of_ne (M := fun _ => DirectScalarQ D)
              (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j) 1
          have hz : combinedCoefficientPart (m := D.m) (k := D.k) s.point =
              combinedCoefficientPart (directLdMap D.combined .aline s).point := by
            funext r; conv_lhs => rw [hT]
            change combinedCoefficientPart _ r +
              T * combinedCoefficientPart (coordinateDirection s.index : Fin D.combined.m → DirectScalarQ D) r = _
            rw [hcf0]; simp
          have hnd : (combinedAxisPolynomial (combinedCoefficientPart (directLdMap D.combined .aline s).point)
              (directCombinedRebaseParameter D (.aline, directLdMap D.combined .aline s)) f).natDegree ≤ D.combined.d :=
            _root_.Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ =>
              (_root_.Polynomial.natDegree_C_mul_le _ _).trans (shiftedLinePolynomial_natDegree_le _ _)
          beta_reduce
          rw [evalCoefficient_coefficientsOfPolynomial hnd, combinedAxisPolynomial, _root_.Polynomial.eval_finsetSum, hz]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, shiftedLinePolynomial_eval]
          congr 1
          have hspec : combinedPointPart (directLdMap D.combined .aline s).point =
              lineRepMap (directCombinedMeasuredDirection D (.aline, directLdMap D.combined .aline s))
                (combinedPointPart (directLdMap D.combined .aline s).point) +
              directCombinedRebaseParameter D (.aline, directLdMap D.combined .aline s) •
                directCombinedMeasuredDirection D (.aline, directLdMap D.combined .aline s) :=
            directLineRepParameter_spec _ _
          have hmd : directCombinedMeasuredDirection D (.aline, directLdMap D.combined .aline s) =
              coordinateDirection j := by simp [directCombinedMeasuredDirection, directLdMap, hsp]
          have hdpt : combinedPointPart (m := D.m) (k := D.k)
              (coordinateDirection s.index : Fin D.combined.m → DirectScalarQ D) =
              coordinateDirection j := by rw [hidx]; exact combinedPointPart_coordDir_pt D j
          have hpt : combinedPointPart s.point =
              lineRepMap (coordinateDirection j) (combinedPointPart s.point) +
                (T + directCombinedRebaseParameter D (.aline, directLdMap D.combined .aline s)) • coordinateDirection j := by
            have hb := lineRepMap_combinedPointPart_lineRepMap D (coordinateDirection s.index) s.point
            rw [hdpt] at hb; rw [hmd] at hspec
            conv_lhs => rw [hT]
            change combinedPointPart (directLdMap D.combined .aline s).point +
              T • combinedPointPart (coordinateDirection s.index) = _
            rw [hdpt, hspec]; dsimp only [directLdMap]; rw [hb]; module
          exact hcond _ hpt r
    · have hidx := hspCf hsp
      rw [directCombined_measuredQuestion_of_coefficientVar D .aline r₀ s hidx,
        directCombined_measuredQuestion_of_coefficientVar D .point r₀ s hidx] at hwin
      have hab := hself _ hwin; subst hab
      cases a with
      | alinePolys _ | dlinePolys _ =>
          simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
      | pointVals bv =>
          have hspL : directCombinedIndexSplit D (directLdMap D.combined .aline s).index = Sum.inr r₀ := hsp
          have hmA : directCombinedAnswerMap D (.aline, directLdMap D.combined .aline s) (.pointVals bv) =
              .alinePolys fun _ => coefficientsOfPolynomial D.combined.d
                (fiberLinePolynomial (combinedCoefficientPart (directLdMap D.combined .aline s).point)
                  (combinedCoefficientPart (directCombinedQuestionDirection D (.aline, directLdMap D.combined .aline s))) bv) := by
            simp only [directCombinedAnswerMap, hspL]
          rw [hmA]; change directLdWinPredicate D.combined _ _ _ (.pointVals _) = true
          suffices hg : directAlinePointCondition D.combined
              (directLdMap D.combined .aline s) (directLdMap D.combined .point s) _ _ by
            simpa [directLdWinPredicate, validDirectLdAnswer] using hg
          intro T hT _; exact hfib D.combined.d D.hd _ _ _ bv T hT
  have hdl_pt : DirectCombinedWinTransport D .dline .point s := fun a b hwin => by
    rcases hsp : directCombinedIndexSplit D s.index with j | r₀
    · have hidx := hspPt hsp
      rw [directCombined_measuredQuestion_of_pointVar D .dline j s hidx,
        directCombined_measuredQuestion_of_pointVar D .point j s hidx] at hwin
      cases a with
      | pointVals _ | alinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
      | dlinePolys f =>
        cases b with
        | alinePolys _ | dlinePolys _ => simp [directLdWinPredicate, validDirectLdAnswer] at hwin
        | pointVals c =>
          have hcond : directDlinePointCondition D
              (directLdMap D .dline ⟨combinedPointPart s.point, j, combinedPointPart s.direction⟩)
              (directLdMap D .point ⟨combinedPointPart s.point, j, combinedPointPart s.direction⟩) f c := by
            simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
          have hspL : directCombinedIndexSplit D (directLdMap D.combined .dline s).index = Sum.inl j := hsp
          have hmA : directCombinedAnswerMap D (.dline, directLdMap D.combined .dline s) (.dlinePolys f) =
              .dlinePolys fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
                (combinedDiagonalPolynomial (combinedCoefficientPart (directLdMap D.combined .dline s).point)
                  (combinedCoefficientPart (directCombinedQuestionDirection D (.dline, directLdMap D.combined .dline s)))
                  (directCombinedRebaseParameter D (.dline, directLdMap D.combined .dline s)) f) := by
            simp only [directCombinedAnswerMap, hspL]
          have hmB : directCombinedAnswerMap D (.point, directLdMap D.combined .point s) (.pointVals c) =
              .pointVals fun _ => ∑ r, combinedCoefficientPart s.point r * c r := rfl
          rw [hmA, hmB]
          suffices hg : directDlinePointCondition D.combined
              (directLdMap D.combined .dline s) (directLdMap D.combined .point s) _ _ by
            simpa [directLdWinPredicate, validDirectLdAnswer] using hg
          intro T hT _
          change s.point = _ at hT
          have hdeg : (combinedDiagonalPolynomial (combinedCoefficientPart (directLdMap D.combined .dline s).point)
              (combinedCoefficientPart (directCombinedQuestionDirection D (.dline, directLdMap D.combined .dline s)))
              (directCombinedRebaseParameter D (.dline, directLdMap D.combined .dline s)) f).natDegree ≤
              D.combined.m * D.combined.d := by
            have h1 : 1 ≤ D.k * D.d := Nat.mul_pos D.hk D.hd
            have hmd : D.m * D.d + 1 ≤ D.combined.m * D.combined.d := by
              change D.m * D.d + 1 ≤ (D.m + D.k) * D.d; rw [Nat.add_mul]; omega
            refine (_root_.Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_).trans hmd
            refine _root_.Polynomial.natDegree_mul_le.trans ((Nat.add_le_add ?_
              (shiftedLinePolynomial_natDegree_le _ _)).trans_eq (Nat.add_comm 1 _))
            exact (_root_.Polynomial.natDegree_add_le _ _).trans <| max_le
              ((_root_.Polynomial.natDegree_C _).le.trans (Nat.zero_le 1))
              ((_root_.Polynomial.natDegree_C_mul_le _ _).trans _root_.Polynomial.natDegree_X_le)
          beta_reduce
          rw [evalCoefficient_coefficientsOfPolynomial hdeg, combinedDiagonalPolynomial,
            _root_.Polynomial.eval_finsetSum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
            _root_.Polynomial.eval_C, _root_.Polynomial.eval_C, _root_.Polynomial.eval_X,
            shiftedLinePolynomial_eval, mul_comm _ T]
          have hz : combinedCoefficientPart (m := D.m) (k := D.k) s.point r =
              combinedCoefficientPart (directLdMap D.combined .dline s).point r +
                T * combinedCoefficientPart (directCombinedQuestionDirection D (.dline, directLdMap D.combined .dline s)) r := by
            conv_lhs => rw [hT]
            rfl
          rw [hz]
          congr 1
          have hspec : combinedPointPart (directLdMap D.combined .dline s).point =
              lineRepMap (directCombinedMeasuredDirection D (.dline, directLdMap D.combined .dline s))
                (combinedPointPart (directLdMap D.combined .dline s).point) +
              directCombinedRebaseParameter D (.dline, directLdMap D.combined .dline s) •
                directCombinedMeasuredDirection D (.dline, directLdMap D.combined .dline s) :=
            directLineRepParameter_spec _ _
          have hdpt : combinedPointPart (m := D.m) (k := D.k) (directPrefixProjection s.index s.direction) =
              directPrefixProjection j (combinedPointPart s.direction) := by
            rw [hidx]; exact combinedPointPart_prefix_pt D j s.direction
          have hmd : directCombinedMeasuredDirection D (.dline, directLdMap D.combined .dline s) =
              directPrefixProjection j (combinedPointPart s.direction) := by
            simp only [directCombinedMeasuredDirection, directLdMap, hidx,
              directCombinedIndexSplit_combinedPointVar]
            rw [combinedPointPart_prefix_pt D j s.direction, directPrefixProjection_idem]
          have hpt : combinedPointPart s.point =
              lineRepMap (directPrefixProjection j (combinedPointPart s.direction)) (combinedPointPart s.point) +
                (T + directCombinedRebaseParameter D (.dline, directLdMap D.combined .dline s)) •
                  directPrefixProjection j (combinedPointPart s.direction) := by
            have hb := lineRepMap_combinedPointPart_lineRepMap D (directPrefixProjection s.index s.direction) s.point
            rw [hdpt] at hb; rw [hmd] at hspec
            conv_lhs => rw [hT]
            change combinedPointPart (directLdMap D.combined .dline s).point +
              T • combinedPointPart (directPrefixProjection s.index s.direction) = _
            rw [hdpt, hspec]; dsimp only [directLdMap]; rw [hb]; module
          exact hcond _ hpt r
    · have hidx := hspCf hsp
      rw [directCombined_measuredQuestion_of_coefficientVar D .dline r₀ s hidx,
        directCombined_measuredQuestion_of_coefficientVar D .point r₀ s hidx] at hwin
      have hab := hself _ hwin; subst hab
      cases a with
      | alinePolys _ | dlinePolys _ =>
          simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
      | pointVals bv =>
          have hspL : directCombinedIndexSplit D (directLdMap D.combined .dline s).index = Sum.inr r₀ := hsp
          have hmA : directCombinedAnswerMap D (.dline, directLdMap D.combined .dline s) (.pointVals bv) =
              .dlinePolys fun _ => coefficientsOfPolynomial (D.combined.m * D.combined.d)
                (fiberLinePolynomial (combinedCoefficientPart (directLdMap D.combined .dline s).point)
                  (combinedCoefficientPart (directCombinedQuestionDirection D (.dline, directLdMap D.combined .dline s))) bv) := by
            simp only [directCombinedAnswerMap, hspL]
          rw [hmA]; change directLdWinPredicate D.combined _ _ _ (.pointVals _) = true
          suffices hg : directDlinePointCondition D.combined
              (directLdMap D.combined .dline s) (directLdMap D.combined .point s) _ _ by
            simpa [directLdWinPredicate, validDirectLdAnswer] using hg
          intro T hT _
          exact hfib (D.combined.m * D.combined.d) (Nat.mul_pos D.combined.hm D.combined.hd) _ _ _ bv T hT
  have hdiag (t : LdType) : DirectCombinedWinTransport D t t s := fun a b hw => by
    have hab := hself _ hw; subst hab
    have hv := hval (t, directLdMap D.combined t s) a
    dsimp only at hv
    generalize directCombinedAnswerMap D (t, directLdMap D.combined t s) a = a' at hv ⊢
    cases t <;> cases a' <;> simp only [directLdWinPredicate, hv, Bool.and_self, ↓reduceIte, decide_true]
  have hal_dl : DirectCombinedWinTransport D .aline .dline s := fun a b _ => by
    have ha := hval (.aline, directLdMap D.combined .aline s) a
    have hb := hval (.dline, directLdMap D.combined .dline s) b
    dsimp only at ha hb
    rcases h1 : directCombinedAnswerMap D (.aline, directLdMap D.combined .aline s) a with _ | f | _
    · simp [validDirectLdAnswer, h1] at ha
    · rcases h2 : directCombinedAnswerMap D (.dline, directLdMap D.combined .dline s) b with _ | _ | g
      · simp [validDirectLdAnswer, h2] at hb
      · simp [validDirectLdAnswer, h2] at hb
      · simp [directLdWinPredicate, validDirectLdAnswer, h1, h2]
    · simp [validDirectLdAnswer, h1] at ha
  cases t₁ <;> cases t₂
  · exact hdiag .point
  · exact hal_pt.symm
  · exact hdl_pt.symm
  · exact hal_pt
  · exact hdiag .aline
  · exact hal_dl
  · exact hdl_pt
  · exact hal_dl.symm
  · exact hdiag .dline

theorem directCombinedStrategy_value_ge (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (ε : ℝ) (hvalue : 1 - ε ≤ S.value) :
    1 - 10 * ε ≤ (directCombinedStrategy D S).value := by
  have hmpos : 0 < D.m := D.hm
  have hkpos : 0 < D.k := D.hk
  letI : Nonempty (Fin D.combined.m) := ⟨⟨0, Nat.add_pos_left hmpos D.k⟩⟩
  have hrm (x y : DirectLdQuestion D.combined)
      (himp : ∀ a b, directLdWinPredicate D (directCombinedMeasuredQuestion D x)
          (directCombinedMeasuredQuestion D y) a b = true →
        directLdWinPredicate D.combined x y (directCombinedAnswerMap D x a)
          (directCombinedAnswerMap D y b) = true) :
      directRejectedMass D.combined (directCombinedStrategy D S) x y ≤
        directRejectedMass D S (directCombinedMeasuredQuestion D x) (directCombinedMeasuredQuestion D y) := by
    classical
    let mx := directCombinedMeasuredQuestion D x
    let my := directCombinedMeasuredQuestion D y
    let F (a b : DirectLdAnswer D) : ℝ :=
      if directLdWinPredicate D.combined x y (directCombinedAnswerMap D x a)
          (directCombinedAnswerMap D y b) then 0 else outcomeWeight S mx my a b
    have how (a' b' : DirectLdAnswer D.combined) :
        outcomeWeight (directCombinedStrategy D S) x y a' b' =
          ∑ a ∈ Finset.univ.filter (fun a => directCombinedAnswerMap D x a = a'),
            ∑ b ∈ Finset.univ.filter (fun b => directCombinedAnswerMap D y b = b'),
              outcomeWeight S mx my a b := by
      show stateQForm S.ψ (heteroKron (((S.A mx).postprocess _).effect a') (((S.B my).postprocess _).effect b')) = _
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect, MIPStarRE.Quantum.Measurement.postprocess_effect,
        heteroKron_finset_sum_left, stateQForm_finset_sum]
      exact Finset.sum_congr rfl fun _ _ => by rw [heteroKron_finset_sum_right, stateQForm_finset_sum]; rfl
    have hstep (a' b') :
        (if directLdWinPredicate D.combined x y a' b' then 0
          else outcomeWeight (directCombinedStrategy D S) x y a' b') =
        ∑ a ∈ Finset.univ.filter (fun a => directCombinedAnswerMap D x a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => directCombinedAnswerMap D y b = b'), F a b := by
      by_cases hw : directLdWinPredicate D.combined x y a' b' = true
      · rw [if_pos hw]; symm
        exact Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => by
          simp [F, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hw]
      · rw [if_neg hw, how]
        exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by
          simp [F, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hw]
    have hmass : directRejectedMass D.combined (directCombinedStrategy D S) x y = ∑ a, ∑ b, F a b := by
      unfold directRejectedMass; simp_rw [hstep]
      rw [← Finset.sum_fiberwise Finset.univ (directCombinedAnswerMap D x) (fun a => ∑ b, F a b)]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans
        (Finset.sum_congr rfl fun a _ => Finset.sum_fiberwise Finset.univ (directCombinedAnswerMap D y) (F a))
    rw [hmass, directRejectedMass]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    dsimp only [F]
    by_cases hw : directLdWinPredicate D mx my a b = true
    · rw [if_pos hw, if_pos (himp a b hw)]
    · rw [if_neg hw]; split_ifs
      · exact outcomeWeight_nonneg S mx my a b
      · exact le_rfl
  let eSp : DirectLdSpace D.combined ≃
      ((Fin D.combined.m × ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) ×
        ((Fin D.k → DirectScalarQ D) × (Fin D.k → DirectScalarQ D))) :=
    { toFun := fun s => ((s.index, (combinedPointPart s.point, combinedPointPart s.direction)),
        (combinedCoefficientPart s.point, combinedCoefficientPart s.direction))
      invFun := fun x => ⟨combinedPoint x.1.2.1 x.2.1, x.1.1, combinedPoint x.1.2.2 x.2.2⟩
      left_inv := fun ⟨_, _, _⟩ => by simp
      right_inv := fun ⟨⟨_, _, _⟩, _, _⟩ => by simp }
  have hbr (types : LdType × LdType) :
      directLdBranchRejectionProbability D.combined (directCombinedStrategy D S) types ≤
        directLdBranchRejectionProbability D S types +
        directLdBranchRejectionProbability D S (.point, .point) := by
    let M (i : Fin D.combined.m) (pd : (Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)) : ℝ :=
      match directCombinedIndexSplit D i with
      | .inl j => directRejectedMass D S (types.1, directLdMap D types.1 ⟨pd.1, j, pd.2⟩)
          (types.2, directLdMap D types.2 ⟨pd.1, j, pd.2⟩)
      | .inr _ => directRejectedMass D S (directLdPointQuestionOf D pd.1) (directLdPointQuestionOf D pd.1)
    have hunif : (uniformDistribution (DirectLdSpace D.combined)).map
        (fun s => (s.index, (combinedPointPart (m := D.m) (k := D.k) s.point,
          combinedPointPart (m := D.m) (k := D.k) s.direction))) =
        uniformDistribution (Fin D.combined.m × ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D))) :=
      uniformDistribution_map_fst_of_equiv (e := eSp) _ fun _ => rfl
    have h1 : directLdBranchRejectionProbability D.combined (directCombinedStrategy D S) types ≤
        avgOver (uniformDistribution (Fin D.combined.m ×
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))) (fun x => M x.1 x.2) := by
      rw [directLdBranchRejectionProbability_eq_avgOver, ← hunif, Distribution.avgOver_map]
      refine avgOver_mono _ _ _ fun s => (hrm _ _ (directCombinedWinTransport_all D types.1 types.2 s)).trans_eq ?_
      rcases hsp : directCombinedIndexSplit D s.index with j | r
      · have hidx : s.index = combinedPointVar D.m D.k j := by
          have hi := congrArg finSumFinEquiv hsp
          rwa [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
        rw [directCombined_measuredQuestion_of_pointVar D types.1 j s hidx,
          directCombined_measuredQuestion_of_pointVar D types.2 j s hidx]
        simp [M, hsp]
      · have hidx : s.index = combinedCoefficientVar D.m D.k r := by
          have hi := congrArg finSumFinEquiv hsp
          rwa [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
        rw [directCombined_measuredQuestion_of_coefficientVar D types.1 r s hidx,
          directCombined_measuredQuestion_of_coefficientVar D types.2 r s hidx]
        simp [M, hsp]
    refine h1.trans ?_
    rw [avgOver_uniform_prod (f := M), avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin]
    have hsum : ∑ i : Fin D.combined.m, avgOver (uniformDistribution _) (M i) =
        (D.m : ℝ) * directLdBranchRejectionProbability D S types +
        (D.k : ℝ) * directLdBranchRejectionProbability D S (.point, .point) := by
      change ∑ i : Fin (D.m + D.k), _ = _
      rw [Fin.sum_univ_add]
      congr 1
      · have hidx : directLdBranchRejectionProbability D S types =
            avgOver (uniformDistribution (Fin D.m)) fun j =>
              avgOver (uniformDistribution _) (M (combinedPointVar D.m D.k j)) := by
          rw [directLdBranchRejectionProbability_eq_avgOver,
            avgOver_uniform_equiv_prod (e := directLdSpaceIndexEquiv D)]
          exact avgOver_congr _ _ _ fun j => avgOver_congr _ _ _ fun pd => by
            simp [M, directLdSpaceIndexEquiv]
        rw [hidx, avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin]
        have hm0 : (D.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        field_simp [hm0]; rfl
      · have hcf (r : Fin D.k) : avgOver (uniformDistribution _) (M (Fin.natAdd D.m r)) =
            directLdBranchRejectionProbability D S (.point, .point) := by
          have heq : M (combinedCoefficientVar D.m D.k r) = fun pd =>
              directRejectedMass D S (directLdPointQuestionOf D pd.1) (directLdPointQuestionOf D pd.1) := by
            funext pd; simp [M]
          change avgOver _ (M (combinedCoefficientVar D.m D.k r)) = _
          rw [heq, avgOver_uniform_prod (fun u _ => directRejectedMass D S (directLdPointQuestionOf D u) (directLdPointQuestionOf D u)),
            directLdBranchRejectionProbability_point_point_eq]
          exact avgOver_congr _ _ _ fun _ => avgOver_uniform_const _
        simp [hcf, Finset.sum_const, nsmul_eq_mul]
    rw [hsum, show ((D.combined.m : ℕ) : ℝ) = (D.m : ℝ) + D.k by change ((D.m + D.k : ℕ) : ℝ) = _; push_cast; ring,
      inv_mul_eq_div, div_le_iff₀ (by positivity)]
    have hB := directLdBranchRejectionProbability_nonneg D S types
    have hP := directLdBranchRejectionProbability_nonneg D S (.point, .point)
    have hm : (0 : ℝ) < D.m := by exact_mod_cast hmpos
    have hk : (0 : ℝ) < D.k := by exact_mod_cast hkpos
    nlinarith [mul_nonneg hm.le hP, mul_nonneg hk.le hB]
  have hnn := directLdBranchRejectionProbability_nonneg D S
  have hcomb : directLdRejectionProbability D.combined (directCombinedStrategy D S) ≤
      10 * directLdRejectionProbability D S := by
    rw [directLdRejectionProbability, directLdRejectionProbability, avgOver_ldType_pair, avgOver_ldType_pair]
    linarith [hbr (.point, .point), hbr (.point, .aline), hbr (.point, .dline),
      hbr (.aline, .point), hbr (.aline, .aline), hbr (.aline, .dline),
      hbr (.dline, .point), hbr (.dline, .aline), hbr (.dline, .dline),
      hnn (.point, .point), hnn (.point, .aline), hnn (.point, .dline),
      hnn (.aline, .point), hnn (.aline, .aline), hnn (.aline, .dline),
      hnn (.dline, .point), hnn (.dline, .aline), hnn (.dline, .dline)]
  rw [directLdRejectionProbability_eq_one_sub_value,
    directLdRejectionProbability_eq_one_sub_value] at hcomb
  linarith

/-! ## Section 3: Recovery consistency transport -/

theorem consistencyDefect_le_of_recoveryBound
    {X Y β Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → MIPStarRE.Quantum.Measurement β ιA) (B : MIPStarRE.Quantum.Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hFbound : ∀ x b g, avgOver (uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, avgOver (uniformDistribution X) (fun x => F x g) ≤ η) :
    consistencyDefect (uniformDistribution X)
        (fun x b => heteroKron ((A x).effect b) 1)
        (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤
      consistencyDefect (uniformDistribution (X × Y))
        (fun z r => heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
        (fun z r => heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ + η := by
  classical
  let w (x : X) (b : β) (g : Γ) : ℝ := stateQForm ψ (heteroKron ((A x).effect b) (B.effect g))
  let W (g : Γ) : ℝ := stateQForm ψ (heteroKron (1 : Op ιA) (B.effect g))
  have hwnn (x b g) : 0 ≤ w x b g := stateQForm_nonneg ψ (kronecker_nonneg ((A x).pos b) (B.pos g))
  have hWnn (g) : 0 ≤ W g := stateQForm_nonneg ψ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (B.pos g))
  have hfib (x g) : ∑ b, w x b g = W g := by
    dsimp [w, W]; rw [← (A x).sum_eq_one, heteroKron_finset_sum_left, stateQForm_finset_sum]
  have hWsum : ∑ g, W g = 1 := by
    dsimp [W]; rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, B.sum_eq_one,
      heteroKron_one_one, stateQForm_one, hψ, one_pow]
  let AgrG (x : X) : ℝ := ∑ b, ∑ g, if f x g = b then w x b g else 0
  let AgrH (x : X) (y : Y) : ℝ := ∑ b, ∑ g, if e₁ x y b = f₁ x y g then w x b g else 0
  have hgoal : consistencyDefect (uniformDistribution X)
      (fun x b => heteroKron ((A x).effect b) 1)
      (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ =
      1 - avgOver (uniformDistribution X) AgrG := by
    rw [consistencyDefect_placed_eq_avg_point (uniformDistribution X) A (fun x => B.postprocess (f x))]
    have hpt (x : X) : (∑ b, ∑ b', if b = b' then 0 else
        stateQForm ψ (heteroKron ((A x).effect b) ((B.postprocess (f x)).effect b'))) = 1 - AgrG x := by
      have h := point_defect_eq (leftPlacedMeasurement (ιB := ιB) (A x))
        (rightPlacedMeasurement (ιA := ιA) (B.postprocess (f x))) ψ
      simp only [leftPlacedMeasurement, rightPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow]; congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect, heteroKron_finset_sum_right,
        stateQForm_finset_sum, Finset.sum_filter]
    rw [avgOver_congr _ _ _ hpt, avgOver_sub, avgOver_uniform_const]
  have hhyp : consistencyDefect (uniformDistribution (X × Y))
      (fun z r => heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
      (fun z r => heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ =
      1 - avgOver (uniformDistribution X) (fun x => avgOver (uniformDistribution Y) (AgrH x)) := by
    rw [consistencyDefect_placed_eq_avg_point (uniformDistribution (X × Y))
      (fun z => (A z.1).postprocess (e₁ z.1 z.2)) (fun z => B.postprocess (f₁ z.1 z.2))]
    have hpt (z : X × Y) : (∑ r, ∑ r', if r = r' then 0 else
        stateQForm ψ (heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r)
          ((B.postprocess (f₁ z.1 z.2)).effect r'))) = 1 - AgrH z.1 z.2 := by
      have h := point_defect_eq (leftPlacedMeasurement (ιB := ιB) ((A z.1).postprocess (e₁ z.1 z.2)))
        (rightPlacedMeasurement (ιA := ιA) (B.postprocess (f₁ z.1 z.2))) ψ
      simp only [leftPlacedMeasurement, rightPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow]; congr 1
      have hterm (r : R) : stateQForm ψ (heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r)
          ((B.postprocess (f₁ z.1 z.2)).effect r)) =
          ∑ b, ∑ g, if e₁ z.1 z.2 b = r ∧ f₁ z.1 z.2 g = r then w z.1 b g else 0 := by
        rw [MIPStarRE.Quantum.Measurement.postprocess_effect, MIPStarRE.Quantum.Measurement.postprocess_effect,
          heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : e₁ z.1 z.2 b = r
        · rw [if_pos hb, heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
          exact Finset.sum_congr rfl fun g _ => by by_cases hg : f₁ z.1 z.2 g = r <;> simp [hb, hg, w]
        · simp [hb]
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun g _ => ?_)
      by_cases hbg : e₁ z.1 z.2 b = f₁ z.1 z.2 g
      · simp [hbg]
      · refine (Finset.sum_eq_zero fun r _ => if_neg fun hp => hbg (hp.1.trans hp.2.symm)).trans ?_
        simp [hbg]
    rw [avgOver_congr _ _ _ hpt, avgOver_sub, avgOver_uniform_const, avgOver_uniform_prod (fun x y => AgrH x y)]
  rw [hgoal, hhyp]
  have hstep (x : X) : avgOver (uniformDistribution Y) (AgrH x) ≤ AgrG x + ∑ g, W g * F x g := by
    dsimp only [AgrH, AgrG]
    rw [avgOver_sum, Finset.sum_congr rfl fun b _ => avgOver_sum _ _]
    have htm (b : β) (g : Γ) : avgOver (uniformDistribution Y)
        (fun y => if e₁ x y b = f₁ x y g then w x b g else 0) ≤
        (if f x g = b then w x b g else 0) + w x b g * F x g := by
      refine (avgOver_mono _ _ (fun y => (if f x g = b then w x b g else 0) +
          (if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) * w x b g) fun y => ?_).trans ?_
      · by_cases hy : e₁ x y b = f₁ x y g
        · by_cases hb : f x g = b
          · simp [hy, hb]
          · simp [hy, hb]
        · rw [if_neg hy]
          have := hwnn x b g
          exact add_nonneg (by split_ifs <;> linarith) (mul_nonneg (by split_ifs <;> norm_num) this)
      · rw [avgOver_add, avgOver_uniform_const, avgOver_mul_const]
        linarith [mul_le_mul_of_nonneg_right (hFbound x b g) (hwnn x b g)]
    refine (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun g _ => htm b g).trans_eq ?_
    simp_rw [Finset.sum_add_distrib]
    congr 1; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => by rw [← Finset.sum_mul, hfib]
  have havg := (avgOver_mono (uniformDistribution X) _ _ hstep).trans_eq
    (avgOver_add (uniformDistribution X) _ _)
  have hfin : avgOver (uniformDistribution X) (fun x => ∑ g, W g * F x g) ≤ η := by
    rw [avgOver_sum, Finset.sum_congr rfl fun g _ => avgOver_const_mul _ _ _]
    exact (Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hFavg g) (hWnn g)).trans_eq
      (by rw [← Finset.sum_mul, hWsum, one_mul])
  linarith

def directCombinedPointEquiv (D : DirectLdParams) :
    ((Fin D.m → DirectScalarQ D) × (Fin D.k → DirectScalarQ D)) ≃
      (Fin D.combined.m → DirectScalarQ D) where
  toFun z := combinedPoint z.1 z.2
  invFun z := (combinedPointPart z, combinedCoefficientPart z)
  left_inv := fun ⟨_, _⟩ => by simp
  right_inv _ := by simp

set_option maxHeartbeats 800000 in
theorem directCombinedRecovery_relation_one (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (GB : DirectPolyMeasTuple D.combined S.ιB) :
    consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u o => heteroKron (((S.A (directLdPointQuestionOf D u)).postprocess
          (directLdPointValuesOrZero D)).effect o) 1)
        (fun u o => heteroKron 1
          (((GB.postprocess (directTupleOfCombinedTuple D)).postprocess (evalDirectPolyTupleAt u)).effect o))
        S.ψ ≤
      consistencyDefect (uniformDistribution (Fin D.combined.m → DirectScalarQ D))
          (fun z o => heteroKron ((((directCombinedStrategy D S).A
            (directLdPointQuestionOf D.combined z)).postprocess
              (directLdPointValuesOrZero D.combined)).effect o) 1)
          (fun z o => heteroKron 1
            ((GB.postprocess (evalDirectPolyTupleAt (D := D.combined) z)).effect o)) S.ψ +
        ((D.combined.m * D.d : ℕ) : ℝ) / D.q := by
  have hkey := consistencyDefect_le_of_recoveryBound
    (X := Fin D.m → DirectScalarQ D) (Y := Fin D.k → DirectScalarQ D)
    (fun u => (S.A (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D))
    GB S.ψ S.ψ_norm
    (fun u p => evalDirectPolyTupleAt u (directTupleOfCombinedTuple D p))
    (fun _ α b => fun _ : Fin D.combined.k => ∑ r, α r * b r)
    (fun u α p => evalDirectPolyTupleAt (D := D.combined) (combinedPoint u α) p)
    (fun u p => directCombinedRecoveryLocalBound D (p default) u)
    (((D.combined.m * D.d : ℕ) : ℝ) / D.q)
    (fun u b p => by
      refine (le_of_eq (avgOver_congr _ _ _ fun α => ?_)).trans
        (directCombinedRecoveryEvent_avg_le D (p default) u b)
      exact if_congr (and_congr Iff.rfl
        ⟨fun hh => (congrFun hh default).symm,
         fun hh => funext fun i => by rw [Unique.eq_default i]; exact hh.symm⟩) rfl rfl)
    (fun p => directCombinedRecoveryLocalBound_avg_le D (p default))
  have hmeas (u : Fin D.m → DirectScalarQ D) (α : Fin D.k → DirectScalarQ D) :
      ((directCombinedStrategy D S).A (directLdPointQuestionOf D.combined (combinedPoint u α))).postprocess
        (directLdPointValuesOrZero D.combined) =
      ((S.A (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D)).postprocess
        (fun b _ => ∑ r, α r * b r) := by
    show ((S.A _).postprocess _).postprocess _ = _
    rw [MIPStarRE.Quantum.Measurement.postprocess_comp, MIPStarRE.Quantum.Measurement.postprocess_comp]
    have hq : directCombinedMeasuredQuestion D (directLdPointQuestionOf D.combined (combinedPoint u α)) =
        directLdPointQuestionOf D u := by
      show directLdPointQuestionOf D (combinedPointPart (combinedPoint u α)) = _; simp
    rw [hq]; congr 1; funext a; cases a <;> funext _ <;> simp [directCombinedAnswerMap, directLdPointQuestionOf, directLdPointValuesOrZero]
  rw [consistencyDefect_congr _ _ _ _ _ S.ψ (fun _ _ => rfl)
    fun u a => by rw [MIPStarRE.Quantum.Measurement.postprocess_comp]]
  refine hkey.trans_eq (congrArg (· + ((D.combined.m * D.d : ℕ) : ℝ) / D.q) ?_)
  rw [← consistencyDefect_uniform_question_equiv (directCombinedPointEquiv D)
    (fun z o => heteroKron ((((directCombinedStrategy D S).A (directLdPointQuestionOf D.combined z)).postprocess
      (directLdPointValuesOrZero D.combined)).effect o) 1)
    (fun z o => heteroKron 1 ((GB.postprocess (evalDirectPolyTupleAt (D := D.combined) z)).effect o)) S.ψ]
  exact consistencyDefect_congr _ _ _ _ _ S.ψ
    (fun z r => congrArg (fun M => heteroKron (M.effect r) (1 : Op S.ιB)) (hmeas z.1 z.2).symm)
    (fun _ _ => rfl)

theorem directCombinedRecovery_relation_two (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (GA : DirectPolyMeasTuple D.combined S.ιA) :
    consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u o => heteroKron
          (((GA.postprocess (directTupleOfCombinedTuple D)).postprocess (evalDirectPolyTupleAt u)).effect o) 1)
        (fun u o => heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
          (directLdPointValuesOrZero D)).effect o)) S.ψ ≤
      consistencyDefect (uniformDistribution (Fin D.combined.m → DirectScalarQ D))
          (fun z o => heteroKron ((GA.postprocess (evalDirectPolyTupleAt (D := D.combined) z)).effect o) 1)
          (fun z o => heteroKron 1 ((((directCombinedStrategy D S).B
            (directLdPointQuestionOf D.combined z)).postprocess
              (directLdPointValuesOrZero D.combined)).effect o)) S.ψ +
        ((D.combined.m * D.d : ℕ) : ℝ) / D.q := by
  let Sswap : Strategy (directLdGame D) :=
    { ιA := S.ιB, ιB := S.ιA, ψ := reindexState (Equiv.prodComm S.ιA S.ιB) S.ψ,
      ψ_norm := (reindexState_norm_eq _ _).trans S.ψ_norm, A := S.B, B := S.A }
  have heq1 : consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u o => heteroKron
        (((GA.postprocess (directTupleOfCombinedTuple D)).postprocess (evalDirectPolyTupleAt u)).effect o) 1)
      (fun u o => heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect o)) S.ψ =
    consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
      (fun u o => heteroKron (((Sswap.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).effect o) 1)
      (fun u o => heteroKron 1
        (((GA.postprocess (directTupleOfCombinedTuple D)).postprocess (evalDirectPolyTupleAt u)).effect o))
      Sswap.ψ := (consistencyDefect_prodComm_heteroKron _ _ _ S.ψ).symm
  have heq2 : consistencyDefect (uniformDistribution (Fin D.combined.m → DirectScalarQ D))
      (fun z o => heteroKron ((((directCombinedStrategy D Sswap).A
        (directLdPointQuestionOf D.combined z)).postprocess
          (directLdPointValuesOrZero D.combined)).effect o) 1)
      (fun z o => heteroKron 1
        ((GA.postprocess (evalDirectPolyTupleAt (D := D.combined) z)).effect o)) Sswap.ψ =
    consistencyDefect (uniformDistribution (Fin D.combined.m → DirectScalarQ D))
      (fun z o => heteroKron ((GA.postprocess (evalDirectPolyTupleAt (D := D.combined) z)).effect o) 1)
      (fun z o => heteroKron 1 ((((directCombinedStrategy D S).B
        (directLdPointQuestionOf D.combined z)).postprocess
          (directLdPointValuesOrZero D.combined)).effect o)) S.ψ :=
    consistencyDefect_prodComm_heteroKron _ _ _ S.ψ
  linarith [directCombinedRecovery_relation_one D Sswap GA]

/-! ## Section 4: Scalar absorption, general-`k` soundness, any-strategy `k = 1` soundness, and coefficient collision -/

theorem exists_directCombinedTransportConstants :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
        Test.mainFormalError D.combined.toLDTParameters
              (directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) ≤
          deltaLd a b ε D.q D.m D.d D.k := by
  refine ⟨100000000000000000000000, 1 / 80000, by norm_num, by norm_num, by norm_num, fun D ε hε0 hε1 => ?_⟩
  have hm1 : (1 : ℝ) ≤ D.m := by exact_mod_cast D.hm
  have hd1 : (1 : ℝ) ≤ D.d := by exact_mod_cast D.hd
  have hk1 : (1 : ℝ) ≤ D.k := by exact_mod_cast D.hk
  have hq1 : (1 : ℝ) ≤ D.q := by exact_mod_cast D.toLDTParameters.hq
  have hM1 : (1 : ℝ) ≤ ((D.m + D.k : ℕ) : ℝ) := by exact_mod_cast D.hm.trans (Nat.le_add_right D.m D.k)
  have hN1 : (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hT := transportEnvelope_nonneg D hε0.le
  have hX := Real.rpow_nonneg hε0.le (1 / 80000 : ℝ)
  have hY := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ D.q) (-(1 / 80000) : ℝ)
  have hZ := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))
  have haux : (directLdAuxParameter D.combined : ℝ) = 2560000 * (((D.m + D.k : ℕ) : ℝ) ^ 3) * D.d := by
    unfold directLdAuxParameter; simp only [DirectLdParams.combined]; push_cast; ring
  have hexp_arg : (directLdAuxParameter D.combined : ℝ) /
      (2560000 * (((D.m + D.k : ℕ) : ℝ) ^ 2)) = ((D.m + D.k : ℕ) : ℝ) * D.d := by
    have hne : (2560000 : ℝ) * (((D.m + D.k : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
    rw [haux, div_eq_iff hne]; ring
  have ht1 : Real.rpow (3 * (10 * ε)) (1 / 40000) ≤ 30 * Real.rpow ε (1 / 80000) := by
    rw [show (3 : ℝ) * (10 * ε) = 30 * ε by ring]; simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by norm_num) hε0.le]
    exact mul_le_mul ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 30))
      (Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)) (Real.rpow_nonneg hε0.le _) (by norm_num)
  have ht2 : Real.rpow ((D.d : ℝ) / D.q) (1 / 40000) ≤ (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv, ← Real.rpow_neg (by linarith)]
    exact mul_le_mul ((Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)).trans_eq (Real.rpow_one _))
      (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)) (Real.rpow_nonneg (by linarith) _) (by linarith)
  have ht3 : Real.exp (-(((D.m + D.k : ℕ) : ℝ) * D.d)) ≤
      Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hMm : (D.m : ℝ) ≤ ((D.m + D.k : ℕ) : ℝ) := by push_cast; linarith
    rw [show ((D.m * D.d : ℕ) : ℝ) = (D.m : ℝ) * D.d by push_cast; ring]
    simp only [Real.rpow_eq_pow]; rw [Real.rpow_def_of_pos (by norm_num)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_right hMm (by positivity : (0 : ℝ) ≤ D.d),
      mul_le_mul_of_nonneg_right hlog (by positivity : (0 : ℝ) ≤ (D.m : ℝ) * D.d)]
  have hE : Test.mainFormalError D.combined.toLDTParameters (directLdAuxParameter D.combined) (3 * (10 * ε)) ≤
      19660800000000000000 * (((D.m + D.k : ℕ) : ℝ) ^ 10) * ((D.d : ℝ) ^ 3) * transportEnvelope D ε := by
    change 100000 * ((directLdAuxParameter D.combined : ℝ) ^ 2) * (((D.m + D.k : ℕ) : ℝ) ^ 4) * _ ≤ _
    have hsum : Real.rpow (3 * (10 * ε)) (1 / 40000) + Real.rpow ((D.d : ℝ) / D.q) (1 / 40000) +
        Real.exp (-((directLdAuxParameter D.combined : ℝ) / (2560000 * (((D.m + D.k : ℕ) : ℝ) ^ 2)))) ≤
        30 * (D.d : ℝ) * transportEnvelope D ε := by
      rw [hexp_arg]; unfold transportEnvelope
      simp only [Real.rpow_eq_pow] at ht1 ht2 ht3 ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hX, mul_nonneg (sub_nonneg.mpr hd1) hY,
        mul_nonneg (sub_nonneg.mpr hd1) hZ]
    have hp : 100000 * ((directLdAuxParameter D.combined : ℝ) ^ 2) * (((D.m + D.k : ℕ) : ℝ) ^ 4) =
        655360000000000000 * (((D.m + D.k : ℕ) : ℝ) ^ 10) * ((D.d : ℝ) ^ 2) := by rw [haux]; ring
    rw [hp]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)
  have hL : ((D.combined.m * D.d : ℕ) : ℝ) / D.q ≤
      ((D.m + D.k : ℕ) : ℝ) * D.d * transportEnvelope D ε := by
    have hinv : (D.q : ℝ)⁻¹ ≤ transportEnvelope D ε := by
      have hqb : Real.rpow (D.q : ℝ) (1 / 80000) ≤ D.q := by
        simp only [Real.rpow_eq_pow]
        exact (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)).trans_eq (Real.rpow_one _)
      have hi : (D.q : ℝ)⁻¹ ≤ Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
        simp only [Real.rpow_eq_pow] at hqb ⊢; rw [Real.rpow_neg (by linarith)]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hqb
      unfold transportEnvelope; simp only [Real.rpow_eq_pow] at hi ⊢; linarith
    rw [show ((D.combined.m * D.d : ℕ) : ℝ) = ((D.m + D.k : ℕ) : ℝ) * D.d by
      change (((D.m + D.k) * D.d : ℕ) : ℝ) = _; push_cast; ring, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hMN : ((D.m + D.k : ℕ) : ℝ) ≤ 2 * ((D.d * D.m * D.k : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hk1),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hd1) (by linarith : (0 : ℝ) ≤ D.m)) (by linarith : (0 : ℝ) ≤ D.k)]
  have hdN : (D.d : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    push_cast
    exact (le_mul_of_one_le_right (by positivity) hm1).trans (le_mul_of_one_le_right (by positivity) hk1)
  have hpoly : ((D.m + D.k : ℕ) : ℝ) ^ 10 * (D.d : ℝ) ^ 3 ≤ 1024 * ((D.d * D.m * D.k : ℕ) : ℝ) ^ 13 := by
    calc ((D.m + D.k : ℕ) : ℝ) ^ 10 * (D.d : ℝ) ^ 3
        ≤ (2 * ((D.d * D.m * D.k : ℕ) : ℝ)) ^ 10 * ((D.d * D.m * D.k : ℕ) : ℝ) ^ 3 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hMN 10) (pow_le_pow_left₀ (by positivity) hdN 3)
            (by positivity) (by positivity)
      _ = _ := by ring
  have hMdle : ((D.m + D.k : ℕ) : ℝ) * D.d ≤ ((D.m + D.k : ℕ) : ℝ) ^ 10 * (D.d : ℝ) ^ 3 :=
    mul_le_mul (by simpa using pow_le_pow_right₀ hM1 (by norm_num : 1 ≤ 10))
      (by simpa using pow_le_pow_right₀ hd1 (by norm_num : 1 ≤ 3)) (by linarith) (by positivity)
  have hN13 : ((D.d * D.m * D.k : ℕ) : ℝ) ^ (13 : ℕ) ≤
      Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) 100000000000000000000000 := by
    simp only [Real.rpow_eq_pow]; rw [← Real.rpow_natCast _ 13]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; norm_num)
  have hR0 := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ)) 100000000000000000000000
  change _ ≤ 100000000000000000000000 *
    Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) 100000000000000000000000 * transportEnvelope D ε
  simp only [Real.rpow_eq_pow] at hN13 ⊢
  linarith [mul_le_mul_of_nonneg_right hMdle hT, mul_le_mul_of_nonneg_right hpoly hT,
    mul_le_mul_of_nonneg_right hN13 hT, mul_nonneg hR0 hT]

theorem exists_direct_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u o => heteroKron (((S.A (directLdPointQuestionOf D u)).postprocess
                    (directLdPointValuesOrZero D)).effect o) 1)
                  (fun u o => heteroKron 1 ((GB.postprocess (evalDirectPolyTupleAt u)).effect o))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u o => heteroKron ((GA.postprocess (evalDirectPolyTupleAt u)).effect o) 1)
                  (fun u o => heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
                    (directLdPointValuesOrZero D)).effect o))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k := by
  obtain ⟨a, b, ha, hb0, hb1, habs⟩ := exists_directCombinedTransportConstants
  refine ⟨a, b, ha, hb0, hb1, fun D ε hε S hS hwin => ?_⟩
  obtain ⟨GA, GB, h1, h2, h3⟩ := exists_directSimultaneousPolynomialMeasurements_of_k_eq_one
    D.combined rfl (directCombinedStrategy D S) (directCombinedStrategy_isProjective D S hS)
    (10 * ε) (directCombinedStrategy_value_ge D S ε hwin)
  refine ⟨GA.postprocess (directTupleOfCombinedTuple D),
    GB.postprocess (directTupleOfCombinedTuple D), ?_, ?_, ?_⟩
  · by_cases hε1 : ε ≤ 1
    · exact (directCombinedRecovery_relation_one D S GB).trans ((add_le_add h1 le_rfl).trans (habs D ε hε hε1))
    · exact (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _ S.ψ S.ψ_norm).trans
        (one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)
  · by_cases hε1 : ε ≤ 1
    · exact (directCombinedRecovery_relation_two D S GA).trans ((add_le_add h2 le_rfl).trans (habs D ε hε hε1))
    · exact (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _ S.ψ S.ψ_norm).trans
        (one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)
  · by_cases hε1 : ε ≤ 1
    · refine (consistencyDefect_postprocess_le (uniformDistribution Unit) (fun _ => GA) (fun _ => GB) S.ψ
        (directTupleOfCombinedTuple D)).trans (h3.trans (le_trans ?_ (habs D ε hε hε1)))
      have : (0 : ℝ) ≤ ((D.combined.m * D.d : ℕ) : ℝ) / D.q := by positivity
      linarith
    · exact (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _ S.ψ S.ψ_norm).trans
        (one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)

theorem le_sqrt_of_le_of_le_one {x T : ℝ} (hxT : x ≤ T) (hT : T ≤ 1) : x ≤ Real.sqrt T := by
  rcases le_or_gt x 0 with hx | hx
  · exact hx.trans (Real.sqrt_nonneg T)
  · exact (Real.sqrt_sq hx.le).symm.trans_le (Real.sqrt_le_sqrt (by nlinarith))

theorem direct_ld_soundness_of_k_eq_one_any_strategy_explicit :
    ∀ (D : DirectLdParams) (ε : ℝ), D.k = 1 → 0 < ε →
        ∀ S : Strategy (directLdGame D), 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u o => heteroKron (((S.A (directLdPointQuestionOf D u)).postprocess
                    (directLdPointValuesOrZero D)).effect o) 1)
                  (fun u o => heteroKron 1 ((GB.postprocess (evalDirectPolyTupleAt u)).effect o))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u o => heteroKron ((GA.postprocess (evalDirectPolyTupleAt u)).effect o) 1)
                  (fun u o => heteroKron 1 (((S.B (directLdPointQuestionOf D u)).postprocess
                    (directLdPointValuesOrZero D)).effect o))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k := by
  let a := pauliBaselineLowDegreeConstant
  let b := pauliBaselineLowDegreePower
  obtain ⟨ha₀, hb₀, _, habs₀⟩ := direct_ld_transport_constants_explicit 1 le_rfl
  have ha : 1 ≤ a := by simpa only [a, pauliBaselineLowDegreeConstant, mul_one] using ha₀
  have hb : 0 < b := by simpa only [b, pauliBaselineLowDegreePower] using hb₀
  have habs : ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
      (D.k : ℝ) * Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * D.d) / D.q + ε) ≤ deltaLd a b ε D.q D.m D.d D.k := by
    simpa only [a, b, pauliBaselineLowDegreeConstant, pauliBaselineLowDegreePower, mul_one, one_mul] using habs₀
  intro D ε hk hε S hwin
  let SN : Strategy (directLdGame D) :=
    paddedStrategy S (none : Option (DirectLdAnswer D)) (none : Option (DirectLdAnswer D))
      (fun q => dilatedMeasurement (default : DirectLdAnswer D) (S.A q))
      (fun q => dilatedMeasurement (default : DirectLdAnswer D) (S.B q))
  have hSNp : SN.IsProjective := paddedStrategy_isProjective S none none _ _
    (fun q => dilatedMeasurement_isProjective default (S.A q))
    (fun q => dilatedMeasurement_isProjective default (S.B q))
  have hSNv : 1 - ε ≤ SN.value := by
    rwa [paddedStrategy_value S none none _ _
      (fun q ans => dilatedMeasurement_compression default ans (S.A q))
      (fun q ans => dilatedMeasurement_compression default ans (S.B q))]
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_of_k_eq_one D hk SN hSNp ε hSNv
  have habsorb {X α : Type} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
      (μ : Distribution X) (hμ : μ.IsProbability)
      (MA : X → Quantum.Measurement α SN.ιA) (MB : X → Quantum.Measurement α SN.ιB)
      (hm : consistencyDefect μ (fun x c => heteroKron ((MA x).effect c) 1)
        (fun x c => heteroKron 1 ((MB x).effect c)) SN.ψ ≤
        Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)) :
      consistencyDefect μ (fun x c => heteroKron ((MA x).effect c) 1)
        (fun x c => heteroKron 1 ((MB x).effect c)) SN.ψ ≤ deltaLd a b ε D.q D.m D.d D.k := by
    have hle1 := consistencyDefect_heteroKron_le_one μ hμ MA MB SN.ψ SN.ψ_norm
    rcases le_or_gt ε 1 with hε1 | hε1
    · have hk1 : (1 : ℝ) ≤ D.k := by exact_mod_cast D.hk
      have hmd : (0 : ℝ) ≤ ((D.m : ℝ) * D.d) / D.q := by positivity
      let T := Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * D.d) / D.q + ε
      have hsq : consistencyDefect μ (fun x c => heteroKron ((MA x).effect c) 1)
          (fun x c => heteroKron 1 ((MB x).effect c)) SN.ψ ≤ Real.sqrt T := by
        rcases le_or_gt T 1 with hT1 | hT1
        · exact le_sqrt_of_le_of_le_one (by dsimp [T]; linarith) hT1
        · exact hle1.trans (Real.sqrt_one.symm.trans_le (Real.sqrt_le_sqrt hT1.le))
      exact hsq.trans ((le_mul_of_one_le_left (Real.sqrt_nonneg T) hk1).trans (habs D ε hε hε1))
    · exact hle1.trans (one_le_deltaLd_of_one_le_error ha hb.le hε1.le D.hm D.hd D.hk)
  let GA0 : DirectPolyMeasTuple D S.ιA := GA.compressAt (none : Option (DirectLdAnswer D))
  let GB0 : DirectPolyMeasTuple D S.ιB := GB.compressAt (none : Option (DirectLdAnswer D))
  refine ⟨GA0, GB0, ?_, ?_, ?_⟩
  · have hc (u) : (((SN.A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).compressAt none) =
        (S.A (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D) := by
      change ((dilatedMeasurement default _).postprocess _).compressAt none = _
      rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
        MIPStarRE.QPBT.Measurement.compressAt_dilatedMeasurement]
    refine (le_of_eq ?_).trans (habsorb _ (uniformDistribution_isProbability _) _ _ h1)
    exact (consistencyDefect_congr _ _ _ _ _ S.ψ
      (fun u o => by rw [← hc u])
      (fun u o => by dsimp only [GB0]; rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess])).trans
      (consistencyDefect_padState_compressAt _ _ _ none none S.ψ).symm
  · have hc (u) : (((SN.B (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D)).compressAt none) =
        (S.B (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D) := by
      change ((dilatedMeasurement default _).postprocess _).compressAt none = _
      rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess,
        MIPStarRE.QPBT.Measurement.compressAt_dilatedMeasurement]
    refine (le_of_eq ?_).trans (habsorb _ (uniformDistribution_isProbability _) _ _ h2)
    exact (consistencyDefect_congr _ _ _ _ _ S.ψ
      (fun u o => by dsimp only [GA0]; rw [MIPStarRE.Quantum.Measurement.compressAt_postprocess])
      (fun u o => by rw [← hc u])).trans
      (consistencyDefect_padState_compressAt _ _ _ none none S.ψ).symm
  · refine (le_of_eq ?_).trans (habsorb _ (uniformDistribution_isProbability Unit) _ _ h3)
    exact (consistencyDefect_padState_compressAt (uniformDistribution Unit)
      (fun _ => GA) (fun _ => GB) none none S.ψ).symm

theorem consistencyDefect_directCoefficients_le_evaluated_add
    {X ιA ιB : Type*} [Fintype X] [DecidableEq X]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : DirectLdParams) (degree : ℕ) (μ : Distribution X)
    (A : X → MIPStarRE.Quantum.Measurement (DirectDegPoly D degree) ιA)
    (B : X → MIPStarRE.Quantum.Measurement (DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ
        (fun x c => heteroKron ((A x).effect c) 1)
        (fun x c => heteroKron 1 ((B x).effect c)) ψ ≤
      consistencyDefect (Distribution.prod μ (uniformDistribution (DirectScalarQ D)))
        (fun xt v => heteroKron (((A xt.1).postprocess fun c => evalCoefficient c xt.2).effect v) 1)
        (fun xt v => heteroKron 1 (((B xt.1).postprocess fun c => evalCoefficient c xt.2).effect v)) ψ +
        (degree : ℝ) / (D.q : ℝ) := by
  refine consistencyDefect_codewords_le_evaluated_add μ A B ψ evalCoefficient
    ((degree : ℝ) / D.q) hμ hψ (by positivity) fun a b hne => ?_
  have hc := evalCoefficient_collision_card_le a b hne
  simp only [avgOver, uniformDistribution, Distribution.uniformOnFinset_support,
    Distribution.uniformOnFinset_weight, Finset.mem_univ, ↓reduceIte, Finset.card_univ,
    card_directScalarQ, mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, one_div]
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

theorem extendedDirectLd_coefficientCollisionLoss_le_five_mul (P : AdmissibleParams) :
    ((P.extendedDirectLd.d : ℝ) + (P.extendedDirectLd.m * P.extendedDirectLd.d : ℝ)) /
        (P.extendedDirectLd.q : ℝ) ≤
      5 * ((P.m * P.d : ℝ) / (P.q : ℝ)) := by
  have hm : (1 : ℝ) ≤ P.m := by exact_mod_cast P.one_le_m
  have hq : (0 : ℝ) < P.q := by
    obtain ⟨k, _, hk⟩ := P.hq; rw [hk]; exact_mod_cast Nat.pow_pos (a := 2) (n := k) (by decide)
  change ((P.d : ℝ) + ((2 * P.m + 2 : ℕ) : ℝ) * P.d) / P.q ≤ 5 * ((P.m : ℝ) * P.d / P.q)
  push_cast
  rw [show 5 * ((P.m : ℝ) * P.d / P.q) = (5 * ((P.m : ℝ) * P.d)) / P.q by ring]
  exact (div_le_div_iff_of_pos_right hq).mpr (by nlinarith [show (0 : ℝ) ≤ P.d by positivity])

end

end MIPStarRE.QPBT
