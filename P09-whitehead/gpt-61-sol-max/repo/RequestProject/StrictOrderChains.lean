import Mathlib.Tactic

import RequestProject.StrictOrderComplex
import RequestProject.CombHurewicz1Pres

/-! Integral cellular normalization of weak order chains, without finite cell assumptions. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P]

  (e : OrdEdge P)
noncomputable def normalizeOrdEdge  : StrictOrdEdge P →₀ ℤ := by
  classical
  exact if h : e.1.1 = e.1.2 then 0 else
    Finsupp.single ⟨e.1, lt_of_le_of_ne e.2 h⟩ 1

noncomputable def normalizeOrdChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdEdge P →₀ ℤ) :=
  Finsupp.linearCombination ℤ normalizeOrdEdge

variable (t : OrdTri P)
noncomputable def normalizeOrdTriangle  : StrictOrdTri P →₀ ℤ := by
  classical
  exact if h : t.1.1 < t.1.2.1 ∧ t.1.2.1 < t.1.2.2 then
    Finsupp.single ⟨t.1, h⟩ 1 else 0

noncomputable def normalizeOrdChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ normalizeOrdTriangle

@[simp] theorem normalizeOrdChain1_single  (n : ℤ) :
    normalizeOrdChain1 (Finsupp.single e n) = n • normalizeOrdEdge e := by
  simp [normalizeOrdChain1]

@[simp] theorem normalizeOrdChain2_single  (n : ℤ) :
    normalizeOrdChain2 (Finsupp.single t n) = n • normalizeOrdTriangle t := by
  simp [normalizeOrdChain2]

theorem normalizeOrdChain1_pathChain (p : List ((orderCx P).E × Bool)) :
    normalizeOrdChain1 (pathChain p) = pathChain (normalizeOrdPath p) := by
  classical
  induction p with
  | nil => simp [normalizeOrdPath]
  | cons e p ih =>
    rw [pathChain_cons, map_add, ih]
    change _ = pathChain (normalizeOrdGerm e ++ normalizeOrdPath p)
    rw [pathChain_append]
    congr 1
    rcases e with ⟨e, b⟩
    cases b <;> by_cases h : e.1.1 = e.1.2 <;>
      simp [normalizeOrdGerm, normalizeOrdEdge, h, pathChain, map_neg]

theorem bdry1_normalizeOrdEdge  :
    bdry1 (strictOrderCx P) (normalizeOrdEdge e) =
      Finsupp.single e.1.2 1 - Finsupp.single e.1.1 1 := by
  aesop (add simp [normalizeOrdEdge, bdry1])

/-- Normalization commutes with the first cellular boundary. -/
theorem bdry1_normalizeOrdChain1 (c : OrdEdge P →₀ ℤ) :
    bdry1 (strictOrderCx P) (normalizeOrdChain1 c) = bdry1 (orderCx P) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [*]
  | single e n =>
    rw [normalizeOrdChain1_single, map_smul, bdry1_normalizeOrdEdge, bdry1_single]
    rfl

/-- Degenerate triangles normalize to zero; genuine triangles retain their boundary. -/
theorem bdry2_normalizeOrdTriangle  :
    bdry2 (strictOrderCx P) (normalizeOrdTriangle t) =
      pathChain (normalizeOrdPath ((orderCx P).att t)) := by
  classical
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  by_cases heab : a = b
  · aesop (add simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx, pathChain])
  · by_cases hebc : b = c
    · simp_all [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx, pathChain, bdry2, Finsupp.linearCombination_apply]
    · have hab'  := lt_of_le_of_ne hab heab
      have hbc'  := lt_of_le_of_ne hbc hebc
      simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx,
        pathChain, bdry2, Finsupp.linearCombination_apply, strictOrderCx, bdry2, hab', hbc', hab'.ne, hbc'.ne, (hab'.trans hbc').ne]

variable (c : OrdTri P →₀ ℤ)
/-- Normalization commutes with the second cellular boundary. -/
theorem bdry2_normalizeOrdChain2  :
    bdry2 (strictOrderCx P) (normalizeOrdChain2 c) =
      normalizeOrdChain1 (bdry2 (orderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [*]
  | single t n =>
    rw [normalizeOrdChain2_single, map_smul, bdry2_normalizeOrdTriangle,
      bdry2_single, map_smul, normalizeOrdChain1_pathChain]

/-- Normalization is a retraction of the inclusion on one-chains. -/
theorem normalizeOrdChain1_inclusion (c : StrictOrdEdge P →₀ ℤ) :
    normalizeOrdChain1 (Finsupp.mapDomain (strictOrderIncl P).onE c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add]
  | single e n =>
    simp [normalizeOrdEdge, strictOrderIncl, e.2.ne]

/-- Normalization is a retraction of the inclusion on two-chains. -/
theorem normalizeOrdChain2_inclusion (c : StrictOrdTri P →₀ ℤ) :
    normalizeOrdChain2 (Finsupp.mapDomain (strictOrderIncl P).onF c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add]
  | single t n =>
    simp [normalizeOrdTriangle, strictOrderIncl, t.2.1, t.2.2]

/-- Every weak cellular two-cycle has a normalized strict cellular two-cycle. -/
theorem normalizeOrdChain2_cycle 
    (hc : bdry2 (orderCx P) c = 0) :
    bdry2 (strictOrderCx P) (normalizeOrdChain2 c) = 0 := by simp_all [bdry2_normalizeOrdChain2]

end FiniteChains.Comb
