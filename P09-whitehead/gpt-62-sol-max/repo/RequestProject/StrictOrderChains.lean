module

public import RequestProject.StrictOrderComplex
public import RequestProject.FinsuppBasis
public import RequestProject.CombHurewicz1Pres

@[expose] public section

/-! Integral cellular normalization of weak order chains, without finite cell assumptions. -/

set_option backward.isDefEq.respectTransparency false

namespace Finsupp

/-- Coordinate restriction from a subtype to a smaller subtype. -/
noncomputable def restrictSubtype {A : Type*} {S T : A → Prop} (h : ∀ ⦃a⦄, S a → T a) :
    ({a // T a} →₀ ℤ) →ₗ[ℤ] ({a // S a} →₀ ℤ) :=
  lcomapDomain (fun a => (⟨a.1, h a.2⟩ : {a // T a}))
    (fun _ _ e => Subtype.ext (congrArg (fun x : {a // T a} => x.1) e))

open scoped Classical in
theorem restrictSubtype_single {A : Type*} {S T : A → Prop} (h : ∀ ⦃a⦄, S a → T a)
    (a : {a // T a}) (n : ℤ) : restrictSubtype h (single a n) =
      if hs : S a.1 then single ⟨a.1, hs⟩ n else 0 := by
  by_cases ha : S a.1
  · rw [dif_pos ha]
    exact comapDomain_single (fun b : {a // S a} => (⟨b.1, h b.2⟩ : {a // T a})) ⟨a.1, ha⟩ n _
  · rw [dif_neg ha]
    exact comapDomain_single_of_not_mem_range (f := fun b : {a // S a} => (⟨b.1, h b.2⟩ : {a // T a}))
      (fun ⟨b, hb⟩ => ha ((congrArg Subtype.val hb) ▸ b.2)) _ _

end Finsupp

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

noncomputable def normalizeOrdEdge (e : OrdEdge P) : StrictOrdEdge P →₀ ℤ := by
  classical
  exact if h : e.1.1 = e.1.2 then 0 else
    Finsupp.single ⟨e.1, lt_of_le_of_ne e.2 h⟩ 1

noncomputable def normalizeOrdChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdEdge P →₀ ℤ) :=
  Finsupp.restrictSubtype (fun _ h => h.le)

noncomputable def normalizeOrdTriangle (t : OrdTri P) : StrictOrdTri P →₀ ℤ := by
  classical
  exact if h : t.1.1 < t.1.2.1 ∧ t.1.2.1 < t.1.2.2 then
    Finsupp.single ⟨t.1, h⟩ 1 else 0

noncomputable def normalizeOrdChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTri P →₀ ℤ) :=
  Finsupp.restrictSubtype (fun _ h => ⟨h.1.le, h.2.le⟩)

@[simp] theorem normalizeOrdChain1_single (e : OrdEdge P) (n : ℤ) :
    normalizeOrdChain1 (Finsupp.single e n) = n • normalizeOrdEdge e := by
  classical
  erw [normalizeOrdChain1, Finsupp.restrictSubtype_single]
  by_cases h : e.1.1 = e.1.2
  · simp [normalizeOrdEdge, h]
  · simp [normalizeOrdEdge, h, lt_of_le_of_ne e.2 h]

@[simp] theorem normalizeOrdChain2_single (t : OrdTri P) (n : ℤ) :
    normalizeOrdChain2 (Finsupp.single t n) = n • normalizeOrdTriangle t := by
  classical
  erw [normalizeOrdChain2, Finsupp.restrictSubtype_single]
  unfold normalizeOrdTriangle
  split <;> simp_all

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

theorem bdry1_normalizeOrdEdge (e : OrdEdge P) :
    bdry1 (strictOrderCx P) (normalizeOrdEdge e) =
      Finsupp.single e.1.2 1 - Finsupp.single e.1.1 1 := by
  classical
  by_cases h : e.1.1 = e.1.2
  · simp [normalizeOrdEdge, h]
  · simp [normalizeOrdEdge, h, strictOrderCx, bdry1]

/-- Normalization commutes with the first cellular boundary. -/
theorem bdry1_normalizeOrdChain1 (c : OrdEdge P →₀ ℤ) :
    bdry1 (strictOrderCx P) (normalizeOrdChain1 c) = bdry1 (orderCx P) c := by
  finsupp_basis c
  intro e
  rw [normalizeOrdChain1_single, map_smul, bdry1_normalizeOrdEdge, bdry1_single]
  rfl

/-- Degenerate triangles normalize to zero; genuine triangles retain their boundary. -/
theorem bdry2_normalizeOrdTriangle (t : OrdTri P) :
    bdry2 (strictOrderCx P) (normalizeOrdTriangle t) =
      pathChain (normalizeOrdPath ((orderCx P).att t)) := by
  classical
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  by_cases heab : a = b
  · subst b
    by_cases hac : a = c <;> simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx,
      pathChain, bdry2, Finsupp.linearCombination_apply, strictOrderCx, hac]
  · by_cases hebc : b = c
    · subst c
      simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx,
        pathChain, bdry2, Finsupp.linearCombination_apply, strictOrderCx, heab]
    · have hab'  := lt_of_le_of_ne hab heab
      have hbc'  := lt_of_le_of_ne hbc hebc
      simp [normalizeOrdTriangle, normalizeOrdPath, normalizeOrdGerm, orderCx,
        pathChain, bdry2, Finsupp.linearCombination_apply, strictOrderCx, bdry2, hab', hbc', hab'.ne, hbc'.ne, (hab'.trans hbc').ne]

/-- Normalization commutes with the second cellular boundary. -/
theorem bdry2_normalizeOrdChain2 (c : OrdTri P →₀ ℤ) :
    bdry2 (strictOrderCx P) (normalizeOrdChain2 c) =
      normalizeOrdChain1 (bdry2 (orderCx P) c) := by
  finsupp_basis c
  intro t
  rw [normalizeOrdChain2_single, map_smul, bdry2_normalizeOrdTriangle,
    bdry2_single, map_smul, normalizeOrdChain1_pathChain]

/-- Normalization is a retraction of the inclusion on one-chains. -/
theorem normalizeOrdChain1_inclusion (c : StrictOrdEdge P →₀ ℤ) :
    normalizeOrdChain1 (Finsupp.mapDomain (strictOrderIncl P).onE c) = c :=
  Finsupp.leftInverse_lcomapDomain_mapDomain (strictOrderIncl P).onE
    (fun _ _ h => Subtype.ext (congrArg (fun e : OrdEdge P => e.1) h)) c

/-- Normalization is a retraction of the inclusion on two-chains. -/
theorem normalizeOrdChain2_inclusion (c : StrictOrdTri P →₀ ℤ) :
    normalizeOrdChain2 (Finsupp.mapDomain (strictOrderIncl P).onF c) = c :=
  Finsupp.leftInverse_lcomapDomain_mapDomain (strictOrderIncl P).onF
    (fun _ _ h => Subtype.ext (congrArg (fun t : OrdTri P => t.1) h)) c

/-- Every weak cellular two-cycle has a normalized strict cellular two-cycle. -/
theorem normalizeOrdChain2_cycle (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    bdry2 (strictOrderCx P) (normalizeOrdChain2 c) = 0 := by
  rw [bdry2_normalizeOrdChain2, hc, map_zero]

end FiniteChains.Comb
