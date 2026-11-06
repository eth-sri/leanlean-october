import RequestProject.CmpNerve
import RequestProject.OrderNormalizationNaturality
import RequestProject.Tac


/-! Explicit finite barycentric subdivision in degrees one and two.
Proof terms only; not compiled under the current workflow. -/

noncomputable section
open scoped Classical

bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Image of a finite nonempty chain under a monotone map. Repeated images
are removed from the simplex, without discarding their chain coefficients. -/
def barycentricMap (f : P → Q) (hf : Monotone f) (σ : NeSpx (cmpRel P)) :
    NeSpx (cmpRel Q) :=
  ⟨σ.1.image f, σ.2.1.image f, by
    apply isSimplex_cmpRel_iff.mpr
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact ((isSimplex_cmpRel_iff.mp σ.2.2) x hx y hy).imp (by aesop) (by aesop)⟩

theorem barycentricMap_monotone (f : P → Q) hf :
    Monotone (barycentricMap f hf) := fun _ _ h => Finset.image_mono f h

@[simp] theorem barycentricMap_spx1 (f : P → Q) hf a :
    barycentricMap f hf (spx1 a) = spx1 (f a) := by
  rfl

@[simp] theorem barycentricMap_spx2 (f : P → Q) hf
    {a b} (hab : a ≤ b) :
    barycentricMap f hf (spx2 hab) = spx2 (hf hab) := by
  apply Subtype.ext
  simp [barycentricMap, spx2]

@[simp] theorem chainMax_barycentricMap (f : P → Q) hf
    σ :
    chainMax (barycentricMap f hf σ) = f (chainMax σ) := by
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp (chainMax_mem (barycentricMap f hf σ))
    rw [← he]
    exact hf (le_chainMax σ hx)
  · exact le_chainMax _
      (Finset.mem_image.mpr ⟨chainMax σ, chainMax_mem σ, rfl⟩)

def spx3 {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) : NeSpx (cmpRel P) :=
  ⟨{a, b, c}, by simp, by
    apply isSimplex_cmpRel_iff.mpr
    grind⟩

theorem spx2_le_spx3_left {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 hab ≤ spx3 hab hbc := by
  intro x hx
  grind [spx2_val, Finset.mem_insert, Finset.mem_singleton, spx3]

theorem spx2_le_spx3_outer {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 (hab.trans hbc) ≤ spx3 hab hbc := by
  intro x hx
  grind [spx2_val, Finset.mem_insert, Finset.mem_singleton, spx3]

theorem spx2_le_spx3_right {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    spx2 hbc ≤ spx3 hab hbc := by
  intro x hx
  simp_all [spx2_val, Finset.mem_insert, Finset.mem_singleton, spx3]

@[simp] theorem chainMax_spx3 {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) :
    chainMax (spx3 hab hbc) = c := by
  apply le_antisymm
  · have h := chainMax_mem (spx3 hab hbc)
    grind [spx3, Finset.mem_insert, Finset.mem_singleton]
  · exact le_chainMax _ (by simp [spx3])

@[simp] theorem barycentricMap_spx3 (f : P → Q) hf
    {a b c} (hab : a ≤ b) (hbc : b ≤ c) :
    barycentricMap f hf (spx3 hab hbc) = spx3 (hf hab) (hf hbc) := by
  apply Subtype.ext
  simp [barycentricMap, spx3]

def barycentricFlag x (e t : NeSpx (cmpRel P))
    (hxe : spx1 x ≤ e) (het : e ≤ t) : OrdTri (NeSpx (cmpRel P)) :=
  ⟨(spx1 x, e, t), hxe, het⟩

def barycentricEdge (e : OrdEdge P) : OrdEdge (NeSpx (cmpRel P)) →₀ ℤ :=
  Finsupp.single ⟨(spx1 e.1.1, spx2 e.2), spx1_le_spx2_left e.2⟩ 1 -
    Finsupp.single ⟨(spx1 e.1.2, spx2 e.2), spx1_le_spx2_right e.2⟩ 1

def barycentricTriangle (t : OrdTri P) : OrdTri (NeSpx (cmpRel P)) →₀ ℤ :=
  Finsupp.single (barycentricFlag t.1.2.1 _ _
    (spx1_le_spx2_left t.2.2) (spx2_le_spx3_right t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.2.2 _ _
    (spx1_le_spx2_right t.2.2) (spx2_le_spx3_right t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.1 _ _
    (spx1_le_spx2_left _) (spx2_le_spx3_outer t.2.1 t.2.2)) 1 +
  Finsupp.single (barycentricFlag t.1.2.2 _ _
    (spx1_le_spx2_right _) (spx2_le_spx3_outer t.2.1 t.2.2)) 1 +
  Finsupp.single (barycentricFlag t.1.1 _ _
    (spx1_le_spx2_left _) (spx2_le_spx3_left t.2.1 t.2.2)) 1 -
  Finsupp.single (barycentricFlag t.1.2.1 _ _
    (spx1_le_spx2_right _) (spx2_le_spx3_left t.2.1 t.2.2)) 1

def barycentricChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ] (OrdEdge (NeSpx (cmpRel P)) →₀ ℤ) :=
  Finsupp.linearCombination ℤ barycentricEdge

def barycentricChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ] (OrdTri (NeSpx (cmpRel P)) →₀ ℤ) :=
  Finsupp.linearCombination ℤ barycentricTriangle

theorem barycentricTriangle_boundary t :
    Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricTriangle t) =
      barycentricChain1 (Comb.bdry2 (orderCx P) (Finsupp.single t 1)) := by
  simp [barycentricTriangle, map_add, map_sub, map_smul, Comb.bdry2_single, one_smul]
  simp [barycentricTriangle, barycentricFlag, barycentricChain1,
    barycentricEdge, Comb.bdry2, orderCx, pathChain]
  abel

theorem barycentricChain2_boundary c :
    Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricChain2 c) =
      barycentricChain1 (Comb.bdry2 (orderCx P) c) := by
  lin_ind c t n =>
    rw [← Finsupp.smul_single_one t n, map_smul, map_smul, map_smul, map_smul]
    congr 1
    simpa only [barycentricChain2, Finsupp.linearCombination_single, one_smul] using
      barycentricTriangle_boundary t

theorem barycentric_mapDomain_sub {I J : Type u} (f : I → J) (x y : I →₀ ℤ) :
    Finsupp.mapDomain f (x - y) = Finsupp.mapDomain f x - Finsupp.mapDomain f y :=
  (Finsupp.mapDomain.addMonoidHom f).map_sub x y

theorem barycentricChain2_natural (f : P → Q) hf c :
    chain2 (orderCxMap (barycentricMap f hf) (barycentricMap_monotone f hf))
      (barycentricChain2 c) = barycentricChain2 (chain2 (orderCxMap f hf) c) := by
  lin_ind c with c d hc hd => simp [map_add, hc, hd]
  | t n =>
    simp [barycentricChain2, barycentricTriangle, barycentricFlag, chain2,
      orderCxMap, barycentric_mapDomain_sub, Finsupp.mapDomain_add,
      barycentricMap_spx1, barycentricMap_spx2, barycentricMap_spx3]

/-- Degenerate weak triangles have zero subdivision, so no artificial
diagonal cell survives the reverse map. -/
theorem barycentricTriangle_degenerate (t : OrdTri P)
    (ht : t.1.1 = t.1.2.1 ∨ t.1.2.1 = t.1.2.2) : barycentricTriangle t = 0 := by
  rcases ht with h | h
  · simp_all [barycentricTriangle, barycentricFlag, spx1, spx2, spx3]
  · simp_all [barycentricTriangle, barycentricFlag, spx1, spx2, spx3]

theorem barycentricChain2_normalization (c : OrdTri P →₀ ℤ) :
    barycentricChain2 c = barycentricChain2 (ordStrictInclusion2 (normalizeOrdChain2 c)) := by
  lin_ind c t n =>
    by_cases hab : t.1.1 = t.1.2.1
    · simp [barycentricChain2, barycentricTriangle_degenerate t (Or.inl hab),
        normalizeOrdChain2_single, normalizeOrdTriangle, hab]
    · by_cases hbc : t.1.2.1 = t.1.2.2
      · simp [barycentricChain2, barycentricTriangle_degenerate t (Or.inr hbc),
          normalizeOrdChain2_single, normalizeOrdTriangle, hbc]
      · have h1 := lt_of_le_of_ne t.2.1 hab
        have h2 := lt_of_le_of_ne t.2.2 hbc
        simp [normalizeOrdChain2_single, normalizeOrdTriangle, h1, h2,
          ordStrictInclusion2, strictOrderIncl]

/-- The last-vertex map recovers the original strict triangle with coefficient
one; the other five flags collapse and have zero normalized coefficient. -/
theorem barycentricChain2_lastVertex c :
    normalizeOrdChain2 (chain2 (orderCxMap (chainMax (P := P)) chainMax_monotone)
      (barycentricChain2 c)) = normalizeOrdChain2 c := by
  lin_ind c with c d hc hd => simp only [map_add, hc, hd]
  | t n =>
    simp [barycentricChain2, barycentricTriangle, barycentricFlag, chain2,
      orderCxMap, barycentric_mapDomain_sub, Finsupp.mapDomain_add,
      normalizeOrdChain2, normalizeOrdTriangle]
