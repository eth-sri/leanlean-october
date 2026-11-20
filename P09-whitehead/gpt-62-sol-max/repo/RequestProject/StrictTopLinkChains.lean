module

public import RequestProject.StrictTriangleBoundary
public import RequestProject.FinsuppBasis

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictBelow (v : P) := {p : P // p < v}

instance (v : P) : PartialOrder (StrictBelow v) := Subtype.partialOrder _

def strictConeRay (v : P) (x : StrictBelow v) : StrictOrdEdge P :=
  ⟨(x.1, v), x.2⟩

/-- The actual triangle over an actual edge in the strict lower interval. -/
def strictConeTriangle (v : P) (e : StrictOrdEdge (StrictBelow v)) : StrictOrdTri P :=
  ⟨(e.1.1.val, e.1.2.val, v), e.2, e.1.2.property⟩

noncomputable def strictRayChain (v : P) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictBelow v →₀ ℤ) :=
  Finsupp.lcomapDomain (strictConeRay v) (fun _ _ h => Subtype.ext (congrArg (·.1.1) h))

theorem strictRayChain_single_of_ne (v : P) (e : StrictOrdEdge P) (h : e.1.2 ≠ v) (n : ℤ) :
    strictRayChain v (Finsupp.single e n) = 0 :=
  Finsupp.comapDomain_single_of_not_mem_range (f := strictConeRay v)
    (fun ⟨_, he⟩ => h (congrArg (·.1.2) he.symm)) _ _

noncomputable def strictTopLinkChain (v : P) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (StrictBelow v) →₀ ℤ) :=
  Finsupp.lcomapDomain (strictConeTriangle v) (fun _ _ h => Subtype.ext (Prod.ext
    (Subtype.ext (congrArg (·.1.1) h)) (Subtype.ext (congrArg (·.1.2.1) h))))

theorem strictTopLinkChain_apply (v : P) (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictBelow v)) :
    strictTopLinkChain v c e = c (strictConeTriangle v e) := rfl

/-- At a maximal vertex, extracting cone rays from the actual triangle boundary
is the actual boundary of the extracted link edge chain. -/
theorem strictTopLink_boundary (v : P) (hm : ∀ p, v ≤ p → p = v)
    (c : StrictOrdTri P →₀ ℤ) :
    strictRayChain v (bdry2 (strictOrderCx P) c) =
      bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) := by
  classical
  finsupp_basis c
  rintro ⟨⟨a, b, c⟩, hab, hbc⟩
  have hb : b ≠ v := fun h => hbc.ne (h.trans (hm c (h ▸ hbc.le)).symm)
  erw [strictTriangle_bdry2_single, map_sub, map_add, strictRayChain_single_of_ne _ _ hb, zero_add]
  by_cases h : c = v
  · subst c
    let e : StrictOrdEdge (StrictBelow v) := ⟨(⟨a, hab.trans hbc⟩, ⟨b, hbc⟩), hab⟩
    change strictRayChain v (Finsupp.single (strictConeRay v e.1.2) 1) -
      strictRayChain v (Finsupp.single (strictConeRay v e.1.1) 1) =
        bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v (Finsupp.single (strictConeTriangle v e) 1))
    simp [strictRayChain, strictTopLinkChain, Finsupp.comapDomain_single]
    rw [bdry1_single, one_smul]
    rfl
  · erw [strictRayChain_single_of_ne _ _ h, strictRayChain_single_of_ne _ _ h, sub_zero]
    have hs : strictTopLinkChain v (Finsupp.single ⟨(a, b, c), hab, hbc⟩ 1) = 0 :=
      Finsupp.comapDomain_single_of_not_mem_range (f := strictConeTriangle v)
        (fun ⟨_, he⟩ => h (congrArg (·.1.2.2) he.symm)) _ _
    erw [hs, map_zero]

/-- Genuine cover two-cycles give genuine one-cycles in the link of each maximal apex. -/
theorem strictTopLink_cycle (v : P) (hm : ∀ p, v ≤ p → p = v)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) = 0 := by
  rw [← strictTopLink_boundary v hm, hc, map_zero]

end FiniteChains.Comb
