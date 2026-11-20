module

public import RequestProject.RelatorCircleAttachingStrict
public import RequestProject.PresCylinderCollapsedRoseLinear
public import RequestProject.RoseCoverLetterChain

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool)) (j : J)
  (f : P → CylBase w) (hf : IsPosetCover f) (m : RelatorCircle w j → P)
  (hm : StrictMono m) (hp : ∀ x, f (m x) = cylOuter (aHom w) x.val)

variable (x : RelatorCircle w j)

/-- The actual collapsed attaching-circle vertices in the actual rose preimage. -/
noncomputable def cylinderCoverCollapsedCircle : cylinderCoverRoseSet w f :=
  ⟨cylinderCoverCollapse w hf _, cylinderCoverCollapse_mem_rose w f hf (m x)⟩

include hp in
/-- Actual collapse projects to the actual letter attaching map. -/
theorem cylinderCoverCollapsedCircle_projection :
    cylinderCoverRoseEnd w f (cylinderCoverCollapsedCircle w j f hf m x) = aFun w x.val := by
  have h := cylinderCoverRoseEnd_projection w f (cylinderCoverCollapsedCircle w j f hf m x)
  erw [cylinderCoverCollapse_projection w hf _, hp x] at h; exact Sum.inl.inj h

include hm hp in
/-- The actual collapsed circle map is strict because its actual attaching projection is strict. -/
theorem cylinderCoverCollapsedCircle_strictMono :
    StrictMono (cylinderCoverCollapsedCircle w j f hf m) := by
  intro x y h
  apply lt_of_le_of_ne ((cylinderCoverCollapse_monotone w hf) (hm h).le)
  intro he
  have hs : cylinderCoverCollapsedCircle w j f hf m x = cylinderCoverCollapsedCircle w j f hf m y := Subtype.ext he
  have hp' := congrArg (cylinderCoverRoseEnd w f) hs
  erw [cylinderCoverCollapsedCircle_projection w j f hf m hp,
    cylinderCoverCollapsedCircle_projection w j f hf m hp] at hp'
  exact (relatorCircleAttaching_strictMono w j h).ne hp'

variable (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)

include hm hp in
/-- Actual collapsed circle chains include as the normalized collapse of the original lifted chains. -/
theorem cylinderCoverCollapsedCircle_chain_inclusion :
    chain1 (strictSubposetIncl (cylinderCoverRoseSet w f))
      (chain1 (strictOrderCxMap (cylinderCoverCollapsedCircle w j f hf m)
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)) c) =
      normalizedStrictChain1 _ (cylinderCoverCollapse_monotone w hf)
        (chain1 (strictOrderCxMap m hm) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    change Finsupp.mapDomain _
      (Finsupp.mapDomain _ _) =
      normalizedStrictChain1 _ _ (Finsupp.mapDomain _ _)
    erw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      normalizedStrictChain1_single]
    have hn : cylinderCoverCollapse w hf _ ≠ cylinderCoverCollapse w hf _ :=
      fun he => (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp e.property).ne
        (Subtype.ext he)
    change Finsupp.single _ n = n • normalizeOrdEdge
      ⟨(cylinderCoverCollapse w hf (m e.val.1), cylinderCoverCollapse w hf (m e.val.2)), _⟩
    simp only [normalizeOrdEdge, dif_neg hn, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl

include hm hp in
/-- The actual linear rose pullback equals the actual collapsed circle chain map. -/
theorem cylinderCoverCollapsedCircle_chain :
    cylinderCoverCollapsedRoseChain w f hf (chain1 (strictOrderCxMap m hm) c) =
      chain1 (strictOrderCxMap _
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)) c := by
  apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective _)
  exact (cylinderCoverCollapsedRoseChain_inclusion w f hf _).trans
    (cylinderCoverCollapsedCircle_chain_inclusion w j f hf m hm hp c).symm

end FiniteChains.PresModel
