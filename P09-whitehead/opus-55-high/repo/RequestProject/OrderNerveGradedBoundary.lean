import RequestProject.OrderNerveGradedDictionary
import RequestProject.OrderNerveExplicitSingularMap
import RequestProject.TopologicalSingular.SupportedFillings
import RequestProject.Tac


bwd

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
open scoped Simplicial
variable {P : Type} [PartialOrder P]

/-- The free simplicial-module boundary, with its exact integer coefficients. -/
theorem mathlibOrderNerve_d_single n (s : ComposableArrows P (n + 1)) r :
    (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom (Finsupp.single s r) =
      ∑ i : Fin (n + 2), (-1) ^ i.val • Finsupp.single ((nerve P).δ i s) r := by
  simp [AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, ModuleCat.free]

/-- Mathlib's differential and the augmented list boundary coincide in every positive degree. -/
theorem orderNerveGradedEncode_boundary n (c : ComposableArrows P (n + 1) →₀ ℤ) :
    orderNerveGradedEncode n ((AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) n).hom c) =
      Nerve.bdry (orderNerveGradedEncode (n + 1) c) := by
  lin_ind c with c d hc hd => simp only [map_add, hc, hd]
  | s r =>
    rwd [mathlibOrderNerve_d_single, map_sum, orderNerveGradedEncode_single,
      map_zsmul, Nerve.bdry_of]
    unfold orderNerveVertexList
    rwd [Nerve.bdryOn_ofFn, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rwd [map_smul, orderNerveGradedEncode_single, smul_comm]
    rfl

/-- Realize a homogeneous part of the augmented nerve by the canonical unit. -/
noncomputable def orderNerveGradedRealize P [PartialOrder P] n :
    Nerve.Ch P →ₗ[ℤ] Chain (orderNerveRealization P) n :=
  ((orderNerveExplicitSingularMap P).f n).hom.comp (orderNerveGradedDecode n)

theorem orderNerveGradedRealize_boundary n {c} (hc : c ∈ Nerve.Inc P) :
    boundary n (orderNerveGradedRealize P (n + 1) c) =
      orderNerveGradedRealize P n (Nerve.bdry c) := by
  have hd : (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom
      (orderNerveGradedDecode _ c) = orderNerveGradedDecode n (Nerve.bdry c) := by
    apply orderNerveGradedEncode_injective n
    grind [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hc, orderNerveGradedEncode_decode _ (Nerve.bdry_mem_inc hc), Nerve.lengthProjection_bdry]
  have he := congrArg (· (orderNerveGradedDecode (n + 1) c))
    ((orderNerveExplicitSingularMap P).comm _ n)
  rwd [complex_d, AlternatingFaceMapComplex.obj_d_eq] at he
  aesop

theorem orderNerveGradedRealize_supported n (A : Set P)
    {c} (hc : c ∈ Nerve.IncOn A) :
    orderNerveGradedRealize P n c ∈
      subChains (orderNerveRealizationSubcomplex P A) n := by
  classical
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    change (orderNerveExplicitSingularMap P).f n (orderNerveGradedDecode n
      (FreeAbelianGroup.of l)) ∈ _
    rwd [orderNerveGradedDecode_of]
    by_cases h : ∃ s : ComposableArrows P n, orderNerveVertexList s = l
    · rwd [orderNerveGradedDecodeList, dif_pos h, orderNerveExplicitSingularMap_single]
      apply single_mem_subChains
      intro z
      apply orderNerveSingularSimplex_supported
      intro i
      apply hl.2
      have hs : h.choose.obj i ∈ orderNerveVertexList h.choose := List.mem_ofFn.mpr ⟨i, rfl⟩
      grind
    · simp [orderNerveGradedDecodeList, dif_neg h, map_zero]
  | zero => simp
  | add x y _ _ hx hy => aesop
  | neg x _ hx => simp_all
