import RequestProject.AcyclicPresentationActualChains
import RequestProject.RegularCoverChainDescent


/-! Retain the actual maps and the triviality on fundamental groups in
the acyclic presentation construction. These data are needed by regular
cover descent and are lost if one retains only the existence of HasChain.
 -/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm.AmbientChain
open Comb

variable {A C : Type} {core : C → FreeGroup A} {n : ℕ}
  (c : AmbientChain core n)

def cellComplex (i : ℕ) := presComplex (c.chainRel i)

def cellInclusion i : Hom (c.cellComplex i) (c.cellComplex (i + 1)) :=
  presInclHom _ (c.chainGenIncl_injective i)
    _ _ _ (c.chainRel_incl i)

theorem cellInclusion_zero (hinj : Function.Injective (expMatrix core))
    i (hi : i < n + 1) : ZeroPi2 (c.cellInclusion i) := by
  apply (zeroPi2_presInclHom_iff (ρ := c.chainRel i) (σ := c.chainRel _)
    _ _
    _ _).mpr
  exact (c.toPresChainFS hinj).zero_pi2 i hi

theorem first_cellInclusion_pi1Trivial : Pi1Trivial (c.cellInclusion 0) := by
  apply (pi1Trivial_presInclHom_iff (ρ := c.chainRel 0) (σ := c.chainRel 1)
    _ _
    _ _).mpr
  intro w
  induction w using QuotientGroup.induction_on with
  | H w =>
      let f : FreeGroup A →* PresGroup (c.chainRel 1) :=
        (QuotientGroup.mk' _).comp (FreeGroup.map Sum.inl)
      have hf : f = 1 := by
        apply FreeGroup.ext_hom
        intro a
        exact c.core_trivial 0 a
      exact DFunLike.congr_fun hf w

end FiniteChains.RelativeNormalForm.AmbientChain

namespace FiniteChains.RelativeNormalForm
open Comb
variable {A C : Type} (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))
