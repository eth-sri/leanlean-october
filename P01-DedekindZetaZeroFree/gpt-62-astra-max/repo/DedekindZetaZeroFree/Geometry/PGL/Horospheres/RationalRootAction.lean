module
public import DedekindZetaZeroFree.Adeles.Approximation.UpperRoots.AngularAction

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Matrix

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

theorem upper_root_action (z : ℂ) (q : KPArch.H3) :
    KPArch.action (KubotaRankTwo.n ℂ z) q = (q.1 + z, q.2) := by
  apply Prod.ext
  · simp [KPArch.action, KPArch.actionDenominator, KubotaRankTwo.coe_n]
  · simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KubotaRankTwo.coe_n, Matrix.det_fin_two]

alias projective_action_mk := DedekindZetaZeroFree.KPMsFixedHaar.projective_action_mk

alias projective_action_mul := DedekindZetaZeroFree.KPMsFixedHaar.projective_action_mul

variable {F : Type} [Field F] [NumberField F]

alias archBasepoint_mul := DedekindZetaZeroFree.KPMsActualAngularRootAlgebraSource.archBasepoint_mul

def archRoot (z : NumberField.InfinitePlace F → ℂ) :
    KPSmoothActualFlowData.GInfinity F :=
  fun v => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ (z v))

def translateCross (z : NumberField.InfinitePlace F → ℂ)
    (p : KPCuspCharts.Cross F) : KPCuspCharts.Cross F :=
  (fun i => p.1 i + z (KPCusp.complexPlace F i), p.2)

alias projective_action_inv_cancel := DedekindZetaZeroFree.KPMsActualAngularRootAlgebraSource.projective_action_inv_cancel

theorem archBasepoint_conjugated_root
    (σ a : KPSmoothActualFlowData.GInfinity F)
    (z : NumberField.InfinitePlace F → ℂ) (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a = fun i =>
      KPArch.action (σ (KPCusp.complexPlace F i)).out
        (KPCuspCharts.toArch F (p,t) i)) :
    KPMsFixedHaarDisintegration.archBasepoint F
      (σ * archRoot z * σ⁻¹ * a) = fun i =>
      KPArch.action (σ (KPCusp.complexPlace F i)).out
        (KPCuspCharts.toArch F (translateCross z p,t) i) := by
  funext i
  rw [archBasepoint_mul]
  change KPArch.action ((σ (KPCusp.complexPlace F i) *
      archRoot z (KPCusp.complexPlace F i)) *
      (σ (KPCusp.complexPlace F i))⁻¹).out
    (KPMsFixedHaarDisintegration.archBasepoint F a i) = _
  rw [ha, projective_action_mul, projective_action_mul,
    projective_action_inv_cancel]
  congr 1
  rw [archRoot, projective_action_mk, upper_root_action]
  rfl

variable (σ : KPCuspArithmetic.PGL2 F)

def archRational :
    KPSmoothActualFlowData.GInfinity F := fun v =>
  Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map v.embedding σ.out)

theorem archRational_action
    (q : KPFiniteCuspAtlas.SymmetricSpace F) :
    (fun i => KPArch.action (archRational σ (KPCusp.complexPlace F i)).out (q i)) =
      KPCuspSiegel.action F σ q := by apply @DedekindZetaZeroFree.KPMsActualAngularRootAlgebraSource.archRational_action <;> assumption

theorem archBasepoint_rational_conjugated_root (a : KPSmoothActualFlowData.GInfinity F)
    (z : NumberField.InfinitePlace F → ℂ) (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F σ (KPCuspCharts.toArch F (p,t))) :
    KPMsFixedHaarDisintegration.archBasepoint F
      (archRational σ * archRoot z * (archRational σ)⁻¹ * a) =
        KPCuspSiegel.action F σ (KPCuspCharts.toArch F (translateCross z p,t)) := by
  rw [← archRational_action] at ha ⊢
  exact archBasepoint_conjugated_root _ _ _ _ _ ha

end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

end
