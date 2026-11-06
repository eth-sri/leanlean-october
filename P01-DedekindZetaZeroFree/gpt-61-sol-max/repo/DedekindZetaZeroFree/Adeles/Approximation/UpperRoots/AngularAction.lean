module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Matrix
namespace DedekindZetaZeroFree.KPMsActualAngularRootAlgebraSource

theorem projective_action_mk (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (q : KPArch.H3) :
    KPArch.action (Matrix.ProjGenLinGroup.mk g).out q = KPArch.action g q := by
  have he : Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk g).out =
      Matrix.ProjGenLinGroup.mk g := Quotient.out_eq _
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  calc
    _ = KPArch.action ((Matrix.ProjGenLinGroup.mk g).out *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) q := by
      rw [(KPArch.action_laws _ _ _).2, KPArch.scalar_action]
    _ = KPArch.action g q := congrArg (fun k => KPArch.action k q) hu

theorem projective_action_mul (g h : Matrix.ProjGenLinGroup (Fin 2) ℂ)
    (q : KPArch.H3) :
    KPArch.action (g * h).out q =
      KPArch.action g.out (KPArch.action h.out q) := by
  have he : g * h = Matrix.ProjGenLinGroup.mk (g.out * h.out) := by
    rw [map_mul]
    exact congrArg₂ (· * ·) (Quotient.out_eq g).symm (Quotient.out_eq h).symm
  rw [he, projective_action_mk, (KPArch.action_laws _ _ _).2]

variable {F : Type} [Field F] [NumberField F]

theorem archBasepoint_mul (g h : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F (g * h) = fun i =>
      KPArch.action (g (KPCusp.complexPlace F i)).out
        (KPMsFixedHaarDisintegration.archBasepoint F h i) := by
  funext i
  exact projective_action_mul _ _ _

theorem projective_action_inv_cancel (g : Matrix.ProjGenLinGroup (Fin 2) ℂ)
    (q : KPArch.H3) :
    KPArch.action g⁻¹.out (KPArch.action g.out q) = q := by
  rw [← projective_action_mul, inv_mul_cancel]
  have he : (1 : Matrix.ProjGenLinGroup (Fin 2) ℂ) =
      Matrix.ProjGenLinGroup.mk 1 := (map_one _).symm
  rw [he, projective_action_mk]
  exact (KPArch.action_laws 1 1 q).1

def archRational (σ : KPCuspArithmetic.PGL2 F) :
    KPSmoothActualFlowData.GInfinity F := fun v =>
  Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map v.embedding σ.out)

theorem archRational_action (σ : KPCuspArithmetic.PGL2 F)
    (q : KPFiniteCuspAtlas.SymmetricSpace F) :
    (fun i => KPArch.action (archRational σ (KPCusp.complexPlace F i)).out (q i)) =
      KPCuspSiegel.action F σ q := by
  have he : σ = Matrix.ProjGenLinGroup.mk σ.out := (Quotient.out_eq σ).symm
  conv_rhs => rw [he, KPCuspSiegel.action_mk]
  funext i
  exact projective_action_mk _ _

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

variable (F : Type) [Field F] [NumberField F] (ζ : F) 
















































open KPAdelicCoverRestrictedProduct
attribute [local instance] localTopology

end DedekindZetaZeroFree.KPMsActualAngularRootAlgebraSource

end
