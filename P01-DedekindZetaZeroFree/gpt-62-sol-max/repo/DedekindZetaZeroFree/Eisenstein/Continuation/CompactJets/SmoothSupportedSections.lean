module

public import DedekindZetaZeroFree.Analysis.RightFrame.CauchyCoefficient
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology Filter

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

section ScalarCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


private theorem jet_constant_word (n : ℕ) (u : E → ℂ) (U : Set E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n u U x v =
      RightFrame.PullbackWords.constantDirectionWord (List.ofFn v) u x := by
  rw [iteratedFDerivWithin_of_isOpen n hU hx]
  induction n generalizing x with
  | zero => simp [RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ n u y (Fin.tail v)) =ᶠ[𝓝 x]
        RightFrame.PullbackWords.constantDirectionWord (List.ofFn (Fin.tail v)) u :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy _
    rw [heq.fderiv_eq]
    simp only [List.ofFn_succ, RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord]
    rfl



end ScalarCalculus

def pointwiseJets (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (k : ℕ) (s : ℂ) : Sections F ζ hζ U R P H := fun i =>
  ⟨fun x => iteratedDerivWithin k (fun z => (w z i).val x) O s, by
    constructor
    · intro x ε hε
      have heq : (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (w z i).val x) =
          (fun z => (w z i).val x) := by
        funext z
        exact (w z i).property.1 x ε hε
      rw [← iteratedDerivWithin_const_mul_field, heq]
    · intro γ x
      have heq : (fun z => (w z i).val ((γ : KPCuspArithmetic.PGL2 F) • x)) =
          (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) * (w z i).val x) := by
        funext z
        exact (w z i).property.2 γ x
      dsimp only
      rw [heq, iteratedDerivWithin_const_mul_field]⟩

@[simp] theorem pointwiseJets_zero (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ) (s : ℂ) :
    pointwiseJets w O 0 s = w s := by
  funext i
  apply Subtype.ext
  simp [pointwiseJets]

@[simp] theorem pointwiseJets_apply (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (k : ℕ) (s : ℂ) (i) (x) :
    (pointwiseJets w O k s i).val x = iteratedDerivWithin k (fun z => (w z i).val x) O s := rfl


theorem pointwiseJets_support (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsClosed K)
    (hsupport : ∀ s ∈ O, tsupport (sectionNorm F ζ hζ U R P H (w s)) ⊆ K)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) :
    tsupport (sectionNorm F ζ hζ U R P H (pointwiseJets w O k s)) ⊆ K := by
  apply closure_minimal _ hK
  intro b hb
  by_contra hbK
  let p := (H.atlas U).components.symm b
  obtain ⟨x, hx⟩ := Quotient.mk_surjective p.2
  have hbase : (H.atlas U).components ⟨p.1, Quotient.mk _ x⟩ = b := by
    rw [hx]
    exact (H.atlas U).components.apply_symm_apply b
  have hzero : Set.EqOn (fun z => (w z p.1).val x) (fun _ => (0 : ℂ)) O := by
    intro z hz
    apply norm_eq_zero.mp
    rw [← sectionNorm_component, hbase]
    exact image_eq_zero_of_notMem_tsupport (fun h => hbK (hsupport z hz h))
  have hz := iteratedDerivWithin_congr (n := k) hzero hs
  simp only [iteratedDerivWithin_fun_const_zero] at hz
  have hnorm : sectionNorm F ζ hζ U R P H (pointwiseJets w O k s) b = 0 := by
    rw [← hbase, sectionNorm_component, pointwiseJets_apply, hz, norm_zero]
  exact hb hnorm

private theorem action_smooth (g : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : KPCuspGenuineMonodromy.SymmetricSpace F => g • x) := by
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [← hG]
  have he : (fun x : KPCuspGenuineMonodromy.SymmetricSpace F =>
      (Matrix.ProjGenLinGroup.mk G : KPCuspArithmetic.PGL2 F) • x) = KPCuspSiegel.glAction F G := by
    funext x; exact KPCuspSiegel.action_mk F G x
  rw [he]
  exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
    (fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F k).embedding G)).of_le le_top

private theorem labeledA_labeledAInv' (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (x : KPCuspGenuineMonodromy.SymmetricSpace F) : labeledA p (labeledAInv p x) = x := by
  funext k
  simp [labeledA, labeledAInv]




end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
