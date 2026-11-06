module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.CommonSectors

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstSectors
open CenteredMomentCompleteCommon CenteredMomentCommonSectors IdealMobiusDivisorSum


def residualPool (C : Ideal ActualEisensteinCubic.O) (hC : C≠0) (S : Finset (Ideal ActualEisensteinCubic.O))  :=
  S.preimage (fun a => C*a) (by intro a ha b hb he;exact mul_left_cancel₀ hC he)

@[simp] theorem mem_residualPool  C   hC   S   a  :
    a∈residualPool C hC S ↔ C*a∈S := Finset.mem_preimage

def pairSector (C D : Ideal ActualEisensteinCubic.O) (S T : Finset (Ideal ActualEisensteinCubic.O))  :=
  (S.product T).filter (fun p => commonPart p.1 p.2=C ∧ commonPart p.2 p.1=D)

def residualPairDomain (C D : Ideal ActualEisensteinCubic.O) (hC : C≠0) (hD : D≠0) (S T : Finset (Ideal ActualEisensteinCubic.O))  :=
  ((residualPool C hC S).product (residualPool D hD T)).filter
    (fun p => IsCoprime C p.1 ∧ IsCoprime C p.2 ∧ IsCoprime p.1 p.2)

section
variable (C D : Ideal ActualEisensteinCubic.O) (hC : C≠0) (hD : D≠0) (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0)
include C D hC hD hCD S T hS hT

theorem residualPair_image      
       
        :
    (residualPairDomain C D hC hD S T).image (fun p => (C*p.1,D*p.2))=pairSector C D S T := by
  ext p
  rcases p with ⟨I,J⟩
  constructor
  · intro hp
    obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hp
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    obtain ⟨hpools,hCa,hCb,hab⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpools
    have has : C*a∈S := (mem_residualPool C hC S a).mp ha
    have hbs : D*b∈T := (mem_residualPool D hD T b).mp hb
    have ha0 : a≠0 := right_ne_zero_of_mul (hS _ has)
    have hb0 : b≠0 := right_ne_zero_of_mul (hT _ hbs)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨has,hbs⟩,
      reconstructed_commonParts C D a b hC hD ha0 hb0 hCD hCa hCb hab⟩
  · intro hp
    obtain ⟨hpools,hCI,hDJ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hIS,hJT⟩ := Finset.mem_product.mp hpools
    have hi : C*residualPart I J=I := by rw [← hCI];exact (reconstruct I J (hS I hIS)).symm
    have hj : D*residualPart J I=J := by rw [← hDJ];exact (reconstruct J I (hT J hJT)).symm
    refine Finset.mem_image.mpr ⟨(residualPart I J,residualPart J I),?_,Prod.ext hi hj⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_,?_,residualParts_coprime I J⟩
    · exact (mem_residualPool C hC S _).mpr (by dsimp only;rw [hi];exact hIS)
    · exact (mem_residualPool D hD T _).mpr (by dsimp only;rw [hj];exact hJT)
    · rw [← hCI]
      exact commonPart_own_residual_coprime I J
    · rw [← hCI]
      exact commonPart_residualPart_coprime I J

section
variable (F : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ)
include F

theorem pairSector_sum      
       
          :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ p∈residualPairDomain C D hC hD S T,F (C*p.1) (D*p.2) := by
  rw [← residualPair_image C D hC hD hCD S T hS hT,Finset.sum_image]
  intro p hp q hq he
  exact Prod.ext (mul_left_cancel₀ hC (congrArg Prod.fst he))
    (mul_left_cancel₀ hD (congrArg Prod.snd he))

theorem pairSector_double_sum      
       
          :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ a∈residualPool C hC S,∑ b∈residualPool D hD T,
        if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F (C*a) (D*b) else 0 := by
  rw [pairSector_sum C D hC hD hCD S T hS hT,residualPairDomain,Finset.sum_filter]
  exact Finset.sum_product _ _ _

end

end

def commonLabels (S T : Finset (Ideal ActualEisensteinCubic.O))  :=
  (S.product T).image (fun p => (commonPart p.1 p.2,commonPart p.2 p.1))

section
variable (S T : Finset (Ideal ActualEisensteinCubic.O))
include S T

theorem commonLabels_data    C D 
    (h : (C,D)∈commonLabels S T) :
    C≠0 ∧ D≠0 ∧ primeSupport C=primeSupport D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  exact ⟨commonPart_ne_zero _ _,commonPart_ne_zero _ _,commonParts_equal_support _ _⟩

theorem sum_common_sectors   (F : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) :
    (∑ I∈S,∑ J∈T,F I J)=
      ∑ p∈commonLabels S T,∑ q∈pairSector p.1 p.2 S T,F q.1 q.2 := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (s:=S.product T) (t:=commonLabels S T)
    (g:=fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O => (commonPart p.1 p.2,commonPart p.2 p.1))
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O => F p.1 p.2)
  symm
  convert hh using 1
  · rfl
  · exact (Finset.sum_product S T (fun p : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O => F p.1 p.2)).symm

end

end SevenEighths.CenteredMomentFirstSectors

end

end OAI
