module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Ideals.SClassPrincipalization

@[expose] public section


open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.FixedSResidue

noncomputable section

variable {F : Type} [Field F] [NumberField F]

section
variable (A : SArithmeticData F)
include A
abbrev FullLocalCharacters   :=
  ((w : InfinitePlace F) → (w.Completionˣ →* ℂˣ)) ×
    ((v : {v // v ∈ A.Sf}) → ((v.val.adicCompletion F)ˣ →* ℂˣ))

def HasFiniteOrder   (σ : FullLocalCharacters A)  :=
  ∃ k : ℕ, 0 < k ∧
    (∀ (w : InfinitePlace F) (x : w.Completionˣ), σ.1 w x ^ k = 1) ∧
    (∀ (v : {v // v ∈ A.Sf}) (x : (v.val.adicCompletion F)ˣ), σ.2 v x ^ k = 1)

abbrev NonzeroSInteger   := {n : A.R // n ≠ 0}

def fieldUnit   (n : NonzeroSInteger A) : Fˣ :=
  Units.mk0 (n.val : F) (by
    intro h
    apply n.property
    exact Subtype.ext h)

def localInverseProduct   (σ : FullLocalCharacters A)
    (n : NonzeroSInteger A)  :=
  (∏ w : InfinitePlace F, ((σ.1 w ((A.diagonal (fieldUnit A n)).1 w) : ℂ)⁻¹)) *
    ∏ v : {v // v ∈ A.Sf}, ((σ.2 v ((A.diagonal (fieldUnit A n)).2 v) : ℂ)⁻¹)

def ConductorSplit  
    (f fS qO : Ideal (𝓞 F))  :=
  f ≠ ⊥ ∧ fS ≠ ⊥ ∧ qO ≠ ⊥ ∧ f = fS * qO ∧
    (∀ v : HeightOneSpectrum (𝓞 F), fS ≤ v.asIdeal → v ∈ A.Sf) ∧
    qO ⊔ A.cS = ⊤

def residueModulus   (qO : Ideal (𝓞 F))  :=
  Ideal.map (algebraMap (𝓞 F) A.R) qO

abbrev ResidueCharacter   (q : Ideal A.R) :=
  (A.R ⧸ q)ˣ →* ℂˣ

def residueZeroExtension   (q : Ideal A.R)
    (lam : ResidueCharacter A q)  :=
  MulChar.ofUnitHom lam

def ExteriorDecomposition  
    (f : Ideal (𝓞 F)) (omega : RayClassCharacter F f)
    (sigma : FullLocalCharacters A) (q : Ideal A.R)
    (lam : ResidueCharacter A q)  :=
  ∀ (a : A.Exterior) (n : NonzeroSInteger A),
    Ideal.span {n.val} = A.extendIdeal a →
      omega a.val = localInverseProduct A sigma n *
        residueZeroExtension A q lam (Ideal.Quotient.mk q n.val)

theorem infiniteComponent_norm  
    (σ : FullLocalCharacters A) (hσ : HasFiniteOrder A σ)
    (w : InfinitePlace F) (x : w.Completionˣ) : ‖(σ.1 w x : ℂ)‖ = 1 := by
  obtain ⟨k, hk, hi, _⟩ := hσ
  exact Complex.norm_eq_one_of_pow_eq_one
    (congrArg (fun u : ℂˣ => (u : ℂ)) (hi w x)) (Nat.ne_of_gt hk)

theorem finiteComponent_norm  
    (σ : FullLocalCharacters A) (hσ : HasFiniteOrder A σ)
    (v : {v // v ∈ A.Sf}) (x : (v.val.adicCompletion F)ˣ) :
    ‖(σ.2 v x : ℂ)‖ = 1 := by
  obtain ⟨k, hk, _, hf⟩ := hσ
  exact Complex.norm_eq_one_of_pow_eq_one
    (congrArg (fun u : ℂˣ => (u : ℂ)) (hf v x)) (Nat.ne_of_gt hk)

theorem localInverseProduct_norm  
    (σ : FullLocalCharacters A) (hσ : HasFiniteOrder A σ)
    (n : NonzeroSInteger A) : ‖localInverseProduct A σ n‖ = 1 := by
  simp [localInverseProduct, norm_mul, norm_prod, norm_inv,
    infiniteComponent_norm A σ hσ, finiteComponent_norm A σ hσ]

theorem conductorSplit_norm_le  
    (f fS qO : Ideal (𝓞 F)) (hf : ConductorSplit A f fS qO) :
    Ideal.absNorm qO ≤ Ideal.absNorm f := by
  obtain ⟨hf0, _, _, hfactor, _⟩ := hf
  have hpos : 0 < Ideal.absNorm f :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hf0)
  apply Nat.le_of_dvd hpos
  apply Ideal.absNorm_dvd_absNorm_of_le
  rw [hfactor]
  exact Ideal.mul_le_right

@[simp]
theorem residueZeroExtension_unit   (q : Ideal A.R)
    (lam : ResidueCharacter A q) (x : (A.R ⧸ q)ˣ) :
    residueZeroExtension A q lam (x : A.R ⧸ q) = (lam x : ℂ) :=
  MulChar.ofUnitHom_coe lam x

theorem residueZeroExtension_top  
    (lam : ResidueCharacter A ⊤) (x : A.R ⧸ (⊤ : Ideal A.R)) :
    residueZeroExtension A ⊤ lam x = 1 := by
  have hx : x = 1 := Subsingleton.elim _ _
  rw [hx, map_one]
end


end
end DedekindZetaZeroFree.Detector.FixedSResidue
