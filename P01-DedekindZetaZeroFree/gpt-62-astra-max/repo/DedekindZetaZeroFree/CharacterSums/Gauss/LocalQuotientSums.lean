module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.RepresentativeIndependence
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ResiduePhases.GlobalQuotientCompatibility

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.CompatiblePrimeRawLocal
open LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

section

variable (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)

def Congruent (n : ℕ) (x y : LocalField p) : Prop :=
  ∃ r : LocalIntegers p, x - y = uniformizer C p ^ n * (r : LocalField p)

def numeratorCongruence (t k J : ℕ) (a h : (LocalIntegers p)ˣ)
    (d : LocalField p) : Prop :=
  Congruent C p k ((h.val : LocalField p) * uniformizer C p ^ J)
    ((a.val : LocalField p) * uniformizer C p ^ t * d)

def rawPhase (t k J : ℕ) (s a h : (LocalIntegers p)ˣ)
    (d v : LocalField p) : ℂ :=
  (negativeTrace p
    ((((h.val : LocalField p) * uniformizer C p ^ J -
      (a.val : LocalField p) * uniformizer C p ^ t * d) * v) /
      ((s.val : LocalField p) * (a.val : LocalField p) *
        uniformizer C p ^ (k + t))) : ℂ)

end

alias sInteger_local_integral := sInteger_local_integral_source

alias negativeTrace_integer := negativeTrace_integer_source

def canonicalLocalRepresentative (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : Residue C p n) : LocalField p :=
  algebraMap F (LocalField p) ((lifts C p n).val x : F)

structure LocalLifts (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) where
  val : Residue C p n → LocalField p
  integral : ∀ x, val x ∈ p.val.adicCompletionIntegers F
  congruent : ∀ x, Congruent C p n (val x) (canonicalLocalRepresentative C p n x)

def canonicalLocalLifts (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : LocalLifts C p n where
  val := canonicalLocalRepresentative C p n
  integral x := sInteger_local_integral p ((lifts C p n).val x)
  congruent x := ⟨0, by simp⟩

section

variable (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (t k J : ℕ)
    (s a h : (LocalIntegers p)ˣ)

theorem rawPhase_representatives_independent
    (d d' v v' : LocalIntegers p)
    (hd : Congruent C p k (d : LocalField p) (d' : LocalField p))
    (hv : Congruent C p t (v : LocalField p) (v' : LocalField p))
    (hc : numeratorCongruence C p t k J a h (d : LocalField p)) :
    rawPhase C p t k J s a h (d : LocalField p) (v : LocalField p) =
      rawPhase C p t k J s a h (d' : LocalField p) (v' : LocalField p) := CRTRawLocalModel.rawPhase_representatives_independent C p t k J s a h
    d d' v v' hd hv hc

def RWithLifts
    (D : LocalLifts C p k) (V : LocalLifts C p t) : ℂ :=
  ∑ d : Residue C p k,
    if numeratorCongruence C p t k J a h (D.val d) then
      maskedPower C p k k d *
        ∑ v : Residue C p t, maskedPower C p t t v *
          rawPhase C p t k J s a h (D.val d) (V.val v)
    else 0

def R : ℂ :=
  RWithLifts C p t k J s a h (canonicalLocalLifts C p k)
    (canonicalLocalLifts C p t)

theorem RWithLifts_independent
    (D D' : LocalLifts C p k) (V V' : LocalLifts C p t) :
    RWithLifts C p t k J s a h D V = RWithLifts C p t k J s a h D' V' := by
  unfold RWithLifts
  apply Finset.sum_congr rfl
  intro d _
  have hd := CRTRawLocalModel.congruent_trans C p k (D.congruent d)
    (CRTRawLocalModel.congruent_symm C p k (D'.congruent d))
  have hc : numeratorCongruence C p t k J a h (D.val d) ↔
      numeratorCongruence C p t k J a h (D'.val d) :=
    CRTRawLocalModel.numeratorCongruence_independent C p t k J a h hd
  by_cases hcon : numeratorCongruence C p t k J a h (D.val d)
  · rw [if_pos hcon, if_pos (hc.mp hcon)]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    exact rawPhase_representatives_independent C p t k J s a h
      ⟨D.val d, D.integral d⟩ ⟨D'.val d, D'.integral d⟩
      ⟨V.val v, V.integral v⟩ ⟨V'.val v, V'.integral v⟩ hd
      (CRTRawLocalModel.congruent_trans C p t (V.congruent v)
        (CRTRawLocalModel.congruent_symm C p t (V'.congruent v))) hcon
  · rw [if_neg hcon, if_neg (fun h' => hcon (hc.mpr h'))]

end

theorem R_one_eq_Ctk (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) :
    R C p t k J 1 1 1 = Ctk C p t k J := by
  unfold R RWithLifts Ctk
  apply Finset.sum_congr rfl
  intro d _
  change (if numeratorCongruence C p t k J 1 1 (canonicalLocalRepresentative C p k d)
    then _ else _) = _
  have hbridge : numeratorCongruence C p t k J 1 1 (canonicalLocalRepresentative C p k d) ↔
      residueMap C p k (generator C p ^ J) =
        residueMap C p k (generator C p ^ t) * d :=
    canonicalNumeratorCongruence_iff C p t k J d
  rw [propext hbridge]
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    rw [psi_residueMap_eq_negativeTrace]
    simp only [canonicalLocalLifts, canonicalLocalRepresentative, rawPhase,
      Units.val_one, map_one, one_mul, mul_one, uniformizer, map_mul, map_sub, map_pow]
    simp only [map_mul, map_sub, map_pow, OneMemClass.coe_one, one_mul]
    simp
  · rfl

end DedekindZetaZeroFree.CompatiblePrimeRawLocal

end
