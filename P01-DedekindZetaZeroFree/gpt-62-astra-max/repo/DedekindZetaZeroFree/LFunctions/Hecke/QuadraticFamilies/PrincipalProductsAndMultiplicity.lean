module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.GcdPairCharacterIdentities
public import DedekindZetaZeroFree.LFunctions.Dedekind.PrincipalHeckeData

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)

private lemma principalProducts_top_ne_bot_ringOfIntegers : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by
  intro h
  have h1 : (1 : 𝓞 F) = 0 := by
    have hm :=
      h ▸ (show (1 : 𝓞 F) ∈ (⊤ : Ideal (𝓞 F)) from Submodule.mem_top)
    simpa using hm
  exact one_ne_zero h1

private lemma mul_ne_bot_of_ne_bot {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I * J ≠ ⊥ := by
  intro h
  rcases Ideal.mul_eq_bot.mp h with h' | h'
  · exact hI h'
  · exact hJ h'

private lemma sup_eq_top_of_dvd {I A M : Ideal (𝓞 F)} (h : I ⊔ M = ⊤) (hdvd : A ∣ M) :
    I ⊔ A = ⊤ := by
  exact le_antisymm le_top (h ▸ sup_le_sup_left (Ideal.dvd_iff_le.mp hdvd) I)

variable (hc : c ≠ ⊥) {a b : Ideal (𝓞 F)} (ha : Squarefree a) (hac : a ⊔ c = ⊤) (hb : Squarefree b)
    (hbc : b ⊔ c = ⊤) (hclass : Q.cls a = Q.cls b)

include hc ha hac hb hbc hclass in
theorem quadraticFamily_eq_of_sameClass_principal_away
    (hprincipal : ∃ q : Ideal (𝓞 F), q ≠ ⊥ ∧
      ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
        I ⊔ (Q.cond a * Q.cond b * q) = ⊤ →
        (Q.χ a) I * (Q.χ b) I = 1) :
    a = b := by

  obtain ⟨⟨u, v⟩, ⟨hau, hbv⟩, -⟩ := SquarefreeGcd.existsUnique_strip ha hb
  obtain ⟨hRne, -, hψ, huvdvd, -⟩ := (rawGcdPairTransport
    hc Q ha hb hac hbc hclass hau hbv)
  obtain ⟨ψ, hψprim, hψval⟩ := hψ
  set R : Ideal (𝓞 F) := c * a * b * Q.cond a * Q.cond b * Q.cond u * Q.cond v with hRdef
  obtain ⟨q, hqne, hq⟩ := hprincipal
  have htop_le :=
    rayCharacter_primitive_modulus_le
      (fun h =>
        mul_ne_bot_of_ne_bot ((Q.primitive a ha hac).1) ((Q.primitive b hb hbc).1) (le_bot_iff.mp (h ▸ Ideal.dvd_iff_le.mp huvdvd))) principalProducts_top_ne_bot_ringOfIntegers (mul_ne_bot_of_ne_bot hqne hRne) ψ hψprim (principalCharacter F) (by
        intro I hI hIsup
        have hdvdq : Q.cond a * Q.cond b * q ∣ u * v * ⊤ * (q * R) := by
          refine ⟨u * v * ⊤ * (c * a * b * Q.cond u * Q.cond v), ?_⟩
          rw [hRdef]
          ac_rfl
        rw [hψval I hI (sup_eq_top_of_dvd hIsup (dvd_mul_of_dvd_right (dvd_mul_left R q) (u * v * ⊤))), hq I hI (sup_eq_top_of_dvd hIsup hdvdq)]
        simp [principalCharacter_apply, hI])
  have hv : v = ⊤ := le_antisymm le_top (htop_le.trans Ideal.mul_le_right)
  have hu : u = ⊤ := by
    rw [hv, Ideal.mul_top] at htop_le
    exact le_antisymm le_top htop_le
  calc a = (a ⊔ b) * u := hau
    _ = (a ⊔ b) * ⊤ := by rw [hu]
    _ = a ⊔ b := Ideal.mul_top _
    _ = (a ⊔ b) * ⊤ := (Ideal.mul_top _).symm
    _ = (a ⊔ b) * v := by rw [hv]
    _ = b := hbv.symm

include hc ha hac hb hbc hclass in
theorem quadraticFamily_principal_product_iff :
    (RayOperations.mul (Q.χ a) (Q.χ b)).IsPrincipal ↔ a = b := by
  constructor
  · intro h
    refine quadraticFamily_eq_of_sameClass_principal_away (Q := Q) hc ha hac hb hbc hclass ?_
    refine ⟨⊤, principalProducts_top_ne_bot_ringOfIntegers, ?_⟩
    intro I hI hIsup
    have hI' : I ⊔ (Q.cond a * Q.cond b) = ⊤ := by simpa using hIsup
    have hval := h I hI hI'
    simpa using hval
  · intro hab
    rw [hab]
    intro I hI hIsup
    have hsq := quadraticFamily_value_sq_eq_one (Q := Q) hb hbc I hI (sup_eq_top_of_dvd hIsup (dvd_mul_right (Q.cond b) (Q.cond b)))
    simpa [pow_two] using hsq

end DedekindZetaZeroFree.LargeSieve
