module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.LargeSieve.SquarefreeGcd

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {a b c d u v : Ideal (𝓞 F)}

private lemma bot_ne_top_ideal : (⊥ : Ideal (𝓞 F)) ≠ ⊤ := by
  simp_all

private def sup_eq_top_of_isRelPrime {x y : Ideal (𝓞 F)} (h : IsRelPrime x y)  :=
  Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

private lemma isRelPrime_of_sup_eq_top {x y : Ideal (𝓞 F)} (h : x ⊔ y = ⊤) :
    IsRelPrime x y := by
  intro z hzx hzy
  rw [Ideal.isUnit_iff]
  exact le_antisymm le_top
    (h ▸ sup_le (Ideal.dvd_iff_le.mp hzx) (Ideal.dvd_iff_le.mp hzy))

theorem ne_bot_of_squarefree (ha : Squarefree a) : a ≠ ⊥ := by
  intro h
  have hbot : (⊥ : Ideal (𝓞 F)) * ⊥ = ⊥ := Ideal.mul_eq_bot.mpr (Or.inl rfl)
  have hdvd : (⊥ : Ideal (𝓞 F)) * ⊥ ∣ a := by rw [hbot, h]
  have hunit  := ha (⊥ : Ideal (𝓞 F)) hdvd
  exact bot_ne_top_ideal ((Ideal.isUnit_iff (I := (⊥ : Ideal (𝓞 F)))).mp hunit)

section
variable (ha : Squarefree a) (hb : Squarefree b)
include ha hb
theorem gcd_ne_bot   : a ⊔ b ≠ ⊥ := by
  intro h
  exact ne_bot_of_squarefree ha (le_bot_iff.mp (h ▸ le_sup_left))

theorem squarefree_gcd   :
    Squarefree (a ⊔ b) :=
  ha.squarefree_of_dvd (Ideal.dvd_iff_le.mpr le_sup_left)

theorem existsUnique_strip   :
    ∃! uv : Ideal (𝓞 F) × Ideal (𝓞 F),
      a = (a ⊔ b) * uv.1 ∧ b = (a ⊔ b) * uv.2 := by
  obtain ⟨u, hu⟩ := Ideal.dvd_iff_le.mpr (le_sup_left : a ≤ a ⊔ b)
  obtain ⟨v, hv⟩ := Ideal.dvd_iff_le.mpr (le_sup_right : b ≤ a ⊔ b)
  refine ⟨(u, v), ⟨hu, hv⟩, ?_⟩
  rintro ⟨u', v'⟩ ⟨hu', hv'⟩
  have hne  := gcd_ne_bot ha hb
  exact Prod.ext (mul_left_cancel₀ hne (hu'.symm.trans hu))
    (mul_left_cancel₀ hne (hv'.symm.trans hv))
end


section
variable (ha : Squarefree a) (hb : Squarefree b)
    (had : a = (a ⊔ b) * u) (hbd : b = (a ⊔ b) * v)
include ha hb had hbd
theorem strip_squarefree_and_coprime
      :
    Squarefree (a ⊔ b) ∧ Squarefree u ∧ Squarefree v ∧
      u ⊔ v = ⊤ ∧ (a ⊔ b) ⊔ u = ⊤ ∧ (a ⊔ b) ⊔ v = ⊤ := by
  have hua : u ∣ a := ⟨a ⊔ b, had.trans (mul_comm _ _)⟩
  have hvb : v ∣ b := ⟨a ⊔ b, hbd.trans (mul_comm _ _)⟩
  have hau  := had.le.trans (by
    calc (a ⊔ b) * u ≤ ⊤ * u := Submodule.smul_mono le_top le_rfl
      _ = u := Ideal.top_mul u)
  have hbv  := hbd.le.trans (by
    calc (a ⊔ b) * v ≤ ⊤ * v := Submodule.smul_mono le_top le_rfl
      _ = v := Ideal.top_mul v)
  refine ⟨squarefree_gcd ha hb, ha.squarefree_of_dvd hua, hb.squarefree_of_dvd hvb, ?_, ?_, ?_⟩
  · refine sup_eq_top_of_isRelPrime fun e heu hev => ?_
    have h1  := Ideal.dvd_iff_le.mp heu
    have h2  := Ideal.dvd_iff_le.mp hev
    have hd : a ⊔ b ≤ e := sup_le (hau.trans h1) (hbv.trans h2)
    exact ha e (Ideal.dvd_iff_le.mpr (had.le.trans (Submodule.smul_mono hd h1)))
  · refine sup_eq_top_of_isRelPrime fun e hed heu => ?_
    have h1  := Ideal.dvd_iff_le.mp heu
    have h2  := Ideal.dvd_iff_le.mp hed
    exact ha e (Ideal.dvd_iff_le.mpr (had.le.trans (Submodule.smul_mono h2 h1)))
  · refine sup_eq_top_of_isRelPrime fun e hed hev => ?_
    have h1  := Ideal.dvd_iff_le.mp hev
    have h2  := Ideal.dvd_iff_le.mp hed
    exact hb e (Ideal.dvd_iff_le.mpr (hbd.le.trans (Submodule.smul_mono h2 h1)))

theorem strip_coprime_aux
     
    (hac : a ⊔ c = ⊤) (hbc : b ⊔ c = ⊤) :
    (a ⊔ b) ⊔ c = ⊤ ∧ u ⊔ c = ⊤ ∧ v ⊔ c = ⊤ := by
  have hrel_ac  := isRelPrime_of_sup_eq_top hac
  have hrel_bc  := isRelPrime_of_sup_eq_top hbc
  have hua : u ∣ a := ⟨a ⊔ b, had.trans (mul_comm _ _)⟩
  have hvb : v ∣ b := ⟨a ⊔ b, hbd.trans (mul_comm _ _)⟩
  refine ⟨?_, ?_, ?_⟩
  · exact sup_eq_top_of_isRelPrime
      (fun e hed hec => hrel_ac (hed.trans (Ideal.dvd_iff_le.mpr le_sup_left)) hec)
  · exact sup_eq_top_of_isRelPrime (fun e heu hec => hrel_ac (heu.trans hua) hec)
  · exact sup_eq_top_of_isRelPrime (fun e hev hec => hrel_bc (hev.trans hvb) hec)
end


end DedekindZetaZeroFree.LargeSieve.SquarefreeGcd
