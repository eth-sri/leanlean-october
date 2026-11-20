module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.SquarefreeGcd

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
    {a b c d u v : Ideal (𝓞 F)}

private lemma bot_ne_top_ideal : (⊥ : Ideal (𝓞 F)) ≠ ⊤ := by
  intro hh
  have h1 : (1 : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := hh ▸ Submodule.mem_top
  rw [Ideal.mem_bot] at h1
  exact one_ne_zero h1

private lemma sup_eq_top_of_isRelPrime {x y : Ideal (𝓞 F)} (h : IsRelPrime x y) :
    x ⊔ y = ⊤ :=
  Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

alias SquarefreeGcdDecomposition.sup_eq_top_of_isRelPrime := sup_eq_top_of_isRelPrime

private lemma isRelPrime_of_sup_eq_top {x y : Ideal (𝓞 F)} (h : x ⊔ y = ⊤) :
    IsRelPrime x y := by
  intro z hzx hzy
  rw [Ideal.isUnit_iff]
  exact le_antisymm le_top
    (h ▸ sup_le (Ideal.dvd_iff_le.mp hzx) (Ideal.dvd_iff_le.mp hzy))

alias SquarefreeGcdDecomposition.isRelPrime_of_sup_eq_top := isRelPrime_of_sup_eq_top

theorem ne_bot_of_squarefree (ha : Squarefree a) : a ≠ ⊥ := by
  intro h
  exact bot_ne_top_ideal ((Ideal.isUnit_iff).mp (ha (⊥ : Ideal (𝓞 F)) (by rw [(Ideal.mul_eq_bot.mpr (Or.inl rfl)), h])))

section

variable (ha : Squarefree a) (hb : Squarefree b)

include ha hb in
theorem gcd_ne_bot : a ⊔ b ≠ ⊥ := fun h => ne_bot_of_squarefree ha (le_bot_iff.mp (h ▸ le_sup_left))

include ha hb in
theorem squarefree_gcd :
    Squarefree (a ⊔ b) :=
  ha.squarefree_of_dvd (Ideal.dvd_iff_le.mpr le_sup_left)

include ha hb in
theorem existsUnique_strip :
    ∃! uv : Ideal (𝓞 F) × Ideal (𝓞 F),
      a = (a ⊔ b) * uv.1 ∧ b = (a ⊔ b) * uv.2 := by
  obtain ⟨u, hu⟩ := Ideal.dvd_iff_le.mpr (le_sup_left : a ≤ a ⊔ b)
  obtain ⟨v, hv⟩ := Ideal.dvd_iff_le.mpr (le_sup_right : b ≤ a ⊔ b)
  refine ⟨(u, v), ⟨hu, hv⟩, ?_⟩
  rintro ⟨u', v'⟩ ⟨hu', hv'⟩
  have hne := gcd_ne_bot ha hb
  exact Prod.ext (mul_left_cancel₀ hne (hu'.symm.trans hu))
    (mul_left_cancel₀ hne (hv'.symm.trans hv))

end

variable (ha : Squarefree a) (hb : Squarefree b) (had : a = (a ⊔ b) * u) (hbd : b = (a ⊔ b) * v)

include ha hb had hbd in
theorem strip_squarefree_and_coprime :
    Squarefree (a ⊔ b) ∧ Squarefree u ∧ Squarefree v ∧
      u ⊔ v = ⊤ ∧ (a ⊔ b) ⊔ u = ⊤ ∧ (a ⊔ b) ⊔ v = ⊤ := by
  refine ⟨squarefree_gcd ha hb, ha.squarefree_of_dvd (⟨a ⊔ b, had.trans (mul_comm _ _)⟩), hb.squarefree_of_dvd (⟨a ⊔ b, hbd.trans (mul_comm _ _)⟩), ?_, ?_, ?_⟩
  · refine sup_eq_top_of_isRelPrime fun e heu hev => ?_
    have h1 := Ideal.dvd_iff_le.mp heu
    exact ha e (Ideal.dvd_iff_le.mpr (had.le.trans (Submodule.smul_mono (sup_le ((had.le.trans (by
      calc _ ≤ ⊤ * u := Submodule.smul_mono le_top le_rfl
        _ = u := Ideal.top_mul u)).trans h1) ((hbd.le.trans (by
      calc _ ≤ ⊤ * v := Submodule.smul_mono le_top le_rfl
        _ = v := Ideal.top_mul v)).trans (Ideal.dvd_iff_le.mp hev))) h1)))
  · refine sup_eq_top_of_isRelPrime fun e hed heu => ?_
    exact ha e (Ideal.dvd_iff_le.mpr (had.le.trans (Submodule.smul_mono (Ideal.dvd_iff_le.mp hed) (Ideal.dvd_iff_le.mp heu))))
  · refine sup_eq_top_of_isRelPrime fun e hed hev => ?_
    exact hb e (Ideal.dvd_iff_le.mpr (hbd.le.trans (Submodule.smul_mono (Ideal.dvd_iff_le.mp hed) (Ideal.dvd_iff_le.mp hev))))

include ha hb had hbd in
theorem strip_coprime_aux
    (hac : a ⊔ c = ⊤) (hbc : b ⊔ c = ⊤) :
    (a ⊔ b) ⊔ c = ⊤ ∧ u ⊔ c = ⊤ ∧ v ⊔ c = ⊤ := by
  have hrel_ac := isRelPrime_of_sup_eq_top hac
  refine ⟨?_, ?_, ?_⟩
  · exact sup_eq_top_of_isRelPrime
      (fun e hed hec => hrel_ac (hed.trans (Ideal.dvd_iff_le.mpr le_sup_left)) hec)
  · exact sup_eq_top_of_isRelPrime (fun e heu hec => hrel_ac (heu.trans (⟨a ⊔ b, had.trans (mul_comm _ _)⟩)) hec)
  · exact sup_eq_top_of_isRelPrime (fun e hev hec => (isRelPrime_of_sup_eq_top hbc) (hev.trans (⟨a ⊔ b, hbd.trans (mul_comm _ _)⟩)) hec)

end DedekindZetaZeroFree.LargeSieve.SquarefreeGcd
