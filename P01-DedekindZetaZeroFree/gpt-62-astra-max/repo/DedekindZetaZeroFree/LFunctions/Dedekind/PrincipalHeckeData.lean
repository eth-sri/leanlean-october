module

public import DedekindZetaZeroFree.LFunctions.Hecke.FunctionalEquation

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical Topology
open Filter

namespace DedekindZetaZeroFree.LargeSieve

 section

variable (F : Type) [Field F] [NumberField F]

lemma top_ne_bot_ringOfIntegers :
    (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by
  intro h
  have h1 : (1 : 𝓞 F) = 0 := by
    have hm :=
      h ▸ (show (1 : 𝓞 F) ∈ (⊤ : Ideal (𝓞 F)) from Submodule.mem_top)
    simpa using hm
  exact one_ne_zero h1

def principalCharacter :
    DedekindZetaZeroFree.RayClassCharacter F ⊤ where
  toFun I := if I = ⊥ then 0 else 1
  map_mul' := by
    intro I J
    rcases eq_or_ne I ⊥ with hI | hI
    · subst hI
      simp
    rcases eq_or_ne J ⊥ with hJ | hJ
    · subst hJ
      simp
    · have h : I * J ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ
      simp [h, hI, hJ]
  map_top' := by
    simp [top_ne_bot_ringOfIntegers F]
  eq_zero_iff' := by
    intro I
    by_cases hI : I = ⊥ <;> simp [hI]
  map_span' := by
    intro α hα _ _
    have h : Ideal.span {α} ≠ ⊥ := by
      intro hbot
      have hmem : α ∈ (⊥ : Ideal (𝓞 F)) := by
        rw [← hbot]
        exact Ideal.subset_span (Set.mem_singleton α)
      exact hα (by simpa using hmem)
    simp [h]

@[simp] theorem principalCharacter_apply
    (I : Ideal (𝓞 F)) :
    principalCharacter F I = if I = ⊥ then 0 else 1 := rfl

theorem principalCharacter_primitive :
    (principalCharacter F).IsPrimitive := fun 𝔣 h𝔣 => (not_lt_of_ge le_top h𝔣).elim

theorem principalCharacter_principal :
    (principalCharacter F).IsPrincipal := by
  intro I hI _
  simp [principalCharacter, hI]

def principalDiscriminant : ℝ :=
  ((|NumberField.discr F| : ℤ) : ℝ)

def principalComplexPlaces : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces F

theorem principalDiscriminant_pos :
    0 < principalDiscriminant F := by
  rw [principalDiscriminant, Int.cast_pos]
  exact abs_pos.mpr (NumberField.discr_ne_zero F)

theorem principalComplexPlaces_pos
    (hF : NumberField.IsTotallyComplex F) :
    1 ≤ principalComplexPlaces F := by
  have hfin := NumberField.IsTotallyComplex.finrank (K := F)
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  rw [principalComplexPlaces]
  omega

end

structure PrincipalHeckeData (F : Type) [Field F] [NumberField F] where
  Lambda : ℂ → ℂ
  E : ℂ → ℂ
  E_differentiable : Differentiable ℂ E
  Lambda_functional_equation : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Lambda s = Lambda (1 - s)
  E_eq_mul_Lambda : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → E s = s * (s - 1) * Lambda s
  E_growth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
    ‖E s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε))
  E_functional_equation : ∀ s : ℂ, E s = E (1 - s)
  Lambda_eq_div : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    Lambda s = E s / (s * (s - 1))
  Lambda_dirichlet : ∀ s : ℂ, 1 < s.re →
    Lambda s = (principalDiscriminant F : ℂ) ^ (s / 2) *
      Complex.Gammaℂ s ^ principalComplexPlaces F *
        (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s))

theorem PrincipalHeckeData.E_zero_eq_one {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) : data.E 0 = data.E 1 := by
  simpa using data.E_functional_equation 0

variable (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)

include hF in
theorem exists_principalHeckeData :
    Nonempty (PrincipalHeckeData F) := by
  have htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot_ringOfIntegers F
  obtain ⟨Λ, E, hΛ_holo, hE_entire, hseries, hFE, hE_eq, hgrowth⟩ :=
    (DedekindZetaZeroFree.Hecke.heckeFunctionalEquation F hF ⊤ htop (principalCharacter F) (principalCharacter_primitive F)).2
      (principalCharacter_principal F)

  have hΛdiv : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ s = E s / (s * (s - 1)) := by
    intro s hs0 hs1
    rw [hE_eq s hs0 hs1,
      mul_div_cancel_left₀ _ (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))]

  have hEfun : ∀ s : ℂ, E s = E (1 - s) := by
    have hEq : (fun s : ℂ => E s) = fun s : ℂ => E (1 - s) := by
      refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := (2 : ℂ)) ?_ ?_ ?_
      · rw [Complex.analyticOnNhd_univ_iff_differentiable]
        exact hE_entire
      · rw [Complex.analyticOnNhd_univ_iff_differentiable]
        have h1s : Differentiable ℂ (fun s : ℂ => 1 - s) := by fun_prop
        exact hE_entire.comp h1s
      · filter_upwards [eventually_ne_nhds (show (2 : ℂ) ≠ 0 by norm_num),
          eventually_ne_nhds (show (2 : ℂ) ≠ 1 by norm_num)] with s hs0 hs1
        have h1s0 : (1 : ℂ) - s ≠ 0 := fun h => hs1 (sub_eq_zero.mp h).symm
        have h1s1 : (1 : ℂ) - s ≠ 1 := by
          intro h
          refine hs0 ?_
          have h1 : -s = 0 := by
            calc -s = (1 - s) - 1 := by ring
              _ = 1 - 1 := by rw [h]
              _ = 0 := by ring
          simpa using neg_eq_zero.mp h1
        rw [hE_eq s hs0 hs1, hE_eq (1 - s) h1s0 h1s1, hFE s hs0 hs1]
        ring
    intro s
    exact congrFun hEq s

  have hbase : (((|NumberField.discr F| : ℤ) : ℂ) *
      (Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℂ)) = (principalDiscriminant F : ℂ) := by
    rw [Ideal.absNorm_top, Nat.cast_one, mul_one, principalDiscriminant,
      ← Complex.ofReal_intCast]
  have hdir : ∀ s : ℂ, 1 < s.re →
      Λ s = (principalDiscriminant F : ℂ) ^ (s / 2) *
        Complex.Gammaℂ s ^ principalComplexPlaces F *
          (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) := by
    intro s hs
    have hg : ∀ I : Ideal (𝓞 F),
        principalCharacter F I * (Ideal.absNorm I : ℂ) ^ (-s) =
          (if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) := by
      intro I
      by_cases hI : I = ⊥ <;> simp [principalCharacter_apply, hI]
    have hseries' : HasSum (fun I : Ideal (𝓞 F) =>
        ((((|NumberField.discr F| : ℤ) : ℂ) *
          (Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ principalComplexPlaces F) *
        (if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s))) (Λ s) :=
      (hseries s hs).congr_fun fun I => by
        rw [principalComplexPlaces, ← hg I]
    rw [← hseries'.tsum_eq, tsum_mul_left, hbase]
  exact ⟨(show PrincipalHeckeData F from
    { Lambda := Λ, E := E,
      E_differentiable := hE_entire,
      Lambda_functional_equation := hFE, E_eq_mul_Lambda := hE_eq, E_growth := hgrowth,
      E_functional_equation := hEfun, Lambda_eq_div := hΛdiv,
       Lambda_dirichlet := hdir})⟩

def principalHeckeData :
    PrincipalHeckeData F :=
  Classical.choice (exists_principalHeckeData F hF)

def principalPoleCoefficient : ℂ :=
  (principalHeckeData F hF).E 1

end DedekindZetaZeroFree.LargeSieve

end
