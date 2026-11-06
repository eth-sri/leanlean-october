module

public import GS.UnitaryLocalModel.MiddleFibres

@[expose] public section


/-!
# Fibres after an injective chart of the dephased unitary slice

These statements certify the nonlinear change from two middle matrices to a
centre and a difference. The local version requires injectivity only on the
chart domain and membership of all four arguments in that domain. Neither
version assumes or asserts the construction of the dephased slice chart.
-/
noncomputable section
namespace GS.UnitaryLocalModel

section
variable {d : ℕ}
def chartMiddle {κ : Type*} (ψ : (Fin d → ℝ) → (κ → ℂ))
    (c z : Fin d → ℝ) (u : AxisVector) : κ → CMat 2 :=
  fun j => middleBlock (ψ (c+z) j) (ψ (c-z) j) u

private theorem centre_difference_unique (c z c' z' : Fin d → ℝ)
    (hplus : c+z=c'+z') (hminus : c-z=c'-z') : c=c' ∧ z=z' := by
  grind

private theorem difference_zero (c z : Fin d → ℝ)
    (he : c+z=c-z) : z=0 := by
  grind

/-- Exact fibres of the nonlinear matrix parametrization, with the collapsed
zero sphere retained. No differentiability assumption is used in this lemma. -/
theorem chartMiddle_fibres_on {κ : Type*}
    (ψ : (Fin d → ℝ) → (κ → ℂ)) (U : Set (Fin d → ℝ)) (hψ : Set.InjOn ψ U)
    (c z c' z' : Fin d → ℝ) {u v : AxisVector}
    (hcp : c+z ∈ U) (hcm : c-z ∈ U)
    (hcp' : c'+z' ∈ U) (hcm' : c'-z' ∈ U)
    (hu : OnSphere u) (hv : OnSphere v) :
    chartMiddle ψ c z u = chartMiddle ψ c' z' v ↔
      c=c' ∧ sphereOuter u z = sphereOuter v z' := by
  constructor
  · intro h
    have he := fun j => congrFun h j
    rcases (middleBlock_family_fibres _ _ _ _ hu hv).mp he with hz | hp | hn
    · have hz0 := difference_zero c z (by aesop)
      have hz'0 := difference_zero c' z' (by aesop)
      subst z
      subst z'
      have hc : c=c' := by aesop
      exact ⟨hc, sphereOuter_zero_fibre u v⟩
    · obtain ⟨hc,hz⟩ := centre_difference_unique c z c' z'
        (by aesop) (by aesop)
      grind
    · obtain ⟨huv,hplus,hminus⟩ := hn
      have hp : c+z=c'+(-z') := by
        aesop
      have hm : c-z=c'-(-z') := by aesop
      obtain ⟨hc,hz⟩ := centre_difference_unique c z c' (-z') hp hm
      rw [hc,huv,hz]
      exact ⟨rfl,sphereOuter_simultaneous_neg v z'⟩
  · rintro ⟨rfl,h⟩
    rcases (sphereOuter_fibres hu hv).mp h with hz | hp | hn
    · simp_all
      funext j
      simp [chartMiddle,middleBlock_equal]
    · grind
    · simp_all
      funext j
      simp only [chartMiddle,← sub_eq_add_neg,sub_neg_eq_add]
      exact middleBlock_simultaneous_swap _ _ _

end

end GS.UnitaryLocalModel
