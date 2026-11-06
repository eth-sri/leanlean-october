module

public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.FixedLevel

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section

def fullRaySector (N : ActualEisensteinCubic.O) (rows : Finset (Ideal ActualEisensteinCubic.O)) (r : ActualEisensteinCubic.O⧸Ideal.span {N^2}) : Finset (Ideal ActualEisensteinCubic.O) :=
  rows.filter (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r)

lemma sum_fullRaySectors {M : Type*} [AddCommMonoid M] (N : ActualEisensteinCubic.O)
    [Fintype (ActualEisensteinCubic.O⧸Ideal.span {N^2})] (rows : Finset (Ideal ActualEisensteinCubic.O)) (f : Ideal ActualEisensteinCubic.O→M) :
    (∑ r : ActualEisensteinCubic.O⧸Ideal.span {N^2}, ∑ K∈fullRaySector N rows r,f K)=∑ K∈rows,f K :=
  Finset.sum_fiberwise rows (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)) f

theorem full_ray_sector_energy (N : ActualEisensteinCubic.O) [Fintype (ActualEisensteinCubic.O⧸Ideal.span {N^2})]
    (rows Pset : Finset (Ideal ActualEisensteinCubic.O)) (f : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (E : ℝ)
    (hE : ∀ r p : ActualEisensteinCubic.O⧸Ideal.span {N^2},
      (∑ K∈fullRaySector N rows r, ‖∑ P∈fullRaySector N Pset p,f K P‖^2)≤E) :
    (∑ K∈rows,‖∑ P∈Pset,f K P‖^2)≤(Fintype.card (ActualEisensteinCubic.O⧸Ideal.span {N^2}):ℝ)^3*E := by
  rw [←sum_fullRaySectors N rows (fun K => ‖∑ P∈Pset,f K P‖^2)]
  calc
    _ ≤ ∑ r : ActualEisensteinCubic.O⧸Ideal.span {N^2}, (Fintype.card (ActualEisensteinCubic.O⧸Ideal.span {N^2}):ℝ)^2*E := by
      apply Finset.sum_le_sum
      intro r hr
      have hh := weighted_finite_row_energy_uniform (Finset.univ : Finset (ActualEisensteinCubic.O⧸Ideal.span {N^2}))
        (fullRaySector N rows r) (fun _ => (1:ℂ))
        (fun p K => ∑ P∈fullRaySector N Pset p,f K P) E (fun p _ => hE r p)
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
      have he : (∑ K∈fullRaySector N rows r, ‖∑ P∈Pset,f K P‖^2)=
          ∑ K∈fullRaySector N rows r, ‖∑ p : ActualEisensteinCubic.O⧸Ideal.span {N^2},∑ P∈fullRaySector N Pset p,f K P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [sum_fullRaySectors]
      linarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
end
end SevenEighths.InverseReflectedPhase

end OAI
