module
public import GafniTao.WooleySection7Congruence
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Extraction of Wooley's top congruences in Section 7

This file formalizes the passage from (7.6), after the source's first
integral change of equations, to (7.10).  The variables on the right lie on
the progression `p^b * t`; hence equation `j` on that side is divisible by
`p^(j*b)`.  For the top `r` equations this kills the right side modulo
`p^((k-r+1)*b)`.  The remaining left displacement is then exactly the
translated-and-dilated displacement used by the equation-(7.12) theorem.
-/

open Finset Polynomial

namespace GafniTao

noncomputable section

/-- The special first-phase normal form (7.7), with zero-based indices. -/
def wooleySection7NormalSystem
    (k p c : ℕ) (psi : WooleyPolynomialSystem k) :
    WooleyPolynomialSystem k := fun j =>
  X ^ ((j : ℕ) + 1) +
    C ((p : ℤ) ^ c) * X ^ (k + 1) * psi j

/-- The top `r` members of (7.7) are literally the system used in (7.10). -/
theorem wooleySection7NormalSystem_top
    {k r p c : ℕ} (hrk : r ≤ k) (psi : WooleyPolynomialSystem k)
    (l : Fin r) :
    wooleySection7NormalSystem k p c psi
        ⟨wooleySection7Node k r l,
          wooleySection7Node_succ_le hrk l⟩ =
      wooleySection7TopSystem k r p c
        (fun u => psi
          ⟨wooleySection7Node k r u,
            wooleySection7Node_succ_le hrk u⟩) l := by
  rfl

/-- Evaluation of equation `j` in the normal system on the progression
`p^b*t` is divisible by `p^(b*(j+1))`. -/
theorem wooleySection7NormalSystem_eval_progression_dvd
    {k p c b : ℕ} (psi : WooleyPolynomialSystem k)
    (j : Fin k) (t : ℤ) :
    (p : ℤ) ^ (b * ((j : ℕ) + 1)) ∣
      (wooleySection7NormalSystem k p c psi j).eval
        ((p : ℤ) ^ b * t) := by
  let d := (j : ℕ) + 1
  have hjk : d ≤ k := j.isLt
  have hfirst : (p : ℤ) ^ (b * d) ∣
      ((p : ℤ) ^ b * t) ^ d := by
    rw [mul_pow, pow_mul]
    simp_all
  have htailPow : (p : ℤ) ^ (b * d) ∣
      ((p : ℤ) ^ b * t) ^ (k + 1) := by
    have hle : b * d ≤ b * (k + 1) :=
      Nat.mul_le_mul_left b (hjk.trans (Nat.le_succ k))
    have hpowers : (p : ℤ) ^ (b * d) ∣
        (p : ℤ) ^ (b * (k + 1)) := pow_dvd_pow (p : ℤ) hle
    have hproduct : (p : ℤ) ^ (b * d) ∣
        (p : ℤ) ^ (b * (k + 1)) * t ^ (k + 1) :=
      dvd_mul_of_dvd_left hpowers _
    simpa only [mul_pow, pow_mul] using hproduct
  have htail : (p : ℤ) ^ (b * d) ∣
      (p : ℤ) ^ c * (((p : ℤ) ^ b * t) ^ (k + 1) *
        (psi j).eval ((p : ℤ) ^ b * t)) := by
    obtain ⟨z, hz⟩ := htailPow
    refine ⟨(p : ℤ) ^ c * z *
      (psi j).eval ((p : ℤ) ^ b * t), ?_⟩
    rw [hz]
    ring
  unfold wooleySection7NormalSystem
  pm_93 eval_add eval_pow eval_X eval_mul eval_C
  dsimp only [d] at hfirst htail ⊢
  exact dvd_add hfirst (by grind)

/-- Every equal-length tuple displacement on the right progression has the
same divisibility. -/
theorem wooleySection7NormalSystem_right_displacement_dvd
    {I : Type*} {k p c b S : ℕ}
    (psi : WooleyPolynomialSystem k) (j : Fin k) (point : I → ℤ)
    (xy : WooleyFiniteTuple S I × WooleyFiniteTuple S I) :
    (p : ℤ) ^ (b * ((j : ℕ) + 1)) ∣
      wooleyIntegerTupleDisplacement S
        (fun x => (wooleySection7NormalSystem k p c psi j).eval
          ((p : ℤ) ^ b * point x)) xy := by
  unfold wooleyIntegerTupleDisplacement
  apply dvd_sub
  · exact dvd_sum fun i _ =>
      wooleySection7NormalSystem_eval_progression_dvd psi j (point (xy.1 i))
  · exact dvd_sum fun i _ =>
      wooleySection7NormalSystem_eval_progression_dvd psi j (point (xy.2 i))

/-- Exact (7.6)-to-(7.10) implication for a system already in the source
normal form (7.7).  The input uses the genuine combined left-minus-right
Fourier displacement modulo `p^B`; the output is integral divisibility by
the precise retained modulus. -/
theorem wooleySection7_original_implies_top_congruences
    {I J : Type*} {k r p c a b B R S : ℕ}
    (hrk : r ≤ k) (hMB : (k - r + 1) * b ≤ B)
    (psi : WooleyPolynomialSystem k) (h : ℤ)
    (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (horiginal : ∀ j : Fin k,
      (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
          (fun x => (wooleySection7NormalSystem k p c psi j).eval
            ((p : ℤ) ^ a * leftPoint x + h)) leftXY -
        wooleyIntegerTupleDisplacement S
          (fun x => (wooleySection7NormalSystem k p c psi j).eval
            ((p : ℤ) ^ b * rightPoint x)) rightXY) :
    ∀ l : Fin r, (p : ℤ) ^ ((k - r + 1) * b) ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7TranslatedDilatedPolynomial p a h
            (wooleySection7TopSystem k r p c
              (fun u => psi
                ⟨wooleySection7Node k r u,
                  wooleySection7Node_succ_le hrk u⟩) l)).eval
              (leftPoint x)) leftXY := by
  intro l
  let j : Fin k :=
    ⟨wooleySection7Node k r l, wooleySection7Node_succ_le hrk l⟩
  pm_4916 M
  let leftDisp : ℤ := wooleyIntegerTupleDisplacement R
    (fun x => (wooleySection7NormalSystem k p c psi j).eval
      ((p : ℤ) ^ a * leftPoint x + h)) leftXY
  let rightDisp : ℤ := wooleyIntegerTupleDisplacement S
    (fun x => (wooleySection7NormalSystem k p c psi j).eval
      ((p : ℤ) ^ b * rightPoint x)) rightXY
  have hcombined : (p : ℤ) ^ M ∣ leftDisp - rightDisp :=
    dvd_trans (pow_dvd_pow (p : ℤ) hMB) (horiginal j)
  have hnode : k - r + 1 ≤ (j : ℕ) + 1 := by
    dsimp only [j, wooleySection7Node]
    omega
  have hrightStrong : (p : ℤ) ^ (b * ((j : ℕ) + 1)) ∣ rightDisp := by
    exact wooleySection7NormalSystem_right_displacement_dvd
      psi j rightPoint rightXY
  have hright : (p : ℤ) ^ M ∣ rightDisp := by
    apply dvd_trans (pow_dvd_pow (p : ℤ) ?_) hrightStrong
    dsimp only [M]
    nlinarith
  have hleft : (p : ℤ) ^ M ∣ leftDisp := by
    rw [show leftDisp = (leftDisp - rightDisp) + rightDisp by ring]
    exact dvd_add hcombined hright
  have htranslate :=
    wooleySection7TranslatedDilatedPolynomial_tupleDisplacement
      p a R h (wooleySection7NormalSystem k p c psi j)
        leftPoint leftXY
  have hnormal : wooleySection7NormalSystem k p c psi j =
      wooleySection7TopSystem k r p c
        (fun u => psi
          ⟨wooleySection7Node k r u,
            wooleySection7Node_succ_le hrk u⟩) l := by
    dsimp only [j]
    exact wooleySection7NormalSystem_top hrk psi l
  dsimp only [leftDisp] at hleft
  rw [hnormal] at hleft htranslate
  dsimp only [M] at hleft ⊢
  rw [htranslate] at hleft
  exact hleft

end

end GafniTao
