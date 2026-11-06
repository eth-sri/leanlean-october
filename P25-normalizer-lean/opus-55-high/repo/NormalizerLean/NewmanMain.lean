module

public import NormalizerLean.NewmanFacts
public import NormalizerLean.NewmanLocal

@[expose] public section

/-!
# T2: Newman's theorem

Every g ∈ Norm(Γ₀(N)) has the form (8′).  Write g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ
coprime (`exists_prim_form`), e = αδ − βγ.  The divisibilities F1–F12 (for g and g⁻¹, and with
s = t − x from the element γ_p of Lemma 3) give, at every prime p, the valuation inequalities of
`local_form`, whose conclusion says: either v_p(e) = 0 and p^{v_p(n)} ∣ γ, or v_p(e) = v_p(n) and
p^{v_p(n)} divides α, γ, δ.  Hence e ∣ n, n ∣ γ, e ∣ α, e ∣ δ, which is (8′).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem dvd_of_forall_vz_le {m x : ℤ} (hm : m ≠ 0) (hx : x ≠ 0)
    (h : ∀ p : ℕ, p.Prime → vz p m ≤ vz p x) : m ∣ x := by
  rw [← Int.natAbs_dvd_natAbs]
  rw [← Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.2 hm) (Int.natAbs_ne_zero.2 hx)]
  intro p
  by_cases hp : p.Prime
  · exact h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end

end NormalizerLean
