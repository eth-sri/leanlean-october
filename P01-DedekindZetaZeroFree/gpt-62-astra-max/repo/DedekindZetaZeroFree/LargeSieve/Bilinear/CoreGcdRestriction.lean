module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ConductorControlledRestriction
public import DedekindZetaZeroFree.LargeSieve.Bilinear.GcdTailAndMaskedShellBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient
open scoped NumberField Classical

theorem gcdPairTransport
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (hGood : CoreGood Q) (hc : c ≠ ⊥) :
    GcdPairTransport Q c := by
  intro d u v hd hu hv hdsf husf hvsf hdusf hdvsf hduc hdvc huv hduv hcls a ha hacd
  have hu_c : u ⊔ c = ⊤ := by
    have h :=
      sup_le_sup_right (Ideal.dvd_iff_le.mp (dvd_mul_left u d)) c
    rw [hduc] at h
    exact top_le_iff.mp h
  have hv_c : v ⊔ c = ⊤ := by
    have h :=
      sup_le_sup_right (Ideal.dvd_iff_le.mp (dvd_mul_left v d)) c
    rw [hdvc] at h
    exact top_le_iff.mp h
  rw [quadraticFamily_conj Q hdvsf hdvc a, quadraticFamily_conj Q hvsf hv_c a]

  have hzw : ∀ w : Ideal (𝓞 F), Squarefree w → w ⊔ c = ⊤ → a ⊔ w ≠ ⊤ → (Q.χ w) a = 0 := by
    intro w hwsf hwc haw
    rw [(Q.χ w).eq_zero_iff']
    refine Or.inr fun hcond => haw ?_
    have h := sup_le_sup_left (Ideal.dvd_iff_le.mp (hGood w hwsf hwc).1) a
    rw [hcond] at h
    exact top_le_iff.mp h
  by_cases huv_a : a ⊔ (u * v) = ⊤
  ·
    have hsup : d * u ⊔ d * v = d := by
      rw [← Ideal.mul_sup, huv]
      simp
    obtain ⟨-, htrans, -⟩ :=
      rawGcdPairTransport hc Q hdusf hdvsf hduc hdvc hcls (by rw [hsup]) (by rw [hsup])
    refine htrans a ha ?_
    have h1 : a ⊔ c = ⊤ := by
      have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (dvd_mul_right c d)) a
      rw [hacd] at h
      exact top_le_iff.mp h
    have hda : a ⊔ d = ⊤ := by
      have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (dvd_mul_left d c)) a
      rw [hacd] at h
      exact top_le_iff.mp h
    have hua : a ⊔ u = ⊤ := by
      have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (dvd_mul_right u v)) a
      rw [huv_a] at h
      exact top_le_iff.mp h
    have hva : a ⊔ v = ⊤ := by
      have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (dvd_mul_left v u)) a
      rw [huv_a] at h
      exact top_le_iff.mp h
    have h2 :=
      Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hda).mul_right (Ideal.isCoprime_iff_sup_eq.mpr hua))
    have h3 :=
      Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hda).mul_right (Ideal.isCoprime_iff_sup_eq.mpr hva))
    refine Ideal.isCoprime_iff_sup_eq.mp
      (((((((Ideal.isCoprime_iff_sup_eq.mpr h1).mul_right (Ideal.isCoprime_iff_sup_eq.mpr h2)).mul_right
        (Ideal.isCoprime_iff_sup_eq.mpr h3)).mul_right (Ideal.isCoprime_iff_sup_eq.mpr ?_)).mul_right
        (Ideal.isCoprime_iff_sup_eq.mpr ?_)).mul_right (Ideal.isCoprime_iff_sup_eq.mpr ?_)).mul_right
        (Ideal.isCoprime_iff_sup_eq.mpr ?_))
    · have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (hGood (d * u) hdusf hduc).2) a
      rw [(Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr h2).mul_right (Ideal.isCoprime_iff_sup_eq.mpr h1)))] at h
      exact top_le_iff.mp h
    · have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (hGood (d * v) hdvsf hdvc).2) a
      rw [(Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr h3).mul_right (Ideal.isCoprime_iff_sup_eq.mpr h1)))] at h
      exact top_le_iff.mp h
    · have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (hGood u husf hu_c).2) a
      rw [(Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hua).mul_right (Ideal.isCoprime_iff_sup_eq.mpr h1)))] at h
      exact top_le_iff.mp h
    · have h :=
        sup_le_sup_left (Ideal.dvd_iff_le.mp (hGood v hvsf hv_c).2) a
      rw [(Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hva).mul_right (Ideal.isCoprime_iff_sup_eq.mpr h1)))] at h
      exact top_le_iff.mp h
  ·
    have hua_or : a ⊔ u ≠ ⊤ ∨ a ⊔ v ≠ ⊤ := by
      by_contra hcon
      push Not at hcon
      exact huv_a (Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hcon.1).mul_right
          (Ideal.isCoprime_iff_sup_eq.mpr hcon.2)))
    rcases hua_or with hua | hva
    · have h2 :=
        hzw (d * u) hdusf hduc fun h => hua (by
          have hh := sup_le_sup_left (Ideal.dvd_iff_le.mp (dvd_mul_left u d)) a
          rw [h] at hh
          exact top_le_iff.mp hh)
      rw [h2, (hzw u husf hu_c hua), zero_mul, zero_mul]
    · have h2 :=
        hzw (d * v) hdvsf hdvc fun h => hva (by
          have hh := sup_le_sup_left (Ideal.dvd_iff_le.mp (dvd_mul_left v d)) a
          rw [h] at hh
          exact top_le_iff.mp hh)
      rw [h2, (hzw v hvsf hv_c hva), mul_zero, mul_zero]

theorem T3_eq_maskedGcdBlock_core
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hGood : CoreGood Q) (W : ℝ → ℝ)
    (M N K : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) :
    T3 F c Q W M N K d g lam =
      maskedGcdBlock F c Q W c M N K d g lam (fun _ => 1) (fun _ => 1) := by
  unfold T3 maskedGcdBlock
  apply Finset.sum_congr rfl
  intro b1 hb1
  apply Finset.sum_congr rfl
  intro b2 hb2
  by_cases h : b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g
  · rw [if_pos h, if_pos h]
    have hsum : (∑ a ∈ kernelRows F c M K,
        (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
          (starRingEnd ℂ) ((Q.χ b2) a)) =
      (∑ a ∈ kernelRows F c M K,
        if a ⊔ (c * d) = ⊤ then
          (W ((Ideal.absNorm a : ℝ) / M) * 1 : ℂ) * (Q.χ b1) a *
            (starRingEnd ℂ) ((Q.χ b2) a)
        else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hcond : a ⊔ (c * d) = ⊤
      · rw [if_pos hcond]; norm_num
      · rw [if_neg hcond]
        have ha' : a ∈ boundedNormIdeals F ((5 / 2) * M) ∧ a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ K < s a := by
          simpa only [kernelRows, Finset.mem_filter] using ha
        have hb1' := (mem_paperShell F c N b1).mp hb1
        have had : a ⊔ d ≠ ⊤ := fun hd_ => hcond (Ideal.isCoprime_iff_sup_eq.mp
            ((Ideal.isCoprime_iff_sup_eq.mpr ha'.2.2.1).mul_right
              (Ideal.isCoprime_iff_sup_eq.mpr hd_)))
        have hab1 : a ⊔ b1 ≠ ⊤ := by
          intro h_
          exact had (top_le_iff.mp (h_ ▸ (sup_le_sup_left (h.1 ▸ le_sup_left) a)))
        have hcondb1 : a ⊔ Q.cond b1 ≠ ⊤ := by
          intro hc_
          exact hab1 (top_le_iff.mp (hc_ ▸ sup_le_sup_left (Ideal.dvd_iff_le.mp (hGood b1 hb1'.1 hb1'.2.1).1) a))
        rw [(((Q.χ b1).eq_zero_iff' a).mpr (Or.inr hcondb1))]; ring
    rw [hsum]
    simp
  · rw [if_neg h, if_neg h]

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient

end
