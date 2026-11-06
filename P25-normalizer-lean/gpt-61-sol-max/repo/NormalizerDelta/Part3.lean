module

public import NormalizerLean.Defs

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

open Matrix
attribute [local simp ←] Matrix.ext_iff

namespace NormalizerLean

/-! # Normalizers, their Newman forms, and the finite coset count -/

variable {N : ℕ}

/-- The p-adic multiplicity, including infinity at zero. -/
notation "vz" => @emultiplicity ℤ _

abbrev latticeMap (N : ℤ) :=
  (Int.castAddHom ℝ).toIntLinearMap.mapMatrix.comp
    (AddMonoidHom.mk' (hadamard !![1, 1; N, 1]) (hadamard_add _ · ·)).toIntLinearMap

abbrev conjMap g :=
  LinearMap.mulLeftRight ℝ (↑ₘg, (↑ₘg).adjugate)

abbrev InLe N M := M ∈ LinearMap.range (latticeMap N)

theorem InLe.int_entries {M} : InLe N M → ∀ i j, M i j ∈ (Int.castRingHom ℝ).range := by
  rintro ⟨v, rfl⟩
  simp [-Int.cast_mul]

theorem InLe.vz {M} (e B C : ℤ)
    : InLe N M → (↑e * M 0 1 = B ∧ ↑e * M 1 0 = C) →
    ∀ p : ℕ, vz p e ≤ vz p B ∧ vz p (e * N) ≤ vz p C := by
  rintro ⟨v, rfl⟩ H
  simp [← mul_assoc] at H
  norm_cast at H
  aesop (add safe emultiplicity_le_emultiplicity_of_dvd_right)

theorem factorization_24 :
    Nat.factorization 24 = Finsupp.single 2 3 + Finsupp.single 3 1 := by
  ext p
  norm_num [Nat.factorization]
  grind

variable [NeZero N] {Δ : Subgroup (ZMod N)ˣ}

local notation "Γ" => GammaDeltaR N Δ
local notation "Γ₀" => Gamma0R N
local notation "η" => hDelta N Δ
local notation "MΔ" => MDelta N Δ
local notation "εΔ" => epsDelta N Δ
local notation "ν" => nDelta N Δ
local notation "𝒩" => NormG Γ

theorem dvd_epsDelta_iff {m} :
    m ∣ εΔ ↔ m ∣ N ∧ ∀ u ∈ Δ, (m : ℤ) ∣ ↑u.val.val ^ 2 - 1 := by
  simp [epsDelta, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]
  intro
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt (NeZero.pos N)) with rfl | hN
  · simp_all
  have : Fact (1 < N) := ⟨hN⟩
  apply forall₂_congr
  intro u hu
  zify [Nat.one_le_pow _ _ (ZMod.val_pos.mpr u.ne_zero), ZMod.cast_eq_val]

instance epsDelta_neZero : NeZero εΔ :=
  ⟨by simp [epsDelta]⟩

variable (N Δ)

instance hDelta_neZero : NeZero η :=
  ⟨by simp +contextual [hDelta, Finset.prod_ne_zero_iff]⟩

theorem factorization_hDelta p :
    Nat.factorization η p =
      min (Nat.factorization εΔ p) (N.factorization p / 2) := by
  rw [hDelta, Nat.factorization_prod_apply (Finset.prod_ne_zero_iff.mp (NeZero.ne η)),
    Finset.sum_congr rfl (fun q hq => by
    rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow])]
  simp_all [← Nat.support_factorization]

attribute [simp] factorization_24 factorization_hDelta

theorem nDelta_mul :
    ν * η ^ 2 = N := by
  apply Nat.div_mul_cancel
  rw [← Nat.factorization_le_iff_dvd (by simp) (NeZero.ne N)]
  intro
  simp
  omega

instance nDelta_neZero : NeZero ν :=
  ⟨by nlinarith [nDelta_mul N Δ, NeZero.pos N]⟩

section
omit [NeZero N]
variable {N Δ}

theorem GammaDelta_subgroupOf :
    (GammaDelta N Δ).subgroupOf (CongruenceSubgroup.Gamma0 N) = Δ.comap (unitMap N) := by
  ext γ
  change (_ ∧ ∃ u ∈ Δ, u.val = (unitMap N γ).val) ↔ _
  norm_cast
  simp

theorem Gamma0R_le_normG_GammaDeltaR' :
    Γ₀ ≤ 𝒩 := by
  apply le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer Set.inter_subset_left,
    GammaDelta_subgroupOf]
  infer_instance

/-- Normalize matrix entries, clear denominators, and discharge the polynomial identities. -/
macro "matrix_calc" hs:(colGt ident)* : tactic => `(tactic|
  simp [$[$hs:ident],*] <;> field_simp <;> grind)

theorem conj_InLe {g Y} (hg : g ∈ 𝒩) (hY : Y ∈ Γ) :
    InLe N (conjMap g ↑ₘY) := by
  obtain ⟨γ, hγ, heq⟩ := (hg Y).mp hY
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    (CongruenceSubgroup.Gamma0_mem.mp hγ.1)
  refine ⟨!![γ 0 0, γ 0 1; k, γ 1 1], ?_⟩
  simpa [hk] using congrArg Subtype.val heq

end

/-- The Atkin–Lehner elements of level N form a subgroup. -/
def alSub : Subgroup SL₂ ℝ where
  carrier := {g | ∃ Q, Q ∣ N ∧ IsAtkinLehner N Q g}
  one_mem' := ⟨1, one_dvd N, 1, 0, 0, 1, by simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨Q₁, hQ₁, x₁, y₁, z₁, w₁, hd₁, hg₁⟩
      ⟨Q₂, hQ₂, x₂, y₂, z₂, w₂, hd₂, hg₂⟩
    set G := Nat.gcd Q₁ Q₂
    have hG0 : 0 < G := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos hQ₁ (NeZero.pos N))
    obtain ⟨q₁, hq₁⟩ : G ∣ Q₁ := Nat.gcd_dvd_left Q₁ Q₂
    obtain ⟨q₂, hq₂⟩ : G ∣ Q₂ := Nat.gcd_dvd_right Q₁ Q₂
    obtain ⟨L, hLN⟩ : G * q₁ * q₂ ∣ N := by
      convert Nat.lcm_dvd hQ₁ hQ₂ using 1
      nlinarith [Nat.gcd_mul_lcm Q₁ Q₂, congrArg₂ HMul.hMul hq₁ hq₂]
    refine ⟨q₁ * q₂, ⟨G * L, by grind⟩, G * x₁ * x₂ + L * y₁ * z₂, q₁ * x₁ * y₂ + q₂ * y₁ * w₂, q₂ * z₁ * x₂ + q₁ * w₁ * z₂,
      L * z₁ * y₂ + G * w₁ * w₂, ?_, ?_⟩
    · apply mul_left_cancel₀ (show (G : ℤ) ^ 2 ≠ 0 by positivity)
      push_cast [hLN, hq₁, hq₂] at hd₁ hd₂ ⊢
      grind
    · matrix_calc hg₁ hg₂ hLN hq₁ hq₂
  inv_mem' := by
    rintro g ⟨Q, hQ, x, y, z, w, hdet, hgm⟩
    exact ⟨Q, hQ, w, -y, -z, x, by
      simp [hgm]
      nlinarith⟩

variable {N Δ}

theorem mem_MDelta_iff {g} :
    g ∈ MΔ ↔ IsNewmanFormH N η g := by
  have hNr := (nDelta_mul N Δ).symm
  rify at hNr
  erw [MDelta, Subgroup.mem_map_equiv, Gamma0Plus, Subgroup.closure_eq (alSub ν)]
  dsimp only [nDelta] at hNr ⊢
  simp only [MulAut.conj_symm_apply, inv_inv, ← MulAut.conj_apply]
  have hc : ↑ₘ(MulAut.conj (projSL !![η, 0; 0, 1]) g) =
      !![g 0 0, η * g 0 1; g 1 0 / η, g 1 1] := by
    matrix_calc MulAut.conj_apply projSL funext_iff
  constructor
  · rintro ⟨Q, hQ, x, y, z, w', hdet, hwm⟩
    refine ⟨x, y, z, w', Q, Nat.pos_of_dvd_of_pos hQ (NeZero.pos ν), hQ, by
      nlinarith, 1, Or.inl rfl, ?_⟩
    rw [hc] at hwm
    simp [hNr] at hwm ⊢
    field_simp at hwm ⊢
    grind
  · rintro ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩
    rw [hgm] at hc
    refine ⟨e, he, ?_⟩
    rcases hε with rfl | rfl
    case' inl => refine ⟨a, b, c, d, by nlinarith, ?_⟩
    case' inr => refine ⟨-a, -b, -c, -d, by nlinarith, ?_⟩
    all_goals
      rw [hc]
      matrix_calc hNr

variable (N Δ)

theorem coe_MDelta :
    ↑MΔ = {g | IsNewmanFormH N η g} :=
  Set.ext fun _ => mem_MDelta_iff

/-- Newman's primitive-lattice argument, with the sharp parameter `η`. -/
theorem normG_GammaDeltaR_le_MDelta :
    𝒩 ≤ MΔ := by
  intro g hg
  apply mem_MDelta_iff.2
  obtain ⟨P12, P21, P11⟩ :
    InLe N (conjMap g (single 0 1 1)) ∧
      InLe N (N • conjMap g (single 1 0 1)) ∧
      InLe N (N • conjMap g (single 0 0 1)) := by
    have H (b c : ℤ) : InLe N (conjMap g
        ↑ᶻ(⟨!![1 + b * N * c, b; N * c, 1], by simp [mul_assoc]⟩)) :=
      conj_InLe hg (Subgroup.mem_map_of_mem _ ⟨by simp, 1, Subgroup.one_mem _, by simp⟩)
    have D b c := sub_mem (H b c) (H 0 0)
    convert And.intro (D 1 0) (And.intro (D 0 1)
      (sub_mem (sub_mem (D 1 1) (D 1 0)) (D 0 1))) using 2
    all_goals
      simp only [← map_sub, ← map_nsmul]
      congr! 2
      simp
  have hNr := nDelta_mul N Δ
  obtain ⟨t, ht, hM⟩ : ∃ t, t ≠ 0 ∧ ∀ i j, t * g i j ∈ (Int.castRingHom ℝ).range := by
    have h12 := InLe.int_entries (Submodule.smul_mem _ ↑N P12)
    have h22 := P11.int_entries
    simp [adjugate_fin_two, mul_assoc, -RingHom.mem_range] at h12 h22
    obtain hx | hx := (g.isCoprime_col 0).ne_zero_or_ne_zero
    all_goals
      refine ⟨_, mul_ne_zero (NeZero.ne (N : ℝ)) hx, ?_⟩
      simp_all [mul_comm, mul_left_comm, -RingHom.mem_range]

  choose A hA using hM
  simp at hA
  let M := ![η * A 0 0, η ^ 2 * A 0 1, A 1 0, η * A 1 1]
  obtain ⟨α, β, γ, δ, hv, hprim⟩ := by
    simpa using Finset.extract_gcd M Finset.univ_nonempty
  let κ := ↑(Finset.univ.gcd M) / (η * t)
  have hgm : ↑ₘg = κ • !![(α : ℝ), β / η; η * γ, δ] := by
    rify at hv
    simp [M, hA] at hv
    matrix_calc κ M

  set E := α * δ - β * γ with h1
  have hdet : κ ^ 2 * E = 1 := by
    convert g.2 using 1
    matrix_calc h1 hgm

  have hepos : 0 < E := by
    rify
    nlinarith
  have := NeZero.mk hepos.ne'
  have hloc p (hp : Nat.Prime p) :
      vz p E ≤ vz p ν ∧
        vz p ν ≤ vz p γ ∧
        vz p E ≤ vz p α ∧ vz p E ≤ vz p δ := by
    have := congr(Nat.factorization $hNr p)
    rify at hNr
    have := P12.vz E (α ^ 2) (-(η ^ 2 * γ ^ 2)) (by
        matrix_calc hgm) p
    have := P21.vz E (-(ν * β ^ 2)) (N * δ ^ 2) (by
        matrix_calc hgm) p
    have hp' := Nat.prime_iff_prime_int.1 hp
    have prim := by simpa only [← hprim, dvd_gcd_iff, dvd_normalize_iff, not_and_or, ← emultiplicity_eq_zero] using hp'.not_dvd_one
    have := min_le_emultiplicity_add (p := ↑p) (a := α * δ) (b := -β * γ)
    by_cases hj : Nat.factorization εΔ p < N.factorization p
    case' pos =>
      obtain ⟨γp, hγN, hvs⟩ :
        ∃ γ : GammaDelta N Δ, γ.val 1 0 = N ∧
          vz p (γ.val 1 1 - γ.val 0 0) ≤ Nat.factorization εΔ p
          := by
        set j := Nat.factorization εΔ p
        have hpN' : p ^ (j + 1) ∣ N := (hp.pow_dvd_iff_le_factorization (NeZero.ne N)).2 (by omega)
        -- some u ∈ Δ with p^{j+1} ∤ val(u)² − 1
        have hnd := Nat.pow_succ_factorization_not_dvd (NeZero.ne εΔ) hp
        rw [dvd_epsDelta_iff] at hnd
        push Not at hnd
        obtain ⟨u, hu, hnd⟩ := hnd hpN'
        obtain ⟨γ, hc, hd⟩ := (ZMod.val_coe_unit_coprime u).symm.isCoprime.exists_SL2_row 1
        refine ⟨⟨γ, ⟨by simp [hc], u, hu, by simp [hd]⟩⟩, hc, ?_⟩
        simp only [hd]
        zify at hnd hpN'
        rw [← ENat.lt_natCast_add_one_iff, ← Nat.cast_succ, emultiplicity_lt_iff_not_dvd]
        intro H
        apply hnd
        convert dvd_add (dvd_mul_of_dvd_right H u.val.val) (dvd_mul_of_dvd_right hpN' (γ 0 1)) using 1
        grind [γ.2, det_fin_two]
      let s := γp.val 1 1 - γp.val 0 0
      have P : InLe N (s • conjMap g (single 1 1 1)) := by
        have h1 := conj_InLe hg (one_mem Γ)
        have hP := conj_InLe hg (Subgroup.mem_map_of_mem _ γp.property)
        convert sub_mem (sub_mem (sub_mem hP (Submodule.smul_mem _ (γp.val 0 0) h1))
          (Submodule.smul_mem _ (γp.val 0 1) P12)) P21 using 1
        simp only [← map_zsmul, ← map_nsmul, ← map_sub]
        congr 1
        simp [s, hγN]
      have := P.vz (E * η) (s * (α * β)) (-(s * η ^ 2 * (γ * δ))) (by
          matrix_calc hgm) p
    all_goals
      simp_all [← sub_eq_add_neg, emultiplicity_mul hp', emultiplicity_pow hp',
        Int.natCast_emultiplicity, ← padicValNat_eq_emultiplicity_of_ne_one hp.ne_one, ← Nat.factorization_def]
      try generalize vz p s = l at *
      iterate 5 generalize vz p _ = v at *
      enat_to_nat <;> simp_all <;> omega

  obtain ⟨hen, ⟨c', hc'⟩, ⟨a', ha'⟩, ⟨d', hd'⟩⟩ :
      E ∣ ν ∧ ↑ν ∣ γ ∧
        E ∣ α ∧ E ∣ δ := by
    and_intros
    all_goals
      apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (NeZero.ne _)).2
      intro p hp
      grind [Int.prime_iff_natAbs_prime, emultiplicity_eq_of_associated_left,
        Int.associated_natAbs p]
  lift E to ℕ using hepos.le with e
  norm_cast at hepos
  refine ⟨a', β, c', d', e, hepos, ?_, ?_, κ * Real.sqrt e, ?_, ?_⟩
  · assumption_mod_cast
  · rw [ha', hd', hc'] at h1
    simp [nDelta] at h1 ⊢
    nlinarith
  · simpa [← sq_eq_one_iff, mul_pow] using hdet
  · rify at *
    matrix_calc hgm ha' hd' hc'

theorem Gamma0R_le_MDelta : Γ₀ ≤ MΔ :=
  Gamma0R_le_normG_GammaDeltaR'.trans (normG_GammaDeltaR_le_MDelta N Δ)

/-!
# §H: h_Δ = h(N) unless one of the cases i)–iii) of `hDelta_eq_hPart_iff`, and conversely

Prime by prime: v_p(h_Δ) = min(v_p(ε_Δ), ⌊v_p(N)/2⌋) and v_p(h(N)) = min(v_p(gcd(N, 24)), ⌊v_p(N)/2⌋), with
v_p(gcd(N, 24)) ≤ v_p(ε_Δ) ≤ v_p(N).  So v_p(h_Δ) ≠ v_p(h(N)) iff
* p ≥ 5: p² ∣ N and p ∣ ε_Δ;   * p = 3: 3⁴ ∣ N and 9 ∣ ε_Δ;   * p = 2: 2⁸ ∣ N and 16 ∣ ε_Δ
(`omega`), and m ∣ ε_Δ iff m ∣ d² − 1 for all d ∈ Δ, where p ∣ d² − 1 ⟺ d ≡ ±1 (p), 9 ∣ d² − 1 ⟺ d ≡ ±1 (9),
16 ∣ d² − 1 ⟺ d ≡ ±1 (8) (`decide` on ℤ/9, ℤ/16).
-/

variable {N}

lemma unit_sq24 {m} (hm : m ∣ 24) : ∀ u : (ZMod m)ˣ, (u : ZMod m) ^ 2 = 1 := by
  have := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> norm_num at hm <;> decide

/- Every residue in Δ is ±1 modulo the given modulus. -/
set_option quotPrecheck false
local notation "AllPm" m:max => ∀ d ∈ Δ, IsPmOneMod m d

variable (N) in
theorem hDelta_eq_hPart_iff :
    η = hPart N ↔
      ¬ ((∃ p, Nat.Prime p ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ AllPm p) ∨
        (3 ^ 4 ∣ N ∧ AllPm 9) ∨
        (2 ^ 8 ∣ N ∧ AllPm 8)) := by
  rw [Nat.eq_iff_prime_padicValNat_eq _ _ (NeZero.ne _) (by
    unfold hPart
    positivity)]
  simp_rw +contextual [← Nat.factorization_def, ← not_ne_iff, ← not_and, ← not_exists]
  apply not_congr
  trans ∃ p : ℕ, p.Prime ∧
    ((5 ≤ p ∧ p ^ 2 ∣ N ∧ AllPm p) ∨
      (p = 3 ∧ 3 ^ 4 ∣ N ∧ AllPm 9) ∨
      (p = 2 ∧ 2 ^ 8 ∣ N ∧ AllPm 8))
  · apply exists_congr
    intro p
    apply and_congr_right
    intro hp
    have hN := NeZero.ne N
    have hle := (Nat.factorization_le_iff_dvd
      (Nat.gcd_ne_zero_left (n := 24) hN) (NeZero.ne εΔ)).2 (by
        refine dvd_epsDelta_iff.2 ⟨Nat.gcd_dvd_left _ _, fun u _ => ?_⟩
        simpa [← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_zero, ZMod.unitsMap_val] using
          unit_sq24 (Nat.gcd_dvd_right N 24) (ZMod.unitsMap (Nat.gcd_dvd_left N 24) u)) p
    simp [Nat.factorization_gcd hN (NeZero.ne 24)] at hle
    have criterion (k m) (hk : Nat.factorization 24 p = k)
        (hiff : ∀ x : ℕ, (x : ZMod (p ^ (k + 1))) ^ 2 = 1 ↔
          (x : ZMod m) = 1 ∨ (x : ZMod m) = -1) :
        Nat.factorization η p ≠ (hPart N).factorization p ↔
          p ^ (2 * (k + 1)) ∣ N ∧ AllPm m := by
      trans p ^ (2 * (k + 1)) ∣ N ∧ p ^ (k + 1) ∣ εΔ
      · norm_num [hp.pow_dvd_iff_le_factorization hN, hp.pow_dvd_iff_le_factorization (NeZero.ne εΔ),
          hPart, -Nat.factorization_def] at hle hk ⊢
        grind
      · apply and_congr_right
        intro hn
        simp only [dvd_epsDelta_iff, (pow_dvd_pow p (by omega : k + 1 ≤ 2 * (k + 1))).trans hn, true_and]
        simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, IsPmOneMod, ZMod.cast_eq_val]
        push_cast
        simp_rw [sub_eq_zero, hiff]
    have : Fact p.Prime := ⟨hp⟩
    by_cases h2 : p = 2
    · subst p
      simpa using (criterion 3 8 (by simp) (by
        intro x
        rw [← map_natCast (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8))]
        generalize (x : ZMod 16) = y
        decide +revert))
    by_cases h3 : p = 3
    · subst p
      simpa using (criterion 1 9 (by simp) (by
        intro x
        generalize (x : ZMod 9) = y
        decide +revert))
    · have h5 := hp.five_le_of_ne_two_of_ne_three h2 h3
      simpa [h5, h2, h3] using criterion 0 p (by simp_all) (by
        rw [pow_one]
        simp [sq_eq_one_iff])
  · simp [and_or_left, exists_or, Nat.prime_two, Nat.prime_three]

/-! ### Hermite normal form and existence of σH -/

variable {R : Set SL₂ ℤ} (hR : IsGamma0Reps N R)

include hR in
theorem exists_sigmaH {g} (hg : g ∈ MΔ) :
    ∃ γ ∈ Γ₀, ∃ r ∈ R, ∃ a b d, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ↑ₘ(γ * g) =
        c • (↑ᶻr * hermMat a b d) := by
  obtain ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩ := mem_MDelta_iff.1 hg
  set h := η
  have hh := NeZero.pos h
  set A := Int.gcd (a * e * h) (N * c)
  have hA : 0 < A := by
    grind [Int.gcd_pos_iff, mul_eq_zero, NeZero.ne N]
  obtain ⟨p, q, hpq, hp, hq⟩ := Int.exists_gcd_one hA
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hpq
  set δ := p * (d * e * h) - q * b with hδdef
  have hAD : A * δ = h ^ 2 * e := by
    have := nDelta_mul N Δ
    zify [nDelta] at this
    grind
  have hδ : 0 < δ := by nlinarith
  set β := u * b + v * (d * e * h)
  set k := β / δ
  set r := β % δ
  have hβ : δ * k + r = β := Int.mul_ediv_add_emod β δ
  have hBD : r < δ := Int.emod_lt_of_pos β hδ
  lift r to ℕ using Int.emod_nonneg β hδ.ne' with B
  lift δ to ℕ using hδ.le with D
  norm_cast at hAD hBD hδ
  let σ : SL₂ ℤ := ⟨!![p, p * k - v; q, q * k + u], by grind [det_fin_two_of]⟩
  have hWmat : !![(a * e * h : ℝ), b; N * c, d * e * h] = ↑ᶻσ * hermMat A B D := by
    simp [σ]
    norm_cast
    grind
  obtain ⟨A', B', D', ⟨hA', hB', hD'⟩, hprim⟩ := by
    simpa [gcd_eq_nat_gcd, ← Nat.gcd_assoc] using
      Finset.extract_gcd ![A, B, D] Finset.univ_nonempty
  set t := Nat.gcd (Nat.gcd A B) D
  obtain ⟨r, ⟨hrR, hσr⟩, -⟩ := hR σ
  set κ := ε / (Real.sqrt e * h)
  let γ := ofZ ((σ * r⁻¹)⁻¹)
  refine ⟨γ, Subgroup.mem_map_of_mem _ (inv_mem hσr), r, hrR, A', B', D', ?_, κ * t, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, hprim⟩ <;> try nlinarith
    apply dvd_trans (b := A * D)
    · exact ⟨t * t, by grind⟩
    · rw [hAD, ← nDelta_mul N Δ, mul_comm ν]
      exact mul_dvd_mul_left _ he
  · rcases hε with rfl | rfl <;> positivity
  · convert congr(↑ₘγ * (κ • $hWmat)) using 1
    · matrix_calc hgm κ
    · simp only [γ, Matrix.mul_smul, ← Matrix.mul_assoc,
        ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul]
      simp [hA', hB', hD']
      grind

/-! ### Uniqueness of σH -/

-- The unused `[NeZero N]` is part of the protected statement.
include hR in
theorem sigmaH_unique
    {r r'} (hr : r ∈ R) (hr' : r' ∈ R) {a b d a' b' d'}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') {c c' : ℝ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    {γ} (hγ : γ ∈ Γ₀)
    (h : c • (↑ᶻr * hermMat a b d) =
      ↑ₘγ * (c' • (↑ᶻr' * hermMat a' b' d')))
    :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  obtain ⟨ha, hd, -, hbd, hprim⟩ := hH
  obtain ⟨ha', hd', -, hbd', hprim'⟩ := hH'
  let M := r'⁻¹ * γ₀⁻¹ * r
  have key : c • (↑ᶻM * hermMat a b d) = c' • hermMat a' b' d' := by
    simpa [M, ← Matrix.mul_assoc,
      ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_assoc,
      -Matrix.mul_apply, -Matrix.SpecialLinearGroup.map_apply_coe] using
      congrArg (↑ᶻ(r'⁻¹ * γ₀⁻¹) * ·) h
  simp at key
  obtain ⟨⟨e00, e01⟩, e10, e11⟩ := key
  have hM10 : M 1 0 = 0 := by grind
  have hdetM := M.SL2_inv_expl_det
  simp [det_fin_two, hM10] at hdetM
  have hss := Int.eq_of_mul_eq_one hdetM
  simp_all only
  obtain ⟨Y1, Y2⟩ : ↑a * b' = (b + M 0 0 * M 0 1 * d) * a' ∧ (a : ℤ) * d' = d * a' := by
    rify at hdetM ⊢
    grind
  obtain rfl : a = a' := by
    have hg := congr(Int.gcd (Int.gcd (↑a * a') $Y1) $Y2)
    simpa [Int.gcd_mul_left, Int.gcd_mul_right, Int.gcd_assoc a, ← Nat.gcd_assoc, hprim, hprim'] using hg
  obtain rfl : d = d' := by nlinarith
  obtain rfl := (Nat.modEq_iff_dvd.mpr ⟨M 0 0 * M 0 1, by nlinarith⟩).eq_of_lt_of_lt hbd hbd'
  refine ⟨?_, by simp⟩
  have hcomm : r' * M = M * r' := by
    apply Subtype.ext
    simp [hM10]
    grind [mul_eq_zero]
  refine (hR r).unique ⟨hr, by simp⟩ ⟨hr', ?_⟩
  convert mul_mem hγ₀
    (show M ∈ _ by simp [hM10]) using 1
  simpa [M, mul_assoc] using congrArg (γ₀ * · * r'⁻¹) hcomm

/-! ### Sets of representatives -/

lemma reps_iff {N R} :
    IsGamma0Reps N R ↔ Subgroup.IsComplement (CongruenceSubgroup.Gamma0 N) R := by
  simp [Subgroup.isComplement_iff_existsUnique_mul_inv_mem, IsGamma0Reps,
    ExistsUnique, and_assoc, and_left_comm]

theorem exists_Gamma0Reps (N) : ∃ R, IsGamma0Reps N R :=
  ⟨_, reps_iff.mpr (Subgroup.isComplement_range_right Quotient.out_eq')⟩

/-! ### The pairs (σ, H) -/

/-- The normalized representative of a pair (σ, H). -/
abbrev sigmaH r a b d :=
  projSL (↑ᶻr * hermMat a b d)

variable (N R) (K : Subgroup SL₂ ℝ)

/- At the fixed level N, the pairs (σ, H) whose normalized matrix lies in K. -/
local notation "SigmaHSet" r:max k:max =>
  {x : SL₂ ℤ × ℕ × ℕ × ℕ // x.1 ∈ r ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
    projSL (↑ᶻx.1 * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈ k}

/-- The map (σ, H) ↦ (σH)⁻¹ Γ₀(N). -/
def sigmaHMap :
    SigmaHSet R K → K ⧸ Subgroup.subgroupOf Γ₀ K :=
  fun ⟨⟨r, a, b, d⟩, _, _, hk⟩ => QuotientGroup.mk ⟨sigmaH r a b d, hk⟩⁻¹

theorem coe_projSL_sigmaH {N} r {a b d} (hH : IsHermiteN N a b d) :
    ↑ₘ(sigmaH r a b d) =
      (Real.sqrt (a * d))⁻¹ • (↑ᶻr * hermMat a b d) := by
  simp [projSL, ← Int.cast_det,
    show (0 : ℝ) < a * d by positivity [hH.1, hH.2.1]]

variable {N R}

-- Keep the level and subgroup explicit so section-variable dependencies are retained.
variable {K} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ)

include hR hK0 hKM in
theorem sigmaHMap_surjective :
    Function.Surjective (sigmaHMap N R K) := by
  intro y
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨γ, hγ, r, hr, a, b, d, hH, c, hc, heq⟩ := exists_sigmaH Δ hR (hKM (inv_mem hk))
  set P := sigmaH r a b d
  have hPm := coe_projSL_sigmaH r hH
  rw [← inv_smul_eq_iff₀ hc] at heq
  rw [← heq, smul_smul] at hPm
  have hdet := congrArg Matrix.det hPm
  simp only [Matrix.SpecialLinearGroup.det_coe, det_smul, Fintype.card_fin, mul_one] at hdet
  have hPk : P * k ∈ Γ₀ := by
    rcases sq_eq_one_iff.mp hdet.symm with hu | hu
    case' inl => convert hγ using 1
    case' inr => convert (Γ₀).mul_mem ⟨-1, by simp, rfl⟩ hγ using 1
    all_goals
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, hPm, hu]
      simp [← Matrix.SpecialLinearGroup.coe_mul]
  refine ⟨⟨(r, a, b, d), hr, hH, (K.mul_mem_cancel_right hk).mp (hK0 hPk)⟩, QuotientGroup.eq.2 ?_⟩
  simpa using hPk

include hR in
theorem relIndex_normG_eq_card_sigmaH :
    Subgroup.relIndex Γ₀ 𝒩 =
      Nat.card (SigmaHSet R 𝒩) := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective _ ⟨?_, sigmaHMap_surjective Δ hR Gamma0R_le_normG_GammaDeltaR' (normG_GammaDeltaR_le_MDelta N Δ)⟩
  rintro ⟨⟨r, a, b, d⟩, hr, hH, _⟩ ⟨⟨r', a', b', d'⟩, hr', hH', _⟩ hxy
  simp [sigmaHMap, QuotientGroup.eq] at hxy
  ext1
  simp
  apply sigmaH_unique hR hr hr' hH hH'
    ?_ ?_ hxy
  · rw [← coe_projSL_sigmaH r hH, ← coe_projSL_sigmaH r' hH',
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  all_goals positivity [hH.1, hH.2.1, hH'.1, hH'.2.1]

/-! ### Finiteness and the index -/

variable (N)

theorem relIndex_Gamma0R_MDelta_ne_zero :
    Subgroup.relIndex Γ₀ MΔ ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_Gamma0Reps N
  have : Finite (SigmaHSet R MΔ) := by
    apply Set.Finite.to_subtype
    have hb := Set.finite_Iic N
    refine ((reps_iff.mp hR).finite_right.prod (hb.prod (hb.prod hb))).subset ?_
    rintro ⟨r, a, b, d⟩ ⟨hr, ⟨ha, hd, hadN, hbd, -⟩, -⟩
    have := Nat.le_of_dvd (NeZero.pos N) hadN
    simp_all
    and_intros <;> nlinarith

  exact Subgroup.index_ne_zero_iff_finite.2 (Finite.of_surjective _
    (sigmaHMap_surjective Δ hR (Gamma0R_le_MDelta N Δ) le_rfl))

theorem card_BG_GammaDeltaR_eq :
    Nat.card (BG Γ) = Δ.index * Subgroup.relIndex Γ₀ 𝒩 := by
  rw [← Subgroup.index, ← Subgroup.relIndex, ← Subgroup.relIndex_mul_relIndex Γ _ _
    (Subgroup.map_mono Set.inter_subset_left) Gamma0R_le_normG_GammaDeltaR', GammaDeltaR, toR, Gamma0R,
    Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.map_intCast_injective,
    Subgroup.relIndex, GammaDelta_subgroupOf, Subgroup.index_comap_of_surjective _ (by
      intro u
      obtain ⟨g, hc, hd⟩ := (ZMod.val_coe_unit_coprime u).symm.isCoprime.exists_SL2_row 1
      refine ⟨⟨g, by simp [hc]⟩, Units.ext ?_⟩
      simp [unitMap, CongruenceSubgroup.Gamma0Map, hd])]

theorem finite_BG_GammaDeltaR :
    Finite (BG Γ) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_BG_GammaDeltaR_eq]
  exact mul_ne_zero Subgroup.index_ne_zero_of_finite (mt
    (Subgroup.relIndex_eq_zero_of_le_right (normG_GammaDeltaR_le_MDelta N Δ))
    (relIndex_Gamma0R_MDelta_ne_zero N Δ))

end NormalizerLean
