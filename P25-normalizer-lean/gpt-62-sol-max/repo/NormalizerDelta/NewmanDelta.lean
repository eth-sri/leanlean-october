module

public import NormalizerDelta.Basic

@[expose] public section

/-! Newman's bound from the transvections and the diagonal differences in Γ. -/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

private def Smat (h : ℕ) (α β γ δ : ℤ) : Mat₂R :=
  !![(α : ℝ), (β : ℝ) / h; (h : ℝ) * γ, (δ : ℝ)]

private theorem det_Smat {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    (Smat h α β γ δ).det = ((α * δ - β * γ : ℤ) : ℝ) := by
  rw [Smat, det_fin_two_of]
  push_cast
  field_simp

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ} {g : SL(2, ℝ)}

local notation "Γ" => GammaDeltaR N Δ
/-- Integral matrices with lower-left entry divisible by N. -/
private def lattice (N : ℕ) : Subring Mat₂R :=
  ((blockTriangularSubalgebra ℤ (ZMod N) (id : Fin 2 → Fin 2)).toSubring.comap
    (Int.castRingHom (ZMod N)).mapMatrix).map castM

private theorem mem_lattice {A : Mat₂R} :
    A ∈ lattice N ↔ ∃ B : Mat₂Z, (N : ℤ) ∣ B 1 0 ∧ castM B = A := by
  simp [lattice, Subring.mem_map, BlockTriangular, Fin.forall_fin_two,
    RingHom.mapMatrix_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

private abbrev conjM (g : SL(2, ℝ)) : Mat₂R →+* Mat₂R :=
  MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct (SpecialLinearGroup.toGL g))

private abbrev conjLattice (N : ℕ) (g : SL(2, ℝ)) : Subring Mat₂R :=
  (lattice N).comap (conjM g)

private theorem lift_mem (hg : g ∈ NormG Γ) {a b c d : ℤ} (h : a * d - b * c = 1) (hc : (N : ℤ) ∣ c)
    {u : (ZMod N)ˣ} (hu : u ∈ Δ) (hd : (u : ZMod N) = (d : ZMod N)) :
    !![(a : ℝ), b; c, d] ∈ conjLattice N g := by
  let Y := ofZ (mkSL _ _ _ _ h)
  have hY : Y ∈ Γ := Subgroup.mem_map_of_mem _ ⟨gamma0_dvd.2 hc, u, hu, hd⟩
  obtain ⟨B, hB, e⟩ := GammaDeltaR_le_Gamma0R ((Subgroup.mem_normalizer_iff.1 hg Y).1 hY)
  exact mem_lattice.2 ⟨B, gamma0_dvd.1 hB, congrArg (fun v : SL(2, ℝ) => v.1) e⟩

private theorem conj_single (g : SL(2, ℝ)) (i j k l : Fin 2) (r : ℝ) :
    conjM g (single i j r) k l = g k i * r * g⁻¹ j l := by
  change ((g.1 * single i j r) * (g⁻¹ : SL(2, ℝ)).1) k l = _
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single]

private theorem det_form {h : ℕ} {κ : ℝ} {a b c d : ℤ} (hh : h ≠ 0)
    (hg : (g : Mat₂R) = κ • Smat h a b c d) : κ ^ 2 * ((a * d - b * c : ℤ) : ℝ) = 1 := by
  simpa only [hg, det_smul, Fintype.card_fin, det_Smat hh] using g.2

private theorem inv_form {h : ℕ} {κ : ℝ} {a b c d : ℤ} (hg : (g : Mat₂R) = κ • Smat h a b c d) :
    (↑(g⁻¹) : Mat₂R) = κ • Smat h d (-b) (-c) a := by
  rw [coe_inv_of_coe_eq_smul hg]
  simp [Smat, neg_div]

private theorem conj_form {h : ℕ} {κ : ℝ} {a b c d e : ℤ} (hh : h ≠ 0)
    (hg : (g : Mat₂R) = κ • Smat h a b c d) (he : e = a*d - b*c) (i j k l : Fin 2) (r : ℝ) :
    (e : ℝ) * conjM g (single i j r) k l = Smat h a b c d k i * r * Smat h d (-b) (-c) a j l := by
  have hd := det_form hh hg
  rw [← he] at hd
  rw [conj_single, hg, inv_form hg]
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (Smat h a b c d k i * r * Smat h d (-b) (-c) a j l) * hd

private theorem upper_dvd {A : Mat₂R} {e x : ℤ} (hA : A ∈ lattice N)
    (h : (e : ℝ) * A 0 1 = x) : e ∣ x := by
  obtain ⟨B, -, rfl⟩ := mem_lattice.1 hA
  change (e : ℝ) * (B 0 1 : ℝ) = _ at h
  exact ⟨B 0 1, by exact_mod_cast h.symm⟩

private theorem lower_dvd {A : Mat₂R} {e x : ℤ} (hA : A ∈ lattice N)
    (h : (e : ℝ) * A 1 0 = x) : e * N ∣ x := by
  obtain ⟨B, hB, rfl⟩ := mem_lattice.1 hA
  change (e : ℝ) * (B 1 0 : ℝ) = _ at h
  exact (mul_dvd_mul_left e hB).trans (dvd_of_eq (by exact_mod_cast h))

variable [NeZero N]

local notation "ε" => epsDelta N Δ
local notation "hΔ" => hDelta N Δ
local notation "n" => nDelta N Δ

/-- Conjugating the three test matrices by a normalizer element preserves the level lattice. -/
private theorem lattice_tests (hg : g ∈ NormG Γ) :
    single 0 1 (1 : ℝ) ∈ conjLattice N g ∧
    single 1 0 (N : ℝ) ∈ conjLattice N g ∧
    single 1 1 (epsDelta N Δ : ℝ) ∈ conjLattice N g := by
  let L := conjLattice N g
  -- The scalars sending the diagonal matrix unit into L form an ideal of ℤ.
  let I : Ideal ℤ := (L.toAddSubgroup.comap ((singleAddMonoidHom 1 1).comp (Int.castAddHom ℝ))).toIntSubmodule
  have h1 : (1 : Mat₂R) ∈ L := one_mem L
  let B : Mat₂R := single 0 1 1
  let C : Mat₂R := single 1 0 N
  have unip (b c : ℤ) (hbc : b * c = 0) (hc : (N : ℤ) ∣ c) :
      1 + single 0 1 (b : ℝ) + single 1 0 (c : ℝ) ∈ L := by
    have := lift_mem hg (a := 1) (b := b) (d := 1) (by simp [hbc]) hc (one_mem Δ) (by simp)
    convert this using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hT : 1 + B ∈ L := by simpa [B] using unip 1 0 (by simp) (dvd_zero _)
  have hU : 1 + C ∈ L := by simpa [C] using unip 0 N (by simp) dvd_rfl
  have hB := (add_mem_cancel_left h1).1 hT
  have hC := (add_mem_cancel_left h1).1 hU
  have hD : single 1 1 (N : ℝ) ∈ L := by simpa [B, C] using mul_mem hC hB
  refine ⟨hB, hC, ?_⟩
  have criterion (m : ℕ) : single 1 1 (m : ℝ) ∈ L ↔ (Submodule.IsPrincipal.generator I).natAbs ∣ m := by
    rw [← Int.cast_natCast]
    change (m : ℤ) ∈ I ↔ _
    rw [Submodule.IsPrincipal.mem_iff_generator_dvd, Int.dvd_natCast]
  apply (criterion _).2
  refine dvd_epsDelta_iff.2 ⟨(criterion N).1 hD, fun u hu => (criterion _).1 ?_⟩
  let v := (u : ZMod N).val
  by_cases hv : v = 0
  · simp [show (u : ZMod N).val = 0 from hv]
  obtain ⟨x, y, hdet⟩ := exists_lift_unit u
  change x * (v : ℤ) - y * N = 1 at hdet
  have hY := lift_mem hg hdet dvd_rfl hu (by simp [v])
  have e : (x : ℝ) * v - (y : ℝ) * N = 1 := by exact_mod_cast hdet
  have hv' : 1 ≤ v ^ 2 := Nat.one_le_pow _ _ (by omega)
  have H := add_mem (nsmul_mem (sub_mem (sub_mem (sub_mem hY (zsmul_mem h1 x))
    (zsmul_mem hB y)) hC) v) (zsmul_mem hD y)
  convert H using 1
  change single (1 : Fin 2) 1 ((v ^ 2 - 1 : ℕ) : ℝ) = _
  rw [Nat.cast_sub hv']
  simp only [← Nat.cast_smul_eq_nsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, Nat.cast_pow, Nat.cast_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [B, C]; linear_combination e

/-- A fixed nonzero entry of the inverse gives an integral rescaling, by conjugating the matrix units in column 1. -/
private theorem integral_scale (hg : g ∈ NormG Γ) :
    ∃ (s : ℝ) (A : Mat₂Z), s ≠ 0 ∧ s • (g : Mat₂R) = castM A := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, (g⁻¹ 1 j : ℝ) ≠ 0 := by
    by_contra! H
    exact (g⁻¹ : SL(2, ℝ)).row_ne_zero 1 (funext H)
  have h (i : Fin 2) : single i 1 (ε : ℝ) ∈ conjLattice N g := by
    fin_cases i
    · simpa [← Nat.cast_smul_eq_nsmul ℝ] using nsmul_mem (lattice_tests hg).1 ε
    · exact (lattice_tests hg).2.2
  choose C hC using fun i => mem_lattice.1 (h i)
  refine ⟨ε * g⁻¹ 1 j, Matrix.of fun i k => C k i j, mul_ne_zero (by have := (epsDelta_pos (N := N) (Δ := Δ)); positivity) hj, ?_⟩
  ext i k
  have e : conjM g (single k 1 (ε : ℝ)) i j = (C k i j : ℝ) :=
    congrArg (fun A : Mat₂R => A i j) (hC k).2.symm
  rw [conj_single] at e
  change (ε : ℝ) * g⁻¹ 1 j * g i k = C k i j
  linear_combination e

private abbrev Primitive (a b c d : ℤ) : Prop :=
  ∀ p : ℤ, Prime p → ¬ (p ∣ a ∧ p ∣ b ∧ p ∣ c ∧ p ∣ d)

private theorem exists_prim (hg : g ∈ NormG Γ) :
    ∃ (κ : ℝ) (a b c d : ℤ),
      Primitive a b c d ∧
      (g : Mat₂R) = κ • Smat hΔ a b c d := by
  obtain ⟨s, A, hs, hA⟩ := integral_scale hg
  let W : Mat₂Z := !![(hΔ : ℤ) * A 0 0, (hΔ : ℤ)^2 * A 0 1; A 1 0, (hΔ : ℤ) * A 1 1]
  let f : Fin 2 × Fin 2 → ℤ := fun i => W i.1 i.2
  obtain ⟨w, hw, hprim⟩ := Finset.extract_gcd f Finset.univ_nonempty
  let G := Finset.univ.gcd f
  let κ : ℝ := G / (hΔ * s)
  have e (i j : Fin 2) : W i j = G * w (i,j) := hw (i,j) (Finset.mem_univ _)
  have hh : (hΔ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hDelta_pos N Δ).ne'
  have hmat : (g : Mat₂R) = κ • Smat hΔ (w (0,0)) (w (0,1)) (w (1,0)) (w (1,1)) := by
    rw [← inv_smul_smul₀ hs (g : Mat₂R), hA, show κ = s⁻¹ * (G / hΔ) by dsimp [κ]; field_simp, ← smul_smul]
    congr 1
    have hW (i j : Fin 2) : (W i j : ℝ) = G * w (i,j) := by exact_mod_cast e i j
    ext i j
    have heq := hW i j
    fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, Smat] <;> field_simp <;>
      simp [W] at heq <;> linear_combination heq

  refine ⟨κ, _, _, _, _, ?_, hmat⟩
  rintro p hp ⟨ha, hb, hc, hd⟩
  have hdvd : (p : ℤ) ∣ Finset.univ.gcd w := by
    apply Finset.dvd_gcd
    rintro ⟨i,j⟩ -
    fin_cases i <;> fin_cases j <;> assumption
  rw [hprim] at hdvd
  exact hp.not_dvd_one hdvd

private theorem test_facts (hg : g ∈ NormG Γ) {κ : ℝ} {a b c d e : ℤ}
    (hf : (g : Mat₂R) = κ • Smat hΔ a b c d) (he : e = a * d - b * c) :
    e ∣ a ^ 2 ∧ e * N ∣ (hΔ : ℤ)^2 * c ^ 2 ∧ e ∣ (n : ℤ) * b ^ 2 ∧
      e * hΔ ∣ (ε : ℤ) * (a * b) ∧ e * N ∣ ((ε : ℤ) * hΔ) * (c * d) := by
  obtain ⟨h12, h21, hs⟩ := lattice_tests hg
  have hh := (hDelta_pos N Δ).ne'
  have H := conj_form hh hf he
  have hn : (N : ℝ) = (n : ℝ) * (hΔ : ℝ)^2 := by exact_mod_cast (nDelta_mul N Δ).symm
  refine ⟨upper_dvd h12 ?_, dvd_neg.1 (lower_dvd h12 (x := -_) ?_),
    dvd_neg.1 (upper_dvd h21 (x := -_) ?_), upper_dvd hs ?_, dvd_neg.1 (lower_dvd hs (x := -_) ?_)⟩
  · rw [H]; push_cast; simp [Smat, pow_two]
  · rw [H]; push_cast; simp [Smat]; ring
  · rw [H, hn]; push_cast; simp [Smat]; field_simp
  · push_cast; rw [mul_right_comm, H]; simp [Smat]; field_simp
  · rw [H]; push_cast; simp [Smat]; ring

attribute [local enat_to_nat_top] add_top

private theorem local_bounds (hg : g ∈ NormG Γ) {κ : ℝ}
    {a b c d : ℤ} (hf : (g : Mat₂R) = κ • Smat hΔ a b c d) {e : ℤ}
    (he' : e = a * d - b * c) (hprim : Primitive a b c d) {p : ℤ} (hp : Prime p) :
    emultiplicity p e ≤ emultiplicity p (n : ℤ) ∧ emultiplicity p (n : ℤ) ≤ emultiplicity p c ∧
      emultiplicity p e ≤ emultiplicity p a ∧ emultiplicity p e ≤ emultiplicity p d := by
  have hq := Int.prime_iff_natAbs_prime.1 hp
  have hcast (m : ℕ) (hm : m ≠ 0) : emultiplicity p (m : ℤ) = (m.factorization p.natAbs : ℕ∞) := by
    rw [← emultiplicity_eq_of_associated_left (Int.associated_natAbs p), Int.natCast_emultiplicity,
      Nat.factorization_def _ hq, padicValNat_eq_emultiplicity_of_ne_one hq.ne_one hm]
  have hN := congr($(nDelta_mul N Δ).factorization p.natAbs)
  rw [Nat.factorization_mul (NeZero.ne n) (pow_ne_zero _ (hDelta_pos N Δ).ne'),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hN
  have he'' : e = d * a - -b * -c := by linear_combination he'
  obtain ⟨F1, F2, F3, F5, F7⟩ := test_facts hg hf he'
  obtain ⟨F4, -, -, F6, F8⟩ := test_facts (inv_mem hg) (inv_form hf) he''
  let v := @emultiplicity ℤ _ p
  have mono {x y : ℤ} (H : x ∣ y) : v x ≤ v y := emultiplicity_le_emultiplicity_of_dvd_right H
  have H1 := mono F1
  have H2 := mono F2
  have H3 := mono F3
  have H4 := mono F4
  have H5 := mono F5
  have H6 := mono F6
  have H7 := mono F7
  have H8 := mono F8
  have lo : min (v (a * d)) (v (b * c)) ≤ v e := by
    simpa [v, he', sub_eq_add_neg] using (min_le_emultiplicity_add (p := p) (a := a*d) (b := -(b * c)))
  have hi : v (b * c) < v (a * d) → v e = v (b * c) := by
    rw [he']; exact emultiplicity_sub_of_gt
  have prim : ¬ (0 < v a ∧ 0 < v b ∧ 0 < v c ∧ 0 < v d) := by
    simpa only [v, dvd_iff_emultiplicity_pos]
      using hprim p hp
  simp only [v, pow_two, emultiplicity_mul hp, emultiplicity_neg, hcast _ (hDelta_pos N Δ).ne',
    hcast _ (NeZero.ne n), hcast _ (NeZero.ne N), hcast _ (epsDelta_pos (N := N) (Δ := Δ)).ne', min_le_iff] at H1 H2 H3 H4 H5 H6 H7 H8 prim lo hi ⊢
  have hk := factorization_hDelta (N := N) (Δ := Δ) p.natAbs
  -- Split the multiplicities into finite and infinite cases, then use Presburger arithmetic.
  generalize emultiplicity p e = E, emultiplicity p a = A, emultiplicity p b = B, emultiplicity p c = C, emultiplicity p d = F
    at H1 H2 H3 H4 H5 H6 H7 H8 prim lo hi ⊢
  clear * - hk hN H1 H2 H3 H4 H5 H6 H7 H8 prim lo hi
  enat_to_nat <;> simp at * <;> omega

/-- Every element of the normalizer has the generalized Newman form. -/
theorem newman_delta' (hg : g ∈ NormG Γ) :
    IsNewmanFormH N hΔ g := by
  obtain ⟨κ, α, β, γ, δ, hp, hmat⟩ := exists_prim hg
  have hh := (hDelta_pos N Δ).ne'
  have hdet := det_form hh hmat
  generalize he : α * δ - β * γ = E at hdet
  have hE : 0 < E := by
    have hr : (0 : ℝ) < κ ^ 2 * (E : ℝ) := hdet ▸ zero_lt_one
    exact_mod_cast pos_of_mul_pos_right hr (sq_nonneg κ)
  obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hE.le
  have hn := Int.natCast_ne_zero.2 (NeZero.ne n)
  have H : (e : ℤ) ∣ (n : ℤ) ∧ (n : ℤ) ∣ γ ∧ (e : ℤ) ∣ α ∧ (e : ℤ) ∣ δ := by
    simpa only [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hE.ne',
      UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hn, ← forall_and, ← imp_and] using
      fun (p : ℤ) (hp' : Prime p) => local_bounds hg hmat he.symm hp hp'
  obtain ⟨hEn, ⟨c, rfl⟩, ⟨a, rfl⟩, ⟨d, rfl⟩⟩ := H
  have he0 : 0 < e := by exact_mod_cast hE
  refine ⟨a, β, c, d, e, he0, Int.natCast_dvd_natCast.1 hEn, ?_, κ * Real.sqrt e, ?_, ?_⟩
  · change a*d*(e : ℤ)^2 - β*c*(n : ℤ) = e
    linear_combination he
  · apply mul_self_eq_one_iff.1
    rw [← pow_two, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast hdet
  · have hhr : (hΔ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
    have hn' : (N : ℝ) = (n : ℝ) * (hΔ : ℝ) ^ 2 := by exact_mod_cast (nDelta_mul N Δ).symm
    rw [hmat, mul_div_assoc, div_self (by positivity : Real.sqrt e ≠ 0), mul_one]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Smat, hn', mul_comm]; field_simp

end

end NormalizerLean
