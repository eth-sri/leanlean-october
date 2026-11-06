module

public import NormalizerLean.Defs

@[expose] public section

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-!
# Basic API for Γ₀(N) ≤ SL₂(ℝ), its normalizer, B(N), S_k and h(N)
-/




/-! ### Membership in Γ₀(N) -/

/-- The real matrix of an integer matrix. -/
abbrev castM (M : M2Z) : M2 := M.map (Int.cast)

theorem mem_Gamma0R_iff {N : ℕ} {g : SL2R} :
    g ∈ Gamma0R N ↔ ∃ M : M2Z,
      (N : ℤ) ∣ M 1 0 ∧ (g : M2) = castM M := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, ?_, ?_⟩
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hA)
    · simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  · rintro ⟨M, hM, hg⟩
    have hdet : M.det = 1 := by
      have h1 := g.2
      rw [hg, det_fin_two] at h1
      rw [det_fin_two]
      simp only [castM, map_apply] at h1
      exact_mod_cast h1
    let A : SL2Z := ⟨M, hdet⟩
    refine ⟨A, CongruenceSubgroup.Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hM), ?_⟩
    refine Matrix.SpecialLinearGroup.ext _ _ (fun i j => ?_)
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hg]
    rfl

/-- Membership in Γ₀(N) from explicit integer entries. -/
theorem mem_Gamma0R_of_entries {N : ℕ} {g : SL2R} (a b c d : ℤ)
    (hg : (g : M2) = !![(a : ℝ), b; c, d]) (hc : (N : ℤ) ∣ c) :
    g ∈ Gamma0R N := by
  refine mem_Gamma0R_iff.2 ⟨!![a, b; c, d], by simpa using hc, ?_⟩
  rw [hg]; mx

/-- Elements of Γ₀(N) have integer entries, lower-left divisible by N, determinant 1. -/
theorem exists_entries_of_mem_Gamma0R {N : ℕ} {g : SL2R} (hg : g ∈ Gamma0R N) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (N : ℤ) ∣ c ∧
      (g : M2) = !![(a : ℝ), b; c, d] := by
  obtain ⟨M, hM, hgM⟩ := mem_Gamma0R_iff.1 hg
  refine ⟨M 0 0, M 0 1, M 1 0, M 1 1, ?_, hM, ?_⟩
  · have h1 := g.2
    rw [hgM, det_fin_two] at h1
    simp only [castM, map_apply] at h1
    exact_mod_cast h1
  · rw [hgM]; mx

/-! ### The normalizer -/

/-! ### B(N) -/

/-! ### h(N) -/

theorem hPart_pos (N : ℕ) : 0 < hPart N := by unfold hPart; positivity

/-! ### Units modulo divisors of 24 square to 1 -/

theorem modEq_of_mul_modEq_one {k : ℕ} (hk : k ∣ 24) {a d : ℤ} (h : a * d ≡ 1 [ZMOD k]) :
    a ≡ d [ZMOD k] := by
  have hk24 := Nat.le_of_dvd (by norm_num) hk
  rw [← ZMod.intCast_eq_intCast_iff] at h ⊢
  push_cast at h
  generalize (a : ZMod k) = x at h ⊢
  generalize (d : ZMod k) = y at h ⊢
  revert x y
  interval_cases k <;> norm_num at hk <;> decide

/-!
# T1 for Atkin–Lehner elements and translations

* `S_mem_normalizer'`: S_k normalizes Γ₀(N) for k ∣ h(N);
* `isAtkinLehner_mem_normalizer'`: every AL element w_Q (Q ∣ N) normalizes Γ₀(N);
* `exists_isAtkinLehner'`: AL elements exist for Q ∥ N;
* `isAtkinLehner_mul_inv_mem'`: two AL elements for Q differ by Γ₀(N).

The AL computations are the identities W γ adj(W) = Q·M₁, adj(W) γ W = Q·M₂, W adj(W') = Q·M₃
with explicit integer matrices Mᵢ (checked symbolically in sympy before being given to `ring`).
-/




/-! ### Scalar bookkeeping -/

theorem coe_inv_of_coe_eq_smul {g : SL2R} {s a b c d : ℝ}
    (h : (g : M2) = s • !![a, b; c, d]) :
    ((g⁻¹ : SL2R) : M2) = s • !![d, -b; -c, a] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, h, adjugate_smul, adjugate_fin_two_of]
  simp

/-! ### Translations -/

/-! ### Atkin–Lehner elements -/

/-!
# T1 in general: matrices of Newman's form (8′) normalize Γ₀(N) ([Nw §1])

With N = e·m·h² (h = h(N), n = N/h² = e·m), g = (ε/√e)·G, G = [[ae, b/h], [Nc/h, de]], and
γ = [[x, y], [Nz, x + hf]] ∈ Γ₀(N) (t ≡ x mod h because units mod h ∣ 24 square to 1),
G γ adj(G) = e·M with M the explicit integer matrix below (checked in sympy first).
Also `conjGamma0n_le_normalizer`: D⁻¹Γ₀(n)D consists of (8′)-matrices with e = 1.
-/




/-! ### D⁻¹Γ₀(n)D -/

theorem coe_projSL (A : M2) (hA : 0 < A.det) :
    ((projSL A : SL2R) : M2) = (Real.sqrt A.det)⁻¹ • A := by
  have : projSL A = ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩ :=
    dif_pos hA
  rw [this]

/-!
# The algebra of Newman's form (8′)

For g = (ε/√e)·[[ae, b/h], [Nc/h, de]] (Newman data (a, b, c, d, e, ε)):
* `NData.e_unique`: e is determined by g (the integer matrix W = [[ae, b], [nc, de]] is primitive:
  d·(ae) − (cm)·b = 1 where n = em);
* `NData.mul`: the product of (8′)-matrices with e, e' is an (8′)-matrix with e₁f₁, where
  e = e₁q, e' = f₁q, gcd(e₁, f₁) = 1 (the Atkin–Lehner product law);
* `NData.one_of_mem`: elements of Γ₀(N) have e = 1;
* `NData.inv`.
-/




/-! ### Uniqueness of e -/

theorem cross_of_prop {κ κ' : ℝ} (hκ : κ ≠ 0) {x y x' y' : ℤ}
    (h1 : κ * x = κ' * x') (h2 : κ * y = κ' * y') : x * y' = y * x' := by
  have : κ * ((x : ℝ) * y') = κ * ((y : ℝ) * x') := by
    calc κ * ((x : ℝ) * y') = (κ * x) * y' := by ring
      _ = κ' * x' * y' := by rw [h1]
      _ = (κ' * y') * x' := by ring
      _ = κ * y * x' := by rw [h2]
      _ = κ * ((y : ℝ) * x') := by ring
  exact_mod_cast mul_left_cancel₀ hκ this

/-! ### Products -/

/-! ### The invariant e(g) and the parities σ_p -/

/-!
# Newman's theorem, step 1: normalizing elements are rational up to a scalar ([Nw §2])

If g = [[x, y], [z, w]] normalizes Γ₀(N), the conjugates of T, U, TU are integral, so
x², xz, z², Nyw, Ny², Nw², Nxw, Nxy, Nzw, Nyz are integers.  With t = x (or t = z if x = 0),
N t x, N t y, N t z, N t w are integers, and g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ
coprime (dividing by the gcd of the entries).
-/




/-- `r` is an integer. -/
def IsIntR (r : ℝ) : Prop := ∃ m : ℤ, r = m

theorem IsIntR.add {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r + s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m + n, by push_cast; ring⟩
theorem IsIntR.sub {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r - s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m - n, by push_cast; ring⟩
theorem IsIntR.mul {r s : ℝ} (hr : IsIntR r) (hs : IsIntR s) : IsIntR (r * s) := by
  obtain ⟨m, rfl⟩ := hr; obtain ⟨n, rfl⟩ := hs; exact ⟨m * n, by push_cast; ring⟩
theorem IsIntR.neg {r : ℝ} (hr : IsIntR r) : IsIntR (-r) := by
  obtain ⟨m, rfl⟩ := hr; exact ⟨-m, by push_cast; ring⟩
theorem IsIntR.int (m : ℤ) : IsIntR m := ⟨m, rfl⟩
theorem IsIntR.nat (m : ℕ) : IsIntR m := ⟨m, by simp⟩
theorem IsIntR.one : IsIntR 1 := ⟨1, by simp⟩

theorem isIntR_entries_of_mem {N : ℕ} {γ : SL2R} (hγ : γ ∈ Gamma0R N) (i j : Fin 2) :
    IsIntR ((γ : M2) i j) := by
  obtain ⟨a, b, c, d, -, -, hm⟩ := exists_entries_of_mem_Gamma0R hγ
  rw [hm]
  fin_cases i <;> fin_cases j <;> simp [IsIntR.int]

/-- T, U, TU ∈ Γ₀(N). -/
def matT : SL2R := ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩
def matU (N : ℕ) : SL2R := ⟨!![1, 0; (N : ℝ), 1], by simp [det_fin_two_of]⟩

theorem coe_conj (g Y : SL2R) :
    ((g * Y * g⁻¹ : SL2R) : M2) =
      (g : M2) * (Y : M2) *
        (g : M2).adjugate := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]

/-!
# Newman's theorem, step 2: the integrality conditions ([Nw §3])

With g = κ·S, S = [[α, β/h], [hγ, δ]] and e = αδ − βγ (so κ²e = 1), conjugation by g is
Φ(M) = S M adj(S) / e.  `InL N M` says that M is an integer matrix with N ∣ M₁₀ and ε ∣ M₁₁ − M₀₀
(ε = gcd(N, 24)); it holds on Γ₀(N) (units mod divisors of 24 square to 1) and is closed under
integer combinations.  Applying Φ to E₁₂ = T − 1, NE₂₁ = U − 1, NE₂₂ = N − (TU − T − U + 1) and
(t − x)E₂₂ = γ − x − yE₁₂ − NE₂₁ (γ = [[x, y], [N, t]] ∈ Γ₀(N)) gives integer divisibilities.
-/




/-- ε = gcd(N, 24). -/
def epsPart (N : ℕ) : ℕ := Nat.gcd N 24

/-! ### Conjugation as a linear map -/

/-- S = [[α, β/h], [hγ, δ]]. -/
def Smat (h : ℕ) (α β γ δ : ℤ) : M2 :=
  !![(α : ℝ), (β : ℝ) / h; (h : ℝ) * γ, (δ : ℝ)]

/-- Φ(M) = S M adj(S) / e. -/
def Phi (h : ℕ) (α β γ δ : ℤ) (M : M2) : M2 :=
  ((α * δ - β * γ : ℤ) : ℝ)⁻¹ • (Smat h α β γ δ * M * (Smat h α β γ δ).adjugate)

theorem Phi_add (h : ℕ) (α β γ δ : ℤ) (M M' : M2) :
    Phi h α β γ δ (M + M') = Phi h α β γ δ M + Phi h α β γ δ M' := by
  simp [Phi, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem Phi_smul (h : ℕ) (α β γ δ : ℤ) (r : ℝ) (M : M2) :
    Phi h α β γ δ (r • M) = r • Phi h α β γ δ M := by
  simp [Phi, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

theorem Phi_sub (h : ℕ) (α β γ δ : ℤ) (M M' : M2) :
    Phi h α β γ δ (M - M') = Phi h α β γ δ M - Phi h α β γ δ M' := by
  have := Phi_add h α β γ δ M ((-1 : ℝ) • M')
  rw [Phi_smul] at this
  simpa [sub_eq_add_neg] using this

theorem det_Smat {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    (Smat h α β γ δ).det = ((α * δ - β * γ : ℤ) : ℝ) := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  rw [Smat, det_fin_two_of]
  push_cast
  field_simp

theorem Phi_one {h : ℕ} (hh : h ≠ 0) {α β γ δ : ℤ} (he : α * δ - β * γ ≠ 0) :
    Phi h α β γ δ 1 = 1 := by
  have her : ((α * δ - β * γ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast he
  rw [Phi, Matrix.mul_one, Matrix.mul_adjugate, det_Smat hh, smul_smul, inv_mul_cancel₀ her,
    one_smul]

/-- Conjugation by g = κ S is Φ. -/
theorem coe_conj_eq_Phi {g : SL2R} {κ : ℝ} {h : ℕ} {α β γ δ : ℤ}
    (hg : (g : M2) = κ • Smat h α β γ δ) (hh : h ≠ 0) (Y : SL2R) :
    ((g * Y * g⁻¹ : SL2R) : M2) =
      Phi h α β γ δ (Y : M2) := by
  have hdet : κ ^ 2 * ((α * δ - β * γ : ℤ) : ℝ) = 1 := by
    have := g.2
    rw [hg, det_smul, Fintype.card_fin, Smat, det_fin_two_of] at this
    have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
    push_cast
    field_simp at this
    linear_combination this
  have hE : ((α * δ - β * γ : ℤ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdet; exact zero_ne_one hdet
  have hinv : κ ^ 2 = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ := by
    field_simp
    linear_combination hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hg, adjugate_smul, Fintype.card_fin]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Phi]
  congr 1

/-- The explicit images of E₁₂, E₂₁, E₂₂ under M ↦ S M adj(S). -/
theorem Phi_E12 (h : ℕ) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 1; 0, 0] = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ •
      !![-(α * h * γ : ℝ), (α : ℝ) ^ 2; -((h : ℝ) ^ 2 * γ ^ 2), α * h * γ] := by
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem Phi_E21 {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 0; 1, 0] = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ •
      !![(β : ℝ) * δ / h, -((β : ℝ) ^ 2 / (h : ℝ) ^ 2); (δ : ℝ) ^ 2, -((β : ℝ) * δ / h)] := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem Phi_E22 {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 0; 0, 1] = ((α * δ - β * γ : ℤ) : ℝ)⁻¹ •
      !![-((β : ℝ) * γ), (α : ℝ) * β / h; -((h : ℝ) * γ * δ), (α : ℝ) * δ] := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-!
# Newman's theorem: valuations, the local constants, and the element γ_p of Lemma 3

* `vz p x` is the p-adic valuation of an integer (0 at 0); `vv B p x` is the same but equal to the
  large value `B` at 0, so that zero entries can be handled by `omega` uniformly.
* the ultrametric relation for e = αδ − βγ in terms of `vv`;
* v_p(h), v_p(ε), v_p(n) in terms of ν = v_p(N);
* `exists_gamma_p`: for p ∣ N an element [[x, y], [N, t]] ∈ Γ₀(N) with min(v_p(t − x), ν) = v_p(ε)
  (x ≡ 3 or 2 mod p^ν by the Chinese remainder theorem).
-/


/-- p-adic valuation of an integer (junk value 0 at 0). -/
def vz (p : ℕ) (x : ℤ) : ℕ := x.natAbs.factorization p

theorem vz_mul {p : ℕ} {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) : vz p (x * y) = vz p x + vz p y := by
  simp [vz, Int.natAbs_mul, Nat.factorization_mul (Int.natAbs_ne_zero.2 hx)
    (Int.natAbs_ne_zero.2 hy)]

theorem vz_neg (p : ℕ) (x : ℤ) : vz p (-x) = vz p x := by simp [vz]

theorem vz_natCast (p n : ℕ) : vz p n = n.factorization p := by simp [vz]

theorem pow_dvd_iff_le_vz {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : x ≠ 0) (m : ℕ) :
    (p : ℤ) ^ m ∣ x ↔ m ≤ vz p x := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast,
    hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.2 hx)]
  rfl

theorem vz_le_of_dvd (p : ℕ) {x y : ℤ} (hy : y ≠ 0) (hxy : x ∣ y) : vz p x ≤ vz p y := by
  have hx : x ≠ 0 := by rintro rfl; exact hy (zero_dvd_iff.1 hxy)
  exact (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.2 hx) (Int.natAbs_ne_zero.2 hy)).2
    (Int.natAbs_dvd_natAbs.2 hxy) p

/-- Valuation with value `B` at 0. -/
def vv (B p : ℕ) (x : ℤ) : ℕ := if x = 0 then B else vz p x

theorem vv_of_ne {B p : ℕ} {x : ℤ} (hx : x ≠ 0) : vv B p x = vz p x := if_neg hx

theorem vv_neg (B p : ℕ) (x : ℤ) : vv B p (-x) = vv B p x := by
  unfold vv
  simp [vz_neg]

/-- From `X ∣ K·x·y`: v(X) ≤ v(K) + v(x) + v(y). -/
theorem le_vv2 {B p : ℕ} {X K x y : ℤ} (hK : K ≠ 0) (hB : vz p X ≤ B) (h : X ∣ K * (x * y)) :
    vz p X ≤ vz p K + vv B p x + vv B p y := by
  by_cases hx : x = 0
  · simp [vv, hx]; omega
  by_cases hy : y = 0
  · simp [vv, hy]; omega
  rw [vv_of_ne hx, vv_of_ne hy]
  have := vz_le_of_dvd p (mul_ne_zero hK (mul_ne_zero hx hy)) h
  rw [vz_mul hK (mul_ne_zero hx hy), vz_mul hx hy] at this
  omega

/-- From `X ∣ K·x²`: v(X) ≤ v(K) + 2v(x). -/
theorem le_vv_sq {B p : ℕ} {X K x : ℤ} (hK : K ≠ 0) (hB : vz p X ≤ B) (h : X ∣ K * x ^ 2) :
    vz p X ≤ vz p K + 2 * vv B p x := by
  have := le_vv2 (x := x) (y := x) hK hB (by rwa [← pow_two])
  omega

/-! ### The ultrametric inequality -/

theorem vz_sub_ge {p : ℕ} (hp : p.Prime) {A C : ℤ} (hAC : A - C ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0) :
    min (vz p A) (vz p C) ≤ vz p (A - C) := by
  rw [← pow_dvd_iff_le_vz hp hAC]
  exact dvd_sub ((pow_dvd_iff_le_vz hp hA _).2 (min_le_left _ _))
    ((pow_dvd_iff_le_vz hp hC _).2 (min_le_right _ _))

theorem vz_sub_eq {p : ℕ} (hp : p.Prime) {A C : ℤ} (hAC : A - C ≠ 0) (hA : A ≠ 0) (hC : C ≠ 0)
    (hne : vz p A ≠ vz p C) : vz p (A - C) = min (vz p A) (vz p C) := by
  apply le_antisymm _ (vz_sub_ge hp hAC hA hC)
  by_contra hlt
  push Not at hlt
  have h1 := (pow_dvd_iff_le_vz hp hAC (min (vz p A) (vz p C) + 1)).2 hlt
  rcases lt_or_gt_of_ne hne with h | h
  · have h2 := (pow_dvd_iff_le_vz hp hC (vz p A + 1)).2 (by omega)
    rw [min_eq_left h.le] at h1
    have h3 : (p : ℤ) ^ (vz p A + 1) ∣ A := by
      have := dvd_add h1 h2
      simpa using this
    have := (pow_dvd_iff_le_vz hp hA _).1 h3
    omega
  · have h2 := (pow_dvd_iff_le_vz hp hA (vz p C + 1)).2 (by omega)
    have h3 : (p : ℤ) ^ (vz p C + 1) ∣ C := by
      rw [min_eq_right h.le] at h1
      have := dvd_sub h2 h1
      simpa using this
    have := (pow_dvd_iff_le_vz hp hC _).1 h3
    omega

/-- The ultrametric relation for e = αδ − βγ, in terms of `vv`. -/
theorem ultra_vv {B p : ℕ} (hp : p.Prime) {α β γ δ : ℤ} (he : α * δ - β * γ ≠ 0)
    (hB : vz p (α * δ - β * γ) < B) :
    min (vv B p α + vv B p δ) (vv B p β + vv B p γ) ≤ vz p (α * δ - β * γ) ∧
      (vv B p α + vv B p δ ≠ vv B p β + vv B p γ →
        vz p (α * δ - β * γ) = min (vv B p α + vv B p δ) (vv B p β + vv B p γ)) := by
  by_cases had : α = 0 ∨ δ = 0
  · have hbg : β * γ ≠ 0 := by rcases had with rfl | rfl <;> simpa using he
    have hβ := left_ne_zero_of_mul hbg
    have hγ := right_ne_zero_of_mul hbg
    have hev : vz p (α * δ - β * γ) = vv B p β + vv B p γ := by
      rcases had with rfl | rfl <;>
      · simp only [zero_mul, mul_zero, zero_sub, vz_neg]
        rw [vz_mul hβ hγ, vv_of_ne hβ, vv_of_ne hγ]
    have hbig : B ≤ vv B p α + vv B p δ := by
      rcases had with rfl | rfl <;> simp [vv]
    constructor <;> [omega; (intro; omega)]
  push Not at had
  by_cases hbg' : β = 0 ∨ γ = 0
  · have hev : vz p (α * δ - β * γ) = vv B p α + vv B p δ := by
      rcases hbg' with rfl | rfl <;>
      · simp only [zero_mul, mul_zero, sub_zero]
        rw [vz_mul had.1 had.2, vv_of_ne had.1, vv_of_ne had.2]
    have hbig : B ≤ vv B p β + vv B p γ := by
      rcases hbg' with rfl | rfl <;> simp [vv]
    constructor <;> [omega; (intro; omega)]
  push Not at hbg'
  have hA := mul_ne_zero had.1 had.2
  have hC := mul_ne_zero hbg'.1 hbg'.2
  rw [vv_of_ne had.1, vv_of_ne had.2, vv_of_ne hbg'.1, vv_of_ne hbg'.2, ← vz_mul had.1 had.2,
    ← vz_mul hbg'.1 hbg'.2]
  exact ⟨vz_sub_ge hp he hA hC, vz_sub_eq hp he hA hC⟩

/-! ### The local constants -/

theorem factorization_24 (p : ℕ) :
    (24 : ℕ).factorization p = if p = 2 then 3 else if p = 3 then 1 else 0 := by
  rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem factorization_two (p : ℕ) : (2 : ℕ).factorization p = if p = 2 then 1 else 0 := by
  rw [Nat.prime_two.factorization, Finsupp.single_apply]
  split_ifs <;> omega

theorem factorization_hPart (N p : ℕ) :
    (hPart N).factorization p = if p = 2 then min 3 (N.factorization 2 / 2) else
      if p = 3 then min 1 (N.factorization 3 / 2) else 0 := by
  unfold hPart
  rw [Nat.factorization_mul (by positivity) (by positivity), Nat.prime_two.factorization_pow,
    Nat.prime_three.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

theorem factorization_epsPart {N : ℕ} (hN : N ≠ 0) (p : ℕ) :
    (epsPart N).factorization p = min (N.factorization p) ((24 : ℕ).factorization p) := by
  unfold epsPart
  rw [Nat.factorization_gcd hN (by norm_num)]
  rfl

/-- The local data at p: ν = v_p(N), j = v_p(ε), k = v_p(h), e₂ = v_p(2). -/
theorem local_constants {N p : ℕ} (hN : N ≠ 0) :
    ((p = 2 ∧ (epsPart N).factorization p = min (N.factorization p) 3 ∧
        (2 : ℕ).factorization p = 1) ∨
      (p = 3 ∧ (epsPart N).factorization p = min (N.factorization p) 1 ∧
        (2 : ℕ).factorization p = 0) ∨
      ((epsPart N).factorization p = 0 ∧ (2 : ℕ).factorization p = 0)) ∧
    (hPart N).factorization p = min ((epsPart N).factorization p) (N.factorization p / 2) := by
  rw [factorization_epsPart hN, factorization_24, factorization_two, factorization_hPart]
  by_cases h2 : p = 2
  · subst h2; simp; omega
  by_cases h3 : p = 3
  · subst h3; simp; omega
  simp [h2, h3]



/-! ### The element γ_p of Lemma 3 -/

/-- If x t − y N = 1, p^ν ∣ N, x ≡ r (mod p^ν), p ∤ x, p^ρ ∥ 1 − r², then
either ν ≤ ρ, or t − x ≠ 0 with v_p(t − x) = ρ. -/
theorem gamma_val {p ν ρ : ℕ} (hp : p.Prime) {N x y t r : ℤ} (hdet : x * t - y * N = 1)
    (hN : (p : ℤ) ^ ν ∣ N) (hxr : (p : ℤ) ^ ν ∣ r - x) (hpx : IsCoprime (p : ℤ) x)
    (hρ1 : (p : ℤ) ^ ρ ∣ 1 - r ^ 2) (hρ2 : ¬ (p : ℤ) ^ (ρ + 1) ∣ 1 - r ^ 2) :
    ν ≤ ρ ∨ (ρ < ν ∧ t - x ≠ 0 ∧ vz p (t - x) = ρ) := by
  rcases le_or_gt ν ρ with h | h
  · exact Or.inl h
  right
  -- x (t − x) ≡ 1 − r² (mod p^ν)
  have hcong : (p : ℤ) ^ ν ∣ x * (t - x) - (1 - r ^ 2) := by
    have : x * (t - x) - (1 - r ^ 2) = y * N + (r - x) * (r + x) := by linear_combination hdet
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hN _) (dvd_mul_of_dvd_left hxr _)
  have hle : ∀ m ≤ ν, (p : ℤ) ^ m ∣ x * (t - x) ↔ (p : ℤ) ^ m ∣ 1 - r ^ 2 := by
    intro m hm
    have hm' := (pow_dvd_pow _ hm).trans hcong
    constructor
    · intro h1; have := dvd_sub h1 hm'; simpa using this
    · intro h1; have := dvd_add hm' h1; simpa using this
  have hcop : ∀ m, IsCoprime ((p : ℤ) ^ m) x := fun m => hpx.pow_left
  have hnot : ¬ (p : ℤ) ^ (ρ + 1) ∣ t - x := by
    intro h1
    exact hρ2 ((hle (ρ + 1) h).1 (dvd_mul_of_dvd_right h1 _))
  have hs : t - x ≠ 0 := by
    intro h0
    rw [h0] at hnot
    exact hnot (dvd_zero _)
  have hyes :=
    (hcop ρ).dvd_of_dvd_mul_left ((hle ρ h.le).2 hρ1)
  refine ⟨h, hs, le_antisymm ?_ ((pow_dvd_iff_le_vz hp hs ρ).1 hyes)⟩
  by_contra hc
  exact hnot ((pow_dvd_iff_le_vz hp hs (ρ + 1)).2 (by omega))

/-!
# Newman's theorem, step 2 continued: the integer divisibilities

For g = κ·S ∈ Norm(Γ₀(N)), S = [[α, β/h], [hγ, δ]], e = αδ − βγ, with h = h(N), n = n(N),
ε = gcd(N, 24):

* F1  e ∣ h·αγ        F2  e ∣ α²          F3  eN ∣ h²γ²         F4  eε ∣ 2h·αγ
* F5  e ∣ nh·βδ       F6  e ∣ n·β²        F7  e ∣ δ²            F8  eε ∣ 2nh·βδ
* F9  e ∣ N·βγ        F10 eh ∣ N·αβ       F11 eN ∣ Nh·γδ        F12 eε ∣ 2N·βγ
* and, for [[x, y], [N, t]] ∈ Γ₀(N) and s = t − x, the same four with s in place of N.
-/




theorem int_eq_of_real {e X a : ℤ} (he : e ≠ 0) (h : ((e : ℝ))⁻¹ * (X : ℝ) = a) : X = e * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have : (X : ℝ) = e * a := by rw [← h]; field_simp
  exact_mod_cast this

theorem int_eq_of_real_div {e X a : ℤ} {d : ℕ} (he : e ≠ 0) (hd : d ≠ 0)
    (h : ((e : ℝ))⁻¹ * ((X : ℝ) / d) = a) : X = e * d * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hdr : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have : (X : ℝ) = e * d * a := by rw [← h]; field_simp
  exact_mod_cast this

/-!
# T2: Newman's theorem

Every g ∈ Norm(Γ₀(N)) has the form (8′).  Write g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ
coprime (`exists_prim_form`), e = αδ − βγ.  The divisibilities F1–F12 (for g and g⁻¹, and with
s = t − x from the element γ_p of Lemma 3) give, at every prime p, the valuation inequalities of
`local_form`, whose conclusion says: either v_p(e) = 0 and p^{v_p(n)} ∣ γ, or v_p(e) = v_p(n) and
p^{v_p(n)} divides α, γ, δ.  Hence e ∣ n, n ∣ γ, e ∣ α, e ∣ δ, which is (8′).
-/




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
