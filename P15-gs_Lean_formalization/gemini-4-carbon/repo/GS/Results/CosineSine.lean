module

public import GS.Unitary.Factorization
public import GS.OriginalLocalModel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix InnerProductSpace GS.UnitaryGeometry
open scoped BigOperators

namespace GS.Results.CosineSine

section RCLikeCS
variable {𝕂 : Type*} [RCLike 𝕂]

private theorem exists_kunitary_mul_diag {n : ℕ} (A : KMat 𝕂 n) (d : Fin n → ℝ)
    (hA : Aᴴ * A = diagonal (fun i => (d i : 𝕂) ^ 2)) :
    ∃ U : KMat 𝕂 n, KUni U ∧ A = U * diagonal (fun i => (d i : 𝕂)) := by
  classical
  let e₀ : OrthonormalBasis (Fin n) 𝕂 (EuclideanSpace 𝕂 (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) 𝕂
  let f : Fin n → EuclideanSpace 𝕂 (Fin n) := fun j => ∑ k, A k j • e₀ k
  have hc (i j : Fin n) : ⟪e₀ i, f j⟫_𝕂 = A i j := by
    simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
  have hgram (i j : Fin n) : ⟪f i, f j⟫_𝕂 = if i = j then (d i : 𝕂) ^ 2 else 0 := by
    calc ⟪f i, f j⟫_𝕂 = ∑ k, star (A k i) * A k j := by
          rw [← e₀.sum_inner_mul_inner (f i) (f j)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← inner_conj_symm (f i) (e₀ k), hc, hc]; rfl
      _ = (Aᴴ * A) i j := rfl
      _ = _ := by rw [hA]; simp [Matrix.diagonal_apply]
  let s : Set (Fin n) := {i | d i ≠ 0}
  let v : Fin n → EuclideanSpace 𝕂 (Fin n) := fun j => ((d j : 𝕂))⁻¹ • f j
  have hv : Orthonormal 𝕂 (s.domRestrict v) := by
    rw [orthonormal_iff_ite]; intro i j
    change ⟪((d i : 𝕂))⁻¹ • f i, ((d j : 𝕂))⁻¹ • f j⟫_𝕂 = _
    rw [inner_smul_left, inner_smul_right, hgram]
    by_cases hij : i = j
    · subst j
      have hd : (d i : 𝕂) ≠ 0 := RCLike.ofReal_ne_zero.mpr i.2
      simp [RCLike.conj_ofReal, hd, pow_two]
    · simp [hij, show (i : Fin n) ≠ j from fun h => hij (Subtype.ext h)]
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank 𝕂 (EuclideanSpace 𝕂 (Fin n)) = Fintype.card (Fin n))
  let U : KMat 𝕂 n := fun i j => ⟪e₀ i, e j⟫_𝕂
  refine ⟨U, kUnitary_of_left ?_, ?_⟩
  · ext i j
    calc (Uᴴ * U) i j = ∑ k, ⟪e i, e₀ k⟫_𝕂 * ⟪e₀ k, e j⟫_𝕂 := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun k _ => by rw [← inner_conj_symm (e i) (e₀ k)]; rfl
      _ = ⟪e i, e j⟫_𝕂 := e₀.sum_inner_mul_inner _ _
      _ = (1 : KMat 𝕂 n) i j := by simpa [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
  · ext i j; rw [Matrix.mul_diagonal]
    by_cases hd : d j = 0
    · have hf : f j = 0 := (inner_self_eq_zero (𝕜 := 𝕂)).mp ((hgram j j).trans (by simp [hd]))
      simp [hd, ← hc, hf]
    · have hj : j ∈ s := hd
      change A i j = ⟪e₀ i, e j⟫_𝕂 * (d j : 𝕂)
      rw [he j hj, inner_smul_right, hc]
      have hd' : (d j : 𝕂) ≠ 0 := RCLike.ofReal_ne_zero.mpr hd
      field_simp [hd']

private theorem kgram_nonneg {n : ℕ} (A : KMat 𝕂 n) (d : Fin n → ℝ)
    (h : Aᴴ * A = diagonal (fun i => (d i : 𝕂))) (i : Fin n) : 0 ≤ d i := by
  have hi := congrArg RCLike.re (congrFun (congrFun h i) i)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
    RCLike.ofReal_re, map_sum] at hi
  rw [← hi]
  refine Finset.sum_nonneg fun j _ => ?_
  have hr : RCLike.re (star (A j i) * A j i) = ‖A j i‖ ^ 2 := by
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [hr]; positivity

private theorem diag_real_conj {n : ℕ} (v : Fin n → ℝ) :
    (diagonal fun i => (v i : 𝕂))ᴴ = diagonal fun i => (v i : 𝕂) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [RCLike.star_def, RCLike.conj_ofReal]
  · simp [Matrix.diagonal_apply, h, Ne.symm h]

private theorem kcs_unitary {n : ℕ} (c s : Fin n → ℝ) (hcs : ∀ i, c i ^ 2 + s i ^ 2 = 1) :
    let dc : KMat 𝕂 n := diagonal fun i => (c i : 𝕂)
    let ds : KMat 𝕂 n := diagonal fun i => (s i : 𝕂)
    KUni (fromBlocks dc (-ds) ds dc) := by
  intro dc ds
  refine kUnitary_of_left ?_
  rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg, diag_real_conj (𝕂 := 𝕂) c,
    diag_real_conj (𝕂 := 𝕂) s, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  have hcsK (j : Fin n) : (c j : 𝕂) ^ 2 + (s j : 𝕂) ^ 2 = 1 := by exact_mod_cast hcs j
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases hij : i = j
  · subst j; simp [dc, ds, Matrix.diagonal_mul_diagonal]; linear_combination hcsK i
  · simp [dc, ds, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, hij]
  · subst j; simp [dc, ds, Matrix.diagonal_mul_diagonal]; ring
  · simp [dc, ds, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, hij]
  · subst j; simp [dc, ds, Matrix.diagonal_mul_diagonal]; ring
  · simp [dc, ds, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, hij]
  · subst j; simp [dc, ds, Matrix.diagonal_mul_diagonal]; linear_combination hcsK i
  · simp [dc, ds, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, hij]

private theorem exists_ksquare_cs {n : ℕ}
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕂) (hQ : KUni Q) :
    ∃ (U₁ U₂ V₁ V₂ : KMat 𝕂 n) (c s : Fin n → ℝ),
      KUni U₁ ∧ KUni U₂ ∧ KUni V₁ ∧ KUni V₂ ∧
      (∀ i, c i ^ 2 + s i ^ 2 = 1) ∧
      Q = fromBlocks U₁ 0 0 U₂ *
        fromBlocks (diagonal fun i => (c i : 𝕂)) (-diagonal fun i => (s i : 𝕂))
          (diagonal fun i => (s i : 𝕂)) (diagonal fun i => (c i : 𝕂)) *
        fromBlocks V₁ 0 0 V₂ := by
  let A := Q.toBlocks₁₁; let B := Q.toBlocks₁₂; let C := Q.toBlocks₂₁; let D := Q.toBlocks₂₂
  have hblocks : Q = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks Q).symm
  have hfirst : Aᴴ * A + Cᴴ * C = 1 := by
    have hh := congrArg Matrix.toBlocks₁₁ hQ.1
    simpa [hblocks, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  let V : KMat 𝕂 n := hH.eigenvectorUnitary
  let d : Fin n → ℝ := hH.eigenvalues
  have hV : KUni V := kUnitary_of_left <| by
    simpa only [V, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hAV : (A * V)ᴴ * (A * V) = diagonal (fun i => (d i : 𝕂)) := by
    simpa [Function.comp_def, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      V, d, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hH.conjStarAlgAut_star_eigenvectorUnitary
  have hBV : (C * V)ᴴ * (C * V) = diagonal (fun i => ((1 - d i : ℝ) : 𝕂)) := by
    have hsum : (A * V)ᴴ * (A * V) + (C * V)ᴴ * (C * V) = 1 := by
      calc _ = Vᴴ * (Aᴴ * A + Cᴴ * C) * V := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hfirst, Matrix.mul_one, hV.1]
    rw [hAV] at hsum; rw [eq_sub_of_add_eq' hsum]
    ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  let c : Fin n → ℝ := fun i => Real.sqrt (d i)
  let s : Fin n → ℝ := fun i => Real.sqrt (1 - d i)
  have hc (i) : c i ^ 2 = d i := Real.sq_sqrt (kgram_nonneg _ _ hAV i)
  have hs (i) : s i ^ 2 = 1 - d i := Real.sq_sqrt (kgram_nonneg _ _ hBV i)
  have hcs (i) : c i ^ 2 + s i ^ 2 = 1 := by rw [hc, hs]; ring
  obtain ⟨U₁, hU₁, he₁⟩ := exists_kunitary_mul_diag (A * V) c (by
    convert hAV using 2; ext i; exact_mod_cast hc i)
  obtain ⟨U₂, hU₂, he₂⟩ := exists_kunitary_mul_diag (C * V) s (by
    convert hBV using 2; ext i; exact_mod_cast hs i)
  let dc : KMat 𝕂 n := diagonal fun i => (c i : 𝕂)
  let ds : KMat 𝕂 n := diagonal fun i => (s i : 𝕂)
  let L := fromBlocks U₁ 0 0 U₂
  let T := fromBlocks V 0 0 (1 : KMat 𝕂 n)
  let K := fromBlocks dc (-ds) ds dc
  have hsplitU {X Y : KMat 𝕂 n} (hX : KUni X) (hY : KUni Y) :
      KUni (fromBlocks X 0 0 Y) := by
    constructor <;> simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, hX.1, hX.2, hY.1, hY.2]
  have hL := hsplitU hU₁ hU₂
  have hT := hsplitU hV kUnitary_one
  have hK : KUni K := kcs_unitary c s hcs
  let E := U₁ᴴ * B; let F := U₂ᴴ * D
  let R := fromBlocks dc E ds F
  have hl₁ : U₁ᴴ * (A * V) = dc := by rw [he₁, ← Matrix.mul_assoc, hU₁.1, Matrix.one_mul]
  have hl₂ : U₂ᴴ * (C * V) = ds := by rw [he₂, ← Matrix.mul_assoc, hU₂.1, Matrix.one_mul]
  have hR : R = Lᴴ * Q * T := by
    rw [hblocks]
    simp [R, L, T, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.mul_assoc, hl₁, hl₂, E, F]
  have hHo : KUni (Kᴴ * R) := kUnitary_mul (kUnitary_conj hK)
    (hR ▸ kUnitary_mul (kUnitary_mul (kUnitary_conj hL) hQ) hT)
  let X := dc * E + ds * F; let W := -ds * E + dc * F
  have hH : Kᴴ * R = fromBlocks 1 X 0 W := by
    dsimp [K, R, X, W, dc, ds]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg, diag_real_conj (𝕂 := 𝕂) c,
      diag_real_conj (𝕂 := 𝕂) s, Matrix.fromBlocks_multiply]
    apply Matrix.fromBlocks_inj.mpr; refine ⟨?_, rfl, ?_, by simp⟩
    · ext i j; by_cases hij : i = j
      · subst j; simp [dc, ds, Matrix.diagonal_mul_diagonal]
        have : (c i : 𝕂) ^ 2 + (s i : 𝕂) ^ 2 = 1 := by exact_mod_cast hcs i
        linear_combination this
      · simp [dc, ds, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, hij]
    · ext i j
      simp [dc, ds, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
      split_ifs <;> ring
  have hX : X = 0 := by
    have hh := congrArg Matrix.toBlocks₁₂ hHo.1
    simpa [hH, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  have hH' : Kᴴ * R = fromBlocks 1 0 0 W := hX ▸ hH
  have hW : KUni W := kUnitary_of_left <| by
    have hh := congrArg Matrix.toBlocks₂₂ hHo.1
    simpa [hH', Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  have hKR : R = K * fromBlocks 1 0 0 W := by
    rw [← hH', ← Matrix.mul_assoc, hK.2, Matrix.one_mul]
  refine ⟨U₁, U₂, Vᴴ, W, c, s, hU₁, hU₂, kUnitary_conj hV, hW, hcs, ?_⟩
  have hQeq : Q = L * R * Tᴴ := by
    rw [hR]; calc Q = (L * Lᴴ) * Q * (T * Tᴴ) := by rw [hL.2, hT.2]; simp
      _ = L * (Lᴴ * Q * T) * Tᴴ := by simp [Matrix.mul_assoc]
  rw [hQeq, hKR]
  simp [L, T, K, dc, ds, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

private def sumEquiv (p : ℕ) : Fin (2 * p) ≃ (Fin p ⊕ Fin p) :=
  finProdFinEquiv.symm.trans
    { toFun := fun x => if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
      invFun := Sum.elim (0, ·) (1, ·)
      left_inv := fun ⟨a, i⟩ => by fin_cases a <;> simp
      right_inv := fun x => by cases x <;> simp }

theorem kScalarCSExhaustion {p : ℕ} {M : KMat 𝕂 (2 * p)} :
    (∃ B₁ B₂ B₃, KSupported (·.val / p) B₁ ∧ KSupported (·.val / 2) B₂ ∧
      KSupported (·.val / p) B₃ ∧ KUni B₁ ∧ KUni B₂ ∧ KUni B₃ ∧
      M = B₃ * (kPerm (GS.scalarShuffle 2 p))ᴴ * B₂ * kPerm (GS.scalarShuffle 2 p) * B₁) ↔
    KUni M := by
  let P := kPerm (𝕂 := 𝕂) (GS.scalarShuffle 2 p)
  have hP := kPerm_unitary (𝕂 := 𝕂) (GS.scalarShuffle 2 p)
  constructor
  · rintro ⟨B₁, B₂, B₃, _, _, _, hu₁, hu₂, hu₃, rfl⟩
    exact kUnitary_mul (kUnitary_mul (kUnitary_mul (kUnitary_mul hu₃ (kUnitary_conj hP)) hu₂) hP) hu₁
  · intro hM
    let e := sumEquiv p
    let flat (X : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) 𝕂) : KMat 𝕂 (2 * p) :=
      Matrix.submatrix X e e
    have hflat_mul (X Y) : flat (X * Y) = flat X * flat Y := by
      ext i j; simp only [flat, submatrix_apply, Matrix.mul_apply]
      exact (Fintype.sum_equiv e (fun k => X (e i) (e k) * Y (e k) (e j))
        (fun k => X (e i) k * Y k (e j)) fun _ => rfl).symm
    have hflat_one : flat 1 = 1 := by ext i j; simp [flat, Matrix.one_apply, e.injective.eq_iff]
    have hflat_u {X} (hX : KUni X) : KUni (flat X) :=
      ⟨by change flat Xᴴ * flat X = 1; rw [← hflat_mul, hX.1, hflat_one],
       by change flat X * flat Xᴴ = 1; rw [← hflat_mul, hX.2, hflat_one]⟩
    let Q : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) 𝕂 := Matrix.submatrix M e.symm e.symm
    have hQ : KUni Q :=
      ⟨by ext i j; have h := congrFun (congrFun hM.1 (e.symm i)) (e.symm j)
          simpa only [Q, submatrix_apply, Matrix.conjTranspose_apply, Matrix.mul_apply,
            Matrix.one_apply, e.symm.injective.eq_iff] using
            (Fintype.sum_equiv e.symm (fun k => star (M (e.symm k) (e.symm i)) * M (e.symm k) (e.symm j))
              (fun k => star (M k (e.symm i)) * M k (e.symm j)) fun _ => rfl).trans h,
       by ext i j; have h := congrFun (congrFun hM.2 (e.symm i)) (e.symm j)
          simpa only [Q, submatrix_apply, Matrix.conjTranspose_apply, Matrix.mul_apply,
            Matrix.one_apply, e.symm.injective.eq_iff] using
            (Fintype.sum_equiv e.symm (fun k => M (e.symm i) (e.symm k) * star (M (e.symm j) (e.symm k)))
              (fun k => M (e.symm i) k * star (M (e.symm j) k)) fun _ => rfl).trans h⟩
    obtain ⟨U₁, U₂, V₁, V₂, c, s, hU₁, hU₂, hV₁, hV₂, hcs, hfac⟩ := exists_ksquare_cs Q hQ
    have hlbl (x : Fin 2 × Fin p) : (finProdFinEquiv x).val / p = x.1.val := by
      have hp : 0 < p := Nat.zero_le _ |>.trans_lt x.2.isLt
      change (x.2.val + p * x.1.val) / p = x.1.val
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt x.2.isLt, Nat.zero_add]
    have hsplit_bd (X Y : KMat 𝕂 p) : KSupported (·.val / p) (flat (fromBlocks X 0 0 Y)) := by
      intro i j hij
      have hne : (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1 := fun h => hij <| by
        have hi := hlbl (finProdFinEquiv.symm i); have hj := hlbl (finProdFinEquiv.symm j)
        simp only [Equiv.apply_symm_apply] at hi hj
        exact hi.trans ((congrArg Fin.val h).trans hj.symm)
      change fromBlocks X 0 0 Y
        (if (finProdFinEquiv.symm i).1 = 0 then Sum.inl (finProdFinEquiv.symm i).2 else Sum.inr (finProdFinEquiv.symm i).2)
        (if (finProdFinEquiv.symm j).1 = 0 then Sum.inl (finProdFinEquiv.symm j).2 else Sum.inr (finProdFinEquiv.symm j).2) = 0
      rcases hxi : finProdFinEquiv.symm i with ⟨a, u⟩
      rcases hxj : finProdFinEquiv.symm j with ⟨b, v⟩
      rw [hxi, hxj] at hne
      fin_cases a <;> fin_cases b <;> simp at hne <;> simp
    have hshuf_lbl (i : Fin (2 * p)) :
        (GS.scalarShuffle 2 p i).val / 2 = (finProdFinEquiv.symm i).2.val := by
      let x := finProdFinEquiv.symm i
      have hcast {a b : ℕ} (h : a = b) (z : Fin a) : (cast (congrArg Fin h) z).val = z.val := by
        cases h; rfl
      change (cast (congrArg Fin (Nat.mul_comm p 2)) (finProdFinEquiv (x.2, x.1))).val / 2 = x.2.val
      rw [hcast (Nat.mul_comm p 2)]
      change (x.1.val + 2 * x.2.val) / 2 = x.2.val
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt x.1.isLt, Nat.zero_add]
    let dc : KMat 𝕂 p := diagonal fun i => (c i : 𝕂)
    let ds : KMat 𝕂 p := diagonal fun i => (s i : 𝕂)
    let Kcs := fromBlocks dc (-ds) ds dc
    have hK_bd : KSupported (·.val / 2) (P * flat Kcs * Pᴴ) := by
      intro i j hij
      let σ := GS.scalarShuffle 2 p
      have hne : (finProdFinEquiv.symm (σ.symm i)).2 ≠ (finProdFinEquiv.symm (σ.symm j)).2 := fun h => hij <| by
        have hi := hshuf_lbl (σ.symm i); have hj := hshuf_lbl (σ.symm j)
        simp only [σ, Equiv.apply_symm_apply] at hi hj
        exact hi.trans ((congrArg Fin.val h).trans hj.symm)
      simp only [P, kPerm_conj, mul_kPerm_apply, kPerm_mul_apply]
      change Kcs
        (if (finProdFinEquiv.symm (σ.symm i)).1 = 0 then Sum.inl (finProdFinEquiv.symm (σ.symm i)).2 else Sum.inr (finProdFinEquiv.symm (σ.symm i)).2)
        (if (finProdFinEquiv.symm (σ.symm j)).1 = 0 then Sum.inl (finProdFinEquiv.symm (σ.symm j)).2 else Sum.inr (finProdFinEquiv.symm (σ.symm j)).2) = 0
      rcases hxi : finProdFinEquiv.symm (σ.symm i) with ⟨a, u⟩
      rcases hxj : finProdFinEquiv.symm (σ.symm j) with ⟨b, v⟩
      rw [hxi, hxj] at hne
      change u ≠ v at hne
      fin_cases a <;> fin_cases b <;> simp [Kcs, dc, ds, hne]
    have hU_split {X Y : KMat 𝕂 p} (hX : KUni X) (hY : KUni Y) :
        KUni (fromBlocks X 0 0 Y) := by
      constructor <;> simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
        ← Matrix.fromBlocks_one, hX.1, hX.2, hY.1, hY.2]
    refine ⟨flat (fromBlocks V₁ 0 0 V₂), P * flat Kcs * Pᴴ, flat (fromBlocks U₁ 0 0 U₂),
      hsplit_bd _ _, hK_bd, hsplit_bd _ _, hflat_u (hU_split hV₁ hV₂),
      kUnitary_mul (kUnitary_mul hP (hflat_u (kcs_unitary c s hcs))) (kUnitary_conj hP),
      hflat_u (hU_split hU₁ hU₂), ?_⟩
    have hM_eq : flat Q = M := by ext i j; simp [flat, Q]
    rw [← hM_eq, hfac, hflat_mul, hflat_mul]
    calc flat (fromBlocks U₁ 0 0 U₂) * flat Kcs * flat (fromBlocks V₁ 0 0 V₂)
      _ = flat (fromBlocks U₁ 0 0 U₂) * (Pᴴ * P) * flat Kcs * (Pᴴ * P) * flat (fromBlocks V₁ 0 0 V₂) := by
        rw [hP.1, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by dsimp [P]; simp only [Matrix.mul_assoc]

end RCLikeCS

theorem scalar_exhaustion {p : ℕ} {M : GS.Mat (2 * p)} :
    GS.InA3Orth p 2 p (GS.permMatrix (GS.scalarShuffle 2 p))
      (GS.permMatrix (GS.scalarShuffle 2 p))ᵀ M ↔ GS.Orthogonal M := by
  simpa only [GS.InA3Orth, GS.BlockDiagonal, GS.Supported, GS.product3, KSupported,
    kPerm_real_eq, kUnitary_real_iff, Matrix.conjTranspose_eq_transpose_of_trivial] using
    kScalarCSExhaustion (𝕂 := ℝ) (p := p) (M := M)

end GS.Results.CosineSine

namespace GS.Results.UnitaryCosineSine
open GS.UnitaryGeometry

theorem scalar_exhaustion {p : ℕ} {M : GS.CMat (2 * p)} :
    CInA3Unitary p 2 p (cPermMatrix (GS.scalarShuffle 2 p))
      (cPermMatrix (GS.scalarShuffle 2 p))ᴴ M ↔ GS.Unitary M :=
  GS.Results.CosineSine.kScalarCSExhaustion (𝕂 := ℂ)

end GS.Results.UnitaryCosineSine
