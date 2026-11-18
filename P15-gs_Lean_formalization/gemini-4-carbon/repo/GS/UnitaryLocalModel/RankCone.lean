module

public import GS.UnitaryNonmanifold.ScalarBridge
public import GS.Frobenius
public import GS.GlobalGeometry.OriginalGImage
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS GS.UnitaryGeometry GS.UnitaryNonmanifold
open scoped BigOperators ComplexOrder MatrixOrder

namespace GS.UnitaryLocalModel

abbrev AxisVector := Fin 3 → ℝ
def OnSphere (u : AxisVector) : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

def pauli (u : AxisVector) : CMat 2 :=
  !![(u 0 : ℂ), (u 1 : ℂ) - Complex.I * (u 2 : ℂ);
      (u 1 : ℂ) + Complex.I * (u 2 : ℂ), -(u 0 : ℂ)]

theorem continuous_pauli : Continuous pauli :=
  continuous_pi fun i => continuous_pi fun j => by fin_cases i <;> fin_cases j <;> simp [pauli] <;> fun_prop

theorem pauli_conjTranspose (u : AxisVector) : (pauli u)ᴴ = pauli u := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply] <;> ring

theorem pauli_square (u : AxisVector) :
    pauli u * pauli u = ((u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 : ℝ) : ℂ) • (1 : CMat 2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pauli_neg (u : AxisVector) : pauli (-u) = -pauli u := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring

theorem exists_sphere_pauli (H : CMat 2) (hH : Hᴴ = H) (ht : Matrix.trace H = 0) (hs : H * H = 1) :
    ∃ u : AxisVector, OnSphere u ∧ pauli u = H := by
  let u : AxisVector := ![(H 0 0).re, (H 1 0).re, (H 1 0).im]
  have hdiag : (H 0 0).im = 0 := by
    have hh := congrArg Complex.im (congrFun (congrFun hH 0) 0)
    simp [Matrix.conjTranspose_apply] at hh; linarith
  have htrace : H 1 1 = -H 0 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using ht
  have hpu : pauli u = H := by
    ext i j; fin_cases i <;> fin_cases j
    · exact Complex.ext (by simp [pauli, u]) (by simp [pauli, u, hdiag])
    · change pauli u 0 1 = H 0 1; rw [show H 0 1 = star (H 1 0) from (congrFun (congrFun hH 0) 1).symm]
      exact Complex.ext (by simp [pauli, u]) (by simp [pauli, u])
    · exact Complex.ext (by simp [pauli, u]) (by simp [pauli, u])
    · change pauli u 1 1 = H 1 1; rw [htrace]; exact Complex.ext (by simp [pauli, u]) (by simp [pauli, u, hdiag])
  refine ⟨u, ?_, hpu⟩
  rw [← hpu, pauli_square] at hs
  change u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Complex.ofReal_re, Complex.one_re]
    using congrArg Complex.re (congrFun (congrFun hs 0) 0)

def middleBlock (a b : ℂ) (u : AxisVector) : CMat 2 :=
  ((a + b) / 2) • (1 : CMat 2) + ((a - b) / 2) • pauli u

theorem middleBlock_simultaneous_swap (a b : ℂ) (u : AxisVector) :
    middleBlock b a (-u) = middleBlock a b u := by
  rw [middleBlock, pauli_neg]; ext i j; simp [middleBlock]; ring

theorem middleBlock_equal (a : ℂ) (u : AxisVector) : middleBlock a a u = a • (1 : CMat 2) := by
  simp [middleBlock]

def sphereOuter {κ : Type*} (u : AxisVector) (z : κ → ℝ) : Matrix (Fin 3) κ ℝ := fun i j => u i * z j

theorem continuous_sphereOuter {κ : Type*} :
    Continuous (fun p : AxisVector × (κ → ℝ) => sphereOuter p.1 p.2) := by
  unfold sphereOuter; fun_prop

theorem sphereOuter_simultaneous_neg {κ : Type*} (u : AxisVector) (z : κ → ℝ) :
    sphereOuter (-u) (-z) = sphereOuter u z := by ext i j; simp [sphereOuter]

theorem sphereOuter_zero_fibre {κ : Type*} (u v : AxisVector) :
    sphereOuter u (0 : κ → ℝ) = sphereOuter v (0 : κ → ℝ) := by ext i j; simp [sphereOuter]

private theorem sphereOuter_col_sq {κ : Type*} {u : AxisVector} (hu : OnSphere u) (z : κ → ℝ) (j : κ) :
    sphereOuter u z 0 j ^ 2 + sphereOuter u z 1 j ^ 2 + sphereOuter u z 2 j ^ 2 = z j ^ 2 := by
  calc _ = (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * z j ^ 2 := by unfold sphereOuter; ring
    _ = z j ^ 2 := by rw [hu, one_mul]

theorem frobSq_sphereOuter {κ : Type*} [Fintype κ] {u : AxisVector} (hu : OnSphere u) (z : κ → ℝ) :
    frobSq (sphereOuter u z) = ∑ j, z j ^ 2 := by
  unfold frobSq frobInner
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]; simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by nlinarith [sphereOuter_col_sq hu z j]

theorem sphereOuter_fibres {κ : Type*} {u v : AxisVector} {z w : κ → ℝ}
    (hu : OnSphere u) (hv : OnSphere v) :
    sphereOuter u z = sphereOuter v w ↔ (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  have hunz {x : AxisVector} (hx : OnSphere x) : ∃ i, x i ≠ 0 := by
    by_contra hn; push_neg at hn; simp [OnSphere, hn 0, hn 1, hn 2] at hx
  have hz_iff {x : AxisVector} (hx : OnSphere x) (y : κ → ℝ) : sphereOuter x y = 0 ↔ y = 0 :=
    ⟨fun h => let ⟨i, hi⟩ := hunz hx; funext fun j => (mul_eq_zero.mp (congrFun (congrFun h i) j)).resolve_left hi,
     fun h => by subst h; ext; simp [sphereOuter]⟩
  have huniq {x y : AxisVector} {a b : κ → ℝ} (hx : OnSphere x) (h : sphereOuter x a = sphereOuter y b)
      (j : κ) (haj : a j ≠ 0) (hj : a j = b j) : x = y ∧ a = b := by
    have hxy : x = y := funext fun i => mul_right_cancel₀ haj (by simpa [sphereOuter, ← hj] using congrFun (congrFun h i) j)
    obtain ⟨i, hi⟩ := hunz hx
    exact ⟨hxy, funext fun k => mul_left_cancel₀ hi (by simpa [sphereOuter, ← hxy] using congrFun (congrFun h i) k)⟩
  by_cases hz : z = 0
  · subst hz; rw [(hz_iff hu 0).mpr rfl]
    exact ⟨fun h => Or.inl ⟨rfl, (hz_iff hv w).mp h.symm⟩,
      by rintro (⟨_, rfl⟩ | ⟨_, hw⟩ | ⟨_, hw⟩)
         · exact ((hz_iff hv 0).mpr rfl).symm
         · exact ((hz_iff hv w).mpr hw.symm).symm
         · exact ((hz_iff hv w).mpr (neg_eq_zero.mp hw.symm)).symm⟩
  · simp only [hz, false_and, false_or]
    refine ⟨fun h => ?_, by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); exacts [rfl, sphereOuter_simultaneous_neg v w]⟩
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by by_contra hn; push_neg at hn; exact hz (funext hn)
    have he : z j ^ 2 = w j ^ 2 := by rw [← sphereOuter_col_sq hu z j, h, sphereOuter_col_sq hv w j]
    rcases mul_eq_zero.mp (show (z j - w j) * (z j + w j) = 0 by nlinarith [he]) with hp | hp
    · exact Or.inl (huniq hu h j hj (sub_eq_zero.mp hp))
    · exact Or.inr (huniq hu (h.trans (sphereOuter_simultaneous_neg v w).symm) j hj (by change z j = -w j; linarith))

section RankCone
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_sphereOuter_le_one (u : AxisVector) (z : κ → ℝ) :
    Matrix.rank (sphereOuter u z) ≤ 1 := by
  let U : Matrix (Fin 3) (Fin 1) ℝ := fun i _ => u i
  let Z : Matrix (Fin 1) κ ℝ := fun _ j => z j
  rw [show sphereOuter u z = U * Z by ext i j; simp [sphereOuter, U, Z, Matrix.mul_apply]]
  exact (Matrix.rank_mul_le_left U Z).trans (by simpa using Matrix.rank_le_card_width U)

theorem exists_sphereOuter_of_rank_le_one (W : Matrix (Fin 3) κ ℝ) (hW : W.rank ≤ 1) :
    ∃ u : AxisVector, OnSphere u ∧ ∃ z : κ → ℝ, sphereOuter u z = W := by
  classical
  by_cases hzero : W = 0
  · refine ⟨fun i => if i = 0 then 1 else 0, by norm_num [OnSphere], 0, ?_⟩
    rw [hzero]; ext; simp [sphereOuter]
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, W i j ≠ 0 := by
    by_contra hn; apply hzero; ext i j; by_contra hij; exact hn ⟨i, j, hij⟩
  let v : AxisVector := fun i => W i j₀
  have hv : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    have hs := sq_pos_of_ne_zero (show v i₀ ≠ 0 from hij)
    fin_cases i₀ <;> dsimp at hs <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  let r := Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
  have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hrs : r ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := Real.sq_sqrt hv.le
  refine ⟨fun i => v i / r, by change (v 0 / r) ^ 2 + (v 1 / r) ^ 2 + (v 2 / r) ^ 2 = 1; field_simp [hr0]; nlinarith [hrs],
    fun j => r * W i₀ j / W i₀ j₀, ?_⟩
  ext i j
  let R : Matrix (Fin 2) (Fin 3) ℝ := fun a b => if ![i, i₀] a = b then 1 else 0
  have hrk : (W.submatrix ![i, i₀] id).rank ≤ 1 := by
    rw [← show R * W = W.submatrix ![i, i₀] id by ext a b; simp [R, Matrix.mul_apply]]
    exact (Matrix.rank_mul_le_right R W).trans hW
  have hm : W i j * W i₀ j₀ = W i j₀ * W i₀ j := by
    simpa using GS.GlobalGeometry.rank_le_one_two_column_minor (W.submatrix ![i, i₀] id) hrk j j₀
  change (W i j₀ / r) * (r * W i₀ j / W i₀ j₀) = W i j
  field_simp [hr0, hij]; nlinarith [hm]
end RankCone

def realify {κ : Type*} (z : κ → ℂ) : κ × Fin 2 → ℝ := fun p => if p.2 = 0 then (z p.1).re else (z p.1).im

theorem middleBlock_family_fibres {κ : Type*} (a b c d : κ → ℂ) {u v : AxisVector}
    (hu : OnSphere u) (hv : OnSphere v) :
    (∀ j, middleBlock (a j) (b j) u = middleBlock (c j) (d j) v) ↔
      (a = b ∧ c = d ∧ a = c) ∨ (u = v ∧ a = c ∧ b = d) ∨ (u = -v ∧ a = d ∧ b = c) := by
  have hrinj : Function.Injective (@realify κ) := fun z w h => funext fun j =>
    Complex.ext (by simpa [realify] using congrFun h (j, 0)) (by simpa [realify] using congrFun h (j, 1))
  constructor
  · intro h
    have htr (x y : ℂ) (w : AxisVector) : Matrix.trace (middleBlock x y w) = x + y := by
      simp [Matrix.trace, Fin.sum_univ_two, middleBlock, pauli]; ring
    have hsum (j : κ) : a j + b j = c j + d j := by simpa only [htr] using congrArg Matrix.trace (h j)
    let ax (H : CMat 2) : Fin 3 → ℂ := ![H 0 0 - H 1 1, H 0 1 + H 1 0, Complex.I * (H 0 1 - H 1 0)]
    have hax (x y : ℂ) (w : AxisVector) (i : Fin 3) : ax (middleBlock x y w) i = (w i : ℂ) * (x - y) := by
      fin_cases i <;> simp [ax, middleBlock, pauli] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    have hso : sphereOuter u (realify (a - b)) = sphereOuter v (realify (c - d)) := by
      ext i p
      have hh : (u i : ℂ) * (a p.1 - b p.1) = (v i : ℂ) * (c p.1 - d p.1) := by
        simpa only [hax] using congrFun (congrArg ax (h p.1)) i
      by_cases hp : p.2 = 0
      · simpa [sphereOuter, realify, hp] using congrArg Complex.re hh
      · simpa [sphereOuter, realify, hp] using congrArg Complex.im hh
    rcases (sphereOuter_fibres hu hv).mp hso with ⟨hz1, hz2⟩ | ⟨huv, hd⟩ | ⟨huv, hd⟩
    · have hab : a = b := sub_eq_zero.mp (hrinj (hz1.trans (by funext p; simp [realify])))
      have hcd : c = d := sub_eq_zero.mp (hrinj (hz2.trans (by funext p; simp [realify])))
      refine Or.inl ⟨hab, hcd, funext fun j => ?_⟩
      have hs := hsum j; rw [hab, hcd] at hs
      have hh : b j = d j := by linear_combination (1 / 2 : ℂ) * hs
      simpa [hab, hcd] using hh
    · have hdiff := hrinj hd
      have ha : a = c := funext fun j => by
        have hd0 : a j - b j = c j - d j := congrFun hdiff j
        linear_combination (1 / 2 : ℂ) * hsum j + (1 / 2 : ℂ) * hd0
      exact Or.inr (Or.inl ⟨huv, ha, funext fun j => add_left_cancel (ha ▸ hsum j)⟩)
    · have hdiff : a - b = -(c - d) := hrinj (hd.trans (by funext p; by_cases hp : p.2 = 0 <;> simp [realify, hp]))
      have ha : a = d := funext fun j => by
        have hd0 : a j - b j = -(c j - d j) := congrFun hdiff j
        linear_combination (1 / 2 : ℂ) * hsum j + (1 / 2 : ℂ) * hd0
      exact Or.inr (Or.inr ⟨huv, ha, funext fun j => by have hs := hsum j; rw [ha] at hs; linear_combination hs⟩)
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> intro j
    · rw [middleBlock_equal, middleBlock_equal]
    · rfl
    · exact middleBlock_simultaneous_swap _ _ _

def chartMiddle {d : ℕ} {κ : Type*} (ψ : (Fin d → ℝ) → (κ → ℂ)) (c z : Fin d → ℝ) (u : AxisVector) : κ → CMat 2 :=
  fun j => middleBlock (ψ (c + z) j) (ψ (c - z) j) u

theorem chartMiddle_fibres_on {d : ℕ} {κ : Type*} (ψ : (Fin d → ℝ) → (κ → ℂ)) (U : Set (Fin d → ℝ))
    (hψ : Set.InjOn ψ U) (c z c' z' : Fin d → ℝ) {u v : AxisVector}
    (hcp : c + z ∈ U) (hcm : c - z ∈ U) (hcp' : c' + z' ∈ U) (hcm' : c' - z' ∈ U)
    (hu : OnSphere u) (hv : OnSphere v) :
    chartMiddle ψ c z u = chartMiddle ψ c' z' v ↔ c = c' ∧ sphereOuter u z = sphereOuter v z' := by
  have hcdu {a b a' b' : Fin d → ℝ} (hp : a + b = a' + b') (hm : a - b = a' - b') : a = a' ∧ b = b' :=
    ⟨funext fun j => by have p := congrFun hp j; have m := congrFun hm j; dsimp at p m; linarith,
     funext fun j => by have p := congrFun hp j; have m := congrFun hm j; dsimp at p m; linarith⟩
  constructor
  · intro h
    rcases (middleBlock_family_fibres _ _ _ _ hu hv).mp (fun j => congrFun h j) with
      ⟨hzz, hzz', hcc⟩ | ⟨huv, hp, hm⟩ | ⟨huv, hp, hm⟩
    · have hz0 : z = 0 := funext fun j => by have hh := congrFun (hψ hcp hcm hzz) j; dsimp at hh; change z j = 0; linarith
      have hz'0 : z' = 0 := funext fun j => by have hh := congrFun (hψ hcp' hcm' hzz') j; dsimp at hh; change z' j = 0; linarith
      subst hz0; subst hz'0; exact ⟨by simpa using hψ hcp hcp' hcc, sphereOuter_zero_fibre u v⟩
    · obtain ⟨rfl, rfl⟩ := hcdu (hψ hcp hcp' hp) (hψ hcm hcm' hm); subst huv; exact ⟨rfl, rfl⟩
    · obtain ⟨hc, hz⟩ := hcdu (by simpa [sub_eq_add_neg] using hψ hcp hcm' hp) (by simpa using hψ hcm hcp' hm)
      rw [hc, huv, hz]; exact ⟨rfl, sphereOuter_simultaneous_neg v z'⟩
  · rintro ⟨rfl, h⟩
    rcases (sphereOuter_fibres hu hv).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · funext j; simp [chartMiddle, middleBlock_equal]
    · rfl
    · funext j; simp only [chartMiddle, ← sub_eq_add_neg, sub_neg_eq_add]; exact middleBlock_simultaneous_swap _ _ _

theorem positive_polar_unique {n : ℕ} (U V P Q : CMat n)
    (hU : GS.Unitary U) (hV : GS.Unitary V) (hP : P.PosDef) (hQ : Q.PosDef) (he : U * P = V * Q) :
    U = V ∧ P = Q := by
  have hs : P ^ 2 = Q ^ 2 := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hQ.isHermitian.eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᴴ U, ← Matrix.mul_assoc Vᴴ V, hU.1, hV.1, Matrix.one_mul, pow_two]
      using congrArg (fun T : CMat n => Tᴴ * T) he
  have hPQ : P = Q := (CFC.sq_eq_sq_iff P Q hP.posSemidef.nonneg hQ.posSemidef.nonneg).mp hs
  subst hPQ; exact ⟨hP.isUnit.mul_right_cancel he, rfl⟩

def normalizedBlockImage {q : ℕ} (L R : Fin q → CMat 2) (N : Fin q → Fin q → CMat 2) : Fin q → Fin q → CMat 2 :=
  fun i j => L i * N i j * R j

def NormalizedPositiveAnchors {q : ℕ} (Q : CMat q) (o : Fin q) (N : Fin q → Fin q → CMat 2) : Prop :=
  (∀ i, ((Q i o)⁻¹ • N i o).PosDef) ∧ (∀ j, ((Q o j)⁻¹ • N o j).PosDef)

theorem normalized_chart_fibres_on {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → (Fin q × Fin q → ℂ)) (U : Set (Fin d → ℝ)) (hψ : Set.InjOn ψ U)
    (L R L' R' : Fin q → CMat 2) (c z c' z' : Fin d → ℝ) (u v : AxisVector)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j))
    (hL' : ∀ i, GS.Unitary (L' i)) (hR' : ∀ j, GS.Unitary (R' j))
    (hRo : R o = 1) (hRo' : R' o = 1)
    (hcp : c + z ∈ U) (hcm : c - z ∈ U) (hcp' : c' + z' ∈ U) (hcm' : c' - z' ∈ U)
    (hu : OnSphere u) (hv : OnSphere v)
    (hN : NormalizedPositiveAnchors Q o (fun i j => chartMiddle ψ c z u (i, j)))
    (hN' : NormalizedPositiveAnchors Q o (fun i j => chartMiddle ψ c' z' v (i, j))) :
    normalizedBlockImage L R (fun i j => chartMiddle ψ c z u (i, j)) =
      normalizedBlockImage L' R' (fun i j => chartMiddle ψ c' z' v (i, j)) ↔
      L = L' ∧ R = R' ∧ c = c' ∧ sphereOuter u z = sphereOuter v z' := by
  have hcanL {W A B : CMat 2} (hW : GS.Unitary W) (he : W * A = W * B) : A = B := by
    simpa only [← Matrix.mul_assoc, hW.1, Matrix.one_mul] using congrArg (Wᴴ * ·) he
  have hcanR {W A B : CMat 2} (hW : GS.Unitary W) (he : A * W = B * W) : A = B := by
    simpa only [Matrix.mul_assoc, hW.2, Matrix.mul_one] using congrArg (· * Wᴴ) he
  have hout {M M' : Fin q → Fin q → CMat 2} (hM : NormalizedPositiveAnchors Q o M)
      (hM' : NormalizedPositiveAnchors Q o M') :
      normalizedBlockImage L R M = normalizedBlockImage L' R' M' ↔ L = L' ∧ R = R' ∧ M = M' := by
    refine ⟨fun he => ?_, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
    have hb (i j) : L i * M i j * R j = L' i * M' i j * R' j := congrFun (congrFun he i) j
    have hLL : L = L' := funext fun i => (positive_polar_unique _ _ _ _ (hL i) (hL' i) (hM.1 i) (hM'.1 i) <| by
      simpa only [Matrix.mul_smul, hRo, hRo', Matrix.mul_one] using congrArg ((Q i o)⁻¹ • ·) (hb i o)).1
    have hRR : R = R' := funext fun j => by
      have hj := hcanL (hL o) (by simpa only [Matrix.mul_assoc, hLL] using hb o j)
      have hscaled : ((Q o j)⁻¹ • M o j) * R j = ((Q o j)⁻¹ • M' o j) * R' j := by
        simpa only [Matrix.smul_mul] using congrArg ((Q o j)⁻¹ • ·) hj
      have hsc : (R j)ᴴ * ((Q o j)⁻¹ • M o j) = (R' j)ᴴ * ((Q o j)⁻¹ • M' o j) := by
        simpa only [Matrix.conjTranspose_mul, (hM.2 j).isHermitian.eq, (hM'.2 j).isHermitian.eq]
          using congrArg Matrix.conjTranspose hscaled
      exact Matrix.conjTranspose_injective (positive_polar_unique _ _ _ _ (hR j).conjTranspose (hR' j).conjTranspose
        (hM.2 j) (hM'.2 j) hsc).1
    exact ⟨hLL, hRR, funext fun i => funext fun j =>
      hcanR (hR j) (hcanL (hL i) (by simpa only [Matrix.mul_assoc, hLL, hRR] using hb i j))⟩
  rw [hout hN hN']
  have he : (fun i j => chartMiddle ψ c z u (i, j)) = (fun i j => chartMiddle ψ c' z' v (i, j)) ↔
      chartMiddle ψ c z u = chartMiddle ψ c' z' v :=
    ⟨fun h => funext fun p => congrFun (congrFun h p.1) p.2, fun h => congrArg (fun F i j => F (i, j)) h⟩
  rw [he, chartMiddle_fibres_on ψ U hψ c z c' z' hcp hcm hcp' hcm' hu hv]

theorem middleBlock_ratio_posDef (a b c : ℂ) (u : AxisVector) (hu : OnSphere u)
    (ha : ∃ r : ℝ, 0 < r ∧ a / c = r) (hb : ∃ s : ℝ, 0 < s ∧ b / c = s) :
    (c⁻¹ • middleBlock a b u).PosDef := by
  obtain ⟨r, hr, ha⟩ := ha; obtain ⟨s, hs, hb⟩ := hb
  have hmul (x y z w : ℂ) : middleBlock x y u * middleBlock z w u = middleBlock (x * z) (y * w) u := by
    have hh : pauli u * pauli u = (1 : CMat 2) := by rw [pauli_square, hu]; simp
    unfold middleBlock
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hh, smul_smul]
    ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hsmul : c⁻¹ • middleBlock a b u = middleBlock (r : ℂ) (s : ℂ) u := by
    rw [show c⁻¹ • middleBlock a b u = middleBlock (c⁻¹ * a) (c⁻¹ * b) u by
          ext i j; simp [middleBlock, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring,
        show c⁻¹ * a = r by simpa [div_eq_mul_inv, mul_comm] using ha,
        show c⁻¹ * b = s by simpa [div_eq_mul_inv, mul_comm] using hb]
  rw [hsmul]
  let B := middleBlock (Real.sqrt r : ℂ) (Real.sqrt s : ℂ) u
  let C := middleBlock ((Real.sqrt r : ℂ)⁻¹) ((Real.sqrt s : ℂ)⁻¹) u
  have hbr : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr))
  have hbs : (Real.sqrt s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hs))
  have hinv : C * B = 1 := by simp [C, B, hmul, hbr, hbs, middleBlock_equal]
  have hinj : Function.Injective B.mulVec := fun x y hxy => by
    simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using congrArg (C *ᵥ ·) hxy
  have hBh : Bᴴ = B := by
    simp [B, middleBlock, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, pauli_conjTranspose]
  have hsq : Bᴴ * B = middleBlock (r : ℂ) (s : ℂ) u := by
    rw [hBh]; dsimp [B]; rw [hmul]
    simp only [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le, Real.mul_self_sqrt hs.le]
  simpa only [Matrix.mul_one, hsq] using (Matrix.PosDef.one : (1 : CMat 2).PosDef).conjTranspose_mul_mul_same hinj

def axisDiagonal : CMat 2 := diagTwo 1 (-1)

theorem exists_axis_of_unitary (S : CMat 2) (hS : GS.Unitary S) :
    ∃ u : AxisVector, OnSphere u ∧ ∀ a b : ℂ, Sᴴ * diagTwo a b * S = middleBlock a b u := by
  let H := Sᴴ * axisDiagonal * S
  have hd_ct : axisDiagonalᴴ = axisDiagonal := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [axisDiagonal, diagTwo, Matrix.conjTranspose_apply]
  have hd_sq : axisDiagonal * axisDiagonal = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [axisDiagonal, diagTwo, Matrix.mul_apply, Fin.sum_univ_two]
  have hh : Hᴴ = H := by simp [H, hd_ct, Matrix.mul_assoc]
  have ht : Matrix.trace H = 0 := by
    change Matrix.trace (Sᴴ * axisDiagonal * S) = 0
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hS.2, Matrix.one_mul]
    simp [axisDiagonal, diagTwo, Matrix.trace, Fin.sum_univ_two]
  have hs : H * H = 1 := by
    calc H * H = Sᴴ * axisDiagonal * (S * Sᴴ) * axisDiagonal * S := by simp [H, Matrix.mul_assoc]
      _ = 1 := by rw [hS.2, Matrix.mul_one, Matrix.mul_assoc Sᴴ, hd_sq, Matrix.mul_one, hS.1]
  obtain ⟨u, hu, he⟩ := exists_sphere_pauli H hh ht hs
  refine ⟨u, hu, fun a b => ?_⟩
  rw [show diagTwo a b = ((a + b) / 2) • (1 : CMat 2) + ((a - b) / 2) • axisDiagonal by
    ext i j; fin_cases i <;> fin_cases j <;> simp [axisDiagonal, diagTwo] <;> ring]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS.1, ← he, H, middleBlock]

theorem middleBlock_unitary_diagonalization (u : AxisVector) (hu : OnSphere u) :
    ∃ S : CMat 2, GS.Unitary S ∧ ∀ a b : ℂ, Sᴴ * diagTwo a b * S = middleBlock a b u := by
  have hd_ct : axisDiagonalᴴ = axisDiagonal := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [axisDiagonal, diagTwo, Matrix.conjTranspose_apply]
  have hd_sq : axisDiagonal * axisDiagonal = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [axisDiagonal, diagTwo, Matrix.mul_apply, Fin.sum_univ_two]
  have hS_mid (S : CMat 2) (hS : GS.Unitary S) (he : Sᴴ * axisDiagonal * S = pauli u) (a b : ℂ) :
      Sᴴ * diagTwo a b * S = middleBlock a b u := by
    rw [show diagTwo a b = ((a + b) / 2) • (1 : CMat 2) + ((a - b) / 2) • axisDiagonal by
      ext i j; fin_cases i <;> fin_cases j <;> simp [axisDiagonal, diagTwo] <;> ring]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS.1, he, middleBlock]
  have hH : pauli u * pauli u = 1 := by rw [pauli_square, hu]; simp
  have hu0 : -1 ≤ u 0 := by dsimp [OnSphere] at hu; nlinarith [sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 0 + 1)]
  by_cases hp : u 0 = -1
  · have h1 : u 1 = 0 := by dsimp [OnSphere] at hu; rw [hp] at hu; nlinarith [sq_nonneg (u 2)]
    have h2 : u 2 = 0 := by dsimp [OnSphere] at hu; rw [hp] at hu; nlinarith [sq_nonneg (u 1)]
    have hX : GS.Unitary (!![0, 1; 1, 0] : CMat 2) := by
      constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    refine ⟨!![0, 1; 1, 0], hX, hS_mid _ hX ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [axisDiagonal, diagTwo, pauli, hp, h1, h2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · let A := (1 : CMat 2) + pauli u * axisDiagonal
    have hpos : 0 < 2 * (1 + u 0) := by linarith [lt_of_le_of_ne hu0 (Ne.symm hp)]
    let r := Real.sqrt (2 * (1 + u 0))
    have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hrs : r ^ 2 = 2 * (1 + u 0) := Real.sq_sqrt hpos.le
    have hac : pauli u * axisDiagonal + axisDiagonal * pauli u = (2 * u 0 : ℝ) • (1 : CMat 2) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, pauli, axisDiagonal,
          diagTwo, Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        norm_num [Complex.real_smul] <;> ring
    have hAA : Aᴴ * A = (2 * (1 + u 0) : ℝ) • (1 : CMat 2) := by
      have ht : axisDiagonal * pauli u * (pauli u * axisDiagonal) = (1 : CMat 2) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pauli u), hH, Matrix.one_mul, hd_sq]
      calc Aᴴ * A = (1 : CMat 2) + 1 + (pauli u * axisDiagonal + axisDiagonal * pauli u) := by
            simp only [A, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
              hd_ct, pauli_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, ht]; abel
        _ = _ := by rw [hac]; ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]; push_cast; ring
    let U := (r⁻¹ : ℝ) • A
    have hUl : Uᴴ * U = 1 := by
      simp only [U, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAA]
      rw [show r⁻¹ * (r⁻¹ * (2 * (1 + u 0))) = 1 by rw [← hrs]; field_simp [hr0], one_smul]
    have hU : GS.Unitary U := ⟨hUl, mul_eq_one_comm.mp hUl⟩
    have hHU : pauli u * U = U * axisDiagonal := by
      simp only [U, Matrix.mul_smul, Matrix.smul_mul]; congr 1; dsimp [A]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
      rw [← Matrix.mul_assoc, hH, Matrix.one_mul, Matrix.mul_assoc, hd_sq, Matrix.mul_one]; abel
    refine ⟨Uᴴ, hU.conjTranspose, hS_mid _ hU.conjTranspose ?_⟩
    rw [Matrix.conjTranspose_conjTranspose, ← hHU, Matrix.mul_assoc, hU.2, Matrix.mul_one]

end GS.UnitaryLocalModel
