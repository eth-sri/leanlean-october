module

public import OAI.Combinatorics.EuclideanRamsey.GramCompletion

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace Pointwise commutatorElement
open Filter Set

namespace EuclideanRamsey

def FiniteEuclidean := ℕ →₀ ℝ

namespace FiniteEuclidean

instance : AddCommGroup FiniteEuclidean := inferInstanceAs (AddCommGroup (ℕ →₀ ℝ))
instance : Module ℝ FiniteEuclidean := inferInstanceAs (Module ℝ (ℕ →₀ ℝ))

abbrev toF (x : FiniteEuclidean) : ℕ →₀ ℝ := x

def product (x y : FiniteEuclidean) : ℝ := x.toF.sum fun n r => r * y.toF n

instance core : InnerProductSpace.Core ℝ FiniteEuclidean where
  inner := product
  conj_inner_symm x y := by
    unfold product
    rw [Finsupp.sum_of_support_subset y.toF Finset.subset_union_right _ (by simp),
      Finsupp.sum_of_support_subset x.toF Finset.subset_union_left _ (by simp)]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  re_inner_nonneg _ := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  add_left _ _ _ := Finsupp.sum_add_index' (by simp) fun _ _ _ => add_mul _ _ _
  smul_left x y r := by
    change (r • x.toF).sum _ = r * product x y
    rw [Finsupp.sum_smul_index' (by simp)]; simp [product, Finsupp.mul_sum, mul_assoc]
  definite x h := Finsupp.ext fun n => by
    by_cases hn : n ∈ x.toF.support
    · exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => mul_self_nonneg _).mp h n hn)
    · exact Finsupp.notMem_support_iff.mp hn

instance : NormedAddCommGroup FiniteEuclidean := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ FiniteEuclidean := InnerProductSpace.ofCore core.toCore

lemma norm_sq (x : FiniteEuclidean) : ‖x‖ ^ 2 = x.toF.sum fun _ r => r ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]; simp [inner, product, Finsupp.sum, sq]

def shift (b : ℕ) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap := Finsupp.lmapDomain ℝ ℝ (fun n => 2 * n + b)
  norm_map' x := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    rw [norm_sq, norm_sq]; exact Finsupp.sum_mapDomain_index_inj fun _ _ h => by omega

def flatten : List FiniteEuclidean → FiniteEuclidean
  | [] => 0
  | x :: l => shift 0 x + shift 1 (flatten l)

lemma norm_flatten_cons (x y : FiniteEuclidean) (l k : List FiniteEuclidean) :
    ‖flatten (x :: l) - flatten (y :: k)‖ ^ 2 = ‖x - y‖ ^ 2 + ‖flatten l - flatten k‖ ^ 2 := by
  have horth (u v : FiniteEuclidean) : ⟪shift 0 u, shift 1 v⟫ = 0 := by
    change (u.toF.mapDomain (fun n => 2 * n + 0)).sum (fun k r => r * (v.toF.mapDomain (fun n => 2 * n + 1)) k) = 0
    rw [Finsupp.sum_mapDomain_index_inj fun _ _ h => by omega]
    refine Finset.sum_eq_zero fun m _ => ?_
    dsimp only; rw [Finsupp.mapDomain_of_notMem_range]
    · exact mul_zero _
    · rintro ⟨_, hm⟩; dsimp only at hm; omega
  rw [show flatten (x :: l) - flatten (y :: k) = shift 0 (x - y) + shift 1 (flatten l - flatten k) by
    simp [flatten, map_sub]; abel, norm_add_sq_real, horth, mul_zero, add_zero,
    LinearIsometry.norm_map, LinearIsometry.norm_map]

lemma flatten_append (l k l' k' : List FiniteEuclidean) (h : l.length = k.length) :
    ‖flatten (l ++ l') - flatten (k ++ k')‖ ^ 2 = ‖flatten l - flatten k‖ ^ 2 + ‖flatten l' - flatten k'‖ ^ 2 := by
  induction l generalizing k with
  | nil => cases k <;> simp_all [flatten]
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k => simp [norm_flatten_cons, ih k (Nat.add_right_cancel h), add_assoc]

def embed (d : ℕ) : Space d →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap := (Finsupp.lmapDomain ℝ ℝ Fin.val).comp
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin d)).symm.toLinearMap.comp
      (EuclideanSpace.equiv (Fin d) ℝ).toLinearMap)
  norm_map' x := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    rw [norm_sq, EuclideanSpace.norm_sq_eq]
    change (Finsupp.mapDomain Fin.val _).sum _ = _
    rw [Finsupp.sum_mapDomain_index_inj Fin.val_injective, Finsupp.sum_fintype _ _ (by simp)]
    simp [Real.norm_eq_abs, sq_abs]

def truncate (d : ℕ) (x : FiniteEuclidean) : Space d := WithLp.toLp 2 fun i => x.toF i

lemma eventually_embed_truncate (x : FiniteEuclidean) :
    ∀ᶠ d : ℕ in atTop, embed (d + 1) (truncate (d + 1) x) = x := by
  filter_upwards [eventually_ge_atTop (x.toF.support.sup id)] with d hd
  refine Finsupp.ext fun n => ?_
  change (Finsupp.mapDomain Fin.val _ : ℕ →₀ ℝ) n = x.toF n
  by_cases hn : n < d + 1
  · exact Finsupp.mapDomain_apply_of_injective Fin.val_injective _ (⟨n, hn⟩ : Fin (d + 1))
  · rw [Finsupp.mapDomain_of_notMem_range]
    · exact (Finsupp.notMem_support_iff.mp fun hm => hn (Nat.lt_succ_of_le ((Finset.le_sup (f := id) hm).trans hd))).symm
    · rintro ⟨i, rfl⟩; exact hn i.2

lemma unit_distance_constant {Y : Type*} (r : ℝ) (hr : 0 < r)
    (f : FiniteEuclidean → Y) (hf : ∀ x y, ‖x - y‖ = r → f x = f y) (x y : FiniteEuclidean) :
    f x = f y := by
  refine ((IsLocallyConstant.iff_exists_open f).mpr fun x => ?_).apply_eq_of_isPreconnected
    isPreconnected_univ (mem_univ x) (mem_univ y)
  refine ⟨Metric.ball x (2 * r), Metric.isOpen_ball, Metric.mem_ball_self (by positivity), fun y hy => ?_⟩
  let v := y - x
  have hxy : ‖v‖ ≤ 2 * r := (show ‖y - x‖ < 2 * r by simpa [Metric.mem_ball, dist_eq_norm] using hy).le
  obtain ⟨n, hn⟩ := v.toF.support.exists_notMem
  let e : FiniteEuclidean := Finsupp.single n 1
  have he : ‖e‖ ^ 2 = 1 := by rw [norm_sq]; simp [e, toF]
  have hv : ⟪v, e⟫ = 0 := by rw [real_inner_comm]; simp [inner, product, e, toF, Finsupp.notMem_support_iff.mp hn]
  let t := Real.sqrt (r ^ 2 - ‖v‖ ^ 2 / 4)
  have ht : t ^ 2 = r ^ 2 - ‖v‖ ^ 2 / 4 := Real.sq_sqrt (by nlinarith [norm_nonneg v])
  let z := x + (1 / 2 : ℝ) • v + t • e
  have hz (c : ℝ) (hc : c ^ 2 = 1 / 4) (w : FiniteEuclidean) (hw : z - w = c • v + t • e) : ‖z - w‖ = r :=
    (sq_eq_sq₀ (norm_nonneg _) hr.le).mp <| by
      rw [hw, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hv]
      simp only [Real.norm_eq_abs, mul_pow, sq_abs, he, hc]; nlinarith
  exact (hf z y (hz (-1 / 2) (by norm_num) y (by dsimp [z, v]; module))).symm.trans
    (hf z x (hz (1 / 2) (by norm_num) x (by dsimp [z]; abel)))

end FiniteEuclidean

section Fractions
variable {G : Type*} [Group G]

def RightFraction {ι : Type*} (M : Submonoid (ι → G)) (z : ι → G) : Prop :=
  ∃ u ∈ M, ∃ v ∈ M, z = u * v⁻¹

lemma RightFraction.inv {ι : Type*} {M : Submonoid (ι → G)} {z : ι → G} (h : RightFraction M z) :
    RightFraction M z⁻¹ := by
  obtain ⟨u, hu, v, hv, rfl⟩ := h; exact ⟨v, hv, u, hu, by group⟩

lemma RightFraction.conj {ι : Type*} {M : Submonoid (ι → G)} (hM : ∀ g : G, (fun _ => g) ∈ M)
    {z : ι → G} (h : RightFraction M z) (g : G) : RightFraction M (fun i => g * z i * g⁻¹) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := h
  exact ⟨(fun _ => g) * u, M.mul_mem (hM g) hu, (fun _ => g) * v, M.mul_mem (hM g) hv,
    by ext; simp only [Pi.mul_apply, Pi.inv_apply]; group⟩

def Derived (N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n + 1 => ⁅Derived N n, Derived N n⁆

instance derived_normal (N : Subgroup G) [hN : N.Normal] (n : ℕ) : (Derived N n).Normal := by
  induction n with
  | zero => exact hN
  | succ _ ih => exact @Subgroup.commutator_normal _ _ _ _ ih ih

lemma derived_le (N : Subgroup G) [N.Normal] (n : ℕ) : Derived N n ≤ N := by
  induction n with | zero => exact le_rfl | succ _ ih => exact (Subgroup.commutator_le_left _ _).trans ih

theorem derived_subset_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Submonoid (ι → G)) (N : Subgroup G) [N.Normal]
    (hd : ∀ g : G, (fun _ => g) ∈ M)
    (hi : ∀ i j : ι, i ≠ j → ∀ v ∈ M, ∃ b ∈ M, v i * b i = 1 ∧ v j * b j = 1)
    (hc : ∀ i j : ι, i ≠ j → ∀ a ∈ N, ∀ b ∈ N, ∃ z ∈ M, z i = a ∧ z j = b)
    (i : ι) {x : G} (hx : x ∈ Derived N (Fintype.card ι - 2)) :
    RightFraction M (Pi.mulSingle i x) := by
  let subF (S : Finset ι) (p : ι) : Subgroup G :=
    { carrier := {g | ∃ z, RightFraction M z ∧ z p = g ∧ ∀ l ∈ S, l ≠ p → z l = 1}
      one_mem' := ⟨1, ⟨1, M.one_mem, 1, M.one_mem, by simp⟩, rfl, fun _ _ _ => rfl⟩
      inv_mem' := fun ⟨z, hz, hzp, hzs⟩ => ⟨z⁻¹, hz.inv, by simp [hzp], fun l hl hlp => by simp [hzs l hl hlp]⟩
      mul_mem' := fun {a b} ⟨z₁, ⟨u, hu, v, hv, he1⟩, h1p, h1s⟩ ⟨z₂, hz₂, h2p, h2s⟩ => by
        obtain ⟨c, hc', d, hd', he2⟩ := hz₂.conj hd (v p)⁻¹
        refine ⟨(u * c) * (v * d)⁻¹, ⟨u * c, M.mul_mem hu hc', v * d, M.mul_mem hv hd', rfl⟩, ?_, fun l hl hlp => ?_⟩
        · have hv2 := congrFun he2 p; have hv1 := congrFun he1 p
          simp only [Pi.mul_apply, Pi.inv_apply] at hv1 hv2 ⊢
          rw [show u p * c p * (v p * d p)⁻¹ = u p * (c p * (d p)⁻¹) * (v p)⁻¹ by group, ← hv2, h2p, ← h1p, hv1]; group
        · have hv2 := congrFun he2 l; have hv1 := congrFun he1 l
          simp only [Pi.mul_apply, Pi.inv_apply] at hv1 hv2 ⊢
          have h10 := h1s l hl hlp; rw [hv1] at h10
          rw [show u l * c l * (v l * d l)⁻¹ = u l * (c l * (d l)⁻¹) * (v l)⁻¹ by group, ← hv2, h2s l hl hlp,
            show u l * ((v p)⁻¹ * 1 * (v p)⁻¹⁻¹) * (v l)⁻¹ = u l * (v l)⁻¹ by group, h10] }
  have mul_pair (S : Finset ι) {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
      (p q : ι) (hpq : p ≠ q) (hs : ∀ l ∈ S, l ≠ p → l ≠ q → t l = 1) :
      ∃ w, RightFraction M w ∧ ∀ l ∈ S, w l = z l * t l := by
    obtain ⟨u, hu, v, hv, rfl⟩ := hz; obtain ⟨c, hc', d, hd', rfl⟩ := ht
    obtain ⟨b, hb, hbp, hbq⟩ := hi p q hpq v hv
    refine ⟨(u * b * c) * (v * b * d)⁻¹, ⟨_, M.mul_mem (M.mul_mem hu hb) hc', _, M.mul_mem (M.mul_mem hv hb) hd', rfl⟩, fun l hl => ?_⟩
    simp only [Pi.mul_apply, Pi.inv_apply]
    have hcomm : v l * b l * (c l * (d l)⁻¹) = c l * (d l)⁻¹ * (v l * b l) := by
      by_cases hlp : l = p
      · subst l; simp [hbp]
      · by_cases hlq : l = q
        · subst l; simp [hbq]
        · have := hs l hl hlp hlq; simp only [Pi.mul_apply, Pi.inv_apply] at this; simp [this]
    calc u l * b l * c l * (v l * b l * d l)⁻¹
      _ = u l * b l * ((c l * (d l)⁻¹) * (v l * b l)⁻¹) := by group
      _ = u l * b l * ((v l * b l)⁻¹ * (c l * (d l)⁻¹)) := by rw [(Commute.inv_left hcomm).eq]
      _ = u l * (v l)⁻¹ * (c l * (d l)⁻¹) := by group
  have base (S : Finset ι) (hS : S.card ≤ 2) (p : ι) (hp : p ∈ S) : N ≤ subF S p := fun a ha => by
    by_cases h : ∃ q ∈ S, q ≠ p
    · obtain ⟨q, hqS, hqp⟩ := h
      obtain ⟨z, hz, hzp, hzq⟩ := hc p q hqp.symm a ha 1 N.one_mem
      refine ⟨z, ⟨z, hz, 1, M.one_mem, by simp⟩, hzp, fun l hl hlp => ?_⟩
      have hlj : l = q := Classical.byContradiction fun hlq => by
        have hs := Finset.card_le_card (show {p, q, l} ⊆ S by intro m hm; simp at hm; rcases hm with rfl | rfl | rfl <;> assumption)
        simp [hqp.symm, Ne.symm hlp, Ne.symm hlq] at hs; omega
      exact hlj ▸ hzq
    · exact ⟨fun _ => a, ⟨_, hd a, 1, M.one_mem, by simp⟩, rfl, fun l hl hlp => (h ⟨l, hl, hlp⟩).elim⟩
  have main (n : ℕ) : ∀ (S : Finset ι), S.card ≤ n + 2 → ∀ p ∈ S, Derived N n ≤ subF S p := by
    induction n with
    | zero => exact base
    | succ n ih =>
      intro S hS p hp
      by_cases hsmall : S.card ≤ 2
      · exact (derived_le N _).trans (base S hsmall p hp)
      have hgt : 1 < (S.erase p).card := by rw [Finset.card_erase_of_mem hp]; omega
      obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hgt
      obtain ⟨hjp, hjS⟩ := Finset.mem_erase.mp hj
      obtain ⟨hkp, hkS⟩ := Finset.mem_erase.mp hk
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      obtain ⟨z, hz, hzp, hzs⟩ := ih (S.erase j) (by rw [Finset.card_erase_of_mem hjS]; omega) p
        (Finset.mem_erase.mpr ⟨hjp.symm, hp⟩) ha
      obtain ⟨t, ht, htp, hts⟩ := ih (S.erase k) (by rw [Finset.card_erase_of_mem hkS]; omega) p
        (Finset.mem_erase.mpr ⟨hkp.symm, hp⟩) hb
      have hzs' (l) (hl : l ∈ S) (hlp : l ≠ p) (hlj : l ≠ j) : z l = 1 := hzs l (Finset.mem_erase.mpr ⟨hlj, hl⟩) hlp
      have hts' (l) (hl : l ∈ S) (hlp : l ≠ p) (hlk : l ≠ k) : t l = 1 := hts l (Finset.mem_erase.mpr ⟨hlk, hl⟩) hlp
      obtain ⟨w₁, hw₁, he₁⟩ := mul_pair S hz ht p k hkp.symm hts'
      obtain ⟨w₂, hw₂, he₂⟩ := mul_pair S hw₁ hz.inv p j hjp.symm fun l hl hlp hlj => by simp [hzs' l hl hlp hlj]
      obtain ⟨w₃, hw₃, he₃⟩ := mul_pair S hw₂ ht.inv p k hkp.symm fun l hl hlp hlk => by simp [hts' l hl hlp hlk]
      refine ⟨w₃, hw₃, ?_, fun l hl hlp => ?_⟩
      · rw [he₃ p hp, he₂ p hp, he₁ p hp]; simp [hzp, htp, commutatorElement_def]
      · rw [he₃ l hl, he₂ l hl, he₁ l hl]; simp only [Pi.inv_apply]
        by_cases hlj : l = j
        · subst l; simp [hts' j hjS hjp hjk]
        · simp [hzs' l hl hlp hlj]
  obtain ⟨z, hz, hzi, hzs⟩ := main (Fintype.card ι - 2) Finset.univ (by simp; omega) i (Finset.mem_univ i) hx
  have he : z = Pi.mulSingle i x := by
    ext l; by_cases hl : l = i
    · subst l; simp [hzi]
    · simp [Pi.mulSingle_eq_of_ne hl, hzs l (Finset.mem_univ l) hl]
  exact he ▸ hz

end Fractions

abbrev LetterGroup := FreeGroup FiniteEuclidean
abbrev Strings := FreeMonoid FiniteEuclidean

def AugKernel : Subgroup LetterGroup :=
  (FreeGroup.lift fun _ : FiniteEuclidean => Multiplicative.ofAdd (1 : ℤ)).ker

instance : AugKernel.Normal := MonoidHom.normal_ker _

inductive UnitWords {ι : Type*} (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℕ → Prop
  | diag (g : LetterGroup) : UnitWords a (fun _ => g) 0
  | copy (b : ι → FiniteEuclidean) (h : ∀ i j, ‖b i - b j‖ = ‖a i - a j‖) :
      UnitWords a (fun i => FreeGroup.of (b i)) 1
  | mul {u v m n} : UnitWords a u m → UnitWords a v n → UnitWords a (u * v) (m + n)

inductive Path {ι : Type*} (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℝ → Prop
  | diag (g : LetterGroup) : Path a (fun _ => g) 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : ∀ i j, ‖b i - b j‖ ^ 2 = u * ‖a i - a j‖ ^ 2) :
      Path a (fun i => FreeGroup.of (b i)) u
  | mul {u v lmb μ} : Path a u lmb → Path a v μ → Path a (u * v) (lmb + μ)

lemma UnitWords.path {ι : Type*} {a : ι → FiniteEuclidean} {w n} (h : UnitWords a w n) : Path a w n := by
  induction h with
  | diag g => simpa using Path.diag g
  | copy b hb => simpa using Path.copy b fun i j => by simp [hb i j]
  | mul _ _ ih1 ih2 => simpa using ih1.mul ih2

def unitMonoid {ι : Type*} (a : ι → FiniteEuclidean) : Submonoid (ι → LetterGroup) where
  carrier := {u | ∃ n, UnitWords a u n}
  one_mem' := ⟨0, .diag 1⟩
  mul_mem' := fun ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, hm.mul hn⟩

lemma extend_pair_E {ι : Type*} (a : ι → FiniteEuclidean) (i j : ι) (z z' : FiniteEuclidean)
    (h : ‖z' - z‖ = ‖a j - a i‖) :
    ∃ b : ι → FiniteEuclidean, b i = z ∧ b j = z' ∧ ∀ k l, ‖b k - b l‖ = ‖a k - a l‖ := by
  let R := (ℝ ∙ (a j - a i - (z' - z)))ᗮ.reflection
  refine ⟨fun k => z + R (a k - a i), by simp, ?_, fun k l => by
    simp [add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right]⟩
  simpa using congrArg (z + ·) (Submodule.reflection_sub h.symm)

lemma unit_pair_inverse {ι : Type*} (a : ι → FiniteEuclidean) (i j : ι) (_ : i ≠ j)
    (u : ι → LetterGroup) (hu : u ∈ unitMonoid a) :
    ∃ b ∈ unitMonoid a, u i * b i = 1 ∧ u j * b j = 1 := by
  obtain ⟨m, hm⟩ := hu
  suffices ∃ v n, UnitWords a v n ∧ v i = (u i)⁻¹ ∧ v j = (u j)⁻¹ from
    let ⟨v, n, hv, hi, hj⟩ := this; ⟨v, ⟨n, hv⟩, by simp [hi], by simp [hj]⟩
  induction hm with
  | diag g => exact ⟨_, 0, .diag g⁻¹, rfl, rfl⟩
  | copy b hb =>
    obtain ⟨c, hci, hcj, hc⟩ := extend_pair_E a i j (b j) (b i) (by rw [hb i j, norm_sub_rev (a i)])
    exact ⟨(fun _ => (FreeGroup.of (b i))⁻¹) * (fun k => FreeGroup.of (c k)) *
      (fun _ => (FreeGroup.of (b j))⁻¹), 1,
      by simpa using ((UnitWords.diag _).mul (.copy c hc)).mul (.diag _),
      by simp [hci], by simp [hcj]⟩
  | mul _ _ ihu ihv =>
    obtain ⟨u', m', hu', hui, huj⟩ := ihu; obtain ⟨v', n', hv', hvi, hvj⟩ := ihv
    exact ⟨v' * u', n' + m', hv'.mul hu', by simp [hui, hvi], by simp [huj, hvj]⟩

lemma unit_pair_coverage {ι : Type*} (a : ι → FiniteEuclidean) (ha : Function.Injective a)
    (i j : ι) (hij : i ≠ j) (g : LetterGroup) (hg : g ∈ AugKernel) (h : LetterGroup) (hh : h ∈ AugKernel) :
    ∃ z ∈ unitMonoid a, z i = g ∧ z j = h := by
  let pHom : (ι → LetterGroup) →* LetterGroup × LetterGroup :=
    { toFun := fun u => (u i, u j), map_one' := rfl, map_mul' := fun _ _ => rfl }
  let P : Subgroup (LetterGroup × LetterGroup) :=
    { (unitMonoid a).map pHom with
      inv_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        obtain ⟨v, hv, hi, hj⟩ := unit_pair_inverse a i j hij u hu
        exact ⟨v, hv, Prod.ext (mul_left_cancel (hi.trans (mul_inv_cancel _).symm))
          (mul_left_cancel (hj.trans (mul_inv_cancel _).symm))⟩ }
  have hdiag (k : LetterGroup) : (k, k) ∈ P := ⟨_, ⟨0, .diag k⟩, rfl⟩
  let Q : Subgroup LetterGroup := P.comap (MonoidHom.inl _ _)
  have : Q.Normal := ⟨fun x hx k => by simpa [Q] using P.mul_mem (P.mul_mem (hdiag k) hx) (hdiag k⁻¹)⟩
  have hle : AugKernel ≤ Q := by
    let q := QuotientGroup.mk' Q
    have hconst (x y : FiniteEuclidean) : q (FreeGroup.of x) = q (FreeGroup.of y) := by
      refine FiniteEuclidean.unit_distance_constant ‖a i - a j‖
        (norm_pos_iff.mpr (sub_ne_zero.mpr (ha.ne hij))) (fun z => q (FreeGroup.of z))
        (fun x y hxy => QuotientGroup.eq_iff_div_mem.mpr ?_) x y
      obtain ⟨b, hbi, hbj, hb⟩ := extend_pair_E a i j x y (by simpa [norm_sub_rev] using hxy)
      have hcopy : (FreeGroup.of x, FreeGroup.of y) ∈ P :=
        ⟨fun k => FreeGroup.of (b k), ⟨1, .copy b hb⟩, Prod.ext (congrArg FreeGroup.of hbi) (congrArg FreeGroup.of hbj)⟩
      simpa [div_eq_mul_inv, Q] using P.mul_mem hcopy (hdiag (FreeGroup.of y)⁻¹)
    let cy : Multiplicative ℤ →* (LetterGroup ⧸ Q) :=
      { toFun := fun n => (q (FreeGroup.of 0)) ^ Multiplicative.toAdd n, map_one' := by simp, map_mul' := zpow_add _ }
    have he : q = cy.comp (FreeGroup.lift fun _ => Multiplicative.ofAdd 1) := by
      apply FreeGroup.ext_hom; intro x; simpa [cy, q] using hconst x 0
    intro x hx; rw [← QuotientGroup.eq_one_iff]; change q x = 1; rw [he]; exact (congrArg cy hx).trans cy.map_one
  obtain ⟨v, hv, hv'⟩ : (g, h) ∈ P := by
    simpa using P.mul_mem (hle hg) (P.mul_mem (hdiag h) (hle (AugKernel.inv_mem hh)))
  exact ⟨v, hv, congrArg Prod.fst hv', congrArg Prod.snd hv'⟩

def BoundedFrac {ι : Type*} (a : ι → FiniteEuclidean) (z : ι → LetterGroup) (c : ℕ) : Prop :=
  ∃ u v m n, UnitWords a u m ∧ UnitWords a v n ∧ z = u * v⁻¹ ∧ m + n ≤ c

lemma BoundedFrac.one {ι : Type*} (a : ι → FiniteEuclidean) : BoundedFrac a 1 0 :=
  ⟨1, 1, 0, 0, .diag 1, .diag 1, by simp, le_rfl⟩

lemma BoundedFrac.inv {ι : Type*} {a : ι → FiniteEuclidean} {z c} (h : BoundedFrac a z c) :
    BoundedFrac a z⁻¹ c :=
  let ⟨u, v, m, n, hm, hn, he, hc⟩ := h; ⟨v, u, n, m, hn, hm, by rw [he]; group, by omega⟩

lemma BoundedFrac.conj {ι : Type*} {a : ι → FiniteEuclidean} {z c} (h : BoundedFrac a z c) (g : LetterGroup) :
    BoundedFrac a (fun i => g * z i * g⁻¹) c := by
  obtain ⟨u, v, m, n, hm, hn, rfl, hc⟩ := h
  exact ⟨(fun _ => g) * u, (fun _ => g) * v, m, n, by simpa using (UnitWords.diag g).mul hm,
    by simpa using (UnitWords.diag g).mul hn, by ext; simp only [Pi.mul_apply, Pi.inv_apply]; group, hc⟩

lemma BoundedFrac.mul_single {ι : Type*} [DecidableEq ι] {a : ι → FiniteEuclidean} {z c d}
    (hz : BoundedFrac a z c) (i : ι) {g : LetterGroup} (hg : BoundedFrac a (Pi.mulSingle i g) d) :
    BoundedFrac a (z * Pi.mulSingle i g) (c + d) := by
  obtain ⟨u, v, m, n, hm, hn, rfl, hc⟩ := hz
  have hh := hg.conj (v i)⁻¹
  rw [show (fun j => (v i)⁻¹ * (Pi.mulSingle i g : ι → LetterGroup) j * ((v i)⁻¹)⁻¹) =
      Pi.mulSingle i ((v i)⁻¹ * g * v i) by ext j; by_cases hj : j = i <;> simp [hj]] at hh
  obtain ⟨u', v', k, l, hk, hl, he, hd⟩ := hh
  refine ⟨u * u', v * v', m + k, n + l, hm.mul hk, hn.mul hl, ?_, by omega⟩
  have ht : v⁻¹ * Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹ * g * v i) * v⁻¹ := by
    ext j; by_cases hj : j = i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc, ht, he]; group

def singleCost {ι : Type*} [DecidableEq ι] (a : ι → FiniteEuclidean) (i : ι) (g : LetterGroup) : ℕ :=
  sInf {c | BoundedFrac a (Pi.mulSingle i g) c}

section OrbitAvg
variable {H ι G : Type*} [Group H] [Fintype H] [Group G]

def orbitAvg (w : H → ι → G) (k : H) (i : ι) : G :=
  ((Finset.univ : Finset H).toList.map fun h => w (h * k) i).prod

def OrbitIn (N : Subgroup G) (w : H → ι → G) (i : ι) : Prop :=
  ∀ g k : H, w g i * (w k i)⁻¹ ∈ N

lemma orbitIn_avg {N : Subgroup G} [N.Normal] {w : H → ι → G} {i : ι} (hw : OrbitIn N w i) :
    OrbitIn N (orbitAvg w) i := fun g k => by
  rw [← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
  change (QuotientGroup.mk' N) (orbitAvg w g i) = (QuotientGroup.mk' N) (orbitAvg w k i)
  simp only [orbitAvg, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun h _ =>
    QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using hw (h * g) (h * k)))

lemma orbitIn_raise (N : Subgroup G) [N.Normal] {w : H → ι → G} {i : ι} (hw : OrbitIn N w i) :
    OrbitIn ⁅N, N⁆ (orbitAvg fun h j => w h j * (w 1 i)⁻¹) i := fun g k => by
  let u (h : H) := w h i * (w 1 i)⁻¹
  let q := QuotientGroup.mk' ⁅N, N⁆
  rw [← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
  change q ((Finset.univ.toList.map fun h => u (h * g)).prod) = q ((Finset.univ.toList.map fun h => u (h * k)).prod)
  simp only [map_list_prod, List.map_map]
  have hp : (Finset.univ.toList.map (· * (k * g⁻¹))).Perm Finset.univ.toList :=
    (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map (mul_left_injective _))
      (Finset.nodup_toList _)).mpr fun h => by simp; exact ⟨h * g * k⁻¹, by group⟩
  have hp' := hp.map fun h => q (u (h * g))
  simp only [List.map_map, Function.comp_def, show ∀ h : H, h * (k * g⁻¹) * g = h * k by intro; group] at hp'
  exact (hp'.prod_eq' (List.pairwise_map.mpr (List.pairwise_of_forall fun a b =>
    commutatorElement_eq_one_iff_commute.mp <| by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.commutator_mem_commutator (hw _ 1) (hw _ 1))))).symm

inductive Evolution : (H → ι → G) → ℕ → (H → ι → G) → ℕ → Prop
  | refl (w m) : Evolution w m w m
  | normalize {w m v n} : Evolution w m v n → (a : G) → Evolution w m (fun h i => v h i * a) n
  | average {w m v n} : Evolution w m v n → Evolution w m (orbitAvg v) (Fintype.card H * n)

lemma Evolution.trans {w v u : H → ι → G} {m n k} (h : Evolution w m v n) (h' : Evolution v n u k) :
    Evolution w m u k := by
  induction h' with | refl => exact h | normalize _ a ih => exact ih.normalize a | average _ ih => exact ih.average

lemma Evolution.orbitIn {w v : H → ι → G} {m n} (h : Evolution w m v n)
    {N : Subgroup G} [N.Normal] {i : ι} (hw : OrbitIn N w i) : OrbitIn N v i := by
  induction h with
  | refl => exact hw
  | normalize _ _ ih => intro g k; simpa [mul_assoc] using ih g k
  | average _ ih => exact orbitIn_avg ih

lemma evolve_finite [Fintype ι] (w : H → ι → G) (m : ℕ) (Good : ι → (H → ι → G) → ℕ → Prop)
    (preserve : ∀ {v n u k}, Evolution v n u k → ∀ i, Good i v n → Good i u k)
    (improve : ∀ {v n}, Evolution w m v n → ∀ i, ∃ u k, Evolution v n u k ∧ Good i u k) :
    ∃ v n, Evolution w m v n ∧ ∀ i, Good i v n := by
  classical
  have aux (t : Finset ι) : ∃ v n, Evolution w m v n ∧ ∀ i ∈ t, Good i v n := by
    induction t using Finset.induction_on with
    | empty => exact ⟨w, m, .refl _ _, by simp⟩
    | insert i t _ ih =>
      obtain ⟨v, n, hev, hv⟩ := ih; obtain ⟨u, k, heu, hu⟩ := improve hev i
      exact ⟨u, k, hev.trans heu, fun j hj => (Finset.mem_insert.mp hj).elim (· ▸ hu) (preserve heu j ∘ hv j)⟩
  simpa using aux Finset.univ

end OrbitAvg

theorem averaged_equal_endpoints {ι H : Type*} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H]
    (a : ι → FiniteEuclidean) (ha : Function.Injective a)
    (z : H → ι → FiniteEuclidean) (σ : ι → H) (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 < δ)
    (hf : ∀ h : H, ∀ i j, ‖z h i - z h j‖ ^ 2 = ‖a i - a j‖ ^ 2)
    (hg : ∀ h : H, ∀ i j, ‖z (h * σ i) i - z (h * σ j) j‖ ^ 2 = q * ‖a i - a j‖ ^ 2) :
    ∃ w lmb μ, Path a w lmb ∧ Path a w μ ∧ 0 < lmb ∧ μ / lmb ≤ q + (Fintype.card ι : ℝ) * δ := by
  classical
  let L := Derived AugKernel (Fintype.card ι - 2)
  have hsc_bd (i : ι) {x : LetterGroup} (hx : x ∈ L) :
      BoundedFrac a (Pi.mulSingle i x) (singleCost a i x) :=
    Nat.sInf_mem (show {c | BoundedFrac a (Pi.mulSingle i x) c}.Nonempty from
      let ⟨u, ⟨m, hm⟩, v, ⟨n, hn⟩, he⟩ :=
        derived_subset_single (unitMonoid a) AugKernel (fun g => ⟨0, .diag g⟩)
          (unit_pair_inverse a) (unit_pair_coverage a ha) i hx
      ⟨m + n, u, v, m, n, hm, hn, he, le_rfl⟩)
  let cost (x : LetterGroup) : ℕ := ∑ i, singleCost a i x
  have hc_one : cost 1 = 0 := Finset.sum_eq_zero fun _ _ =>
    Nat.eq_zero_of_le_zero (Nat.sInf_le (by simpa using BoundedFrac.one a))
  have hc_inv {x} (hx : x ∈ L) : cost x⁻¹ = cost x := by
    have hle {y} (hy : y ∈ L) : cost y⁻¹ ≤ cost y := Finset.sum_le_sum fun i _ =>
      Nat.sInf_le (by rw [Pi.mulSingle_inv]; exact (hsc_bd i hy).inv)
    exact le_antisymm (hle hx) (by simpa using hle (L.inv_mem hx))
  have hc_conj {x} (hx : x ∈ L) (k : LetterGroup) : cost (k * x * k⁻¹) = cost x := by
    have hle {y} (hy : y ∈ L) (k : LetterGroup) : cost (k * y * k⁻¹) ≤ cost y := Finset.sum_le_sum fun i _ =>
      Nat.sInf_le (by
        have := (hsc_bd i hy).conj k
        rwa [show (fun j => k * (Pi.mulSingle i y : ι → LetterGroup) j * k⁻¹) = Pi.mulSingle i (k * y * k⁻¹) by
          ext j; by_cases hj : j = i <;> simp [hj]] at this)
    exact le_antisymm (hle hx k) (by simpa [mul_assoc] using hle ((inferInstance : L.Normal).conj_mem _ hx k) k⁻¹)
  have hc_mul {x y} (hx : x ∈ L) (hy : y ∈ L) : cost (x * y) ≤ cost x + cost y :=
    (Finset.sum_le_sum fun i _ => Nat.sInf_le (by rw [Pi.mulSingle_mul]; exact (hsc_bd i hx).mul_single i (hsc_bd i hy))).trans_eq
      Finset.sum_add_distrib
  have hc_list (l : List LetterGroup) (hl : ∀ x ∈ l, x ∈ L) (M : ℕ) (hM : ∀ x ∈ l, cost x ≤ M) :
      cost l.prod ≤ l.length * M := by
    induction l with
    | nil => simp [hc_one]
    | cons x l ih =>
      have hlp : ∀ y ∈ l, y ∈ L := fun y hy => hl y (by simp [hy])
      exact (hc_mul (hl x (by simp)) (L.list_prod_mem hlp)).trans <| by
        simpa [Nat.add_mul, add_comm] using add_le_add (hM x (by simp)) (ih hlp fun y hy => hM y (by simp [hy]))
  let letter (h : H) (i : ι) : LetterGroup := FreeGroup.of (z h i)
  have hraise (r : ℕ) : ∀ (v : H → ι → LetterGroup) (n : ℕ) (i : ι), OrbitIn AugKernel v i →
      ∃ u k, Evolution v n u k ∧ OrbitIn (Derived AugKernel r) u i := by
    induction r with
    | zero => exact fun v n _ hv => ⟨v, n, .refl _ _, hv⟩
    | succ r ih =>
      intro v n i hv; obtain ⟨u, k, heu, hu⟩ := ih v n i hv
      exact ⟨_, _, (heu.normalize (u 1 i)⁻¹).average, orbitIn_raise (Derived AugKernel r) hu⟩
  obtain ⟨v₀, n₀, hev₀, hv₀⟩ := evolve_finite letter 1 (fun i v _ => OrbitIn L v i)
    (fun he _ hi => he.orbitIn hi)
    (fun he i => hraise _ _ _ i (he.orbitIn fun _ _ => by change FreeGroup.lift _ _ = 1; simp [letter]))
  let OrbitBd (v : H → ι → LetterGroup) (b : ℝ) (i : ι) : Prop :=
    OrbitIn L v i ∧ ∀ g k : H, (cost (v g i * (v k i)⁻¹) : ℝ) ≤ b
  have hbd_evol {v u : H → ι → LetterGroup} {n k : ℕ} (he : Evolution v n u k) {i : ι}
      (hb : OrbitBd v (δ * n) i) : OrbitBd u (δ * k) i := by
    induction he with
    | refl => exact hb
    | normalize _ c ih =>
      exact ⟨(Evolution.normalize (.refl _ 0) c).orbitIn ih.1, fun g h => by simpa [mul_assoc] using ih.2 g h⟩
    | @average v' n' _ ih =>
      refine ⟨orbitIn_avg ih.1, fun g₁ g₂ => ?_⟩
      have hprod (l : List H) :
          (l.map fun g => v' (g * g₁) i).prod * ((l.map fun g => v' (g * g₂) i).prod)⁻¹ ∈ L ∧
          cost ((l.map fun g => v' (g * g₁) i).prod * ((l.map fun g => v' (g * g₂) i).prod)⁻¹) ≤
            (l.map fun g => cost (v' (g * g₁) i * (v' (g * g₂) i)⁻¹)).sum := by
        induction l with
        | nil => simp [hc_one, L.one_mem]
        | cons g l ihl =>
          have hg := ih.1 (g * g₁) (g * g₂)
          let w' := (l.map fun k => v' (k * g₁) i).prod * ((l.map fun k => v' (k * g₂) i).prod)⁻¹
          have hz : v' (g * g₁) i * w' * (v' (g * g₁) i)⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem _ ihl.1 _
          simp only [List.map_cons, List.prod_cons, List.sum_cons]
          rw [show v' (g * g₁) i * (l.map fun k => v' (k * g₁) i).prod *
              (v' (g * g₂) i * (l.map fun k => v' (k * g₂) i).prod)⁻¹ =
            (v' (g * g₁) i * w' * (v' (g * g₁) i)⁻¹) * (v' (g * g₁) i * (v' (g * g₂) i)⁻¹) by dsimp [w']; group]
          exact ⟨L.mul_mem hz hg, (hc_mul hz hg).trans (by rw [hc_conj ihl.1]; omega)⟩
      exact ((Nat.cast_le.mpr (hprod Finset.univ.toList).2).trans_eq (by simp)).trans
        ((Finset.sum_le_sum (s := Finset.univ) fun g _ => ih.2 (g * g₁) (g * g₂)).trans_eq (by simp; ring))
  have hvalid {v : H → ι → LetterGroup} {n : ℕ} (he : Evolution letter 1 v n) :
      0 < n ∧ (∀ k : H, Path a (v k) n) ∧ (∀ k : H, Path a (fun i => v (k * σ i) i) (q * n)) := by
    have lpath (l : List H) {r : ℝ} {p : H → ι → LetterGroup} (hp : ∀ h, Path a (p h) r) :
        Path a (fun i => (l.map fun h => p h i).prod) (l.length * r) := by
      induction l with
      | nil => simpa using Path.diag 1
      | cons h l ih => simpa [add_mul, one_mul, add_comm, Pi.mul_def] using (hp h).mul ih
    induction he with
    | refl => exact ⟨zero_lt_one, fun k => by simpa using Path.copy (z k) (by simpa using hf k),
        fun k => by simpa using Path.copy _ (hg k)⟩
    | normalize _ c ih => exact ⟨ih.1, fun k => by simpa [Pi.mul_def] using (ih.2.1 k).mul (.diag c),
        fun k => by simpa [Pi.mul_def] using (ih.2.2 k).mul (.diag c)⟩
    | @average v' n' _ ih =>
      refine ⟨Nat.mul_pos Fintype.card_pos ih.1, fun k => ?_, fun k => ?_⟩
      · change Path a (fun i => (Finset.univ.toList.map fun h => v' (h * k) i).prod) _
        simpa using lpath Finset.univ.toList fun h => ih.2.1 (h * k)
      · change Path a (fun i => (Finset.univ.toList.map fun h => v' (h * (k * σ i)) i).prod) _
        convert lpath Finset.univ.toList (p := fun h i => v' (h * (k * σ i)) i)
          (fun h => by simpa [mul_assoc] using ih.2.2 (h * k)) using 1
        simp; ring
  obtain ⟨w, m, hew, hw⟩ := evolve_finite v₀ n₀ (fun i w m => OrbitBd w (δ * m) i)
    (fun he _ hi => hbd_evol he hi)
    (fun {u k} he i => by
      have hk : 0 < k := (hvalid (hev₀.trans he)).1
      have huL : OrbitIn L u i := he.orbitIn (hv₀ i)
      let u₀ (h : H) (j : ι) := u h j * (u 1 i)⁻¹
      let B : ℕ := ∑ h, cost (u₀ h i)
      let h1 : ℕ := Fintype.card H - 1
      have hh' : (0 : ℝ) < Fintype.card H := Nat.cast_pos.mpr Fintype.card_pos
      have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      have hB1 : (0 : ℝ) < 2 * B + 1 := by positivity
      obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (div_pos (mul_pos hδ hk') hB1)
        (show (h1 : ℝ) / Fintype.card H < 1 by
          rw [div_lt_one hh', Nat.cast_lt]; exact Nat.sub_lt Fintype.card_pos zero_lt_one)
      rw [div_pow, div_lt_iff₀ (pow_pos hh' _), div_mul_eq_mul_div, lt_div_iff₀ hB1] at ht
      have hrate : ((2 * (B * h1 ^ t) : ℕ) : ℝ) ≤ δ * ((Fintype.card H ^ t * k : ℕ) : ℝ) := by
        push_cast; nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) h1) t]
      have hiter (step : ℕ) : ∃ v, Evolution u₀ k v (Fintype.card H ^ step * k) ∧
          (∀ h, v h i ∈ L) ∧ ∀ h, cost (v h i) ≤ B * h1 ^ step := by
        induction step with
        | zero => exact ⟨u₀, by simpa using Evolution.refl u₀ k, fun h => huL h 1,
            fun h => (Finset.single_le_sum (f := fun g => cost (u₀ g i))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)).trans_eq (Nat.mul_one B).symm⟩
        | succ step ihs =>
          obtain ⟨v, hev, hvm, hvb⟩ := ihs
          have hstep (g : H) : orbitAvg v g i * (v 1 i)⁻¹ ∈ L ∧
              cost (orbitAvg v g i * (v 1 i)⁻¹) ≤ B * h1 ^ (step + 1) := by
            obtain ⟨p, q', heq⟩ := List.mem_iff_append.mp (Finset.mem_toList.mpr (Finset.mem_univ g⁻¹))
            let pa := (p.map fun h => v (h * g) i).prod
            let qa := (q'.map fun h => v (h * g) i).prod
            have hpa : pa ∈ L := L.list_prod_mem (by simpa using fun h _ => hvm (h * g))
            have hqa : qa ∈ L := L.list_prod_mem (by simpa using fun h _ => hvm (h * g))
            have hconj : v 1 i * qa * (v 1 i)⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem _ hqa _
            rw [show orbitAvg v g i * (v 1 i)⁻¹ = pa * (v 1 i * qa * (v 1 i)⁻¹) by
              simp [orbitAvg, heq, pa, qa, List.prod_append, mul_assoc]]
            refine ⟨L.mul_mem hpa hconj, ?_⟩
            have hcpa := hc_list (p.map fun h => v (h * g) i) (by simpa using fun h _ => hvm _) _ (by simpa using fun h _ => hvb _)
            have hcqa := hc_list (q'.map fun h => v (h * g) i) (by simpa using fun h _ => hvm _) _ (by simpa using fun h _ => hvb _)
            have hlen : p.length + q'.length = h1 := by
              have := congrArg List.length heq; simp [List.length_append] at this; dsimp [h1]; omega
            refine (hc_mul hpa hconj).trans ?_
            rw [hc_conj hqa]
            calc cost pa + cost qa ≤ p.length * _ + q'.length * _ := by simpa using add_le_add hcpa hcqa
              _ = (p.length + q'.length) * _ := (Nat.add_mul _ _ _).symm
              _ = B * h1 ^ (step + 1) := by rw [hlen, pow_succ]; ring
          refine ⟨fun g j => orbitAvg v g j * (v 1 i)⁻¹, ?_, fun g => (hstep g).1, fun g => (hstep g).2⟩
          convert hev.average.normalize (v 1 i)⁻¹ using 1; ring
      obtain ⟨v, hev, hvm, hvb⟩ := hiter t
      refine ⟨v, _, (Evolution.normalize (.refl u k) (u 1 i)⁻¹).trans hev,
        fun g₁ g₂ => L.mul_mem (hvm g₁) (L.inv_mem (hvm g₂)), fun g₁ g₂ => ?_⟩
      have hnat : cost (v g₁ i * (v g₂ i)⁻¹) ≤ 2 * (B * h1 ^ t) := by
        have := hc_mul (hvm g₁) (L.inv_mem (hvm g₂))
        rw [hc_inv (hvm g₂)] at this
        have h1' := hvb g₁; have h2' := hvb g₂; omega
      exact (Nat.cast_le.mpr hnat).trans hrate)
  obtain ⟨hm, hwf, hwg⟩ := hvalid (hev₀.trans hew)
  let Dp := w 1
  let Dm : ι → LetterGroup := fun i => w (σ i) i
  let r : ι → LetterGroup := Dp⁻¹ * Dm
  have hrc (i : ι) : r i ∈ L ∧ (cost (r i) : ℝ) ≤ δ * m := by
    have hmem := (hw i).1 1 (σ i); have hcs := (hw i).2 1 (σ i)
    rw [show r i = (w 1 i)⁻¹ * (w 1 i * (w (σ i) i)⁻¹)⁻¹ * ((w 1 i)⁻¹)⁻¹ by dsimp [r, Dp, Dm]; group]
    exact ⟨(inferInstance : L.Normal).conj_mem _ (L.inv_mem hmem) _,
      by rw [hc_conj (L.inv_mem hmem), hc_inv hmem]; exact hcs⟩
  have htuple (l : List ι) : BoundedFrac a ((l.map fun i => Pi.mulSingle i (r i)).prod)
      ((l.map fun i => singleCost a i (r i)).sum) := by
    induction l with
    | nil => simpa using BoundedFrac.one a
    | cons i l ihl =>
      have ht := ihl.mul_single i (hsc_bd i (hrc i).1)
      have hcomm : Commute (Pi.mulSingle i (r i)) ((l.map fun j => Pi.mulSingle j (r j)).prod) :=
        Commute.list_prod_right _ _ fun y hy => by
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
          by_cases hji : j = i
          · subst j; rfl
          · ext k; by_cases hki : k = i
            · subst k; simp [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
            · simp [Pi.mulSingle_eq_of_ne hki]
      simpa [hcomm.symm.eq, Nat.add_comm] using ht
  have hprod_eq : (Finset.univ.toList.map fun i => Pi.mulSingle i (r i)).prod = r := by
    have aux (l : List ι) (hl : l.Nodup) (i : ι) :
        ((l.map fun j => Pi.mulSingle j (r j)).prod) i = if i ∈ l then r i else 1 := by
      induction l with
      | nil => simp
      | cons j l ih =>
        obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
        rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl]
        by_cases h : i = j <;> [subst j; skip] <;> simp [*]
    ext i; simpa using aux Finset.univ.toList (Finset.nodup_toList _) i
  have hb := htuple Finset.univ.toList
  rw [hprod_eq, show (Finset.univ.toList.map fun i => singleCost a i (r i)).sum = ∑ i, singleCost a i (r i) by simp] at hb
  obtain ⟨u, v, b, e, hu, hv, he, hbe⟩ := hb
  have heq : Dp * u = Dm * v := by simpa [r, mul_assoc] using (congrArg (fun t => Dp * t * v) he).symm
  have hp1 : Path a (Dp * u) (m + b) := (hwf 1).mul hu.path
  have hp2 : Path a (Dp * u) (q * m + e) := heq ▸ (by simpa [Dm] using hwg 1 : Path a Dm (q * m)).mul hv.path
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hb' : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have he' : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  refine ⟨_, _, _, hp1, hp2, by positivity, (div_le_iff₀ (by positivity)).mpr ?_⟩
  have hc_sum : (b : ℝ) + e ≤ (Fintype.card ι : ℝ) * (δ * m) := by
    refine (show (b : ℝ) + e ≤ ∑ i, (singleCost a i (r i) : ℝ) by exact_mod_cast hbe).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => δ * m) fun i _ => ?_).trans (by simp)
    exact (Nat.cast_le.mpr (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).trans (hrc i).2
  have : 0 ≤ (Fintype.card ι : ℝ) * δ := by positivity
  nlinarith

section Ultrafilters
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

@[simp] lemma pure_mul_ultra {M : Type*} [Monoid M] (x : M) (V : Ultrafilter M) :
    (pure x : Ultrafilter M) * V = V.map (x * ·) :=
  Ultrafilter.coe_inj.mp (Filter.ext' fun _ => by simp [Ultrafilter.eventually_mul])

@[simp] lemma mul_pure_ultra {M : Type*} [Monoid M] (U : Ultrafilter M) (y : M) :
    U * (pure y : Ultrafilter M) = U.map (· * y) :=
  Ultrafilter.coe_inj.mp (Filter.ext' fun _ => by simp [Ultrafilter.eventually_mul])

@[instance_reducible] def ultrafilterMonoid {M : Type*} [Monoid M] : Monoid (Ultrafilter M) where
  toSemigroup := Ultrafilter.semigroup
  one := pure 1
  one_mul U := (pure_mul_ultra 1 U).trans (by simp)
  mul_one U := (mul_pure_ultra U 1).trans (by simp)

inductive Col (ι : Type*)
  | common (U : Ultrafilter Strings)
  | copy (u : ℝ) (b : ι → FiniteEuclidean)

def Col.weight {ι : Type*} : Col ι → ℝ
  | .common _ => 0
  | .copy u _ => u

def Col.value {ι : Type*} : Col ι → ι → Ultrafilter Strings
  | .common U, _ => U
  | .copy _ b, i => pure (FreeMonoid.of (b i))

def Col.Realizes {ι : Type*} : Col ι → (ι → Strings) → Prop
  | .common _, x => ∃ y, ∀ i, x i = y
  | .copy _ b, x => x = fun i => FreeMonoid.of (b i)

def Col.Valid {ι : Type*} (a : ι → FiniteEuclidean) : Col ι → Prop
  | .common _ => True
  | .copy u b => ∀ i j, ‖b i - b j‖ ^ 2 = u * ‖a i - a j‖ ^ 2

lemma cols_realize {ι : Type*} {a : ι → FiniteEuclidean} {qs : List (Col ι)}
    (hq : ∀ c ∈ qs, c.Valid a) {xs : List (ι → Strings)} (hx : List.Forall₂ Col.Realizes qs xs) :
    (∀ i j, (((xs.map fun x => x i).prod : Strings)).toList.length = (((xs.map fun x => x j).prod : Strings)).toList.length) ∧
    ∀ i j, ‖FiniteEuclidean.flatten (((xs.map fun x => x i).prod : Strings)).toList -
      FiniteEuclidean.flatten (((xs.map fun x => x j).prod : Strings)).toList‖ ^ 2 =
      (qs.map Col.weight).sum * ‖a i - a j‖ ^ 2 := by
  induction hx with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => by simp [FiniteEuclidean.flatten]⟩
  | @cons c x qs xs hcx hxs ih =>
    obtain ⟨hlen, hen⟩ := ih fun d hd => hq d (List.mem_cons_of_mem _ hd)
    have hc := hq c List.mem_cons_self
    have hstep : (∀ i j, (x i).toList.length = (x j).toList.length) ∧
        ∀ i j, ‖FiniteEuclidean.flatten (x i).toList - FiniteEuclidean.flatten (x j).toList‖ ^ 2 =
          c.weight * ‖a i - a j‖ ^ 2 := by
      cases c with
      | common _ => obtain ⟨y, hy⟩ := hcx; exact ⟨fun _ _ => by simp [hy], fun _ _ => by simp [hy, Col.weight]⟩
      | copy u b =>
        subst hcx
        exact ⟨fun _ _ => rfl, fun i j => by simpa [FiniteEuclidean.flatten, ← map_sub, Col.weight] using hc i j⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp only [List.map_cons, List.prod_cons, FreeMonoid.toList_mul, List.length_append, hstep.1 i j, hlen i j]
    · simp only [List.map_cons, List.prod_cons, FreeMonoid.toList_mul, List.sum_cons]
      rw [FiniteEuclidean.flatten_append _ _ _ _ (hstep.1 i j), hstep.2, hen, add_mul]

lemma Path.expand {ι : Type*} {a : ι → FiniteEuclidean} {w u} (h : Path a w u)
    (Ψ : LetterGroup →ₙ* Ultrafilter Strings) (p : Ultrafilter Strings)
    (hgen : ∀ z, Ψ (FreeGroup.of z) = letI := ultrafilterMonoid (M := Strings); p * pure (FreeMonoid.of z) * p) :
    ∃ qs : List (Col ι), (∀ c ∈ qs, c.Valid a) ∧ (qs.map Col.weight).sum = u ∧
      (letI := ultrafilterMonoid (M := Strings); ∀ i, (qs.map fun c => c.value i).prod = Ψ (w i)) := by
  let _ := ultrafilterMonoid (M := Strings)
  induction h with
  | diag g => exact ⟨[.common (Ψ g)], by simp [Col.Valid], by simp [Col.weight], fun _ => by simp [Col.value]⟩
  | @copy u b hb =>
    refine ⟨[.common p, .copy u b, .common p], by simp [Col.Valid, hb], by simp [Col.weight], fun i => ?_⟩
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Col.value, mul_one, hgen, mul_assoc]
  | mul _ _ ihu ihv =>
    obtain ⟨qs, hq, hsu, hpe⟩ := ihu; obtain ⟨rs, hr, hsv, hre⟩ := ihv
    exact ⟨qs ++ rs, fun c hc => (List.mem_append.mp hc).elim (hq c) (hr c), by simp [hsu, hsv],
      fun i => by simp only [List.map_append, List.prod_append, hpe, hre, Pi.mul_apply, (Ψ.map_mul _ _).symm]⟩

lemma Path.scale {ι : Type*} {a : ι → FiniteEuclidean} {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => FreeGroup.map (Real.sqrt c • ·) (w i)) (c * lmb) := by
  induction h with
  | diag _ => simpa using Path.diag _
  | copy b hb =>
    simpa [FreeGroup.map.of] using Path.copy (fun i => Real.sqrt c • b i) fun i j => by
      rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hc, hb]; ring
  | mul _ _ ih1 ih2 => simpa [Pi.mul_def, mul_add] using ih1.mul ih2

lemma synchronize_paths {ι : Type*} {a : ι → FiniteEuclidean} (n : ℕ) (hn : 1 ≤ n)
    {w : ι → LetterGroup} {lmb μ : ℝ} (hp : Path a w lmb) (hm : Path a w μ)
    (hlmb : 0 < lmb) (hratio : μ / lmb < 1 / (n : ℝ)) :
    ∃ W, ∀ t : ℕ, 1 ≤ t → t ≤ n → Path a W (1 / (t : ℝ)) := by
  let ρ := μ / lmb
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hρ : ρ < 1 := hratio.trans_le ((div_le_one hn').mpr (by exact_mod_cast hn))
  let w₀ : ι → LetterGroup := fun i => FreeGroup.map (Real.sqrt lmb⁻¹ • ·) (w i)
  have hp0 : Path a w₀ 1 := by
    have := hp.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le); rwa [inv_mul_cancel₀ hlmb.ne'] at this
  have hm0 : Path a w₀ ρ := by
    have := hm.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le); rwa [show lmb⁻¹ * μ = ρ by dsimp [ρ]; ring] at this
  let v (j : ℕ) : ℝ := if j < n then 1 / (j + 1 : ℕ) else ρ
  have hv (j : ℕ) (hj : j < n) : v (j + 1) ≤ v j := by
    dsimp [v]; rw [ite_eq_left hj]; split_ifs with hj'
    · exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.le_succ _)
    · rw [show j + 1 = n by omega]; exact hratio.le
  let c (j : ℕ) := (v j - v (j + 1)) / (1 - ρ)
  let ww (j : ℕ) : ι → LetterGroup := fun i => FreeGroup.map (Real.sqrt (c j) • ·) (w₀ i)
  refine ⟨((List.range n).map ww).prod, fun t ht htn => ?_⟩
  let k := t - 1
  have hk : k ≤ n := by omega
  let u (j : ℕ) := if j < k then c j * ρ else c j
  have hprod (l : List ℕ) (hl : ∀ j ∈ l, Path a (ww j) (u j)) : Path a (l.map ww).prod (l.map u).sum := by
    induction l with
    | nil => simpa [Pi.one_def] using Path.diag 1
    | cons j l ihl => simpa using (hl j (by simp)).mul (ihl fun m hm => hl m (by simp [hm]))
  have hp' := hprod (List.range n) fun j hj => by
    have hcj : 0 ≤ c j := div_nonneg (sub_nonneg.mpr (hv j (List.mem_range.mp hj))) (by linarith)
    dsimp [u]; split_ifs <;> [exact hm0.scale (c j) hcj; simpa using hp0.scale (c j) hcj]
  have hsum : ((List.range n).map u).sum = 1 / (t : ℝ) := by
    rw [(List.sum_toFinset u List.nodup_range).symm, show (List.range n).toFinset = Finset.range n by ext; simp,
      ← Finset.sum_range_add_sum_Ico u hk]
    have hleft : ∑ j ∈ Finset.range k, u j = (v 0 - v k) / (1 - ρ) * ρ := by
      rw [← Finset.sum_range_sub' v k, Finset.sum_div, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j hj => by simp [u, c, Finset.mem_range.mp hj]
    have hright : ∑ j ∈ Finset.Ico k n, u j = (v k - v n) / (1 - ρ) := by
      refine (Finset.sum_congr rfl (g := fun j => (v j - v (j + 1)) / (1 - ρ))
        fun j hj => by simp [u, c, not_lt.mpr (Finset.mem_Ico.mp hj).1]).trans ?_
      rw [← Finset.sum_div, Finset.sum_Ico_eq_sub _ hk, Finset.sum_range_sub', Finset.sum_range_sub']; ring
    have hvk : v k = 1 / (t : ℝ) := by
      dsimp [v, k]; rw [ite_eq_left (by omega), show ((t - 1 + 1 : ℕ) : ℝ) = t by exact_mod_cast (by omega : t - 1 + 1 = t)]
    rw [hleft, hright, show v 0 = 1 by simp [v, show 0 < n by omega], show v n = ρ by simp [v], hvk]
    field_simp [show 1 - ρ ≠ 0 by linarith]; ring
  exact hsum ▸ hp'

lemma exists_corner_map : ∃ (p : Ultrafilter Strings) (Ψ : LetterGroup →ₙ* Ultrafilter Strings),
    ∀ z, Ψ (FreeGroup.of z) = (letI := ultrafilterMonoid (M := Strings); p * pure (FreeMonoid.of z) * p) := by
  let _ := ultrafilterMonoid (M := Strings)
  let S := Ultrafilter Strings
  have hc : ∀ y : S, Continuous (· * y) := Ultrafilter.continuous_mul_left
  let ideals : Set (Set S) := {N | IsClosed N ∧ N.Nonempty ∧ ∀ x y, y ∈ N → x * y ∈ N}
  obtain ⟨N, hN⟩ : ∃ N, Minimal (· ∈ ideals) N := by
    refine zorn_superset _ fun c hcs hchain => ⟨⋂₀ c, ⟨isClosed_sInter fun N hN => (hcs hN).1, ?_,
      fun x y hy => mem_sInter.mpr fun N hN => (hcs hN).2.2 x y (mem_sInter.mp hy N hN)⟩,
      fun N hN => sInter_subset_of_mem hN⟩
    obtain rfl | hcn := c.eq_empty_or_nonempty
    · simp
    · rw [sInter_eq_iInter]; have := hcn.coe_sort
      exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
        (DirectedOn.directed_val (IsChain.directedOn hchain.symm))
        (fun M => (hcs M.2).2.1) (fun M => (hcs M.2).1.isCompact) (fun M => (hcs M.2).1)
  obtain ⟨p, hpN, hp⟩ := exists_idempotent_in_compact_subsemigroup hc N
    hN.prop.2.1 hN.prop.1.isCompact fun x _ y hy => hN.prop.2.2 x y hy
  have hi (y : S) (hpy : p * y = y) (hyp : y * p = y) : ∃ v : S, p * v = v ∧ v * p = v ∧ v * y = p := by
    have hpr : range (· * y) = N := hN.eq_of_subset
      ⟨(isCompact_range (hc y)).isClosed, ⟨y * y, y, rfl⟩, by rintro a _ ⟨b, rfl⟩; exact ⟨a * b, mul_assoc a b y⟩⟩
      (by rintro _ ⟨a, rfl⟩; exact hN.prop.2.2 a y (hyp ▸ hN.prop.2.2 y p hpN))
    obtain ⟨v, hv : v * y = p⟩ := hpr.symm ▸ hpN
    exact ⟨p * v * p, by simp [← mul_assoc, hp], by simp [mul_assoc, hp],
      by rw [mul_assoc, mul_assoc p, hpy, ← mul_assoc p, mul_assoc p, hv, hp]⟩
  let Corner := {x : S // p * x = x ∧ x * p = x}
  let _ : Mul Corner := ⟨fun x y => ⟨x.1 * y.1, by rw [← mul_assoc, x.2.1], by rw [mul_assoc, y.2.2]⟩⟩
  let _ : One Corner := ⟨⟨p, hp, hp⟩⟩
  let _ : Inv Corner := ⟨fun y => ⟨(hi y.1 y.2.1 y.2.2).choose,
    (hi y.1 y.2.1 y.2.2).choose_spec.1, (hi y.1 y.2.1 y.2.2).choose_spec.2.1⟩⟩
  let _ : Group Corner := Group.ofLeftAxioms (fun _ _ _ => Subtype.ext (mul_assoc _ _ _))
    (fun x => Subtype.ext x.2.1) (fun x => Subtype.ext (hi x.1 x.2.1 x.2.2).choose_spec.2.2)
  let ψ : LetterGroup →* Corner := FreeGroup.lift fun z =>
    ⟨p * pure (FreeMonoid.of z) * p, by simp [← mul_assoc, hp], by simp [mul_assoc, hp]⟩
  exact ⟨p, { toFun := fun x => (ψ x).1, map_mul' := fun x y => by rw [ψ.map_mul]; rfl },
    fun z => congrArg Subtype.val (FreeGroup.lift_apply_of (x := z))⟩

lemma exists_ultra_color {M κ : Type*} [Finite κ] (U : Ultrafilter M) (c : M → κ) :
    ∃ k, {x | c x = k} ∈ U :=
  Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall fun x => ⟨c x, rfl⟩)

def ultraColor {M κ : Type*} [Finite κ] (c : M → κ) (U : Ultrafilter M) : κ :=
  (exists_ultra_color U c).choose

lemma ultraColor_spec {M κ : Type*} [Finite κ] (c : M → κ) (U : Ultrafilter M) :
    {x | c x = ultraColor c U} ∈ U :=
  (exists_ultra_color U c).choose_spec

theorem paths_monochromatic {s : ℕ} (a : Fin s → FiniteEuclidean)
    (hpaths : ∀ n : ℕ, 1 ≤ n → ∃ w lmb μ, Path a w lmb ∧ Path a w μ ∧ 0 < lmb ∧ μ / lmb < 1 / (n : ℝ))
    {κ : Type*} [Finite κ] (c : FiniteEuclidean → κ) :
    ∃ b : Fin s → FiniteEuclidean, (∀ i j, ‖b i - b j‖ = ‖a i - a j‖) ∧ ∃ k : κ, ∀ i, c (b i) = k := by
  classical
  let _ := ultrafilterMonoid (M := Strings)
  obtain ⟨β, hβ, hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) κ
  let _ := hβ
  obtain ⟨w, lmb, μ, hp, hm, hlmb, hratio⟩ := hpaths (Fintype.card β + 1) (by omega)
  obtain ⟨W, hW⟩ := synchronize_paths (Fintype.card β + 1) (by omega) hp hm hlmb hratio
  obtain ⟨p, Ψ, hgen⟩ := exists_corner_map
  let coloring : Strings → κ := fun x => c (FiniteEuclidean.flatten x.toList)
  let L : List β := Finset.univ.toList
  let C : (β → Fin s) → κ := fun x => ultraColor coloring ((L.map fun j => Ψ (W (x j))).prod)
  obtain ⟨line, k, hline⟩ := hHJ C
  let S : Finset β := Finset.univ.filter fun j => line.idxFun j = none
  let t := S.card
  have ht : 1 ≤ t := Finset.card_pos.mpr <| let ⟨j, hj⟩ := line.proper; ⟨j, by simp [S, hj]⟩
  obtain ⟨qs, hqs, hws, hqe⟩ := (hW t ht ((Finset.card_le_univ S).trans (Nat.le_succ _))).expand Ψ p hgen
  let q (j : β) : List (Col (Fin s)) := (line.idxFun j).elim qs fun i => [.common (Ψ (W i))]
  have hval : ∀ col ∈ (L.map q).flatten, col.Valid a := by
    simp only [List.mem_flatten, List.mem_map]
    rintro col ⟨_, ⟨j, _, rfl⟩, hcol⟩
    cases he : line.idxFun j with
    | none => exact hqs col (by simpa [q, he] using hcol)
    | some v => exact (by simpa [q, he] using hcol : col = .common (Ψ (W v))) ▸ trivial
  have hprod_eq (ls : List β) (i : Fin s) :
      ((ls.map q).flatten.map fun c => c.value i).prod = (ls.map fun j => Ψ (W (line i j))).prod := by
    induction ls with
    | nil => rfl
    | cons j ls ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append, List.prod_append, List.prod_cons, ih]
      congr 1
      cases he : line.idxFun j <;> [simpa [q, he, Combinatorics.Line.coe_apply] using hqe i;
        simp [q, he, Combinatorics.Line.coe_apply, Col.value]]
  have hweight : ((L.map q).flatten.map Col.weight).sum = 1 := by
    rw [List.map_flatten, List.sum_flatten, List.map_map]
    have h1 : (L.map ((List.sum ∘ List.map Col.weight) ∘ q)).sum = ∑ j, ((q j).map Col.weight).sum := by simp [L]
    rw [show List.map (List.sum ∘ List.map Col.weight) (L.map q) = L.map ((List.sum ∘ List.map Col.weight) ∘ q)
      from List.map_map, h1]
    have h2 (j : β) : ((q j).map Col.weight).sum = if line.idxFun j = none then 1 / (t : ℝ) else 0 := by
      cases he : line.idxFun j <;> simp [q, he, hws, Col.weight]
    simp_rw [h2, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    change (t : ℝ) * (1 / (t : ℝ)) = 1
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (by omega))
  have hrealize (cols : List (Col (Fin s))) (B : Fin s → Set Strings)
      (hB : ∀ i, B i ∈ ((cols.map fun c => c.value i).prod : Ultrafilter Strings)) :
      ∃ xs : List (Fin s → Strings), List.Forall₂ Col.Realizes cols xs ∧
        ∀ i, (xs.map fun x => x i).prod ∈ B i := by
    induction cols generalizing B with
    | nil =>
      refine ⟨[], .nil, fun i => ?_⟩
      have hi : B i ∈ (pure 1 : Ultrafilter Strings) := hB i
      simpa using hi
    | cons col cols ih =>
      have hh (i : Fin s) : ∀ᶠ x in (col.value i : Filter Strings),
          {y | x * y ∈ B i} ∈ ((cols.map fun c => c.value i).prod : Ultrafilter Strings) :=
        (Ultrafilter.eventually_mul _ _ _).mp (hB i)
      obtain ⟨x, hx, hxB⟩ : ∃ x : Fin s → Strings, col.Realizes x ∧ ∀ i,
          {y | x i * y ∈ B i} ∈ ((cols.map fun c => c.value i).prod : Ultrafilter Strings) := by
        cases col with
        | common U =>
          dsimp [Col.value] at hh
          obtain ⟨x, hx⟩ := (eventually_all.mpr hh).exists
          exact ⟨fun _ => x, ⟨x, fun _ => rfl⟩, hx⟩
        | copy _ b => exact ⟨fun i => FreeMonoid.of (b i), rfl, fun i => by simpa [Col.value] using hh i⟩
      obtain ⟨xs, hxs, hsB⟩ := ih (fun i => {y | x i * y ∈ B i}) hxB
      exact ⟨x :: xs, .cons hx hxs, fun i => by simpa using hsB i⟩
  obtain ⟨xs, hxs, hxB⟩ := hrealize (L.map q).flatten (fun _ => {x | coloring x = k}) fun i => by
    rw [hprod_eq L i]; have hk : {x | coloring x = C (line i)} ∈ _ := ultraColor_spec coloring _; rwa [hline i] at hk
  have hfam := cols_realize hval hxs
  rw [hweight] at hfam
  refine ⟨fun i => FiniteEuclidean.flatten ((xs.map fun x => x i).prod : Strings).toList,
    fun i j => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_, k, hxB⟩
  rw [hfam.2, one_mul]

end Ultrafilters

theorem realCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hreal : RealCriterion a) : Ramsey a := by
  classical
  let aE : Fin s → FiniteEuclidean := fun i => FiniteEuclidean.embed d (a i)
  have hpaths : ∀ n : ℕ, 1 ≤ n → ∃ w lmb μ,
      Path aE w lmb ∧ Path aE w μ ∧ 0 < lmb ∧ μ / lmb < 1 / (n : ℝ) := fun n hn => by
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    let η : ℝ := 1 / (4 * n)
    let δ : ℝ := 1 / (4 * n * s)
    obtain ⟨ℓ, f, g, hf, hg, hperm⟩ := realCriterion_two_scale a hd (by omega) hreal η (by positivity)
    choose σ hσ using hperm
    let perm (τ : Equiv.Perm (Fin ℓ)) : Space ℓ ≃ₗᵢ[ℝ] Space ℓ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ τ
    let z (h : Equiv.Perm (Fin ℓ)) (i : Fin s) : FiniteEuclidean := FiniteEuclidean.embed ℓ (perm h (f i))
    have hσ' (i : Fin s) : perm (σ i) (f i) = g i := by ext j; simpa [perm] using (hσ i ((σ i).symm j)).symm
    obtain ⟨w, lmb, μ, hp, hm, hlmb, hr⟩ := averaged_equal_endpoints aE
      ((FiniteEuclidean.embed d).injective.comp ha) z σ (η / (1 + η)) δ (by positivity) (by positivity)
      (fun h i j => by simp [z, aE, ← map_sub, hf i j])
      (fun h i j => by
        have hc (k : Fin s) : z (h * σ k) k = FiniteEuclidean.embed ℓ (perm h (g k)) := by
          change FiniteEuclidean.embed ℓ (perm h (perm (σ k) (f k))) = _; rw [hσ']
        rw [hc i, hc j]; simp [aE, ← map_sub, hg i j])
    rw [Fintype.card_fin] at hr
    refine ⟨w, lmb, μ, hp, hm, hlmb, hr.trans_lt ?_⟩
    have hη : 0 < η := by positivity
    have hq' : η / (1 + η) < η := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
    have hs' : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have he : η + s * δ = 1 / (2 * n) := by dsimp [η, δ]; field_simp; ring
    have hhalf : (1 : ℝ) / (2 * n) < 1 / n := one_div_lt_one_div_of_lt hn' (by linarith)
    linarith
  intro r _
  by_contra! hbad
  choose c hc using fun n => hbad (n + 1) (by omega)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  let C : FiniteEuclidean → Fin r := fun z => ultraColor (fun n => c n (FiniteEuclidean.truncate (n + 1) z)) U
  obtain ⟨b, hb, k, hbk⟩ := paths_monochromatic aE hpaths C
  have hcol : ∀ᶠ n in (U : Filter ℕ), ∀ i, c n (FiniteEuclidean.truncate (n + 1) (b i)) = k :=
    eventually_all.mpr fun i => by
      have hh : ∀ᶠ n in (U : Filter ℕ), c n (FiniteEuclidean.truncate (n + 1) (b i)) = C (b i) :=
        ultraColor_spec (fun n => c n (FiniteEuclidean.truncate (n + 1) (b i))) U
      rwa [hbk i] at hh
  have he : ∀ᶠ n in (U : Filter ℕ), ∀ i, FiniteEuclidean.embed (n + 1) (FiniteEuclidean.truncate (n + 1) (b i)) = b i :=
    eventually_all.mpr fun i => Ultrafilter.of_le atTop (FiniteEuclidean.eventually_embed_truncate (b i))
  obtain ⟨n, hn, hcn⟩ := (he.and hcol).exists
  obtain ⟨i, hi⟩ := hc n (fun i => FiniteEuclidean.truncate (n + 1) (b i))
    (fun i j => by rw [dist_eq_norm, dist_eq_norm, ← (FiniteEuclidean.embed (n + 1)).norm_map,
      map_sub, hn i, hn j, hb, ← map_sub, LinearIsometry.norm_map]) k
  exact hi (hcn i)

end EuclideanRamsey
end
end OAI
