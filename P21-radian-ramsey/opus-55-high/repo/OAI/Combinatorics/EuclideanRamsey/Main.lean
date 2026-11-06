/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Main.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathFractions

public section

noncomputable section
set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
notation "𝔨" => ‖a i - a j‖ ^ 2
notation "𝔧" => flatten (x i).toList
notation "𝔦" => (hcs hN)
notation "𝔥" => (hx i j)
local notation "𝔤" => (k + 2)
local notation "𝔢" => (by omega)
notation "𝔡" => (by positivity)
local notation "𝔠" => (.of z)
local notation "𝔟" => (l - 𝔤 * m)
local notation "𝔞" => (f i)
open GradedPaths

abbrev LetterGroup := FreeGroup FiniteEuclidean
variable {ι : Type*} (a : ι → FiniteEuclidean)

def CopyPath (u : ℝ) (b : ι → FiniteEuclidean) : Prop :=
  0 ≤ u ∧ ∀ i j, ‖b i - b j‖ ^ 2 = u * 𝔨

inductive Path (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℝ → Prop
  | diag g : Path a (fun _ => g) 0
  | copy {u} b : CopyPath a u b → Path a (fun i => .of (b i)) u
  | mul {u v l m} : Path a u l → Path a v m → Path a (u * v) (l + m)

def paths : GradedPaths ι LetterGroup := ⟨Path a, .diag, .mul⟩

variable {a}

lemma Path.nonneg (h : Path a w u) : 0 ≤ u := by
  induction h with
  | diag => rfl
  | copy _ h => exact h.1
  | mul _ _ h h' => exact add_nonneg h h'


lemma extend_pair (b : ι → FiniteEuclidean) i j z z' (h : ‖z' - z‖ = ‖b j - b i‖) :
    ∃ c : ι → FiniteEuclidean, c i = z ∧ c j = z' ∧ ∀ k l, ‖c k - c l‖ = ‖b k - b l‖ :=
  ⟨fun k => z + (ℝ ∙ (b j - b i - (z' - z)))ᗮ.reflection (b k - b i), by simp,
    by simp [Submodule.reflection_sub h.symm], by simp [← map_sub]⟩

lemma pair_inverse : (paths a).PairInverse := by
  intro i j _ v m hv
  induction hv with
  | diag g => exact ⟨_, 0, .diag g⁻¹, rfl, rfl⟩
  | copy b hb =>
    obtain ⟨c, hci, hcj, hc⟩ := extend_pair b i j (b j) (b i) (norm_sub_rev _ _)
    exact ⟨(fun _ => (FreeGroup.of (b i))⁻¹) * (fun k => FreeGroup.of (c k)) * fun _ => (FreeGroup.of (b j))⁻¹, _,
      ((Path.diag _).mul (.copy c ⟨hb.1, fun k l => by rw [hc]; exact hb.2 k l⟩)).mul (.diag _), by simp_all, by simp_all⟩
  | mul _ _ ihu ihv =>
    obtain ⟨u', m', hu', hui, huj⟩ := ihu
    obtain ⟨v', n', hv', hvi, hvj⟩ := ihv
    exact ⟨v' * u', n' + m', hv'.mul hu', by simp_all, by simp_all⟩

abbrev AugKernel : Subgroup LetterGroup := .normalClosure {g | ∃ x y, g = .of x * (FreeGroup.of y)⁻¹}

lemma pair_coverage (ha : a.Injective) : (paths a).PairCoverage AugKernel := by
  intro i j hij g hg h hh
  let S : Subgroup (LetterGroup × LetterGroup) :=
    { carrier := {p | ∃ u m, Path a u m ∧ (u i, u j) = p}
      one_mem' := ⟨_, 0, .diag 1, rfl⟩
      mul_mem' := fun ⟨u, m, hu, e⟩ ⟨v, n, hv, e'⟩ => ⟨u * v, m + n, hu.mul hv, by aesop⟩
      inv_mem' := fun ⟨u, m, hu, e⟩ => let ⟨b, n, hb, h1, h2⟩ := pair_inverse i j hij u m hu
                                       ⟨b, n, hb, by aesop⟩ }
  have hd (g) : (g, g) ∈ S := ⟨_, 0, .diag g, rfl⟩
  let K := S.comap (MonoidHom.inl _ _)
  have : K.Normal := ⟨fun g hg k => Subgroup.mem_comap.2 <| by simpa using S.mul_mem (S.mul_mem (hd k) hg) (hd k⁻¹)⟩
  have hK : AugKernel ≤ K := Subgroup.normalClosure_le_normal fun _ ⟨x, y, e⟩ => by
    rw [e, SetLike.mem_coe, ← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
    refine FiniteEuclidean.unit_distance_constant _ (norm_pos_iff.2 (sub_ne_zero.2 (ha.ne hij))) (fun z => (FreeGroup.of z : LetterGroup ⧸ K)) (fun x y hxy => QuotientGroup.eq_iff_div_mem.2 ?_) x y
    obtain ⟨c, hci, hcj, hc⟩ := extend_pair a i j x y (by rw [norm_sub_rev, hxy, norm_sub_rev])
    refine Subgroup.mem_comap.2 ?_
    convert S.mul_mem ⟨_, 1, .copy c ⟨zero_le_one, fun k l => by grind⟩, by rw [hci, hcj]⟩ (hd (FreeGroup.of y)⁻¹)
    simp [div_eq_mul_inv]
  obtain ⟨u, m, hu, e⟩ := S.mul_mem (hK (AugKernel.mul_mem hg (AugKernel.inv_mem hh))) (hd h)
  exact ⟨u, m, hu, by simp_all, by simp_all⟩


lemma Path.prod (l : List α) (w : α → ι → LetterGroup) u (h : ∀ j ∈ l, Path a (w j) (u j)) :
    Path a (fun i => (l.map fun j => w j i).prod) (l.map u).sum := by
  induction l with
  | nil => exact .diag 1
  | cons j l ih => exact (h j (by simp)).mul (ih fun k hk => h k (by grind))

def dil (c : ℝ) : LetterGroup →* LetterGroup := FreeGroup.map (√c • ·)

lemma Path.scale (h : Path a w u) c (hc : 0 ≤ c) : Path a (fun i => dil c (w i)) (c * u) := by
  induction h with
  | diag g => simpa using Path.diag (dil c g)
  | copy b hb => simpa [dil] using Path.copy (fun i => √c • b i) ⟨mul_nonneg hc hb.1, fun i j => by
      rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hc, hb.2]
      ring⟩
  | mul _ _ hu hv => simpa [Pi.mul_def, mul_add] using hu.mul hv

lemma sync (hl : Path a w l) (hm : Path a w m) (hl0 : 0 < l) (k : ℕ) (hk : 𝔤 * m ≤ l) :
    ∃ V c, 0 < c ∧ Path a V (c * m) ∧ ∀ t ≤ k, Path a V (c * l / (t + 1)) := by
  induction k with
  | zero => exact ⟨w, 1, one_pos, by grind, fun t ht => by simp_all⟩
  | succ k ih =>
    have := hm.nonneg
    push_cast at hk
    obtain ⟨V, c, hc, hVm, hV⟩ := ih (by linarith)
    have hβ : 0 ≤ (k + 1) * 𝔟 := mul_nonneg 𝔡 (by linarith)
    refine ⟨fun i => dil l (V i) * dil ((k + 1) * 𝔟) (V i), c * (l + (k + 1) * 𝔟), by positivity,
      by convert (hVm.scale _ hl0.le).mul (hVm.scale _ hβ)
         ring, fun t ht => ?_⟩
    rcases ht.lt_or_eq with ht | rfl
    · convert ((hV t 𝔢).scale _ hl0.le).mul ((hV t 𝔢).scale _ hβ)
      ring
    · convert (hVm.scale _ hl0.le).mul ((hV k le_rfl).scale _ hβ)
      push_cast
      field_simp; ring

abbrev Strings := FreeMonoid FiniteEuclidean
open FiniteEuclidean

lemma flatten_append l k l' k' (h : l.length = k.length) :
    ‖flatten (l ++ l') - flatten (k ++ k')‖ ^ 2 = ‖flatten l - flatten k‖ ^ 2 + ‖flatten l' - flatten k'‖ ^ 2 := by
  induction l generalizing k with
  | nil => cases k <;> simp_all
  | cons x l ih => cases k with
    | nil => simp at h
    | cons y k => simp only [List.cons_append, flatten_cons, ih k (by grind)]
                  ring

variable (a)

def Fam (u : ℝ) (x : ι → Strings) : Prop :=
  ∀ i j, (x i).toList.length = (x j).toList.length ∧ ‖𝔧 - flatten (x j).toList‖ ^ 2 = u * 𝔨

attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

def Rlz (u : ℝ) (V : ι → Ultrafilter Strings) : Prop :=
  ∀ B : ι → Set Strings, (∀ i, B i ∈ V i) → ∃ x, Fam a u x ∧ ∀ i, x i ∈ B i

variable {a}

lemma Rlz.mul (hV : Rlz a u V) (hW : Rlz a v W) : Rlz a (u + v) fun i => V i * W i := fun B hB => by
  obtain ⟨x, hx, hxB⟩ := hV (fun i => {x | {y | x * y ∈ B i} ∈ W i}) fun i => (Ultrafilter.eventually_mul _ _ _).1 (hB i)
  obtain ⟨y, hy, hyB⟩ := hW (fun i => {y | x i * y ∈ B i}) hxB
  exact ⟨x * y, fun i j => ⟨by simp [𝔥.1, (hy i j).1], by
    simp [flatten_append _ _ _ _ 𝔥.1, 𝔥.2, (hy i j).2]
    ring⟩, hyB⟩

lemma Path.real [Finite ι] (Ψ : LetterGroup →ₙ* Ultrafilter Strings) p
    (hΨ : ∀ z, Ψ 𝔠 = p * pure 𝔠 * p) (h : Path a w u) : Rlz a u fun i => Ψ (w i) := by
  have const U : Rlz a 0 fun _ => U := fun B hB =>
    let ⟨x, hx⟩ := (Filter.eventually_all.2 hB).exists
    ⟨fun _ => x, fun _ _ => by simp, hx⟩
  induction h with
  | diag g => exact const _
  | copy b hb =>
    simpa [hΨ] using ((const p).mul fun B hB => ⟨_, fun i j => ⟨rfl, by simpa [flatten_cons, flatten.eq_1] using hb.2 i j⟩,
      fun i => Ultrafilter.mem_pure.1 (hB i)⟩).mul (const p)
  | mul _ _ hu hv => simpa using hu.mul hv


lemma exists_corner_map : ∃ (p : Ultrafilter Strings) (Ψ : LetterGroup →ₙ* Ultrafilter Strings),
    ∀ z, Ψ 𝔠 = p * pure 𝔠 * p := by
  obtain ⟨N, hN⟩ := zorn_superset {N : Set (Ultrafilter Strings) | IsClosed N ∧ N.Nonempty ∧ ∀ x, ∀ y ∈ N, x * y ∈ N}
    fun c hcs hchain => by
      obtain rfl | hc := c.eq_empty_or_nonempty
      · exact ⟨_, ⟨isClosed_univ, Set.univ_nonempty, by simp⟩, by simp⟩
      have := hc.to_subtype
      exact ⟨⋂₀ c, ⟨isClosed_sInter fun N hN => 𝔦.1, IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (IsChain.directedOn hchain.symm) (fun N hN => 𝔦.2.1) (fun N hN => 𝔦.1.isCompact) fun N hN => 𝔦.1,
        fun x y hy => Set.mem_sInter.2 fun N hN => 𝔦.2.2 x y (hy N hN)⟩, fun _ => Set.sInter_subset_of_mem⟩
  obtain ⟨p, hpN, hp⟩ := exists_idempotent_in_compact_subsemigroup Ultrafilter.continuous_mul_left N hN.prop.2.1
    hN.prop.1.isCompact fun x _ y hy => hN.prop.2.2 x y hy
  have hi y (hpy : p * y = y) (hy : y * p = y) : ∃ v, p * v = v ∧ v * p = v ∧ v * y = p := by
    obtain ⟨v, hv⟩ : p ∈ Set.range (· * y) := hN.eq_of_subset ⟨(isCompact_range (Ultrafilter.continuous_mul_left y)).isClosed,
      ⟨_, y, rfl⟩, by rintro x _ ⟨z, rfl⟩
                      exact ⟨x * z, mul_assoc x z y⟩⟩ (by rintro _ ⟨z, rfl⟩; exact hN.prop.2.2 z y (hy ▸ hN.prop.2.2 y p hpN)) ▸ hpN
    exact ⟨p * v * p, by grind, by grind, by grind⟩
  choose v h1 h2 h3 using hi
  let C := {x : Ultrafilter Strings // p * x = x ∧ x * p = x}
  let : Mul C := ⟨fun x y => ⟨x.1 * y.1, by grind, by grind⟩⟩
  let : One C := ⟨⟨p, hp, hp⟩⟩
  let : Inv C := ⟨fun y => ⟨v y.1 y.2.1 y.2.2, h1 .., h2 ..⟩⟩
  let : Group C := .ofLeftAxioms (fun x y z => Subtype.ext (mul_assoc ..)) (fun x => Subtype.ext x.2.1) fun x => Subtype.ext (h3 ..)
  exact ⟨p, ⟨fun g => (FreeGroup.lift (fun z => (⟨p * pure 𝔠 * p, by grind, by grind⟩ : C)) g).1,
    fun x y => by rw [map_mul]
                  rfl⟩, fun z => by simp⟩


notation "𝔣" => (Finset.univ.filter fun j => line.idxFun j = none)

theorem ramsey_of_paths (a : Fin s → Space d)
    (hV : ∀ k : ℕ, ∃ V L, 0 < L ∧ ∀ t ≤ k, Path (embed d ∘ a) V (L / (t + 1))) : Ramsey a := by
  intro r hr
  by_contra hbad
  push Not at hbad
  choose c hc using fun n => hbad (n + 1) 𝔢
  choose C hC using fun z : FiniteEuclidean => (Ultrafilter.eventually_exists_iff
    (P := fun k n => c n (WithLp.toLp 2 fun i => z i) = k)).1 (.of_forall fun _ => ⟨_, rfl⟩)
  obtain ⟨β, _, hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) (Fin r)
  obtain ⟨V, L, hL, hV⟩ := hV (Fintype.card β)
  obtain ⟨p, Ψ, hΨ⟩ := exists_corner_map
  let word (x : β → Fin s) := dil L⁻¹ ((Finset.univ.toList.map fun j => V (x j)).prod)
  choose col hcol using fun x => (Ultrafilter.eventually_exists_iff (f := Ψ (word x))
    (P := fun k y => C (flatten y.toList) = k)).1 (.of_forall fun _ => ⟨_, rfl⟩)
  obtain ⟨line, k, hk⟩ := hHJ col
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.2 (line.proper.imp fun j hj => Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩) : 0 < (𝔣).card).ne'
  have hw : Path (embed d ∘ a) (fun i => word (line i)) 1 := by
    convert (Path.prod _ _ (fun j => if line.idxFun j = none then L / (t + 1) else 0) fun j _ => ?_).scale L⁻¹ 𝔡
    · simp [Finset.sum_map_toList, Finset.sum_ite, ht]
      field_simp
    · have := Finset.card_le_univ 𝔣
      cases h : line.idxFun j <;> simp [h, Combinatorics.Line.coe_apply]
      exacts [hV t 𝔢, .diag _]
  obtain ⟨x, hx, hxB⟩ := hw.real Ψ p hΨ (fun _ => {y | C (flatten y.toList) = k}) fun i => hk i ▸ hcol (line i)
  obtain ⟨M, hM⟩ := Finite.exists_le fun i => (𝔧).support.sup id
  obtain ⟨n, hn, hn'⟩ := ((Filter.eventually_all.2 fun i => hC (𝔧)).and
    (Ultrafilter.of_le Filter.atTop (Filter.eventually_ge_atTop M))).exists
  have he i : embed (n + 1) (WithLp.toLp 2 fun j => 𝔧 j) = 𝔧 := by
    ext m
    by_cases hm : m < n + 1
    · exact embed_apply _ _ ⟨m, hm⟩
    · rw [embed_outside _ _ _ 𝔢, eq_comm, ← Finsupp.notMem_support_iff]
      exact fun h => hm (Nat.lt_succ_of_le ((Finset.le_sup h).trans ((hM i).trans hn')))
  refine (hc n _ (fun i j => ?_) k).elim fun i hi => hi ((hn i).trans (hxB i))
  rw [dist_eq_norm, dist_eq_norm, ← (embed (n + 1)).norm_map, map_sub, he, he, ← (embed d).norm_map, map_sub]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [𝔥.2, one_mul]; rfl)


theorem fieldCriterion_ramsey (a : Fin s → Space d) (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : RealCriterion a) : Ramsey a := by
  refine ramsey_of_paths a fun k => ?_
  have hη : 0 < 1 / (2 * 𝔤 : ℝ) := by positivity
  obtain ⟨ℓ, -, f, g, hf, hg, hperm⟩ := realCriterion_two_scale a hd 𝔢 h _ hη
  choose σ hσ using hperm
  let : MulAction (Equiv.Perm (Fin ℓ)) (Fin ℓ → ℝ) := arrowAction
  let z (x : Fin ℓ → ℝ) := embed ℓ (WithLp.toLp 2 x)
  let A := embed d ∘ a
  have hz h (b : Fin s → Space ℓ) q (hb : ∀ i j, ‖b i - b j‖ ^ 2 = q * 𝔨) hq :
      CopyPath A q fun i => z (h • ⇑(b i)) :=
    ⟨hq, fun i j => by simp only [z, A, Function.comp, ← map_sub, LinearIsometry.norm_map]; exact (congrArg (· ^ 2) ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ h).norm_map (b i - b j))).trans (hb i j)⟩
  have hg' i : σ i • ⇑𝔞 = ⇑(g i) := funext fun x => (by simpa using hσ i ((σ i)⁻¹ x) : g i x = f i ((σ i)⁻¹ x)).symm
  let P := paths A
  obtain ⟨w, m, hW, hm, hw⟩ := finite_group_averaging (H := Equiv.Perm (Fin ℓ)) AugKernel (s - 2) P.cost
    (fun g hg => cost_bdd fun i => derived_le_single _ _ P pair_inverse (pair_coverage ((embed d).injective.comp ha)) (by simp_all) i hg)
    (fun x => .of (z x)) (fun x y => Subgroup.subset_normalClosure ⟨_, _, rfl⟩)
    (fun v n => ∀ (f : Fin s → Fin ℓ → ℝ) q, (∀ h, CopyPath A q fun i => z (h • f i)) →
      Path A (fun i => v 𝔞) (q * n))
    (fun v n hv => ⟨fun b f q hq => by simpa [Pi.mul_def] using (hv f q hq).mul (.diag b), fun f q hq => by
      simpa [ave, mul_left_comm] using Path.prod Finset.univ.toList (fun k i => v (k • f i)) (fun _ => q * n) fun k _ =>
        hv _ q fun h => by simpa [mul_smul] using hq (h * k)⟩)
    (fun f q hq => by simpa using Path.copy _ (by simpa using hq 1)) (1 / (2 * 𝔤) / s) 𝔡 (Finset.univ.image fun i => ⇑𝔞)
  have hq := hW (fun i => σ i • ⇑𝔞) _ fun h => by simpa only [hg'] using hz h g _ hg 𝔡
  obtain ⟨u, v, m', n', hu, hv, he, hmn⟩ := frac_tuple (fun i => (w 𝔞)⁻¹ * w (σ i • ⇑𝔞)) _ fun i => by
    simpa [mul_assoc] using P.cost.conj (w 𝔞)⁻¹ (hw _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) (σ i))
  have e : (fun i => w (σ i • ⇑𝔞)) * v = (fun i => w 𝔞) * u :=
    funext fun i => by simp [inv_mul_eq_iff_eq_mul.1 (congrFun he i), mul_assoc]
  have := hu.nonneg
  obtain ⟨V, c, hc, -, hV⟩ := sync ((hW (fun i => ⇑𝔞) 1 fun h => hz h f 1 (by grind) zero_le_one).mul hu) (e ▸ hq.mul hv) 𝔡 k (by
    rw [Fintype.card_fin, ← mul_assoc, mul_div_cancel₀ _ 𝔡] at hmn
    field_simp at hmn ⊢
    nlinarith [ mul_nonneg (by positivity : (0 : ℝ) ≤ k * k + k) this])
  exact ⟨V, _, by positivity, hV⟩
