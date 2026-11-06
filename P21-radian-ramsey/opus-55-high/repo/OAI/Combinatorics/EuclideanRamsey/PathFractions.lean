/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean

@[expose] public section
open scoped commutatorElement
set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔟" => (u x)
local notation "𝔞" => (g • x)

variable [Group G] (N : Subgroup G) [N.Normal]

structure Cost (G : Type*) [Group G] where
  R : G → ℝ → Prop
  one : R 1 0
  inv {g b} : R g b → R g⁻¹ b
  conj {g b} (k) : R g b → R (k * g * k⁻¹) b
  mul {g h b c} : R g b → R h c → R (g * h) (b + c)
  mono {g b c} : R g b → b ≤ c → R g c

def Cost.ofSub : Cost G :=
  ⟨fun g _ => g ∈ N, N.one_mem, N.inv_mem, fun k h => ‹N.Normal›.conj_mem _ h k, N.mul_mem, fun h _ => h⟩

lemma Cost.prod (C : Cost G) (l : List α) a b c (h : ∀ j ∈ l, C.R (a j * (b j)⁻¹) c) :
    C.R ((l.map a).prod * (l.map b).prod⁻¹) (l.length * c) := by
  induction l with
  | nil => simpa using C.one
  | cons j l ih =>
    convert C.mul (C.conj (a j) (ih fun k hk => h k (by grind))) (h j (by simp)) using 1 <;> simp [mul_assoc]
    ring

structure GradedPaths (ι G : Type*) [Group G] where
  Holds : (ι → G) → ℝ → Prop
  diag : ∀ g, Holds (fun _ => g) 0
  mul : ∀ {u v m n}, Holds u m → Holds v n → Holds (u * v) (m + n)

namespace GradedPaths
variable (P : GradedPaths ι G)

def Frac (z : ι → G) (c : ℝ) : Prop :=
  ∃ u v m n, P.Holds u m ∧ P.Holds v n ∧ z = u * v⁻¹ ∧ m + n ≤ c

def PairInverse : Prop :=
  ∀ i j, i ≠ j → ∀ v m, P.Holds v m → ∃ b n, P.Holds b n ∧ b i = (v i)⁻¹ ∧ b j = (v j)⁻¹

def PairCoverage : Prop :=
  ∀ i j, i ≠ j → ∀ a ∈ N, ∀ b ∈ N, ∃ z m, P.Holds z m ∧ z i = a ∧ z j = b

variable {P}

lemma Frac.mono (h : P.Frac z c) (hcd : c ≤ d) : P.Frac z d := by
  grind [Frac]

lemma frac_one : P.Frac 1 0 := ⟨1, 1, 0, 0, P.diag 1, P.diag 1, by simp⟩

lemma Frac.inv (h : P.Frac z c) : P.Frac z⁻¹ c := by
  obtain ⟨u, v, m, n, h⟩ := h
  exact ⟨v, u, n, m, by grind [mul_inv_rev, inv_inv]⟩

lemma Frac.conj (h : P.Frac z c) g : P.Frac (fun i => g * z i * g⁻¹) c := by
  obtain ⟨u, v, m, n, hm, hn, rfl, hc⟩ := h
  exact ⟨_, _, _, _, P.mul (P.diag g) hm, P.mul (P.diag g) hn, by ext; simp; group, by simpa⟩

variable [DecidableEq ι]

lemma conj_single i g h : (fun j => g * (Pi.mulSingle i h : ι → G) j * g⁻¹) = Pi.mulSingle i (g * h * g⁻¹) := by
  ext j
  by_cases j = i <;> simp_all

lemma Frac.mul_single (hz : P.Frac z c) i (hg : P.Frac (Pi.mulSingle i g) d) :
    P.Frac (z * Pi.mulSingle i g) (c + d) := by
  obtain ⟨u, v, m, n, hm, hn, rfl, hc⟩ := hz
  have hh := hg.conj (v i)⁻¹
  rw [conj_single, inv_inv] at hh
  obtain ⟨a, b, k, l, hk, hl, he, hd⟩ := hh
  refine ⟨u * a, v * b, m + k, n + l, P.mul hm hk, P.mul hn hl, ?_, by linarith⟩
  rw [mul_assoc, show v⁻¹ * Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹ * g * v i) * v⁻¹ by
    ext j
    by_cases h : j = i <;> simp [h], he]
  group

lemma Frac.mul_pair (hP : P.PairInverse) (hz : P.Frac z c) (ht : P.Frac t d)
    i j (hij : i ≠ j) (hs : ∀ l, l ≠ i → l ≠ j → t l = 1) : ∃ e, P.Frac (z * t) e := by
  obtain ⟨u, v, m, n, hu, hv, rfl, -⟩ := hz
  obtain ⟨c, d, m', n', hc, hd, rfl, -⟩ := ht
  obtain ⟨b, k, hb, hi, hj⟩ := hP i j hij v n hv
  have : Commute (v * b) (c * d⁻¹) := by
    ext l
    by_cases hli : l = i
    · simp [hli, hi]
    by_cases hlj : l = j
    · simp [hlj, hj]
    simp [hs l hli hlj]
  exact ⟨_, u * b * c, v * b * d, _, _, P.mul (P.mul hu hb) hc, P.mul (P.mul hv hb) hd, by
    rw [show u * v⁻¹ = u * b * (v * b)⁻¹ by group, mul_assoc, this.inv_left.eq]
    group, le_rfl⟩

variable (P) in
def single (i : ι) : Subgroup G where
  carrier := {g | ∃ c, P.Frac (Pi.mulSingle i g) c}
  one_mem' := ⟨0, by simpa using P.frac_one⟩
  mul_mem' := fun ⟨c, hc⟩ ⟨d, hd⟩ => ⟨c + d, by rw [Pi.mulSingle_mul]; exact hc.mul_single _ hd⟩
  inv_mem' := fun ⟨c, hc⟩ => ⟨c, by rw [Pi.mulSingle_inv]; exact hc.inv⟩

end GradedPaths

def Derived : ℕ → Subgroup G
  | 0 => N
  | n + 1 => ⁅Derived n, Derived n⁆

instance (n : ℕ) : (Derived N n).Normal := by
  induction n <;> unfold Derived <;> infer_instance

lemma derived_le n : Derived N n ≤ N := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (Subgroup.commutator_le_left _ _).trans ih

namespace GradedPaths

def restrict {ι κ : Type*} (P : GradedPaths ι G) (f : κ → ι) : GradedPaths κ G where
  Holds u n := ∃ v, P.Holds v n ∧ u = v ∘ f
  diag g := ⟨_, P.diag g, rfl⟩
  mul := fun ⟨v, hv, e⟩ ⟨w, hw, e'⟩ => ⟨v * w, P.mul hv hw, by rw [e, e']; rfl⟩

lemma le_single_of_card [Fintype ι] [DecidableEq ι] (P : GradedPaths ι G)
    (hc : P.PairCoverage N) (h : Fintype.card ι ≤ 2) i : N ≤ P.single i := by
  intro a ha
  obtain ⟨z, m, hz, hi, hj⟩ : ∃ z m, P.Holds z m ∧ z i = a ∧ ∀ l, l ≠ i → z l = 1 := by
    by_cases hj : ∃ j, j ≠ i
    · obtain ⟨j, hj⟩ := hj
      obtain ⟨z, m, hz, hi, hj'⟩ := hc i j hj.symm a ha 1 N.one_mem
      refine ⟨z, m, hz, hi, fun l hl => ?_⟩
      by_contra hl'
      exact absurd (Fintype.two_lt_card_iff.2 ⟨i, j, l, hj.symm, hl.symm, by grind⟩) (by omega)
    · exact ⟨_, 0, P.diag a, rfl, fun l hl => absurd ⟨l, hl⟩ hj⟩
  exact ⟨m, z, 1, m, 0, hz, P.diag 1, by ext l; by_cases h : l = i <;> simp_all, by simp⟩

theorem derived_le_single n [Fintype ι] [DecidableEq ι]
    (P : GradedPaths ι G) (hi : P.PairInverse) (hc : P.PairCoverage N)
    (hn : Fintype.card ι ≤ n + 2) i : Derived N n ≤ P.single i := by
  induction n generalizing ι with
  | zero => exact P.le_single_of_card N hc hn i
  | succ n ih =>
    by_cases hs : Fintype.card ι ≤ 2
    · exact (derived_le N _).trans (P.le_single_of_card N hc hs i)
    obtain ⟨⟨j, hji⟩, ⟨k, hki⟩, hjk⟩ := Fintype.one_lt_card_iff.1 (by simp; omega : 1 < Fintype.card {l // l ≠ i})
    simp at hjk
    have lift j (hji : j ≠ i) a (ha : a ∈ Derived N n) :
        ∃ z c, P.Frac z c ∧ z i = a ∧ ∀ l, l ≠ i → l ≠ j → z l = 1 := by
      obtain ⟨c, _, _, m, m', ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, he, hc'⟩ :=
        ih (P.restrict (Subtype.val : {l // l ≠ j} → ι))
          (fun i j hij v m ⟨w, hw, e⟩ => by
            obtain ⟨b, n, hb, h1, h2⟩ := hi i j (Subtype.val_injective.ne hij) w m hw
            exact ⟨b ∘ Subtype.val, n, ⟨b, hb, rfl⟩, by simp [e, h1], by simp [e, h2]⟩)
          (fun i j hij a ha b hb => by
            obtain ⟨z, m, hz, h1, h2⟩ := hc i j (Subtype.val_injective.ne hij) a ha b hb
            exact ⟨z ∘ Subtype.val, m, ⟨z, hz, rfl⟩, h1, h2⟩)
          (by simp_all)
          ⟨i, hji.symm⟩ ha
      refine ⟨u * v⁻¹, c, ⟨u, v, m, m', hu, hv, rfl, hc'⟩, ?_, fun l hli hlj => ?_⟩
      · simpa using (congrFun he ⟨i, hji.symm⟩).symm
      · simpa [hli] using (congrFun he ⟨l, hlj⟩).symm
    intro x hx
    refine Subgroup.commutator_le.2 (fun a ha b hb => ?_) hx
    obtain ⟨z, c, hz, hzi, hsz⟩ := lift j hji a ha
    obtain ⟨t, d, ht, hti, hst⟩ := lift k hki b hb
    obtain ⟨e₁, h₁⟩ := hz.mul_pair hi ht i k hki.symm hst
    obtain ⟨e₂, h₂⟩ := h₁.mul_pair hi hz.inv i j hji.symm (by simp_all)
    obtain ⟨e₃, h₃⟩ := h₂.mul_pair hi ht.inv i k hki.symm (by simp_all)
    refine ⟨e₃, ?_⟩
    convert h₃
    ext l
    by_cases hli : l = i
    · simp [hli, hzi, hti, commutatorElement_def]
    by_cases hlj : l = j
    · simp [hlj, hji, hst j hji hjk]
    · simp [hli, hsz l hli hlj]

variable [Fintype ι] [DecidableEq ι] (P : GradedPaths ι G)

def cost : Cost G where
  R g b := ∀ i, P.Frac (Pi.mulSingle i g) b
  one i := by simpa using P.frac_one
  inv h i := by rw [Pi.mulSingle_inv]
                exact (h i).inv
  conj k h i := conj_single i k _ ▸ (h i).conj k
  mul h h' i := by rw [Pi.mulSingle_mul]
                   exact (h i).mul_single i (h' i)
  mono h hb i := (h i).mono hb

variable {P}
lemma cost_bdd (h : ∀ i, g ∈ P.single i) : ∃ b, P.cost.R g b :=
  let ⟨M, hM⟩ := Finite.exists_le fun i => (h i).choose
  ⟨M, fun i => (h i).choose_spec.mono (hM i)⟩

lemma frac_tuple r B (h : ∀ i, P.cost.R (r i) B) : P.Frac r (Fintype.card ι * B) := by
  have (s : Finset ι) : P.Frac (fun l => if l ∈ s then r l else 1) (s.card * B) := by
    induction s using Finset.induction_on with
    | empty => simpa [Pi.one_def] using P.frac_one
    | insert a s ha ih =>
      convert ih.mul_single a (h a a) using 1
      · ext l
        by_cases hl : l = a <;> simp [hl, ha]
      · simp [Finset.card_insert_of_notMem ha]
        ring
  simpa using this Finset.univ
end GradedPaths
variable (H : Type*) [Group H] [MulAction H X] [Fintype H]
noncomputable def ave (w : X → G) (x : X) : G := ((Finset.univ.toList : List H).map fun k => w (k • x)).prod

def OrbitB (C : Cost G) (v : X → G) (x : X) (b : ℝ) : Prop := ∀ g h : H, C.R (v 𝔞 * (v (h • x))⁻¹) b

def Closed (P : (X → G) → ℝ → Prop) : Prop := ∀ v n, P v n → (∀ a, P (fun x => v x * a) n) ∧ P (ave H v) (Fintype.card H * n)

def Evo (v : X → G) (n : ℝ) (u : X → G) (k : ℝ) : Prop := ∀ P, Closed H P → P v n → P u k
variable {H}

lemma OrbitB.avg {v : X → G} (hv : OrbitB H C v x b) : OrbitB H C (ave H v) x (Fintype.card H * b) := by
  intro g h
  simpa [ave, mul_smul] using C.prod Finset.univ.toList _ _ b fun k _ => hv (k * g) (k * h)

lemma orbitB_closed (C : Cost G) (x : X) δ : Closed H fun v n => OrbitB H C v x (δ * n) :=
  fun v n hv => ⟨fun a g h => by aesop, by simpa [mul_left_comm] using hv.avg⟩


lemma contract (C : Cost G) {x : X} (hb : ∀ g : H, C.R (v 𝔞) B) (g : H) :
    C.R (ave H v 𝔞 * (v x)⁻¹) ((Fintype.card H - 1) * B) := by
  obtain ⟨p, q, he⟩ := List.mem_iff_append.1 (Finset.mem_toList.2 (Finset.mem_univ g⁻¹))
  have hl := congrArg List.length he
  simp at hl
  have h l := C.prod l (fun k => v ((k * g) • x)) 1 B fun _ _ => by simp_all
  convert C.mul (h p) (C.conj (v x) (h q)) using 1
  · simp [ave, he, mul_assoc, mul_smul, Pi.one_def]
  · rw [hl]
    push_cast
    ring

notation "𝔴" => (ave H fun y => u y * 𝔟⁻¹)

lemma raise {D : Subgroup G} [D.Normal] {x : X} (hu : OrbitB H (.ofSub D) u x b) :
    OrbitB H (.ofSub ⁅D, D⁆) 𝔴 x b' := by
  have key (g : H) : QuotientGroup.mk' ⁅D, D⁆ (𝔴 𝔞) = QuotientGroup.mk' _ (𝔴 x) := by
    simp only [ave, map_list_prod, List.map_map]
    classical
    have hp : (Finset.univ.toList.map (· * g)).Perm Finset.univ.toList :=
      List.perm_of_nodup_nodup_toFinset_eq ((Finset.nodup_toList _).map (mul_left_injective g)) (Finset.nodup_toList _) (by ext k; simpa using ⟨k * g⁻¹, by group⟩)
    have hm (k : H) : u (k • x) * 𝔟⁻¹ ∈ D := by simpa [Cost.ofSub] using hu k 1
    simpa [mul_smul, Function.comp_def] using (hp.map (fun k => QuotientGroup.mk' ⁅D, D⁆ (u (k • x) * 𝔟⁻¹))).prod_eq'
      (List.pairwise_of_forall_mem_list fun a ha b hb => by
        simp only [List.mem_map] at ha hb
        obtain ⟨k, -, rfl⟩ := ha
        obtain ⟨l, -, rfl⟩ := hb
        exact commutatorElement_eq_one_iff_commute.1 (by rw [← map_commutatorElement]; exact (QuotientGroup.eq_one_iff _).2 (Subgroup.commutator_mem_commutator (hm k) (hm l))))
  intro g h
  simpa [Cost.ofSub, div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.1 ((key g).trans (key h).symm)


lemma rate (h : ℕ) (hh : 0 < h) k B δ (hk : 0 < k) (hδ : 0 < δ) :
    ∃ t, 2 * (B * (h - 1 : ℝ) ^ t) ≤ δ * (h ^ t * k) := by
  have h1 : (1 : ℝ) ≤ h := mod_cast hh
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show 0 < δ * k / (2 * |B| + 1) by positivity) (show (h - 1 : ℝ) / h < 1 by rw [div_lt_one (by positivity)]; linarith)
  refine ⟨t, ?_⟩
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)] at ht
  nlinarith [le_abs_self B, pow_nonneg (show (0 : ℝ) ≤ h - 1 by linarith) t, pow_pos (show (0 : ℝ) < h by linarith) t]

theorem finite_group_averaging r (C : Cost G)
    (hC : ∀ g ∈ Derived N r, ∃ b, C.R g b) letter (hletter : ∀ x y, letter x * (letter y)⁻¹ ∈ N)
    W (hW : Closed H W) (h1 : W letter 1) δ (hδ : 0 < δ) (s : Finset X) :
    ∃ w m, W w m ∧ 0 < m ∧ ∀ x ∈ s, ∀ h : H, C.R (w (h • x) * (w x)⁻¹) (δ * m) := by
  classical
  let I v n := W v n ∧ 0 < n ∧ ∀ x, OrbitB H (.ofSub N) v x (0 * n)
  have hI : Closed H I := fun v n ⟨h1, h2, h3⟩ => ⟨fun a => ⟨(hW v n h1).1 a, h2, fun x => (orbitB_closed _ x 0 v n (h3 x)).1 a⟩,
    (hW v n h1).2, by positivity, fun x => (orbitB_closed _ x 0 v n (h3 x)).2⟩
  have improve (v n) (hv : I v n) x : ∃ u k, Evo H v n u k ∧ OrbitB H C u x (δ * k) := by
    have (j : ℕ) : ∃ u k, Evo H v n u k ∧ OrbitB H (.ofSub (Derived N j)) u x 0 := by
      induction j with
      | zero => exact ⟨v, n, fun _ _ h => h, by simpa [Derived] using hv.2.2 x⟩
      | succ j ih =>
        obtain ⟨u, k, e, hu⟩ := ih
        exact ⟨_, _, fun P hP h => (hP _ _ ((hP _ _ (e P hP h)).1 𝔟⁻¹)).2, raise hu⟩
    obtain ⟨u, k, e, hu⟩ := this r
    choose b hb using fun g => hC _ (by simpa [Cost.ofSub] using hu g 1)
    obtain ⟨B, hB⟩ := Finite.exists_le b
    have (t : ℕ) : ∃ v', Evo H u k v' (Fintype.card H ^ t * k) ∧ ∀ g : H, C.R (v' 𝔞) (B * (Fintype.card H - 1) ^ t) := by
      induction t with
      | zero => exact ⟨_, fun P hP h => by simpa using (hP _ _ h).1 𝔟⁻¹, fun g => by simpa using C.mono (hb g) (hB g)⟩
      | succ t ih =>
        obtain ⟨v', e', hv'⟩ := ih
        exact ⟨fun y => ave H v' y * (v' x)⁻¹, fun P hP h => by simpa [pow_succ, mul_assoc, mul_left_comm] using (hP _ _ (hP _ _ (e' P hP h)).2).1 (v' x)⁻¹,
          fun g => by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using contract C hv' g⟩
    obtain ⟨t, ht⟩ := rate (Fintype.card H) Fintype.card_pos k B δ (e I hI hv).2.1 hδ
    obtain ⟨v', e', hv'⟩ := this t
    exact ⟨v', _, fun P hP h => e' P hP (e P hP h), fun g h => C.mono (C.mul (hv' g) (C.inv (hv' h))) (by linarith)⟩
  have key (s : Finset X) : ∃ v n, I v n ∧ ∀ x ∈ s, OrbitB H C v x (δ * n) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨letter, 1, ⟨h1, one_pos, fun x g h => by simpa [Cost.ofSub] using hletter _ _⟩, by simp⟩
    | insert x s hx ih =>
      obtain ⟨v, n, hv, hs⟩ := ih
      obtain ⟨u, k, e, hu⟩ := improve v n hv x
      exact ⟨u, k, e I hI hv, by simpa [hu] using fun y hy => e _ (orbitB_closed C y δ) (hs y hy)⟩
  obtain ⟨v, n, ⟨hW, hn, -⟩, h⟩ := key s
  exact ⟨v, n, hW, hn, fun x hx h' => by simpa using h x hx h' 1⟩
