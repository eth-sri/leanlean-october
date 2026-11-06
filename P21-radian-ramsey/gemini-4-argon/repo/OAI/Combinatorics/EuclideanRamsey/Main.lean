module

public import OAI.Combinatorics.EuclideanRamsey.CorrectionPaths
public import OAI.Combinatorics.EuclideanRamsey.TensorDescent

@[expose] public section

namespace OAI.EuclideanRamsey
noncomputable section
open Filter Set
open scoped BigOperators RealInnerProductSpace TensorProduct commutatorElement

universe uGroup uIndex uAction uPoint uAlpha

section Fractions
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

def RightFraction (M : Submonoid (ι → G)) (z : ι → G) : Prop :=
  ∃ u ∈ M, ∃ v ∈ M, z = u * v⁻¹

def HasDiagonal (M : Submonoid (ι → G)) : Prop := ∀ g : G, (fun _ => g) ∈ M

def PairInverse (M : Submonoid (ι → G)) : Prop :=
  ∀ i j : ι, i ≠ j → ∀ v ∈ M, ∃ b ∈ M, v i * b i = 1 ∧ v j * b j = 1

omit [DecidableEq ι] in
lemma RightFraction.inv {M : Submonoid (ι → G)} {z : ι → G} :
    RightFraction M z → RightFraction M z⁻¹ := by
  rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨v, hv, u, hu, by group⟩

omit [DecidableEq ι] in
lemma RightFraction.conjugate {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} : RightFraction M z → ∀ g : G, RightFraction M fun i => g * z i * g⁻¹ := by
  rintro ⟨u, hu, v, hv, rfl⟩ g
  exact ⟨(fun _ => g) * u, M.mul_mem (hM g) hu,
    (fun _ => g) * v, M.mul_mem (hM g) hv, by ext i; simp only [Pi.mul_apply, Pi.inv_apply]; group⟩

lemma conjugate_single (i : ι) (g h : G) :
    (fun j => g * (Pi.mulSingle i h : ι → G) j * g⁻¹) = Pi.mulSingle i (g * h * g⁻¹) := by
  ext j; by_cases hj : j = i <;> simp [hj]

def singleFractions (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) : Subgroup G where
  carrier := {g | RightFraction M (Pi.mulSingle i g)}
  one_mem' := ⟨1, M.one_mem, 1, M.one_mem, by simp⟩
  mul_mem' {x y} hx hy := by
    change RightFraction M (Pi.mulSingle i (x * y))
    rw [Pi.mulSingle_mul]
    obtain ⟨u, hu, v, hv, hx0⟩ := hx
    rw [hx0]
    have hh := hy.conjugate hM (v i)⁻¹
    rw [conjugate_single, inv_inv] at hh
    obtain ⟨a, ha, b, hb, he⟩ := hh
    refine ⟨u * a, M.mul_mem hu ha, v * b, M.mul_mem hv hb, ?_⟩
    have ht : v⁻¹ * Pi.mulSingle i y = Pi.mulSingle i ((v i)⁻¹ * y * v i) * v⁻¹ := by
      ext j; by_cases hj : j = i
      · subst j; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [mul_assoc, ht, he]; group
  inv_mem' {a} ha := by
    change RightFraction M (Pi.mulSingle i a⁻¹)
    rw [Pi.mulSingle_inv]; exact ha.inv

lemma RightFraction.mul_pair {M : Submonoid (ι → G)} (hM : PairInverse M)
    {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
    (i j : ι) (hij : i ≠ j) (hs : ∀ l, l ≠ i → l ≠ j → t l = 1) :
    RightFraction M (z * t) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := hz
  obtain ⟨c, hc, d, hd, rfl⟩ := ht
  obtain ⟨b, hb, hi, hj⟩ := hM i j hij v hv
  have hcomm : Commute (v * b) (c * d⁻¹) := by
    ext l
    by_cases hli : l = i
    · subst l; simp only [Pi.mul_apply, Pi.inv_apply] at *; rw [hi]; simp
    by_cases hlj : l = j
    · subst l; simp only [Pi.mul_apply, Pi.inv_apply] at *; rw [hj]; simp
    · have hh : c l * (d l)⁻¹ = 1 := hs l hli hlj
      change v l * b l * (c l * (d l)⁻¹) = c l * (d l)⁻¹ * (v l * b l)
      rw [hh]; simp
  refine ⟨u * b * c, M.mul_mem (M.mul_mem hu hb) hc, v * b * d, M.mul_mem (M.mul_mem hv hb) hd, ?_⟩
  rw [show u * v⁻¹ = u * b * (v * b)⁻¹ by group, mul_assoc, hcomm.inv_left.eq]; group

end Fractions

section DerivedSection
variable {G : Type uGroup} [Group G]

def Derived (N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n + 1 => ⁅Derived N n, Derived N n⁆

instance derived_normal (N : Subgroup G) [N.Normal] (n : ℕ) : (Derived N n).Normal := by
  induction n with
  | zero => exact inferInstanceAs N.Normal
  | succ _ _ => exact Subgroup.commutator_normal _ _

def PairCoverage {ι : Type uIndex} (M : Submonoid (ι → G)) (N : Subgroup G) : Prop :=
  ∀ i j : ι, i ≠ j → ∀ a ∈ N, ∀ b ∈ N, ∃ z ∈ M, z i = a ∧ z j = b

theorem derived_subset_single (N : Subgroup G) [N.Normal] (n : ℕ)
    (ι : Type uIndex) [Fintype ι] [DecidableEq ι] (M : Submonoid (ι → G))
    (hd : HasDiagonal M) (hi : PairInverse M) (hc : PairCoverage M N)
    (hcard : Fintype.card ι ≤ n + 2) (i : ι) : Derived N n ≤ singleFractions M hd i := by
  induction n generalizing ι with
  | zero =>
    intro a ha
    change RightFraction M (Pi.mulSingle i a)
    by_cases h : ∃ j : ι, j ≠ i
    · obtain ⟨j, hji⟩ := h
      obtain ⟨z, hz, hzi, hzj⟩ := hc i j hji.symm a ha 1 N.one_mem
      refine ⟨z, hz, 1, M.one_mem, ?_⟩
      ext l
      by_cases hli : l = i
      · subst l; simpa using hzi.symm
      · have hlj : l = j := by
          by_contra hlj
          have hs : ({i, j, l} : Finset ι).card ≤ Fintype.card ι := Finset.card_le_univ _
          have : 3 ≤ Fintype.card ι := by simpa [hji, hji.symm, hli, Ne.symm hli, hlj, Ne.symm hlj] using hs
          omega
        subst l; simpa [Pi.mulSingle_eq_of_ne hli] using hzj.symm
    · refine ⟨_, hd a, 1, M.one_mem, ?_⟩
      ext l; rw [show l = i by by_contra hh; exact h ⟨l, hh⟩]; simp
  | succ n ih =>
    by_cases hsmall : Fintype.card ι ≤ 2
    · exact (Subgroup.commutator_le_left _ _).trans (ih ι M hd hi hc (by omega) i)
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
    obtain ⟨k, hki, hkj⟩ : ∃ k : ι, k ≠ i ∧ k ≠ j := by
      by_contra hh
      have he : (Finset.univ : Finset ι) ⊆ {i, j} := fun k _ => by
        by_cases hki : k = i <;> [ simp [hki]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (by by_contra hkj; exact hh ⟨k, hki, hkj⟩)) ]
      exact hsmall ((Finset.card_le_card he).trans ((Finset.card_insert_le _ _).trans (by simp)))
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have lift (j : ι) (hji : j ≠ i) (a : G) (ha : a ∈ Derived N n) :
        ∃ z : ι → G, RightFraction M z ∧ z i = a ∧ ∀ l, l ≠ i → l ≠ j → z l = 1 := by
      let κ := {l : ι // l ≠ j}
      let rHom : (ι → G) →* (κ → G) := { toFun := (· ∘ Subtype.val), map_one' := rfl, map_mul' := fun _ _ => rfl }
      let M' := M.map rHom
      let i' : κ := ⟨i, hji.symm⟩
      have hκ : Fintype.card κ ≤ n + 2 := by
        have hh := Fintype.card_subtype_lt (p := fun l : ι => l ≠ j) (x := j) (by simp)
        change Fintype.card κ < Fintype.card ι at hh; omega
      have he := ih κ M' (fun g => ⟨fun _ => g, hd g, rfl⟩)
        (by rintro x y hxy _ ⟨v, hv, rfl⟩
            obtain ⟨b, hb, hx, hy⟩ := hi x.1 y.1 (hxy ∘ Subtype.ext) v hv
            exact ⟨rHom b, ⟨b, hb, rfl⟩, hx, hy⟩)
        (fun x y hxy a ha b hb => by
          obtain ⟨z, hz, hx, hy⟩ := hc x.1 y.1 (hxy ∘ Subtype.ext) a ha b hb
          exact ⟨rHom z, ⟨z, hz, rfl⟩, hx, hy⟩) hκ i' ha
      obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, he⟩ := he
      refine ⟨u * v⁻¹, ⟨u, hu, v, hv, rfl⟩, by simpa [rHom, i'] using (congrFun he i').symm, fun l hli hlj => ?_⟩
      simpa [rHom, i', Pi.mulSingle_eq_of_ne (hli ∘ congrArg Subtype.val : (⟨l, hlj⟩ : κ) ≠ i')] using
        (congrFun he ⟨l, hlj⟩).symm
    obtain ⟨z, hz, hzi, hsz⟩ := lift j hji a ha
    obtain ⟨t, ht, hti, hst⟩ := lift k hki b hb
    have hzi' : ∀ l, l ≠ i → l ≠ j → z⁻¹ l = 1 := by simpa only [Pi.inv_apply, inv_eq_one] using hsz
    have hti' : ∀ l, l ≠ i → l ≠ k → t⁻¹ l = 1 := by simpa only [Pi.inv_apply, inv_eq_one] using hst
    have h := ((hz.mul_pair hi ht i k hki.symm hst).mul_pair hi hz.inv i j hji.symm hzi').mul_pair hi ht.inv i k hki.symm hti'
    have he : z * t * z⁻¹ * t⁻¹ = Pi.mulSingle i ⁅a, b⁆ := by
      ext l
      by_cases hli : l = i
      · subst l; simp [commutatorElement_def, hzi, hti]
      · by_cases hlj : l = j
        · subst l; simp [hst j hli hkj.symm, Pi.mulSingle_eq_of_ne hli]
        · simp [hsz l hli hlj, Pi.mulSingle_eq_of_ne hli]
    rwa [he] at h

end DerivedSection

def freeAugmentation (X : Type uPoint) : FreeGroup X →* Multiplicative ℤ :=
  FreeGroup.lift fun _ => Multiplicative.ofAdd 1

def AugKernel (X : Type uPoint) : Subgroup (FreeGroup X) := (freeAugmentation X).ker

instance (X : Type uPoint) : (AugKernel X).Normal := inferInstanceAs (freeAugmentation X).ker.Normal

abbrev LetterGroup := FreeGroup FiniteEuclidean
variable {ι : Type uIndex}

inductive UnitWords (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℕ → Prop
  | diag (g : LetterGroup) : UnitWords a (fun _ => g) 0
  | copy (b : ι → FiniteEuclidean) (h : ∀ i j, ‖b i - b j‖ = ‖a i - a j‖) :
      UnitWords a (fun i => FreeGroup.of (b i)) 1
  | mul {u v m n} : UnitWords a u m → UnitWords a v n → UnitWords a (u * v) (m + n)

section UnitGraded
variable (a : ι → FiniteEuclidean) [DecidableEq ι]

def unitMonoid : Submonoid (ι → LetterGroup) where
  carrier := {u | ∃ n, UnitWords a u n}
  one_mem' := ⟨0, .diag 1⟩
  mul_mem' := fun ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, hm.mul hn⟩

omit [DecidableEq ι] in
lemma unitDiagonal : HasDiagonal (unitMonoid a) := fun g => ⟨0, .diag g⟩

def BoundedFraction (z : ι → LetterGroup) (c : ℕ) : Prop :=
  ∃ (u v : ι → LetterGroup) (m n : ℕ), UnitWords a u m ∧ UnitWords a v n ∧ z = u * v⁻¹ ∧ m + n ≤ c

omit [DecidableEq ι] in
lemma bounded_one : BoundedFraction a 1 0 :=
  ⟨1, 1, 0, 0, .diag 1, .diag 1, by simp, le_rfl⟩

omit [DecidableEq ι] in
lemma bounded_inv {z : ι → LetterGroup} {c : ℕ} : BoundedFraction a z c → BoundedFraction a z⁻¹ c := by
  rintro ⟨u, v, m, n, hm, hn, rfl, hc⟩
  exact ⟨v, u, n, m, hn, hm, by group, by omega⟩

omit [DecidableEq ι] in
lemma bounded_conjugate {z : ι → LetterGroup} {c : ℕ} :
    BoundedFraction a z c → ∀ g : LetterGroup, BoundedFraction a (fun i => g * z i * g⁻¹) c := by
  rintro ⟨u, v, m, n, hm, hn, rfl, hc⟩ g
  exact ⟨(fun _ => g) * u, (fun _ => g) * v, m, n,
    by simpa using (UnitWords.diag g).mul hm, by simpa using (UnitWords.diag g).mul hn,
    by ext i; simp only [Pi.mul_apply, Pi.inv_apply]; group, hc⟩

lemma bounded_mul_single {z : ι → LetterGroup} {c d : ℕ} (hz : BoundedFraction a z c)
    (i : ι) {g : LetterGroup} (hg : BoundedFraction a (Pi.mulSingle i g) d) :
    BoundedFraction a (z * Pi.mulSingle i g) (c + d) := by
  obtain ⟨u, v, m, n, hm, hn, rfl, hc⟩ := hz
  have hh := bounded_conjugate a hg (v i)⁻¹
  rw [conjugate_single, inv_inv] at hh
  obtain ⟨u', v', k, l, hk, hl, he, hd⟩ := hh
  refine ⟨u * u', v * v', m + k, n + l, hm.mul hk, hn.mul hl, ?_, by omega⟩
  have ht : v⁻¹ * Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹ * g * v i) * v⁻¹ := by
    ext j; by_cases hj : j = i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc, ht, he]; group

end UnitGraded

def CopyPath (a : ι → FiniteEuclidean) (u : ℝ) (b : ι → FiniteEuclidean) : Prop :=
  0 ≤ u ∧ ∀ i j, ‖b i - b j‖ ^ 2 = u * ‖a i - a j‖ ^ 2

inductive Path (a : ι → FiniteEuclidean) : (ι → LetterGroup) → ℝ → Prop
  | diag (g : LetterGroup) : Path a (fun _ => g) 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : CopyPath a u b) :
      Path a (fun i => FreeGroup.of (b i)) u
  | mul {u v lmb μ} : Path a u lmb → Path a v μ → Path a (u * v) (lmb + μ)

lemma UnitWords.path {a : ι → FiniteEuclidean} {w n} (h : UnitWords a w n) : Path a w n := by
  induction h with
  | diag g => simpa only [Nat.cast_zero] using Path.diag (a := a) g
  | copy b hb =>
    simpa only [Nat.cast_one] using Path.copy (a := a) (u := 1) b ⟨zero_le_one, fun i j => by simp [hb i j]⟩
  | mul _ _ ihu ihv => simpa only [Nat.cast_add] using ihu.mul ihv

lemma extend_pair_E (a : ι → FiniteEuclidean) (i j : ι) (z z' : FiniteEuclidean)
    (h : ‖z' - z‖ = ‖a j - a i‖) :
    ∃ b : ι → FiniteEuclidean, b i = z ∧ b j = z' ∧ ∀ k l, ‖b k - b l‖ = ‖a k - a l‖ := by
  let R := (ℝ ∙ ((a j - a i) - (z' - z)))ᗮ.reflection
  refine ⟨fun k => z + R (a k - a i), by simp, ?_, fun k l => ?_⟩
  · simpa using congrArg (z + ·) (Submodule.reflection_sub h.symm)
  · simp only [add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right, LinearIsometryEquiv.norm_map]

lemma unit_pair_inverse (a : ι → FiniteEuclidean) [DecidableEq ι] : PairInverse (unitMonoid a) := by
  rintro i j _ u ⟨m, hm : UnitWords a u m⟩
  suffices ∃ v n, UnitWords a v n ∧ v i = (u i)⁻¹ ∧ v j = (u j)⁻¹ by
    obtain ⟨v, n, hv, hi, hj⟩ := this
    exact ⟨v, ⟨n, hv⟩, by simp [hi], by simp [hj]⟩
  induction hm with
  | diag g => exact ⟨_, 0, .diag g⁻¹, rfl, rfl⟩
  | copy b hb =>
    obtain ⟨c, hci, hcj, hc⟩ := extend_pair_E a i j (b j) (b i) (by rw [hb i j, norm_sub_rev (a i) (a j)])
    refine ⟨(fun _ => (FreeGroup.of (b i))⁻¹) * (fun k => FreeGroup.of (c k)) * (fun _ => (FreeGroup.of (b j))⁻¹), 1,
      by simpa using ((UnitWords.diag _).mul (.copy c hc)).mul (.diag _), by simp [hci], by simp [hcj]⟩
  | @mul u v m n _ _ ihu ihv =>
    obtain ⟨u', m', hu', hui, huj⟩ := ihu
    obtain ⟨v', n', hv', hvi, hvj⟩ := ihv
    exact ⟨v' * u', n' + m', hv'.mul hu', by simp [hui, hvi], by simp [huj, hvj]⟩

section Orbit
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

def SameOrbit (x y : X) : Prop := ∃ h : H, h • x = y
lemma SameOrbit.refl (x : X) : SameOrbit (H := H) x x := ⟨1, one_smul _ _⟩
lemma SameOrbit.symm {x y : X} : SameOrbit (H := H) x y → SameOrbit (H := H) y x := by
  rintro ⟨h, rfl⟩; exact ⟨h⁻¹, inv_smul_smul h x⟩
lemma SameOrbit.trans {x y z : X} : SameOrbit (H := H) x y → SameOrbit (H := H) y z →
    SameOrbit (H := H) x z := by
  rintro ⟨h, rfl⟩ ⟨g, rfl⟩; exact ⟨g * h, mul_smul _ _ _⟩

lemma product_difference_mem {N : Subgroup G} [N.Normal] {α : Type uAlpha}
    (l : List α) (a b : α → G) (h : ∀ j ∈ l, a j * (b j)⁻¹ ∈ N) :
    (l.map a).prod * ((l.map b).prod)⁻¹ ∈ N := by
  induction l with
  | nil => simp [N.one_mem]
  | cons j l ih =>
    have hm := ih fun k hk => h k (by simp [hk])
    simp only [List.map_cons, List.prod_cons]
    rw [show a j * (l.map a).prod * (b j * (l.map b).prod)⁻¹ =
      (a j * ((l.map a).prod * (l.map b).prod⁻¹) * (a j)⁻¹) * (a j * (b j)⁻¹) by group]
    exact N.mul_mem ((inferInstance : N.Normal).conj_mem _ hm _) (h j (by simp))

structure NormalCost (L : Subgroup G) where
  cost : G → ℝ
  nonneg : ∀ g, 0 ≤ cost g
  one : cost 1 = 0
  inv : ∀ g ∈ L, cost g⁻¹ ≤ cost g
  conj : ∀ g ∈ L, ∀ k, cost (k * g * k⁻¹) ≤ cost g
  mul : ∀ g ∈ L, ∀ h ∈ L, cost (g * h) ≤ cost g + cost h

namespace NormalCost
variable {L : Subgroup G} [L.Normal] (c : NormalCost L)

omit [L.Normal] in
lemma list_bound_const {α : Type uAlpha} (l : List α) (f : α → G) (h : ∀ g, f g ∈ L) (B : ℝ) (hB : ∀ g, c.cost (f g) ≤ B) :
    (l.map f).prod ∈ L ∧ c.cost (l.map f).prod ≤ l.length * B := by
  induction l with
  | nil => simp [L.one_mem, c.one]
  | cons g l ih =>
    exact ⟨L.mul_mem (h g) ih.1,
      (c.mul _ (h g) _ ih.1).trans (by simpa [add_mul, add_comm] using add_le_add (hB g) ih.2)⟩

end NormalCost

abbrev groupList (H : Type uAction) [Fintype H] : List H := (Finset.univ : Finset H).toList

abbrev orbitAverage [Fintype H] (w : X → G) (x : X) : G :=
  ((groupList H).map fun h => w (h • x)).prod

def OrbitIn (N : Subgroup G) (w : X → G) (x : X) : Prop :=
  ∀ y z, SameOrbit (H := H) x y → SameOrbit (H := H) x z → w y * (w z)⁻¹ ∈ N

def OrbitBound {L : Subgroup G} (c : NormalCost L) (w : X → G) (b : ℝ) (x : X) : Prop :=
  OrbitIn (H := H) L w x ∧ ∀ y z, SameOrbit (H := H) x y → SameOrbit (H := H) x z →
    c.cost (w y * (w z)⁻¹) ≤ b

variable [Fintype H]

inductive Evolution : (X → G) → ℕ → (X → G) → ℕ → Prop
  | refl (w m) : Evolution w m w m
  | normalize {w m v n} : Evolution w m v n → (a : G) → Evolution w m (fun x => v x * a) n
  | average {w m v n} : Evolution w m v n → Evolution w m (orbitAverage (H := H) v) (Fintype.card H * n)

namespace Evolution
variable {w v u : X → G} {m n k : ℕ}

lemma trans (h : Evolution (H := H) w m v n) (h' : Evolution (H := H) v n u k) :
    Evolution (H := H) w m u k := by
  induction h' with
  | refl => exact h
  | normalize _ a ih => exact ih.normalize a
  | average _ ih => exact ih.average

lemma positive (h : Evolution (H := H) w m v n) (hm : 0 < m) : 0 < n := by
  induction h with
  | refl => exact hm
  | normalize _ _ ih => exact ih
  | average _ ih => exact Nat.mul_pos Fintype.card_pos ih

lemma orbitIn (h : Evolution (H := H) w m v n) {N : Subgroup G} [N.Normal] {x : X}
    (hw : OrbitIn (H := H) N w x) : OrbitIn (H := H) N v x := by
  induction h with
  | refl => exact hw
  | normalize _ a ih =>
    intro y z hy hz; simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using ih y z hy hz
  | average _ ih =>
    exact fun y z hy hz => product_difference_mem _ _ _ fun g _ =>
      ih _ _ (hy.trans ⟨g, rfl⟩) (hz.trans ⟨g, rfl⟩)

lemma orbitBound (h : Evolution (H := H) w m v n) {L : Subgroup G} [L.Normal]
    {c : NormalCost L} {δ : ℝ} {x : X} (hw : OrbitBound (H := H) c w (δ * m) x) :
    OrbitBound (H := H) c v (δ * n) x := by
  refine ⟨h.orbitIn hw.1, ?_⟩
  induction h with
  | refl => exact hw.2
  | normalize _ a ih =>
    intro y z hy hz
    simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using ih y z hy hz
  | @average v' n' h' ih =>
    intro y z hy hz
    have aux (l : List H) :
        c.cost ((l.map fun g => v' (g • y)).prod * ((l.map fun g => v' (g • z)).prod)⁻¹) ≤
          l.length * (δ * n') := by
      induction l with
      | nil => simp [c.one]
      | cons j l ihl =>
        have hm := product_difference_mem l (fun g => v' (g • y)) (fun g => v' (g • z))
          fun g _ => (h'.orbitIn hw.1) _ _ (hy.trans ⟨g, rfl⟩) (hz.trans ⟨g, rfl⟩)
        have hj := (h'.orbitIn hw.1) _ _ (hy.trans ⟨j, rfl⟩) (hz.trans ⟨j, rfl⟩)
        let z₀ := (l.map fun g => v' (g • y)).prod * ((l.map fun g => v' (g • z)).prod)⁻¹
        have hz₀ : v' (j • y) * z₀ * (v' (j • y))⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem _ hm _
        simp only [List.map_cons, List.prod_cons, List.length_cons]
        rw [show v' (j • y) * (l.map fun g => v' (g • y)).prod * (v' (j • z) * (l.map fun g => v' (g • z)).prod)⁻¹ =
          (v' (j • y) * z₀ * (v' (j • y))⁻¹) * (v' (j • y) * (v' (j • z))⁻¹) by dsimp [z₀]; group]
        exact (c.mul _ hz₀ _ hj).trans
          (by push_cast; linarith [c.conj z₀ hm (v' (j • y)), ih _ _ (hy.trans ⟨j, rfl⟩) (hz.trans ⟨j, rfl⟩), ihl])
    simpa [mul_left_comm] using aux (groupList H)

end Evolution

variable [Fintype X]

lemma evolve_finite (w : X → G) (m : ℕ) (Good : X → (X → G) → ℕ → Prop)
    (preserve : ∀ {v n u k}, Evolution (H := H) v n u k → ∀ x, Good x v n → Good x u k)
    (improve : ∀ {v n}, Evolution (H := H) w m v n → ∀ x,
      ∃ u k, Evolution (H := H) v n u k ∧ Good x u k) :
    ∃ v n, Evolution (H := H) w m v n ∧ ∀ x, Good x v n := by
  classical
  have aux (t : Finset X) : ∃ v n, Evolution (H := H) w m v n ∧ ∀ x ∈ t, Good x v n := by
    induction t using Finset.induction_on with
    | empty => exact ⟨w, m, .refl _ _, by simp⟩
    | @insert x t _ ih =>
      obtain ⟨v, n, hev, hv⟩ := ih
      obtain ⟨u, k, heu, hu⟩ := improve hev x
      refine ⟨u, k, hev.trans heu, fun y hy => ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hu
      · exact preserve heu y (hv y hy)
  simpa using aux Finset.univ

end Orbit

lemma Evolution.path {ι : Type uIndex} {H : Type uAction} {X : Type uPoint} [Group H] [Fintype H] [MulAction H X]
    {a : ι → FiniteEuclidean} (z : X → FiniteEuclidean)
    (f : ι → X) (q : ℝ) (hq : ∀ h : H, CopyPath a q fun i => z (h • f i))
    {w : X → LetterGroup} {m : ℕ} (hw : Evolution (H := H) (fun x => FreeGroup.of (z x)) 1 w m) :
    Path a (fun i => w (f i)) (q * m) := by
  induction hw generalizing f with
  | refl => simpa [one_smul] using Path.copy (a := a) _ (hq 1)
  | normalize _ g ih => simpa [Pi.mul_def] using (ih f hq).mul (.diag g)
  | @average v n _ ih =>
    have aux (l : List H) : Path a (fun i => (l.map fun h => v (h • f i)).prod) (l.length * (q * n)) := by
      induction l with
      | nil => simpa [Pi.one_def] using Path.diag (a := a) 1
      | cons g l ihl =>
        simpa [add_mul, add_comm, Pi.mul_def] using (ih (fun i => g • f i) fun h => by simpa only [mul_smul] using hq (h * g)).mul ihl
    simpa [mul_left_comm] using aux (groupList H)

attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

@[instance_reducible] def ultrafilterMonoid {M : Type*} [Monoid M] : Monoid (Ultrafilter M) where
  toSemigroup := Ultrafilter.semigroup
  one := pure 1
  one_mul U := by
    change (pure (1 : M) : Ultrafilter M) * U = U
    exact Ultrafilter.coe_inj.mp <| Filter.ext' fun _ => by simp [Ultrafilter.eventually_mul]
  mul_one U := by
    change U * (pure (1 : M) : Ultrafilter M) = U
    exact Ultrafilter.coe_inj.mp <| Filter.ext' fun _ => by simp [Ultrafilter.eventually_mul]

attribute [local instance] ultrafilterMonoid

abbrev Strings := FreeMonoid FiniteEuclidean

lemma norm_flatten_cons (p q : FiniteEuclidean) (l k : List FiniteEuclidean) :
    ‖FiniteEuclidean.flatten (p :: l) - FiniteEuclidean.flatten (q :: k)‖ ^ 2 =
      ‖p - q‖ ^ 2 + ‖FiniteEuclidean.flatten l - FiniteEuclidean.flatten k‖ ^ 2 := by
  rw [show FiniteEuclidean.flatten (p :: l) - FiniteEuclidean.flatten (q :: k) =
    FiniteEuclidean.block 0 (p - q) + FiniteEuclidean.block 1 (FiniteEuclidean.flatten l - FiniteEuclidean.flatten k) by
      simp [FiniteEuclidean.flatten, map_sub]; abel,
    norm_add_sq_real, FiniteEuclidean.inner_block_ne 0 1 (by decide), mul_zero, add_zero,
    LinearIsometry.norm_map, LinearIsometry.norm_map]

def ColumnPath {ι : Type*} (a : ι → FiniteEuclidean) (U : ι → Ultrafilter Strings) (u : ℝ) : Prop :=
  ∀ B : ι → Set Strings, (∀ i, B i ∈ U i) → ∃ x : ι → Strings,
    ((∀ i j, (x i).toList.length = (x j).toList.length) ∧
      ∀ i j, ‖FiniteEuclidean.flatten (x i).toList - FiniteEuclidean.flatten (x j).toList‖ ^ 2 = u * ‖a i - a j‖ ^ 2) ∧
    ∀ i, x i ∈ B i

lemma ColumnPath.common {ι : Type*} [Finite ι] {a : ι → FiniteEuclidean} (U : Ultrafilter Strings) :
    ColumnPath a (fun _ => U) 0 := fun _ hB =>
  let ⟨y, hy⟩ := (eventually_all.mpr hB).exists
  ⟨fun _ => y, ⟨fun _ _ => rfl, fun _ _ => by simp⟩, hy⟩

lemma ColumnPath.copy {ι : Type*} {a : ι → FiniteEuclidean} {u : ℝ} (b : ι → FiniteEuclidean) (hb : CopyPath a u b) :
    ColumnPath a (fun i => pure (FreeMonoid.of (b i))) u := fun _ hB =>
  ⟨fun i => FreeMonoid.of (b i),
    ⟨fun _ _ => rfl, fun i j => by simpa [← map_sub, FiniteEuclidean.flatten] using hb.2 i j⟩,
    fun i => by simpa using hB i⟩

lemma ColumnPath.mul {ι : Type*} {a : ι → FiniteEuclidean} {U V u v}
    (hU : ColumnPath a U u) (hV : ColumnPath a V v) : ColumnPath a (U * V) (u + v) := fun B hB => by
  obtain ⟨x, hx, hxB⟩ := hU (fun i => {s | {t | s * t ∈ B i} ∈ V i})
    fun i => (Ultrafilter.eventually_mul _ _ _).mp (hB i)
  obtain ⟨y, hy, hyB⟩ := hV (fun i => {t | x i * t ∈ B i}) hxB
  refine ⟨x * y, ⟨fun i j => by change ((x i).toList ++ (y i).toList).length = _; simp [hx.1 i j, hy.1 i j],
    fun i j => ?_⟩, hyB⟩
  have hfl (l k l' k' : List FiniteEuclidean) (hlk : l.length = k.length) :
      ‖FiniteEuclidean.flatten (l ++ l') - FiniteEuclidean.flatten (k ++ k')‖ ^ 2 =
        ‖FiniteEuclidean.flatten l - FiniteEuclidean.flatten k‖ ^ 2 +
        ‖FiniteEuclidean.flatten l' - FiniteEuclidean.flatten k'‖ ^ 2 := by
    induction l generalizing k with
    | nil => cases k <;> simp [FiniteEuclidean.flatten] at hlk ⊢
    | cons p l ih =>
      cases k with
      | nil => simp at hlk
      | cons q k => simp [norm_flatten_cons, ih k (Nat.succ.inj hlk), add_assoc]
  change ‖FiniteEuclidean.flatten ((x i).toList ++ (y i).toList) -
    FiniteEuclidean.flatten ((x j).toList ++ (y j).toList)‖ ^ 2 = _
  rw [hfl _ _ _ _ (hx.1 i j), hx.2, hy.2, add_mul]

def scaleGroup (c : ℝ) : LetterGroup →* LetterGroup := FreeGroup.map fun z => Real.sqrt c • z

lemma Path.scale {ι : Type*} {a : ι → FiniteEuclidean} {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => scaleGroup c (w i)) (c * lmb) := by
  induction h with
  | diag g => simpa using Path.diag (a := a) (scaleGroup c g)
  | @copy u b hb =>
    simpa only [scaleGroup, FreeGroup.map.of] using
      Path.copy (fun i => Real.sqrt c • b i) ⟨mul_nonneg hc hb.1, fun i j => by
        rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hc, hb.2]; ring⟩
  | mul _ _ ihu ihv => simpa only [map_mul, Pi.mul_apply, Pi.mul_def, mul_add] using ihu.mul ihv

lemma exists_ultra_color {M κ : Type*} [Finite κ] (c : M → κ) (U : Ultrafilter M) :
    ∃ k, {x | c x = k} ∈ U :=
  Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall fun x => ⟨c x, rfl⟩)

def Corner {S : Type*} [Semigroup S] (p : S) := {x : S // p * x = x ∧ x * p = x}

instance {S : Type*} [Semigroup S] {p : S} : Semigroup (Corner p) where
  mul x y := ⟨x.val * y.val, by rw [← mul_assoc, x.2.1], by rw [mul_assoc, y.2.2]⟩
  mul_assoc _ _ _ := Subtype.ext (mul_assoc _ _ _)

def permute {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ)) :
    EuclideanSpace ℝ (Fin ℓ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ℓ) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

set_option maxHeartbeats 800000 in
theorem ramsey_of_algebraic {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsph : ∀ i, ∑ j, coordinate a i j * coordinate a i j = 1) : Ramsey a := by
  classical
  have : FiniteDimensional ℚ (Coeff a) := by
    unfold Coeff coordinateField
    have : Finite (Set.range fun ij : Fin s × Fin d => a ij.1 ij.2) := Set.finite_range _
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨ij, rfl⟩
    exact (halg ij.1 ij.2).isIntegral
  have : Algebra.FormallyUnramified ℚ (Coeff a) :=
    Algebra.FormallyUnramified.of_isSeparable ℚ (Coeff a)
  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := Coeff a)).mp inferInstance
  let φ : TensorRing a →ₐ[ℚ] RealTensor :=
    Algebra.TensorProduct.map (coordinateField a).val (coordinateField a).val
  have hreal : RealCriterion a := by
    let P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a) := fun α β => match α, β with
      | none, none => -t
      | some j, some j' => if j = j' then t else 0
      | _, _ => 0
    have hP (i : Fin s) : ∑ α, ∑ β,
        ((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * P α β *
        ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β)) = 0 := by
      have hterm (x : Coeff a) : (x ⊗ₜ[ℚ] (1 : Coeff a)) * t * ((1 : Coeff a) ⊗ₜ[ℚ] x) =
          ((x * x) ⊗ₜ[ℚ] (1 : Coeff a)) * t := by
        have hx := ht x
        rw [sub_mul] at hx
        rw [mul_assoc, mul_comm t, sub_eq_zero.mp hx, ← mul_assoc,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [P, Fintype.sum_option, augmented, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        zero_add, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hterm,
        ← Finset.sum_mul, ← TensorProduct.sum_tmul, hsph i]
      change (1 : TensorRing a) * (-t) * 1 + 1 * t = 0
      ring
    have haug (i : Fin s) (α : Option (Fin d)) :
        ((augmented a i α : Coeff a) : ℝ) = realAugmented a i α := by cases α <;> rfl
    have hmul (T : TensorRing a) :
        Algebra.TensorProduct.lmul' ℚ (φ T) = ((Algebra.TensorProduct.lmul' ℚ T : Coeff a) : ℝ) := by
      induction T using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy => simp [hx, hy]
    refine ⟨fun α β => φ (P α β), fun i => ?_, ?_⟩
    · have hφ (x y : Coeff a) : φ (x ⊗ₜ[ℚ] y) = (x : ℝ) ⊗ₜ[ℚ] (y : ℝ) := rfl
      simpa only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_zero,
        hφ, haug, OneMemClass.coe_one] using congrArg φ (hP i)
    · ext α β
      change Algebra.TensorProduct.lmul' ℚ (φ (P (some α) (some β))) = _
      rw [hmul]
      by_cases h : α = β <;> simp [P, h, ht1, Matrix.one_apply]
  let a' (i : Fin s) := FiniteEuclidean.embed d (a i)
  intro r _
  by_contra hbad
  have hc (n : ℕ) : ∃ c : Space (n + 1) → Fin r,
      ¬ ∃ b : Fin s → Space (n + 1), Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k := by
    by_contra hh; push Not at hh; exact hbad ⟨n + 1, by omega, hh⟩
  choose c hc using hc
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  let trunc (n : ℕ) (x : FiniteEuclidean) : Space n := WithLp.toLp 2 fun i => FiniteEuclidean.coords x i
  let c' (z : FiniteEuclidean) : Fin r := (exists_ultra_color (fun n => c n (trunc (n + 1) z)) U).choose
  obtain ⟨β, hβ, hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) (Fin r)
  let := hβ
  let n := Fintype.card β + 1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
  let η : ℝ := 1 / (4 * n)
  let δ : ℝ := 1 / (4 * n * s)
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ℓ, f, g, hf, hg, hperm⟩ := realCriterion_two_scale a hd (by omega) hreal η hη
  let q := η / (1 + η)
  have hq : 0 < q := div_pos hη (by linarith)
  choose σ hσ using hperm
  let H := Equiv.Perm (Fin ℓ)
  let X := H × Fin s
  let : MulAction H X :=
    { smul := fun h x => (h * x.1, x.2)
      one_smul := fun _ => Prod.ext (one_mul _) rfl
      mul_smul := fun _ _ _ => Prod.ext (mul_assoc _ _ _) rfl }
  let z (x : X) : FiniteEuclidean := FiniteEuclidean.embed ℓ (permute x.1 (f x.2))
  have hσ' (i : Fin s) : permute (σ i) (f i) = g i := by
    ext j; simpa [permute] using (hσ i ((σ i).symm j)).symm
  have hcopy (h : H) (i : Fin s) : z (h • ((σ i, i) : X)) = FiniteEuclidean.embed ℓ (permute h (g i)) := by
    rw [← hσ' i]; rfl
  let N := AugKernel FiniteEuclidean
  let L := Derived N (s - 2)
  have hL (i : Fin s) : L ≤ singleFractions (unitMonoid a') (unitDiagonal a') i :=
    derived_subset_single N (s - 2) (Fin s) (unitMonoid a') (unitDiagonal a') (unit_pair_inverse a')
      (fun i j hij g' hg' h' hh' => by
        let G : Subgroup (LetterGroup × LetterGroup) :=
          { toSubmonoid := (unitMonoid a').map
              ({ toFun := fun u => (u i, u j), map_one' := rfl, map_mul' := fun _ _ => rfl } : (Fin s → LetterGroup) →* _)
            inv_mem' := by
              rintro _ ⟨u, hu, rfl⟩
              obtain ⟨v, hv, hi, hj⟩ := unit_pair_inverse a' i j hij u hu
              exact ⟨v, hv, Prod.ext (mul_left_cancel (a := u i) (by simpa using hi))
                (mul_left_cancel (a := u j) (by simpa using hj))⟩ }
        have hdiag (k : LetterGroup) : (k, k) ∈ G := ⟨_, unitDiagonal a' k, rfl⟩
        let L' : Subgroup LetterGroup := G.comap (MonoidHom.inl LetterGroup LetterGroup)
        have : L'.Normal := ⟨fun x hx k => by
          change (k * x * k⁻¹, 1) ∈ G
          simpa using G.mul_mem (G.mul_mem (hdiag k) hx) (hdiag k⁻¹)⟩
        have hle : N ≤ L' := by
          let q' := QuotientGroup.mk' L'
          have hconst : ∀ x y, q' (FreeGroup.of x) = q' (FreeGroup.of y) :=
            FiniteEuclidean.unit_distance_constant _
              (norm_pos_iff.mpr (sub_ne_zero.mpr fun he => hij (ha ((FiniteEuclidean.embed d).injective he))))
              (fun z => q' (FreeGroup.of z)) fun x y hxy => by
                obtain ⟨b, hbi, hbj, hb⟩ := extend_pair_E a' i j x y
                  (by simpa only [norm_sub_rev y x, norm_sub_rev (a' j) (a' i)] using hxy)
                have hcopy : (FreeGroup.of x, FreeGroup.of y) ∈ G :=
                  ⟨fun k => FreeGroup.of (b k), ⟨1, UnitWords.copy b hb⟩,
                    Prod.ext (congrArg FreeGroup.of hbi) (congrArg FreeGroup.of hbj)⟩
                apply QuotientGroup.eq_iff_div_mem.mpr
                simpa [L', div_eq_mul_inv] using G.mul_mem hcopy (hdiag (FreeGroup.of y)⁻¹)
          let cy : Multiplicative ℤ →* (LetterGroup ⧸ L') :=
            { toFun := fun n => q' (FreeGroup.of 0) ^ Multiplicative.toAdd n
              map_one' := by simp
              map_mul' := fun _ _ => zpow_add _ _ _ }
          have he : q' = cy.comp (freeAugmentation FiniteEuclidean) := by
            apply FreeGroup.ext_hom; intro x; simpa [cy, freeAugmentation, q'] using hconst x 0
          intro x hx
          apply (QuotientGroup.eq_one_iff _).mp
          change q' x = 1
          rw [he, MonoidHom.comp_apply, (hx : freeAugmentation FiniteEuclidean x = 1), map_one]
        obtain ⟨v, hv, hv'⟩ := G.mul_mem (hle hg') (G.mul_mem (hdiag h') (hle (N.inv_mem hh')))
        exact ⟨v, hv, (congrArg Prod.fst hv').trans (by simp), (congrArg Prod.snd hv').trans (by simp)⟩)
      (by rw [Fintype.card_fin]; omega) i
  let sc (i : Fin s) (g : LetterGroup) : ℕ := sInf {c | BoundedFraction a' (Pi.mulSingle i g) c}
  have sb {i : Fin s} {g : LetterGroup} (hg : g ∈ L) :
      BoundedFraction a' (Pi.mulSingle i g) (sc i g) := by
    obtain ⟨u, ⟨m, hm⟩, v, ⟨n, hn⟩, he⟩ := hL i hg
    exact Nat.sInf_mem (⟨m + n, u, v, m, n, hm, hn, he, le_rfl⟩ : ∃ c, BoundedFraction a' _ c)
  let c₀ : NormalCost L :=
    { cost g := ∑ i, (sc i g : ℝ)
      nonneg _ := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      one := Finset.sum_eq_zero fun i _ => by
        exact_mod_cast Nat.eq_zero_of_le_zero (Nat.sInf_le (by simpa using bounded_one a'))
      inv g hg := Finset.sum_le_sum fun i _ => Nat.cast_le.mpr <|
        Nat.sInf_le (by rw [Pi.mulSingle_inv]; exact bounded_inv a' (sb hg))
      conj g hg k := Finset.sum_le_sum fun i _ => Nat.cast_le.mpr <|
        Nat.sInf_le (conjugate_single i k g ▸ bounded_conjugate a' (sb hg) k)
      mul g hg h hh := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Nat.cast_add, Nat.cast_le]
        exact Nat.sInf_le (by rw [Pi.mulSingle_mul]; exact bounded_mul_single a' (sb hg) i (sb hh)) }
  let letter (x : X) : LetterGroup := FreeGroup.of (z x)
  have hraise (d₀ : ℕ) (v : X → LetterGroup) (n₀ : ℕ) (x : X) (hw : OrbitIn (H := H) N v x) :
      ∃ u k, Evolution (H := H) v n₀ u k ∧ OrbitIn (H := H) (Derived N d₀) u x := by
    induction d₀ with
    | zero => exact ⟨v, n₀, .refl _ _, hw⟩
    | succ d₀ ih =>
      obtain ⟨u, k, heu, hu⟩ := ih
      refine ⟨_, _, (heu.normalize (u x)⁻¹).average, fun y z' hy hz => ?_⟩
      let M := Derived N d₀
      let w' (y : X) := u y * (u x)⁻¹
      obtain ⟨h, rfl⟩ := hy.symm.trans hz
      let q' := QuotientGroup.mk' ⁅M, M⁆
      rw [← div_eq_mul_inv]
      apply QuotientGroup.eq_iff_div_mem.mp
      change q' (orbitAverage (H := H) w' y) = q' (orbitAverage (H := H) w' (h • y))
      simp only [orbitAverage, map_list_prod, List.map_map]
      have hperm' : ((groupList H).map (· * h)).Perm (groupList H) := by
        refine (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map (mul_left_injective h))
          (Finset.nodup_toList _)).mpr fun g' => ?_
        simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, iff_true]
        exact ⟨g' * h⁻¹, inv_mul_cancel_right g' h⟩
      have hp' := hperm'.map fun g' => q' (w' (g' • y))
      simp only [List.map_map, Function.comp_def, mul_smul] at hp'
      refine (hp'.prod_eq' <| List.pairwise_map.mpr <| List.pairwise_of_forall fun g' k' => ?_).symm
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.commutator_mem_commutator
          (by simpa only [mul_smul] using hu _ _ (hy.trans ⟨g' * h, rfl⟩) (SameOrbit.refl x))
          (by simpa only [mul_smul] using hu _ _ (hy.trans ⟨k' * h, rfl⟩) (SameOrbit.refl x)))
  obtain ⟨v₀, n₀, hev, hv⟩ := evolve_finite letter 1 (fun x v _ => OrbitIn (H := H) L v x)
    (fun he _ hx => he.orbitIn hx) fun he x => hraise (s - 2) _ _ x
      (he.orbitIn fun _ _ _ _ => by change freeAugmentation _ _ = 1; simp [freeAugmentation, letter])
  have hn₀ : 0 < n₀ := hev.positive Nat.zero_lt_one
  obtain ⟨w, m, hew, hw⟩ := evolve_finite v₀ n₀ (fun x w m => OrbitBound (H := H) c₀ w (δ * m) x)
    (fun he _ hx => he.orbitBound hx) fun {u d₀} he x => by
      have hd₀ : 0 < d₀ := he.positive hn₀
      have hu : OrbitIn (H := H) L u x := he.orbitIn (hv x)
      let w₀ (y : X) : LetterGroup := u y * (u x)⁻¹
      let B : ℝ := ∑ y, c₀.cost (w₀ y)
      have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => c₀.nonneg _
      have hmem (y : X) (hy : SameOrbit (H := H) x y) : w₀ y ∈ L :=
        hu y x hy (SameOrbit.refl x)
      have hbound (y : X) (_ : SameOrbit (H := H) x y) : c₀.cost (w₀ y) ≤ B :=
        Finset.single_le_sum (fun _ _ => c₀.nonneg _) (Finset.mem_univ y)
      have hh' : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
      have hd' : (0 : ℝ) < d₀ := by exact_mod_cast hd₀
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ * d₀ / (2 * B + 1) by positivity)
        (show (Fintype.card H - 1 : ℝ) / Fintype.card H < 1 by rw [div_lt_one hh']; linarith)
      rw [div_pow, lt_div_iff₀ (by positivity), div_mul_eq_mul_div, div_lt_iff₀ (pow_pos hh' k)] at hk
      have hh1 : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos
      have hnon : 0 ≤ (Fintype.card H - 1 : ℝ) ^ k := pow_nonneg (by linarith) k
      have hrate : 2 * (B * (Fintype.card H - 1 : ℝ) ^ k) ≤ δ * ((Fintype.card H ^ k * d₀ : ℕ) : ℝ) := by
        push_cast; nlinarith
      have hiter (k : ℕ) : ∃ v', Evolution (H := H) w₀ d₀ v' (Fintype.card H ^ k * d₀) ∧
          (∀ y, SameOrbit (H := H) x y → v' y ∈ L) ∧
          ∀ y, SameOrbit (H := H) x y → c₀.cost (v' y) ≤ B * (Fintype.card H - 1 : ℝ) ^ k := by
        induction k with
        | zero => exact ⟨w₀, by simpa using Evolution.refl w₀ d₀, hmem, by simpa using hbound⟩
        | succ k ih =>
          obtain ⟨v', hev', hm', hb'⟩ := ih
          have hcb (y : X) (hy : SameOrbit (H := H) x y) :
              orbitAverage (H := H) v' y * (v' x)⁻¹ ∈ L ∧
              c₀.cost (orbitAverage (H := H) v' y * (v' x)⁻¹) ≤
                (Fintype.card H - 1 : ℝ) * (B * (Fintype.card H - 1 : ℝ) ^ k) := by
            let B' := B * (Fintype.card H - 1 : ℝ) ^ k
            obtain ⟨g', hg'⟩ := hy.symm
            obtain ⟨p, q', he'⟩ := List.mem_iff_append.mp (by simp : g' ∈ groupList H)
            have hmem' (h : H) : v' (h • y) ∈ L := hm' _ (hy.trans ⟨h, rfl⟩)
            have hcost' (h : H) : c₀.cost (v' (h • y)) ≤ B' := hb' _ (hy.trans ⟨h, rfl⟩)
            obtain ⟨ha', hca⟩ := c₀.list_bound_const p (fun h => v' (h • y)) hmem' B' hcost'
            obtain ⟨hb'', hcb'⟩ := c₀.list_bound_const q' (fun h => v' (h • y)) hmem' B' hcost'
            let b := (q'.map fun h => v' (h • y)).prod
            have hc' : v' x * b * (v' x)⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem _ hb'' _
            rw [show orbitAverage (H := H) v' y * (v' x)⁻¹ = (p.map fun h => v' (h • y)).prod * (v' x * b * (v' x)⁻¹) by
              simp [orbitAverage, he', hg', b, List.prod_append, mul_assoc]]
            refine ⟨L.mul_mem ha' hc', ?_⟩
            have hn'' : (Fintype.card H : ℝ) = p.length + (q'.length + 1) := by
              have := (by simp : (groupList H).length = Fintype.card H) ▸ congrArg List.length he'
              exact_mod_cast (by simpa [List.length_append] using this)
            calc
              _ ≤ c₀.cost (p.map fun h => v' (h • y)).prod + c₀.cost b :=
                (c₀.mul _ ha' _ hc').trans (add_le_add_right (c₀.conj b hb'' (v' x)) _)
              _ ≤ p.length * B' + q'.length * B' := add_le_add hca hcb'
              _ = (Fintype.card H - 1 : ℝ) * B' := by rw [hn'']; ring
          refine ⟨fun y => orbitAverage (H := H) v' y * (v' x)⁻¹, ?_,
            fun y hy => (hcb y hy).1, fun y hy => ?_⟩
          · convert hev'.average.normalize (v' x)⁻¹ using 1; simp [pow_succ, mul_left_comm, mul_comm]
          · convert (hcb y hy).2 using 1; ring
      obtain ⟨v', hev', hvm, hvb⟩ := hiter k
      refine ⟨v', Fintype.card H ^ k * d₀, (Evolution.normalize (.refl u d₀) (u x)⁻¹).trans hev',
        fun y z' hy hz => L.mul_mem (hvm y hy) (L.inv_mem (hvm z' hz)),
        fun y z' hy hz => ?_⟩
      exact (c₀.mul (v' y) (hvm y hy) (v' z')⁻¹ (L.inv_mem (hvm z' hz))).trans
        (by linarith [c₀.inv _ (hvm z' hz), hvb y hy, hvb z' hz])
  have hm : 0 < m := hew.positive hn₀
  have hwm (x y : X) (hxy : SameOrbit (H := H) x y) :
      w x * (w y)⁻¹ ∈ L ∧ c₀.cost (w x * (w y)⁻¹) ≤ δ * m :=
    ⟨(hw x).1 x y (SameOrbit.refl x) hxy, (hw x).2 x y (SameOrbit.refl x) hxy⟩
  let Dp (i : Fin s) : LetterGroup := w (1, i)
  let Dm (i : Fin s) : LetterGroup := w (σ i, i)
  have hp : Path a' Dp m := by
    simpa using (hev.trans hew).path z (fun i => (1, i)) 1 fun h => ⟨zero_le_one, fun i j => by
      change ‖FiniteEuclidean.embed ℓ (permute (h * 1) (f i)) -
        FiniteEuclidean.embed ℓ (permute (h * 1) (f j))‖ ^ 2 = _
      simp only [mul_one, ← map_sub, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map,
        one_mul, hf i j, a']⟩
  have hn0 : Path a' Dm (q * m) := (hev.trans hew).path z (fun i => (σ i, i)) q fun h => ⟨hq.le, fun i j => by
    dsimp only; rw [hcopy h i, hcopy h j]
    simp only [← map_sub, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map, hg i j, a', q]⟩
  let r₀ : Fin s → LetterGroup := Dp⁻¹ * Dm
  have hrc (i : Fin s) : r₀ i ∈ L ∧ c₀.cost (r₀ i) ≤ δ * m := by
    obtain ⟨hmem, hcost⟩ := hwm (1, i) (σ i, i) ⟨σ i, Prod.ext (mul_one _) rfl⟩
    have he : r₀ i = (w (1, i))⁻¹ * (w (1, i) * (w (σ i, i))⁻¹)⁻¹ * ((w (1, i))⁻¹)⁻¹ := by
      dsimp [r₀, Dp, Dm]; group
    rw [he]
    exact ⟨(inferInstance : L.Normal).conj_mem _ (L.inv_mem hmem) _,
      (c₀.conj _ (L.inv_mem hmem) _).trans ((c₀.inv _ hmem).trans hcost)⟩
  have hbt : BoundedFraction a' r₀ (∑ i, sc i (r₀ i)) := by
    have aux (l : List (Fin s)) (hl : l.Nodup) :
        BoundedFraction a' (fun j => if j ∈ l then r₀ j else 1) (l.map fun i => sc i (r₀ i)).sum := by
      induction l with
      | nil => simpa [Pi.one_def] using bounded_one a'
      | cons i l ih =>
        obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
        have ht := bounded_mul_single a' (ih hl) i (sb (hrc i).1)
        have he : (fun j => if j ∈ l then r₀ j else 1) * Pi.mulSingle i (r₀ i) =
            fun j => if j ∈ i :: l then r₀ j else 1 := by
          ext j; by_cases hj : j = i <;> [subst j; skip] <;> simp [*]
        simpa [he, Nat.add_comm] using ht
    simpa [Finset.sum_toList] using aux Finset.univ.toList (Finset.nodup_toList _)
  obtain ⟨u, v, b, e, hu, hv, he, hbe⟩ := hbt
  have hbe' : ((b + e : ℕ) : ℝ) ≤ s * (δ * m) := by
    calc ((b + e : ℕ) : ℝ) ≤ ∑ i, (sc i (r₀ i) : ℝ) := by exact_mod_cast hbe
      _ ≤ ∑ _i : Fin s, (δ * m) := Finset.sum_le_sum fun i _ =>
        (Finset.single_le_sum (f := fun j => (sc j (r₀ i) : ℝ))
          (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)).trans (hrc i).2
      _ = _ := by simp
  have heq : Dp * u = Dm * v := by
    simpa [r₀, mul_assoc] using (congrArg (fun t => Dp * t * v) he).symm
  let w' := Dp * u
  let lmb : ℝ := (m : ℝ) + b
  let μ : ℝ := q * m + e
  have hlmb : 0 < lmb := by dsimp [lmb]; positivity
  have hp' : Path a' w' lmb := hp.mul (UnitWords.path hu)
  have hm' : Path a' (Dp * u) μ := heq ▸ hn0.mul (UnitWords.path hv)
  have hratio : μ / lmb < 1 / (n : ℝ) := by
    have hr : μ / lmb ≤ q + s * δ := by
      rw [div_le_iff₀ hlmb]
      have hc' : (b : ℝ) + e ≤ s * (δ * m) := by simpa only [Nat.cast_add] using hbe'
      have : 0 ≤ (s : ℝ) * δ := by positivity
      dsimp [μ, lmb]; nlinarith
    refine hr.trans_lt ?_
    have hq' : q < η := (div_lt_iff₀ (by linarith)).mpr (by nlinarith)
    have he1 : η + s * δ = 1 / (2 * n) := by dsimp [η, δ]; field_simp; ring
    have hhalf : (1 : ℝ) / (2 * n) < 1 / n := one_div_lt_one_div_of_lt hn' (by linarith)
    linarith
  let ρ := μ / lmb
  have hρ : ρ < 1 := hratio.trans_le ((div_le_one hn').mpr (by exact_mod_cast (by omega : 1 ≤ n)))
  have hnorm : Path a' (fun i => scaleGroup lmb⁻¹ (w' i)) 1 := by
    simpa [inv_mul_cancel₀ hlmb.ne'] using hp'.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  have hnorm' : Path a' (fun i => scaleGroup lmb⁻¹ (w' i)) ρ := by
    simpa [ρ, div_eq_mul_inv, mul_comm, w'] using hm'.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  let v' (j : ℕ) : ℝ := if j < n then 1 / (j + 1 : ℕ) else ρ
  have hv' (j : ℕ) (hj : j < n) : v' (j + 1) ≤ v' j := by
    dsimp [v']; rw [ite_eq_left hj]; split_ifs with hj'
    · exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : j + 1 ≤ j + 1 + 1))
    · simpa [show j + 1 = n by omega, ρ] using hratio.le
  let cs (j : ℕ) := (v' j - v' (j + 1)) / (1 - ρ)
  have hcs (j : ℕ) (hj : j < n) : 0 ≤ cs j := div_nonneg (sub_nonneg.mpr (hv' j hj)) (by linarith)
  let ww (j : ℕ) (i : Fin s) : LetterGroup := scaleGroup (cs j) (scaleGroup lmb⁻¹ (w' i))
  let W : Fin s → LetterGroup := ((List.range n).map ww).prod
  let US := Ultrafilter Strings
  have hcont : ∀ y : US, Continuous (· * y) := Ultrafilter.continuous_mul_left
  let ideals : Set (Set US) := {N | IsClosed N ∧ N.Nonempty ∧ ∀ x y, y ∈ N → x * y ∈ N}
  obtain ⟨N₀, hN⟩ : ∃ N₀, Minimal (· ∈ ideals) N₀ := by
    refine zorn_superset _ fun ch hcs hchain => ⟨⋂₀ ch, ⟨isClosed_sInter fun N₀ hN => (hcs hN).1, ?_,
      fun x y hy => mem_sInter.mpr fun N₀ hN => (hcs hN).2.2 x y (mem_sInter.mp hy N₀ hN)⟩,
      fun N₀ hN => sInter_subset_of_mem hN⟩
    obtain rfl | hcn := ch.eq_empty_or_nonempty
    · simp
    convert! @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      _ _ _ hcn.coe_sort ((↑) : ch → Set US)
      (DirectedOn.directed_val (IsChain.directedOn hchain.symm))
      (fun N₀ => (hcs N₀.prop).2.1) (fun N₀ => (hcs N₀.prop).1.isCompact) (fun N₀ => (hcs N₀.prop).1)
    exact sInter_eq_iInter
  obtain ⟨p, hpN, hp0⟩ := exists_idempotent_in_compact_subsemigroup hcont N₀
    hN.prop.2.1 hN.prop.1.isCompact fun x _ y hy => hN.prop.2.2 x y hy
  have hi (y : US) (hy : p * y = y ∧ y * p = y) : ∃ v : US, (p * v = v ∧ v * p = v) ∧ v * y = p := by
    have hpr : Set.range (· * y) = N₀ := hN.eq_of_subset
      ⟨(isCompact_range (hcont y)).isClosed, ⟨y * y, y, rfl⟩, by rintro a _ ⟨b, rfl⟩; exact ⟨a * b, mul_assoc a b y⟩⟩
      (by rintro _ ⟨a, rfl⟩; exact hN.prop.2.2 a y (hy.2 ▸ hN.prop.2.2 y p hpN))
    obtain ⟨v, hv : v * y = p⟩ := hpr ▸ hpN
    exact ⟨p * v * p, ⟨by simp [← mul_assoc, hp0], by simp [mul_assoc, hp0]⟩,
      by rw [mul_assoc, mul_assoc p v, hy.1, hv, hp0]⟩
  let : One (Corner p) := ⟨⟨p, hp0, hp0⟩⟩
  let : Inv (Corner p) := ⟨fun y => ⟨(hi y.1 y.2).choose, (hi y.1 y.2).choose_spec.1⟩⟩
  let : Group (Corner p) := Group.ofLeftAxioms (fun _ _ _ => mul_assoc _ _ _)
    (fun x => Subtype.ext x.2.1) fun x => Subtype.ext (hi x.1 x.2).choose_spec.2
  let letter' (z : FiniteEuclidean) : Corner p :=
    ⟨p * pure (FreeMonoid.of z) * p, by simp [← mul_assoc, hp0], by simp [mul_assoc, hp0]⟩
  let ψ : LetterGroup →* Corner p := FreeGroup.lift letter'
  let Ψ : LetterGroup →ₙ* US := ({ toFun := Subtype.val, map_mul' _ _ := rfl } : Corner p →ₙ* US).comp ψ.toMulHom
  have hgen (z : FiniteEuclidean) : Ψ (FreeGroup.of z) = p * pure (FreeMonoid.of z) * p :=
    congrArg Subtype.val (FreeGroup.lift_apply_of (f := letter') (x := z))
  let coloring (x : Strings) : Fin r := c' (FiniteEuclidean.flatten x.toList)
  let L₀ : List β := Finset.univ.toList
  obtain ⟨line, k, hline⟩ := hHJ fun x => (exists_ultra_color coloring ((L₀.map fun j => Ψ (W (x j))).prod)).choose
  let S : Finset β := Finset.univ.filter fun j => line.idxFun j = none
  let t₀ := S.card
  have ht₀ : 1 ≤ t₀ := Finset.card_pos.mpr (let ⟨j, hj⟩ := line.proper; ⟨j, by simp [S, hj]⟩)
  have htn : t₀ ≤ n := (Finset.card_le_univ S).trans (Nat.le_succ _)
  have hWt : Path a' W (1 / (t₀ : ℝ)) := by
    let km := t₀ - 1
    have hkm : km ≤ n := by omega
    let u0 (j : ℕ) := if j < km then cs j * ρ else cs j
    have hlprod (l : List ℕ) (h : ∀ j ∈ l, Path a' (ww j) (u0 j)) :
        Path a' ((l.map ww).prod) ((l.map u0).sum) := by
      induction l with
      | nil => simpa [Pi.one_def] using Path.diag (a := a') 1
      | cons j l ih => simpa using (h j (by simp)).mul (ih fun m hm => h m (by simp [hm]))
    have hp'' := hlprod (List.range n) fun j hj => by
      have hj' := List.mem_range.mp hj
      dsimp [u0]; split_ifs
      · exact hnorm'.scale (cs j) (hcs j hj')
      · simpa using hnorm.scale (cs j) (hcs j hj')
    have hs : ((List.range n).map u0).sum = 1 / (t₀ : ℝ) := by
      change ∑ j ∈ Finset.range n, u0 j = _
      rw [← Finset.sum_range_add_sum_Ico u0 hkm]
      have h1 : ∑ j ∈ Finset.range km, u0 j = ∑ j ∈ Finset.range km, (v' j - v' (j + 1)) / (1 - ρ) * ρ :=
        Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
      have h2 : ∑ j ∈ Finset.Ico km n, u0 j = ∑ j ∈ Finset.Ico km n, (v' j - v' (j + 1)) / (1 - ρ) :=
        Finset.sum_congr rfl fun j hj => ite_eq_right (not_lt_of_ge (Finset.mem_Ico.mp hj).1)
      rw [h1, h2, ← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_div,
        Finset.sum_Ico_eq_sub _ hkm, Finset.sum_range_sub', Finset.sum_range_sub']
      have hv0 : v' 0 = 1 := by simp [v', n]
      have hvn : v' n = ρ := by simp [v']
      have hvk : v' km = 1 / (t₀ : ℝ) := by
        dsimp [v']; rw [ite_eq_left (show km < n by omega), show km + 1 = t₀ by omega]
      rw [hv0, hvn, hvk]
      field_simp [show 1 - ρ ≠ 0 by linarith]
      ring
    rwa [hs] at hp''
  have hexp {w r} (h : Path a' w r) : ColumnPath a' (fun i => Ψ (w i)) r := by
    induction h with
    | diag g => exact .common (Ψ g)
    | copy b hb => simpa [Pi.mul_def, hgen] using ((ColumnPath.common p).mul (.copy b hb)).mul (.common p)
    | mul _ _ ihu ihv => simpa only [Pi.mul_def, map_mul] using ihu.mul ihv
  let u' (j : β) : ℝ := if line.idxFun j = none then 1 / (t₀ : ℝ) else 0
  have hfl (l : List β) : ColumnPath a' (fun i => (l.map fun j => Ψ (W (line i j))).prod) ((l.map u').sum) := by
    induction l with
    | nil => exact .common 1
    | cons j l ih =>
      have hj : ColumnPath a' (fun i => Ψ (W (line i j))) (u' j) := by
        cases he : line.idxFun j with
        | none => simpa [u', he, Combinatorics.Line.coe_apply] using hexp hWt
        | some i => simpa [u', he, Combinatorics.Line.coe_apply] using ColumnPath.common (a := a') (Ψ (W i))
      simpa [Pi.mul_def] using hj.mul ih
  have hfull : ColumnPath a' (fun i => (L₀.map fun j => Ψ (W (line i j))).prod) 1 := by
    convert hfl L₀ using 1
    have hw : (L₀.map u').sum = ∑ j ∈ S, 1 / (t₀ : ℝ) := by simp [L₀, u', ← Finset.sum_filter, S]
    rw [hw, Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel (Nat.cast_ne_zero.mpr (by omega))]
  obtain ⟨xs, hxs, hbk⟩ := hfull (fun _ => {x : Strings | coloring x = k}) fun i => by
    have hk := (exists_ultra_color coloring ((L₀.map fun j => Ψ (W (line i j))).prod)).choose_spec
    dsimp only at hline
    rwa [hline i] at hk
  let b (i : Fin s) := FiniteEuclidean.flatten (xs i).toList
  have hb (i j : Fin s) : ‖b i - b j‖ = ‖a' i - a' j‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [hxs.2 i j, one_mul])
  have hcolor : ∀ᶠ n in (U : Filter ℕ), ∀ i, c n (trunc (n + 1) (b i)) = k :=
    eventually_all.mpr fun i => (hbk i : c' (b i) = k) ▸ (exists_ultra_color _ U).choose_spec
  have he : ∀ᶠ n in (U : Filter ℕ), ∀ i, FiniteEuclidean.embed (n + 1) (trunc (n + 1) (b i)) = b i :=
    eventually_all.mpr fun i => (Ultrafilter.of_le atTop) <| by
      filter_upwards [eventually_ge_atTop ((FiniteEuclidean.coords (b i)).support.sup id)] with n hd
      refine Finsupp.ext fun m => ?_
      change FiniteEuclidean.coords (FiniteEuclidean.embed (n + 1) (trunc (n + 1) (b i))) m =
        FiniteEuclidean.coords (b i) m
      by_cases hm : m < n + 1
      · exact Finsupp.mapDomain_apply_of_injective Fin.val_injective _ ⟨m, hm⟩
      · refine Eq.trans (by apply Finsupp.mapDomain_of_notMem_range; rintro ⟨j, rfl⟩; exact hm j.isLt)
          (Finsupp.notMem_support_iff.mp fun hms => hm (Nat.lt_succ_of_le ((Finset.le_sup (f := id) hms).trans hd))).symm
  obtain ⟨n', hn'', hcol⟩ := (he.and hcolor).exists
  exact hc n' ⟨fun i => trunc (n' + 1) (b i),
    fun i j => by rw [dist_eq_norm, dist_eq_norm, ← (FiniteEuclidean.embed (n' + 1)).norm_map,
      map_sub, hn'' i, hn'' j, hb, ← map_sub, LinearIsometry.norm_map], k, hcol⟩

end
end OAI.EuclideanRamsey
