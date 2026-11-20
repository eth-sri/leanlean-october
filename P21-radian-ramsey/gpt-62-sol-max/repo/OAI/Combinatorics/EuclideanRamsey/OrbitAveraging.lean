/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.DerivedFractions
public import OAI.Combinatorics.EuclideanRamsey.PathSynchronization

@[expose] public section

open Finset
open scoped commutatorElement
namespace OAI.EuclideanRamsey
noncomputable section
variable {G H ι : Type*} [Group G] [Group H]

namespace NormalBound

def subgroup (N : Subgroup G) [N.Normal] : NormalBound G where
  Holds _ g := g ∈ N
  one := N.one_mem
  weaken h _ := h
  mul := N.mul_mem
  inv := N.inv_mem
  conj h g := Subgroup.Normal.conj_mem inferInstance _ h g

lemma product_difference {α : Type*} (c : NormalBound G)
    (l : List α) (a b : α → G) (B : ℝ)
    (h : ∀ j ∈ l, c.Holds B (a j*(b j)⁻¹)) : c.Holds (l.length*B) ((l.map a).prod*((l.map b).prod)⁻¹) := by
  induction l with
  | nil => simpa using c.one
  | cons j l ih =>
    have hx := ih (fun k hk => h k (by simp [hk]))
    simp only [List.length_cons,Nat.cast_succ,add_mul,one_mul,List.map_cons,List.prod_cons]
    rw [add_comm]
    convert c.mul (h j (by simp)) (c.conj hx (b j)) using 1
    group
end NormalBound

abbrev Words (H ι G : Type*) := H → ι → G

variable [Fintype H]

def groupList (H : Type*) [Fintype H] : List H := (univ : Finset H).toList

private lemma groupList_perm (h : H) : ((groupList H).map (·*h)).Perm (groupList H) := by
  classical
  apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map (mul_left_injective h))
    (Finset.nodup_toList _)).mpr
  intro g
  simpa using (Equiv.mulRight h).surjective g

def average (w : Words H ι G) (a : G) : Words H ι G := fun h i => ((groupList H).map (fun g => w (g*h) i*a)).prod

def OrbitBound (c : NormalBound G) (w : Words H ι G) (b : ℝ) (i : ι) : Prop :=
  ∀ h k, c.Holds b (w h i * (w k i)⁻¹)

abbrev OrbitIn (N : Subgroup G) [N.Normal] := OrbitBound (H:=H) (ι:=ι) (NormalBound.subgroup N)

namespace OrbitBound
variable {c : NormalBound G} {w : Words H ι G} {b : ℝ} {i : ι}
lemma avg (hw : OrbitBound c w b i) (a : G) : OrbitBound c (average w a) (Fintype.card H*b) i := by
  intro h k
  simpa [average,groupList] using c.product_difference (groupList H)
    (fun g => w (g*h) i*a) (fun g => w (g*k) i*a) b (fun g _ => by simpa using hw (g*h) (g*k))
end OrbitBound

private lemma raise {N : Subgroup G} [N.Normal] {w : Words H ι G} {i : ι}
    (hw : OrbitIn N w 0 i) : OrbitIn ⁅N,N⁆ (average w (w 1 i)⁻¹) 0 i := by
  let q := QuotientGroup.mk' ⁅N,N⁆
  let a (g : H) := w g i * (w 1 i)⁻¹
  have hc (g k : H) : Commute (q (a g)) (q (a k)) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.commutator_mem_commutator (hw g 1) (hw k 1))
  intro h k
  rw [← div_eq_mul_inv]
  apply QuotientGroup.eq_iff_div_mem.mp
  change q (average w _ h i) = q (average w _ k i)
  have hp := ((groupList_perm h).trans (groupList_perm k).symm).map (q ∘ a)
  simpa only [average,a,map_list_prod,List.map_map,Function.comp_def] using
    hp.prod_eq' (List.pairwise_map.mpr (List.pairwise_of_forall (fun g j => hc g j)))

private lemma contraction_bound (c : NormalBound G)
    (w : Words H ι G) (a : G) (i : ι) (h : H) (B : ℝ) (hw : ∀ g, c.Holds B (w g i*a)) :
    c.Holds ((Fintype.card H-1:ℝ)*B) (average w a h i * (w 1 i*a)⁻¹) := by
  obtain ⟨l,r,he⟩ := List.append_of_mem (show h⁻¹ ∈ groupList H by simp [groupList])
  have hp (L : List H) : c.Holds ((L.length:ℝ)*B) ((L.map (fun g => w (g*h) i*a)).prod) := by
    simpa using c.product_difference L (fun g => w (g*h) i*a) (fun _ => 1)
      B (fun g _ => by simpa using hw (g*h))
  have hl := congrArg (fun l : List H => (l.length:ℝ)) he
  simp [groupList] at hl
  rw [show (Fintype.card H:ℝ)-1 = (l.length:ℝ)+(r.length:ℝ) by linarith,add_mul]
  convert c.mul (hp l) (c.conj (hp r) (w 1 i*a)) using 1
  simp [average,he,mul_assoc]

/-- Reachability under appending a common word and multiplying all the translates. -/
inductive Evolution (w : Words H ι G) (m : ℝ) : Words H ι G → ℝ → Prop
  | refl : Evolution w m w m
  | avg {v n} : Evolution w m v n → (a : G) → Evolution w m (average v a) (Fintype.card H*n)

namespace Evolution
variable {w v u : Words H ι G} {m n k : ℝ}
lemma trans (h : Evolution w m v n) (h' : Evolution v n u k) : Evolution w m u k := by
  induction h' with
  | refl => exact h
  | avg _ a ih => exact ih.avg a

lemma positive (h : Evolution w m v n) (hm : 0 < m) : 0 < n := by
  induction h with
  | refl => exact hm
  | avg _ _ ih => exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) ih

lemma bound (h : Evolution w m v n) {c : NormalBound G} {δ : ℝ} {i : ι}
    (hw : OrbitBound c w (δ*m) i) : OrbitBound c v (δ*n) i := by
  induction h with
  | refl => exact hw
  | avg _ a ih => simpa only [mul_left_comm] using ih.avg a
lemma mem (h : Evolution w m v n) {N : Subgroup G} [N.Normal] {i : ι}
    (hw : OrbitIn N w 0 i) : OrbitIn N v 0 i := by
  exact h.bound (c:=NormalBound.subgroup N) (δ:=0) hw
end Evolution

omit [Group G] in
lemma Evolution.path {a : ι → Hilbert} {w v : Words H ι LetterGroup} {m n : ℝ}
    (h : Evolution w m v n) (f : ι → H) (q : ℝ)
    (hw : ∀ g : H, Path a (fun i => w (g*f i) i) (q*m)) (g : H) :
    Path a (fun i => v (g*f i) i) (q*n) := by
  revert g
  induction h with
  | refl => exact hw
  | @avg v n _ k ih =>
    intro g
    simpa [average,groupList,mul_assoc,List.map_const',mul_left_comm] using
      Path.list_prod (groupList H) (fun j i => v ((j*g)*f i) i*k) (fun _ => q*n)
        (fun j _ => (ih (j*g)).mul_diag k)

private lemma raise_to (N : Subgroup G) [N.Normal] (r : ℕ)
    (w : Words H ι G) (m : ℝ) (i : ι) (hw : OrbitIn N w 0 i) :
    ∃ v n, Evolution w m v n ∧ OrbitIn (Derived N r) v 0 i := by
  induction r with
  | zero => exact ⟨w,m,.refl,hw⟩
  | succ r ih =>
    obtain ⟨v,n,hv,hm⟩ := ih
    exact ⟨_,_,hv.avg _,raise hm⟩

private lemma make_small (L : Subgroup G) [L.Normal] (c : NormalBound G)
    (cover : ∀ x ∈ L, ∃ B, c.Holds B x)
    (w : Words H ι G) (m : ℝ) (hm : 0 < m) (i : ι)
    (hw : OrbitIn L w 0 i) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v n, Evolution w m v n ∧ OrbitBound c v (δ*n) i := by
  classical
  choose b hb using fun g => cover _ (hw g 1)
  let B := max (⨆ g, b g) 1
  have hB : 0 < B := lt_max_of_lt_right zero_lt_one
  have hb' (g : H) : c.Holds B (w g i * (w 1 i)⁻¹) :=
    c.weaken (hb g) ((le_ciSup (Set.finite_range b).bddAbove g).trans (le_max_left ..))
  let h : ℝ := Fintype.card H
  have hh : 0 < h := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ*m/(2*B) by positivity)
    (show (h-1)/h < 1 by rw [div_lt_one hh]; linarith)
  rw [div_pow,div_lt_div_iff₀ (by positivity) (by positivity)] at hk
  have step (j : ℕ) : ∃ v a, Evolution w m v (h^j*m) ∧ ∀ g, c.Holds (B*(h-1)^j) (v g i*a) := by
    induction j with
    | zero => exact ⟨w,_,by simpa using (Evolution.refl (w:=w) (m:=m)),by simpa using hb'⟩
    | succ j ih =>
      obtain ⟨v,a,hv,hvb⟩ := ih
      refine ⟨average v a,(v 1 i*a)⁻¹,?_,fun g => ?_⟩
      · simpa [h,pow_succ,mul_left_comm,mul_comm] using hv.avg a
      · convert contraction_bound c v a i g _ hvb using 1; ring
  obtain ⟨v,a,hv,hvb⟩ := step k
  exact ⟨v,_,hv,fun g j => by
    simpa using
      c.weaken (c.mul (hvb g) (c.inv (hvb j))) (show _ ≤ δ*(h^k*m) by bound)⟩

theorem averaging [Fintype ι] (N : Subgroup G) [N.Normal] (r : ℕ)
    (c : ι → NormalBound G) (cover : ∀ i x, x ∈ Derived N r → ∃ B, (c i).Holds B x) (letter : Words H ι G)
    (hletter : ∀ i h k, letter h i * (letter k i)⁻¹ ∈ N) (δ : ℝ) (hδ : 0 < δ) :
    ∃ w m, Evolution letter 1 w m ∧ 0 < m ∧ ∀ i, OrbitBound (c i) w (δ*m) i := by
  let P (p : Words H ι G × ℝ) := Evolution letter 1 p.1 p.2
  let C (i : ι) (p : Words H ι G × ℝ) := OrbitBound (c i) p.1 (δ*p.2) i
  obtain ⟨⟨w,m⟩,hw,hwb⟩ := collect_conditions univ (P:=P) (C:=C) ⟨(letter,1),.refl⟩
    (fun i _ p he => by
      rcases p with ⟨v,n⟩
      change Evolution letter 1 v n at he
      obtain ⟨u,k,hu,hu'⟩ := raise_to N r _ _ i (he.mem (hletter i))
      obtain ⟨z,l,hz,hzb⟩ := make_small _ (c i) (cover i) _ _ ((he.trans hu).positive zero_lt_one) i hu' δ hδ
      exact ⟨(z,l),he.trans (hu.trans hz),hzb,fun _ => (hu.trans hz).bound⟩)
  exact ⟨w,m,hw,hw.positive zero_lt_one,fun i => hwb i (mem_univ i)⟩

end
end OAI.EuclideanRamsey
