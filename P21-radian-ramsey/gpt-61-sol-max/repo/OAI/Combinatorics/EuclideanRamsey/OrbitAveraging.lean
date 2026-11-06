/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.NormalCost

@[expose] public section

namespace OAI.EuclideanRamsey







variable {G : Type*} {H : Type*} {X : Type*} [Group G] [Group H] [MulAction H X]

inductive OrbitWords (letter : X → G) : (X → G) → ℕ → Prop
  | diag (g : G) : OrbitWords letter (fun _ => g) 0
  | point (h : H) : OrbitWords letter (fun x => letter (h•x)) 1
  | mul {u v m n} : OrbitWords letter u m → OrbitWords letter v n → OrbitWords letter (u*v) (m+n)
namespace OrbitWords
variable {letter : X → G} {w : X → G} {m : ℕ}
lemma reindex (hw : OrbitWords (H:=H) letter w m) (g : H) :
    OrbitWords (H:=H) letter (fun x => w (g•x)) m := by
  induction hw with
  | diag a => exact .diag a
  | point h => simpa [mul_smul] using (point (letter:=letter) (h*g))
  | mul _ _ ihu ihv => exact .mul ihu ihv
end OrbitWords

def OrbitIn (N : Subgroup G) (w : X → G) (x : X) : Prop :=
  ∀ y z,y ∈ MulAction.orbit H x → z ∈ MulAction.orbit H x → w y*(w z)⁻¹∈N

def OrbitBound {L : Subgroup G} (c : NormalCost L) (w : X → G) (b : ℝ) (x : X) : Prop :=
  ∀ y z,y ∈ MulAction.orbit H x → z ∈ MulAction.orbit H x →
    w y*(w z)⁻¹∈L ∧ c.cost (w y*(w z)⁻¹)≤b

lemma orbitIn_normalize {N : Subgroup G} {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) (a : G) : OrbitIn (H:=H) N (fun y => w y*a) x := by
  intro y z hy hz
  aesop

lemma orbitIn_average [Fintype H] {N : Subgroup G} [N.Normal] {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) : OrbitIn (H:=H) N (orbitAverage (H:=H) w) x := by
  intro y z hy hz
  rw [← div_eq_mul_inv]
  apply QuotientGroup.eq_iff_div_mem.mp
  change (QuotientGroup.mk' N) (orbitAverage (H:=H) w y) =
    (QuotientGroup.mk' N) (orbitAverage (H:=H) w z)
  simp only [orbitAverage, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa [div_eq_mul_inv] using hw _ _
    (MulAction.mem_orbit_trans (MulAction.mem_orbit y g) hy) (MulAction.mem_orbit_trans (MulAction.mem_orbit z g) hz)

lemma orbitBound_normalize {L : Subgroup G} {c : NormalCost L} {w : X → G} {b : ℝ} {x : X}
    (hw : OrbitBound (H:=H) c w b x) (a : G) :
    OrbitBound (H:=H) c (fun y => w y*a) b x := by
  intro y z hy hz
  simpa [mul_assoc] using hw y z hy hz

lemma orbitBound_average [Fintype H] {L : Subgroup G} [L.Normal] {c : NormalCost L}
    {w : X → G} {b : ℝ} {x : X} (hw : OrbitBound (H:=H) c w b x) :
    OrbitBound (H:=H) c (orbitAverage (H:=H) w) (Fintype.card H*b) x := by
  intro y z hy hz
  have hh g := hw (g•y) (g•z)
    (MulAction.mem_orbit_trans (MulAction.mem_orbit y g) hy)
    (MulAction.mem_orbit_trans (MulAction.mem_orbit z g) hz)
  simpa [orbitAverage,groupList] using c.product_difference (groupList H)
    (fun g => w (g•y)) (fun g => w (g•z)) b (fun g _ => hh g)

lemma contraction_bound [Fintype H] {L : Subgroup G} [L.Normal] (c : NormalCost L)
    (w : X → G) (x y : X) (hxy : y ∈ MulAction.orbit H x) (B : ℝ)
    (hw : ∀ z,z ∈ MulAction.orbit H x → w z∈L ∧ c.cost (w z)≤B) :
    orbitAverage (H:=H) w y*(w x)⁻¹∈L ∧
    c.cost (orbitAverage (H:=H) w y*(w x)⁻¹) ≤ (Fintype.card H-1:ℝ)*B := by
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_symm.mp hxy
  obtain ⟨p,q,he⟩ := List.mem_iff_append.mp (by classical simp [groupList] : g ∈ groupList H)
  let a := (p.map (fun h => w (h•y))).prod
  let b := (q.map (fun h => w (h•y))).prod
  have hbound (l : List H) : (l.map (fun h => w (h•y))).prod∈L ∧
      c.cost (l.map (fun h => w (h•y))).prod ≤ (l.length:ℝ)*B := by
    simpa using c.product_difference l (fun h => w (h•y)) (fun _ => 1) B
      (fun h _ => by simpa using hw _ (MulAction.mem_orbit_trans (MulAction.mem_orbit y h) hxy))
  have ha : a∈L := (hbound p).1
  have hb' : b∈L := (hbound q).1
  have hc : w x*b*(w x)⁻¹∈L := (inferInstance : L.Normal).conj_mem _ hb' _
  have hid : orbitAverage (H:=H) w y*(w x)⁻¹=a*(w x*b*(w x)⁻¹) := by
    simp [orbitAverage,he,hg,a,b,List.prod_append,mul_assoc]
  rw [hid]
  refine ⟨L.mul_mem ha hc,?_⟩
  have hn : (Fintype.card H:ℝ)=(p.length:ℝ)+1+(q.length:ℝ) := by
    have := congrArg List.length he
    simp [groupList] at this
    exact_mod_cast (by grind)
  calc
    _ ≤ c.cost a+c.cost b := by simpa [c.conj b hb'] using c.mul a ha _ hc
    _ ≤ _ := by rw [hn]; nlinarith [(hbound p).2, (hbound q).2]


variable [Fintype H]

inductive Evolution : (X → G) → ℕ → (X → G) → ℕ → Prop
  | refl (w m) : Evolution w m w m
  | normalize {w m v n} : Evolution w m v n → (a : G) →
      Evolution w m (fun x => v x*a) n
  | average {w m v n} : Evolution w m v n →
      Evolution w m (orbitAverage (H:=H) v) (Fintype.card H*n)
namespace Evolution
variable {w v u : X → G} {m n k : ℕ}
lemma trans (h : Evolution (H:=H) w m v n) (h' : Evolution (H:=H) v n u k) :
    Evolution (H:=H) w m u k := by
  induction h' <;> solve_by_elim [normalize, average]
lemma words {letter : X → G} (h : Evolution (H:=H) w m v n)
    (hw : OrbitWords (H:=H) letter w m) : OrbitWords (H:=H) letter v n := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => simpa [Pi.mul_def] using ih.mul (.diag a)
  | @average v n _ ih =>
      have aux (l : List H) : OrbitWords (H:=H) letter
          (fun x => (l.map (fun h => v (h•x))).prod) (l.length*n) := by
        induction l with
        | nil => simpa using (OrbitWords.diag (letter:=letter) (H:=H) 1)
        | cons h l ihList => simpa [Nat.add_mul,add_comm,Pi.mul_def] using (ih.reindex h).mul ihList
      change OrbitWords letter (fun x => ((groupList H).map (fun h => v (h•x))).prod) _
      simpa [groupList] using aux (groupList H)
lemma positive (h : Evolution (H:=H) w m v n) (hm : 0 < m) : 0 < n := by
  induction h <;> positivity
lemma orbitIn (h : Evolution (H:=H) w m v n) {N : Subgroup G} [N.Normal] {x : X}
    (hw : OrbitIn (H:=H) N w x) : OrbitIn (H:=H) N v x := by
  induction h <;> solve_by_elim [orbitIn_normalize, orbitIn_average]
lemma orbitBound (h : Evolution (H:=H) w m v n) {L : Subgroup G} [L.Normal]
    {c : NormalCost L} {δ : ℝ} {x : X} (hw : OrbitBound (H:=H) c w (δ*m) x) :
    OrbitBound (H:=H) c v (δ*n) x := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => exact orbitBound_normalize ih a
  | average _ ih =>
    simpa [mul_left_comm] using orbitBound_average ih
end Evolution

lemma evolve_finite [Fintype X] (w : X → G) (m : ℕ)
    (Good : X → (X → G) → ℕ → Prop)
    (preserve : ∀ {v n u k},Evolution (H:=H) v n u k → ∀ x,Good x v n → Good x u k)
    (improve : ∀ {v n},Evolution (H:=H) w m v n → ∀ x,
      ∃ u k,Evolution (H:=H) v n u k ∧ Good x u k) :
    ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x,Good x v n := by
  classical
  have aux (t : Finset X) : ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x∈t,Good x v n := by
    induction t using Finset.induction_on with
    | empty => exact ⟨w,m,.refl _ _,by simp⟩
    | @insert x t hx ih =>
      obtain ⟨v,n,hev,hv⟩ := ih
      obtain ⟨u,k,heu,hu⟩ := improve hev x
      refine ⟨u,k,hev.trans heu,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hu
      · exact preserve heu y (hv y hy)
  simpa using aux Finset.univ

variable [Fintype X]

theorem finite_group_averaging (N : Subgroup G) [N.Normal] (r : ℕ)
    (c : NormalCost (Derived N r)) (letter : X → G)
    (hletter : ∀ x y,letter x*(letter y)⁻¹∈N) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : X → G) (m : ℕ),OrbitWords (H:=H) letter w m ∧ 0 < m ∧
      ∀ x y,y ∈ MulAction.orbit H x →
        w x*(w y)⁻¹∈Derived N r ∧ c.cost (w x*(w y)⁻¹)≤δ*m := by
  have hstart : OrbitWords (H:=H) letter letter 1 := by
    simpa using (OrbitWords.point (letter:=letter) (1:H))
  obtain ⟨v,n,hev,hv⟩ : ∃ v n,Evolution (H:=H) letter 1 v n ∧
      ∀ x,OrbitIn (H:=H) (Derived N r) v x := by
    apply evolve_finite letter 1 (fun x v _ => OrbitIn (H:=H) (Derived N r) v x)
    · intro v n u k he x hx
      exact he.orbitIn hx
    · intro v n he x
      have hw : OrbitIn (H:=H) N v x := he.orbitIn (fun _ _ _ _ => hletter _ _)
      clear c
      induction r with
      | zero => exact ⟨v,n,.refl _ _,hw⟩
      | succ r ih =>
        obtain ⟨v,n,hev,hv⟩ := ih
        refine ⟨_,_,(hev.normalize (v x)⁻¹).average,?_⟩
        intro y z hy hz
        let N' := Derived N r
        let w' := fun y => v y*(v x)⁻¹
        have hmem g : w' (g•y)∈N' :=
          hv _ _ (MulAction.mem_orbit_trans (MulAction.mem_orbit y g) hy) (MulAction.mem_orbit_self x)
        obtain ⟨h,rfl⟩ := MulAction.mem_orbit_trans hz (MulAction.mem_orbit_symm.mp hy)
        let q := QuotientGroup.mk' ⁅N',N'⁆
        rw [← div_eq_mul_inv]
        apply QuotientGroup.eq_iff_div_mem.mp
        change q (orbitAverage (H:=H) w' y) = q (orbitAverage (H:=H) w' (h•y))
        simp [orbitAverage, map_list_prod]
        have hp := (groupList_mul_perm h).map (fun g => q (w' (g•y)))
        simp [Function.comp_def, mul_smul] at hp
        symm
        apply hp.prod_eq'
        apply List.pairwise_map.mpr
        apply List.pairwise_of_forall
        intro g k
        apply commutatorElement_eq_one_iff_commute.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr
          (Subgroup.commutator_mem_commutator (by simpa [mul_smul] using hmem (g*h))
            (by simpa [mul_smul] using hmem (k*h)))
  have hn  := hev.positive Nat.zero_lt_one
  obtain ⟨w,m,hew,hw⟩ := evolve_finite v n (fun x w m => OrbitBound (H:=H) c w (δ*m) x)
    (by intro _ _ _ _ he x hx; exact he.orbitBound hx)
    (by
      intro u m₀ he x
      classical
      let L := Derived N r
      have hlocal := he.orbitIn (hv x)
      have hpositive := he.positive hn
      let w₀  := fun y => u y*(u x)⁻¹
      let B  := ∑ y,c.cost (w₀ y)
      have hB : 0≤B := Finset.sum_nonneg (fun y _ => c.nonneg _)
      have hbound y (hy : y ∈ MulAction.orbit H x) :
          w₀ y∈L ∧ c.cost (w₀ y)≤B :=
        ⟨hlocal y x hy (MulAction.mem_orbit_self x),
          Finset.single_le_sum (fun z _ => c.nonneg _) (Finset.mem_univ y)⟩
      have hH : (0:ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
      have hden : 0 < 2*B+1 := by positivity
      obtain ⟨k,hkraw⟩ := exists_pow_lt_of_lt_one
        (show 0 < δ*m₀/(2*B+1) by positivity)
        (show (Fintype.card H-1:ℝ)/Fintype.card H < 1 by rw [div_lt_one hH]; linarith)
      have hk : 2*(B*(Fintype.card H-1:ℝ)^k) ≤ δ*((Fintype.card H^k*m₀:ℕ):ℝ) := by
        rw [div_pow, div_lt_div_iff₀ (pow_pos hH _) hden] at hkraw
        push_cast
        nlinarith [pow_nonneg (sub_nonneg.mpr (show (1:ℝ) ≤ Fintype.card H by
          exact_mod_cast (Nat.succ_le_of_lt Fintype.card_pos))) k]
      obtain ⟨v,hev,hv⟩ : ∃ v,Evolution (H:=H) w₀ m₀ v ((Fintype.card H)^k*m₀) ∧
          ∀ y,y ∈ MulAction.orbit H x → v y∈L ∧ c.cost (v y)≤B*(Fintype.card H-1:ℝ)^k := by
        clear hk hkraw
        induction k with
        | zero => exact ⟨w₀,by simpa using (Evolution.refl (H:=H) w₀ m₀),by simpa using hbound⟩
        | succ k ih =>
          obtain ⟨v,hev,hv⟩ := ih
          refine ⟨fun y => orbitAverage (H:=H) v y*(v x)⁻¹,?_,?_⟩
          · convert hev.average.normalize (v x)⁻¹ using 1 ; group
          · intro y hy
            simpa [pow_succ,mul_comm,mul_left_comm,mul_assoc] using contraction_bound c v x y hy _ hv
      refine ⟨v,(Fintype.card H)^k*m₀,(Evolution.normalize (.refl u m₀) (u x)⁻¹).trans hev,?_⟩
      intro y z hy hz
      refine ⟨L.mul_mem (hv y hy).1 (L.inv_mem (hv z hz).1),?_⟩
      have hcm := c.mul (v y) (hv y hy).1 (v z)⁻¹ (L.inv_mem (hv z hz).1)
      rw [c.inv _ (hv z hz).1] at hcm
      exact hcm.trans ((add_le_add (hv y hy).2 (hv z hz).2).trans (by linarith)))
  refine ⟨w,m,hew.words (hev.words hstart),hew.positive hn,?_⟩
  intro x y hxy
  exact hw x x y (MulAction.mem_orbit_self x) hxy
end OAI.EuclideanRamsey
