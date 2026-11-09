module

public import ADR11.Trees.Classify

@[expose] public section

namespace ADR11

open Finset

theorem kingmanTransition_eq_sum_range {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : IsForest F) (hk : 1 ≤ #(roots F)) (t : ℝ)
    (G : Finset (Finset L)) :
    kingmanTransition t F G =
      ∑ j ∈ range #(roots F), deathProb #(roots F) (#(roots F) - j) t * (jumpMatrix ^ j) F G := by
  rw [kingmanTransition_apply hF]
  have hsupp (j) (h : (jumpMatrix ^ j) F G ≠ 0) := (jumpMatrix_pow_support hF h).2.2.2
  have hzero (j) (hj : j ∈ range #(roots F)) (hne : #(roots F) - j ≠ #(roots G)) :
      (jumpMatrix ^ j) F G = 0 := by_contra fun h => hne <| by
    have := hsupp j h; rwa [ite_eq_left (mem_range.1 hj), eq_comm] at this
  by_cases hr : 1 ≤ #(roots G) ∧ #(roots G) ≤ #(roots F)
  · rw [Finset.sum_eq_single (#(roots F) - #(roots G))]
    · congr 2; omega
    · exact fun j hj hne => by rw [hzero j hj (by omega), mul_zero]
    · exact fun h => absurd (mem_range.2 (by omega)) h
  · rw [Finset.sum_eq_zero fun j hj => by
      rw [hzero j hj (by have := mem_range.1 hj; omega), mul_zero]]
    by_cases hgt : #(roots F) < #(roots G)
    · rw [deathProb_eq_zero_of_lt hgt, zero_mul]
    · have : (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0 :=
        by_contra fun h => by have := hsupp _ h; split_ifs at this <;> omega
      rw [this, mul_zero]

def gPoly : ℕ → ℕ → List (ℚ × ℕ)
  | 1, 1 => [(1, 0)]
  | 2, 1 => [(1, 0), (-1, 1)]
  | 2, 2 => [(1, 1)]
  | 3, 1 => [(1, 0), (-3/2, 1), (1/2, 3)]
  | 3, 2 => [(3/2, 1), (-3/2, 3)]
  | 3, 3 => [(1, 3)]
  | 4, 1 => [(1, 0), (-9/5, 1), (1, 3), (-1/5, 6)]
  | 4, 2 => [(9/5, 1), (-3, 3), (6/5, 6)]
  | 4, 3 => [(2, 3), (-2, 6)]
  | 4, 4 => [(1, 6)]
  | _, _ => []

theorem deathProb_eq_gPoly {k j : ℕ} (hk2 : 2 ≤ k) (hk4 : k ≤ 4) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (t : ℝ) :
    deathProb k j t = ((gPoly k j).map fun ce => (ce.1 : ℝ) * Real.exp (-t) ^ ce.2).sum := by
  have hpow (m : ℕ) : ∀ {k : ℕ}, 1 ≤ k → k ≤ 4 →
      deathPow m k j = ((gPoly k j).map fun ce => (ce.1 : ℝ) * (-(ce.2 : ℝ)) ^ m).sum := by
    have hj4 : j ≤ 4 := le_trans hjk hk4
    induction m with
    | zero => intro k hk1 hk4; interval_cases k <;> interval_cases j <;> simp [deathPow, gPoly] <;> norm_num
    | succ m ih =>
      intro k hk1 hk4; rw [deathPow_succ]
      rcases eq_or_lt_of_le hk1 with rfl | hk2
      · interval_cases j <;> simp [gPoly, pow_succ]
      · rw [ih (by omega) (by omega), ih hk1 hk4]
        interval_cases k <;> interval_cases j <;>
          simp only [gPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_succ,
            Nat.choose] <;> push_cast <;> ring
  have hsum (L : List (ℚ × ℕ)) : HasSum
      (fun m : ℕ => (L.map fun ce => t ^ m / (m.factorial : ℝ) * ((ce.1 : ℝ) * (-(ce.2 : ℝ)) ^ m)).sum)
      ((L.map fun ce => (ce.1 : ℝ) * Real.exp (-t) ^ ce.2).sum) := by
    induction L with
    | nil => simp
    | cons ce L ih =>
      simp only [List.map_cons, List.sum_cons]
      refine (?_ : HasSum _ _).add ih
      rw [← Real.exp_nat_mul, show (ce.2 : ℝ) * -t = -(ce.2 : ℝ) * t by ring]
      convert (fact_hasSum_exp_mul (-(ce.2 : ℝ)) t).mul_left (ce.1 : ℝ) using 1
      ext m; ring
  unfold deathProb
  rw [← (hsum (gPoly k j)).tsum_eq]
  exact tsum_congr fun m => by
    rw [hpow m (by omega) hk4, ← List.sum_map_mul_left]

structure CTerm where
  coef : ℚ
  key : List (ℕ × ℕ)
  forest : List ℕ

noncomputable def monoVal {n : ℕ} (len : Finset (Fin n) → ℝ) (k : List (ℕ × ℕ)) : ℝ :=
  (k.map fun ae => Real.exp (-len (decC n ae.1)) ^ ae.2).prod

noncomputable def CTerm.val {n : ℕ} (len : Finset (Fin n) → ℝ) (τ : CTerm) : ℝ :=
  τ.coef * monoVal len τ.key

@[simp] theorem monoVal_nil {n : ℕ} (len : Finset (Fin n) → ℝ) : monoVal len [] = 1 := rfl

@[simp] theorem monoVal_cons {n : ℕ} (len : Finset (Fin n) → ℝ) (ae : ℕ × ℕ)
    (k : List (ℕ × ℕ)) :
    monoVal len (ae :: k) = Real.exp (-len (decC n ae.1)) ^ ae.2 * monoVal len k := by
  simp [monoVal]

theorem monoVal_append {n : ℕ} (len : Finset (Fin n) → ℝ) (k₁ k₂ : List (ℕ × ℕ)) :
    monoVal len (k₁ ++ k₂) = monoVal len k₁ * monoVal len k₂ := by
  simp [monoVal, List.prod_append]

def kernelAux (a k : ℕ) (τ : CTerm) : List CTerm :=
  (List.range k).flatMap fun j => (gPoly k (k - j)).flatMap fun ce =>
    (jumpL j τ.forest).map fun q => ⟨τ.coef * ce.1 * q.1, τ.key ++ [(a, ce.2)], q.2⟩

def kernelK (a k : ℕ) (τ : CTerm) : Option (List CTerm) :=
  if k ≤ 1 then some [τ]
  else if k ≤ 4 then some (kernelAux a k τ) else none

def kernelL (n a : ℕ) (τ : CTerm) : Option (List CTerm) :=
  if checkF n τ.forest then kernelK a (rootsL τ.forest).length τ else none

theorem kernelL_spec {n a : ℕ} (len : Finset (Fin n) → ℝ) {τ : CTerm} {K : List CTerm}
    (h : kernelL n a τ = some K) (G : Finset (Finset (Fin n))) :
    τ.val len * kingmanTransition (len (decC n a)) (decF n τ.forest) G =
      (K.map fun τ' => if decF n τ'.forest = G then τ'.val len else 0).sum := by
  unfold kernelL at h
  split_ifs at h with hc
  obtain ⟨hv, hnd, hF⟩ := of_checkF hc
  have hk := card_roots_decF hv hnd
  unfold kernelK at h
  split_ifs at h with h1 h4
  · cases h
    rw [kingmanTransition_of_card_roots_le_one hF (by omega)]
    simp [eq_comm]
  · cases h
    rw [kingmanTransition_eq_sum_range hF (by omega), hk, sum_range_eq_list,
      ← List.sum_map_mul_left, kernelAux, sum_map_flatMap]
    congr 1; refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    rw [sum_map_flatMap, deathProb_eq_gPoly (by omega) h4 (by omega) (by omega),
      jumpMatrix_pow_decF j _ hv hnd hF G, sum_mul_sum_list, ← List.sum_map_mul_left]
    congr 1; refine List.map_congr_left fun ce _ => ?_
    rw [← List.sum_map_mul_left, List.map_map]
    congr 1; refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply, CTerm.val, monoVal_append, monoVal_cons, monoVal_nil]
    split_ifs <;> push_cast <;> ring

noncomputable def iterSum {ι β : Type*} [Fintype β] [DecidableEq β] (μ : ι → Finset β → ℝ) :
    List ι → Finset β → (Finset β → ℝ) → ℝ
  | [], S, φ => φ S
  | B :: l, S, φ => ∑ F, μ B F * iterSum μ l (F ∪ S) φ

def piInsertEquiv {ι γ : Type*} [DecidableEq ι] {B : ι} {C : Finset ι} (hB : B ∉ C) :
    (↥(insert B C) → γ) ≃ γ × (↥C → γ) where
  toFun f := (f ⟨B, mem_insert_self B C⟩, fun i => f ⟨i.1, mem_insert_of_mem i.2⟩)
  invFun p i := if h : i.1 = B then p.1 else p.2 ⟨i.1, (mem_insert.1 i.2).resolve_left h⟩
  left_inv f := funext fun i => by
    by_cases h : i.1 = B <;> simp [h]; exact congrArg f (Subtype.ext h.symm)
  right_inv := fun ⟨_, _⟩ => Prod.ext (by simp)
    (funext fun i => by simp [show i.1 ≠ B from fun h => hB (h ▸ i.2)])

theorem sum_pi_eq_iterSum {ι β : Type*} [DecidableEq ι] [Fintype β] [DecidableEq β]
    (μ : ι → Finset β → ℝ) (φ : Finset β → ℝ) : ∀ (l : List ι), l.Nodup →
    ∀ (C : Finset ι), C = l.toFinset → ∀ S : Finset β,
    ∑ f : ↥C → Finset β, (∏ B : ↥C, μ B (f B)) * φ (univ.sup f ∪ S) = iterSum μ l S φ
  | [], _, C, hC, S => by rw [List.toFinset_nil] at hC; subst hC; rw [iterSum, Fintype.sum_unique]; simp
  | B :: l, hnd, C, hC, S => by
    rw [List.toFinset_cons] at hC; subst hC
    rw [List.nodup_cons] at hnd
    have hB : B ∉ l.toFinset := by simpa using hnd.1
    rw [iterSum, Fintype.sum_equiv (piInsertEquiv hB) _
      (fun p => μ B p.1 * ((∏ i : ↥l.toFinset, μ i (p.2 i)) * φ (univ.sup p.2 ∪ (p.1 ∪ S))))]
    · rw [Fintype.sum_prod_type]
      congr 1; ext x; dsimp only
      rw [← Finset.mul_sum, sum_pi_eq_iterSum μ φ l hnd.2 _ rfl (x ∪ S)]
    · intro f
      have hsup : univ.sup f = f ⟨B, mem_insert_self B l.toFinset⟩ ∪
          univ.sup fun i : ↥l.toFinset => f ⟨i.1, mem_insert_of_mem i.2⟩ := by
        rw [Finset.univ_eq_attach, Finset.attach_insert, Finset.sup_insert, Finset.sup_image,
          ← Finset.univ_eq_attach]; rfl
      have hprod : ∏ i : ↥(insert B l.toFinset), μ i (f i) =
          μ B (f ⟨B, mem_insert_self B l.toFinset⟩) *
            ∏ i : ↥l.toFinset, μ i (f ⟨i.1, mem_insert_of_mem i.2⟩) := by
        rw [Finset.univ_eq_attach, Finset.attach_insert, Finset.prod_insert, Finset.prod_image,
          ← Finset.univ_eq_attach]
        · exact fun _ _ _ _ hxy => Subtype.ext (congrArg Subtype.val hxy :)
        · simp [fun x : ↥l.toFinset => show (x : ι) ≠ B from fun h => hB (h ▸ x.2)]
      rw [hprod, hsup]
      simp only [piInsertEquiv, Equiv.coe_fn_mk, mul_assoc, union_assoc, union_left_comm]

theorem sum_collapse {β γ : Type*} [Fintype γ] [DecidableEq γ] (M : List β) (key : β → γ)
    (v : β → ℝ) (ψ : γ → ℝ) :
    ∑ x, (M.map fun b => if key b = x then v b else 0).sum * ψ x =
      (M.map fun b => v b * ψ (key b)).sum := by
  induction M with
  | nil => simp
  | cons b M ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul,
      zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]

theorem sum_ite_list_sum {β γ : Type*} [Fintype γ] (E : List β) (p : γ → Prop) [DecidablePred p]
    (f : β → γ → ℝ) :
    ∑ x, (if p x then (E.map fun b => f b x).sum else 0) =
      (E.map fun b => ∑ x, if p x then f b x else 0).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, ← ih, ← Finset.sum_add_distrib]
    congr 1; ext x; split_ifs <;> simp

def normKey (k : List (ℕ × ℕ)) : List (ℕ × ℕ) := k.filter (·.2 != 0)

theorem monoVal_normKey {n : ℕ} (len : Finset (Fin n) → ℝ) (k : List (ℕ × ℕ)) :
    monoVal len (normKey k) = monoVal len k := by
  induction k with
  | nil => rfl
  | cons ae k ih => by_cases h : ae.2 = 0 <;> simp [normKey, h] at ih ⊢ <;> exact ih

noncomputable def evalPoly {n : ℕ} (len : Finset (Fin n) → ℝ) (P : List (ℚ × List (ℕ × ℕ))) : ℝ :=
  (P.map fun p => (p.1 : ℝ) * monoVal len p.2).sum

@[simp] theorem evalPoly_nil {n : ℕ} (len : Finset (Fin n) → ℝ) : evalPoly len [] = 0 := rfl

@[simp] theorem evalPoly_cons {n : ℕ} (len : Finset (Fin n) → ℝ) (p : ℚ × List (ℕ × ℕ))
    (P : List (ℚ × List (ℕ × ℕ))) :
    evalPoly len (p :: P) = (p.1 : ℝ) * monoVal len p.2 + evalPoly len P := rfl

def root_famMask (n : ℕ) (l : List ℕ) : ℕ := l.foldr (fun c acc => 2 ^ (c % 2 ^ n) ||| acc) 0

theorem root_testBit_famMask (n : ℕ) (l : List ℕ) (c : ℕ) :
    (root_famMask n l).testBit c = decide (c < 2 ^ n ∧ decC n c ∈ decF n l) := by
  induction l with
  | nil => simp [root_famMask, decF]
  | cons a l ih =>
    rw [root_famMask, List.foldr_cons, Nat.testBit_or, ← root_famMask, ih, Nat.testBit_two_pow,
      decF_cons]
    have hlt : a % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
    by_cases hc : c < 2 ^ n
    · simp [hc, mem_insert, ← decC_mod n a, decC_inj hc hlt, eq_comm]
    · simp [hc, show a % 2 ^ n ≠ c from fun e => hc (e ▸ hlt)]

theorem root_decF_eq_iff_famMask {n : ℕ} {a b : List ℕ} :
    decF n a = decF n b ↔ root_famMask n a = root_famMask n b := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun c => by rw [root_testBit_famMask, root_testBit_famMask, h],
    fun h => Subset.antisymm (fun A hA => ?_) (fun A hA => ?_)⟩ <;>
  · obtain ⟨c, _, rfl⟩ := mem_decF.1 hA
    have hm := congrArg (·.testBit (c % 2 ^ n)) h
    simp only [root_testBit_famMask, Nat.mod_lt _ (by positivity : 0 < 2 ^ n), decC_mod,
      true_and, decide_eq_decide] at hm
    tauto

def root_collect (n : ℕ) (M : List CTerm) (u : List ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  let m := root_famMask n u
  (M.filter fun τ => root_famMask n τ.forest == m).map fun τ => (τ.coef, normKey τ.key)

theorem sum_eq_evalPoly_root_collect {n : ℕ} (len : Finset (Fin n) → ℝ) (M : List CTerm)
    (u : List ℕ) :
    (M.map fun τ => if decF n τ.forest = decF n u then τ.val len else 0).sum =
      evalPoly len (root_collect n M u) := by
  induction M with
  | nil => rfl
  | cons τ M ih =>
    rw [List.map_cons, List.sum_cons, ih]
    by_cases h : root_famMask n τ.forest = root_famMask n u
    · rw [ite_eq_left (root_decF_eq_iff_famMask.2 h)]; simp [root_collect, h, CTerm.val, monoVal_normKey]
    · rw [ite_eq_right (mt root_decF_eq_iff_famMask.1 h)]; simp [root_collect, h]

inductive PTree where
  | node (a : ℕ) (cs : List PTree)

def PTree.code : PTree → ℕ
  | .node a _ => a

def PTree.children : PTree → List PTree
  | .node _ cs => cs

def CTerm.mul (τ τ' : CTerm) : CTerm := ⟨τ.coef * τ'.coef, τ.key ++ τ'.key, τ'.forest⟩

section Engine

variable (n : ℕ)

mutual
def PTree.out : PTree → Option (List CTerm)
  | .node a cs => match PTree.prodL cs (sampledL n a) with
    | some E => flatMapO (kernelL n a) E
    | none => none
def PTree.prodL : List PTree → List ℕ → Option (List CTerm)
  | [], S => some [⟨1, [], S⟩]
  | c :: cs, S => match PTree.out c with
    | some M => flatMapO (fun τ => (PTree.prodL cs (τ.forest ∪ S)).map (List.map τ.mul)) M
    | none => none
end

mutual
def PTree.wfB (H : Finset (Finset (Fin n))) : PTree → Bool
  | .node a cs =>
    decide (childClusters H (decC n a) = (cs.map fun c => decC n c.code).toFinset) &&
      decide (cs.map fun c => decC n c.code).Nodup &&
      cs.all (fun c => decide (c.code < 2 ^ n) && c.code != 2 ^ n - 1) && PTree.wfListB H cs
def PTree.wfListB (H : Finset (Finset (Fin n))) : List PTree → Bool
  | [] => true
  | c :: cs => PTree.wfB H c && PTree.wfListB H cs
end

def PTree.unrootedL (T : PTree) : Option (List CTerm) :=
  match PTree.prodL n T.children (sampledL n T.code) with
  | some E => flatMapO (fun τ => if checkF n τ.forest then
      some ((jumpL ((rootsL τ.forest).length - 1) τ.forest).map fun q =>
        ⟨τ.coef * q.1, τ.key, unrootL n q.2⟩) else none) E
  | none => none

variable {n} (H : Finset (Finset (Fin n))) (len : Finset (Fin n) → ℝ)

theorem wfB_node {a : ℕ} {cs : List PTree} (h : (PTree.node a cs).wfB n H = true) :
    childClusters H (decC n a) = (cs.map fun c => decC n c.code).toFinset ∧
      (cs.map fun c => decC n c.code).Nodup ∧
      (∀ c ∈ cs, c.code < 2 ^ n ∧ c.code ≠ 2 ^ n - 1) ∧ PTree.wfListB n H cs = true := by
  simp only [PTree.wfB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

mutual
theorem PTree.out_spec : ∀ (T : PTree), T.wfB n H = true → T.code < 2 ^ n →
    T.code ≠ 2 ^ n - 1 → ∀ M, T.out n = some M → ∀ G,
    forestDist H len id (decC n T.code) G =
      (M.map fun τ => if decF n τ.forest = G then τ.val len else 0).sum
  | .node a cs, hwf, hlt, hne, M, hM, G => by
    obtain ⟨hC, hnd, hcodes, hwfl⟩ := wfB_node H hwf
    simp only [PTree.code] at hlt hne ⊢
    simp only [PTree.out] at hM
    split at hM
    · rename_i E hE
      rw [forestDist, sum_pi_eq_iterSum _ (fun F => populationKernel len _ F G) _ hnd _ hC,
        populationKernel, ite_eq_right (fun h => hne ((decC_eq_univ_iff hlt).1 h)), ← decF_sampledL,
        PTree.prodL_spec cs hwfl hcodes _ E hE]
      exact (sum_flatMapO hM _ _ fun τ _ K hK => (kernelL_spec len hK G).symm).symm
    · simp at hM
theorem PTree.prodL_spec : ∀ (cs : List PTree), PTree.wfListB n H cs = true →
    (∀ c ∈ cs, c.code < 2 ^ n ∧ c.code ≠ 2 ^ n - 1) → ∀ S M, PTree.prodL n cs S = some M →
    ∀ φ, iterSum (forestDist H len id) (cs.map fun c => decC n c.code) (decF n S) φ =
      (M.map fun τ => τ.val len * φ (decF n τ.forest)).sum
  | [], _, _, S, M, hM, φ => by
    simp only [PTree.prodL, Option.some.injEq] at hM; subst hM
    simp [iterSum, CTerm.val]
  | c :: cs, hwf, hcodes, S, M, hM, φ => by
    simp only [PTree.wfListB, Bool.and_eq_true] at hwf
    simp only [PTree.prodL] at hM
    split at hM
    · rename_i Mc hMc
      have hc := hcodes c List.mem_cons_self
      simp only [List.map_cons, iterSum]
      simp_rw [PTree.out_spec c hwf.1 hc.1 hc.2 Mc hMc]
      rw [sum_collapse]
      refine (sum_flatMapO hM _ _ fun τ _ x hx => ?_).symm
      obtain ⟨Mτ, hMτ, rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [← decF_union, PTree.prodL_spec cs hwf.2
        (fun c' hc' => hcodes c' (List.mem_cons_of_mem _ hc')) _ Mτ hMτ φ, List.map_map,
        ← List.sum_map_mul_left]
      congr 1; refine List.map_congr_left fun τ' _ => ?_
      simp only [Function.comp_apply, CTerm.val, CTerm.mul, monoVal_append]; push_cast; ring
    · simp at hM
end

theorem PTree.unrootedL_spec (τ : SpeciesTree (Fin n)) (hτ : τ.clusters = H) (T : PTree)
    (hwf : T.wfB n H = true) (htop : T.code = 2 ^ n - 1)
    {M : List CTerm} (hM : T.unrootedL n = some M) (u : List ℕ) :
    τ.unrootedDist id (decF n u) = evalPoly τ.length (root_collect n M u) := by
  rw [← sum_eq_evalPoly_root_collect]
  unfold PTree.unrootedL at hM
  split at hM
  · rename_i E hE
    have hf (G) : forestDist H τ.length id univ G =
        (E.map fun r => r.val τ.length * kingmanAbsorption (decF n r.forest) G).sum := by
      obtain ⟨a, cs⟩ := T
      simp only [PTree.code, PTree.children] at htop hE
      subst htop
      obtain ⟨hC, hnd, hcodes, hwfl⟩ := wfB_node H hwf
      rw [decC_full] at hC
      rw [forestDist, sum_pi_eq_iterSum _ (fun F => populationKernel τ.length _ F G) _ hnd _ hC,
        populationKernel, ite_eq_left rfl, ← decC_full n, ← decF_sampledL]
      exact PTree.prodL_spec H τ.length cs hwfl hcodes _ E hE _
    unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist
    rw [hτ]; simp_rw [hf]; rw [sum_ite_list_sum]
    refine (sum_flatMapO hM _ _ fun r _ x hx => ?_).symm
    split_ifs at hx with hc; cases hx
    obtain ⟨hv, hnd, hF⟩ := of_checkF hc
    have h1 (x) : (if unroot x = decF n u then r.val τ.length *
        kingmanAbsorption (decF n r.forest) x else 0) =
        ((jumpL ((rootsL r.forest).length - 1) r.forest).map fun q =>
          if decF n q.2 = x then (q.1 : ℝ) else 0).sum *
          (if unroot x = decF n u then r.val τ.length else 0) := by
      rw [kingmanAbsorption_apply hF, card_roots_decF hv hnd, jumpMatrix_pow_decF _ _ hv hnd hF]
      split_ifs <;> ring
    simp_rw [h1]; rw [sum_collapse, List.map_map]
    congr 1; refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply, CTerm.val, decF_unrootL]
    split_ifs <;> push_cast <;> ring
  · simp at hM

end Engine

def root_addTerm (t : ℚ × List (ℕ × ℕ)) : List (ℚ × List (ℕ × ℕ)) → List (ℚ × List (ℕ × ℕ))
  | [] => [t]
  | s :: l => if s.2 = t.2 then (s.1 + t.1, s.2) :: l else s :: root_addTerm t l

theorem root_evalPoly_addTerm {n : ℕ} (len : Finset (Fin n) → ℝ) (t : ℚ × List (ℕ × ℕ)) :
    ∀ l, evalPoly len (root_addTerm t l) = t.1 * monoVal len t.2 + evalPoly len l
  | [] => by simp [root_addTerm]
  | s :: l => by
    unfold root_addTerm
    split_ifs with h
    · simp only [evalPoly_cons, h]; push_cast; ring
    · simp only [evalPoly_cons, root_evalPoly_addTerm len t l]; ring

def root_polyEqB (P Q : List (ℚ × List (ℕ × ℕ))) : Bool :=
  ((P ++ Q.map fun t => (-t.1, t.2)).foldr root_addTerm []).all fun t => t.1 == 0

theorem root_evalPoly_append {n : ℕ} (len : Finset (Fin n) → ℝ)
    (P Q : List (ℚ × List (ℕ × ℕ))) : evalPoly len (P ++ Q) = evalPoly len P + evalPoly len Q := by
  simp [evalPoly, List.sum_append]

theorem root_evalPoly_scale {n : ℕ} (len : Finset (Fin n) → ℝ) (c : ℚ) :
    ∀ Q : List (ℚ × List (ℕ × ℕ)),
      evalPoly len (Q.map fun t => (c * t.1, t.2)) = (c : ℝ) * evalPoly len Q
  | [] => by simp
  | t :: Q => by
    rw [List.map_cons, evalPoly_cons, evalPoly_cons, root_evalPoly_scale len c Q]
    push_cast; ring

theorem root_evalPoly_eq_of_polyEqB {n : ℕ} (len : Finset (Fin n) → ℝ)
    {P Q : List (ℚ × List (ℕ × ℕ))} (h : root_polyEqB P Q = true) :
    evalPoly len P = evalPoly len Q := by
  have h0 (L : List (ℚ × List (ℕ × ℕ))) (hL : (L.all fun t => t.1 == 0) = true) :
      evalPoly len L = 0 := by
    induction L with
    | nil => rfl
    | cons t L ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
      rw [evalPoly_cons, hL.1, ih hL.2]; simp
  have hn (R : List (ℚ × List (ℕ × ℕ))) : evalPoly len (R.foldr root_addTerm []) = evalPoly len R := by
    induction R with
    | nil => rfl
    | cons t R ih => rw [List.foldr_cons, root_evalPoly_addTerm, ih, evalPoly_cons]
  have e := h0 _ h
  rw [hn, root_evalPoly_append,
    show Q.map (fun t => (-t.1, t.2)) = Q.map (fun t => (-1 * t.1, t.2)) by simp,
    root_evalPoly_scale] at e
  push_cast at e; linarith

def childCodes (all : List ℕ) (a : ℕ) : List ℕ :=
  all.filter fun b => b != a && (b &&& a == b) &&
    all.all fun c => !(b != c && (b &&& c == b) && (c != a && (c &&& a == c)))

def buildPTreeAux (all : List ℕ) : ℕ → ℕ → PTree
  | 0, a => .node a []
  | k + 1, a => .node a ((childCodes all a).map (buildPTreeAux all k))

def buildPTree (n : ℕ) (cs : List ℕ) : PTree :=
  buildPTreeAux (cs ++ (List.range n).map (2 ^ ·)) n (2 ^ n - 1)

def root_T5code (i : ℕ) : List ℕ :=
  let p := [(0, 0), (3, 7), (3, 11), (3, 19), (5, 7), (5, 13), (5, 21), (9, 11), (9, 13), (9, 25),
    (17, 19), (17, 21), (17, 25), (6, 7), (10, 11), (18, 19)].getD i (0, 0)
  unrootL 5 [p.1, p.2, 1, 2, 4, 8, 16, 31]

noncomputable def u (σ : SpeciesTree (Fin 5)) (i : ℕ) : ℝ :=
  σ.unrootedDist id (decF 5 (root_T5code i))

def root_Q4code (a : ℕ) : List ℕ := unrootL 4 [a, 1, 2, 4, 8, 15]

def root_q4CertB (cs : List ℕ) (P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ))) : Bool :=
  (buildPTree 4 cs).wfB 4 (h4 cs) &&
    match (buildPTree 4 cs).unrootedL 4 with
    | some M => [(root_Q4code 3, P₁), (root_Q4code 5, P₂), (root_Q4code 9, P₃)].all fun t =>
        root_polyEqB (root_collect 4 M t.1) t.2
    | none => false

noncomputable abbrev Q4Eq (τ : SpeciesTree (Fin 4)) (x y z : ℝ) : Prop :=
  τ.unrootedDist id (treeOfClusters {{0, 1}}) = x ∧
  τ.unrootedDist id (treeOfClusters {{0, 2}}) = y ∧
  τ.unrootedDist id (treeOfClusters {{0, 3}}) = z

theorem root_q4 (τ : SpeciesTree (Fin 4)) {cs : List ℕ}
    (hτ : τ.clusters = h4 cs) {P₁ P₂ P₃ : List (ℚ × List (ℕ × ℕ))}
    (hc : root_q4CertB cs P₁ P₂ P₃ = true := by decide +kernel) :
    Q4Eq τ (evalPoly τ.length P₁) (evalPoly τ.length P₂) (evalPoly τ.length P₃) := by
  unfold root_q4CertB at hc
  cases hM : (buildPTree 4 cs).unrootedL 4 with
  | none => simp [hM] at hc
  | some M =>
    simp only [hM, Bool.and_eq_true, List.all_eq_true] at hc
    have h (a : ℕ) (P : List (ℚ × List (ℕ × ℕ)))
        (ht : (root_Q4code a, P) ∈ [(root_Q4code 3, P₁), (root_Q4code 5, P₂), (root_Q4code 9, P₃)])
        {b : Fin 4} (hu : decF 4 (root_Q4code a) = treeOfClusters {{0, b}} := by decide +kernel) :
        τ.unrootedDist id (treeOfClusters {{0, b}}) = evalPoly τ.length P := by
      rw [← hu, (buildPTree 4 cs).unrootedL_spec _ τ hτ hc.1 rfl hM,
        root_evalPoly_eq_of_polyEqB τ.length (hc.2 _ ht)]
    exact ⟨h 3 P₁ List.mem_cons_self,
      h 5 P₂ (List.mem_cons_of_mem _ List.mem_cons_self),
      h 9 P₃ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem root_decC4_3 : decC 4 3 = {0, 1} := by decide +kernel
theorem root_decC4_12 : decC 4 12 = {2, 3} := by decide +kernel

def root_linComb (M : List CTerm) (L : List (ℚ × ℕ)) : List (ℚ × List (ℕ × ℕ)) :=
  L.flatMap fun p => (root_collect 5 M (root_T5code p.2)).map fun q => (p.1 * q.1, q.2)

noncomputable def linVal (τ : SpeciesTree (Fin 5)) (L : List (ℚ × ℕ)) : ℝ :=
  (L.map fun p => (p.1 : ℝ) * u τ p.2).sum

def diffPoly (c : ℚ) (p : List (ℕ × ℕ)) (a e d : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  [(c, normKey (p ++ [(a, e)])), (-c, p ++ [(a, e + d)])]

theorem root_evalPoly_linComb (τ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))}
    (hτ : τ.clusters = H) (T : PTree) (hwf : T.wfB 5 H = true) (htop : T.code = 31)
    {M : List CTerm} (hM : T.unrootedL 5 = some M) :
    ∀ L : List (ℚ × ℕ), evalPoly τ.length (root_linComb M L) = linVal τ L
  | [] => rfl
  | (c, i) :: L => by
    rw [root_linComb, List.flatMap_cons, ← root_linComb, root_evalPoly_append,
      root_evalPoly_scale, root_evalPoly_linComb τ hτ T hwf htop hM L,
      ← T.unrootedL_spec H τ hτ hwf htop hM]
    rfl

theorem monoVal_pos {n : ℕ} (len : Finset (Fin n) → ℝ) (k : List (ℕ × ℕ)) : 0 < monoVal len k :=
  List.prod_pos fun _ hx => by
    obtain ⟨ae, -, rfl⟩ := List.mem_map.1 hx
    exact pow_pos (Real.exp_pos _) _

theorem monoVal_single_lt_one {n : ℕ} (τ : SpeciesTree (Fin n)) {a d : ℕ}
    (ha : decC n a ∈ τ.clusters) (hu : decC n a ≠ univ) (hd : d ≠ 0 := by decide) :
    monoVal τ.length [(a, d)] < 1 := by
  rw [monoVal_cons, monoVal_nil, mul_one]
  exact pow_lt_one₀ (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (τ.length_pos _ ha hu))) hd

variable {τ τ' : SpeciesTree (Fin 5)}

theorem linVal_congr (h : τ.unrootedDist id = τ'.unrootedDist id)
    (L : List (ℚ × ℕ)) : linVal τ L = linVal τ' L := by
  unfold linVal u; rw [h]

theorem u_eq_of_lin {i j : ℕ}
    (h : linVal τ [(1, i), (-1, j)] = evalPoly τ.length []) : u τ i = u τ j := by
  simp only [linVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    evalPoly_nil] at h
  push_cast at h; linarith

theorem u_lt_of_lin {i j a e d : ℕ} {c : ℚ} {p : List (ℕ × ℕ)}
    (ha : decC 5 a ∈ τ.clusters ∧ decC 5 a ≠ univ)
    (h : linVal τ [(1, j), (-1, i)] = evalPoly τ.length (diffPoly c p a e d))
    (hc : 0 < c := by norm_num) (hd : d ≠ 0 := by decide) :
    u τ i < u τ j := by
  simp only [linVal, diffPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    evalPoly_cons, evalPoly_nil, monoVal_normKey, monoVal_append, monoVal_cons, monoVal_nil,
    mul_one, pow_add] at h
  push_cast at h
  have hlt : Real.exp (-τ.length (decC 5 a)) ^ d < 1 := by
    simpa [monoVal_cons, monoVal_nil] using monoVal_single_lt_one τ ha.1 ha.2 hd
  have hpos : 0 < (c : ℝ) * (monoVal τ.length p * Real.exp (-τ.length (decC 5 a)) ^ e) *
      (1 - Real.exp (-τ.length (decC 5 a)) ^ d) :=
    mul_pos (mul_pos (Rat.cast_pos.2 hc) (mul_pos (monoVal_pos _ _) (pow_pos (Real.exp_pos _) _)))
      (sub_pos.2 hlt)
  linarith

theorem linVal_eq_monoVal {L : List (ℚ × ℕ)} {m : List (ℕ × ℕ)}
    (h : linVal τ L = evalPoly τ.length [(1, m)]) : linVal τ L = monoVal τ.length m := by
  simpa [evalPoly_cons, evalPoly_nil] using h

theorem monoVal_eq_of_lin {L : List (ℚ × ℕ)} {m : List (ℕ × ℕ)}
    (hd : τ.unrootedDist id = τ'.unrootedDist id)
    (h : linVal τ L = evalPoly τ.length [(1, m)])
    (h' : linVal τ' L = evalPoly τ'.length [(1, m)]) :
    monoVal τ.length m = monoVal τ'.length m := by
  rw [← linVal_eq_monoVal h, ← linVal_eq_monoVal h', linVal_congr hd]

theorem monoVal_cons_cancel {a e : ℕ} {k : List (ℕ × ℕ)}
    (ha : τ.length (decC 5 a) = τ'.length (decC 5 a))
    (h : monoVal τ.length ((a, e) :: k) = monoVal τ'.length ((a, e) :: k)) :
    monoVal τ.length k = monoVal τ'.length k := by
  simpa [ha, (pow_pos (Real.exp_pos _) _).ne'] using h

theorem length_eq_of_single {a d : ℕ}
    (h : monoVal τ.length [(a, d)] = monoVal τ'.length [(a, d)]) (hd : d ≠ 0 := by decide) :
    τ.length (decC 5 a) = τ'.length (decC 5 a) := by
  simp only [monoVal_cons, monoVal_nil, mul_one] at h
  exact neg_inj.1 (Real.exp_injective
    ((pow_left_inj₀ (Real.exp_pos _).le (Real.exp_pos _).le hd).1 h))

theorem length_eq_of_pair {a e b d : ℕ}
    (ha : τ.length (decC 5 a) = τ'.length (decC 5 a))
    (h : monoVal τ.length [(a, e), (b, d)] = monoVal τ'.length [(a, e), (b, d)])
    (hd : d ≠ 0 := by decide) :
    τ.length (decC 5 b) = τ'.length (decC 5 b) :=
  length_eq_of_single (monoVal_cons_cancel ha h) hd

theorem length_eq_of_pair_left {a d b e : ℕ}
    (hb : τ.length (decC 5 b) = τ'.length (decC 5 b))
    (h : monoVal τ.length [(a, d), (b, e)] = monoVal τ'.length [(a, d), (b, e)])
    (hd : d ≠ 0 := by decide) :
    τ.length (decC 5 a) = τ'.length (decC 5 a) :=
  length_eq_of_pair hb (by simp only [monoVal_cons, monoVal_nil] at h ⊢; linarith) hd

theorem length_eq_of_triple {a e₁ b e₂ c d : ℕ}
    (ha : τ.length (decC 5 a) = τ'.length (decC 5 a))
    (hb : τ.length (decC 5 b) = τ'.length (decC 5 b))
    (h : monoVal τ.length [(a, e₁), (b, e₂), (c, d)] =
      monoVal τ'.length [(a, e₁), (b, e₂), (c, d)])
    (hd : d ≠ 0 := by decide) :
    τ.length (decC 5 c) = τ'.length (decC 5 c) :=
  length_eq_of_pair hb (monoVal_cons_cancel ha h) hd

theorem length_eq_of_cube {p : List (ℕ × ℕ)} {b : ℕ}
    (h1 : monoVal τ.length (p ++ [(b, 1)]) = monoVal τ'.length (p ++ [(b, 1)]))
    (h3 : monoVal τ.length (p ++ [(b, 3)]) = monoVal τ'.length (p ++ [(b, 3)])) :
    τ.length (decC 5 b) = τ'.length (decC 5 b) := by
  have h : monoVal τ.length (p ++ [(b, 1)]) * monoVal τ.length [(b, 2)] =
      monoVal τ'.length (p ++ [(b, 1)]) * monoVal τ'.length [(b, 2)] := by
    simpa only [monoVal_append, monoVal_cons, monoVal_nil, mul_one,
      show ∀ x : ℝ, x ^ 3 = x ^ 1 * x ^ 2 by intro x; ring, mul_assoc] using h3
  rw [h1, mul_right_inj' (monoVal_pos _ _).ne'] at h
  exact length_eq_of_single h

def root_fullCertB (cs : List ℕ) (reqs : List (List (ℚ × ℕ) × List (ℚ × List (ℕ × ℕ)))) : Bool :=
  cs.all (· < 31) && (buildPTree 5 cs).wfB 5 (h5 cs) &&
    match (buildPTree 5 cs).unrootedL 5 with
    | some M => reqs.all fun r => root_polyEqB (root_linComb M r.1) r.2
    | none => false

theorem fullCert_all (τ : SpeciesTree (Fin 5)) {cs : List ℕ}
    (hτ : τ.clusters = h5 cs)
    {reqs : List (List (ℚ × ℕ) × List (ℚ × List (ℕ × ℕ)))} (hc : root_fullCertB cs reqs = true) :
    (∀ a ∈ cs, decC 5 a ∈ τ.clusters ∧ decC 5 a ≠ univ) ∧
      reqs.Forall (fun r => linVal τ r.1 = evalPoly τ.length r.2) := by
  unfold root_fullCertB at hc
  cases hM : (buildPTree 5 cs).unrootedL 5 with
  | none => simp [hM] at hc
  | some M =>
    simp only [hM, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    refine ⟨fun a ha => ⟨hτ ▸ mem_insert_of_mem (mem_union_left _ (decC_mem_decF ha)),
      fun h => by have := hc.1.1 a ha; have := (decC_eq_univ_iff (by omega)).1 h; omega⟩,
      List.forall_iff_forall_mem.2 fun r hr => ?_⟩
    rw [← root_evalPoly_linComb τ hτ (buildPTree 5 cs) hc.1.2 rfl hM r.1]
    exact root_evalPoly_eq_of_polyEqB τ.length (hc.2 r hr)

theorem sameRooted_of_cs {cs : List ℕ}
    (h : τ.clusters = h5 cs) (h' : τ'.clusters = τ.clusters)
    (hl : cs.Forall fun a => τ.length (decC 5 a) = τ'.length (decC 5 a)) :
    τ.SameRootedMetricTree τ' := by
  refine ⟨h'.symm, fun A hA h2 hu => ?_⟩
  rw [h] at hA
  rcases mem_insert.1 hA with rfl | hA
  · exact absurd rfl hu
  rcases mem_union.1 hA with hA | hA
  · obtain ⟨a, ha, rfl⟩ := mem_decF.1 hA
    exact List.forall_iff_forall_mem.1 hl a ha
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hA
    simp at h2

end ADR11
