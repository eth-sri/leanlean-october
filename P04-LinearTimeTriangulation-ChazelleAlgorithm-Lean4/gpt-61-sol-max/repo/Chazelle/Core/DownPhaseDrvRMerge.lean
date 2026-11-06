module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRBSort
public import Chazelle.Core.DownPhaseDrvSplice

/-!
# Down-phase driver (RAM side): merging two sorted lists of event codes

`mergeE` merges the sorted code lists `src[0, mid)` and `src[mid, hi)` into `dst[0, hi)` by the
event comparator (one merge of `SortR`, `mergeLoop evCmp`): registers `210070` (`src`), `210071`
(`dst`), `210072` (`mid`), `210073` (`hi`) of `bDownDrv`.  `mergeE_exec`: the output is
`List.merge E E₂` for the comparator `codeLe` (`merge_congr`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

/-- `List.merge` only depends on the comparator on the elements of its arguments. -/
theorem merge_congr {f g : ℕ → ℕ → Bool} :
    ∀ (l₁ l₂ : List ℕ), (∀ x ∈ l₁, ∀ y ∈ l₂, f x y = g x y) →
      List.merge l₁ l₂ f = List.merge l₁ l₂ g := by
  intro l₁ l₂
  induction l₁ generalizing l₂ with
  | nil => simp_all
  | cons x xs ih =>
    induction l₂ with
    | nil => simp_all
    | cons y ys ih₂ =>
      grind [List.cons_merge_cons]

/-- The merge registers. -/
def mgSetup : Stmt :=
  block [.constN 30006 1, .copyN 30007 210070, .copyN 30008 210071, .copyN 30011 210072,
    .copyN 30012 210073, .constN 30013 0, .copyN 30014 210072, .constN 30015 0]

/-- **The merge.** -/
def mergeE : Stmt := .seq mgSetup (SortR.mergeLoop evCmp)

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Merging two sorted lists of event codes.** -/
theorem mergeE_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {S Dst mid hi D T : ℕ} {M : Model} {L : List (ℕ × ℕ × ℕ)}
    {E E₂ : List ℕ}
    (h70 : c.nreg 210070 = S) (h71 : c.nreg 210071 = Dst) (h72 : c.nreg 210072 = mid)
    (h73 : c.nreg 210073 = hi) (hmh : mid ≤ hi)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T) (h42' : c.nreg 42001 = 2 * L.length)
    (hwf : ModelDescWF P Dst c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hL : ChordTriplesOK M (Qof P) L) (hR : RecsAt c.nmem T L) (hTA : T + 8 * L.length ≤ Dst)
    (hE : seg c.nmem S mid = E) (hE₂ : seg c.nmem (S + mid) (hi - mid) = E₂)
    (hcodes : ∀ x ∈ E ++ E₂, x < 2 * L.length) (hSD : S + hi ≤ Dst)
    (hroom : Dst + hi + 1 ≤ W) :
    ∃ c' k, Exec P W mergeE c c' k ∧ k ≤ (11010 + 16) * hi + 10 ∧ WordsBounded W c' ∧
      seg c'.nmem Dst hi = List.merge E E₂ (DownDrv.codeLeB M (Qof P) L) ∧
      (∀ a, (a < Dst ∨ Dst + hi ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg ALLOC = c.nreg ALLOC ∧
      (∀ r, bandOf r ∉ ({bSign, bBuild} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = T ∧ c'.nreg 42001 = 2 * L.length ∧
      (∀ r, 43000 ≤ r → r < 44000 → c'.nreg r = c.nreg r) := by
  have hW1 : 1 ≤ W := by omega
  -- the registers
  obtain ⟨c₁, k₁, e₁, hk₁, v6, v7, v8, v11, v12, v13, v14, v15, g₁, m₁, rr₁, rm₁, o₁⟩ :
      ∃ c₁ k₁, Exec P W mgSetup c c₁ k₁ ∧ k₁ = 8 ∧ c₁.nreg 30006 = 1 ∧ c₁.nreg 30007 = S ∧
      c₁.nreg 30008 = Dst ∧ c₁.nreg 30011 = mid ∧ c₁.nreg 30012 = hi ∧ c₁.nreg 30013 = 0 ∧
      c₁.nreg 30014 = mid ∧ c₁.nreg 30015 = 0 ∧
      (∀ r, (r < 30000 ∨ 40000 ≤ r) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold mgSetup
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;>
      config_simp <;> (try simp only [h70, h71, h72, h73])
    grind [Machine.upd_other]
  have w₁ := e₁.wb_right
  -- the comparator
  have hcmp := evCmp_ok (P := P) (W := W) hG hWn (m₀ := c₁.nmem) (A₀ := Dst) (D := D) (T := T)
    (M := M) (L := L) (by omega) (by simp_all) (by simp_all) hL
    (by simp_all) hTA c₁.nreg
  have hJ₁ : EvJ c₁.nmem Dst D T (2 * L.length) c₁.nreg c₁ :=
    ⟨by simp_all, by simp_all, by simp_all,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hI : SortR.MergeInv W (EvJ c₁.nmem Dst D T (2 * L.length) c₁.nreg)
      (evLeB M (Qof P) L (2 * L.length)) {bSign, bBuild} Dst c₁ c₁ S Dst 0 mid hi E E₂ c₁ :=
    { wb := w₁, hJ := hJ₁, loc := SortR.Loc.refl _ _ _, one := v6, rsrc := v7, rdst := v8,
      rmid := v11, rhi := v12, keep := fun _ _ _ _ _ _ _ _ _ _ => rfl,
      lo_i := by rw [v13], i_mid := by omega, mid_j := by rw [v14],
      j_hi := by omega, rk := by omega,
      bsrc := by omega, bdst := by omega, disj := Or.inl (by omega), dA := le_rfl,
      ma := by simp_all,
      mb := by simp_all,
      out := by simp_all,
      mem := fun _ _ => rfl }
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hseg⟩ := SortR.mergeLoop_inv (P := P) hcmp
    (evJ_stable _ _ _ _ _ _) (by decide) hI
  rw [v15, Nat.sub_zero] at hk₂
  rw [Nat.add_zero, Nat.sub_zero] at hseg
  obtain ⟨j1, j2, j3, j4, j5⟩ := I₂.hJ
  obtain ⟨l1, l2, l3, l4, l5⟩ := I₂.loc
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, I₂.wb, ?_, fun a ha => ?_, fun r hr hra => ?_, ?_,
    fun r hr => ?_, by rw [l4, rm₁], by rw [l5, o₁], j1, j2, j3, fun r h1 h2 => ?_⟩
  · rw [hseg]
    refine merge_congr E E₂ fun x hx y hy => ?_
    grind [evLeB, DownDrv.codeLeB]
  · rcases ha with ha | ha
    · ram_grind
    · rw [I₂.mem a (Or.inr (by omega)), m₁]
  · grind [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort]
  · rw [I₂.keep ALLOC (Or.inr rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), g₁ _ (by decide)]
  all_goals grind

end exec

end

end DrvR

end Chazelle.Core
