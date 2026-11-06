module

public import NearlyMinimax.LowSmoothnessVariance
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-! # IID design patch counts

Patch membership is measured under an actual product probability measure
on the design sample. The binomial law is derived by partitioning that
sample space into disjoint membership cells.
-/

𝚨

𝚯

noncomputable section

𝚬

𝗇 𝔇 𝚅₁
𝗇 𝔑 x i ∈ A
𝗇 𝔉 fun i => 𝔑
/-- Number of iid design observations falling in a patch. -/
def designPatchCount (n : ℕ) (A : Set α) (x : 𝔇) : ℕ :=
  (Finset.univ.filter 𝔉).card

/-- The cell with precisely the observation indices in `s` inside the patch. -/
def designMembershipCell (n : ℕ) (A : Set α) (s : 𝙍) : Set 𝔇 :=
  Set.pi Set.univ fun i => if i ∈ s then A else Aᶜ

𝗃 𝔓 ἀ n A
𝗇 𝔒 𝔓 designPatchCount
𝗇 𝔄 𝔒 x
theorem design_patch_count_le n (A : Set α) x :
    𝔄 ≤ n := by
  unfold designPatchCount
  simpa using Finset.card_le_card $ Finset.filter_subset 𝔉 Finset.univ

𝗇 𝔈 𝔓 designMembershipCell s
theorem design_membership_cell_iff n (A : Set α)
    s x :
    x ∈ 𝔈 ↔ ∀ i, 𝔑 ↔ i ∈ s := by
  simp only [designMembershipCell]
  grind

theorem design_membership_cell_measurable [MeasurableSpace α]
    n (A : Set α) (hA : MeasurableSet A) s :
    MeasurableSet 𝔈 := by
  apply MeasurableSet.pi Set.countable_univ
  aesop

𝗇 𝔍 (𝔓 design_membership_cell_iff s x).mp
theorem design_membership_cells_disjoint n (A : Set α) :
    Pairwise fun s t => Disjoint 𝔈 $ 𝔓 designMembershipCell t := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  apply hst
  ext i
  exact (𝔍 hs i).symm.trans
    $ (𝔓 design_membership_cell_iff t x).mp ht i

𝗇 𝔎 𝔄 = k
/-- The count event is a disjoint union of cells indexed by subsets of its count. -/
theorem design_patch_count_fiber n A k :
    {x : 𝔇 | 𝔎} =
      ⋃ s ∈ Finset.univ.powersetCard k, 𝔈 := by
  ext x
  constructor
  · intro hx
    let s := Finset.univ.filter 𝔉
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · simpa
    · rw [design_membership_cell_iff]
      grind
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hfilter : Finset.univ.filter 𝔉 = s := by
      ext i
      simpa using 𝔍 hxs i
    aesop

𝗇 𝔅 Measure.pi 𝘫
/-- Membership cells have the product Bernoulli probabilities dictated by
independence under the iid design product measure. -/
theorem iid_design_membership_cell_measure [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] n A
    s :
    𝔅 𝔈 =
       μ A ^ s.card * μ Aᶜ ^ (n - s.card) := by
  rw [designMembershipCell, Measure.pi_pi]
  simp only [apply_ite]
  rw [Finset.prod_ite]
  have hin : (Finset.univ.filter fun i => i ∈ s) = s := 𝖢₄
  have hout : (Finset.univ.filter fun i => i ∉ s) = Finset.univ \ s := 𝖤₃
  rw [hin, hout]
  simp [Finset.card_sdiff_of_subset $ Finset.subset_univ s ]

𝗇 𝔏 binomialCountMass n (μ.real A) k
/-- Exact binomial count law, in real probabilities, for an arbitrary measurable
patch under an arbitrary iid design probability measure. -/
theorem iid_design_patch_count_probability [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] n A (hA : MeasurableSet A) k :
    (𝔅).real {x : 𝔇 | 𝔎} =
      𝔏 := by
  rw [measureReal_def, design_patch_count_fiber]
  rw [measure_biUnion_finset]
  · rw [ENNReal.toReal_sum fun s _ => 𝚃₁ ]
    have hcell s (hs : s ∈ Finset.univ.powersetCard k) :
        (𝔅 𝔈).toReal =
           μ.real A ^ k * (1 - μ.real A) ^ (n - k) := by
      rw [iid_design_membership_cell_measure, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
      rw [(Finset.mem_powersetCard.mp hs).2]
      have hcompl : μ.real Aᶜ = 1 - μ.real A := by
        simpa using measureReal_compl hA (μ := μ)
      tauto
    rw [Finset.sum_congr rfl hcell]
    simp
    unfold binomialCountMass
    ring
  · intro s hs t ht hst
    exact 𝔓 design_membership_cells_disjoint hst
  · intro s _
    exact 𝔓 design_membership_cell_measurable hA s

/-- The patch count is a measurable random variable. -/
theorem design_patch_count_measurable [MeasurableSpace α]
    n (A : Set α) (hA : MeasurableSet A) : Measurable 𝔒 := by
  have heq : 𝔒 =
       fun x => ∑ i : Fin n, if 𝔑 then 1 else 0 := by
    aesop
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hA.preimage $ measurable_pi_apply i ) measurable_const measurable_const

𝗇 𝔊 ∫ x : 𝔇, e 𝔄 ∂𝔅
𝗇 𝔐 𝗉
/-- Every finite function of the actual patch count integrates against its
binomial law. This connects the counting estimate to the iid design measure. -/
theorem iid_design_count_integral [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] n A (hA : MeasurableSet A)
    (e : 𝙜) :
    𝔊 =
      ∑ k ∈ Finset.range 𝔐, 𝔏 * e k := by
  let ν := 𝖲₂
  have hm k : MeasurableSet {x : 𝔇 | 𝔎} :=
    (measurableSet_singleton k).preimage $ 𝔓 design_patch_count_measurable hA
  have hdecomp x : e 𝔄 =
      ∑ k ∈ Finset.range 𝔐,
        ({x : 𝔇 | 𝔎}).indicator (fun _ => e k) x := by
    symm
    calc
      _ = ({x : 𝔇 | 𝔄 = 𝔄}).indicator
          (fun _ => e 𝔄) x := by
        apply Finset.sum_eq_single 𝔄
        · intro k _ hk
          simp [Ne.symm hk]
        · intro hn
          exact False.elim $ hn $ Finset.mem_range.mpr
            $ Nat.lt_succ_iff.mpr $ 𝔓 design_patch_count_le x
      _ = e 𝔄 := 𝖢₄
  rw [ funext hdecomp , integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_indicator_const (e k) $ hm k , iid_design_patch_count_probability μ n A hA k]
    simp
  · intro k _
    exact (integrable_const $ e k ).indicator $ hm k

/-- Integration of a genuine iid patch count gives the quadratic collision
energy bound, without assuming a binomial count law as a hypothesis. -/
theorem iid_design_collision_energy_bound [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) A (hA : MeasurableSet A)
    C η (e : 𝙜) (hC : 𝖺₁) (hmean : n * μ.real A ≤ 1)
    (he0 : e 0 = 0) (he1 : e 1 = 0) (he : ∀ k, 𝚂 → e k ≤ C ^ k * 𝗩) :
    𝔊 ≤
      C ^ 2 * Real.exp C * 𝗩 * (n * μ.real A) ^ 2 := by
  rw [iid_design_count_integral μ n A hA e]
  exact binomial_collision_energy_bound n (μ.real A) C η e measureReal_nonneg
    measureReal_le_one hC hmean he0 he1 he
