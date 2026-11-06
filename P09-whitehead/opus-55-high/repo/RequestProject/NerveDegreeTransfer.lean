import RequestProject.NerveDegreeGluing


/-! Homogeneous positive-degree fillings transfer from an actual induced subposet. -/
namespace FiniteChains.Nerve
universe u
variable {P Q : Type u}

theorem lengthProjection_cmap (f : P → Q) n c :
    lengthProjection n (cmap f c) = cmap f (lengthProjection n c) := by
  classical
  refine ext_apply
    (F := (lengthProjection n).comp (cmap f))
    (G := (cmap f).comp (lengthProjection n)) ?_ c
  aesop

variable [Preorder P]

theorem fillsDegreeIn_of_subtype {A : P → Prop} {n} (hne : ∃ p, A p)
    (hfill : ∀ c ∈ Inc {p : P // A p}, lengthProjection n c = c → bdry c = 0 →
      ∃ y ∈ Inc {p : P // A p}, bdry y = c) : FillsDegreeIn A n := by
  intro c hc hd hcyc
  obtain ⟨c', hc', he⟩ := exists_preimage_of_mem_incOn A hc
  have hd' : lengthProjection n c' = c' := by
    apply cmap_val_injective A hne
    rw [← lengthProjection_cmap, he, hd]
  have hcyc' : bdry c' = 0 := by
    apply cmap_val_injective A hne
    rw [cmap_bdry, he, hcyc, map_zero]
  obtain ⟨y, hy, hdy⟩ := hfill c' hc' hd' hcyc'
  exact ⟨cmap Subtype.val y, cmap_val_mem_incOn A hy, by rw [← cmap_bdry, hdy, he]⟩

theorem fillsDegreeIn_congr {A B : P → Prop} {n}
    (he : ∀ p, A p ↔ B p) (h : FillsDegreeIn A n) : FillsDegreeIn B n := by
  grind [show B = A from by grind]

theorem generatesDegreeIn_congr {A B Base : P → Prop} {n}
    (he : ∀ p, A p ↔ B p) (h : GeneratesDegreeIn A Base n) :
    GeneratesDegreeIn B Base n := by
  grind [show B = A from by grind]
