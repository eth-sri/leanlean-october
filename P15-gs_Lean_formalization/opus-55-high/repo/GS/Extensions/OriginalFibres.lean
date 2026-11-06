module

public import GS.Extensions.OriginalCompact
public import GS.Extensions.TransportedProjection

@[expose] public section


/-!
# Missing algebra and angle recovery in the ORIGINAL f/g fibre proof

The central result gives actual equality of f/g
fibres under explicit local analytic hypotheses: bounded angles, scalar sign
normalization, and injectivity of originalPsi on a set containing c ± z.
Those hypotheses are NOT claimed established uniformly on some K_eta here.
In particular no smoothness of the singular matrix family is assumed.
-/

noncomputable section
namespace GS.Extensions

 theorem middleFamily_fibres {q : ℕ} (A B A' B' : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v)
    (h : ∀ i j, middleBlock (A i j) (B i j) u =
      middleBlock (A' i j) (B' i j) v) :
    (A=B ∧ A'=B' ∧ A=A') ∨
      (u=v ∧ A=A' ∧ B=B') ∨ (u=-v ∧ A=B' ∧ B=A') := by
  have hs i j := (middleBlock_eq_sum_and_difference _ _ _ _ u v (h i j)).1
  have hout : outer u (fun ij : Fin q × Fin q => A ij.1 ij.2-B ij.1 ij.2) =
      outer v (fun ij : Fin q × Fin q => A' ij.1 ij.2-B' ij.1 ij.2) := by
    ext r ij
    have := congrFun (congrFun (middleBlock_eq_sum_and_difference _ _ _ _ u v (h ij.1 ij.2)).2 0) r
    fin_cases r <;> simpa [outer,T,mul_comm] using this
  rcases (outer_fibres hu hv).mp hout with ⟨h₀,h₀'⟩ | ⟨huv,hd⟩ | ⟨huv,hd⟩ <;>
    simp only [funext_iff, Pi.zero_apply, Pi.neg_apply, Prod.forall] at *
  · refine .inl ⟨?_, ?_, ?_⟩ <;> ext i j <;> grind
  · refine .inr (.inl ⟨huv, ?_, ?_⟩) <;> ext i j <;> grind
  · refine .inr (.inr ⟨huv, ?_, ?_⟩) <;> ext i j <;> grind

 theorem sandwich_trace (a b l r : ℝ) (u : CircleVector) :
    (rotation l * middleBlock a b u * rotation r) 0 0 +
      (rotation l * middleBlock a b u * rotation r) 1 1 =
        (a+b)*Real.cos (l+r) ∧
    (rotation l * middleBlock a b u * rotation r) 1 0 -
      (rotation l * middleBlock a b u * rotation r) 0 1 =
        (a+b)*Real.sin (l+r) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [rotation,middleBlock,T,Real.cos_add,Real.sin_add]
  constructor <;> ring

 theorem scaled_trig_unique (s s' θ θ' : ℝ)
    (hprod : 0 < s*s')
    (hθ : θ ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (hθ' : θ' ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (hc : s*Real.cos θ=s'*Real.cos θ')
    (hs : s*Real.sin θ=s'*Real.sin θ') : θ=θ' := by
  have hnorm (a t : ℝ) : (a*Real.cos t)^2+(a*Real.sin t)^2=a^2 := by
    linear_combination a^2 * Real.sin_sq_add_cos_sq t
  obtain rfl : s = s' := (sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [← hnorm s θ, ← hnorm s' θ', hc, hs])).resolve_right
    (by rintro rfl; nlinarith [sq_nonneg s'])
  exact Real.injOn_sin hθ hθ' (mul_left_cancel₀ (by grind) hs)

/-- Recover the sum of angles from two scalar matrix invariants. This is an
alternative proof of the polar-factor step, not a new parameterization. It
requires no assertion that the original M_ij is symmetric or positive definite. -/
 theorem sandwich_angle_unique (a b a' b' l r l' r' q₀ : ℝ) (u v : CircleVector)
    (h : rotation l * middleBlock a b u * rotation r =
      rotation l' * middleBlock a' b' v * rotation r')
    (hp : 0<(a+b)*q₀) (hp' : 0<(a'+b')*q₀)
    (ht : l+r ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))
    (ht' : l'+r' ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2)) : l+r=l'+r' :=
  scaled_trig_unique (a+b) (a'+b') _ _ (by nlinarith [mul_pos hp hp', sq_nonneg q₀]) ht ht'
    (by simpa only [sandwich_trace] using congrArg (fun X : Mat 2 => X 0 0+X 1 1) h)
    (by simpa only [sandwich_trace] using congrArg (fun X : Mat 2 => X 1 0-X 0 1) h)

 theorem originalF_block_eq {q : ℕ} (Q₀ : Mat q)
    (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (h : originalF Q₀ (ell,r,c,z,u)=originalF Q₀ (ell',r',c',w,v)) (i j : Fin q) :
    rotation (ell i) * middleBlock (originalPsi Q₀ (c+z) i j)
      (originalPsi Q₀ (c-z) i j) u * rotation (r j) =
    rotation (ell' i) * middleBlock (originalPsi Q₀ (c'+w) i j)
      (originalPsi Q₀ (c'-w) i j) v * rotation (r' j) := by
  ext s t
  simpa only [originalF, Equiv.symm_apply_apply] using congrFun (congrFun h (finProdFinEquiv (i,s))) (finProdFinEquiv (j,t))

/-- Explicit local analytic input. No statement of equal fibres is hidden here.
The set V is a matrix-exponential chart domain supplied by a later analytic
lemma. The angles and signs are the ones in the original manuscript. -/
 def NormalizedOriginal {q : ℕ} (Q₀ : Mat q) (V : Set (Mat q))
    (p : OriginalParameters q) : Prop :=
  let (ell,r,c,z,u) := p
  OnCircle u ∧
    (∀ j : Fin q, j.val=0 → r j=0) ∧
    (∀ i j, ell i+r j ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2)) ∧
    (∀ i j, 0 < (originalPsi Q₀ (c+z) i j+originalPsi Q₀ (c-z) i j)*Q₀ i j) ∧
    c+z ∈ V ∧ c-z ∈ V

 theorem original_same_fibres_normalized {q : ℕ} (hq : 0<q) (Q₀ : Mat q)
    (V : Set (Mat q)) (hinj : Set.InjOn (originalPsi Q₀) V)
    (p p' : OriginalParameters q)
    (hp : NormalizedOriginal Q₀ V p) (hp' : NormalizedOriginal Q₀ V p') :
    originalF Q₀ p=originalF Q₀ p' ↔ originalG p=originalG p' := by
  obtain ⟨ell,r,c,z,u⟩ := p
  obtain ⟨ell',r',c',w,v⟩ := p'
  obtain ⟨hu,hr₀,ht,hpos,hplus,hminus⟩ := hp
  obtain ⟨hv,hr₀',ht',hpos',hplus',hminus'⟩ := hp'
  refine ⟨fun hF => ?_, originalF_eq_of_originalG_eq Q₀ ell r ell' r' c z c' w u v hu hv⟩
  have hblocks := originalF_block_eq Q₀ ell r ell' r' c z c' w u v hF
  have hangles i j := sandwich_angle_unique _ _ _ _ _ _ _ _ (Q₀ i j) u v
    (hblocks i j) (hpos i j) (hpos' i j) (ht i j) (ht' i j)
  obtain rfl : ell=ell' := funext fun i => by grind [hangles i ⟨0,hq⟩]
  obtain rfl : r=r' := by aesop
  apply (originalG_fibres ell r ell r c z c' w u v hu hv).mpr
  have key {x y x' y' : Mat q} (h1 : x+y = x'+y') (h2 : x-y = x'-y') : x = x' ∧ y = y' :=
    ⟨by linear_combination (norm := module) (2⁻¹:ℝ) • (h1 + h2), by linear_combination (norm := module) (2⁻¹:ℝ) • (h1 - h2)⟩
  rcases middleFamily_fibres _ _ _ _ u v hu hv fun i j => lift_injective (rotation (ell i)) (rotation (r j))
      (rotation_orthogonal _) (rotation_orthogonal _) (hblocks i j) with
    ⟨hAB,hAB',hAA'⟩ | ⟨huv,hAA',hBB'⟩ | ⟨huv,hAB',hBA'⟩
  · obtain ⟨rfl, rfl⟩ := key (hinj hplus hplus' hAA') (hinj hminus hminus' (hAB.symm.trans (hAA'.trans hAB')))
    have : z = 0 := by linear_combination (norm := module) (2⁻¹:ℝ) • hinj hplus hminus hAB
    exact ⟨rfl, rfl, rfl, .inl ⟨this, this⟩⟩
  · obtain ⟨rfl, rfl⟩ := key (hinj hplus hplus' hAA') (hinj hminus hminus' hBB')
    exact ⟨rfl, rfl, rfl, .inr (.inl ⟨huv, rfl⟩)⟩
  · obtain ⟨rfl, rfl⟩ := key ((hinj hplus hminus' hAB').trans (sub_eq_add_neg _ _)) ((hinj hminus hplus' hBA').trans (sub_neg_eq_add _ _).symm)
    exact ⟨rfl, rfl, rfl, .inr (.inr ⟨huv, rfl⟩)⟩

end GS.Extensions
