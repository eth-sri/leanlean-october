module

public import NearlyMinimax.GaussianPrimitiveSeparated
public import Mathlib.MeasureTheory.Integral.Pi
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Coefficient moment tensorization under actual finite product measures.
Only the primitive weighted coefficient pairs need to be integrable. -/
open MeasureTheory MvPolynomial
𝚪
𝚨
𝚩
𝚰

variable {σ E F : Type*} [DecidableEq σ] [MeasurableSpace E] [MeasurableSpace F]

𝗇 𝔍 σ →₀ ℕ
𝗇 𝔙 MvPolynomial σ ℝ
def polynomialPairMoment (w : 𝙏) (P P' : E → 𝔙)
    (β β' : 𝔍) (e : E) : ℝ := w e * (P e).coeff β * (P' e).coeff β'

𝗇 𝔟 fun z => P z.1 * Q z.2
𝗇 𝔓 𝔟
𝗇 𝔠 fun z => P' z.1 * Q' z.2
𝗇 𝔔 𝔠
theorem polynomialPairMoment_mul_expansion
    w v P P'
    Q Q' (β β' : 𝔍) z :
    polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      𝔓 𝔔 β β' z =
      ∑ b ∈ _root_.Finset.HasAntidiagonal.antidiagonal β,
        ∑ b' ∈ _root_.Finset.HasAntidiagonal.antidiagonal β',
        polynomialPairMoment w P P' b.1 b'.1 z.1 *
          polynomialPairMoment v Q Q' b.2 b'.2 z.2 := by
  unfold polynomialPairMoment
  rw [coeff_mul, coeff_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  grind

𝗇 𝔞 fun z => w z.1 * v z.2
𝗇 𝔈 polynomialPairMoment 𝔞 𝔟 𝔠 β β' z
𝗃 𝔭 ἀ w P P' β β'
𝗇 𝔦 𝔭 polynomialPairMoment
𝗇 𝔑 ∀ β β', Integrable 𝔦 μ
𝗇 𝔧 polynomialPairMoment v Q Q' β β'
𝗇 𝔒 ∀ β β', Integrable 𝔧 ν
theorem polynomialPairMoment_product_integrable
    (μ : Measure E) (ν : Measure F) [SigmaFinite μ] [SigmaFinite ν]
    w v P P'
    Q Q'
    (hP : 𝔑)
    (hQ : 𝔒)
    (β β' : 𝔍) :
    Integrable (polynomialPairMoment 𝔞
      𝔓 𝔔 β β') $ μ.prod ν := by
  change Integrable (fun z => 𝔈) $ μ.prod ν
  simp_rw [polynomialPairMoment_mul_expansion]
  fun_prop

𝗃 𝔫 ∫ e, ἀ e ∂μ
theorem polynomialPairMoment_product_integral
    (μ : Measure E) (ν : Measure F) [SigmaFinite μ] [SigmaFinite ν]
    w v P P'
    Q Q'
    (hP : 𝔑)
    (hQ : 𝔒)
    (p p' q q' : 𝔙) a b
    (hEP : ∀ β β', 𝔫 𝔦 =
      a * p.coeff β * p'.coeff β')
    (hEQ : ∀ β β', ∫ e, 𝔧 e ∂ν =
      b * q.coeff β * q'.coeff β') β β' :
     ∫ z, 𝔈 ∂μ.prod ν =
       a * b * (p * q).coeff β * (p' * q').coeff β' := by
  simp_rw [polynomialPairMoment_mul_expansion]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ =>
    (hP c.1 c'.1).mul_prod $ hQ c.2 c'.2 ]
  simp_rw [integral_finsetSum _ fun (c' : 𝔍 × 𝔍) _ =>
    (hP _ c'.1).mul_prod $ hQ _ c'.2 , integral_prod_mul, hEP, hEQ]
  rw [coeff_mul, coeff_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  grind

𝗃 𝔥 ∏ j, ἀ j (e j)
𝗇 𝔇 𝔥 w * (𝔥 P).coeff β * (𝔥 P').coeff β'
𝗇 𝔐 𝗚₁
def tensorPolynomialPairMoment (w : Fin n → 𝙏)
    (P P' : Fin n → E → 𝔙) (β β' : 𝔍)
    (e : 𝔐) : ℝ :=
  𝔇

𝗇 𝔚 polynomialPairMoment (w j) (P j) (P' j) β β'
𝗇 𝔄 ∀ j β β', 𝔫 𝔚 = a j * (p j).coeff β * (p' j).coeff β'
𝗇 𝔨 𝘫
𝗇 𝔅 Measure.pi 𝔨
𝗃 𝔮 ∏ j, ἀ j
𝗇 𝔉 𝔮 a * (𝔮 p).coeff β * (𝔮 p').coeff β'
𝗇 𝔊 ∀ j β β', Integrable 𝔚 μ
𝗇 𝔛 𝔭 tensorPolynomialPairMoment
𝗇 𝔩 𝚓
𝗇 𝔎 𝔛 ∘ (MeasurableEquiv.piFinSuccAbove 𝔩 0).symm
𝗃 𝔢 fun j => ἀ j.succ
𝗃 𝔣 ἀ μ _ (w 0) W (P 0) (P' 0) Q Q' (hi 0) hiTail
𝗃 𝔤 ∏ j : Fin n, ἀ j.succ
𝗃 𝔪 ∏ j, ἀ j.succ (x j)
𝗃 𝔬 ∫ e, ἀ e ∂𝔅 = 𝔉
theorem tensorPolynomialPairMoment_fin
    (μ : Measure E) [SigmaFinite μ] n
    w P P'
    (p p' : Fin n → 𝔙) (a : 𝙔)
    (hi : 𝔊)
    (he : 𝔄) :
    ∀ β β', Integrable 𝔛 𝔅 ∧
      𝔬 𝔛 := by
  induction n with
  | zero =>
    intro β β'
    have hprob : IsProbabilityMeasure $ Measure.pi fun _ : Fin 0 => μ := by
      constructor
      simp
    let _ := hprob
    constructor
    · simp
    · simp only [tensorPolynomialPairMoment, Finset.univ_eq_empty, Finset.prod_empty,
        integral_const, probReal_univ, one_smul]
  | succ n ih =>
    intro β β'
    let W (x : 𝔐) := 𝔪 w
    let Q (x : 𝔐) := 𝔪 P
    let Q' (x : 𝔐) := 𝔪 P'
    have htail := ih 𝔢 w 𝔢 P 𝔢 P'
      𝔢 p 𝔢 p' 𝔢 a
      𝔢 hi 𝔢 he
    have hiTail := fun b b' => (htail b b').1
    let G := polynomialPairMoment (fun z : E × 𝔐 => w 0 z.1 * W z.2)
      (fun z => P 0 z.1 * Q z.2) (fun z => P' 0 z.1 * Q' z.2) β β'
    have hGi : Integrable G $ μ.prod 𝔅 :=
      𝔣 polynomialPairMoment_product_integrable β β'
    have hGe :=
      𝔣 polynomialPairMoment_product_integral (p 0) (p' 0) 𝔤 p 𝔤 p'
        (a 0) 𝔤 a (he 0) (fun b b' => (htail b b').2) β β'
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin 𝗉 => μ) 0).symm
    have hcomp : 𝔎 = G := by
      funext z
      simp only [Function.comp_def, tensorPolynomialPairMoment,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, G, W, Q, Q',
        polynomialPairMoment, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, cast_eq]
    constructor
    · rw [← hmp.integrable_comp_emb $ MeasurableEquiv.measurableEmbedding _ ]
      simp_all
    · rw [← hmp.integral_comp']
      change ∫ x, 𝔎 x
        ∂μ.prod 𝔅 = _
      rw [hcomp, hGe]
      simp only [Fin.prod_univ_succ]

def tensorPolynomialPairMoment_fintype [Fintype κ]
    (w : κ → 𝙏) (P P' : κ → E → 𝔙)
    (β β' : 𝔍) (e : κ → E) : ℝ :=
  𝔇

𝗇 𝔜 𝔭 tensorPolynomialPairMoment_fintype
𝗇 𝔏 𝔜 ∘ MeasurableEquiv.piCongrLeft 𝔩 e
𝗃 𝔡 fun j => ἀ $ e j
𝗇 𝔖 𝔡 w
𝗇 𝔗 𝔡 P
𝗇 𝔘 𝔡 P'
theorem tensorPolynomialPairMoment_fintype_integral [Fintype κ]
    (μ : Measure E) [SigmaFinite μ]
    w P P'
    (p p' : κ → 𝔙) (a : 𝖱₁)
    (hi : 𝔊)
    (he : 𝔄) β β' :
    Integrable 𝔜 𝔅 ∧
      𝔬 𝔜 := by
  classical
  let e := (Fintype.equivFin κ).symm
  have h := tensorPolynomialPairMoment_fin μ (Fintype.card κ)
    𝔖 𝔗 𝔘
    𝔡 p 𝔡 p' 𝔡 a
    𝔡 hi 𝔡 he β β'
  have hmp := measurePreserving_piCongrLeft 𝔨 e
  have hcomp : 𝔏 =
      tensorPolynomialPairMoment 𝔖 𝔗
        𝔘 β β' := by
    funext x
    simp only [Function.comp_def, tensorPolynomialPairMoment_fintype,
      tensorPolynomialPairMoment, ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply]
  constructor
  · rw [← hmp.integrable_comp_emb $ MeasurableEquiv.measurableEmbedding _ , hcomp]
    exact h.1
  · rw [← hmp.integral_comp']
    change ∫ x, 𝔏 x
      ∂𝔅 = _
    rw [hcomp, h.2]
    simp only [e.prod_comp]
