/-
  KineticCounterexamples — all-in-one file.

  Lean 4 formalization of
    H. Dong and W. Wang, *Several counterexamples to kinetic Schauder estimates*
    (arXiv:2607.20682): Sections 1–4 (Theorem 2.1, Remark 2.2, Proposition 3.1,
    the disproof of Conjecture 1.1, Theorem 4.1, Remark 4.2, Theorem 4.3).

  This is the concatenation, in dependency order, of the 26 modules of the Lake project
  `KineticCounterexamples` (each module wrapped in its own `section`). It needs only Mathlib
  (rev b3b63681020779dc7e14866c0b2afbd84e0722e4, Lean v4.35.0-rc2); inside any Lake project
  with that Mathlib, check it with

      lake env lean KineticCounterexamples_AllInOne.lean

  The `#print axioms` commands at the end list the axioms of the main results: only
  `propext`, `Classical.choice`, `Quot.sound`.  See REPORT.md for the paper-to-Lean table.
-/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Basic.Real.Sign

-- ============================================================================
-- KineticCounterexamples/Profile.lean
-- ============================================================================

section File_Profile

/-!
# The Airy-type profile `J` and the one-frequency integral `I_N`

This file contains the one-dimensional analysis shared by
*Several counterexamples to kinetic Schauder estimates* (Dong–Wang) and
*A note on relativistic kinetic Schauder estimates* (Wang):

* `J y = ∫₀^∞ e^{-r³/3} e^{-iry} dr` (display (2.6) of Dong–Wang) and its derivatives
  `Jn n y = ∫₀^∞ (-ir)ⁿ e^{-r³/3} e^{-iry} dr`;
* smoothness of `J`, `deriv (Jn n) = Jn (n+1)`, the bounds `‖Jn n y‖ ≤ mom n`;
* `J''(0) = -1` (display (2.10)), the Riemann–Lebesgue limit `J''(y) → 0`,
  and the Airy-type ODE `J'' - i y J = -1`;
* `C₀ = ∫₀^∞ e^{-r³/3} dr = 3^{-2/3} Γ(1/3)`;
* `I_N(η) = ∫₀^∞ exp(-N²s³/3) e^{-iNsη} ds` (display (2.3)) and the scaling
  `I_N(η) = N^{-2/3} J(N^{1/3} η)` (display (2.7)).
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped ContDiff

namespace KS

/-- The weight `e^{-r³/3}`. -/
def wt (r : ℝ) : ℝ := Real.exp (-(r ^ 3 / 3))

lemma wt_pos (r : ℝ) : 0 < wt r := Real.exp_pos _

lemma wt_le_one {r : ℝ} (hr : 0 ≤ r) : wt r ≤ 1 := by
  unfold wt; rw [Real.exp_le_one_iff]; have := pow_nonneg hr 3; linarith

lemma wt_zero : wt 0 = 1 := by simp [wt]

lemma contDiff_wt : ContDiff ℝ ∞ wt := by
  unfold wt; fun_prop

lemma hasDerivAt_wt (r : ℝ) : HasDerivAt wt (-(r ^ 2) * wt r) r := by
  unfold wt
  have h : HasDerivAt (fun r : ℝ => -(r ^ 3 / 3)) (-(r ^ 2)) r := by
    have := ((hasDerivAt_pow 3 r).div_const 3).neg
    convert this using 1; push_cast; ring
  have := h.exp
  convert this using 1; ring

/-- `r ↦ rⁿ e^{-r³/3}` is integrable on `(0,∞)`. -/
lemma integrableOn_pow_mul_wt (n : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ n * wt r) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 3) (s := n) (b := 1/3)
    (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) (by norm_num) (by norm_num)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp only [wt]
  rw [Real.rpow_natCast]
  congr 2
  rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- The moments `∫₀^∞ rⁿ e^{-r³/3} dr`. -/
def mom (n : ℕ) : ℝ := ∫ r in Ioi (0:ℝ), r ^ n * wt r

lemma mom_nonneg (n : ℕ) : 0 ≤ mom n :=
  setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg (pow_nonneg (le_of_lt hr) n)
    (wt_pos r).le)

lemma mom_pos (n : ℕ) : 0 < mom n := by
  unfold mom
  rw [integral_pos_iff_support_of_nonneg_ae]
  · have : Ioi (0:ℝ) ⊆ Function.support (fun r : ℝ => r ^ n * wt r) := by
      intro r hr
      exact (mul_pos (pow_pos hr n) (wt_pos r)).ne'
    have h2 : Ioi (0:ℝ) ∩ Function.support (fun r : ℝ => r ^ n * wt r) = Ioi 0 :=
      inter_eq_left.2 this
    rw [Measure.restrict_apply' measurableSet_Ioi, inter_comm, h2]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (pow_nonneg (le_of_lt hr) n) (wt_pos r).le
  · exact integrableOn_pow_mul_wt n

/-- `∫₀^∞ r² e^{-r³/3} dr = 1`. -/
lemma mom_two : mom 2 = 1 := by
  unfold mom
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun r => -wt r) (x ^ 2 * wt x) x := by
    intro x _
    have := (hasDerivAt_wt x).neg
    convert this using 1; ring
  have hlim : Tendsto (fun r => -wt r) atTop (𝓝 0) := by
    have : Tendsto (fun r : ℝ => -(r ^ 3 / 3)) atTop atBot := by
      apply tendsto_neg_atTop_atBot.comp
      exact (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
    have h2 := Real.tendsto_exp_atBot.comp this
    simpa [wt] using h2.neg
  have hcont : ContinuousWithinAt (fun r => -wt r) (Ici 0) 0 :=
    (contDiff_wt.continuous.neg).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (integrableOn_pow_mul_wt 2) hlim]
  simp [wt_zero]

/-- The integrand of `Jn n y`. -/
def Jint (n : ℕ) (y r : ℝ) : ℂ :=
  (-(I * r)) ^ n * (wt r : ℂ) * Complex.exp (-((r * y : ℝ) : ℂ) * I)

/-- `Jn n y = ∫₀^∞ (-ir)ⁿ e^{-r³/3} e^{-iry} dr`; it is the `n`-th derivative of `J`. -/
def Jn (n : ℕ) (y : ℝ) : ℂ := ∫ r in Ioi (0:ℝ), Jint n y r

/-- The profile `J(y) = ∫₀^∞ e^{-r³/3} e^{-iry} dr` of display (2.6). -/
def J (y : ℝ) : ℂ := ∫ r in Ioi (0:ℝ), (wt r : ℂ) * Complex.exp (-((r * y : ℝ) : ℂ) * I)

lemma J_eq_Jn (y : ℝ) : J y = Jn 0 y := by
  simp [J, Jn, Jint]

lemma norm_exp_neg_ofReal_mul_I (t : ℝ) : ‖Complex.exp (-(t : ℂ) * I)‖ = 1 := by
  rw [show -(t : ℂ) * I = ((-t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_Jint (n : ℕ) (y r : ℝ) : ‖Jint n y r‖ = |r| ^ n * wt r := by
  simp only [Jint, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_mul,
    norm_exp_neg_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (wt_pos r)]

lemma continuous_Jint (n : ℕ) (y : ℝ) : Continuous (Jint n y) := by
  unfold Jint wt; fun_prop

lemma integrableOn_Jint (n : ℕ) (y : ℝ) : IntegrableOn (Jint n y) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_pow_mul_wt n) (continuous_Jint n y).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [norm_Jint, abs_of_pos hr]

lemma norm_Jn_le (n : ℕ) (y : ℝ) : ‖Jn n y‖ ≤ mom n := by
  unfold Jn mom
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  simp only [norm_Jint, abs_of_pos (show (0:ℝ) < r from hr)]

lemma hasDerivAt_Jint (n : ℕ) (y r : ℝ) :
    HasDerivAt (fun y => Jint n y r) (Jint (n + 1) y r) y := by
  unfold Jint
  have h1 : HasDerivAt (fun y : ℝ => -((r * y : ℝ) : ℂ) * I) (-(r : ℂ) * I) y := by
    have : HasDerivAt (fun y : ℝ => ((r * y : ℝ) : ℂ)) (r : ℂ) y := by
      have := ((hasDerivAt_id y).const_mul r).ofReal_comp
      simpa using this
    convert (this.neg.mul_const I) using 1
  have h2 := h1.cexp
  have h3 := h2.const_mul ((-(I * r)) ^ n * (wt r : ℂ))
  convert h3 using 1
  ring

lemma hasDerivAt_Jn (n : ℕ) (y : ℝ) : HasDerivAt (Jn n) (Jn (n + 1) y) y := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun y r => Jint n y r) (F' := fun y r => Jint (n + 1) y r) (x₀ := y)
    (bound := fun r => r ^ (n + 1) * wt r) (s := univ) univ_mem
    (Eventually.of_forall (fun y => (continuous_Jint n y).aestronglyMeasurable))
    (integrableOn_Jint n y) (continuous_Jint (n + 1) y).aestronglyMeasurable ?_
    (integrableOn_pow_mul_wt (n + 1)) ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    intro x _
    rw [norm_Jint, abs_of_pos hr]
  · exact Eventually.of_forall (fun r x _ => hasDerivAt_Jint n x r)

lemma deriv_Jn (n : ℕ) : deriv (Jn n) = Jn (n + 1) := by
  funext y; exact (hasDerivAt_Jn n y).deriv

lemma differentiable_Jn (n : ℕ) : Differentiable ℝ (Jn n) :=
  fun y => (hasDerivAt_Jn n y).differentiableAt

lemma continuous_Jn (n : ℕ) : Continuous (Jn n) := (differentiable_Jn n).continuous

lemma iteratedDeriv_Jn (n m : ℕ) : iteratedDeriv m (Jn n) = Jn (n + m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ, ih, deriv_Jn]; rfl

lemma contDiff_Jn (n : ℕ) : ContDiff ℝ ∞ (Jn n) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_Jn]
  exact differentiable_Jn _

lemma contDiff_J : ContDiff ℝ ∞ J := by
  have : J = Jn 0 := funext J_eq_Jn
  rw [this]; exact contDiff_Jn 0

lemma hasDerivAt_J (y : ℝ) : HasDerivAt J (Jn 1 y) y := by
  have : J = Jn 0 := funext J_eq_Jn
  rw [this]; exact hasDerivAt_Jn 0 y

/-- Display (2.10): `J''(0) = -∫₀^∞ r² e^{-r³/3} dr = -1`. -/
lemma Jn_two_zero : Jn 2 0 = -1 := by
  have h : ∀ r : ℝ, Jint 2 0 r = -((r ^ 2 * wt r : ℝ) : ℂ) := by
    intro r
    simp only [Jint, mul_zero, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero,
      mul_one]
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  unfold Jn
  simp_rw [h]
  rw [integral_neg, integral_complex_ofReal]
  have := mom_two
  unfold mom at this
  rw [this]; simp

/-- Display (2.9) at the level of bounds: `|J''| ≤ 1`. -/
lemma norm_Jn_two_le (y : ℝ) : ‖Jn 2 y‖ ≤ 1 := by
  have := norm_Jn_le 2 y; rwa [mom_two] at this

/-- The Airy-type identity `J''(y) - i y J(y) = -1`, obtained by differentiating the integrand
in `r` (the rescaled version of `I_N'' - iNη I_N = -1`). -/
lemma Jn_two_sub (y : ℝ) : Jn 2 y - I * y * Jn 0 y = -1 := by
  -- the primitive `E(r) = e^{-r³/3} e^{-iry}`
  set E : ℝ → ℂ := fun r => (wt r : ℂ) * Complex.exp (-((r * y : ℝ) : ℂ) * I) with hE
  have hE' : ∀ r : ℝ, HasDerivAt E (Jint 2 y r - I * y * Jint 0 y r) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => (wt r : ℂ)) ((-(r ^ 2) * wt r : ℝ) : ℂ) r :=
      (hasDerivAt_wt r).ofReal_comp
    have h2 : HasDerivAt (fun r : ℝ => -((r * y : ℝ) : ℂ) * I) (-(y : ℂ) * I) r := by
      have : HasDerivAt (fun r : ℝ => ((r * y : ℝ) : ℂ)) (y : ℂ) r := by
        have := ((hasDerivAt_id r).mul_const y).ofReal_comp
        simpa using this
      convert (this.neg.mul_const I) using 1
    have h3 := h1.mul h2.cexp
    convert h3 using 1
    simp only [Jint, pow_zero, one_mul]
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  have hlim : Tendsto E atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : ∀ r, ‖E r‖ = wt r := by
      intro r
      simp only [hE, norm_mul, norm_exp_neg_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (wt_pos r)]
    simp_rw [this]
    have : Tendsto (fun r : ℝ => -(r ^ 3 / 3)) atTop atBot := by
      apply tendsto_neg_atTop_atBot.comp
      exact (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
    exact Real.tendsto_exp_atBot.comp this
  have hint : IntegrableOn (fun r => Jint 2 y r - I * y * Jint 0 y r) (Ioi 0) :=
    (integrableOn_Jint 2 y).sub ((integrableOn_Jint 0 y).const_mul _)
  have hcont : ContinuousWithinAt E (Ici 0) 0 := by
    have : Continuous E := by rw [hE]; unfold wt; fun_prop
    exact this.continuousWithinAt
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun r _ => hE' r) hint hlim
  have hE0 : E 0 = 1 := by simp [hE, wt_zero]
  rw [hE0, integral_sub (integrableOn_Jint 2 y) ((integrableOn_Jint 0 y).const_mul _),
    integral_const_mul] at key
  unfold Jn
  rw [key]; ring

/-- The Riemann–Lebesgue lemma for `J''`: `J''(y) → 0` as `y → ∞`. -/
lemma tendsto_Jn_two : Tendsto (Jn 2) atTop (𝓝 0) := by
  set φ : ℝ → ℂ := (Ioi (0:ℝ)).indicator (fun r => (-(I * r)) ^ 2 * (wt r : ℂ)) with hφ
  have hrep : ∀ y : ℝ, Jn 2 y = FourierTransform.fourier φ (y / (2 * π)) := by
    intro y
    rw [Real.fourier_real_eq]
    rw [show (fun v : ℝ => (Real.fourierChar (-(v * (y / (2 * π))))) • φ v) =
        (Ioi (0:ℝ)).indicator (fun r => Jint 2 y r) from ?_]
    · rw [integral_indicator measurableSet_Ioi]; rfl
    funext v
    by_cases hv : v ∈ Ioi (0:ℝ)
    · rw [hφ, indicator_of_mem hv, indicator_of_mem hv, Circle.smul_def,
        Real.fourierChar_apply, smul_eq_mul]
      simp only [Jint]
      have : (↑(2 * π * -(v * (y / (2 * π)))) : ℂ) * I = -((v * y : ℝ) : ℂ) * I := by
        congr 1
        push_cast
        field_simp
      rw [this]; ring
    · rw [hφ, indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]
  have h1 := Real.zero_at_infty_fourier φ
  have h2 : Tendsto (fun y : ℝ => y / (2 * π)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have := h1.comp h2
  simpa [Function.comp_def, ← hrep] using this

/-- `C₀ = ∫₀^∞ e^{-r³/3} dr`. -/
def C0 : ℝ := mom 0

lemma C0_eq : C0 = ∫ r in Ioi (0:ℝ), Real.exp (-(r ^ 3 / 3)) := by
  simp [C0, mom, wt]

/-- `C₀ = 3^{-2/3} Γ(1/3)`. -/
lemma C0_eq_Gamma : C0 = (3:ℝ) ^ (-(2/3 : ℝ)) * Real.Gamma (1/3) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := 0) (b := 1/3)
    (by norm_num) (by norm_num) (by norm_num)
  have h' : ∫ x in Ioi (0:ℝ), x ^ (0:ℝ) * Real.exp (-(1/3) * x ^ (3:ℝ)) = C0 := by
    unfold C0 mom
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    simp only [Real.rpow_zero, one_mul, pow_zero, wt]
    congr 1
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [h'] at h
  rw [h]
  have e1 : ((1:ℝ)/3) ^ (-((0:ℝ) + 1) / 3) = (3:ℝ) ^ ((1:ℝ)/3) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  rw [e1, show ((0:ℝ) + 1) / 3 = 1/3 by ring]
  have e2 : (3:ℝ) ^ ((1:ℝ)/3) * (1/3) = (3:ℝ) ^ (-(2/3:ℝ)) := by
    rw [show (-(2/3:ℝ)) = 1/3 - 1 by ring, Real.rpow_sub (by norm_num), Real.rpow_one]
    ring
  rw [← e2]

lemma C0_pos : 0 < C0 := mom_pos 0

/-- `|J| ≤ C₀`. -/
lemma norm_J_le (y : ℝ) : ‖J y‖ ≤ C0 := by
  rw [J_eq_Jn]; exact norm_Jn_le 0 y

/-! ### The one-frequency integral `I_N` -/

/-- `I_N(η) = ∫₀^∞ exp(-N²s³/3) e^{-iNsη} ds`, display (2.3). -/
def IN (N η : ℝ) : ℂ :=
  ∫ s in Ioi (0:ℝ), (Real.exp (-(N ^ 2 * s ^ 3 / 3)) : ℂ) * Complex.exp (-((N * s * η : ℝ) : ℂ) * I)

/-- The real cube root `N^{1/3}`. -/
def cbrt (N : ℝ) : ℝ := N ^ ((1:ℝ)/3)

lemma cbrt_pos {N : ℝ} (hN : 0 < N) : 0 < cbrt N := Real.rpow_pos_of_pos hN _

lemma cbrt_pow_three {N : ℝ} (hN : 0 ≤ N) : cbrt N ^ 3 = N := by
  unfold cbrt
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]; norm_num

/-- Display (2.7): `I_N(η) = N^{-2/3} J(N^{1/3} η)`, written with `a = N^{1/3}`. -/
lemma IN_eq {N : ℝ} (hN : 0 < N) (η : ℝ) :
    IN N η = ((cbrt N ^ 2)⁻¹ : ℝ) * J (cbrt N * η) := by
  set a := cbrt N with ha
  have ha0 : 0 < a := cbrt_pos hN
  have ha3 : a ^ 3 = N := cbrt_pow_three hN.le
  have hb : 0 < a ^ 2 := by positivity
  -- substitute `s = r / a²`, i.e. `r = a² s`
  have key := integral_comp_mul_left_Ioi
    (fun r : ℝ => (wt r : ℂ) * Complex.exp (-((r * (a * η) : ℝ) : ℂ) * I)) 0 hb
  simp only [mul_zero] at key
  unfold IN
  have hcongr : ∀ s : ℝ, (Real.exp (-(N ^ 2 * s ^ 3 / 3)) : ℂ) *
      Complex.exp (-((N * s * η : ℝ) : ℂ) * I) =
      (wt (a ^ 2 * s) : ℂ) * Complex.exp (-(((a ^ 2 * s) * (a * η) : ℝ) : ℂ) * I) := by
    intro s
    have e1 : -(N ^ 2 * s ^ 3 / 3) = -((a ^ 2 * s) ^ 3 / 3) := by rw [← ha3]; ring
    have e2 : N * s * η = (a ^ 2 * s) * (a * η) := by rw [← ha3]; ring
    simp only [wt, e1, e2]
  simp_rw [hcongr]
  rw [key]
  unfold J
  rw [Complex.real_smul]

end KS

end -- (the file's `noncomputable section`)

end File_Profile

-- ============================================================================
-- KineticCounterexamples/Setup.lean
-- ============================================================================

section File_Setup

/-!
# Kinetic cylinders, Hölder seminorms and the velocity-only Schauder conjecture

We fix the notation of Section 1 of Dong–Wang, *Several counterexamples to kinetic Schauder
estimates*:

* `Q d r = (-r², 0] × B_{r³} × B_r ⊂ ℝ × ℝᵈ × ℝᵈ` (kinetic cylinders);
* the velocity Hölder seminorm
  `[h]_{C^α_v(Q)} = sup { |h(t,x,v) - h(t,x,v')| / |v-v'|^α : (t,x,v),(t,x,v') ∈ Q,
     0 < |v-v'| < 1/2 }`, valued in `ℝ≥0∞` (so that an unbounded quotient gives `∞`);
  for matrix-valued functions the Frobenius norm is used;
* the analogous spatial seminorm `[h]_{C^β_x(Q)}`;
* partial derivatives `∂_t`, `∇_x`, the velocity Hessian `D_v² f`;
* Conjecture 1.1 (= [Henderson–Wang, Conjecture 1.3]) as a proposition `Conj11 d α Λ`.

The supremum norm `‖f‖_{L∞(Q)}` is taken as a pointwise supremum over `Q`; since it dominates
the essential supremum, our formal conjecture is implied by the one in the paper, so its
negation is (at least) as strong as the paper's claim.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace KS

/-- `ℝᵈ` with the Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Points `(t, x, v)` of `ℝ × ℝᵈ × ℝᵈ`. -/
abbrev Pt (d : ℕ) := ℝ × E d × E d

variable {d : ℕ}

/-- The kinetic cylinder `Q_r = (-r², 0] × B_{r³} × B_r`. -/
def Q (d : ℕ) (r : ℝ) : Set (Pt d) :=
  {p | p.1 ∈ Ioc (-r ^ 2) 0 ∧ p.2.1 ∈ Metric.ball (0 : E d) (r ^ 3) ∧
    p.2.2 ∈ Metric.ball (0 : E d) r}

lemma mem_Q {r t : ℝ} {x v : E d} :
    (t, x, v) ∈ Q d r ↔ (-r ^ 2 < t ∧ t ≤ 0) ∧ ‖x‖ < r ^ 3 ∧ ‖v‖ < r := by
  simp [Q, mem_Ioc]

/-- The `i`-th standard basis vector. -/
abbrev ev (i : Fin d) : E d := EuclideanSpace.single i 1

/-- Time derivative `∂_t F`. -/
def dT (F : Pt d → ℝ) (p : Pt d) : ℝ := deriv (fun s => F (s, p.2.1, p.2.2)) p.1

/-- Spatial gradient `∇_x F` (as a linear functional). -/
def gradX (F : Pt d → ℝ) (p : Pt d) : E d →L[ℝ] ℝ := fderiv ℝ (fun y => F (p.1, y, p.2.2)) p.2.1

/-- Velocity gradient `∇_v F` (as a linear functional). -/
def gradV (F : Pt d → ℝ) (p : Pt d) : E d →L[ℝ] ℝ := fderiv ℝ (fun w => F (p.1, p.2.1, w)) p.2.2

/-- The velocity Hessian `(D_v² F)_{ij} = ∂_{v_i} ∂_{v_j} F`. -/
def hessV (F : Pt d → ℝ) (p : Pt d) : Matrix (Fin d) (Fin d) ℝ := fun i j =>
  fderiv ℝ (fun w => fderiv ℝ (fun w' => F (p.1, p.2.1, w')) w (ev j)) p.2.2 (ev i)

/-- The kinetic transport term `v · ∇_x F`. -/
def transport (F : Pt d → ℝ) (p : Pt d) : ℝ := gradX F p p.2.2

/-- The Frobenius norm `|M| = (∑ Mᵢⱼ²)^{1/2}`. -/
def frob (M : Matrix (Fin d) (Fin d) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)

lemma frob_nonneg (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ frob M := Real.sqrt_nonneg _

lemma abs_le_frob (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) : |M i j| ≤ frob M := by
  unfold frob
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h1 : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  linarith

/-- The Frobenius norm of a matrix whose only possibly nonzero entry is at `(i₀,i₀)`. -/
lemma frob_single (i₀ : Fin d) (a : ℝ) :
    frob (fun i j => if i = i₀ ∧ j = i₀ then a else 0 : Matrix (Fin d) (Fin d) ℝ) = |a| := by
  unfold frob
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]
  · simp

lemma frob_le_of_entries (M : Matrix (Fin d) (Fin d) ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i j, |M i j| ≤ K) : frob M ≤ d * K := by
  unfold frob
  have hsum : ∑ i, ∑ j, M i j ^ 2 ≤ (d * K) ^ 2 := by
    calc ∑ i, ∑ j, M i j ^ 2 ≤ ∑ _i : Fin d, ∑ _j : Fin d, K ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          have := h i j
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (d * K) ^ 2 := by simp; ring
  calc Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤ Real.sqrt ((d * K) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = d * K := Real.sqrt_sq (by positivity)

/-! ### Hölder seminorms and sup norms (valued in `ℝ≥0∞`) -/

/-- A generic velocity Hölder seminorm, for a given "distance" `δ` on the target. -/
def semVg {F : Type*} (δ : F → F → ℝ) (α : ℝ) (S : Set (Pt d)) (h : Pt d → F) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (x : E d) (v : E d) (v' : E d) (_ : (t, x, v) ∈ S) (_ : (t, x, v') ∈ S)
    (_ : 0 < ‖v - v'‖) (_ : ‖v - v'‖ < 1 / 2),
    ENNReal.ofReal (δ (h (t, x, v)) (h (t, x, v')) / ‖v - v'‖ ^ α)

/-- The velocity Hölder seminorm `[h]_{C^α_v(S)}` of a real function. -/
def semR (α : ℝ) (S : Set (Pt d)) (h : Pt d → ℝ) : ℝ≥0∞ :=
  semVg (fun a b : ℝ => |a - b|) α S h

/-- The velocity Hölder seminorm `[h]_{C^α_v(S)}` of a matrix function (Frobenius norm). -/
def semM (α : ℝ) (S : Set (Pt d)) (h : Pt d → Matrix (Fin d) (Fin d) ℝ) : ℝ≥0∞ :=
  semVg (fun A B : Matrix (Fin d) (Fin d) ℝ => frob (A - B)) α S h

/-- The spatial Hölder seminorm `[h]_{C^β_x(S)}` of a real function. -/
def semX (β : ℝ) (S : Set (Pt d)) (h : Pt d → ℝ) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (x : E d) (x' : E d) (v : E d) (_ : (t, x, v) ∈ S) (_ : (t, x', v) ∈ S)
    (_ : 0 < ‖x - x'‖) (_ : ‖x - x'‖ < 1 / 2),
    ENNReal.ofReal (|h (t, x, v) - h (t, x', v)| / ‖x - x'‖ ^ β)

/-- The supremum norm `‖h‖_{L∞(S)}` (pointwise supremum). -/
def supN (S : Set (Pt d)) (h : Pt d → ℝ) : ℝ≥0∞ := ⨆ (p : Pt d) (_ : p ∈ S), ENNReal.ofReal |h p|

/-- The supremum of the Frobenius norm over `S`. -/
def supNM (S : Set (Pt d)) (h : Pt d → Matrix (Fin d) (Fin d) ℝ) : ℝ≥0∞ :=
  ⨆ (p : Pt d) (_ : p ∈ S), ENNReal.ofReal (frob (h p))

lemma le_semVg {F : Type*} (δ : F → F → ℝ) (α : ℝ) (S : Set (Pt d)) (h : Pt d → F)
    {t : ℝ} {x v v' : E d} (h1 : (t, x, v) ∈ S) (h2 : (t, x, v') ∈ S)
    (h3 : 0 < ‖v - v'‖) (h4 : ‖v - v'‖ < 1 / 2) :
    ENNReal.ofReal (δ (h (t, x, v)) (h (t, x, v')) / ‖v - v'‖ ^ α) ≤ semVg δ α S h := by
  unfold semVg
  refine le_trans ?_ (le_iSup _ t)
  refine le_trans ?_ (le_iSup _ x)
  refine le_trans ?_ (le_iSup _ v)
  refine le_trans ?_ (le_iSup _ v')
  refine le_trans ?_ (le_iSup _ h1)
  refine le_trans ?_ (le_iSup _ h2)
  refine le_trans ?_ (le_iSup _ h3)
  exact le_trans (le_refl _) (le_iSup_of_le h4 (le_refl _))

lemma semVg_le {F : Type*} (δ : F → F → ℝ) (α : ℝ) (S : Set (Pt d)) (h : Pt d → F) (M : ℝ)
    (hM : ∀ t x v v', (t, x, v) ∈ S → (t, x, v') ∈ S → 0 < ‖v - v'‖ → ‖v - v'‖ < 1 / 2 →
      δ (h (t, x, v)) (h (t, x, v')) / ‖v - v'‖ ^ α ≤ M) :
    semVg δ α S h ≤ ENNReal.ofReal M := by
  unfold semVg
  refine iSup_le fun t => iSup_le fun x => iSup_le fun v => iSup_le fun v' => ?_
  refine iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 => iSup_le fun h4 => ?_
  exact ENNReal.ofReal_le_ofReal (hM t x v v' h1 h2 h3 h4)

lemma le_semX (β : ℝ) (S : Set (Pt d)) (h : Pt d → ℝ)
    {t : ℝ} {x x' v : E d} (h1 : (t, x, v) ∈ S) (h2 : (t, x', v) ∈ S)
    (h3 : 0 < ‖x - x'‖) (h4 : ‖x - x'‖ < 1 / 2) :
    ENNReal.ofReal (|h (t, x, v) - h (t, x', v)| / ‖x - x'‖ ^ β) ≤ semX β S h := by
  unfold semX
  refine le_trans ?_ (le_iSup _ t)
  refine le_trans ?_ (le_iSup _ x)
  refine le_trans ?_ (le_iSup _ x')
  refine le_trans ?_ (le_iSup _ v)
  refine le_trans ?_ (le_iSup _ h1)
  refine le_trans ?_ (le_iSup _ h2)
  refine le_trans ?_ (le_iSup _ h3)
  exact le_trans (le_refl _) (le_iSup_of_le h4 (le_refl _))

lemma semX_le (β : ℝ) (S : Set (Pt d)) (h : Pt d → ℝ) (M : ℝ)
    (hM : ∀ t x x' v, (t, x, v) ∈ S → (t, x', v) ∈ S → 0 < ‖x - x'‖ → ‖x - x'‖ < 1 / 2 →
      |h (t, x, v) - h (t, x', v)| / ‖x - x'‖ ^ β ≤ M) :
    semX β S h ≤ ENNReal.ofReal M := by
  unfold semX
  refine iSup_le fun t => iSup_le fun x => iSup_le fun x' => iSup_le fun v => ?_
  refine iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 => iSup_le fun h4 => ?_
  exact ENNReal.ofReal_le_ofReal (hM t x x' v h1 h2 h3 h4)

lemma le_supN (S : Set (Pt d)) (h : Pt d → ℝ) {p : Pt d} (hp : p ∈ S) :
    ENNReal.ofReal |h p| ≤ supN S h :=
  le_trans (le_refl _) (le_iSup_of_le p (le_iSup_of_le hp (le_refl _)))

lemma supN_le (S : Set (Pt d)) (h : Pt d → ℝ) (M : ℝ) (hM : ∀ p ∈ S, |h p| ≤ M) :
    supN S h ≤ ENNReal.ofReal M :=
  iSup_le fun p => iSup_le fun hp => ENNReal.ofReal_le_ofReal (hM p hp)

lemma supNM_le (S : Set (Pt d)) (h : Pt d → Matrix (Fin d) (Fin d) ℝ) (M : ℝ)
    (hM : ∀ p ∈ S, frob (h p) ≤ M) : supNM S h ≤ ENNReal.ofReal M :=
  iSup_le fun p => iSup_le fun hp => ENNReal.ofReal_le_ofReal (hM p hp)

/-- A function independent of `v` has zero velocity seminorm. -/
lemma semR_eq_zero_of_indep (α : ℝ) (S : Set (Pt d)) (h : Pt d → ℝ)
    (hh : ∀ t x v v', h (t, x, v) = h (t, x, v')) : semR α S h = 0 := by
  apply le_antisymm _ zero_le
  have := semVg_le (fun a b : ℝ => |a - b|) α S h 0 (fun t x v v' _ _ _ _ => by
    simp [hh t x v v'])
  simpa [semR] using this

lemma semM_eq_zero_of_indep (α : ℝ) (S : Set (Pt d)) (h : Pt d → Matrix (Fin d) (Fin d) ℝ)
    (hh : ∀ t x v v', h (t, x, v) = h (t, x, v')) : semM α S h = 0 := by
  apply le_antisymm _ zero_le
  have := semVg_le (fun A B : Matrix (Fin d) (Fin d) ℝ => frob (A - B)) α S h 0
    (fun t x v v' _ _ _ _ => by simp [hh t x v v', frob])
  simpa [semM] using this

/-! ### Conjecture 1.1 -/

/-- Membership in `C^α_v(S)` for a real function: bounded with finite velocity seminorm. -/
def InCv (α : ℝ) (S : Set (Pt d)) (h : Pt d → ℝ) : Prop := supN S h < ⊤ ∧ semR α S h < ⊤

/-- Membership in `C^α_v(S)` for a matrix-valued function. -/
def InCvM (α : ℝ) (S : Set (Pt d)) (h : Pt d → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  supNM S h < ⊤ ∧ semM α S h < ⊤

/-- Uniform ellipticity `Λ⁻¹ Id ≤ a ≤ Λ Id` in the Loewner order. -/
def Elliptic (Λ : ℝ) (a : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (a - Λ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    (Λ • (1 : Matrix (Fin d) (Fin d) ℝ) - a).PosSemidef

/-- The kinetic Fokker–Planck equation (1.1) `(∂_t + v·∇_x) f = tr(a D_v² f) + c f + g` at `p`. -/
def KFP (f : Pt d → ℝ) (a : Pt d → Matrix (Fin d) (Fin d) ℝ) (c g : Pt d → ℝ) (p : Pt d) : Prop :=
  dT f p + transport f p = Matrix.trace (a p * hessV f p) + c p * f p + g p

/-- **Conjecture 1.1** ([Henderson–Wang, Conjecture 1.3]) for given `d, α, Λ`: there is a constant
`C` such that every smooth solution of (1.1) in `Q₁` with `Λ⁻¹ ≤ a ≤ Λ`, `|c|, |g| ≤ Λ`, and
`f, D_v² f, a, c, g ∈ C^α_v(Q₁)` obeys the estimate (1.2). -/
def Conj11 (d : ℕ) (α Λ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (f c g : Pt d → ℝ) (a : Pt d → Matrix (Fin d) (Fin d) ℝ),
    ContDiff ℝ ∞ f →
    (∀ p ∈ Q d 1, Elliptic Λ (a p)) → (∀ p ∈ Q d 1, |c p| ≤ Λ) → (∀ p ∈ Q d 1, |g p| ≤ Λ) →
    InCv α (Q d 1) f → InCvM α (Q d 1) (hessV f) → InCvM α (Q d 1) a →
    InCv α (Q d 1) c → InCv α (Q d 1) g →
    (∀ p ∈ Q d 1, KFP f a c g p) →
    semM α (Q d (1/2)) (hessV f) ≤
      ENNReal.ofReal C * (1 + semR α (Q d 1) c + semM α (Q d 1) a ^ (1 + 2 / α)) *
          supN (Q d 1) f +
        ENNReal.ofReal C * (1 + semM α (Q d 1) a) * semR α (Q d 1) g

end KS

end -- (the file's `noncomputable section`)

end File_Setup

-- ============================================================================
-- KineticCounterexamples/OneFreq.lean
-- ============================================================================

section File_OneFreq

/-!
# The one-frequency solutions `f_N = Re(e^{iNx₁} I_N(v₁))`

Display (2.4) of Dong–Wang: `F_N(x,v) = e^{iNx₁} I_N(v₁)`, `f_N = Re F_N`, `g_N = cos(Nx₁)`.
We compute all derivatives entering the kinetic equation and prove that `f_N` is a smooth
stationary solution of `(∂_t + v·∇_x) f_N = Δ_v f_N + g_N` on all of `ℝ × ℝᵈ × ℝᵈ`.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace KS

variable {d : ℕ}

/-! ### Calculus helpers -/

lemma hasFDerivAt_coord (i : Fin d) (w : E d) :
    HasFDerivAt (fun w : E d => w i) (EuclideanSpace.proj i : E d →L[ℝ] ℝ) w :=
  (EuclideanSpace.proj i : E d →L[ℝ] ℝ).hasFDerivAt

lemma hasFDerivAt_comp_coord {h : ℝ → ℝ} {h' : ℝ} {i : Fin d} {w : E d}
    (hh : HasDerivAt h h' (w i)) :
    HasFDerivAt (fun w : E d => h (w i)) (h' • (EuclideanSpace.proj i : E d →L[ℝ] ℝ)) w := by
  exact hh.comp_hasFDerivAt w (hasFDerivAt_coord i w)

lemma fderiv_comp_coord_apply {h : ℝ → ℝ} {h' : ℝ} {i : Fin d} {w : E d}
    (hh : HasDerivAt h h' (w i)) (u : E d) :
    fderiv ℝ (fun w : E d => h (w i)) w u = h' * u i := by
  rw [(hasFDerivAt_comp_coord hh).fderiv]
  simp

lemma ev_apply (i j : Fin d) : (ev i : E d) j = if j = i then 1 else 0 := by
  simp [ev, PiLp.single_apply]

/-- Real part of a complex-valued derivative. -/
lemma HasDerivAt.re_of {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x := by
  have := (Complex.reCLM.hasFDerivAt (x := f x)).comp_hasDerivAt x h
  simpa only [Function.comp_def, Complex.reCLM_apply] using this

/-- Derivative of `η ↦ Re(z · Jn k (a η))`. -/
lemma hasDerivAt_re_Jn (z : ℂ) (a : ℝ) (k : ℕ) (η : ℝ) :
    HasDerivAt (fun η => (z * Jn k (a * η)).re) ((z * a * Jn (k + 1) (a * η)).re) η := by
  have h1 : HasDerivAt (fun η : ℝ => Jn k (a * η)) ((a : ℂ) * Jn (k + 1) (a * η)) η := by
    have h0 : HasDerivAt (fun η : ℝ => a * η) a η := by
      simpa using (hasDerivAt_id η).const_mul a
    have := (hasDerivAt_Jn k (a * η)).scomp η h0
    simpa [Function.comp_def, Complex.real_smul] using this
  have h2 := HasDerivAt.re_of (h1.const_mul z)
  rw [show z * a * Jn (k + 1) (a * η) = z * ((a : ℂ) * Jn (k + 1) (a * η)) by ring]
  exact h2

/-! ### The one-frequency solution -/

/-- The cube root `a = N^{1/3}` and `N^{-2/3} = (a²)⁻¹`. -/
lemma cbrt_sq_inv {N : ℝ} (hN : 0 < N) : (cbrt N ^ 2)⁻¹ = N ^ (-(2/3 : ℝ)) := by
  unfold cbrt
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, Real.rpow_neg hN.le]
  norm_num

lemma cbrt_rpow {N : ℝ} (hN : 0 < N) (α : ℝ) : cbrt N ^ α = N ^ (α / 3) := by
  unfold cbrt
  rw [← Real.rpow_mul hN.le]; congr 1; ring

variable [NeZero d]

/-- `f_N(t,x,v) = Re(e^{iNx₁} I_N(v₁))` (display (2.4)). -/
def fN (d : ℕ) [NeZero d] (N : ℝ) (p : Pt d) : ℝ :=
  (Complex.exp (I * ((N * p.2.1 0 : ℝ) : ℂ)) * IN N (p.2.2 0)).re

/-- `g_N(t,x,v) = cos(N x₁)` (display (2.4)). -/
def gN (d : ℕ) [NeZero d] (N : ℝ) (p : Pt d) : ℝ := Real.cos (N * p.2.1 0)

/-- The phase `e^{iNx₁}` times `(a²)⁻¹`. -/
def zN (N x₁ : ℝ) : ℂ := Complex.exp (I * ((N * x₁ : ℝ) : ℂ)) * (((cbrt N ^ 2)⁻¹ : ℝ) : ℂ)

lemma fN_eq {N : ℝ} (hN : 0 < N) (p : Pt d) :
    fN d N p = (zN N (p.2.1 0) * Jn 0 (cbrt N * p.2.2 0)).re := by
  unfold fN zN
  rw [IN_eq hN, J_eq_Jn]
  ring_nf

lemma norm_exp_I_mul (θ : ℝ) : ‖Complex.exp (I * (θ : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ

lemma norm_zN {N : ℝ} (hN : 0 < N) (x₁ : ℝ) : ‖zN N x₁‖ = (cbrt N ^ 2)⁻¹ := by
  unfold zN
  rw [norm_mul, norm_exp_I_mul, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by have := cbrt_pos hN; positivity)]

lemma re_exp_I_mul (θ : ℝ) : (Complex.exp (I * (θ : ℂ))).re = Real.cos θ := by
  rw [mul_comm, Complex.exp_ofReal_mul_I_re]

/-- The `x₁`-derivative of the phase. -/
lemma hasDerivAt_zN (N x₁ : ℝ) :
    HasDerivAt (fun x₁ => zN N x₁) (I * N * zN N x₁) x₁ := by
  unfold zN
  have h0 : HasDerivAt (fun x₁ : ℝ => I * ((N * x₁ : ℝ) : ℂ)) (I * N) x₁ := by
    have : HasDerivAt (fun x₁ : ℝ => ((N * x₁ : ℝ) : ℂ)) (N : ℂ) x₁ := by
      have := ((hasDerivAt_id x₁).const_mul N).ofReal_comp
      simpa using this
    simpa using this.const_mul I
  have := h0.cexp.mul_const ((((cbrt N ^ 2)⁻¹ : ℝ) : ℂ))
  convert this using 1; ring

lemma contDiff_fN {N : ℝ} (hN : 0 < N) : ContDiff ℝ ∞ (fN d N) := by
  have hfun : fN d N = fun p : Pt d => (zN N (p.2.1 0) * Jn 0 (cbrt N * p.2.2 0)).re :=
    funext (fN_eq hN)
  rw [hfun]
  have hx : ContDiff ℝ ∞ (fun p : Pt d => p.2.1 0) :=
    ((EuclideanSpace.proj (0 : Fin d) : E d →L[ℝ] ℝ).contDiff).comp (contDiff_fst.comp contDiff_snd)
  have hv : ContDiff ℝ ∞ (fun p : Pt d => p.2.2 0) :=
    ((EuclideanSpace.proj (0 : Fin d) : E d →L[ℝ] ℝ).contDiff).comp (contDiff_snd.comp contDiff_snd)
  have hz : ContDiff ℝ ∞ (fun x₁ : ℝ => zN N x₁) := by
    unfold zN
    apply ContDiff.mul _ contDiff_const
    apply Complex.contDiff_exp.comp
    apply ContDiff.mul contDiff_const
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  have hJ : ContDiff ℝ ∞ (fun p : Pt d => Jn 0 (cbrt N * p.2.2 0)) :=
    (contDiff_Jn 0).comp (contDiff_const.mul hv)
  exact Complex.reCLM.contDiff.comp ((hz.comp hx).mul hJ)

lemma contDiff_gN (N : ℝ) : ContDiff ℝ ∞ (gN d N) := by
  unfold gN
  have hx : ContDiff ℝ ∞ (fun p : Pt d => p.2.1 0) :=
    ((EuclideanSpace.proj (0 : Fin d) : E d →L[ℝ] ℝ).contDiff).comp (contDiff_fst.comp contDiff_snd)
  exact Real.contDiff_cos.comp (contDiff_const.mul hx)

lemma abs_fN_le {N : ℝ} (hN : 0 < N) (p : Pt d) : |fN d N p| ≤ C0 * N ^ (-(2/3 : ℝ)) := by
  rw [fN_eq hN]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_zN hN, cbrt_sq_inv hN, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_Jn_le 0 _) (Real.rpow_nonneg hN.le _)

lemma abs_gN_le (N : ℝ) (p : Pt d) : |gN d N p| ≤ 1 := Real.abs_cos_le_one _

/-- `f_N` is stationary. -/
lemma dT_fN (N : ℝ) (p : Pt d) : dT (fN d N) p = 0 := by
  simp [dT, fN]

/-- The transport term: `v · ∇_x f_N = Re(i N v₁ e^{iNx₁} I_N(v₁))`. -/
lemma transport_fN {N : ℝ} (hN : 0 < N) (p : Pt d) :
    transport (fN d N) p = (I * N * zN N (p.2.1 0) * Jn 0 (cbrt N * p.2.2 0)).re * p.2.2 0 := by
  unfold transport gradX
  have hfun : (fun y : E d => fN d N (p.1, y, p.2.2)) =
      fun y : E d => (fun x₁ => (zN N x₁ * Jn 0 (cbrt N * p.2.2 0)).re) (y 0) := by
    funext y; rw [fN_eq hN]
  rw [hfun]
  have hd : HasDerivAt (fun x₁ => (zN N x₁ * Jn 0 (cbrt N * p.2.2 0)).re)
      ((I * N * zN N (p.2.1 0) * Jn 0 (cbrt N * p.2.2 0)).re) (p.2.1 0) := by
    exact HasDerivAt.re_of ((hasDerivAt_zN N (p.2.1 0)).mul_const (Jn 0 (cbrt N * p.2.2 0)))
  rw [fderiv_comp_coord_apply hd]

/-- The velocity Hessian of `f_N`: only the `(1,1)` entry is nonzero, and it equals
`Re(e^{iNx₁} J''(N^{1/3} v₁))` (display (2.8)). -/
lemma hessV_fN {N : ℝ} (hN : 0 < N) (p : Pt d) :
    hessV (fN d N) p = fun i j =>
      if i = 0 ∧ j = 0 then (zN N (p.2.1 0) * (cbrt N) ^ 2 * Jn 2 (cbrt N * p.2.2 0)).re
      else 0 := by
  set a := cbrt N
  set z := zN N (p.2.1 0)
  funext i j
  unfold hessV
  -- first derivative in `v`
  have h1 : ∀ w : E d, fderiv ℝ (fun w' => fN d N (p.1, p.2.1, w')) w (ev j) =
      (z * a * Jn 1 (a * w 0)).re * (if (0 : Fin d) = j then 1 else 0) := by
    intro w
    have hfun : (fun w' : E d => fN d N (p.1, p.2.1, w')) =
        fun w' : E d => (fun η => (z * Jn 0 (a * η)).re) (w' 0) := by
      funext w'; rw [fN_eq hN]
    rw [hfun, fderiv_comp_coord_apply (hasDerivAt_re_Jn z a 0 (w 0)), ev_apply]
  have hfun2 : (fun w : E d => fderiv ℝ (fun w' => fN d N (p.1, p.2.1, w')) w (ev j)) =
      fun w : E d => (fun η => ((z * a) * Jn 1 (a * η)).re * (if (0 : Fin d) = j then 1 else 0))
        (w 0) := by
    funext w; rw [h1 w]
  rw [hfun2]
  have hd : HasDerivAt (fun η => ((z * a) * Jn 1 (a * η)).re * (if (0 : Fin d) = j then 1 else 0))
      (((z * a) * a * Jn 2 (a * p.2.2 0)).re * (if (0 : Fin d) = j then 1 else 0)) (p.2.2 0) :=
    (hasDerivAt_re_Jn (z * a) a 1 (p.2.2 0)).mul_const _
  rw [fderiv_comp_coord_apply hd, ev_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst hi hj
    simp only [ite_true, and_self, mul_one]
    congr 1; ring
  · simp [hi, hj, Ne.symm hj]
  · simp [hi, hj, Ne.symm hi]
  · simp [hi, hj, Ne.symm hi]

/-- The `(1,1)` entry of the Hessian in the form `Re(e^{iNx₁} J''(N^{1/3}v₁))`. -/
lemma hessV_fN_00 {N : ℝ} (hN : 0 < N) (p : Pt d) :
    hessV (fN d N) p 0 0 =
      (Complex.exp (I * ((N * p.2.1 0 : ℝ) : ℂ)) * Jn 2 (cbrt N * p.2.2 0)).re := by
  rw [hessV_fN hN]
  simp only [and_self, ite_true]
  unfold zN
  have ha : cbrt N ^ 2 ≠ 0 := by have := cbrt_pos hN; positivity
  congr 1
  have : (((cbrt N ^ 2)⁻¹ : ℝ) : ℂ) * ((cbrt N : ℂ) ^ 2) = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, inv_mul_cancel₀ ha, Complex.ofReal_one]
  calc Complex.exp (I * ((N * p.2.1 0 : ℝ) : ℂ)) * (((cbrt N ^ 2)⁻¹ : ℝ) : ℂ) * (cbrt N : ℂ) ^ 2 *
        Jn 2 (cbrt N * p.2.2 0)
      = Complex.exp (I * ((N * p.2.1 0 : ℝ) : ℂ)) *
          ((((cbrt N ^ 2)⁻¹ : ℝ) : ℂ) * ((cbrt N : ℂ) ^ 2)) * Jn 2 (cbrt N * p.2.2 0) := by ring
    _ = _ := by rw [this, mul_one]

lemma trace_hessV_fN {N : ℝ} (hN : 0 < N) (p : Pt d) :
    Matrix.trace (hessV (fN d N) p) = hessV (fN d N) p 0 0 := by
  unfold Matrix.trace
  rw [Finset.sum_eq_single 0]
  · rfl
  · intro i _ hi
    simp only [Matrix.diag_apply]
    rw [hessV_fN hN]; simp [hi]
  · simp

/-- **Display (2.1)**: `f_N` solves `(∂_t + v·∇_x) f_N = Δ_v f_N + g_N` everywhere. -/
theorem fN_solves {N : ℝ} (hN : 0 < N) (p : Pt d) :
    dT (fN d N) p + transport (fN d N) p = Matrix.trace (hessV (fN d N) p) + gN d N p := by
  rw [dT_fN, transport_fN hN, trace_hessV_fN hN, hessV_fN_00 hN]
  set a := cbrt N with ha
  have ha0 : 0 < a := cbrt_pos hN
  have ha3 : a ^ 3 = N := cbrt_pow_three hN.le
  set y := a * p.2.2 0 with hy
  set e := Complex.exp (I * ((N * p.2.1 0 : ℝ) : ℂ)) with he
  -- the ODE `J'' = i y J - 1`
  have hode : Jn 2 y = I * y * Jn 0 y - 1 := by have := Jn_two_sub y; linear_combination this
  rw [hode]
  unfold zN gN
  rw [← he]
  have hN' : (N : ℂ) = (a : ℂ) ^ 3 := by rw [← ha3]; push_cast; ring
  set A : ℝ := (a ^ 2)⁻¹ with hAdef
  have hA : (A : ℂ) * (a : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, hAdef, inv_mul_cancel₀ (by positivity),
      Complex.ofReal_one]
  have key : (I * N * (e * (A : ℂ)) * Jn 0 y).re * p.2.2 0 =
      (e * (I * y * Jn 0 y)).re := by
    have : I * N * (e * (A : ℂ)) * Jn 0 y * (p.2.2 0 : ℂ) = e * (I * y * Jn 0 y) := by
      have hy' : (y : ℂ) = (a : ℂ) * (p.2.2 0 : ℂ) := by rw [hy]; push_cast; ring
      rw [hN', hy']
      linear_combination (e * I * (a : ℂ) * (p.2.2 0 : ℂ) * Jn 0 y) * hA
    rw [← this, ← Complex.re_mul_ofReal]
  rw [zero_add, key]
  have : (e * (I * y * Jn 0 y - 1)).re = (e * (I * y * Jn 0 y)).re - e.re := by
    rw [mul_sub, mul_one, Complex.sub_re]
  rw [this, he, re_exp_I_mul]
  ring

end KS

end -- (the file's `noncomputable section`)

end File_OneFreq

-- ============================================================================
-- KineticCounterexamples/Counterexample.lean
-- ============================================================================

section File_Counterexample

/-!
# Theorem 2.1, Remark 2.2 and Proposition 3.1 of Dong–Wang; Conjecture 1.1 is false

* `thm_2_1` — Theorem 2.1: for every `d ≥ 1`, `α ∈ (0,1)` there are `c₀ > 0`, `N₀ ≥ 1` and for
  `N ≥ N₀` smooth stationary solutions `f_N` of `(∂_t + v·∇_x) f_N = Δ_v f_N + g_N` in `Q₁` with
  `‖g_N‖_∞ ≤ 1`, `[g_N]_{C^α_v(Q₁)} = 0`, `‖f_N‖_{L∞(Q₁)} ≤ C₀ N^{-2/3}` and
  `[D_v² f_N]_{C^α_v(Q_{1/2})} ≥ c₀ N^{α/3}`.
* `conj11_false` — the estimate (1.2) is false, i.e. `¬ Conj11 d α Λ`.
* `rem_2_2` — Remark 2.2: adding any term depending only on `‖g‖_{L∞}` does not help.
* `prop_3_1` and `conj11_zero_false` — Proposition 3.1 (zero-forcing variant).
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace KS

variable {d : ℕ}

/-! ### Hölder bounds for the profile -/

lemma norm_Jn_sub_le (k : ℕ) (y y' : ℝ) : ‖Jn k y - Jn k y'‖ ≤ mom (k + 1) * |y - y'| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := Jn k) (x := y') (y := y)
    (fun x _ => differentiable_Jn k x) (fun x _ => by rw [deriv_Jn]; exact norm_Jn_le (k + 1) x)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using this

/-- A bounded Lipschitz function is `α`-Hölder for every `α ∈ (0,1]`. -/
lemma holder_of_lip_bdd {φ : ℝ → ℂ} {L B α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hB : ∀ y, ‖φ y‖ ≤ B) (hlip : ∀ y y', ‖φ y - φ y'‖ ≤ L * |y - y'|) (y y' : ℝ) :
    ‖φ y - φ y'‖ ≤ max L (2 * B) * |y - y'| ^ α := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rcases le_or_gt |y - y'| 1 with h | h
  · calc ‖φ y - φ y'‖ ≤ L * |y - y'| := hlip y y'
      _ ≤ L * |y - y'| ^ α := by
          apply mul_le_mul_of_nonneg_left _ hL
          have := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (y - y')) h hα0.le hα1
          simpa using this
      _ ≤ max L (2 * B) * |y - y'| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
  · have h1 : 1 ≤ |y - y'| ^ α := Real.one_le_rpow h.le hα0.le
    calc ‖φ y - φ y'‖ ≤ ‖φ y‖ + ‖φ y'‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB y, hB y']
      _ ≤ 2 * B * |y - y'| ^ α := by nlinarith
      _ ≤ max L (2 * B) * |y - y'| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- The Hölder constant of `J`. -/
def KJ : ℝ := max (mom 1) (2 * C0)

/-- The Hölder constant of `J''`. -/
def KJ2 : ℝ := max (mom 3) 2

lemma KJ_pos : 0 < KJ := lt_of_lt_of_le (by have := C0_pos; linarith) (le_max_right _ _)

lemma KJ2_pos : 0 < KJ2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)

lemma J_holder {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (y y' : ℝ) :
    ‖Jn 0 y - Jn 0 y'‖ ≤ KJ * |y - y'| ^ α :=
  holder_of_lip_bdd hα0 hα1 (mom_nonneg 1) (fun y => by have := norm_Jn_le 0 y; exact this)
    (norm_Jn_sub_le 0) y y'

lemma J2_holder {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (y y' : ℝ) :
    ‖Jn 2 y - Jn 2 y'‖ ≤ KJ2 * |y - y'| ^ α :=
  by simpa [KJ2] using
    holder_of_lip_bdd hα0 hα1 (mom_nonneg 3) norm_Jn_two_le (norm_Jn_sub_le 2) y y'

lemma abs_coord_sub_le (v v' : E d) (i : Fin d) : |v i - v' i| ≤ ‖v - v'‖ := by
  have := PiLp.norm_apply_le (v - v') i
  simpa [Real.norm_eq_abs] using this

lemma rpow_div_rpow_le_one {r α : ℝ} (hr : 0 < r) (hα : 0 < α) :
    r ^ α / r ^ α = 1 := div_self (Real.rpow_pos_of_pos hr α).ne'

/-! ### Constant shifts do not change derivatives -/

lemma dT_const_add (c : ℝ) (F : Pt d → ℝ) (p : Pt d) : dT (fun q => c + F q) p = dT F p := by
  unfold dT; exact deriv_const_add c

lemma transport_const_add (c : ℝ) (F : Pt d → ℝ) (p : Pt d) :
    transport (fun q => c + F q) p = transport F p := by
  unfold transport gradX; rw [fderiv_const_add]

lemma hessV_const_add (c : ℝ) (F : Pt d → ℝ) (p : Pt d) :
    hessV (fun q => c + F q) p = hessV F p := by
  have h : ∀ w, fderiv ℝ (fun w' => c + F (p.1, p.2.1, w')) w =
      fderiv ℝ (fun w' => F (p.1, p.2.1, w')) w := fun w => fderiv_const_add c
  unfold hessV
  simp_rw [h]
  rfl

variable [NeZero d]

/-! ### Bounds for `f_N` -/

lemma fN_indep_t (N t t' : ℝ) (x v : E d) : fN d N (t, x, v) = fN d N (t', x, v) := by
  simp [fN]

lemma gN_indep_v (N t : ℝ) (x v v' : E d) : gN d N (t, x, v) = gN d N (t, x, v') := by
  simp [gN]

lemma gN_indep_t (N t t' : ℝ) (x v : E d) : gN d N (t, x, v) = gN d N (t', x, v) := by
  simp [gN]

/-- `|f_N(t,x,v) - f_N(t,x,v')| ≤ K_J N^{(α-2)/3} |v - v'|^α`. -/
lemma fN_sub_le {N α : ℝ} (hN : 0 < N) (hα0 : 0 < α) (hα1 : α ≤ 1) (t : ℝ) (x v v' : E d) :
    |fN d N (t, x, v) - fN d N (t, x, v')| ≤ KJ * N ^ ((α - 2) / 3) * ‖v - v'‖ ^ α := by
  rw [fN_eq hN, fN_eq hN]
  simp only
  set a := cbrt N
  have ha : 0 < a := cbrt_pos hN
  rw [← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_zN hN]
  have h1 := J_holder hα0 hα1 (a * v 0) (a * v' 0)
  have h2 : |a * v 0 - a * v' 0| ^ α ≤ a ^ α * ‖v - v'‖ ^ α := by
    rw [← mul_sub, abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (abs_coord_sub_le v v' 0) hα0.le)
      (Real.rpow_nonneg ha.le _)
  have h3 : (a ^ 2)⁻¹ * a ^ α = N ^ ((α - 2) / 3) := by
    rw [cbrt_sq_inv hN, cbrt_rpow hN, ← Real.rpow_add hN]; congr 1; ring
  calc (a ^ 2)⁻¹ * ‖Jn 0 (a * v 0) - Jn 0 (a * v' 0)‖
      ≤ (a ^ 2)⁻¹ * (KJ * (a ^ α * ‖v - v'‖ ^ α)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact h1.trans (mul_le_mul_of_nonneg_left h2 KJ_pos.le)
    _ = KJ * ((a ^ 2)⁻¹ * a ^ α) * ‖v - v'‖ ^ α := by ring
    _ = KJ * N ^ ((α - 2) / 3) * ‖v - v'‖ ^ α := by rw [h3]

lemma semR_fN_le {N α : ℝ} (hN : 0 < N) (hα0 : 0 < α) (hα1 : α ≤ 1) (S : Set (Pt d)) :
    semR α S (fN d N) ≤ ENNReal.ofReal (KJ * N ^ ((α - 2) / 3)) := by
  apply semVg_le
  intro t x v v' _ _ h3 _
  rw [div_le_iff₀ (Real.rpow_pos_of_pos h3 α)]
  exact fN_sub_le hN hα0 hα1 t x v v'

lemma supN_fN_le {N : ℝ} (hN : 0 < N) (S : Set (Pt d)) :
    supN S (fN d N) ≤ ENNReal.ofReal (C0 * N ^ (-(2/3 : ℝ))) :=
  supN_le _ _ _ (fun p _ => abs_fN_le hN p)

/-- The `(1,1)` Hessian entry `H(p) = Re(e^{iNx₁} J''(N^{1/3} v₁))`. -/
def H00 (d : ℕ) [NeZero d] (N : ℝ) (p : Pt d) : ℝ :=
  (Complex.exp (I * ((N * p.2.1 0 : ℝ) : ℂ)) * Jn 2 (cbrt N * p.2.2 0)).re

lemma hessV_fN_eq {N : ℝ} (hN : 0 < N) (p : Pt d) :
    hessV (fN d N) p = fun i j => if i = 0 ∧ j = 0 then H00 d N p else 0 := by
  have h00 := hessV_fN_00 hN p
  rw [hessV_fN hN] at h00 ⊢
  simp only [and_self, ite_true] at h00
  funext i j
  split_ifs with h
  · exact h00
  · rfl

lemma frob_hessV_fN_sub {N : ℝ} (hN : 0 < N) (p p' : Pt d) :
    frob (hessV (fN d N) p - hessV (fN d N) p') = |H00 d N p - H00 d N p'| := by
  rw [hessV_fN_eq hN, hessV_fN_eq hN, ← frob_single (0 : Fin d)]
  congr 1
  funext i j
  show (if i = 0 ∧ j = 0 then H00 d N p else 0) - (if i = 0 ∧ j = 0 then H00 d N p' else 0) = _
  by_cases h : i = 0 ∧ j = 0 <;> simp [h]

lemma frob_hessV_fN {N : ℝ} (hN : 0 < N) (p : Pt d) :
    frob (hessV (fN d N) p) = |H00 d N p| := by
  rw [hessV_fN_eq hN, frob_single]

lemma abs_H00_le (N : ℝ) (p : Pt d) : |H00 d N p| ≤ 1 := by
  unfold H00
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_exp_I_mul, one_mul]
  exact norm_Jn_two_le _

lemma H00_sub_le {N α : ℝ} (hN : 0 < N) (hα0 : 0 < α) (hα1 : α ≤ 1) (t : ℝ) (x v v' : E d) :
    |H00 d N (t, x, v) - H00 d N (t, x, v')| ≤ KJ2 * N ^ (α / 3) * ‖v - v'‖ ^ α := by
  unfold H00
  simp only
  set a := cbrt N
  have ha : 0 < a := cbrt_pos hN
  rw [← Complex.sub_re, ← mul_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_exp_I_mul, one_mul]
  have h1 := J2_holder hα0 hα1 (a * v 0) (a * v' 0)
  have h2 : |a * v 0 - a * v' 0| ^ α ≤ a ^ α * ‖v - v'‖ ^ α := by
    rw [← mul_sub, abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (abs_coord_sub_le v v' 0) hα0.le)
      (Real.rpow_nonneg ha.le _)
  calc ‖Jn 2 (a * v 0) - Jn 2 (a * v' 0)‖ ≤ KJ2 * (a ^ α * ‖v - v'‖ ^ α) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 KJ2_pos.le)
    _ = KJ2 * N ^ (α / 3) * ‖v - v'‖ ^ α := by rw [cbrt_rpow hN]; ring

lemma semM_hessV_fN_le {N α : ℝ} (hN : 0 < N) (hα0 : 0 < α) (hα1 : α ≤ 1) (S : Set (Pt d)) :
    semM α S (hessV (fN d N)) ≤ ENNReal.ofReal (KJ2 * N ^ (α / 3)) := by
  apply semVg_le
  intro t x v v' _ _ h3 _
  rw [div_le_iff₀ (Real.rpow_pos_of_pos h3 α), frob_hessV_fN_sub hN]
  exact H00_sub_le hN hα0 hα1 t x v v'

lemma supNM_hessV_fN_le {N : ℝ} (hN : 0 < N) (S : Set (Pt d)) :
    supNM S (hessV (fN d N)) ≤ ENNReal.ofReal 1 :=
  supNM_le _ _ _ (fun p _ => by rw [frob_hessV_fN hN]; exact abs_H00_le N p)

/-! ### The lower bound for the velocity Hessian -/

/-- A fixed `Y > 0` with `Re J''(Y) - Re J''(0) ≥ 1/2` (display (2.11)). -/
lemma exists_Y : ∃ Y : ℝ, 0 < Y ∧ 1 / 2 ≤ (Jn 2 Y).re - (Jn 2 0).re := by
  have h := tendsto_Jn_two
  have hev : ∀ᶠ y in atTop, ‖Jn 2 y‖ < 1 / 2 :=
    (tendsto_zero_iff_norm_tendsto_zero.1 h).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨Y, hY1, hY2⟩ := (hev.and (eventually_gt_atTop 0)).exists
  refine ⟨Y, hY2, ?_⟩
  rw [Jn_two_zero]
  have := (Complex.abs_re_le_norm (Jn 2 Y)).trans hY1.le
  have := (abs_le.1 this).1
  simp only [Complex.neg_re, Complex.one_re]
  linarith

lemma norm_smul_ev (s : ℝ) (i : Fin d) : ‖s • (ev i : E d)‖ = |s| := by
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

lemma smul_ev_apply (s : ℝ) (i : Fin d) : (s • (ev i : E d)) i = s := by
  simp [ev]

/-- **The lower bound (2.2)**: `[D_v² f_N]_{C^α_v(Q_{1/2})} ≥ N^{α/3} / (2 Y^α)` once `N > 8Y³`. -/
lemma semM_hessV_fN_ge {Y : ℝ} (hY : 0 < Y) (hYJ : 1 / 2 ≤ (Jn 2 Y).re - (Jn 2 0).re)
    {α : ℝ} (hα : 0 < α) {N : ℝ} (hN8 : 8 * Y ^ 3 < N) :
    ENNReal.ofReal (1 / (2 * Y ^ α) * N ^ (α / 3)) ≤ semM α (Q d (1/2)) (hessV (fN d N)) := by
  have hN : 0 < N := lt_trans (by positivity) hN8
  set a := cbrt N with ha_def
  have ha : 0 < a := cbrt_pos hN
  have ha3 : a ^ 3 = N := cbrt_pow_three hN.le
  have h2Y : 2 * Y < a := by
    by_contra hcon
    push Not at hcon
    have : a ^ 3 ≤ (2 * Y) ^ 3 := pow_le_pow_left₀ ha.le hcon 3
    nlinarith
  set v : E d := (Y / a) • ev 0 with hv
  have hYa : 0 < Y / a := div_pos hY ha
  have hYa2 : Y / a < 1 / 2 := by rw [div_lt_iff₀ ha]; linarith
  have hnv : ‖v - 0‖ = Y / a := by rw [sub_zero, hv, norm_smul_ev, abs_of_pos hYa]
  have hmem1 : ((0 : ℝ), (0 : E d), v) ∈ Q d (1/2) := by
    rw [mem_Q]; refine ⟨⟨by norm_num, le_refl _⟩, by simp, ?_⟩
    rw [hv, norm_smul_ev, abs_of_pos hYa]; norm_num; linarith
  have hmem2 : ((0 : ℝ), (0 : E d), (0 : E d)) ∈ Q d (1/2) := by
    rw [mem_Q]; refine ⟨⟨by norm_num, le_refl _⟩, by simp, by simp⟩
  have key := le_semVg (fun A B : Matrix (Fin d) (Fin d) ℝ => frob (A - B)) α (Q d (1/2))
    (hessV (fN d N)) hmem1 hmem2 (by rw [hnv]; exact hYa) (by rw [hnv]; exact hYa2)
  refine le_trans ?_ key
  apply ENNReal.ofReal_le_ofReal
  rw [frob_hessV_fN_sub hN, hnv]
  have hv0 : v 0 = Y / a := by rw [hv, smul_ev_apply]
  have e1 : H00 d N ((0 : ℝ), (0 : E d), v) = (Jn 2 Y).re := by
    unfold H00; simp only
    rw [hv0, show a * (Y / a) = Y by field_simp]
    simp
  have e2 : H00 d N ((0 : ℝ), (0 : E d), (0 : E d)) = (Jn 2 0).re := by
    unfold H00; simp
  rw [e1, e2, abs_of_nonneg (by linarith)]
  have hpow : (Y / a) ^ α = Y ^ α / N ^ (α / 3) := by
    rw [Real.div_rpow hY.le ha.le, cbrt_rpow hN]
  rw [hpow]
  have hYα : 0 < Y ^ α := Real.rpow_pos_of_pos hY α
  have hNα : 0 < N ^ (α / 3) := Real.rpow_pos_of_pos hN _
  rw [le_div_iff₀ (div_pos hYα hNα)]
  field_simp
  linarith

/-! ### Theorem 2.1 -/

/-- **Theorem 2.1** (explicit form): with `Y` from `exists_Y`, for every `N > 8Y³` the functions
`f_N = Re(e^{iNx₁} I_N(v₁))`, `g_N = cos(N x₁)` have all the properties claimed. -/
theorem thm_2_1_explicit {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {Y : ℝ} (hY : 0 < Y)
    (hYJ : 1 / 2 ≤ (Jn 2 Y).re - (Jn 2 0).re) {N : ℝ} (hN8 : 8 * Y ^ 3 < N) :
    ContDiff ℝ ∞ (fN d N) ∧ ContDiff ℝ ∞ (gN d N) ∧
      (∀ t t' x v, fN d N (t, x, v) = fN d N (t', x, v)) ∧
      (∀ p : Pt d, dT (fN d N) p + transport (fN d N) p =
        Matrix.trace (hessV (fN d N) p) + gN d N p) ∧
      (∀ p : Pt d, |gN d N p| ≤ 1) ∧ semR α (Q d 1) (gN d N) = 0 ∧
      supN (Q d 1) (fN d N) ≤ ENNReal.ofReal (C0 * N ^ (-(2/3 : ℝ))) ∧
      ENNReal.ofReal (1 / (2 * Y ^ α) * N ^ (α / 3)) ≤ semM α (Q d (1/2)) (hessV (fN d N)) := by
  have hN : 0 < N := lt_trans (by positivity) hN8
  exact ⟨contDiff_fN hN, contDiff_gN N, fN_indep_t N, fN_solves hN, abs_gN_le N,
    semR_eq_zero_of_indep α _ _ (gN_indep_v N), supN_fN_le hN _,
    semM_hessV_fN_ge hY hYJ hα0 hN8⟩

/-- **Theorem 2.1.** Let `d ≥ 1` and `α ∈ (0,1)`. There exist `c₀ > 0`, `N₀ ≥ 1` and, for every
`N ≥ N₀`, a smooth real-valued stationary solution `f_N` of `(∂_t + v·∇_x) f_N = Δ_v f_N + g_N`
in `Q₁` with `‖g_N‖_{L∞(Q₁)} ≤ 1` and `[g_N]_{C^α_v(Q₁)} = 0`, such that
`‖f_N‖_{L∞(Q₁)} ≤ C₀ N^{-2/3}` and `[D_v² f_N]_{C^α_v(Q_{1/2})} ≥ c₀ N^{α/3}`. -/
theorem thm_2_1 (d : ℕ) [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      ∃ f g : Pt d → ℝ, ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
        (∀ t t' x v, f (t, x, v) = f (t', x, v)) ∧
        (∀ p ∈ Q d 1, dT f p + transport f p = Matrix.trace (hessV f p) + g p) ∧
        (∀ p ∈ Q d 1, |g p| ≤ 1) ∧ semR α (Q d 1) g = 0 ∧
        supN (Q d 1) f ≤ ENNReal.ofReal (C0 * N ^ (-(2/3 : ℝ))) ∧
        ENNReal.ofReal (c0 * N ^ (α / 3)) ≤ semM α (Q d (1/2)) (hessV f) := by
  obtain ⟨Y, hY, hYJ⟩ := exists_Y
  refine ⟨1 / (2 * Y ^ α), by have := Real.rpow_pos_of_pos hY α; positivity,
    8 * Y ^ 3 + 1, by have := pow_pos hY 3; linarith, fun N hN => ?_⟩
  have hN8 : 8 * Y ^ 3 < N := by linarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := thm_2_1_explicit (d := d) hα0 hα1 hY hYJ hN8
  exact ⟨fN d N, gN d N, h1, h2, h3, fun p _ => h4 p, fun p _ => h5 p, h6, h7, h8⟩

/-! ### Conjecture 1.1 is false (end of the proof of Theorem 2.1) and Remark 2.2 -/

lemma elliptic_one {Λ : ℝ} (hΛ : 1 < Λ) : Elliptic Λ (1 : Matrix (Fin d) (Fin d) ℝ) := by
  constructor
  · have : (1 : Matrix (Fin d) (Fin d) ℝ) - Λ⁻¹ • 1 = (1 - Λ⁻¹) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [sub_smul, one_smul]
    rw [this]
    exact Matrix.PosSemidef.one.smul (by
      have : Λ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hΛ
      linarith)
  · have : Λ • (1 : Matrix (Fin d) (Fin d) ℝ) - 1 = (Λ - 1) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [sub_smul, one_smul]
    rw [this]
    exact Matrix.PosSemidef.one.smul (by linarith)

lemma inCvM_one (α : ℝ) (S : Set (Pt d)) :
    InCvM α S (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  refine ⟨lt_of_le_of_lt (supNM_le _ _ (d * 1) (fun p _ => frob_le_of_entries _ zero_le_one
    (fun i j => by
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]))) ENNReal.ofReal_lt_top, ?_⟩
  rw [semM_eq_zero_of_indep α S _ (fun _ _ _ _ => rfl)]
  exact ENNReal.zero_lt_top

lemma inCv_zero (α : ℝ) (S : Set (Pt d)) : InCv α S (fun _ => (0 : ℝ)) := by
  refine ⟨lt_of_le_of_lt (supN_le _ _ 0 (fun p _ => by simp)) ENNReal.ofReal_lt_top, ?_⟩
  rw [semR_eq_zero_of_indep α S _ (fun _ _ _ _ => rfl)]
  exact ENNReal.zero_lt_top

lemma semR_zero (α : ℝ) (S : Set (Pt d)) : semR α S (fun _ => (0 : ℝ)) = 0 :=
  semR_eq_zero_of_indep α S _ (fun _ _ _ _ => rfl)

lemma semM_one (α : ℝ) (S : Set (Pt d)) :
    semM α S (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ)) = 0 :=
  semM_eq_zero_of_indep α S _ (fun _ _ _ _ => rfl)

lemma inCv_fN {N α : ℝ} (hN : 0 < N) (hα0 : 0 < α) (hα1 : α ≤ 1) (S : Set (Pt d)) :
    InCv α S (fN d N) :=
  ⟨lt_of_le_of_lt (supN_fN_le hN S) ENNReal.ofReal_lt_top,
    lt_of_le_of_lt (semR_fN_le hN hα0 hα1 S) ENNReal.ofReal_lt_top⟩

lemma inCvM_hessV_fN {N α : ℝ} (hN : 0 < N) (hα0 : 0 < α) (hα1 : α ≤ 1) (S : Set (Pt d)) :
    InCvM α S (hessV (fN d N)) :=
  ⟨lt_of_le_of_lt (supNM_hessV_fN_le hN S) ENNReal.ofReal_lt_top,
    lt_of_le_of_lt (semM_hessV_fN_le hN hα0 hα1 S) ENNReal.ofReal_lt_top⟩

lemma inCv_gN (N α : ℝ) (S : Set (Pt d)) : InCv α S (gN d N) := by
  refine ⟨lt_of_le_of_lt (supN_le _ _ 1 (fun p _ => abs_gN_le N p)) ENNReal.ofReal_lt_top, ?_⟩
  rw [semR_eq_zero_of_indep α S _ (gN_indep_v N)]
  exact ENNReal.zero_lt_top

lemma kfp_fN {N : ℝ} (hN : 0 < N) (p : Pt d) :
    KFP (fN d N) (fun _ => 1) (fun _ => 0) (gN d N) p := by
  unfold KFP
  rw [fN_solves hN p, one_mul, zero_mul, add_zero]

/-- `‖g_N‖_{L∞(Q₁)} = 1`. -/
lemma supN_gN (N : ℝ) : supN (Q d 1) (gN d N) = 1 := by
  apply le_antisymm
  · have := supN_le (Q d 1) (gN d N) 1 (fun p _ => abs_gN_le N p)
    simpa using this
  · have hmem : ((0 : ℝ), (0 : E d), (0 : E d)) ∈ Q d 1 := by
      rw [mem_Q]; refine ⟨⟨by norm_num, le_refl _⟩, by simp, by simp⟩
    have := le_supN (Q d 1) (gN d N) hmem
    simpa [gN] using this

/-- **Remark 2.2** as a formal statement: the estimate (1.2) with an extra term `Φ(‖g‖_{L∞(Q₁)})`,
for an arbitrary function `Φ` taking finite values, still fails. -/
def Conj11plus (d : ℕ) (α Λ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ Φ : ℝ≥0∞ → ℝ≥0∞, (∀ s, s < ⊤ → Φ s < ⊤) ∧
    ∀ (f c g : Pt d → ℝ) (a : Pt d → Matrix (Fin d) (Fin d) ℝ),
    ContDiff ℝ ∞ f →
    (∀ p ∈ Q d 1, Elliptic Λ (a p)) → (∀ p ∈ Q d 1, |c p| ≤ Λ) → (∀ p ∈ Q d 1, |g p| ≤ Λ) →
    InCv α (Q d 1) f → InCvM α (Q d 1) (hessV f) → InCvM α (Q d 1) a →
    InCv α (Q d 1) c → InCv α (Q d 1) g →
    (∀ p ∈ Q d 1, KFP f a c g p) →
    semM α (Q d (1/2)) (hessV f) ≤
      ENNReal.ofReal C * (1 + semR α (Q d 1) c + semM α (Q d 1) a ^ (1 + 2 / α)) *
          supN (Q d 1) f +
        ENNReal.ofReal C * (1 + semM α (Q d 1) a) * semR α (Q d 1) g + Φ (supN (Q d 1) g)

/-- **Remark 2.2.** -/
theorem rem_2_2 (d : ℕ) (hd : 1 ≤ d) {α Λ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hΛ : 1 < Λ) :
    ¬ Conj11plus d α Λ := by
  have : NeZero d := ⟨by omega⟩
  rintro ⟨C, Φ, hΦ, hC⟩
  obtain ⟨Y, hY, hYJ⟩ := exists_Y
  set K : ℝ := (Φ 1).toReal with hK
  have hΦ1 : Φ 1 = ENNReal.ofReal K := by
    rw [hK, ENNReal.ofReal_toReal (hΦ 1 ENNReal.one_lt_top).ne]
  -- for `N ≥ 1`, the right-hand side is at most `max C 0 * C₀ + K`
  have hbig : ∀ᶠ N : ℝ in atTop, 8 * Y ^ 3 < N ∧ 1 ≤ N ∧
      max C 0 * C0 + K < 1 / (2 * Y ^ α) * N ^ (α / 3) := by
    refine (eventually_gt_atTop _).and ((eventually_ge_atTop 1).and ?_)
    have ht : Tendsto (fun N : ℝ => 1 / (2 * Y ^ α) * N ^ (α / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).const_mul_atTop
        (by have := Real.rpow_pos_of_pos hY α; positivity)
    exact ht.eventually_gt_atTop _
  obtain ⟨N, hN8, hN1, hNbig⟩ := hbig.exists
  have hN : 0 < N := by linarith
  have hest := hC (fN d N) (fun _ => 0) (gN d N) (fun _ => 1) (contDiff_fN hN)
    (fun p _ => elliptic_one hΛ) (fun p _ => by simp; linarith)
    (fun p _ => (abs_gN_le N p).trans hΛ.le) (inCv_fN hN hα0 hα1.le _)
    (inCvM_hessV_fN hN hα0 hα1.le _) (inCvM_one α _) (inCv_zero α _) (inCv_gN N α _)
    (fun p _ => kfp_fN hN p)
  rw [semR_zero, semM_one, semR_eq_zero_of_indep α _ _ (gN_indep_v N), supN_gN, hΦ1,
    ENNReal.zero_rpow_of_pos (by positivity)] at hest
  simp only [add_zero, mul_one, mul_zero, zero_add] at hest
  have hlow := semM_hessV_fN_ge (d := d) hY hYJ hα0 hN8
  have hsup := supN_fN_le (d := d) hN (Q d 1)
  have h1 : ENNReal.ofReal (1 / (2 * Y ^ α) * N ^ (α / 3)) ≤
      ENNReal.ofReal (max C 0 * (C0 * N ^ (-(2/3 : ℝ))) + K) := by
    refine hlow.trans (hest.trans ?_)
    rw [ENNReal.ofReal_add (by have := C0_pos; positivity)
      (ENNReal.toReal_nonneg), ENNReal.ofReal_mul (le_max_right _ _)]
    gcongr
    exact le_max_left _ _
  rw [ENNReal.ofReal_le_ofReal_iff (by have := C0_pos; positivity)] at h1
  have hNpow : N ^ (-(2/3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have : max C 0 * (C0 * N ^ (-(2/3 : ℝ))) ≤ max C 0 * C0 := by
    apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
    have := C0_pos
    nlinarith
  linarith

/-- **Conjecture 1.1 is false** (conclusion of Theorem 2.1): for every `d ≥ 1`, `α ∈ (0,1)` and
`Λ > 1` there is no constant `C` for which (1.2) holds. -/
theorem conj11_false (d : ℕ) (hd : 1 ≤ d) {α Λ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hΛ : 1 < Λ) :
    ¬ Conj11 d α Λ := by
  rintro ⟨C, hC⟩
  apply rem_2_2 d hd hα0 hα1 hΛ
  refine ⟨C, fun _ => 0, fun _ _ => ENNReal.zero_lt_top, ?_⟩
  intro f c g a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rw [add_zero]
  exact hC f c g a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

end KS

end -- (the file's `noncomputable section`)

end File_Counterexample

-- ============================================================================
-- KineticCounterexamples/ZeroForcing.lean
-- ============================================================================

section File_ZeroForcing

/-!
# Proposition 3.1 of Dong–Wang: the zero-forcing variant

`u_N = 1 + f_N`, `c_N = g_N / (1 + f_N)` solve `(∂_t + v·∇_x) u_N = Δ_v u_N + c_N u_N` with
`1/2 ≤ u_N ≤ 3/2`, `‖c_N‖_∞ ≤ C`, `[c_N]_{C^α_v(Q₁)} ≤ C N^{(α-2)/3}` and
`[D_v² u_N]_{C^α_v(Q_{1/2})} ≥ c N^{α/3}`; consequently the velocity-only estimate fails even
with `g ≡ 0` (`conj11_zero_false`).
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace KS

variable {d : ℕ} [NeZero d]

/-- `u_N = 1 + f_N`. -/
def uN (d : ℕ) [NeZero d] (N : ℝ) (p : Pt d) : ℝ := 1 + fN d N p

/-- `c_N = g_N / (1 + f_N)`. -/
def cN (d : ℕ) [NeZero d] (N : ℝ) (p : Pt d) : ℝ := gN d N p / (1 + fN d N p)

/-- Smallness of `f_N` for large `N`. -/
lemma eventually_fN_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, 0 < N ∧ C0 * N ^ (-(2/3 : ℝ)) ≤ ε := by
  refine (eventually_gt_atTop 0).and ?_
  have h : Tendsto (fun N : ℝ => C0 * N ^ (-(2/3 : ℝ))) atTop (𝓝 (C0 * 0)) :=
    (tendsto_rpow_neg_atTop (by norm_num)).const_mul C0
  rw [mul_zero] at h
  exact (h.eventually (ge_mem_nhds hε))

lemma one_add_fN_ge {N ε : ℝ} (hN : 0 < N) (hε : C0 * N ^ (-(2/3 : ℝ)) ≤ ε) (p : Pt d) :
    1 - ε ≤ 1 + fN d N p := by
  have := abs_fN_le (d := d) hN p
  have := (abs_le.1 (this.trans hε)).1
  linarith

lemma contDiff_cN {N : ℝ} (hN : 0 < N) (hε : C0 * N ^ (-(2/3 : ℝ)) ≤ 1 / 2) :
    ContDiff ℝ ∞ (cN d N) := by
  unfold cN
  exact (contDiff_gN N).div (contDiff_const.add (contDiff_fN hN))
    (fun p => by have := one_add_fN_ge (d := d) hN hε p; linarith)

lemma contDiff_uN {N : ℝ} (hN : 0 < N) : ContDiff ℝ ∞ (uN d N) :=
  contDiff_const.add (contDiff_fN hN)

lemma hessV_uN (N : ℝ) (p : Pt d) : hessV (uN d N) p = hessV (fN d N) p :=
  hessV_const_add 1 (fN d N) p

lemma kfp_uN {N : ℝ} (hN : 0 < N) (hε : C0 * N ^ (-(2/3 : ℝ)) ≤ 1 / 2) (p : Pt d) :
    KFP (uN d N) (fun _ => 1) (cN d N) (fun _ => 0) p := by
  unfold KFP
  have hpos : 1 + fN d N p ≠ 0 := by have := one_add_fN_ge (d := d) hN hε p; linarith
  have e1 : dT (uN d N) p = dT (fN d N) p := dT_const_add 1 (fN d N) p
  have e2 : transport (uN d N) p = transport (fN d N) p := transport_const_add 1 (fN d N) p
  have e3 : cN d N p * uN d N p = gN d N p := by
    unfold cN uN; field_simp
  rw [e1, e2, hessV_uN, one_mul, e3, add_zero]
  exact fN_solves hN p

lemma abs_cN_le {N ε : ℝ} (hN : 0 < N) (hε : C0 * N ^ (-(2/3 : ℝ)) ≤ ε) (hε1 : ε < 1)
    (p : Pt d) : |cN d N p| ≤ 1 / (1 - ε) := by
  have h1 := one_add_fN_ge (d := d) hN hε p
  have h2 : 0 < 1 - ε := by linarith
  unfold cN
  rw [abs_div, abs_of_pos (lt_of_lt_of_le h2 h1)]
  rw [div_le_div_iff₀ (lt_of_lt_of_le h2 h1) h2]
  have := abs_gN_le (d := d) N p
  nlinarith [abs_nonneg (gN d N p)]

lemma cN_sub_le {N : ℝ} (hN : 0 < N) (hε : C0 * N ^ (-(2/3 : ℝ)) ≤ 1 / 2) (t : ℝ) (x v v' : E d) :
    |cN d N (t, x, v) - cN d N (t, x, v')| ≤ 4 * |fN d N (t, x, v) - fN d N (t, x, v')| := by
  have h1 := one_add_fN_ge (d := d) hN hε (t, x, v)
  have h2 := one_add_fN_ge (d := d) hN hε (t, x, v')
  have hg : gN d N (t, x, v') = gN d N (t, x, v) := gN_indep_v N t x v' v
  unfold cN
  rw [hg]
  set A := 1 + fN d N (t, x, v)
  set B := 1 + fN d N (t, x, v')
  have hA : 0 < A := by linarith
  have hB : 0 < B := by linarith
  have e : gN d N (t, x, v) / A - gN d N (t, x, v) / B =
      gN d N (t, x, v) * (B - A) / (A * B) := by field_simp
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hA hB)]
  have hBA : B - A = -(fN d N (t, x, v) - fN d N (t, x, v')) := by simp only [A, B]; ring
  rw [hBA, abs_neg, div_le_iff₀ (mul_pos hA hB)]
  have hg1 := abs_gN_le (d := d) N (t, x, v)
  have hAB : 1 / 4 ≤ A * B := by nlinarith
  have hf := abs_nonneg (fN d N (t, x, v) - fN d N (t, x, v'))
  nlinarith

lemma semR_cN_le {N α : ℝ} (hN : 0 < N) (hε : C0 * N ^ (-(2/3 : ℝ)) ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (S : Set (Pt d)) :
    semR α S (cN d N) ≤ ENNReal.ofReal (4 * KJ * N ^ ((α - 2) / 3)) := by
  apply semVg_le
  intro t x v v' _ _ h3 _
  rw [div_le_iff₀ (Real.rpow_pos_of_pos h3 α)]
  calc |cN d N (t, x, v) - cN d N (t, x, v')| ≤ 4 * |fN d N (t, x, v) - fN d N (t, x, v')| :=
        cN_sub_le hN hε t x v v'
    _ ≤ 4 * (KJ * N ^ ((α - 2) / 3) * ‖v - v'‖ ^ α) := by
        gcongr; exact fN_sub_le hN hα0 hα1 t x v v'
    _ = 4 * KJ * N ^ ((α - 2) / 3) * ‖v - v'‖ ^ α := by ring

/-- **Proposition 3.1.** Let `d ≥ 1` and `α ∈ (0,1)`. There exist `C, c > 0`, `N₀ ≥ 1` and, for
every `N ≥ N₀`, smooth stationary solutions `u_N` of `(∂_t + v·∇_x) u_N = Δ_v u_N + c_N u_N` in
`Q₁` with zero forcing, such that `1/2 ≤ u_N ≤ 3/2`, `‖c_N‖_{L∞(Q₁)} ≤ C`,
`[c_N]_{C^α_v(Q₁)} ≤ C N^{(α-2)/3}`, while `[D_v² u_N]_{C^α_v(Q_{1/2})} ≥ c N^{α/3}`. -/
theorem prop_3_1 (d : ℕ) [NeZero d] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      ∃ u cc : Pt d → ℝ, ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ cc ∧
        (∀ t t' x v, u (t, x, v) = u (t', x, v)) ∧
        (∀ p ∈ Q d 1, dT u p + transport u p = Matrix.trace (hessV u p) + cc p * u p) ∧
        (∀ p ∈ Q d 1, 1 / 2 ≤ u p ∧ u p ≤ 3 / 2) ∧
        supN (Q d 1) cc ≤ ENNReal.ofReal C ∧
        semR α (Q d 1) cc ≤ ENNReal.ofReal (C * N ^ ((α - 2) / 3)) ∧
        ENNReal.ofReal (c * N ^ (α / 3)) ≤ semM α (Q d (1/2)) (hessV u) := by
  obtain ⟨Y, hY, hYJ⟩ := exists_Y
  have hev : ∀ᶠ N : ℝ in atTop, (0 < N ∧ C0 * N ^ (-(2/3 : ℝ)) ≤ 1 / 2) ∧ 8 * Y ^ 3 < N :=
    (eventually_fN_small (by norm_num)).and (eventually_gt_atTop _)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨max 2 (4 * KJ), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    1 / (2 * Y ^ α), by have := Real.rpow_pos_of_pos hY α; positivity,
    max N1 1, le_max_right _ _, fun N hN => ?_⟩
  obtain ⟨⟨hN0, hε⟩, hN8⟩ := hN1 N (le_trans (le_max_left _ _) hN)
  refine ⟨uN d N, cN d N, contDiff_uN hN0, contDiff_cN hN0 hε,
    fun t t' x v => by simp [uN, fN_indep_t N t t' x v], fun p _ => ?_, fun p _ => ?_, ?_, ?_, ?_⟩
  · have := kfp_uN (d := d) hN0 hε p
    unfold KFP at this
    rw [this, one_mul, add_zero]
  · have := abs_fN_le (d := d) hN0 p
    have := abs_le.1 (this.trans hε)
    unfold uN; constructor <;> linarith [this.1, this.2]
  · refine supN_le _ _ _ (fun p _ => ?_)
    refine (abs_cN_le hN0 hε (by norm_num) p).trans ?_
    norm_num
  · refine (semR_cN_le hN0 hε hα0 hα1.le _).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hN0.le _)
  · have h : hessV (uN d N) = hessV (fN d N) := funext (hessV_uN N)
    rw [h]
    exact semM_hessV_fN_ge hY hYJ hα0 hN8

/-- The velocity-only estimate (1.2) restricted to zero forcing `g ≡ 0`
(this is implied by `Conj11`). -/
def Conj11zero (d : ℕ) (α Λ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (f c : Pt d → ℝ) (a : Pt d → Matrix (Fin d) (Fin d) ℝ),
    ContDiff ℝ ∞ f →
    (∀ p ∈ Q d 1, Elliptic Λ (a p)) → (∀ p ∈ Q d 1, |c p| ≤ Λ) →
    InCv α (Q d 1) f → InCvM α (Q d 1) (hessV f) → InCvM α (Q d 1) a → InCv α (Q d 1) c →
    (∀ p ∈ Q d 1, KFP f a c (fun _ => 0) p) →
    semM α (Q d (1/2)) (hessV f) ≤
      ENNReal.ofReal C * (1 + semR α (Q d 1) c + semM α (Q d 1) a ^ (1 + 2 / α)) *
        supN (Q d 1) f

omit [NeZero d] in
lemma conj11_imp_zero {d : ℕ} {α Λ : ℝ} (hΛ : 1 < Λ) (h : Conj11 d α Λ) : Conj11zero d α Λ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun f c a h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
  have := hC f c (fun _ => 0) a h1 h2 h3 (fun p _ => by simp; linarith) h4 h5 h6 h7
    (by
      refine ⟨lt_of_le_of_lt (supN_le _ _ 0 (fun p _ => by simp)) ENNReal.ofReal_lt_top, ?_⟩
      rw [semR_eq_zero_of_indep α _ _ (fun _ _ _ _ => rfl)]; exact ENNReal.zero_lt_top) h8
  rwa [semR_eq_zero_of_indep α _ (fun _ => (0 : ℝ)) (fun _ _ _ _ => rfl), mul_zero,
    add_zero] at this

/-- **Proposition 3.1, final assertion**: the velocity-only estimate fails even when `g ≡ 0`. -/
theorem conj11_zero_false (d : ℕ) (hd : 1 ≤ d) {α Λ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hΛ : 1 < Λ) : ¬ Conj11zero d α Λ := by
  have : NeZero d := ⟨by omega⟩
  rintro ⟨C, hC⟩
  obtain ⟨Y, hY, hYJ⟩ := exists_Y
  set ε : ℝ := min (1 / 2) (1 - Λ⁻¹) with hεdef
  have hΛinv : Λ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hΛ
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε2 : ε ≤ 1 / 2 := min_le_left _ _
  have hεΛ : 1 / (1 - ε) ≤ Λ := by
    have h1 : ε ≤ 1 - Λ⁻¹ := min_le_right _ _
    have h2 : 0 < 1 - ε := by linarith
    rw [div_le_iff₀ h2]
    have hΛ0 : 0 < Λ := by linarith
    have : Λ * Λ⁻¹ = 1 := mul_inv_cancel₀ hΛ0.ne'
    nlinarith
  set M : ℝ := max C 0 * (1 + 4 * KJ) * (3 / 2) with hM
  have hev : ∀ᶠ N : ℝ in atTop, (0 < N ∧ C0 * N ^ (-(2/3 : ℝ)) ≤ ε) ∧ 8 * Y ^ 3 < N ∧ 1 ≤ N ∧
      M < 1 / (2 * Y ^ α) * N ^ (α / 3) := by
    refine (eventually_fN_small hε0).and ((eventually_gt_atTop _).and
      ((eventually_ge_atTop 1).and ?_))
    have ht : Tendsto (fun N : ℝ => 1 / (2 * Y ^ α) * N ^ (α / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).const_mul_atTop
        (by have := Real.rpow_pos_of_pos hY α; positivity)
    exact ht.eventually_gt_atTop _
  obtain ⟨N, ⟨hN0, hNε⟩, hN8, hN1, hNbig⟩ := hev.exists
  have hNε2 : C0 * N ^ (-(2/3 : ℝ)) ≤ 1 / 2 := hNε.trans hε2
  -- the hypotheses of the zero-forcing estimate for `u_N`, `c_N`, `a = Id`
  have hinCvu : InCv α (Q d 1) (uN d N) := by
    refine ⟨lt_of_le_of_lt (supN_le _ _ (3 / 2) (fun p _ => ?_)) ENNReal.ofReal_lt_top, ?_⟩
    · have := abs_le.1 ((abs_fN_le (d := d) hN0 p).trans hNε2)
      unfold uN; rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · have hsem : semR α (Q d 1) (uN d N) = semR α (Q d 1) (fN d N) := by
        unfold semR semVg uN; simp
      rw [hsem]; exact (inCv_fN hN0 hα0 hα1.le _).2
  have hinCvMu : InCvM α (Q d 1) (hessV (uN d N)) := by
    have h : hessV (uN d N) = hessV (fN d N) := funext (hessV_uN N)
    rw [h]; exact inCvM_hessV_fN hN0 hα0 hα1.le _
  have hinCvc : InCv α (Q d 1) (cN d N) :=
    ⟨lt_of_le_of_lt (supN_le _ _ _ (fun p _ => abs_cN_le hN0 hNε2 (by norm_num) p))
      ENNReal.ofReal_lt_top,
      lt_of_le_of_lt (semR_cN_le hN0 hNε2 hα0 hα1.le _) ENNReal.ofReal_lt_top⟩
  have hest := hC (uN d N) (cN d N) (fun _ => 1) (contDiff_uN hN0)
    (fun p _ => elliptic_one hΛ)
    (fun p _ => (abs_cN_le hN0 hNε (by linarith) p).trans hεΛ)
    hinCvu hinCvMu (inCvM_one α _) hinCvc (fun p _ => kfp_uN hN0 hNε2 p)
  rw [semM_one, ENNReal.zero_rpow_of_pos (by positivity), add_zero] at hest
  -- bound the right-hand side
  have hsupu : supN (Q d 1) (uN d N) ≤ ENNReal.ofReal (3 / 2) := by
    refine supN_le _ _ _ (fun p _ => ?_)
    have := abs_le.1 ((abs_fN_le (d := d) hN0 p).trans hNε2)
    unfold uN; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hsemc : semR α (Q d 1) (cN d N) ≤ ENNReal.ofReal (4 * KJ) := by
    refine (semR_cN_le hN0 hNε2 hα0 hα1.le _).trans (ENNReal.ofReal_le_ofReal ?_)
    have : N ^ ((α - 2) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have := KJ_pos
    nlinarith
  have hrhs : ENNReal.ofReal C * (1 + semR α (Q d 1) (cN d N)) * supN (Q d 1) (uN d N) ≤
      ENNReal.ofReal M := by
    rw [hM, ENNReal.ofReal_mul (by have := KJ_pos; positivity),
      ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_add zero_le_one
        (by have := KJ_pos; positivity), ENNReal.ofReal_one]
    gcongr
    exact le_max_left _ _
  have hlow := semM_hessV_fN_ge (d := d) hY hYJ hα0 hN8
  have h : hessV (uN d N) = hessV (fN d N) := funext (hessV_uN N)
  rw [h] at hest
  have := (hlow.trans hest).trans hrhs
  rw [ENNReal.ofReal_le_ofReal_iff (by have := KJ_pos; positivity)] at this
  linarith

end KS

end -- (the file's `noncomputable section`)

end File_ZeroForcing

-- ============================================================================
-- KineticCounterexamples/Spatial.lean
-- ============================================================================

section File_Spatial

/-!
# The spatial Hölder seminorm of the forcing `g_N = cos(N x₁)`

Introduction of Dong–Wang and Remark 3.2 of the relativistic note:
`[g_N]_{C^{α/3}_x(Q₁)} ≍ N^{α/3}` — the forcing is invisible to velocity (momentum) seminorms but
its spatial seminorm at the kinetic exponent has exactly the size of the Hessian growth.
We prove the two-sided bound `2π^{-β} N^β ≤ [g_N]_{C^β_x(Q₁)} ≤ 2 N^β` for every `β ∈ (0,1]`
and `N > 2π`; the claim is the case `β = α/3`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace KS

lemma abs_cos_sub_cos_le_rpow {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (a b : ℝ) :
    |Real.cos a - Real.cos b| ≤ 2 * |a - b| ^ β := by
  rcases le_or_gt |a - b| 1 with h | h
  · calc |Real.cos a - Real.cos b| ≤ |a - b| := Real.abs_cos_sub_cos_le a b
      _ ≤ |a - b| ^ β := by
          have := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (a - b)) h hβ0.le hβ1
          simpa using this
      _ ≤ 2 * |a - b| ^ β := by
          have := Real.rpow_nonneg (abs_nonneg (a - b)) β; linarith
  · have h1 : 1 ≤ |a - b| ^ β := Real.one_le_rpow h.le hβ0.le
    calc |Real.cos a - Real.cos b| ≤ |Real.cos a| + |Real.cos b| := abs_sub _ _
      _ ≤ 2 := by linarith [Real.abs_cos_le_one a, Real.abs_cos_le_one b]
      _ ≤ 2 * |a - b| ^ β := by linarith

variable {d : ℕ} [NeZero d]

/-- **Spatial seminorm of the forcing** (Dong–Wang, Section 1; relativistic note, Remark 3.2):
`2π^{-β} N^β ≤ [cos(N x₁)]_{C^β_x(Q₁)} ≤ 2 N^β` for `β ∈ (0,1]`, `N > 2π`. -/
theorem semX_gN (d : ℕ) [NeZero d] {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {N : ℝ}
    (hN : 2 * π < N) :
    ENNReal.ofReal (2 * π ^ (-β) * N ^ β) ≤ semX β (Q d 1) (gN d N) ∧
      semX β (Q d 1) (gN d N) ≤ ENNReal.ofReal (2 * N ^ β) := by
  have hN0 : 0 < N := lt_trans (by positivity) hN
  constructor
  · set x : E d := (π / N) • ev 0 with hx
    have hπN : 0 < π / N := div_pos Real.pi_pos hN0
    have hπN2 : π / N < 1 / 2 := by rw [div_lt_iff₀ hN0]; linarith
    have hnx : ‖x - 0‖ = π / N := by rw [sub_zero, hx, norm_smul_ev, abs_of_pos hπN]
    have hmem1 : ((0 : ℝ), x, (0 : E d)) ∈ Q d 1 := by
      rw [mem_Q]; refine ⟨⟨by norm_num, le_refl _⟩, ?_, by simp⟩
      rw [hx, norm_smul_ev, abs_of_pos hπN]; norm_num; linarith
    have hmem2 : ((0 : ℝ), (0 : E d), (0 : E d)) ∈ Q d 1 := by
      rw [mem_Q]; refine ⟨⟨by norm_num, le_refl _⟩, by simp, by simp⟩
    have key := le_semX β (Q d 1) (gN d N) hmem1 hmem2 (by rw [hnx]; exact hπN)
      (by rw [hnx]; exact hπN2)
    refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) key
    rw [hnx]
    have hx0 : x 0 = π / N := by rw [hx, smul_ev_apply]
    simp only [gN, hx0, PiLp.zero_apply, mul_zero, Real.cos_zero]
    rw [show N * (π / N) = π by field_simp, Real.cos_pi]
    rw [Real.div_rpow Real.pi_pos.le hN0.le, Real.rpow_neg Real.pi_pos.le]
    have : 0 < π ^ β := Real.rpow_pos_of_pos Real.pi_pos β
    have : 0 < N ^ β := Real.rpow_pos_of_pos hN0 β
    rw [show |(-1 : ℝ) - 1| = 2 by norm_num]
    field_simp
  · apply semX_le
    intro t x x' v _ _ h3 _
    rw [div_le_iff₀ (Real.rpow_pos_of_pos h3 β)]
    unfold gN
    simp only
    refine (abs_cos_sub_cos_le_rpow hβ0 hβ1 _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos hN0, Real.mul_rpow hN0.le (abs_nonneg _)]
    have := Real.rpow_le_rpow (abs_nonneg _) (abs_coord_sub_le x x' 0) hβ0.le
    have hNβ := Real.rpow_pos_of_pos hN0 β
    nlinarith [Real.rpow_nonneg (abs_nonneg (x 0 - x' 0)) β]

end KS

end -- (the file's `noncomputable section`)

end File_Spatial

-- ============================================================================
-- KineticCounterexamples/Endpoint/ParamInt.lean
-- ============================================================================

section File_Endpoint_ParamInt

/-!
# Smoothness of parametric integrals

If `p ↦ F p a` is smooth for every `a` and every iterated derivative is dominated, uniformly in
the parameter, by an integrable function of `a`, then `p ↦ ∫ F p a dμ` is smooth and its
iterated derivatives are the integrals of the iterated derivatives.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace KS

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem hasFTaylorSeriesUpTo_integral (F : P → α → E) (hF : ∀ a, ContDiff ℝ ∞ (fun p => F p a))
    (hmeas : ∀ n p, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (fun p => F p a) p) μ)
    (b : ℕ → α → ℝ) (hb : ∀ n, Integrable (b n) μ)
    (hbound : ∀ n p a, ‖iteratedFDeriv ℝ n (fun p => F p a) p‖ ≤ b n a) :
    HasFTaylorSeriesUpTo ∞ (fun p => ∫ a, F p a ∂μ)
      (fun p n => ∫ a, iteratedFDeriv ℝ n (fun p => F p a) p ∂μ) := by
  have hint : ∀ n p, Integrable (fun a => iteratedFDeriv ℝ n (fun p => F p a) p) μ := fun n p =>
    (hb n).mono' (hmeas n p) (Eventually.of_forall (fun a => hbound n p a))
  constructor
  · intro p
    rw [ContinuousMultilinearMap.curry0_apply, ContinuousMultilinearMap.integral_apply (hint 0 p)]
    congr 1
  · intro m _ p
    have hderiv : ∀ a y, HasFDerivAt (fun y => iteratedFDeriv ℝ m (fun p => F p a) y)
        ((iteratedFDeriv ℝ (m + 1) (fun p => F p a) y).curryLeft) y := by
      intro a y
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun p => F p a)) y :=
        ((hF a).differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) y
      have := hd.hasFDerivAt
      rw [fderiv_iteratedFDeriv] at this
      exact this
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (x₀ := p)
      (F := fun y a => iteratedFDeriv ℝ m (fun p => F p a) y)
      (F' := fun y a => (iteratedFDeriv ℝ (m + 1) (fun p => F p a) y).curryLeft)
      (bound := b (m + 1)) (s := Set.univ) Filter.univ_mem
      (Eventually.of_forall (fun y => hmeas m y)) (hint m p)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => P) E).toContinuousLinearEquiv
        |>.toContinuousLinearMap.continuous.comp_aestronglyMeasurable (hmeas (m + 1) p))
      (Eventually.of_forall (fun a y _ => by
        rw [ContinuousMultilinearMap.curryLeft_norm]; exact hbound (m + 1) y a))
      (hb (m + 1)) (Eventually.of_forall (fun a y _ => hderiv a y))
    have hcomm : ∫ a, (iteratedFDeriv ℝ (m + 1) (fun p => F p a) p).curryLeft ∂μ =
        (∫ a, iteratedFDeriv ℝ (m + 1) (fun p => F p a) p ∂μ).curryLeft := by
      let L : (P [×(m + 1)]→L[ℝ] E) ≃L[ℝ] (P →L[ℝ] P [×m]→L[ℝ] E) :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => P) E).toContinuousLinearEquiv
      have := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (F := P →L[ℝ] P [×m]→L[ℝ] E) (μ := μ) L
        (fun a => iteratedFDeriv ℝ (m + 1) (fun p => F p a) p)
      exact this
    rw [hcomm] at key
    exact key
  · intro m _
    exact continuous_of_dominated (fun p => hmeas m p)
      (fun p => Eventually.of_forall (fun a => hbound m p a)) (hb m)
      (Eventually.of_forall (fun a => (hF a).continuous_iteratedFDeriv
        (by exact_mod_cast le_top)))

/-- Smoothness of a parametric integral under uniform domination of all iterated derivatives. -/
theorem contDiff_integral_of_bound (F : P → α → E) (hF : ∀ a, ContDiff ℝ ∞ (fun p => F p a))
    (hmeas : ∀ n p, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (fun p => F p a) p) μ)
    (b : ℕ → α → ℝ) (hb : ∀ n, Integrable (b n) μ)
    (hbound : ∀ n p a, ‖iteratedFDeriv ℝ n (fun p => F p a) p‖ ≤ b n a) :
    ContDiff ℝ ∞ (fun p => ∫ a, F p a ∂μ) :=
  (hasFTaylorSeriesUpTo_integral F hF hmeas b hb hbound).contDiff

/-- The iterated derivatives of the parametric integral. -/
theorem iteratedFDeriv_integral_of_bound (F : P → α → E) (hF : ∀ a, ContDiff ℝ ∞ (fun p => F p a))
    (hmeas : ∀ n p, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (fun p => F p a) p) μ)
    (b : ℕ → α → ℝ) (hb : ∀ n, Integrable (b n) μ)
    (hbound : ∀ n p a, ‖iteratedFDeriv ℝ n (fun p => F p a) p‖ ≤ b n a) (n : ℕ) (p : P) :
    iteratedFDeriv ℝ n (fun p => ∫ a, F p a ∂μ) p =
      ∫ a, iteratedFDeriv ℝ n (fun p => F p a) p ∂μ := by
  have h := (hasFTaylorSeriesUpTo_integral F hF hmeas b hb hbound).eq_iteratedFDeriv
    (m := n) (by exact_mod_cast le_top) p
  exact h.symm

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_ParamInt

-- ============================================================================
-- KineticCounterexamples/Endpoint/Heat.lean
-- ============================================================================

section File_Endpoint_Heat

/-!
# The heat kernel and the heat semigroup on `ℝᵈ`

* `hk d τ w = (4πτ)^{-d/2} e^{-|w|²/(4τ)}` is the Gaussian heat kernel `G_τ`;
* `heat τ h x = ∫ G_τ(x - y) h(y) dy` is the heat semigroup `P_τ = e^{τΔ}`;
* `heat_eq_fourier`: `P_τ h(x) = ∫ ĥ(ξ) e^{-4π²τ|ξ|²} e^{2πi⟨x,ξ⟩} dξ` for integrable `h`
  (Mathlib's normalisation `ĥ(ξ) = ∫ e^{-2πi⟨y,ξ⟩} h(y) dy`);
* the two bounds `|P_τ h| ≤ sup |h|` and `|P_τ h| ≤ (4πτ)^{-d/2} ‖h‖_{L¹}` used in (4.3).
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped FourierTransform RealInnerProductSpace

namespace KS

variable {d : ℕ}

/-- The heat kernel `G_τ(w) = (4πτ)^{-d/2} exp(-|w|²/(4τ))`. -/
def hk (d : ℕ) (τ : ℝ) (w : E d) : ℝ :=
  (4 * π * τ) ^ (-(d : ℝ) / 2) * Real.exp (-‖w‖ ^ 2 / (4 * τ))

lemma hk_pos {τ : ℝ} (hτ : 0 < τ) (w : E d) : 0 < hk d τ w := by
  unfold hk
  have : 0 < 4 * π * τ := by positivity
  positivity

lemma hk_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (w : E d) : 0 ≤ hk d τ w := by
  unfold hk
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

lemma hk_le {τ : ℝ} (hτ : 0 < τ) (w : E d) : hk d τ w ≤ (4 * π * τ) ^ (-(d : ℝ) / 2) := by
  unfold hk
  have h1 : Real.exp (-‖w‖ ^ 2 / (4 * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg ‖w‖]
    · positivity
  have h2 : 0 ≤ (4 * π * τ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  calc _ ≤ (4 * π * τ) ^ (-(d : ℝ) / 2) * 1 := by gcongr
    _ = _ := mul_one _

lemma hk_neg (τ : ℝ) (w : E d) : hk d τ (-w) = hk d τ w := by simp [hk]

lemma hk_sub_comm (τ : ℝ) (x y : E d) : hk d τ (x - y) = hk d τ (y - x) := by
  rw [← neg_sub, hk_neg]

lemma continuous_hk (τ : ℝ) : Continuous (hk d τ) := by
  unfold hk
  fun_prop

lemma measurable_hk_uncurry : Measurable (fun q : ℝ × E d => hk d q.1 q.2) := by
  unfold hk
  fun_prop

/-- The Gaussian integral: `∫ G_τ = 1`. -/
lemma integral_hk {τ : ℝ} (hτ : 0 < τ) : ∫ w, hk d τ w = 1 := by
  unfold hk
  rw [integral_const_mul]
  have hb : (0 : ℝ) < 1 / (4 * τ) := by positivity
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E d) hb
  have e1 : (fun w : E d => Real.exp (-‖w‖ ^ 2 / (4 * τ))) =
      fun w : E d => Real.exp (-(1 / (4 * τ)) * ‖w‖ ^ 2) := by
    funext w; congr 1; ring
  rw [e1, this, finrank_euclideanSpace_fin]
  have e2 : π / (1 / (4 * τ)) = 4 * π * τ := by field_simp
  rw [e2, show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring, Real.rpow_neg (by positivity)]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos (by positivity) _).ne'

lemma integrable_hk {τ : ℝ} (hτ : 0 < τ) : Integrable (hk d τ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_hk hτ]; exact one_ne_zero

lemma integrable_hk_sub {τ : ℝ} (hτ : 0 < τ) (x : E d) :
    Integrable (fun y => hk d τ (x - y)) :=
  (integrable_hk hτ).comp_sub_left x

lemma integral_hk_sub {τ : ℝ} (hτ : 0 < τ) (x : E d) : ∫ y, hk d τ (x - y) = 1 := by
  rw [integral_sub_left_eq_self (hk d τ) volume x, integral_hk hτ]

/-! ### The heat semigroup -/

/-- The heat semigroup `P_τ h (x) = ∫ G_τ(x - y) h(y) dy`. -/
def heat (τ : ℝ) (h : E d → ℂ) (x : E d) : ℂ := ∫ y, (hk d τ (x - y) : ℂ) * h y

lemma norm_heat_le_sup {τ : ℝ} (hτ : 0 < τ) {h : E d → ℂ} {K : ℝ}
    (hK : ∀ y, ‖h y‖ ≤ K) (x : E d) : ‖heat τ h x‖ ≤ K := by
  unfold heat
  have hbd : Integrable (fun y => hk d τ (x - y) * K) := (integrable_hk_sub hτ x).mul_const K
  calc ‖∫ y, (hk d τ (x - y) : ℂ) * h y‖ ≤ ∫ y, hk d τ (x - y) * K := by
        apply norm_integral_le_of_norm_le hbd
        filter_upwards with y
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk_nonneg hτ.le _)]
        exact mul_le_mul_of_nonneg_left (hK y) (hk_nonneg hτ.le _)
    _ = K := by rw [integral_mul_const, integral_hk_sub hτ x, one_mul]

lemma norm_heat_le_L1 {τ : ℝ} (hτ : 0 < τ) {h : E d → ℂ} (hh : Integrable h) (x : E d) :
    ‖heat τ h x‖ ≤ (4 * π * τ) ^ (-(d : ℝ) / 2) * ∫ y, ‖h y‖ := by
  unfold heat
  have hbd : Integrable (fun y => (4 * π * τ) ^ (-(d : ℝ) / 2) * ‖h y‖) :=
    hh.norm.const_mul _
  calc ‖∫ y, (hk d τ (x - y) : ℂ) * h y‖ ≤ ∫ y, (4 * π * τ) ^ (-(d : ℝ) / 2) * ‖h y‖ := by
        apply norm_integral_le_of_norm_le hbd
        filter_upwards with y
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk_nonneg hτ.le _)]
        exact mul_le_mul_of_nonneg_right (hk_le hτ _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The Fourier transform of the modulated Gaussian is the heat kernel. -/
lemma fourier_gauss_eq_hk {τ : ℝ} (hτ : 0 < τ) (x y : E d) :
    𝓕 (fun ξ : E d => cexp (-((4 * π ^ 2 * τ : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 +
      2 * π * Complex.I * (⟪x, ξ⟫ : ℂ))) y = (hk d τ (x - y) : ℂ) := by
  have hb : 0 < (((4 * π ^ 2 * τ : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; positivity
  rw [fourier_gaussian_innerProductSpace' hb x y, finrank_euclideanSpace_fin]
  have hπ : 0 < π := Real.pi_pos
  have h1 : (π : ℂ) / ((4 * π ^ 2 * τ : ℝ) : ℂ) = (((4 * π * τ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e1 : ((π : ℂ) / ((4 * π ^ 2 * τ : ℝ) : ℂ)) ^ ((d : ℂ) / 2) =
      (((4 * π * τ) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [h1, show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    ring_nf
  have e2 : cexp (-(π : ℂ) ^ 2 * (‖x - y‖ : ℂ) ^ 2 / ((4 * π ^ 2 * τ : ℝ) : ℂ)) =
      ((Real.exp (-‖x - y‖ ^ 2 / (4 * τ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  rw [e1, e2, ← Complex.ofReal_mul]
  rfl

/-- **Fourier representation of the heat semigroup**:
`P_τ h(x) = ∫ ĥ(ξ) e^{-4π²τ|ξ|²} e^{2πi⟨x,ξ⟩} dξ`. -/
theorem heat_eq_fourier {τ : ℝ} (hτ : 0 < τ) {h : E d → ℂ} (hh : Integrable h) (x : E d) :
    heat τ h x = ∫ ξ, 𝓕 h ξ * cexp (-((4 * π ^ 2 * τ : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 +
      2 * π * Complex.I * (⟪x, ξ⟫ : ℂ)) := by
  set φ : E d → ℂ := fun ξ => cexp (-((4 * π ^ 2 * τ : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 +
      2 * π * Complex.I * (⟪x, ξ⟫ : ℂ)) with hφ
  have hb : 0 < (((4 * π ^ 2 * τ : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; positivity
  have hφi : Integrable φ :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb (2 * π * Complex.I) x
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure (E d))) (ν := (volume : Measure (E d))) (L := innerₗ (E d))
    Real.continuous_fourierChar continuous_inner hh hφi
  simp only [flip_innerₗ, smul_eq_mul] at key
  change ∫ ξ, 𝓕 h ξ * φ ξ = ∫ y, h y * 𝓕 φ y at key
  rw [key]
  unfold heat
  congr 1
  funext y
  rw [hφ, fourier_gauss_eq_hk hτ x y, mul_comm]

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Heat

-- ============================================================================
-- KineticCounterexamples/Endpoint/Ech.lean
-- ============================================================================

section File_Endpoint_Ech

/-!
# Oscillatory integrands `c(a) e^{2πi A_a(p)}`

* `ech t = e^{2πit}` and the bound `‖D^n (e^{2πi A(·)})‖ ≤ (2π‖A‖)^n`;
* joint smoothness of parametric iterated derivatives (for measurability in the parameter);
* differentiation under the integral sign for `p ↦ ∫ c(a) e^{2πi A_a(p)} dμ(a)`.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped ContDiff

namespace KS

/-- `e(t) = e^{2πit}`. -/
def ech (t : ℝ) : ℂ := cexp (((2 * π * t : ℝ) : ℂ) * I)

lemma hasDerivAt_ech (t : ℝ) : HasDerivAt ech (2 * π * I * ech t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((2 * π * t : ℝ) : ℂ) * I) (((2 * π : ℝ) : ℂ) * I) t := by
    have := ((hasDerivAt_id t).const_mul (2 * π)).ofReal_comp
    simpa using this.mul_const I
  have h2 := h1.cexp
  unfold ech
  convert h2 using 1
  push_cast
  ring

lemma contDiff_ech : ContDiff ℝ ∞ ech := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => ((2 * π * t : ℝ) : ℂ) * I) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
  exact Complex.contDiff_exp.comp h1

lemma norm_ech (t : ℝ) : ‖ech t‖ = 1 := by
  unfold ech
  rw [Complex.norm_exp_ofReal_mul_I]

lemma ech_zero : ech 0 = 1 := by simp [ech]

lemma ech_add (s t : ℝ) : ech (s + t) = ech s * ech t := by
  unfold ech
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma iteratedDeriv_ech (n : ℕ) : iteratedDeriv n ech = fun t => (2 * π * I) ^ n * ech t := by
  induction n with
  | zero => funext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have := ((hasDerivAt_ech t).const_mul ((2 * π * I) ^ n)).deriv
    rw [this]
    ring

lemma norm_iteratedFDeriv_ech (n : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ n ech t‖ = (2 * π) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_ech, norm_mul, norm_ech, mul_one,
    norm_pow, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_of_nonneg Real.pi_pos.le]

lemma norm_iteratedFDeriv_ech_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] ℝ) (n : ℕ) (p : P) :
    ‖iteratedFDeriv ℝ n (fun p => ech (A p)) p‖ ≤ (2 * π * ‖A‖) ^ n := by
  have h := A.iteratedFDeriv_comp_right contDiff_ech p (i := n) (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n (ech ∘ A) p‖ ≤ _
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_ech, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact le_of_eq (by ring)

lemma norm_iteratedFDeriv_mul_ech_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : ℂ) (A : P →L[ℝ] ℝ) (n : ℕ) (p : P) :
    ‖iteratedFDeriv ℝ n (fun p => c * ech (A p)) p‖ ≤ ‖c‖ * (2 * π * ‖A‖) ^ n := by
  have hcd : ContDiff ℝ ∞ (fun p => ech (A p)) := contDiff_ech.comp A.contDiff
  have : (fun p => c * ech (A p)) = c • (fun p => ech (A p)) := by funext p; simp
  rw [this, iteratedFDeriv_const_smul_apply (hcd.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_ech_comp A n p) (norm_nonneg _)

/-! ### Joint smoothness of parametric iterated derivatives -/

theorem contDiff_iteratedFDeriv_param {A P G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : A → P → G} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (n : ℕ) :
    ContDiff ℝ ∞ (fun q : A × P => iteratedFDeriv ℝ n (F q.1) q.2) := by
  induction n with
  | zero =>
    have : (fun q : A × P => iteratedFDeriv ℝ 0 (F q.1) q.2) =
        fun q => (continuousMultilinearCurryFin0 ℝ P G).symm (F q.1 q.2) := by
      funext q; ext m; simp [iteratedFDeriv_zero_apply]
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ P G).symm.contDiff.comp hF
  | succ n ih =>
    have : (fun q : A × P => iteratedFDeriv ℝ (n + 1) (F q.1) q.2) =
        fun q => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) G).symm
          (fderiv ℝ (fun y => iteratedFDeriv ℝ n (F q.1) y) q.2) := by
      funext q
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    rw [this]
    have hu : ContDiff ℝ ∞ (Function.uncurry
        (fun (q : A × P) (y : P) => iteratedFDeriv ℝ n (F q.1) y)) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hfd : ContDiff ℝ ∞ (fun q : A × P => fderiv ℝ (fun y => iteratedFDeriv ℝ n (F q.1) y) q.2) :=
      ContDiff.fderiv (f := fun (q : A × P) (y : P) => iteratedFDeriv ℝ n (F q.1) y)
        (g := fun q => q.2) hu contDiff_snd (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) G).symm.contDiff.comp hfd

/-! ### Differentiation under the integral sign -/

variable {P α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MeasurableSpace α] {μ : Measure α}

lemma hasFDerivAt_mul_ech (c : ℂ) (A : P →L[ℝ] ℝ) (p : P) :
    HasFDerivAt (fun p => c * ech (A p)) (A.smulRight (c * (2 * π * I) * ech (A p))) p := by
  have h := (hasDerivAt_ech (A p)).hasFDerivAt.comp p A.hasFDerivAt
  have h2 := h.const_mul c
  refine h2.congr_fderiv ?_
  ext q
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply,
    Complex.real_smul, smul_eq_mul]
  ring

theorem hasFDerivAt_integral_ech (c : α → ℂ) (A : α → P →L[ℝ] ℝ)
    (hmeas : ∀ p, AEStronglyMeasurable (fun a => c a * ech (A a p)) μ)
    (p₀ : P)
    (hmeas' : AEStronglyMeasurable (fun a => (A a).smulRight (c a * (2 * π * I) * ech (A a p₀))) μ)
    (hint : Integrable (fun a => ‖c a‖) μ)
    (hint1 : Integrable (fun a => 2 * π * (‖c a‖ * ‖A a‖)) μ) :
    HasFDerivAt (fun p => ∫ a, c a * ech (A a p) ∂μ)
      (∫ a, (A a).smulRight (c a * (2 * π * I) * ech (A a p₀)) ∂μ) p₀ := by
  have hF_int : Integrable (fun a => c a * ech (A a p₀)) μ := by
    refine hint.mono' (hmeas p₀) (Eventually.of_forall fun a => ?_)
    rw [norm_mul, norm_ech, mul_one]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (x₀ := p₀)
    (F := fun y a => c a * ech (A a y))
    (F' := fun y a => (A a).smulRight (c a * (2 * π * I) * ech (A a y)))
    (bound := fun a => 2 * π * (‖c a‖ * ‖A a‖)) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall (fun y => hmeas y)) hF_int hmeas'
    (Eventually.of_forall (fun a y _ => ?_)) hint1
    (Eventually.of_forall (fun a y _ => hasFDerivAt_mul_ech (c a) (A a) y))
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_mul, norm_mul, norm_ech, mul_one]
  have : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
  rw [this]
  exact le_of_eq (by ring)

theorem fderiv_integral_ech_apply (c : α → ℂ) (A : α → P →L[ℝ] ℝ)
    (hmeas : ∀ p, AEStronglyMeasurable (fun a => c a * ech (A a p)) μ)
    (p₀ : P)
    (hmeas' : AEStronglyMeasurable (fun a => (A a).smulRight (c a * (2 * π * I) * ech (A a p₀))) μ)
    (hint : Integrable (fun a => ‖c a‖) μ)
    (hint1 : Integrable (fun a => 2 * π * (‖c a‖ * ‖A a‖)) μ) (q : P) :
    fderiv ℝ (fun p => ∫ a, c a * ech (A a p) ∂μ) p₀ q =
      ∫ a, c a * ((2 * π * I) * (A a q : ℂ)) * ech (A a p₀) ∂μ := by
  rw [(hasFDerivAt_integral_ech c A hmeas p₀ hmeas' hint hint1).fderiv]
  have hI : Integrable (fun a => (A a).smulRight (c a * (2 * π * I) * ech (A a p₀))) μ := by
    refine hint1.mono' hmeas' (Eventually.of_forall fun a => ?_)
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_mul, norm_mul, norm_ech, mul_one]
    have : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
        Complex.norm_of_nonneg Real.pi_pos.le]
    rw [this]
    exact le_of_eq (by ring)
  rw [ContinuousLinearMap.integral_apply hI q]
  congr 1
  funext a
  simp only [ContinuousLinearMap.smulRight_apply, real_smul]
  ring

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Ech

-- ============================================================================
-- KineticCounterexamples/Endpoint/SolOp.lean
-- ============================================================================

section File_Endpoint_SolOp

/-!
# The solution operator `𝒮h(x,v) = ∫₀^∞ P_{s³/3} h(x - s v) ds`

For a Schwartz function `h` we write
`𝒮h(x,v) = ∫∫_{(0,∞)×ℝᵈ} ĥ(ξ) e^{-(4π²/3)s³|ξ|²} e^{2πi(⟨ξ,x⟩ - s⟨ξ,v⟩)} dξ ds`
(`kinF`), prove that it agrees with the physical formula (4.3) (`kin_eq_kinF`), that it is
`C^∞` (`contDiff_kinF`), and compute its first and second derivatives under the integral sign.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set SchwartzMap
open scoped FourierTransform RealInnerProductSpace ContDiff

namespace KS

variable {d : ℕ}

/-- The kinetic solution operator (4.3): `𝒮h(x,v) = ∫₀^∞ P_{s³/3} h(x - s v) ds`. -/
def kin (h : E d → ℂ) (x v : E d) : ℂ := ∫ s in Ioi (0 : ℝ), heat (s ^ 3 / 3) h (x - s • v)

/-- The measure `ds ⊗ dξ` on `(0,∞) × ℝᵈ`. -/
abbrev μK (d : ℕ) : Measure (ℝ × E d) := (volume.restrict (Ioi (0 : ℝ))).prod volume

/-- The phase `(x,v) ↦ ⟨ξ,x⟩ - s⟨ξ,v⟩`, for `a = (s, ξ)`. -/
def kPh (a : ℝ × E d) : E d × E d →L[ℝ] ℝ :=
  (innerSL ℝ a.2).comp (ContinuousLinearMap.fst ℝ (E d) (E d)) -
    a.1 • (innerSL ℝ a.2).comp (ContinuousLinearMap.snd ℝ (E d) (E d))

@[simp] lemma kPh_apply (a : ℝ × E d) (p : E d × E d) :
    kPh a p = ⟪a.2, p.1⟫ - a.1 * ⟪a.2, p.2⟫ := by
  simp [kPh]

lemma continuous_kPh : Continuous (kPh (d := d)) := by
  unfold kPh
  have h1 : Continuous (fun a : ℝ × E d => innerSL ℝ a.2) := (innerSL ℝ).continuous.comp continuous_snd
  exact (h1.clm_comp continuous_const).sub (continuous_fst.smul (h1.clm_comp continuous_const))

lemma norm_kPh_le (a : ℝ × E d) : ‖kPh a‖ ≤ (1 + |a.1|) * ‖a.2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [kPh_apply, Real.norm_eq_abs]
  have h1 : |⟪a.2, p.1⟫| ≤ ‖a.2‖ * ‖p.1‖ := abs_real_inner_le_norm _ _
  have h2 : |⟪a.2, p.2⟫| ≤ ‖a.2‖ * ‖p.2‖ := abs_real_inner_le_norm _ _
  have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have hn : 0 ≤ ‖a.2‖ := norm_nonneg _
  have h3 : |⟪a.2, p.1⟫ - a.1 * ⟪a.2, p.2⟫| ≤ |⟪a.2, p.1⟫| + |a.1| * |⟪a.2, p.2⟫| := by
    rw [← abs_mul]; exact abs_sub _ _
  have h4 : ‖a.2‖ * ‖p.1‖ ≤ ‖a.2‖ * ‖p‖ := mul_le_mul_of_nonneg_left hp1 hn
  have h5 : ‖a.2‖ * ‖p.2‖ ≤ ‖a.2‖ * ‖p‖ := mul_le_mul_of_nonneg_left hp2 hn
  have h6 : |a.1| * |⟪a.2, p.2⟫| ≤ |a.1| * (‖a.2‖ * ‖p‖) :=
    mul_le_mul_of_nonneg_left (h2.trans h5) (abs_nonneg _)
  nlinarith

/-- The Fourier amplitude `ĥ(ξ) e^{-(4π²/3) s³ |ξ|²}`. -/
def kAmp (h : E d → ℂ) (a : ℝ × E d) : ℂ :=
  𝓕 h a.2 * ((Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2)) : ℝ) : ℂ)

lemma norm_kAmp (h : E d → ℂ) (a : ℝ × E d) :
    ‖kAmp h a‖ = ‖𝓕 h a.2‖ * Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2)) := by
  rw [kAmp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The Fourier form of the solution operator. -/
def kinF (h : E d → ℂ) (p : E d × E d) : ℂ := ∫ a, kAmp h a * ech (kPh a p) ∂(μK d)

/-- The dominating functions for the derivatives of the integrand of `kinF`. -/
def kB (h : E d → ℂ) (n : ℕ) (a : ℝ × E d) : ℝ :=
  ‖𝓕 h a.2‖ * Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2)) *
    (2 * π * ((1 + |a.1|) * ‖a.2‖)) ^ n

lemma kB_nonneg (h : E d → ℂ) (n : ℕ) (a : ℝ × E d) : 0 ≤ kB h n a := by
  unfold kB; positivity

/-! ### Integrability of the dominating functions -/

lemma ae_ne_zero_E (hd : 1 ≤ d) : ∀ᵐ ξ : E d ∂volume, ξ ≠ 0 := by
  haveI : Nontrivial (E d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  exact compl_mem_ae_iff.mpr (measure_singleton 0)

/-- `ξ ↦ |ξ|^a |φ(ξ)|` is integrable for a Schwartz function `φ` and `a > -d`. -/
lemma integrable_rpow_mul_norm_schwartz (hd : 1 ≤ d) (φ : 𝓢(E d, ℂ)) {a : ℝ}
    (ha : -(d : ℝ) < a) : Integrable (fun ξ : E d => ‖ξ‖ ^ a * ‖φ ξ‖) := by
  have hmeas : AEStronglyMeasurable (fun ξ : E d => ‖ξ‖ ^ a * ‖φ ξ‖) volume :=
    ((continuous_norm.measurable.pow_const a).mul φ.continuous.norm.measurable).aestronglyMeasurable
  have hball : IntegrableOn (fun ξ : E d => ‖ξ‖ ^ a * ‖φ ξ‖) (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by rw [finrank_euclideanSpace_fin]; exact hd)
      (C := SchwartzMap.seminorm ℝ 0 0 φ) (α := -a)
      (by rw [finrank_euclideanSpace_fin]; linarith) _ hmeas
    filter_upwards with ξ
    rw [neg_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ φ ξ)
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hout : IntegrableOn (fun ξ : E d => ‖ξ‖ ^ a * ‖φ ξ‖) (Metric.ball 0 1)ᶜ := by
    set N : ℕ := ⌈a⌉₊
    have hN := (φ.integrable_pow_mul volume N).integrableOn (s := (Metric.ball (0 : E d) 1)ᶜ)
    refine hN.mono' hmeas.restrict ?_
    rw [ae_restrict_iff' measurableSet_ball.compl]
    filter_upwards with ξ hξ
    have h1 : 1 ≤ ‖ξ‖ := by simpa [Metric.mem_ball, dist_zero_right] using hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil a)
  have := hball.union hout
  rwa [union_compl_self, integrableOn_univ] at this

/-- `∫₀^∞ sᵐ e^{-b s³} ds`. -/
lemma integrableOn_pow_mul_exp_cube (m : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s ^ m * Real.exp (-b * s ^ 3)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (m : ℝ)) (p := 3) (b := b)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) (by norm_num) hb
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  simp only
  rw [Real.rpow_natCast, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma integral_pow_mul_exp_cube (m : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ s in Ioi (0 : ℝ), s ^ m * Real.exp (-b * s ^ 3) =
      b ^ (-((m : ℝ) + 1) / 3) * (1 / 3) * Real.Gamma (((m : ℝ) + 1) / 3) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := (m : ℝ)) (b := b) (by norm_num)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) hb
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  rw [Real.rpow_natCast, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma one_add_pow_le (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : (1 + s) ^ n ≤ 2 ^ n * (1 + s ^ n) := by
  rcases le_total s 1 with h | h
  · calc (1 + s) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + s ^ n) := by
        have : 0 ≤ s ^ n := pow_nonneg hs n
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
  · calc (1 + s) ^ n ≤ (2 * s) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * s ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + s ^ n) := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

/-- For fixed `ξ ≠ 0`, the `s`-section of `kB` is integrable, with an explicit bound. -/
lemma kB_section (h : E d → ℂ) (n : ℕ) {ξ : E d} (hξ : ξ ≠ 0) :
    IntegrableOn (fun s => kB h n (s, ξ)) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), kB h n (s, ξ) ≤
        ‖𝓕 h ξ‖ * (2 * π * ‖ξ‖) ^ n * 2 ^ n *
          ((4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) ^ (-((0 : ℝ) + 1) / 3) * (1 / 3) *
              Real.Gamma (((0 : ℝ) + 1) / 3) +
            (4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 1) / 3) * (1 / 3) *
              Real.Gamma (((n : ℝ) + 1) / 3)) := by
  set b := 4 * π ^ 2 / 3 * ‖ξ‖ ^ 2 with hb_def
  have hb : 0 < b := by
    have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    positivity
  set K := ‖𝓕 h ξ‖ * (2 * π * ‖ξ‖) ^ n * 2 ^ n with hK
  have hK0 : 0 ≤ K := by positivity
  have hI0 := integrableOn_pow_mul_exp_cube 0 hb
  have hIn := integrableOn_pow_mul_exp_cube n hb
  have hsum : IntegrableOn (fun s : ℝ => K * (s ^ 0 * Real.exp (-b * s ^ 3) +
      s ^ n * Real.exp (-b * s ^ 3))) (Ioi 0) := (hI0.add hIn).const_mul K
  have hle : ∀ s ∈ Ioi (0 : ℝ), kB h n (s, ξ) ≤
      K * (s ^ 0 * Real.exp (-b * s ^ 3) + s ^ n * Real.exp (-b * s ^ 3)) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    unfold kB
    simp only [abs_of_nonneg hs0]
    have e1 : Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) = Real.exp (-b * s ^ 3) := by
      congr 1; rw [hb_def]; ring
    have e2 : (2 * π * ((1 + s) * ‖ξ‖)) ^ n = (2 * π * ‖ξ‖) ^ n * (1 + s) ^ n := by
      rw [show 2 * π * ((1 + s) * ‖ξ‖) = (2 * π * ‖ξ‖) * (1 + s) by ring, mul_pow]
    rw [e1, e2, hK]
    have h1 := one_add_pow_le n hs0
    have hA : 0 ≤ ‖𝓕 h ξ‖ * Real.exp (-b * s ^ 3) * (2 * π * ‖ξ‖) ^ n := by positivity
    calc ‖𝓕 h ξ‖ * Real.exp (-b * s ^ 3) * ((2 * π * ‖ξ‖) ^ n * (1 + s) ^ n)
        = (‖𝓕 h ξ‖ * Real.exp (-b * s ^ 3) * (2 * π * ‖ξ‖) ^ n) * (1 + s) ^ n := by ring
      _ ≤ (‖𝓕 h ξ‖ * Real.exp (-b * s ^ 3) * (2 * π * ‖ξ‖) ^ n) * (2 ^ n * (1 + s ^ n)) :=
          mul_le_mul_of_nonneg_left h1 hA
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (fun s => kB h n (s, ξ)) (volume.restrict (Ioi 0)) := by
    apply Continuous.aestronglyMeasurable
    show Continuous (fun s : ℝ => ‖𝓕 h ξ‖ * Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) *
      (2 * π * ((1 + |s|) * ‖ξ‖)) ^ n)
    fun_prop
  have hint : IntegrableOn (fun s => kB h n (s, ξ)) (Ioi 0) := by
    refine hsum.mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (kB_nonneg _ _ _)]
    exact hle s hs
  refine ⟨hint, ?_⟩
  calc ∫ s in Ioi (0 : ℝ), kB h n (s, ξ)
      ≤ ∫ s in Ioi (0 : ℝ), K * (s ^ 0 * Real.exp (-b * s ^ 3) + s ^ n * Real.exp (-b * s ^ 3)) :=
        setIntegral_mono_on hint hsum measurableSet_Ioi hle
    _ = K * ((∫ s in Ioi (0 : ℝ), s ^ 0 * Real.exp (-b * s ^ 3)) +
          ∫ s in Ioi (0 : ℝ), s ^ n * Real.exp (-b * s ^ 3)) := by
        rw [integral_const_mul, integral_add hI0 hIn]
    _ = _ := by
        rw [integral_pow_mul_exp_cube 0 hb, integral_pow_mul_exp_cube n hb]
        push_cast
        ring

lemma continuous_kB (hS : 𝓢(E d, ℂ)) (n : ℕ) : Continuous (kB (⇑hS) n) := by
  unfold kB
  have : Continuous (fun a : ℝ × E d => ‖𝓕 (⇑hS) a.2‖) := by
    rw [← fourier_coe]
    exact (𝓕 hS).continuous.norm.comp continuous_snd
  fun_prop

/-- The dominating functions are integrable (this is where `d ≥ 1` and the Schwartz decay of `ĥ`
are used; near `ξ = 0` the bound behaves like `|ξ|^{-2/3}`). -/
theorem integrable_kB (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (n : ℕ) :
    Integrable (kB (⇑hS) n) (μK d) := by
  have hmeas : AEStronglyMeasurable (kB (⇑hS) n) (μK d) :=
    (continuous_kB hS n).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [ae_ne_zero_E hd] with ξ hξ
    exact (kB_section (⇑hS) n hξ).1
  · -- the bound, as a function of `ξ`
    set c := 4 * π ^ 2 / 3 with hc
    have hc0 : 0 < c := by positivity
    set G : E d → ℝ := fun ξ => ‖𝓕 (⇑hS) ξ‖ * (2 * π * ‖ξ‖) ^ n * 2 ^ n *
          ((c * ‖ξ‖ ^ 2) ^ (-((0 : ℝ) + 1) / 3) * (1 / 3) * Real.Gamma (((0 : ℝ) + 1) / 3) +
            (c * ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 1) / 3) * (1 / 3) * Real.Gamma (((n : ℝ) + 1) / 3))
      with hG
    -- `G` agrees a.e. with a combination of `|ξ|^a |𝓕h(ξ)|`
    set A1 : ℝ := (2 * π) ^ n * 2 ^ n * (c ^ (-((0 : ℝ) + 1) / 3) * (1 / 3) *
      Real.Gamma (((0 : ℝ) + 1) / 3))
    set A2 : ℝ := (2 * π) ^ n * 2 ^ n * (c ^ (-((n : ℝ) + 1) / 3) * (1 / 3) *
      Real.Gamma (((n : ℝ) + 1) / 3))
    set a1 : ℝ := (n : ℝ) + 2 * (-((0 : ℝ) + 1) / 3)
    set a2 : ℝ := (n : ℝ) + 2 * (-((n : ℝ) + 1) / 3)
    have hFS : ∀ ξ, ‖𝓕 (⇑hS) ξ‖ = ‖(𝓕 hS) ξ‖ := fun ξ => by rw [fourier_coe]
    have hGi : Integrable (fun ξ : E d => A1 * (‖ξ‖ ^ a1 * ‖(𝓕 hS) ξ‖) +
        A2 * (‖ξ‖ ^ a2 * ‖(𝓕 hS) ξ‖)) := by
      have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      refine ((integrable_rpow_mul_norm_schwartz hd (𝓕 hS) ?_).const_mul A1).add
        ((integrable_rpow_mul_norm_schwartz hd (𝓕 hS) ?_).const_mul A2)
      · simp only [a1]; linarith
      · simp only [a2]; linarith
    have hGae : G =ᵐ[volume] fun ξ : E d => A1 * (‖ξ‖ ^ a1 * ‖(𝓕 hS) ξ‖) +
        A2 * (‖ξ‖ ^ a2 * ‖(𝓕 hS) ξ‖) := by
      filter_upwards [ae_ne_zero_E hd] with ξ hξ
      have hξp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      simp only [hG, hFS]
      have key : ∀ r : ℝ, (c * ‖ξ‖ ^ 2) ^ r = c ^ r * ‖ξ‖ ^ (2 * r) := by
        intro r
        rw [Real.mul_rpow hc0.le (by positivity), ← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul hξp.le]
        norm_num
      rw [key, key, mul_pow]
      have e1 : ‖ξ‖ ^ n * ‖ξ‖ ^ (2 * (-((0 : ℝ) + 1) / 3)) = ‖ξ‖ ^ a1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hξp]
      have e2 : ‖ξ‖ ^ n * ‖ξ‖ ^ (2 * (-((n : ℝ) + 1) / 3)) = ‖ξ‖ ^ a2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hξp]
      rw [← e1, ← e2]
      simp only [A1, A2]
      ring
    have hGint : Integrable G := hGi.congr hGae.symm
    refine hGint.mono' ?_ ?_
    · exact ((continuous_kB hS n).norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    · filter_upwards [ae_ne_zero_E hd] with ξ hξ
      have h1 := (kB_section (⇑hS) n hξ).2
      have e : (fun s => ‖kB (⇑hS) n (s, ξ)‖) = fun s => kB (⇑hS) n (s, ξ) := by
        funext s; rw [Real.norm_eq_abs, abs_of_nonneg (kB_nonneg _ _ _)]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => norm_nonneg _), e]
      exact h1

/-! ### Smoothness of the solution operator -/

lemma continuous_kAmp (hS : 𝓢(E d, ℂ)) : Continuous (kAmp (d := d) ⇑hS) := by
  unfold kAmp
  have h1 : Continuous (fun a : ℝ × E d => 𝓕 (⇑hS) a.2) := by
    rw [← fourier_coe]; exact (𝓕 hS).continuous.comp continuous_snd
  have h2 : Continuous (fun a : ℝ × E d => Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2))) := by
    fun_prop
  exact h1.mul (Complex.continuous_ofReal.comp h2)

lemma contDiff_kAmp (hS : 𝓢(E d, ℂ)) : ContDiff ℝ ∞ (kAmp (d := d) ⇑hS) := by
  unfold kAmp
  have h1 : ContDiff ℝ ∞ (fun a : ℝ × E d => 𝓕 (⇑hS) a.2) := by
    rw [← fourier_coe]; exact ((𝓕 hS).smooth ⊤).comp contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun a : ℝ × E d => Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2))) := by
    apply Real.contDiff_exp.comp
    exact ((contDiff_const.mul (contDiff_fst.pow 3)).mul
      ((contDiff_norm_sq ℝ).comp contDiff_snd)).neg
  exact h1.mul (Complex.ofRealCLM.contDiff.comp h2)

lemma contDiff_kPh_uncurry :
    ContDiff ℝ ∞ (fun q : (ℝ × E d) × (E d × E d) => kPh q.1 q.2) := by
  simp only [kPh_apply]
  have i1 : ContDiff ℝ ∞ (fun q : (ℝ × E d) × (E d × E d) => ⟪q.1.2, q.2.1⟫) :=
    contDiff_inner.comp (contDiff_fst.snd.prodMk contDiff_snd.fst)
  have i2 : ContDiff ℝ ∞ (fun q : (ℝ × E d) × (E d × E d) => ⟪q.1.2, q.2.2⟫) :=
    contDiff_inner.comp (contDiff_fst.snd.prodMk contDiff_snd.snd)
  exact i1.sub (contDiff_fst.fst.mul i2)

lemma contDiff_kInt_uncurry (hS : 𝓢(E d, ℂ)) :
    ContDiff ℝ ∞ (Function.uncurry
      (fun (a : ℝ × E d) (p : E d × E d) => kAmp ⇑hS a * ech (kPh a p))) :=
  ((contDiff_kAmp hS).comp contDiff_fst).mul (contDiff_ech.comp contDiff_kPh_uncurry)

lemma continuous_kPh_apply (q : E d × E d) : Continuous (fun a : ℝ × E d => kPh a q) :=
  continuous_kPh.clm_apply continuous_const

lemma integrable_kInt (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (p : E d × E d) :
    Integrable (fun a => kAmp ⇑hS a * ech (kPh a p)) (μK d) := by
  refine (integrable_kB hd hS 0).mono'
    ((continuous_kAmp hS).mul (contDiff_ech.continuous.comp
      (continuous_kPh_apply p))).aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  rw [norm_mul, norm_ech, mul_one, norm_kAmp, kB, pow_zero, mul_one]

/-- **Smoothness** of `𝒮h` (Fourier form). -/
theorem contDiff_kinF (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) : ContDiff ℝ ∞ (kinF (d := d) ⇑hS) := by
  have hjoint := contDiff_kInt_uncurry hS
  apply contDiff_integral_of_bound (F := fun p a => kAmp ⇑hS a * ech (kPh a p)) (μ := μK d)
    (b := kB ⇑hS)
  · intro a; exact contDiff_const.mul (contDiff_ech.comp (kPh a).contDiff)
  · intro n p
    have := contDiff_iteratedFDeriv_param
      (F := fun (a : ℝ × E d) (p : E d × E d) => kAmp ⇑hS a * ech (kPh a p)) hjoint n
    exact (this.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact integrable_kB hd hS
  · intro n p a
    refine (norm_iteratedFDeriv_mul_ech_comp _ _ n p).trans ?_
    rw [norm_kAmp]
    unfold kB
    have h1 := norm_kPh_le a
    have h2 : 0 ≤ ‖𝓕 (⇑hS) a.2‖ * Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2)) := by
      positivity
    apply mul_le_mul_of_nonneg_left _ h2
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### Derivatives under the integral sign -/

lemma fderiv_int_ech (c : ℝ × E d → ℂ) (hc : Continuous c)
    (hint : Integrable (fun a => ‖c a‖) (μK d))
    (hint1 : Integrable (fun a => 2 * π * (‖c a‖ * ‖kPh a‖)) (μK d)) (p₀ q : E d × E d) :
    fderiv ℝ (fun p => ∫ a, c a * ech (kPh a p) ∂(μK d)) p₀ q =
      ∫ a, c a * ((2 * π * I) * (kPh a q : ℂ)) * ech (kPh a p₀) ∂(μK d) := by
  apply fderiv_integral_ech_apply c kPh
  · intro p
    exact (hc.mul (contDiff_ech.continuous.comp (continuous_kPh_apply p))).aestronglyMeasurable
  · have hz : Continuous (fun a => c a * (2 * π * I) * ech (kPh a p₀)) :=
      (hc.mul continuous_const).mul (contDiff_ech.continuous.comp (continuous_kPh_apply p₀))
    have : Continuous (fun a => (kPh a).smulRight (c a * (2 * π * I) * ech (kPh a p₀))) := by
      have h := ((ContinuousLinearMap.smulRightL ℝ (E d × E d) ℂ).continuous.comp
        continuous_kPh).clm_apply hz
      refine h.congr (fun a => ?_)
      exact ContinuousLinearMap.ext fun y => by simp
    exact this.aestronglyMeasurable
  · exact hint
  · exact hint1

lemma norm_mul_kPh_le (hS : 𝓢(E d, ℂ)) (a : ℝ × E d) :
    2 * π * (‖kAmp ⇑hS a‖ * ‖kPh a‖) ≤ kB ⇑hS 1 a := by
  rw [norm_kAmp, kB, pow_one]
  have h1 := norm_kPh_le a
  set A := ‖𝓕 (⇑hS) a.2‖ * Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2))
  have h2 : 0 ≤ 2 * π * A := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  calc 2 * π * (A * ‖kPh a‖) = 2 * π * A * ‖kPh a‖ := by ring
    _ ≤ 2 * π * A * ((1 + |a.1|) * ‖a.2‖) := h3
    _ = A * (2 * π * ((1 + |a.1|) * ‖a.2‖)) := by ring

/-- First derivative of `𝒮h` under the integral sign. -/
theorem fderiv_kinF (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (p q : E d × E d) :
    fderiv ℝ (kinF ⇑hS) p q =
      ∫ a, kAmp ⇑hS a * ((2 * π * I) * (kPh a q : ℂ)) * ech (kPh a p) ∂(μK d) := by
  have e : kinF (d := d) ⇑hS = fun p => ∫ a, kAmp ⇑hS a * ech (kPh a p) ∂(μK d) := rfl
  rw [e]
  apply fderiv_int_ech _ (continuous_kAmp hS)
  · refine (integrable_kB hd hS 0).mono' (continuous_kAmp hS).norm.aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    rw [norm_norm, norm_kAmp, kB, pow_zero, mul_one]
  · refine (integrable_kB hd hS 1).mono' ?_ (Eventually.of_forall fun a => ?_)
    · exact (continuous_const.mul ((continuous_kAmp hS).norm.mul
        continuous_kPh.norm)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact norm_mul_kPh_le hS a

/-- Second derivative of `𝒮h` under the integral sign. -/
theorem fderiv_fderiv_kinF (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (p q q' : E d × E d) :
    fderiv ℝ (fun p => fderiv ℝ (kinF ⇑hS) p q) p q' =
      ∫ a, kAmp ⇑hS a * ((2 * π * I) * (kPh a q : ℂ)) * ((2 * π * I) * (kPh a q' : ℂ)) *
        ech (kPh a p) ∂(μK d) := by
  have e : (fun p => fderiv ℝ (kinF ⇑hS) p q) = fun p =>
      ∫ a, (kAmp ⇑hS a * ((2 * π * I) * (kPh a q : ℂ))) * ech (kPh a p) ∂(μK d) := by
    funext p; rw [fderiv_kinF hd hS]
  rw [e]
  have hnorm : ∀ a, ‖kAmp ⇑hS a * ((2 * π * I) * (kPh a q : ℂ))‖ =
      ‖kAmp ⇑hS a‖ * (2 * π * |kPh a q|) := by
    intro a
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  have hkq : ∀ a, |kPh a q| ≤ ‖kPh a‖ * ‖q‖ := fun a => by
    rw [← Real.norm_eq_abs]; exact (kPh a).le_opNorm q
  have hc : Continuous (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a q : ℂ))) :=
    (continuous_kAmp hS).mul (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_kPh_apply q)))
  rw [fderiv_int_ech _ hc]
  · refine ((integrable_kB hd hS 1).mul_const ‖q‖).mono' hc.norm.aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    rw [norm_norm, hnorm]
    have h1 := norm_mul_kPh_le hS a
    have h2 := hkq a
    calc ‖kAmp ⇑hS a‖ * (2 * π * |kPh a q|) ≤ ‖kAmp ⇑hS a‖ * (2 * π * (‖kPh a‖ * ‖q‖)) := by
          gcongr
      _ = (2 * π * (‖kAmp ⇑hS a‖ * ‖kPh a‖)) * ‖q‖ := by ring
      _ ≤ kB ⇑hS 1 a * ‖q‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  · refine ((integrable_kB hd hS 2).mul_const ‖q‖).mono' ?_ (Eventually.of_forall fun a => ?_)
    · exact (continuous_const.mul (hc.norm.mul continuous_kPh.norm)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnorm]
      have h2 := hkq a
      have h4 := norm_kPh_le a
      rw [norm_kAmp, kB]
      set A := ‖𝓕 (⇑hS) a.2‖ * Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2))
      have hA : 0 ≤ A := by positivity
      have hk : 0 ≤ ‖kPh a‖ := norm_nonneg _
      have hB : ‖kPh a‖ ≤ (1 + |a.1|) * ‖a.2‖ := h4
      have hq : 0 ≤ ‖q‖ := norm_nonneg _
      have hπ : 0 < π := Real.pi_pos
      calc 2 * π * (A * (2 * π * |kPh a q|) * ‖kPh a‖)
          ≤ 2 * π * (A * (2 * π * (‖kPh a‖ * ‖q‖)) * ‖kPh a‖) := by gcongr
        _ = A * (2 * π * ‖kPh a‖) ^ 2 * ‖q‖ := by ring
        _ ≤ A * (2 * π * ((1 + |a.1|) * ‖a.2‖)) ^ 2 * ‖q‖ := by gcongr
        _ = _ := rfl

/-! ### The physical and Fourier forms agree -/

theorem kin_eq_kinF (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (x v : E d) :
    kin (⇑hS) x v = kinF (⇑hS) (x, v) := by
  unfold kinF
  rw [integral_prod _ (integrable_kInt hd hS (x, v))]
  unfold kin
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0 : ℝ) < s ^ 3 / 3 := by
    have : 0 < s := hs
    positivity
  rw [heat_eq_fourier hs' hS.integrable]
  congr 1
  funext ξ
  unfold kAmp ech
  rw [kPh_apply]
  dsimp only
  rw [mul_assoc (𝓕 (⇑hS) ξ), Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  rw [inner_sub_left, real_inner_smul_left, real_inner_comm ξ x, real_inner_comm ξ v]
  push_cast
  ring

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_SolOp

-- ============================================================================
-- KineticCounterexamples/Endpoint/KinEq.lean
-- ============================================================================

section File_Endpoint_KinEq

/-!
# The equation `v·∇ₓ 𝒮h = Δᵥ 𝒮h + h` and the velocity Hessian at `v = 0`

All statements are about the complex-valued smooth function `kinF h : ℝᵈ × ℝᵈ → ℂ` for a
Schwartz function `h`.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set SchwartzMap
open scoped FourierTransform RealInnerProductSpace ContDiff

namespace KS

variable {d : ℕ}

lemma inner_ev (ξ : E d) (i : Fin d) : ⟪ξ, ev i⟫ = ξ i := by
  simp [ev, EuclideanSpace.inner_single_right]

lemma sum_inner_ev_sq (ξ : E d) : ∑ i : Fin d, ⟪ξ, ev i⟫ ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [inner_ev]
  rw [EuclideanSpace.real_norm_sq_eq]

lemma kPh_v0 (a : ℝ × E d) (v : E d) : kPh a (v, 0) = ⟪a.2, v⟫ := by simp

lemma kPh_0e (a : ℝ × E d) (w : E d) : kPh a (0, w) = -(a.1 * ⟪a.2, w⟫) := by simp

/-- The profile `F(s) = e^{-(4π²/3)|ξ|² s³} e^{-2πi s⟨ξ,v⟩}` and its derivative. -/
lemma hasDerivAt_profile (ξ v : E d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        ech (-(s * ⟪ξ, v⟫)))
      (-(((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) * ech (-(s * ⟪ξ, v⟫)) *
        (2 * π * I * ⟪ξ, v⟫ + 4 * π ^ 2 * s ^ 2 * ‖ξ‖ ^ 2))) s := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)))
      (Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) * (-(4 * π ^ 2 / 3 * (3 * s ^ 2) * ‖ξ‖ ^ 2)))
      s := by
    have := (((hasDerivAt_pow 3 s).const_mul (4 * π ^ 2 / 3)).mul_const (‖ξ‖ ^ 2)).neg.exp
    convert this using 1
  have h2 : HasDerivAt (fun s : ℝ => ech (-(s * ⟪ξ, v⟫)))
      (2 * π * I * ech (-(s * ⟪ξ, v⟫)) * ((-⟪ξ, v⟫ : ℝ) : ℂ)) s := by
    set w : ℝ := ⟪ξ, v⟫ with hw
    have hl : HasDerivAt (fun s : ℝ => -(s * w)) (-w) s := (hasDerivAt_mul_const w).fun_neg
    have := (hasDerivAt_ech (-(s * w))).scomp s hl
    refine this.congr_deriv ?_
    rw [Complex.real_smul]
    push_cast
    ring
  have h3 := h1.ofReal_comp.mul h2
  convert h3 using 1
  push_cast
  ring

theorem kinF_equation (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (x v : E d) :
    fderiv ℝ (kinF ⇑hS) (x, v) (v, 0) -
      ∑ i : Fin d, fderiv ℝ (fun p => fderiv ℝ (kinF ⇑hS) p (0, ev i)) (x, v) (0, ev i) =
    hS x := by
  -- step 1: collect everything into a single integral
  set Q : ℝ × E d → ℂ := fun a => kAmp ⇑hS a * ech (kPh a (x, v)) *
    (2 * π * I * ⟪a.2, v⟫ + 4 * π ^ 2 * a.1 ^ 2 * ‖a.2‖ ^ 2) with hQ
  have hint1 : Integrable (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a (v, 0) : ℂ)) *
      ech (kPh a (x, v))) (μK d) := by
    have hc : Continuous (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a (v, 0) : ℂ)) *
        ech (kPh a (x, v))) :=
      ((continuous_kAmp hS).mul (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_kPh_apply _)))).mul (contDiff_ech.continuous.comp (continuous_kPh_apply _))
    refine ((integrable_kB hd hS 1).mul_const ‖(v, (0 : E d))‖).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    simp only [norm_mul, norm_ech, mul_one, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h1 := norm_mul_kPh_le hS a
    have h2 : ‖kPh a (v, 0)‖ ≤ ‖kPh a‖ * ‖(v, (0 : E d))‖ := (kPh a).le_opNorm _
    rw [← Real.norm_eq_abs]
    calc ‖kAmp ⇑hS a‖ * (2 * π * ‖kPh a (v, 0)‖)
        ≤ ‖kAmp ⇑hS a‖ * (2 * π * (‖kPh a‖ * ‖(v, (0 : E d))‖)) := by gcongr
      _ = 2 * π * (‖kAmp ⇑hS a‖ * ‖kPh a‖) * ‖(v, (0 : E d))‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hint2 : ∀ i : Fin d, Integrable (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a (0, ev i) : ℂ)) *
      ((2 * π * I) * (kPh a (0, ev i) : ℂ)) * ech (kPh a (x, v))) (μK d) := by
    intro i
    have hc : Continuous (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a (0, ev i) : ℂ)) *
        ((2 * π * I) * (kPh a (0, ev i) : ℂ)) * ech (kPh a (x, v))) :=
      (((continuous_kAmp hS).mul (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_kPh_apply _)))).mul (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_kPh_apply _)))).mul (contDiff_ech.continuous.comp (continuous_kPh_apply _))
    refine ((integrable_kB hd hS 2).mul_const (‖((0 : E d), ev i)‖ ^ 2)).mono'
      hc.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
    simp only [norm_mul, norm_ech, mul_one, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [← Real.norm_eq_abs, norm_kAmp, kB]
    have h2 : ‖kPh a (0, ev i)‖ ≤ ‖kPh a‖ * ‖((0 : E d), ev i)‖ := (kPh a).le_opNorm _
    have h4 := norm_kPh_le a
    set A := ‖𝓕 (⇑hS) a.2‖ * Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2))
    have hA : 0 ≤ A := by positivity
    have hπ : 0 < π := Real.pi_pos
    calc A * (2 * π * ‖kPh a (0, ev i)‖) * (2 * π * ‖kPh a (0, ev i)‖)
        ≤ A * (2 * π * (‖kPh a‖ * ‖((0 : E d), ev i)‖)) *
            (2 * π * (‖kPh a‖ * ‖((0 : E d), ev i)‖)) := by gcongr
      _ = A * (2 * π * ‖kPh a‖) ^ 2 * ‖((0 : E d), ev i)‖ ^ 2 := by ring
      _ ≤ A * (2 * π * ((1 + |a.1|) * ‖a.2‖)) ^ 2 * ‖((0 : E d), ev i)‖ ^ 2 := by gcongr
  have hsum := integral_finsetSum (μ := μK d) Finset.univ (fun i _ => hint2 i)
  have e1 : ∑ i : Fin d, fderiv ℝ (fun p => fderiv ℝ (kinF ⇑hS) p (0, ev i)) (x, v) (0, ev i) =
      ∫ a, ∑ i : Fin d, kAmp ⇑hS a * ((2 * π * I) * (kPh a (0, ev i) : ℂ)) *
        ((2 * π * I) * (kPh a (0, ev i) : ℂ)) * ech (kPh a (x, v)) ∂(μK d) := by
    rw [hsum]
    exact Finset.sum_congr rfl (fun i _ => fderiv_fderiv_kinF hd hS _ _ _)
  rw [e1, fderiv_kinF hd hS, ← integral_sub hint1 (integrable_finsetSum Finset.univ fun i _ => hint2 i)]
  have e2 : (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a (v, 0) : ℂ)) * ech (kPh a (x, v)) -
      ∑ i : Fin d, kAmp ⇑hS a * ((2 * π * I) * (kPh a (0, ev i) : ℂ)) *
        ((2 * π * I) * (kPh a (0, ev i) : ℂ)) * ech (kPh a (x, v))) = Q := by
    funext a
    simp only [hQ, kPh_v0, kPh_0e]
    have hs : ∑ i : Fin d, kAmp ⇑hS a * ((2 * π * I) * ((-(a.1 * ⟪a.2, ev i⟫) : ℝ) : ℂ)) *
        ((2 * π * I) * ((-(a.1 * ⟪a.2, ev i⟫) : ℝ) : ℂ)) * ech (kPh a (x, v)) =
        kAmp ⇑hS a * ech (kPh a (x, v)) * (-(4 * π ^ 2 * a.1 ^ 2) *
          ∑ i : Fin d, ((⟪a.2, ev i⟫ ^ 2 : ℝ) : ℂ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hs, ← Complex.ofReal_sum, sum_inner_ev_sq]
    push_cast
    ring
  rw [e2]
  -- step 2: Fubini, integrating first in `s`
  have hQi : Integrable Q (μK d) := by
    rw [← e2]
    exact hint1.sub (integrable_finsetSum Finset.univ fun i _ => hint2 i)
  rw [integral_prod_symm Q hQi]
  -- step 3: the `s`-integral is `ĥ(ξ) e^{2πi⟨ξ,x⟩}` for `ξ ≠ 0`
  have hinner : ∀ ξ : E d, ξ ≠ 0 → ∫ s in Ioi (0 : ℝ), Q (s, ξ) = 𝓕 (⇑hS) ξ * ech ⟪ξ, x⟫ := by
    intro ξ hξ
    set F : ℝ → ℂ := fun s => ((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        ech (-(s * ⟪ξ, v⟫)) with hF
    set F' : ℝ → ℂ := fun s => -(((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        ech (-(s * ⟪ξ, v⟫)) * (2 * π * I * ⟪ξ, v⟫ + 4 * π ^ 2 * s ^ 2 * ‖ξ‖ ^ 2)) with hF'
    have hQF : ∀ s, Q (s, ξ) = -(𝓕 (⇑hS) ξ * ech ⟪ξ, x⟫) * F' s := by
      intro s
      simp only [hQ, hF', kAmp, kPh_apply]
      rw [show ⟪ξ, x⟫ - s * ⟪ξ, v⟫ = ⟪ξ, x⟫ + -(s * ⟪ξ, v⟫) by ring, ech_add]
      ring
    have hb : 0 < 4 * π ^ 2 / 3 * ‖ξ‖ ^ 2 := by
      have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      positivity
    have hF'int : IntegrableOn F' (Ioi 0) := by
      have i0 := integrableOn_pow_mul_exp_cube 0 hb
      have i2 := integrableOn_pow_mul_exp_cube 2 hb
      have hsum : IntegrableOn (fun s : ℝ => 2 * π * |⟪ξ, v⟫| * (s ^ 0 *
          Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3)) + 4 * π ^ 2 * ‖ξ‖ ^ 2 *
          (s ^ 2 * Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3))) (Ioi 0) :=
        (i0.const_mul _).add (i2.const_mul _)
      have hc : Continuous F' := by
        simp only [hF']
        have c1 : Continuous (fun s : ℝ => ech (-(s * ⟪ξ, v⟫))) :=
          contDiff_ech.continuous.comp (by fun_prop)
        have c2 : Continuous (fun s : ℝ =>
            ((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (by fun_prop)
        have c3 : Continuous (fun s : ℝ => (2 * π * I * (⟪ξ, v⟫ : ℂ) +
            4 * π ^ 2 * (s : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2)) :=
          continuous_const.add ((continuous_const.mul
            (Complex.continuous_ofReal.pow 2)).mul continuous_const)
        exact ((c2.mul c1).mul c3).neg
      refine hsum.mono' hc.aestronglyMeasurable.restrict ?_
      filter_upwards with s
      simp only [hF', norm_neg, norm_mul, norm_ech, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have e : Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) =
          Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3) := by congr 1; ring
      rw [e]
      have hn : ‖(2 * π * I * (⟪ξ, v⟫ : ℂ) + 4 * π ^ 2 * (s : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2)‖ ≤
          2 * π * |⟪ξ, v⟫| + 4 * π ^ 2 * ‖ξ‖ ^ 2 * s ^ 2 := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_norm, sq_abs, mul_one]
        ring
      have hE : 0 < Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3) := Real.exp_pos _
      calc Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3) *
            ‖(2 * π * I * (⟪ξ, v⟫ : ℂ) + 4 * π ^ 2 * (s : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2)‖
          ≤ Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3) *
            (2 * π * |⟪ξ, v⟫| + 4 * π ^ 2 * ‖ξ‖ ^ 2 * s ^ 2) :=
            mul_le_mul_of_nonneg_left hn hE.le
        _ = _ := by ring
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (f := F) (f' := F') (a := 0) (m := 0)
      ((hasDerivAt_profile ξ v 0).continuousAt.continuousWithinAt)
      (fun s _ => hasDerivAt_profile ξ v s) hF'int ?_
    · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hQF s), integral_const_mul, hFTC]
      simp [hF, ech_zero]
    · -- `F → 0` at infinity
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun s => ‖F s‖) = fun s => Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3) := by
        funext s
        simp only [hF, norm_mul, norm_ech, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        congr 1; ring
      rw [this]
      apply Real.tendsto_exp_atBot.comp
      apply Tendsto.neg_mul_atTop (by linarith) tendsto_const_nhds
      exact tendsto_pow_atTop (by norm_num)
  have hae : (fun ξ => ∫ s in Ioi (0 : ℝ), Q (s, ξ)) =ᵐ[volume]
      fun ξ => 𝓕 (⇑hS) ξ * ech ⟪ξ, x⟫ := by
    filter_upwards [ae_ne_zero_E hd] with ξ hξ
    exact hinner ξ hξ
  rw [integral_congr_ae hae]
  -- step 4: Fourier inversion
  have hinv := Continuous.fourierInv_fourier_eq hS.continuous hS.integrable
    (by rw [← fourier_coe]; exact (𝓕 hS).integrable)
  have := congrFun hinv x
  rw [fourierInv_eq] at this
  rw [← this]
  congr 1
  funext ξ
  rw [Circle.smul_def, smul_eq_mul, mul_comm]
  rfl

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_KinEq

-- ============================================================================
-- KineticCounterexamples/Endpoint/Hess0.lean
-- ============================================================================

section File_Endpoint_Hess0

/-!
# The velocity Hessian of `𝒮h` on `{v = 0}`

* `hess0_kinF_s`: `∂_{v_i v_j} 𝒮h(x,0) = ∫₀^∞ s² ∂_{x_i x_j} P_{s³/3} h(x) ds`
  (written with `P_τ(∂ᵢ∂ⱼh)`);
* `hess0_kinF`: `∂_{v_i v_j} 𝒮h(x,0) = -∫ ĥ(ξ) ξᵢξⱼ/|ξ|² e^{2πi⟨ξ,x⟩} dξ`, i.e. the second order
  Riesz transform `∂ᵢ∂ⱼ(-Δ)^{-1} h` (4.4);
* `hess0_kinF_lap`: for `h = Δw`, `∂_{v_i v_j} 𝒮h(x,0) = -∂ᵢ∂ⱼ w(x)`.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set SchwartzMap
open scoped FourierTransform RealInnerProductSpace ContDiff LineDeriv

namespace KS

variable {d : ℕ}

lemma norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  simp [abs_of_pos Real.pi_pos]

lemma integrable_D2 (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (q q' p : E d × E d) :
    Integrable (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a q : ℂ)) *
      ((2 * π * I) * (kPh a q' : ℂ)) * ech (kPh a p)) (μK d) := by
  have hc : Continuous (fun a => kAmp ⇑hS a * ((2 * π * I) * (kPh a q : ℂ)) *
      ((2 * π * I) * (kPh a q' : ℂ)) * ech (kPh a p)) :=
    (((continuous_kAmp hS).mul (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_kPh_apply _)))).mul (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_kPh_apply _)))).mul (contDiff_ech.continuous.comp (continuous_kPh_apply _))
  refine ((integrable_kB hd hS 2).mul_const (‖q‖ * ‖q'‖)).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  simp only [norm_mul, norm_ech, mul_one, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_kAmp, kB]
  have h2 : ‖kPh a q‖ ≤ ‖kPh a‖ * ‖q‖ := (kPh a).le_opNorm _
  have h2' : ‖kPh a q'‖ ≤ ‖kPh a‖ * ‖q'‖ := (kPh a).le_opNorm _
  have h4 := norm_kPh_le a
  set A := ‖𝓕 (⇑hS) a.2‖ * Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2))
  have hA : 0 ≤ A := by positivity
  have hπ : 0 < π := Real.pi_pos
  calc A * (2 * π * ‖kPh a q‖) * (2 * π * ‖kPh a q'‖)
      ≤ A * (2 * π * (‖kPh a‖ * ‖q‖)) * (2 * π * (‖kPh a‖ * ‖q'‖)) := by gcongr
    _ = A * (2 * π * ‖kPh a‖) ^ 2 * (‖q‖ * ‖q'‖) := by ring
    _ ≤ A * (2 * π * ((1 + |a.1|) * ‖a.2‖)) ^ 2 * (‖q‖ * ‖q'‖) := by gcongr

/-- The integrand of the Hessian on `{v = 0}`. -/
lemma D2_integrand_v0 (hS : 𝓢(E d, ℂ)) (x : E d) (i j : Fin d) (a : ℝ × E d) :
    kAmp ⇑hS a * ((2 * π * I) * (kPh a (0, ev j) : ℂ)) * ((2 * π * I) * (kPh a (0, ev i) : ℂ)) *
      ech (kPh a (x, 0)) =
    ((a.1 ^ 2 : ℝ) : ℂ) * (𝓕 (⇑hS) a.2 * ((-(4 * π ^ 2 * ⟪a.2, ev i⟫ * ⟪a.2, ev j⟫) : ℝ) : ℂ) *
      ((Real.exp (-(4 * π ^ 2 / 3 * a.1 ^ 3 * ‖a.2‖ ^ 2)) : ℝ) : ℂ) * ech ⟪a.2, x⟫) := by
  simp only [kAmp, kPh_apply, inner_zero_right, mul_zero, sub_zero]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∂_{v_i v_j} 𝒮h(x,0)` as an iterated integral, `s` outside. -/
theorem hess0_kinF_s (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (x : E d) (i j : Fin d) :
    fderiv ℝ (fun p => fderiv ℝ (kinF ⇑hS) p (0, ev j)) (x, 0) (0, ev i) =
      ∫ s in Ioi (0 : ℝ), ((s ^ 2 : ℝ) : ℂ) * ∫ ξ, 𝓕 (⇑hS) ξ *
        ((-(4 * π ^ 2 * ⟪ξ, ev i⟫ * ⟪ξ, ev j⟫) : ℝ) : ℂ) *
        ((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) * ech ⟪ξ, x⟫ := by
  rw [fderiv_fderiv_kinF hd hS]
  have hi := integrable_D2 hd hS (0, ev j) (0, ev i) (x, 0)
  rw [integral_prod _ hi]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  simp_rw [D2_integrand_v0 hS x i j]
  rw [integral_const_mul]

/-- `∂_{v_i v_j} 𝒮h(x,0) = -∫ ĥ(ξ) ξᵢξⱼ/|ξ|² e^{2πi⟨ξ,x⟩} dξ` (the Riesz transform (4.4)). -/
theorem hess0_kinF (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (x : E d) (i j : Fin d) :
    fderiv ℝ (fun p => fderiv ℝ (kinF ⇑hS) p (0, ev j)) (x, 0) (0, ev i) =
      ∫ ξ, 𝓕 (⇑hS) ξ * ((-(⟪ξ, ev i⟫ * ⟪ξ, ev j⟫ / ‖ξ‖ ^ 2) : ℝ) : ℂ) * ech ⟪ξ, x⟫ := by
  rw [fderiv_fderiv_kinF hd hS]
  have hi := integrable_D2 hd hS (0, ev j) (0, ev i) (x, 0)
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [ae_ne_zero_E hd] with ξ hξ
  simp_rw [D2_integrand_v0 hS x i j]
  have hb : 0 < 4 * π ^ 2 / 3 * ‖ξ‖ ^ 2 := by
    have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    positivity
  have e : ∀ s : ℝ, ((s ^ 2 : ℝ) : ℂ) * (𝓕 (⇑hS) ξ * ((-(4 * π ^ 2 * ⟪ξ, ev i⟫ * ⟪ξ, ev j⟫) : ℝ) : ℂ) *
      ((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) * ech ⟪ξ, x⟫) =
      (𝓕 (⇑hS) ξ * ((-(4 * π ^ 2 * ⟪ξ, ev i⟫ * ⟪ξ, ev j⟫) : ℝ) : ℂ) * ech ⟪ξ, x⟫) *
        ((s ^ 2 * Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3) : ℝ) : ℂ) := by
    intro s
    have : Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2)) =
        Real.exp (-(4 * π ^ 2 / 3 * ‖ξ‖ ^ 2) * s ^ 3) := by congr 1; ring
    rw [this]; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, integral_complex_ofReal, integral_pow_mul_exp_cube 2 hb]
  have hξ2 : ‖ξ‖ ^ 2 ≠ 0 := by
    have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    positivity
  have h3 : (((2 : ℕ) : ℝ) + 1) / 3 = 1 := by norm_num
  have h3' : -(((2 : ℕ) : ℝ) + 1) / 3 = -1 := by norm_num
  rw [h3, h3', Real.Gamma_one, Real.rpow_neg_one]
  push_cast
  field_simp

/-! ### Fourier transform of derivatives of Schwartz functions -/

/-- The directional derivative `∂_m f` of a Schwartz function. -/
def dS (m : E d) (f : 𝓢(E d, ℂ)) : 𝓢(E d, ℂ) := ∂_{m} f

lemma dS_apply (m : E d) (f : 𝓢(E d, ℂ)) (x : E d) : dS m f x = fderiv ℝ f x m := rfl

lemma fourier_lineDeriv_apply (f : 𝓢(E d, ℂ)) (m ξ : E d) :
    𝓕 (⇑(dS m f)) ξ = (2 * π * I) * (⟪ξ, m⟫ : ℂ) * 𝓕 (⇑f) ξ := by
  unfold dS
  rw [← fourier_coe, SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : E d => ⟪x, m⟫).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [SchwartzMap.smul_apply, smulLeftCLM_apply_apply hg, fourier_coe, smul_eq_mul,
    Complex.real_smul]
  ring

lemma fourier_lineDeriv2_apply (f : 𝓢(E d, ℂ)) (m m' ξ : E d) :
    𝓕 (⇑(dS m (dS m' f))) ξ =
      ((-(4 * π ^ 2 * ⟪ξ, m⟫ * ⟪ξ, m'⟫) : ℝ) : ℂ) * 𝓕 (⇑f) ξ := by
  rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The `s`-section of the Hessian integrand is `s² P_{s³/3}(∂ᵢ∂ⱼ h)(x)`. -/
lemma sec_D2_heat (hS : 𝓢(E d, ℂ)) (x : E d) (i j : Fin d) {s : ℝ} (hs : 0 < s) :
    ∫ ξ, kAmp ⇑hS (s, ξ) * ((2 * π * I) * (kPh (s, ξ) (0, ev j) : ℂ)) *
        ((2 * π * I) * (kPh (s, ξ) (0, ev i) : ℂ)) * ech (kPh (s, ξ) (x, 0)) =
      ((s ^ 2 : ℝ) : ℂ) * heat (s ^ 3 / 3) (⇑(dS (ev i) (dS (ev j) hS))) x := by
  simp_rw [D2_integrand_v0 hS x i j]
  rw [integral_const_mul]
  have hs' : (0 : ℝ) < s ^ 3 / 3 := by positivity
  rw [heat_eq_fourier hs' (dS (ev i) (dS (ev j) hS)).integrable]
  congr 1
  congr 1
  funext ξ
  rw [fourier_lineDeriv2_apply]
  have hexp : (((Real.exp (-(4 * π ^ 2 / 3 * s ^ 3 * ‖ξ‖ ^ 2))) : ℝ) : ℂ) * ech ⟪ξ, x⟫ =
      cexp (-((4 * π ^ 2 * (s ^ 3 / 3) : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 + 2 * π * I * (⟪x, ξ⟫ : ℂ)) := by
    unfold ech
    rw [Complex.ofReal_exp, ← Complex.exp_add, real_inner_comm ξ x]
    congr 1
    push_cast
    ring
  rw [← hexp]
  ring

/-- `∂_{v_i v_j} 𝒮h(x,0) = ∫₀^∞ s² P_{s³/3}(∂ᵢ∂ⱼ h)(x) ds`. -/
theorem hess0_kinF_heat (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (x : E d) (i j : Fin d) :
    fderiv ℝ (fun p => fderiv ℝ (kinF ⇑hS) p (0, ev j)) (x, 0) (0, ev i) =
      ∫ s in Ioi (0 : ℝ), ((s ^ 2 : ℝ) : ℂ) * heat (s ^ 3 / 3) (⇑(dS (ev i) (dS (ev j) hS))) x := by
  rw [fderiv_fderiv_kinF hd hS]
  rw [integral_prod _ (integrable_D2 hd hS (0, ev j) (0, ev i) (x, 0))]
  exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => sec_D2_heat hS x i j hs)

lemma integrableOn_hess_heat (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (x : E d) (i j : Fin d) :
    IntegrableOn (fun s : ℝ => ((s ^ 2 : ℝ) : ℂ) *
      heat (s ^ 3 / 3) (⇑(dS (ev i) (dS (ev j) hS))) x) (Ioi 0) := by
  have h1 := (integrable_D2 hd hS (0, ev j) (0, ev i) (x, 0)).integral_prod_left
  exact IntegrableOn.congr_fun (s := Ioi 0) h1 (fun s hs => sec_D2_heat hS x i j hs)
    measurableSet_Ioi

/-! ### The case `h = Δw` -/

/-- The Laplacian of a Schwartz function. -/
def lapS (w : 𝓢(E d, ℂ)) : 𝓢(E d, ℂ) := ∑ i : Fin d, dS (ev i) (dS (ev i) w)

lemma lapS_apply (w : 𝓢(E d, ℂ)) (x : E d) :
    lapS w x = ∑ i : Fin d, (dS (ev i) (dS (ev i) w)) x := by
  simp [lapS]

lemma fourier_lapS_apply (w : 𝓢(E d, ℂ)) (ξ : E d) :
    𝓕 (⇑(lapS w)) ξ = ((-(4 * π ^ 2 * ‖ξ‖ ^ 2)) : ℝ) * 𝓕 (⇑w) ξ := by
  rw [← fourier_coe, ← fourierTransformCLM_apply (𝕜 := ℂ), lapS, map_sum, _root_.sum_apply]
  simp_rw [fourierTransformCLM_apply, fourier_coe, fourier_lineDeriv2_apply]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  rw [← sum_inner_ev_sq, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The identity used in Theorem 4.3**: for `h = Δw`, `∂_{v_i v_j} 𝒮h(x,0) = -∂ᵢ∂ⱼ w(x)`. -/
theorem hess0_kinF_lap (hd : 1 ≤ d) (w : 𝓢(E d, ℂ)) (x : E d) (i j : Fin d) :
    fderiv ℝ (fun p => fderiv ℝ (kinF ⇑(lapS w)) p (0, ev j)) (x, 0) (0, ev i) =
      -(dS (ev i) (dS (ev j) w)) x := by
  rw [hess0_kinF hd]
  have e : ∀ ξ : E d, 𝓕 (⇑(lapS w)) ξ * ((-(⟪ξ, ev i⟫ * ⟪ξ, ev j⟫ / ‖ξ‖ ^ 2) : ℝ) : ℂ) *
      ech ⟪ξ, x⟫ = -(ech ⟪ξ, x⟫ * 𝓕 (⇑(dS (ev i) (dS (ev j) w))) ξ) := by
    intro ξ
    rw [fourier_lapS_apply, fourier_lineDeriv2_apply]
    by_cases hξ : ξ = 0
    · subst hξ; simp
    · have hc : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hξ).ne'
      push_cast
      field_simp
  simp_rw [e]
  rw [integral_neg]
  congr 1
  have hinv := Continuous.fourierInv_fourier_eq (dS (ev i) (dS (ev j) w)).continuous
    (dS (ev i) (dS (ev j) w)).integrable
    (by rw [← fourier_coe]; exact (𝓕 (dS (ev i) (dS (ev j) w))).integrable)
  have := congrFun hinv x
  rw [fourierInv_eq] at this
  rw [← this]
  congr 1

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Hess0

-- ============================================================================
-- KineticCounterexamples/Endpoint/Lift.lean
-- ============================================================================

section File_Endpoint_Lift

/-!
# Stationary solutions on `ℝ_t × ℝᵈ_x × ℝᵈ_v`

For a real forcing `g`, the stationary function `f(t,x,v) = Re 𝒮g(x,v)` (`solF`).

* for `g ∈ C_c^∞`: `f` is smooth and solves `(∂_t + v·∇_x) f = Δ_v f + g` everywhere
  (`solF_smooth`, `solF_KFP`), and its velocity Hessian is given by the formulas of `Hess0`;
* for any bounded integrable `g`: the heat-kernel bound `|f| ≤ ∫₀^∞ min(K, (4πs³/3)^{-d/2} L) ds`
  with `K = sup|g|`, `L = ‖g‖_{L¹}` (`abs_solF_le`).
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set SchwartzMap
open scoped FourierTransform RealInnerProductSpace ContDiff

namespace KS

variable {d : ℕ}

/-- The stationary solution `f(t,x,v) = Re 𝒮h(x,v)` (formula (4.3)). -/
def solF (h : E d → ℂ) (p : Pt d) : ℝ := (kin h p.2.1 p.2.2).re

/-! ### Generic facts about stationary lifts `f(t,x,v) = Re K(x,v)` -/

/-- The stationary lift of `K : ℝᵈ × ℝᵈ → ℂ`. -/
def liftK (K : E d × E d → ℂ) (p : Pt d) : ℝ := (K (p.2.1, p.2.2)).re

lemma contDiff_liftK {K : E d × E d → ℂ} (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (liftK K) :=
  Complex.reCLM.contDiff.comp (hK.comp (contDiff_snd.fst.prodMk contDiff_snd.snd))

lemma dT_liftK (K : E d × E d → ℂ) (p : Pt d) : dT (liftK K) p = 0 := by
  unfold dT liftK
  simp

lemma fderiv_slice_x {K : E d × E d → ℂ} (hK : Differentiable ℝ K) (x w e : E d) :
    fderiv ℝ (fun y => (K (y, w)).re) x e = (fderiv ℝ K (x, w) (e, 0)).re := by
  have h1 : HasFDerivAt (fun y => K (y, w))
      ((fderiv ℝ K (x, w)).comp (ContinuousLinearMap.inl ℝ (E d) (E d))) x :=
    (hK (x, w)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x w)
  have h2 : HasFDerivAt (fun y => (K (y, w)).re) _ x := Complex.reCLM.hasFDerivAt.comp x h1
  rw [h2.fderiv]
  simp

lemma fderiv_slice_v {K : E d × E d → ℂ} (hK : Differentiable ℝ K) (x w e : E d) :
    fderiv ℝ (fun w' => (K (x, w')).re) w e = (fderiv ℝ K (x, w) (0, e)).re := by
  have h1 : HasFDerivAt (fun w' => K (x, w'))
      ((fderiv ℝ K (x, w)).comp (ContinuousLinearMap.inr ℝ (E d) (E d))) w :=
    (hK (x, w)).hasFDerivAt.comp w (hasFDerivAt_prodMk_right x w)
  have h2 : HasFDerivAt (fun w' => (K (x, w')).re) _ w := Complex.reCLM.hasFDerivAt.comp w h1
  rw [h2.fderiv]
  simp

lemma transport_liftK {K : E d × E d → ℂ} (hK : Differentiable ℝ K) (t : ℝ) (x v : E d) :
    transport (liftK K) (t, x, v) = (fderiv ℝ K (x, v) (v, 0)).re := by
  unfold transport gradX liftK
  exact fderiv_slice_x hK x v v

lemma hessV_liftK {K : E d × E d → ℂ} (hK : ContDiff ℝ ∞ K) (t : ℝ) (x v : E d) (i j : Fin d) :
    hessV (liftK K) (t, x, v) i j =
      (fderiv ℝ (fun q => fderiv ℝ K q (0, ev j)) (x, v) (0, ev i)).re := by
  have hdiff : Differentiable ℝ K := hK.differentiable (by simp)
  unfold hessV liftK
  simp only
  have e : (fun w => fderiv ℝ (fun w' => (K (x, w')).re) w (ev j)) =
      fun w => (fderiv ℝ K (x, w) (0, ev j)).re := by
    funext w; exact fderiv_slice_v hdiff x w (ev j)
  rw [e]
  have hG : Differentiable ℝ (fun q : E d × E d => fderiv ℝ K q (0, ev j)) := by
    have : ContDiff ℝ ∞ (fun q : E d × E d => fderiv ℝ K q (0, ev j)) :=
      (hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact this.differentiable (by simp)
  exact fderiv_slice_v hG x v (ev i)

lemma continuous_hessV_liftK {K : E d × E d → ℂ} (hK : ContDiff ℝ ∞ K) (i j : Fin d) :
    Continuous (fun q : E d × E d => hessV (liftK K) (0, q.1, q.2) i j) := by
  have e : (fun q : E d × E d => hessV (liftK K) (0, q.1, q.2) i j) =
      fun q => (fderiv ℝ (fun q => fderiv ℝ K q (0, ev j)) q (0, ev i)).re := by
    funext q; exact hessV_liftK hK 0 q.1 q.2 i j
  rw [e]
  have h1 : ContDiff ℝ ∞ (fun q : E d × E d => fderiv ℝ K q (0, ev j)) :=
    (hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2 : Continuous (fun q : E d × E d =>
      fderiv ℝ (fun q => fderiv ℝ K q (0, ev j)) q (0, ev i)) :=
    (h1.continuous_fderiv (by simp)).clm_apply continuous_const
  exact Complex.continuous_re.comp h2

lemma stationary_liftK (K : E d × E d → ℂ) (t t' : ℝ) (x v : E d) :
    liftK K (t, x, v) = liftK K (t', x, v) := rfl

/-- If `K` solves `v·∇ₓK - Δᵥ K = g` (with `g` real), the lift solves the KFP equation (4.1). -/
lemma KFP_liftK {K : E d × E d → ℂ} (hK : ContDiff ℝ ∞ K) (g : E d → ℝ)
    (heq : ∀ x v, fderiv ℝ K (x, v) (v, 0) -
      ∑ i : Fin d, fderiv ℝ (fun q => fderiv ℝ K q (0, ev i)) (x, v) (0, ev i) = (g x : ℂ))
    (p : Pt d) : KFP (liftK K) (fun _ => 1) (fun _ => 0) (fun p => g p.2.1) p := by
  obtain ⟨t, x, v⟩ := p
  have hdiff : Differentiable ℝ K := hK.differentiable (by simp)
  unfold KFP
  rw [dT_liftK, transport_liftK hdiff, Matrix.one_mul, Matrix.trace]
  simp only [Matrix.diag, hessV_liftK hK]
  have := congrArg Complex.re (heq x v)
  rw [Complex.sub_re, Complex.re_sum, Complex.ofReal_re] at this
  linarith

/-! ### The solution operator applied to real `C_c^∞` forcings -/

/-- A real `C_c^∞` function as a complex Schwartz function. -/
def toS (g : E d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) : 𝓢(E d, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (g x : ℂ)) (hgc.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp hg)

@[simp] lemma toS_apply (g : E d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : E d) : toS g hg hgc x = (g x : ℂ) := rfl

lemma coe_toS (g : E d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (⇑(toS g hg hgc) : E d → ℂ) = fun x => (g x : ℂ) := rfl

lemma solF_eq_liftK (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) : solF (⇑hS) = liftK (kinF ⇑hS) := by
  funext p
  unfold solF liftK
  rw [kin_eq_kinF hd hS]

theorem solF_smooth (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) : ContDiff ℝ ∞ (solF (⇑hS)) := by
  rw [solF_eq_liftK hd hS]
  exact contDiff_liftK (contDiff_kinF hd hS)

theorem solF_stationary (h : E d → ℂ) (t t' : ℝ) (x v : E d) :
    solF h (t, x, v) = solF h (t', x, v) := rfl

/-- **The equation (4.1)** for `f = Re 𝒮g`, `g ∈ C_c^∞` real. -/
theorem solF_KFP (hd : 1 ≤ d) (g : E d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (p : Pt d) :
    KFP (solF (fun y => (g y : ℂ))) (fun _ => 1) (fun _ => 0) (fun p => g p.2.1) p := by
  rw [← coe_toS g hg hgc, solF_eq_liftK hd]
  apply KFP_liftK (contDiff_kinF hd _) g
  intro x v
  rw [kinF_equation hd, toS_apply]

theorem hessV_solF (hd : 1 ≤ d) (hS : 𝓢(E d, ℂ)) (t : ℝ) (x v : E d) (i j : Fin d) :
    hessV (solF (⇑hS)) (t, x, v) i j =
      (fderiv ℝ (fun q => fderiv ℝ (kinF ⇑hS) q (0, ev j)) (x, v) (0, ev i)).re := by
  rw [solF_eq_liftK hd hS, hessV_liftK (contDiff_kinF hd hS)]

/-! ### The `L^∞` bound -/

/-- The heat-kernel bound for `𝒮` (§4): `∫₀^∞ min(K, (4π s³/3)^{-d/2} L) ds`. -/
def kinBd (d : ℕ) (K L : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), min K ((4 * π * (s ^ 3 / 3)) ^ (-(d : ℝ) / 2) * L)

lemma integrableOn_kinBd (hd : 1 ≤ d) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) :
    IntegrableOn (fun s : ℝ => min K ((4 * π * (s ^ 3 / 3)) ^ (-(d : ℝ) / 2) * L)) (Ioi 0) := by
  have hmeas : Measurable (fun s : ℝ => min K ((4 * π * (s ^ 3 / 3)) ^ (-(d : ℝ) / 2) * L)) := by
    fun_prop
  have h01 : IntegrableOn (fun s : ℝ => min K ((4 * π * (s ^ 3 / 3)) ^ (-(d : ℝ) / 2) * L))
      (Ioc 0 1) := by
    refine (integrableOn_const (C := K) (by simp)).mono' hmeas.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    have hs0 : 0 ≤ s := le_of_lt hs.1
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hK (mul_nonneg (Real.rpow_nonneg (by positivity) _) hL))]
    exact min_le_left _ _
  have h1 : IntegrableOn (fun s : ℝ => min K ((4 * π * (s ^ 3 / 3)) ^ (-(d : ℝ) / 2) * L))
      (Ioi 1) := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hp : IntegrableOn (fun s : ℝ => s ^ (-(3 * (d : ℝ) / 2))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine (hp.const_mul ((4 * π / 3) ^ (-(d : ℝ) / 2) * L)).mono'
      hmeas.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with s hs
    have hs0 : 0 < s := lt_trans one_pos hs
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hK (by positivity))]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [show 4 * π * (s ^ 3 / 3) = (4 * π / 3) * s ^ 3 by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast s 3,
      ← Real.rpow_mul hs0.le]
    ring_nf
  have := h01.union h1
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

lemma kinBd_mono (hd : 1 ≤ d) {K L L' : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hLL : L ≤ L') :
    kinBd d K L ≤ kinBd d K L' := by
  unfold kinBd
  apply setIntegral_mono_on (integrableOn_kinBd hd hK hL)
    (integrableOn_kinBd hd hK (hL.trans hLL)) measurableSet_Ioi
  intro s hs
  have hs0 : 0 ≤ s := le_of_lt hs
  apply min_le_min le_rfl
  exact mul_le_mul_of_nonneg_left hLL (Real.rpow_nonneg (by positivity) _)

theorem norm_kin_le (hd : 1 ≤ d) {h : E d → ℂ} (hh : Integrable h) {K : ℝ}
    (hK : ∀ y, ‖h y‖ ≤ K) (x v : E d) : ‖kin h x v‖ ≤ kinBd d K (∫ y, ‖h y‖) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hL0 : 0 ≤ ∫ y, ‖h y‖ := integral_nonneg fun y => norm_nonneg _
  unfold kin kinBd
  apply norm_integral_le_of_norm_le (integrableOn_kinBd hd hK0 hL0)
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with s hs
  have hs' : (0 : ℝ) < s ^ 3 / 3 := by
    have : 0 < s := hs
    positivity
  exact le_min (norm_heat_le_sup hs' hK _) (norm_heat_le_L1 hs' hh _)

theorem abs_solF_le (hd : 1 ≤ d) {h : E d → ℂ} (hh : Integrable h) {K : ℝ}
    (hK : ∀ y, ‖h y‖ ≤ K) (p : Pt d) : |solF h p| ≤ kinBd d K (∫ y, ‖h y‖) :=
  (Complex.abs_re_le_norm _).trans (norm_kin_le hd hh hK _ _)

/-- `‖g‖_{L¹} ≤ |B₁|` when `|g| ≤ 1` and `g` vanishes outside the unit ball. -/
lemma integral_norm_le_vol_ball {h : E d → ℂ} (hh : ∀ y, ‖h y‖ ≤ 1)
    (hs : ∀ y, 1 ≤ ‖y‖ → h y = 0) : ∫ y, ‖h y‖ ≤ (volume (Metric.ball (0 : E d) 1)).toReal := by
  have e : ∫ y, ‖h y‖ = ∫ y in Metric.ball (0 : E d) 1, ‖h y‖ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    have : 1 ≤ ‖y‖ := by simpa [Metric.mem_ball, dist_zero_right] using hy
    simp [hs y this]
  rw [e]
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (E d)))
    (s := Metric.ball (0 : E d) 1)
    (f := fun y => ‖h y‖) (C := 1) measure_ball_lt_top (fun y _ => by
      rw [norm_norm]; exact hh y)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _), one_mul] at this
  exact this

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Lift

-- ============================================================================
-- KineticCounterexamples/Endpoint/Phys.lean
-- ============================================================================

section File_Endpoint_Phys

/-!
# The heat-kernel form of `∂_{v_i v_j} f(0,0)`

For a real `g ∈ C_c^∞(ℝᵈ)` and `f = Re 𝒮g`:
`∂_{v_i v_j} f(t,0,0) = ∫₀^∞ s² ∫ ∂_j∂_i G_{s³/3}(y) g(y) dy ds`,
and for `i ≠ j`, `∂_j∂_i G_τ(y) = yᵢ yⱼ/(4τ²) G_τ(y)` (`hessV_solF_phys`).
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set SchwartzMap
open scoped FourierTransform RealInnerProductSpace ContDiff

namespace KS

variable {d : ℕ}

/-! ### Derivatives of the heat kernel -/

lemma hasFDerivAt_hk {τ : ℝ} (hτ : 0 < τ) (y : E d) :
    HasFDerivAt (hk d τ) ((-(hk d τ y / (2 * τ))) • innerSL ℝ y) y := by
  have h1 := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 : HasFDerivAt (fun x : E d => -‖x‖ ^ 2 / (4 * τ))
      ((-(1 / (2 * τ))) • innerSL ℝ y) y := by
    have := (h1.fun_neg).mul_const (1 / (4 * τ))
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_fderiv ?_
    · simp only; ring
    · ext m
      simp
      ring
  have h3 := (h2.exp).const_mul ((4 * π * τ) ^ (-(d : ℝ) / 2))
  have e : hk d τ = fun x => (4 * π * τ) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * τ)) := by
    funext x; rfl
  rw [e]
  refine h3.congr_fderiv ?_
  ext m
  simp [hk]
  ring

lemma fderiv_hk_apply {τ : ℝ} (hτ : 0 < τ) (y m : E d) :
    fderiv ℝ (hk d τ) y m = -(⟪y, m⟫ / (2 * τ)) * hk d τ y := by
  rw [(hasFDerivAt_hk hτ y).fderiv]
  simp
  ring

lemma differentiable_hk {τ : ℝ} (hτ : 0 < τ) : Differentiable ℝ (hk d τ) :=
  fun y => (hasFDerivAt_hk hτ y).differentiableAt

lemma hasFDerivAt_inner_left (m y : E d) :
    HasFDerivAt (fun z : E d => ⟪z, m⟫) (innerSL ℝ m) y := by
  have := (innerSL ℝ m).hasFDerivAt (x := y)
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp [real_inner_comm]

lemma hasFDerivAt_inner_div (τ : ℝ) (m y : E d) :
    HasFDerivAt (fun z : E d => -(⟪z, m⟫ / (2 * τ))) ((-(1 / (2 * τ))) • innerSL ℝ m) y := by
  have := ((hasFDerivAt_inner_left m y).mul_const (1 / (2 * τ))).fun_neg
  refine (this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_fderiv ?_
  · simp only; ring
  · rw [neg_smul]

lemma fderiv_fderiv_hk_apply {τ : ℝ} (hτ : 0 < τ) (y m m' : E d) :
    fderiv ℝ (fun z => fderiv ℝ (hk d τ) z m) y m' =
      (⟪y, m⟫ * ⟪y, m'⟫ / (4 * τ ^ 2) - ⟪m', m⟫ / (2 * τ)) * hk d τ y := by
  have e : (fun z => fderiv ℝ (hk d τ) z m) = fun z => -(⟪z, m⟫ / (2 * τ)) * hk d τ z := by
    funext z; exact fderiv_hk_apply hτ z m
  rw [e]
  have h := (hasFDerivAt_inner_div τ m y).fun_mul (hasFDerivAt_hk hτ y)
  rw [h.fderiv]
  simp
  rw [real_inner_comm m m']
  field_simp
  ring

lemma continuous_fderiv_hk_apply {τ : ℝ} (hτ : 0 < τ) (m : E d) :
    Continuous (fun y => fderiv ℝ (hk d τ) y m) := by
  have e : (fun y => fderiv ℝ (hk d τ) y m) = fun y => -(⟪y, m⟫ / (2 * τ)) * hk d τ y := by
    funext y; exact fderiv_hk_apply hτ y m
  rw [e]
  exact ((continuous_id.inner continuous_const).div_const _).neg.mul (continuous_hk τ)

lemma differentiable_fderiv_hk_apply {τ : ℝ} (hτ : 0 < τ) (m : E d) :
    Differentiable ℝ (fun y => fderiv ℝ (hk d τ) y m) := by
  have e : (fun y => fderiv ℝ (hk d τ) y m) = fun y => -(⟪y, m⟫ / (2 * τ)) * hk d τ y := by
    funext y; exact fderiv_hk_apply hτ y m
  rw [e]
  exact fun y => ((hasFDerivAt_inner_div τ m y).fun_mul (hasFDerivAt_hk hτ y)).differentiableAt

lemma continuous_fderiv_fderiv_hk_apply {τ : ℝ} (hτ : 0 < τ) (m m' : E d) :
    Continuous (fun y => fderiv ℝ (fun z => fderiv ℝ (hk d τ) z m) y m') := by
  have e : (fun y => fderiv ℝ (fun z => fderiv ℝ (hk d τ) z m) y m') = fun y =>
      (⟪y, m⟫ * ⟪y, m'⟫ / (4 * τ ^ 2) - ⟪m', m⟫ / (2 * τ)) * hk d τ y := by
    funext y; exact fderiv_fderiv_hk_apply hτ y m m'
  rw [e]
  exact ((((continuous_id.inner continuous_const).mul (continuous_id.inner continuous_const)).div_const
    _).sub continuous_const).mul (continuous_hk τ)

/-! ### Integration by parts against the heat kernel -/

lemma ibp_hk {τ : ℝ} (hτ : 0 < τ) (g : E d → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (m m' : E d) :
    ∫ y, hk d τ y * fderiv ℝ (fun z => fderiv ℝ g z m') y m =
      ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d τ) z m) y m' * g y := by
  have hg1 : ContDiff ℝ ∞ (fun z => fderiv ℝ g z m') :=
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hgc1 : HasCompactSupport (fun z => fderiv ℝ g z m') := hgc.fderiv_apply ℝ m'
  have hgc2 : HasCompactSupport (fun z => fderiv ℝ (fun z => fderiv ℝ g z m') z m) :=
    hgc1.fderiv_apply ℝ m
  have cg1 : Continuous (fun z => fderiv ℝ g z m') := hg1.continuous
  have cg2 : Continuous (fun z => fderiv ℝ (fun z => fderiv ℝ g z m') z m) :=
    (hg1.continuous_fderiv (by simp)).clm_apply continuous_const
  -- first integration by parts
  have step1 : ∫ y, hk d τ y * fderiv ℝ (fun z => fderiv ℝ g z m') y m =
      -∫ y, fderiv ℝ (hk d τ) y m * fderiv ℝ g y m' := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact ((continuous_fderiv_hk_apply hτ m).mul cg1).integrable_of_hasCompactSupport
        hgc1.mul_left
    · exact ((continuous_hk τ).mul cg2).integrable_of_hasCompactSupport hgc2.mul_left
    · exact ((continuous_hk τ).mul cg1).integrable_of_hasCompactSupport hgc1.mul_left
    · exact fun x _ => differentiable_hk hτ x
    · exact fun x _ => (hg1.differentiable (by simp)) x
  -- second integration by parts
  have step2 : ∫ y, fderiv ℝ (hk d τ) y m * fderiv ℝ g y m' =
      -∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d τ) z m) y m' * g y := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact ((continuous_fderiv_fderiv_hk_apply hτ m m').mul hg.continuous).integrable_of_hasCompactSupport
        hgc.mul_left
    · exact ((continuous_fderiv_hk_apply hτ m).mul cg1).integrable_of_hasCompactSupport
        hgc1.mul_left
    · exact ((continuous_fderiv_hk_apply hτ m).mul hg.continuous).integrable_of_hasCompactSupport
        hgc.mul_left
    · exact fun x _ => differentiable_fderiv_hk_apply hτ m x
    · exact fun x _ => (hg.differentiable (by simp)) x
  rw [step1, step2, neg_neg]

/-! ### The physical representation -/

lemma fderiv_ofReal_apply {G : E d → ℝ} {y : E d} (hG : DifferentiableAt ℝ G y) (m : E d) :
    fderiv ℝ (fun z => (G z : ℂ)) y m = (fderiv ℝ G y m : ℂ) := by
  have h : HasFDerivAt (fun z => (G z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ G y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hG.hasFDerivAt
  rw [h.fderiv]
  simp

lemma dS_dS_toS_apply (g : E d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (m m' y : E d) :
    dS m (dS m' (toS g hg hgc)) y = (fderiv ℝ (fun z => fderiv ℝ g z m') y m : ℂ) := by
  have hg1 : ContDiff ℝ ∞ (fun z => fderiv ℝ g z m') :=
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [dS_apply]
  have e : (⇑(dS m' (toS g hg hgc)) : E d → ℂ) = fun z => (fderiv ℝ g z m' : ℂ) := by
    funext z
    rw [dS_apply, coe_toS]
    exact fderiv_ofReal_apply ((hg.differentiable (by simp)) z) m'
  rw [e]
  exact fderiv_ofReal_apply ((hg1.differentiable (by simp)) y) m

/-- `P_τ(∂ᵢ∂ⱼ g)(0) = ∫ ∂ⱼ∂ᵢG_τ · g`. -/
lemma heat_dS_dS_zero (g : E d → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {τ : ℝ} (hτ : 0 < τ) (m m' : E d) :
    heat τ (⇑(dS m (dS m' (toS g hg hgc)))) 0 =
      ((∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d τ) z m) y m' * g y : ℝ) : ℂ) := by
  unfold heat
  simp_rw [dS_dS_toS_apply g hg hgc, zero_sub, hk_neg]
  rw [← ibp_hk hτ g hg hgc m m', ← integral_complex_ofReal]
  congr 1
  funext y
  push_cast
  ring

/-- **Heat-kernel form of the velocity Hessian at the origin.** -/
theorem hessV_solF_phys (hd : 1 ≤ d) (g : E d → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (t : ℝ) (i j : Fin d) :
    IntegrableOn (fun s : ℝ => s ^ 2 *
      ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d (s ^ 3 / 3)) z (ev i)) y (ev j) * g y) (Ioi 0) ∧
    hessV (solF (fun y => (g y : ℂ))) (t, 0, 0) i j =
      ∫ s in Ioi (0 : ℝ), s ^ 2 *
        ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d (s ^ 3 / 3)) z (ev i)) y (ev j) * g y := by
  set hS := toS g hg hgc
  have hcoe : (fun y => (g y : ℂ)) = ⇑hS := (coe_toS g hg hgc).symm
  have key : ∀ s ∈ Ioi (0 : ℝ), ((s ^ 2 : ℝ) : ℂ) * heat (s ^ 3 / 3) (⇑(dS (ev i) (dS (ev j) hS))) 0 =
      ((s ^ 2 * ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d (s ^ 3 / 3)) z (ev i)) y (ev j) * g y : ℝ) : ℂ) := by
    intro s hs
    have hs' : (0 : ℝ) < s ^ 3 / 3 := by
      have : 0 < s := hs
      positivity
    rw [heat_dS_dS_zero g hg hgc hs', Complex.ofReal_mul]
  have hI := integrableOn_hess_heat hd hS 0 i j
  have hI' := IntegrableOn.congr_fun hI key measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · have h2 := hI'.re
    refine IntegrableOn.congr_fun h2 (fun s _ => ?_) measurableSet_Ioi
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  · rw [hcoe, hessV_solF hd hS, hess0_kinF_heat hd hS, setIntegral_congr_fun measurableSet_Ioi key,
      integral_complex_ofReal, Complex.ofReal_re]

/-- For `i ≠ j`, `∂ⱼ∂ᵢG_τ(y) = yᵢyⱼ/(4τ²) G_τ(y)`. -/
lemma fderiv_fderiv_hk_ev {τ : ℝ} (hτ : 0 < τ) (y : E d) {i j : Fin d} (hij : i ≠ j) :
    fderiv ℝ (fun z => fderiv ℝ (hk d τ) z (ev i)) y (ev j) =
      y i * y j / (4 * τ ^ 2) * hk d τ y := by
  rw [fderiv_fderiv_hk_apply hτ, inner_ev, inner_ev]
  have : ⟪(ev j : E d), ev i⟫ = 0 := by
    rw [inner_ev]; simp [ev, Ne.symm hij]
  rw [this]
  ring

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Phys

-- ============================================================================
-- KineticCounterexamples/Endpoint/Riesz.lean
-- ============================================================================

section File_Endpoint_Riesz

/-!
# The Riesz-kernel lower bound

* `kerK d s y = s² G_{s³/3}(y) / (4 (s³/3)²)` and `∫₀^∞ kerK d s y ds = c_K |y|^{-(d+2)}`
  (`kerK_integral`), with `c_K > 0` explicit (it equals `Γ(d/2+1)/π^{d/2}`, the constant `c_d`
  of (4.5));
* Tonelli: if `P ≥ 0`, `∫₀^∞ ∫ kerK(s,y) P(y) dy ds = ∫ c_K |y|^{-(d+2)} P(y) dy`
  (`ofReal_integral_kerK`);
* dyadic boxes `[a,2a)² × [0,a/√d)^{d-2}` on which `∫ |y|^{-(d+2)} y₁y₂ dy ≥ c` uniformly in `a`.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ENNReal

namespace KS

variable {d : ℕ}

/-- The kernel `s² G_{s³/3}(y) / (4 (s³/3)²)`. -/
def kerK (d : ℕ) (s : ℝ) (y : E d) : ℝ := s ^ 2 * (hk d (s ^ 3 / 3) y / (4 * (s ^ 3 / 3) ^ 2))

/-- The constant `c_K` (equal to `Γ(d/2+1)/π^{d/2}`). -/
def cK (d : ℕ) : ℝ :=
  3 / 4 * (4 * π / 3) ^ (-(d : ℝ) / 2) * (3 / 4) ^ (-((d : ℝ) / 2 + 1)) * Real.Gamma ((d : ℝ) / 2 + 1)

lemma cK_pos : 0 < cK d := by
  unfold cK
  have : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma kerK_nonneg {s : ℝ} (hs : 0 ≤ s) (y : E d) : 0 ≤ kerK d s y := by
  unfold kerK
  have := hk_nonneg (d := d) (τ := s ^ 3 / 3) (by positivity) y
  positivity

lemma measurable_kerK : Measurable (fun q : ℝ × E d => kerK d q.1 q.2) := by
  unfold kerK
  have : Measurable (fun q : ℝ × E d => hk d (q.1 ^ 3 / 3) q.2) :=
    measurable_hk_uncurry.comp ((measurable_fst.pow_const 3).div_const 3 |>.prodMk measurable_snd)
  fun_prop

/-- The substitution `s = x^{-1/3}`. -/
lemma kerK_subst (y : E d) {x : ℝ} (hx : 0 < x) :
    (|(-1 / 3 : ℝ)| * x ^ ((-1 / 3 : ℝ) - 1)) • kerK d (x ^ (-1 / 3 : ℝ)) y =
      3 / 4 * (4 * π / 3) ^ (-(d : ℝ) / 2) *
        (x ^ ((d : ℝ) / 2) * Real.exp (-(3 * ‖y‖ ^ 2 / 4) * x ^ (1 : ℝ))) := by
  set u := x ^ (-1 / 3 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx _
  have hu3 : u ^ 3 = x⁻¹ := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  have hu2 : u ^ 2 = x ^ (-2 / 3 : ℝ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hx43 : x ^ ((-1 / 3 : ℝ) - 1) * x ^ (-2 / 3 : ℝ) = (x ^ 2)⁻¹ := by
    rw [← Real.rpow_add hx, ← Real.rpow_natCast, ← Real.rpow_neg hx.le]
    norm_num
  have hpow : (4 * π * (x⁻¹ / 3)) ^ (-(d : ℝ) / 2) = (4 * π / 3) ^ (-(d : ℝ) / 2) * x ^ ((d : ℝ) / 2) := by
    rw [show 4 * π * (x⁻¹ / 3) = (4 * π / 3) * x⁻¹ by ring,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
    ring_nf
  unfold kerK hk
  rw [hu3, hu2, hpow, abs_of_neg (by norm_num : (-1 / 3 : ℝ) < 0), Real.rpow_one, smul_eq_mul]
  have hexp : Real.exp (-‖y‖ ^ 2 / (4 * (x⁻¹ / 3))) = Real.exp (-(3 * ‖y‖ ^ 2 / 4) * x) := by
    congr 1; field_simp
  rw [hexp]
  have hx2 : x ^ 2 ≠ 0 := by positivity
  calc -(-1 / 3) * x ^ ((-1 / 3 : ℝ) - 1) * (x ^ (-2 / 3 : ℝ) * ((4 * π / 3) ^ (-(d : ℝ) / 2) *
        x ^ ((d : ℝ) / 2) * Real.exp (-(3 * ‖y‖ ^ 2 / 4) * x) / (4 * (x⁻¹ / 3) ^ 2)))
      = (1 / 3) * (x ^ ((-1 / 3 : ℝ) - 1) * x ^ (-2 / 3 : ℝ)) * ((4 * π / 3) ^ (-(d : ℝ) / 2) *
        x ^ ((d : ℝ) / 2) * Real.exp (-(3 * ‖y‖ ^ 2 / 4) * x)) / (4 * (x⁻¹ / 3) ^ 2) := by ring
    _ = _ := by
        rw [hx43]
        field_simp

/-- **The kernel**: `∫₀^∞ s² G_{s³/3}(y)/(4(s³/3)²) ds = c_K |y|^{-(d+2)}`. -/
theorem kerK_integral {y : E d} (hy : y ≠ 0) :
    IntegrableOn (fun s => kerK d s y) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), kerK d s y = cK d * (‖y‖ ^ (d + 2))⁻¹ := by
  have hp : (-1 / 3 : ℝ) ≠ 0 := by norm_num
  have hb : 0 < 3 * ‖y‖ ^ 2 / 4 := by
    have : 0 < ‖y‖ := norm_pos_iff.mpr hy
    positivity
  set Q : ℝ → ℝ := fun x => 3 / 4 * (4 * π / 3) ^ (-(d : ℝ) / 2) *
    (x ^ ((d : ℝ) / 2) * Real.exp (-(3 * ‖y‖ ^ 2 / 4) * x ^ (1 : ℝ))) with hQ
  have hq : (-1 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hQi : IntegrableOn Q (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow hq one_pos hb).const_mul _
  have hEq : EqOn Q (fun x => (|(-1 / 3 : ℝ)| * x ^ ((-1 / 3 : ℝ) - 1)) •
      kerK d (x ^ (-1 / 3 : ℝ)) y) (Ioi 0) := fun x hx => (kerK_subst y hx).symm
  constructor
  · rw [← integrableOn_Ioi_comp_rpow_iff (fun s => kerK d s y) hp]
    exact hQi.congr_fun hEq measurableSet_Ioi
  · rw [← integral_comp_rpow_Ioi (fun s => kerK d s y) hp, ← setIntegral_congr_fun measurableSet_Ioi hEq]
    simp only [hQ]
    rw [integral_const_mul, _root_.integral_rpow_mul_exp_neg_mul_rpow one_pos hq hb]
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have e1 : (3 * ‖y‖ ^ 2 / 4) ^ (-((d : ℝ) / 2 + 1) / 1) =
        (3 / 4) ^ (-((d : ℝ) / 2 + 1)) * (‖y‖ ^ (d + 2))⁻¹ := by
      rw [div_one, show 3 * ‖y‖ ^ 2 / 4 = 3 / 4 * ‖y‖ ^ 2 by ring,
        Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast ‖y‖ 2, ← Real.rpow_mul hy0.le,
        show ((2 : ℕ) : ℝ) * -((d : ℝ) / 2 + 1) = -(((d + 2 : ℕ)) : ℝ) by push_cast; ring,
        Real.rpow_neg hy0.le, Real.rpow_natCast]
    rw [e1]
    simp only [div_one]
    unfold cK
    ring

/-! ### Tonelli -/

/-- If `P ≥ 0`, then `∫₀^∞ ∫ kerK(s,y) P(y) dy ds = ∫ P(y) c_K |y|^{-(d+2)} dy` (in `ℝ≥0∞`). -/
theorem ofReal_integral_kerK (hd : 1 ≤ d) (P : E d → ℝ) (hPm : Measurable P)
    (hP0 : ∀ y, 0 ≤ P y) (hPi : ∀ s ∈ Ioi (0 : ℝ), Integrable (fun y => kerK d s y * P y))
    (hint : IntegrableOn (fun s => ∫ y, kerK d s y * P y) (Ioi 0)) :
    ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ∫ y, kerK d s y * P y) =
      ∫⁻ y, ENNReal.ofReal (P y * (cK d * (‖y‖ ^ (d + 2))⁻¹)) := by
  have hnn : ∀ s ∈ Ioi (0 : ℝ), ∀ y, 0 ≤ kerK d s y * P y :=
    fun s hs y => mul_nonneg (kerK_nonneg (le_of_lt hs) y) (hP0 y)
  rw [ofReal_integral_eq_lintegral_ofReal hint]
  swap
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun s hs => integral_nonneg (hnn s hs)
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun s hs =>
    ofReal_integral_eq_lintegral_ofReal (hPi s hs) (Eventually.of_forall (hnn s hs)))]
  have hmeas : AEMeasurable (Function.uncurry fun (s : ℝ) (y : E d) =>
      ENNReal.ofReal (kerK d s y * P y)) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    apply Measurable.aemeasurable
    exact (measurable_kerK.mul (hPm.comp measurable_snd)).ennreal_ofReal
  rw [lintegral_lintegral_swap hmeas]
  apply lintegral_congr_ae
  filter_upwards [ae_ne_zero_E hd] with y hy
  have hk := kerK_integral (d := d) hy
  rw [show (fun s => ENNReal.ofReal (kerK d s y * P y)) =
      fun s => ENNReal.ofReal (P y) * ENNReal.ofReal (kerK d s y) by
    funext s
    rw [← ENNReal.ofReal_mul (hP0 y), mul_comm]]
  have hmk : Measurable (fun s : ℝ => ENNReal.ofReal (kerK d s y)) := by
    have : Measurable (fun s : ℝ => kerK d s y) :=
      measurable_kerK.comp (measurable_id.prodMk measurable_const)
    exact this.ennreal_ofReal
  rw [lintegral_const_mul _ hmk]
  rw [← ofReal_integral_eq_lintegral_ofReal hk.1]
  · rw [hk.2, ← ENNReal.ofReal_mul (hP0 y)]
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun s hs => kerK_nonneg (le_of_lt hs) y

/-! ### Dyadic boxes -/

/-- The box `{a ≤ y_{i₀} < 2a, a ≤ y_{i₁} < 2a, 0 ≤ y_j < a/√d (j ≠ i₀,i₁)}`. -/
def dbox (i0 i1 : Fin d) (a : ℝ) : Set (E d) :=
  {y | a ≤ y i0 ∧ y i0 < 2 * a ∧ a ≤ y i1 ∧ y i1 < 2 * a ∧
    ∀ j, j ≠ i0 → j ≠ i1 → 0 ≤ y j ∧ y j < a / √d}

/-- Lower endpoints and side lengths of the box. -/
def dlo (i0 i1 : Fin d) (a : ℝ) (j : Fin d) : ℝ := if j = i0 ∨ j = i1 then a else 0
def dlen (i0 i1 : Fin d) (a : ℝ) (j : Fin d) : ℝ := if j = i0 ∨ j = i1 then a else a / √d

lemma dbox_eq (i0 i1 : Fin d) (hij : i0 ≠ i1) (a : ℝ) :
    dbox i0 i1 a = (WithLp.ofLp) ⁻¹' (Set.pi univ fun j =>
      Ico (dlo i0 i1 a j) (dlo i0 i1 a j + dlen i0 i1 a j)) := by
  ext y
  simp only [dbox, dlo, dlen, mem_setOf_eq, mem_preimage, Set.mem_pi, mem_univ, forall_true_left,
    mem_Ico]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ j
    by_cases hj0 : j = i0
    · subst hj0; simp only [true_or, ite_true]; exact ⟨h1, by linarith⟩
    by_cases hj1 : j = i1
    · subst hj1; simp only [or_true, ite_true]; exact ⟨h3, by linarith⟩
    simp only [hj0, hj1, or_self, ite_false, zero_add]
    exact h5 j hj0 hj1
  · intro h
    have e0 := h i0
    have e1 := h i1
    simp only [true_or, or_true, ite_true] at e0 e1
    refine ⟨e0.1, by linarith [e0.2], e1.1, by linarith [e1.2], fun j hj0 hj1 => ?_⟩
    have := h j
    simp only [hj0, hj1, or_self, ite_false, zero_add] at this
    exact this

lemma measurableSet_dbox (i0 i1 : Fin d) (hij : i0 ≠ i1) (a : ℝ) :
    MeasurableSet (dbox i0 i1 a) := by
  rw [dbox_eq i0 i1 hij]
  exact (MeasurableSet.univ_pi fun j => measurableSet_Ico).preimage (by fun_prop)

lemma vol_dbox_ge (hd : 1 ≤ d) (i0 i1 : Fin d) (hij : i0 ≠ i1) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal ((a / √d) ^ d) ≤ volume (dbox i0 i1 a) := by
  rw [dbox_eq i0 i1 hij, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    ((MeasurableSet.univ_pi fun j => measurableSet_Ico).nullMeasurableSet), volume_pi_pi]
  have hsd : 1 ≤ √(d : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  have hle : a / √d ≤ a := div_le_self ha.le hsd
  calc ENNReal.ofReal ((a / √d) ^ d) = ∏ _j : Fin d, ENNReal.ofReal (a / √d) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ENNReal.ofReal_pow (by positivity)]
    _ ≤ ∏ j : Fin d, volume (Ico (dlo i0 i1 a j) (dlo i0 i1 a j + dlen i0 i1 a j)) := by
        apply Finset.prod_le_prod' (fun j _ => ?_)
        rw [Real.volume_Ico, add_sub_cancel_left]
        apply ENNReal.ofReal_le_ofReal
        unfold dlen
        split_ifs
        · exact hle
        · exact le_rfl

lemma norm_sq_le_of_mem_dbox (i0 i1 : Fin d) (hij : i0 ≠ i1) {a : ℝ} (ha : 0 < a) {y : E d}
    (hy : y ∈ dbox i0 i1 a) : ‖y‖ ≤ 3 * a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  have hd : (0 : ℝ) < d := by
    have : 0 < d := Fin.pos i0
    exact_mod_cast this
  have hterm : ∀ j, y j ^ 2 ≤ (if j = i0 then 4 * a ^ 2 else 0) + (if j = i1 then 4 * a ^ 2 else 0) +
      a ^ 2 / d := by
    intro j
    by_cases hj0 : j = i0
    · subst hj0
      simp only [ite_true, if_neg hij]
      have : y j ^ 2 ≤ 4 * a ^ 2 := by nlinarith
      have : 0 ≤ a ^ 2 / d := by positivity
      linarith
    by_cases hj1 : j = i1
    · subst hj1
      simp only [ite_true, if_neg hj0]
      have : y j ^ 2 ≤ 4 * a ^ 2 := by nlinarith
      have : 0 ≤ a ^ 2 / d := by positivity
      linarith
    simp only [if_neg hj0, if_neg hj1, zero_add]
    obtain ⟨hl, hr⟩ := h5 j hj0 hj1
    have hs : (a / √d) ^ 2 = a ^ 2 / d := by
      rw [div_pow, Real.sq_sqrt hd.le]
    have : y j ^ 2 ≤ (a / √d) ^ 2 := by
      apply pow_le_pow_left₀ hl hr.le
    linarith
  have hsum : ‖y‖ ^ 2 ≤ 9 * a ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ j, y j ^ 2 ≤ ∑ j : Fin d, ((if j = i0 then 4 * a ^ 2 else 0) +
          (if j = i1 then 4 * a ^ 2 else 0) + a ^ 2 / d) := Finset.sum_le_sum fun j _ => hterm j
      _ = 4 * a ^ 2 + 4 * a ^ 2 + d * (a ^ 2 / d) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
      _ = 9 * a ^ 2 := by field_simp; ring
  nlinarith [norm_nonneg y]

/-- The uniform lower bound on a dyadic box. -/
def cbox (d : ℕ) : ℝ := cK d / (3 ^ (d + 2) * √d ^ d)

lemma cbox_pos (hd : 1 ≤ d) : 0 < cbox d := by
  unfold cbox
  have := cK_pos (d := d)
  have : 0 < √(d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  positivity

lemma lintegral_dbox_ge (hd : 1 ≤ d) (i0 i1 : Fin d) (hij : i0 ≠ i1) {a : ℝ} (ha : 0 < a)
    (P : E d → ℝ) (hP : ∀ y ∈ dbox i0 i1 a, y i0 * y i1 ≤ P y) :
    ENNReal.ofReal (cbox d) ≤
      ∫⁻ y in dbox i0 i1 a, ENNReal.ofReal (P y * (cK d * (‖y‖ ^ (d + 2))⁻¹)) := by
  set c := a ^ 2 * (cK d * ((3 * a) ^ (d + 2))⁻¹) with hc
  have hlow : ∀ y ∈ dbox i0 i1 a, ENNReal.ofReal c ≤
      ENNReal.ofReal (P y * (cK d * (‖y‖ ^ (d + 2))⁻¹)) := by
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    have hy' := hy
    obtain ⟨h1, _, h3, _, _⟩ := hy'
    have hn := norm_sq_le_of_mem_dbox i0 i1 hij ha hy
    have hn0 : 0 < ‖y‖ := by
      have : 0 < y i0 := lt_of_lt_of_le ha h1
      have : |y i0| ≤ ‖y‖ := by
        have := PiLp.norm_apply_le y i0
        rwa [Real.norm_eq_abs] at this
      linarith [abs_of_pos ‹0 < y i0›]
    have hP' := hP y hy
    have ha2 : a ^ 2 ≤ y i0 * y i1 := by nlinarith
    have hinv : ((3 * a) ^ (d + 2))⁻¹ ≤ (‖y‖ ^ (d + 2))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hn0.le hn _
    have hK := cK_pos (d := d)
    calc c = a ^ 2 * (cK d * ((3 * a) ^ (d + 2))⁻¹) := rfl
      _ ≤ P y * (cK d * (‖y‖ ^ (d + 2))⁻¹) := by
        apply mul_le_mul (ha2.trans hP') _ (by positivity) (by linarith [sq_nonneg a, ha2, hP'])
        exact mul_le_mul_of_nonneg_left hinv hK.le
  have hc0 : 0 ≤ c := by
    have := cK_pos (d := d)
    rw [hc]; positivity
  have e : c * (a / √d) ^ d = cbox d := by
    rw [hc, cbox, div_pow, mul_pow]
    have : 0 < √(d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    field_simp
    ring
  calc ENNReal.ofReal (cbox d) = ENNReal.ofReal c * ENNReal.ofReal ((a / √d) ^ d) := by
        rw [← ENNReal.ofReal_mul hc0, e]
    _ ≤ ENNReal.ofReal c * volume (dbox i0 i1 a) := by
        gcongr; exact vol_dbox_ge hd i0 i1 hij ha
    _ = ∫⁻ _y in dbox i0 i1 a, ENNReal.ofReal c := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono' (measurableSet_dbox i0 i1 hij a) hlow

lemma dbox_disjoint (i0 i1 : Fin d) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (dbox i0 i1 (1 / 2 ^ (k + 1))) (dbox i0 i1 (1 / 2 ^ (l + 1))) := by
  rw [Set.disjoint_left]
  rintro y ⟨h1, h2, -⟩ ⟨h3, h4, -⟩
  rcases lt_or_gt_of_ne hkl with h | h
  · -- `2^{-(k+1)} ≤ y < 2^{-l}` and `2^{-(l+1)} ≤ y < 2^{-l}` with `k < l`
    have : (1 : ℝ) / 2 ^ (l + 1) * 2 ≤ 1 / 2 ^ (k + 1) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (2 : ℝ) ^ (k + 1) * 2 ≤ 2 ^ (l + 1) := by
        rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  · have : (1 : ℝ) / 2 ^ (k + 1) * 2 ≤ 1 / 2 ^ (l + 1) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (2 : ℝ) ^ (l + 1) * 2 ≤ 2 ^ (k + 1) := by
        rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith

/-- Summing the dyadic boxes: `#S · c ≤ ∫⁻ P(y) c_K|y|^{-(d+2)}` if `P ≥ y_{i₀}y_{i₁}` on each box. -/
lemma lintegral_ge_card (hd : 1 ≤ d) (i0 i1 : Fin d) (hij : i0 ≠ i1) (S : Finset ℕ)
    (P : E d → ℝ) (hP : ∀ k ∈ S, ∀ y ∈ dbox i0 i1 (1 / 2 ^ (k + 1)), y i0 * y i1 ≤ P y) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal (cbox d) ≤
      ∫⁻ y, ENNReal.ofReal (P y * (cK d * (‖y‖ ^ (d + 2))⁻¹)) := by
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal (cbox d) = ∑ _k ∈ S, ENNReal.ofReal (cbox d) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ S, ∫⁻ y in dbox i0 i1 (1 / 2 ^ (k + 1)),
          ENNReal.ofReal (P y * (cK d * (‖y‖ ^ (d + 2))⁻¹)) :=
        Finset.sum_le_sum fun k hk => lintegral_dbox_ge hd i0 i1 hij (by positivity) P (hP k hk)
    _ = ∫⁻ y in ⋃ k ∈ S, dbox i0 i1 (1 / 2 ^ (k + 1)),
          ENNReal.ofReal (P y * (cK d * (‖y‖ ^ (d + 2))⁻¹)) := by
        rw [lintegral_biUnion_finset]
        · intro k _ l _ hkl
          exact dbox_disjoint i0 i1 hkl
        · intro k _
          exact measurableSet_dbox i0 i1 hij _
    _ ≤ _ := setLIntegral_le_lintegral _ _

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Riesz

-- ============================================================================
-- KineticCounterexamples/Endpoint/Thm41.lean
-- ============================================================================

section File_Endpoint_Thm41

/-!
# Theorem 4.1 of Dong–Wang (bounded forcing, logarithmic blow-up of `D_v² f`)

For `d ≥ 2` there are `C, c > 0` and, for every `0 < ε < 1/10`, a forcing `g_ε ∈ C_c^∞(ℝᵈ)`
independent of `v` with `|g_ε| ≤ 1`, and a smooth stationary solution `f_ε` of
`(∂_t + v·∇_x) f = Δ_v f + g_ε` on `ℝ × ℝᵈ × ℝᵈ` with `|f_ε| ≤ C`, but
`∂_{v₁v₂} f_ε(t,0,0) ≥ c log(1/ε)`; in particular `‖D_v² f_ε‖_{L^∞(B_{1/4}×B_{1/4})} ≥ c log(1/ε)`.

The construction is the one of the paper: `g_ε(x) = χ(x) σ(x₁/ε) σ(x₂/ε)` and
`f_ε = ∫₀^∞ P_{s³/3} g_ε(x - s v) ds`.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ENNReal ContDiff

namespace KS

variable {d : ℕ}

/-! ### The profile `σ` -/

/-- An odd smooth function with `|σ| ≤ 1`, `sσ(s) ≥ 0` and `σ(s) = sgn s` for `|s| ≥ 1`. -/
def sig (t : ℝ) : ℝ := Real.smoothTransition t - Real.smoothTransition (-t)

lemma contDiff_sig : ContDiff ℝ ∞ sig := by
  unfold sig
  exact (Real.smoothTransition.contDiff (n := ⊤)).sub
    ((Real.smoothTransition.contDiff (n := ⊤)).comp contDiff_neg)

lemma sig_of_one_le {t : ℝ} (ht : 1 ≤ t) : sig t = 1 := by
  unfold sig
  rw [Real.smoothTransition.one_of_one_le ht, Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

lemma sig_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ sig t := by
  unfold sig
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : -t ≤ 0), sub_zero]
  exact Real.smoothTransition.nonneg t

lemma sig_nonpos {t : ℝ} (ht : t ≤ 0) : sig t ≤ 0 := by
  unfold sig
  rw [Real.smoothTransition.zero_of_nonpos ht, zero_sub, neg_nonpos]
  exact Real.smoothTransition.nonneg _

lemma abs_sig_le (t : ℝ) : |sig t| ≤ 1 := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg (sig_nonneg ht)]
    unfold sig
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : -t ≤ 0), sub_zero]
    exact Real.smoothTransition.le_one t
  · rw [abs_of_nonpos (sig_nonpos ht)]
    unfold sig
    rw [Real.smoothTransition.zero_of_nonpos ht, zero_sub, neg_neg]
    exact Real.smoothTransition.le_one _

lemma mul_sig_nonneg (t : ℝ) : 0 ≤ t * sig t := by
  rcases le_total 0 t with ht | ht
  · exact mul_nonneg ht (sig_nonneg ht)
  · exact mul_nonneg_of_nonpos_of_nonpos ht (sig_nonpos ht)

/-! ### The forcing `g_ε` -/

/-- The cutoff `χ ∈ C_c^∞(B₁)`, `0 ≤ χ ≤ 1`, `χ = 1` on `B_{1/2}`. -/
def chiB (d : ℕ) : ContDiffBump (0 : E d) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

/-- The forcing (4.2): `g_ε(x) = χ(x) σ(x₁/ε) σ(x₂/ε)`. -/
def gEps (i0 i1 : Fin d) (ε : ℝ) (x : E d) : ℝ := chiB d x * sig (x i0 / ε) * sig (x i1 / ε)

lemma contDiff_gEps (i0 i1 : Fin d) (ε : ℝ) : ContDiff ℝ ∞ (gEps i0 i1 ε) := by
  unfold gEps
  have hc : ContDiff ℝ ∞ (fun x : E d => chiB d x) := (chiB d).contDiff
  have h0 : ContDiff ℝ ∞ (fun x : E d => x i0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i0).contDiff
  have h1 : ContDiff ℝ ∞ (fun x : E d => x i1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i1).contDiff
  exact (hc.mul (contDiff_sig.comp (h0.div_const ε))).mul (contDiff_sig.comp (h1.div_const ε))

lemma hasCompactSupport_gEps (i0 i1 : Fin d) (ε : ℝ) : HasCompactSupport (gEps i0 i1 ε) := by
  unfold gEps
  exact ((chiB d).hasCompactSupport.mul_right).mul_right

lemma abs_gEps_le (i0 i1 : Fin d) (ε : ℝ) (x : E d) : |gEps i0 i1 ε x| ≤ 1 := by
  unfold gEps
  rw [abs_mul, abs_mul, abs_of_nonneg (chiB d).nonneg]
  have h1 := (chiB d).le_one (x := x)
  have h2 := abs_sig_le (x i0 / ε)
  have h3 := abs_sig_le (x i1 / ε)
  have h4 : 0 ≤ chiB d x := (chiB d).nonneg
  calc chiB d x * |sig (x i0 / ε)| * |sig (x i1 / ε)| ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

lemma gEps_eq_zero (i0 i1 : Fin d) (ε : ℝ) {x : E d} (hx : 1 ≤ ‖x‖) : gEps i0 i1 ε x = 0 := by
  unfold gEps
  rw [(chiB d).zero_of_le_dist]
  · ring
  · simp only [chiB, dist_zero_right]; linarith

lemma P_gEps_nonneg (i0 i1 : Fin d) {ε : ℝ} (hε : 0 < ε) (y : E d) :
    0 ≤ y i0 * y i1 * gEps i0 i1 ε y := by
  unfold gEps
  have h0 : 0 ≤ y i0 * sig (y i0 / ε) := by
    have := mul_sig_nonneg (y i0 / ε)
    have e : y i0 * sig (y i0 / ε) = ε * (y i0 / ε * sig (y i0 / ε)) := by field_simp
    rw [e]; exact mul_nonneg hε.le this
  have h1 : 0 ≤ y i1 * sig (y i1 / ε) := by
    have := mul_sig_nonneg (y i1 / ε)
    have e : y i1 * sig (y i1 / ε) = ε * (y i1 / ε * sig (y i1 / ε)) := by field_simp
    rw [e]; exact mul_nonneg hε.le this
  have hc : 0 ≤ chiB d y := (chiB d).nonneg
  have : y i0 * y i1 * (chiB d y * sig (y i0 / ε) * sig (y i1 / ε)) =
      chiB d y * (y i0 * sig (y i0 / ε)) * (y i1 * sig (y i1 / ε)) := by ring
  rw [this]
  positivity

lemma P_gEps_on_box (i0 i1 : Fin d) (hij : i0 ≠ i1) {ε a : ℝ} (hε : 0 < ε) (haε : ε ≤ a)
    (ha : a ≤ 1 / 8) {y : E d} (hy : y ∈ dbox i0 i1 a) :
    y i0 * y i1 ≤ y i0 * y i1 * gEps i0 i1 ε y := by
  have ha0 : 0 < a := lt_of_lt_of_le hε haε
  have hn := norm_sq_le_of_mem_dbox i0 i1 hij ha0 hy
  obtain ⟨h1, -, h3, -, -⟩ := hy
  have hchi : chiB d y = 1 := by
    apply (chiB d).one_of_mem_closedBall
    simp only [chiB, Metric.mem_closedBall, dist_zero_right]
    linarith
  have hs0 : sig (y i0 / ε) = 1 := sig_of_one_le (by rw [le_div_iff₀ hε]; linarith)
  have hs1 : sig (y i1 / ε) = 1 := sig_of_one_le (by rw [le_div_iff₀ hε]; linarith)
  unfold gEps
  rw [hchi, hs0, hs1]
  simp

/-! ### The logarithmic lower bound -/

/-- The number of dyadic scales between `ε` and `1/8`. -/
def mEps (ε : ℝ) : ℕ := Nat.log 2 ⌊1 / ε⌋₊

lemma mEps_spec {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) :
    3 ≤ mEps ε ∧ (2 : ℝ) ^ mEps ε ≤ 1 / ε ∧ Real.log (1 / ε) < (mEps ε + 1) * Real.log 2 := by
  have h10 : (10 : ℝ) < 1 / ε := by
    rw [lt_div_iff₀ hε]; linarith
  have hfl : 10 ≤ ⌊1 / ε⌋₊ := by
    apply Nat.le_floor; push_cast; linarith
  have hne : ⌊1 / ε⌋₊ ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold mEps
    apply Nat.le_log_of_pow_le (by norm_num)
    omega
  · calc (2 : ℝ) ^ mEps ε = ((2 ^ mEps ε : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊1 / ε⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hne
      _ ≤ 1 / ε := Nat.floor_le (by positivity)
  · have h1 : 1 / ε < (⌊1 / ε⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ⌊1 / ε⌋₊ < 2 ^ (mEps ε).succ := Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : (⌊1 / ε⌋₊ : ℝ) + 1 ≤ 2 ^ (mEps ε + 1) := by
      have : ⌊1 / ε⌋₊ + 1 ≤ 2 ^ (mEps ε + 1) := h2
      exact_mod_cast this
    have h4 : 1 / ε < (2 : ℝ) ^ (mEps ε + 1) := lt_of_lt_of_le h1 h3
    have h5 := Real.log_lt_log (by positivity) h4
    rw [Real.log_pow] at h5
    push_cast at h5
    linarith

/-- The Hessian lower bound `∂_{v₁v₂} f_ε(t,0,0) ≥ c log(1/ε)`. -/
theorem hess_gEps_ge (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) (t : ℝ) :
    cbox d / (4 * Real.log 2) * Real.log (1 / ε) ≤
      hessV (solF (fun y => (gEps (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ ε y : ℂ))) (t, 0, 0)
        ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hd1 : 1 ≤ d := by omega
  set g := gEps i0 i1 ε
  have hg := contDiff_gEps i0 i1 ε
  have hgc := hasCompactSupport_gEps i0 i1 ε
  obtain ⟨hI, hEq⟩ := hessV_solF_phys hd1 g hg hgc t i0 i1
  set P : E d → ℝ := fun y => y i0 * y i1 * g y with hP
  -- rewrite the integrand with the kernel
  have e : ∀ s ∈ Ioi (0 : ℝ), s ^ 2 *
      ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d (s ^ 3 / 3)) z (ev i0)) y (ev i1) * g y =
      ∫ y, kerK d s y * P y := by
    intro s hs
    have hτ : (0 : ℝ) < s ^ 3 / 3 := by
      have : 0 < s := hs
      positivity
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [fderiv_fderiv_hk_ev hτ y hij]
    simp only [kerK, hP]
    ring
  rw [hEq, setIntegral_congr_fun measurableSet_Ioi e]
  have hI' : IntegrableOn (fun s => ∫ y, kerK d s y * P y) (Ioi 0) :=
    hI.congr_fun e measurableSet_Ioi
  have hPc : Continuous P := by
    have : Continuous g := hg.continuous
    simp only [hP]
    fun_prop
  have hPi : ∀ s ∈ Ioi (0 : ℝ), Integrable (fun y => kerK d s y * P y) := by
    intro s hs
    have hks : Continuous (fun y => kerK d s y) := by
      unfold kerK
      exact continuous_const.mul ((continuous_hk _).div_const _)
    exact (hks.mul hPc).integrable_of_hasCompactSupport (hgc.mul_left.mul_left)
  have key := ofReal_integral_kerK hd1 P hPc.measurable (P_gEps_nonneg i0 i1 hε) hPi hI'
  -- dyadic boxes `a_k = 2^{-(k+1)}`, `2 ≤ k ≤ m - 1`
  obtain ⟨hm3, hm2, hmlog⟩ := mEps_spec hε hε'
  set m := mEps ε
  set S : Finset ℕ := Finset.Icc 2 (m - 1)
  have hbox : ∀ k ∈ S, ∀ y ∈ dbox i0 i1 (1 / 2 ^ (k + 1)), y i0 * y i1 ≤ P y := by
    intro k hk y hy
    obtain ⟨hk2, hkm⟩ := Finset.mem_Icc.mp hk
    apply P_gEps_on_box i0 i1 hij hε _ _ hy
    · -- `ε ≤ 2^{-(k+1)}`
      have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [le_div_iff₀ (by positivity)]
      calc ε * 2 ^ (k + 1) ≤ ε * 2 ^ m := by gcongr
        _ ≤ ε * (1 / ε) := by gcongr
        _ = 1 := by field_simp
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ^ 3 ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  have hcard := lintegral_ge_card hd1 i0 i1 hij S P hbox
  rw [← key] at hcard
  have hSc : (S.card : ℝ) = (m : ℝ) - 2 := by
    simp only [S, Nat.card_Icc]
    have : m - 1 + 1 - 2 = m - 2 := by omega
    rw [this, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hcb := cbox_pos hd1
  have hlhs : (S.card : ℝ≥0∞) * ENNReal.ofReal (cbox d) = ENNReal.ofReal (S.card * cbox d) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [hlhs] at hcard
  have hpos : 0 < (S.card : ℝ) * cbox d := by
    rw [hSc]
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have : (0 : ℝ) < m - 2 := by linarith
    positivity
  have hle : (S.card : ℝ) * cbox d ≤ ∫ s in Ioi (0 : ℝ), ∫ y, kerK d s y * P y := by
    rcases (ENNReal.ofReal_le_ofReal_iff'.mp hcard) with h | h
    · exact h
    · linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc cbox d / (4 * Real.log 2) * Real.log (1 / ε)
      ≤ cbox d / (4 * Real.log 2) * ((m + 1) * Real.log 2) := by
        gcongr
    _ = (m + 1) / 4 * cbox d := by field_simp
    _ ≤ (S.card : ℝ) * cbox d := by
        rw [hSc]
        have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
        gcongr
        linarith
    _ ≤ _ := hle

/-! ### Essential suprema of continuous functions -/

lemma le_essSup_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {U : Set X} (hU : IsOpen U)
    (hpos : ∀ V, IsOpen V → (V ∩ U).Nonempty → 0 < μ (V ∩ U)) {F : X → ℝ≥0∞}
    (hF : Continuous F) {x0 : X} (hx0 : x0 ∈ U) : F x0 ≤ essSup F (μ.restrict U) := by
  by_contra h
  push Not at h
  obtain ⟨b, hb1, hb2⟩ := exists_between h
  set V := {x | b < F x}
  have hV : IsOpen V := hF.isOpen_preimage _ isOpen_Ioi
  have hae := ae_lt_of_essSup_lt hb1
  have h0 : (μ.restrict U) V = 0 := by
    apply measure_mono_null (t := {x | ¬ F x < b})
    · intro x hx; simp only [mem_setOf_eq, not_lt]; exact le_of_lt hx
    · exact hae
  rw [Measure.restrict_apply hV.measurableSet] at h0
  have := hpos V hV ⟨x0, hb2, hx0⟩
  rw [h0] at this
  exact lt_irrefl _ this

lemma continuous_frob {X : Type*} [TopologicalSpace X] {H : X → Matrix (Fin d) (Fin d) ℝ}
    (hH : ∀ i j, Continuous (fun q => H q i j)) : Continuous (fun q => frob (H q)) := by
  unfold frob
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => (hH i j).pow 2)

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1** (Dong–Wang). For `d ≥ 2` there are `C, c > 0` such that for every
`0 < ε < 1/10` there are `g_ε ∈ C_c^∞(ℝᵈ)` with `|g_ε| ≤ 1` and a smooth stationary solution `f_ε`
of `(∂_t + v·∇_x) f_ε = Δ_v f_ε + g_ε` in `ℝ × ℝᵈ × ℝᵈ` with `|f_ε| ≤ C`, but
`∂_{v₁v₂} f_ε(t,0,0) ≥ c log(1/ε)` and `‖D_v² f_ε‖_{L^∞(B_{1/4} × B_{1/4})} ≥ c log(1/ε)`. -/
theorem thm_4_1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∃ (g : E d → ℝ) (f : Pt d → ℝ),
        ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ x, |g x| ≤ 1) ∧
        ContDiff ℝ ∞ f ∧ (∀ t t' x v, f (t, x, v) = f (t', x, v)) ∧
        (∀ p, KFP f (fun _ => 1) (fun _ => 0) (fun p => g p.2.1) p) ∧
        (∀ p, |f p| ≤ C) ∧
        (∀ t, c * Real.log (1 / ε) ≤ hessV f (t, 0, 0) ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
        ENNReal.ofReal (c * Real.log (1 / ε)) ≤
          essSup (fun q : E d × E d => ENNReal.ofReal (frob (hessV f (0, q.1, q.2))))
            (volume.restrict (Metric.ball (0 : E d) (1 / 4) ×ˢ Metric.ball (0 : E d) (1 / 4))) := by
  have hd1 : 1 ≤ d := by omega
  set L := (volume (Metric.ball (0 : E d) 1)).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hKB : 0 ≤ kinBd d 1 L := by
    unfold kinBd
    apply setIntegral_nonneg measurableSet_Ioi
    intro s hs
    have : 0 ≤ s := le_of_lt hs
    exact le_min zero_le_one (mul_nonneg (Real.rpow_nonneg (by positivity) _) hL)
  refine ⟨kinBd d 1 L + 1, cbox d / (4 * Real.log 2), by linarith,
    div_pos (cbox_pos hd1) (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity),
    fun ε hε hε' => ?_⟩
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  set g := gEps i0 i1 ε
  have hg := contDiff_gEps i0 i1 ε
  have hgc := hasCompactSupport_gEps i0 i1 ε
  set hS := toS g hg hgc
  have hcoe : (fun y => (g y : ℂ)) = ⇑hS := (coe_toS g hg hgc).symm
  refine ⟨g, solF (fun y => (g y : ℂ)), hg, hgc, abs_gEps_le i0 i1 ε, ?_, solF_stationary _,
    solF_KFP hd1 g hg hgc, ?_, hess_gEps_ge hd hε hε', ?_⟩
  · rw [hcoe]; exact solF_smooth hd1 hS
  · intro p
    have hint : Integrable (fun y => (g y : ℂ)) := by rw [hcoe]; exact hS.integrable
    have h1 := abs_solF_le hd1 hint (K := 1) (fun y => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_gEps_le i0 i1 ε y) p
    have h2 : ∫ y, ‖(g y : ℂ)‖ ≤ L := integral_norm_le_vol_ball
      (fun y => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_gEps_le i0 i1 ε y)
      (fun y hy => by
        have : g y = 0 := gEps_eq_zero i0 i1 ε hy
        rw [this, Complex.ofReal_zero])
    have h3 := kinBd_mono hd1 zero_le_one (integral_nonneg fun y => norm_nonneg _) h2
    linarith
  · -- the `L^∞` formulation
    have hK := contDiff_kinF hd1 hS
    have hf : solF (fun y => (g y : ℂ)) = liftK (kinF ⇑hS) := by
      rw [hcoe]; exact solF_eq_liftK hd1 hS
    have hcont : Continuous (fun q : E d × E d =>
        ENNReal.ofReal (frob (hessV (solF (fun y => (g y : ℂ))) (0, q.1, q.2)))) := by
      rw [hf]
      exact ENNReal.continuous_ofReal.comp (continuous_frob fun i j => continuous_hessV_liftK hK i j)
    have hU : IsOpen (Metric.ball (0 : E d) (1 / 4) ×ˢ Metric.ball (0 : E d) (1 / 4)) :=
      Metric.isOpen_ball.prod Metric.isOpen_ball
    have h0U : ((0 : E d), (0 : E d)) ∈ Metric.ball (0 : E d) (1 / 4) ×ˢ Metric.ball (0 : E d) (1 / 4) := by
      simp [Metric.mem_ball]
    have hle := le_essSup_of_continuous (μ := (volume : Measure (E d × E d))) hU
      (fun V hV hne => (hV.inter hU).measure_pos _ hne) hcont h0U
    refine le_trans ?_ hle
    apply ENNReal.ofReal_le_ofReal
    have := hess_gEps_ge hd hε hε' 0
    exact this.trans ((le_abs_self _).trans (abs_le_frob _ _ _))

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Thm41

-- ============================================================================
-- KineticCounterexamples/Endpoint/Distrib.lean
-- ============================================================================

section File_Endpoint_Distrib

/-!
# Distributional solutions and `D_v² f ∈ L^∞_loc`

* `IsDistribSol f g`: `f ∈ L¹_loc(ℝ × ℝᵈ × ℝᵈ)` and for every test function `φ ∈ C_c^∞`,
  `∫ f (-∂_t φ - v·∇_x φ - Δ_v φ) = ∫ g φ`, i.e. `(∂_t + v·∇_x) f = Δ_v f + g` in `𝒟'`;
* `HessVLinfLoc f`: the distributional velocity Hessian of `f` is represented by a matrix-valued
  function in `L^∞_loc`;
* classical solutions are distributional solutions (`isDistribSol_of_KFP`).
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ENNReal ContDiff

namespace KS

variable {d : ℕ}

instance instIsAddHaarVolumeEE : (volume : Measure (E d × E d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

instance instIsAddHaarVolumePt : (volume : Measure (Pt d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- `(∂_t + v·∇_x) f = Δ_v f + g` in the sense of distributions on `ℝ × ℝᵈ × ℝᵈ`. -/
def IsDistribSol (f g : Pt d → ℝ) : Prop :=
  LocallyIntegrable f ∧ ∀ φ : Pt d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ p, f p * (-(dT φ p) - transport φ p - Matrix.trace (hessV φ p)) = ∫ p, g p * φ p

/-- `D_v² f ∈ L^∞_loc` in the sense of distributions: there is a locally integrable, locally
essentially bounded matrix field `H` with `∫ f ∂_{v_i v_j} φ = ∫ H_{ij} φ` for all test functions. -/
def HessVLinfLoc (f : Pt d → ℝ) : Prop :=
  ∃ H : Pt d → Matrix (Fin d) (Fin d) ℝ, (∀ i j, LocallyIntegrable (fun p => H p i j)) ∧
    (∀ K : Set (Pt d), IsCompact K → ∃ M : ℝ, ∀ᵐ p, p ∈ K → frob (H p) ≤ M) ∧
    ∀ φ : Pt d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ i j, ∫ p, f p * hessV φ p i j = ∫ p, H p i j * φ p

/-! ### Slice derivatives as full derivatives -/

/-- The unit vectors of `ℝ × ℝᵈ × ℝᵈ`. -/
def eT : Pt d := (1, 0, 0)
def eX (i : Fin d) : Pt d := (0, ev i, 0)
def eV (i : Fin d) : Pt d := (0, 0, ev i)

lemma hasFDerivAt_sliceX (t : ℝ) (x v : E d) :
    HasFDerivAt (fun z : E d => ((t, z, v) : Pt d))
      ((ContinuousLinearMap.inr ℝ ℝ (E d × E d)).comp (ContinuousLinearMap.inl ℝ (E d) (E d))) x :=
  (hasFDerivAt_prodMk_right t (x, v)).comp x (hasFDerivAt_prodMk_left x v)

lemma hasFDerivAt_sliceV (t : ℝ) (x v : E d) :
    HasFDerivAt (fun w : E d => ((t, x, w) : Pt d))
      ((ContinuousLinearMap.inr ℝ ℝ (E d × E d)).comp (ContinuousLinearMap.inr ℝ (E d) (E d))) v :=
  (hasFDerivAt_prodMk_right t (x, v)).comp v (hasFDerivAt_prodMk_right x v)

lemma dT_eq_fderiv {F : Pt d → ℝ} (hF : Differentiable ℝ F) (p : Pt d) :
    dT F p = fderiv ℝ F p eT := by
  obtain ⟨t, x, v⟩ := p
  unfold dT
  have h1 : HasDerivAt (fun s : ℝ => ((s, x, v) : Pt d)) ((1, 0, 0) : Pt d) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (x, v))
  have h2 := (hF (t, x, v)).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.deriv

lemma gradX_eq_fderiv {F : Pt d → ℝ} (hF : Differentiable ℝ F) (t : ℝ) (x v y : E d) :
    gradX F (t, x, v) y = fderiv ℝ F (t, x, v) (0, y, 0) := by
  unfold gradX
  dsimp only
  have h : HasFDerivAt (fun z => F (t, z, v)) _ x :=
    (hF (t, x, v)).hasFDerivAt.comp x (hasFDerivAt_sliceX t x v)
  rw [h.fderiv]
  simp

lemma fderiv_sliceV_eq {F : Pt d → ℝ} (hF : Differentiable ℝ F) (t : ℝ) (x w e : E d) :
    fderiv ℝ (fun w' => F (t, x, w')) w e = fderiv ℝ F (t, x, w) (0, 0, e) := by
  have h : HasFDerivAt (fun w' => F (t, x, w')) _ w :=
    (hF (t, x, w)).hasFDerivAt.comp w (hasFDerivAt_sliceV t x w)
  rw [h.fderiv]
  simp

lemma transport_eq_fderiv {F : Pt d → ℝ} (hF : Differentiable ℝ F) (t : ℝ) (x v : E d) :
    transport F (t, x, v) = ∑ i : Fin d, v i * fderiv ℝ F (t, x, v) (eX i) := by
  unfold transport
  rw [gradX_eq_fderiv hF]
  have hv : ((0 : ℝ), v, (0 : E d)) = ∑ i : Fin d, v i • eX i := by
    have e1 : v = ∑ i : Fin d, v i • ev i := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
      simp [ev]
    set L := (ContinuousLinearMap.inr ℝ ℝ (E d × E d)).comp (ContinuousLinearMap.inl ℝ (E d) (E d))
    have hL : ∀ w, L w = ((0 : ℝ), w, (0 : E d)) := fun w => rfl
    rw [← hL]
    conv_lhs => rw [e1]
    rw [map_sum]
    simp only [map_smul, hL, eX, Prod.smul_mk, smul_zero]
  rw [hv, map_sum]
  simp [map_smul]

lemma hessV_eq_fderiv {F : Pt d → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x v : E d) (i j : Fin d) :
    hessV F (t, x, v) i j = fderiv ℝ (fun q => fderiv ℝ F q (eV j)) (t, x, v) (eV i) := by
  have hdF : Differentiable ℝ F := hF.differentiable (by simp)
  unfold hessV
  simp only
  have e : (fun w => fderiv ℝ (fun w' => F (t, x, w')) w (ev j)) =
      fun w => fderiv ℝ F (t, x, w) (eV j) := by
    funext w; rw [fderiv_sliceV_eq hdF]; rfl
  rw [e]
  have hG : Differentiable ℝ (fun q : Pt d => fderiv ℝ F q (eV j)) := by
    have : ContDiff ℝ ∞ (fun q : Pt d => fderiv ℝ F q (eV j)) :=
      (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact this.differentiable (by simp)
  have h0 : HasFDerivAt (fun q : Pt d => fderiv ℝ F q (eV j))
      (fderiv ℝ (fun q : Pt d => fderiv ℝ F q (eV j)) (t, x, v)) (t, x, v) :=
    (hG (t, x, v)).hasFDerivAt
  have h1 := HasFDerivAt.comp v h0 (hasFDerivAt_sliceV t x v)
  have h : HasFDerivAt (fun w => fderiv ℝ F (t, x, w) (eV j)) _ v := h1
  rw [h.fderiv]
  simp [eV]

/-! ### Classical solutions are distributional solutions -/

lemma ibp_Pt {f φ : Pt d → ℝ} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (w : Pt d) :
    ∫ p, f p * fderiv ℝ φ p w = -∫ p, fderiv ℝ f p w * φ p := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  · exact (hf.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport (hφc.fderiv_apply ℝ w).mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  · exact fun x _ => (hf.differentiable (by simp)) x
  · exact fun x _ => (hφ.differentiable (by simp)) x

/-- **Classical solutions are distributional solutions.** -/
theorem isDistribSol_of_KFP {f : Pt d → ℝ} (hf : ContDiff ℝ ∞ f) {g : E d → ℝ}
    (hg : Continuous g) (heq : ∀ p, KFP f (fun _ => 1) (fun _ => 0) (fun p => g p.2.1) p) :
    IsDistribSol f (fun p => g p.2.1) := by
  refine ⟨hf.continuous.locallyIntegrable, fun φ hφ hφc => ?_⟩
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by simp)
  -- the coordinate functions `v_i`
  set vi : Fin d → Pt d → ℝ := fun i p => p.2.2 i with hvi
  have hvi_cd : ∀ i, ContDiff ℝ ∞ (vi i) := fun i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).comp
      ((ContinuousLinearMap.snd ℝ (E d) (E d)).comp (ContinuousLinearMap.snd ℝ ℝ (E d × E d)))).contDiff
  have hvi_fd : ∀ i p, fderiv ℝ (vi i) p (eX i) = 0 := by
    intro i p
    have : vi i = ⇑((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).comp
      ((ContinuousLinearMap.snd ℝ (E d) (E d)).comp (ContinuousLinearMap.snd ℝ ℝ (E d × E d)))) := rfl
    rw [this, ContinuousLinearMap.fderiv]
    simp [eX]
  -- rewrite the operators with full derivatives
  have hT : ∀ p, dT φ p = fderiv ℝ φ p eT := dT_eq_fderiv hdφ
  have hX : ∀ p : Pt d, transport φ p = ∑ i, p.2.2 i * fderiv ℝ φ p (eX i) := by
    rintro ⟨t, x, v⟩; exact transport_eq_fderiv hdφ t x v
  have hV : ∀ p : Pt d, Matrix.trace (hessV φ p) =
      ∑ i, fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) p (eV i) := by
    rintro ⟨t, x, v⟩
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.sum_congr rfl fun i _ => hessV_eq_fderiv hφ t x v i i
  have hTf : ∀ p, dT f p = fderiv ℝ f p eT := dT_eq_fderiv hdf
  have hXf : ∀ p : Pt d, transport f p = ∑ i, p.2.2 i * fderiv ℝ f p (eX i) := by
    rintro ⟨t, x, v⟩; exact transport_eq_fderiv hdf t x v
  have hVf : ∀ p : Pt d, Matrix.trace (hessV f p) =
      ∑ i, fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i) := by
    rintro ⟨t, x, v⟩
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.sum_congr rfl fun i _ => hessV_eq_fderiv hf t x v i i
  -- integrability of all the pieces
  have cφ : ∀ w : Pt d, Continuous (fun p => fderiv ℝ φ p w) := fun w =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ1 : ∀ i, ContDiff ℝ ∞ (fun q => fderiv ℝ φ q (eV i)) := fun i =>
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hf1 : ∀ i, ContDiff ℝ ∞ (fun q => fderiv ℝ f q (eV i)) := fun i =>
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have Iint : ∀ (u ψ : Pt d → ℝ), Continuous u → Continuous ψ →
      HasCompactSupport ψ → Integrable (fun p => u p * ψ p) :=
    fun u ψ hu hψ hψc => (hu.mul hψ).integrable_of_hasCompactSupport hψc.mul_left
  have i1 : Integrable (fun p => f p * fderiv ℝ φ p eT) :=
    Iint _ _ hf.continuous (cφ eT) (hφc.fderiv_apply ℝ eT)
  have i2 : ∀ i, Integrable (fun p => f p * (p.2.2 i * fderiv ℝ φ p (eX i))) := by
    intro i
    have := Iint _ _ ((hf.continuous.mul (hvi_cd i).continuous)) (cφ (eX i))
      (hφc.fderiv_apply ℝ (eX i))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply, hvi]; ring
  have i3 : ∀ i, Integrable (fun p => f p * fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) p (eV i)) :=
    fun i => Iint _ _ hf.continuous
      (((hφ1 i).continuous_fderiv (by simp)).clm_apply continuous_const)
      (((hφc.fderiv_apply ℝ (eV i))).fderiv_apply ℝ (eV i))
  -- integrations by parts
  have ibpT : ∫ p, f p * fderiv ℝ φ p eT = -∫ p, fderiv ℝ f p eT * φ p := ibp_Pt hf hφ hφc eT
  have ibpX : ∀ i, ∫ p, f p * (p.2.2 i * fderiv ℝ φ p (eX i)) =
      -∫ p, p.2.2 i * fderiv ℝ f p (eX i) * φ p := by
    intro i
    have h := ibp_Pt ((hf.mul (hvi_cd i))) hφ hφc (eX i)
    have e2 : ∀ p, fderiv ℝ (fun x => f x * vi i x) p (eX i) = p.2.2 i * fderiv ℝ f p (eX i) := by
      intro p
      rw [fderiv_fun_mul (hdf p) (((hvi_cd i).differentiable (by simp)) p)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hvi_fd i p]
      simp [hvi]
    calc ∫ p, f p * (p.2.2 i * fderiv ℝ φ p (eX i))
        = ∫ p, f p * vi i p * fderiv ℝ φ p (eX i) := by
          congr 1; funext p; simp only [hvi]; ring
      _ = -∫ p, fderiv ℝ (fun x => f x * vi i x) p (eX i) * φ p := h
      _ = -∫ p, p.2.2 i * fderiv ℝ f p (eX i) * φ p := by
          congr 2; funext p; rw [e2]
  have ibpV : ∀ i, ∫ p, f p * fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) p (eV i) =
      ∫ p, fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i) * φ p := by
    intro i
    have h1 := ibp_Pt hf (hφ1 i) (hφc.fderiv_apply ℝ (eV i)) (eV i)
    have h2 := ibp_Pt (hf1 i) hφ hφc (eV i)
    rw [h1, h2, neg_neg]
  -- assemble
  have hsplit : (fun p => f p * (-(dT φ p) - transport φ p - Matrix.trace (hessV φ p))) =
      fun p => -(f p * fderiv ℝ φ p eT) - ∑ i, f p * (p.2.2 i * fderiv ℝ φ p (eX i)) -
        ∑ i, f p * fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) p (eV i) := by
    funext p
    rw [hT, hX, hV]
    simp only [mul_sub, mul_neg, Finset.mul_sum]
  have i1' : Integrable (fun p => -(f p * fderiv ℝ φ p eT)) := i1.neg
  have i2' : Integrable (fun p => ∑ i, f p * (p.2.2 i * fderiv ℝ φ p (eX i))) :=
    integrable_finsetSum _ fun i _ => i2 i
  have i3' : Integrable (fun p => ∑ i, f p * fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) p (eV i)) :=
    integrable_finsetSum _ fun i _ => i3 i
  have i12 : Integrable (fun p => -(f p * fderiv ℝ φ p eT) -
      ∑ i, f p * (p.2.2 i * fderiv ℝ φ p (eX i))) := i1'.sub i2'
  rw [hsplit, integral_sub i12 i3', integral_sub i1' i2', integral_neg,
    integral_finsetSum _ (fun i _ => i2 i), integral_finsetSum _ (fun i _ => i3 i), ibpT]
  simp_rw [ibpX, ibpV]
  -- the right-hand side
  have hrhs : (fun p : Pt d => g p.2.1 * φ p) = fun p =>
      (fderiv ℝ f p eT + ∑ i, p.2.2 i * fderiv ℝ f p (eX i) -
        ∑ i, fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i)) * φ p := by
    funext p
    have := heq p
    unfold KFP at this
    rw [hTf, hXf, Matrix.one_mul, hVf] at this
    simp only [zero_mul, add_zero] at this
    rw [show g p.2.1 = fderiv ℝ f p eT + ∑ i, p.2.2 i * fderiv ℝ f p (eX i) -
      ∑ i, fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i) by linarith]
  rw [hrhs]
  have j1 : Integrable (fun p => fderiv ℝ f p eT * φ p) :=
    Iint _ _ ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) hφ.continuous hφc
  have j2 : ∀ i, Integrable (fun p : Pt d => p.2.2 i * fderiv ℝ f p (eX i) * φ p) := fun i =>
    Iint _ _ ((hvi_cd i).continuous.mul ((hf.continuous_fderiv (by simp)).clm_apply
      continuous_const)) hφ.continuous hφc
  have j3 : ∀ i, Integrable (fun p => fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i) * φ p) :=
    fun i => Iint _ _ (((hf1 i).continuous_fderiv (by simp)).clm_apply continuous_const)
      hφ.continuous hφc
  have hr2 : (fun p => (fderiv ℝ f p eT + ∑ i, p.2.2 i * fderiv ℝ f p (eX i) -
        ∑ i, fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i)) * φ p) =
      fun p => fderiv ℝ f p eT * φ p + ∑ i, p.2.2 i * fderiv ℝ f p (eX i) * φ p -
        ∑ i, fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i) * φ p := by
    funext p; simp only [add_mul, sub_mul, Finset.sum_mul]
  have j2' : Integrable (fun p : Pt d => ∑ i, p.2.2 i * fderiv ℝ f p (eX i) * φ p) :=
    integrable_finsetSum _ fun i _ => j2 i
  have j3' : Integrable (fun p => ∑ i, fderiv ℝ (fun q => fderiv ℝ f q (eV i)) p (eV i) * φ p) :=
    integrable_finsetSum _ fun i _ => j3 i
  have j12 : Integrable (fun p => fderiv ℝ f p eT * φ p +
      ∑ i, p.2.2 i * fderiv ℝ f p (eX i) * φ p) := j1.add j2'
  rw [hr2, integral_sub j12 j3', integral_add j1 j2',
    integral_finsetSum _ (fun i _ => j2 i), integral_finsetSum _ (fun i _ => j3 i)]
  simp only [neg_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  try ring

/-! ### Passing to the limit in the forcing -/

lemma aesm_heat_path {h : E d → ℂ} (hh : AEStronglyMeasurable h) (x v : E d) :
    AEStronglyMeasurable (fun s : ℝ => heat (s ^ 3 / 3) h (x - s • v)) (volume.restrict (Ioi 0)) := by
  unfold heat
  have hG : AEStronglyMeasurable (fun q : ℝ × E d =>
      ((hk d (q.1 ^ 3 / 3) (x - q.1 • v - q.2) : ℝ) : ℂ) * h q.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    apply AEStronglyMeasurable.mul
    · apply Continuous.comp_aestronglyMeasurable Complex.continuous_ofReal
      apply Measurable.aestronglyMeasurable
      exact measurable_hk_uncurry.comp (((measurable_fst.pow_const 3).div_const 3).prodMk
        ((measurable_const.sub (measurable_fst.smul measurable_const)).sub measurable_snd))
    · exact hh.comp_snd
  exact hG.integral_prod_right'

lemma integral_norm_le_of_bound {h : E d → ℝ} {K : ℝ} (hK : ∀ y, |h y| ≤ K)
    (hs : ∀ y, 1 ≤ ‖y‖ → h y = 0) :
    ∫ y, ‖(h y : ℂ)‖ ≤ K * (volume (Metric.ball (0 : E d) 1)).toReal := by
  have e : ∫ y, ‖(h y : ℂ)‖ = ∫ y in Metric.ball (0 : E d) 1, ‖(h y : ℂ)‖ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    have : 1 ≤ ‖y‖ := by simpa [Metric.mem_ball, dist_zero_right] using hy
    simp [hs y this]
  rw [e]
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (E d)))
    (s := Metric.ball (0 : E d) 1) (f := fun y => ‖(h y : ℂ)‖) (C := K) measure_ball_lt_top
    (fun y _ => by rw [norm_norm, Complex.norm_real, Real.norm_eq_abs]; exact hK y)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)] at this
  exact this

/-- `𝒮 g_n → 𝒮 g` pointwise if `g_n → g` a.e., boundedly, with supports in `B₁`. -/
theorem solF_tendsto (hd : 1 ≤ d) {g : E d → ℝ} {gn : ℕ → E d → ℝ} {K : ℝ}
    (hgm : ∀ n, AEStronglyMeasurable (gn n)) (hK : ∀ n y, |gn n y| ≤ K)
    (hs : ∀ n y, 1 ≤ ‖y‖ → gn n y = 0)
    (hlim : ∀ᵐ y, Tendsto (fun n => gn n y) atTop (𝓝 (g y))) (p : Pt d) :
    Tendsto (fun n => solF (fun y => (gn n y : ℂ)) p) atTop (𝓝 (solF (fun y => (g y : ℂ)) p)) := by
  obtain ⟨t, x, v⟩ := p
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 0)
  set L := K * (volume (Metric.ball (0 : E d) 1)).toReal
  have hL0 : 0 ≤ L := mul_nonneg hK0 ENNReal.toReal_nonneg
  have hgnC : ∀ n, AEStronglyMeasurable (fun y => (gn n y : ℂ)) := fun n =>
    Complex.continuous_ofReal.comp_aestronglyMeasurable (hgm n)
  have hgnI : ∀ n, Integrable (fun y => (gn n y : ℂ)) := by
    intro n
    have hb : IntegrableOn (fun y => (gn n y : ℂ)) (Metric.ball (0 : E d) 1) :=
      IntegrableOn.of_bound measure_ball_lt_top (hgnC n).restrict K
        (Eventually.of_forall fun y => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hK n y)
    refine hb.integrable_of_forall_notMem_eq_zero (fun y hy => ?_)
    have : 1 ≤ ‖y‖ := by simpa [Metric.mem_ball, dist_zero_right] using hy
    simp [hs n y this]
  -- convergence of `P_τ g_n(z)` for each `τ > 0`
  have hheat : ∀ s ∈ Ioi (0 : ℝ), Tendsto (fun n => heat (s ^ 3 / 3) (fun y => (gn n y : ℂ))
      (x - s • v)) atTop (𝓝 (heat (s ^ 3 / 3) (fun y => (g y : ℂ)) (x - s • v))) := by
    intro s hs0
    have hτ : (0 : ℝ) < s ^ 3 / 3 := by
      have : 0 < s := hs0
      positivity
    unfold heat
    apply tendsto_integral_of_dominated_convergence (fun y => hk d (s ^ 3 / 3) (x - s • v - y) * K)
    · intro n
      exact (Complex.continuous_ofReal.comp ((continuous_hk _).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable.mul (hgnC n)
    · exact (integrable_hk_sub hτ _).mul_const K
    · intro n
      filter_upwards with y
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk_nonneg hτ.le _),
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hK n y) (hk_nonneg hτ.le _)
    · filter_upwards [hlim] with y hy
      exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hy)
  have hkin : Tendsto (fun n => kin (fun y => (gn n y : ℂ)) x v) atTop
      (𝓝 (kin (fun y => (g y : ℂ)) x v)) := by
    unfold kin
    apply tendsto_integral_of_dominated_convergence
      (fun s => min K ((4 * π * (s ^ 3 / 3)) ^ (-(d : ℝ) / 2) * L))
    · intro n; exact aesm_heat_path (hgnC n) x v
    · exact integrableOn_kinBd hd hK0 hL0
    · intro n
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with s hs0
      have hτ : (0 : ℝ) < s ^ 3 / 3 := by
        have : 0 < s := hs0
        positivity
      refine le_min (norm_heat_le_sup hτ (fun y => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hK n y) _) ?_
      refine (norm_heat_le_L1 hτ (hgnI n) _).trans ?_
      apply mul_le_mul_of_nonneg_left (integral_norm_le_of_bound (hK n) (hs n))
      exact Real.rpow_nonneg (by positivity) _
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall hheat
  exact (Complex.continuous_re.tendsto _).comp hkin

/-- **Approximation**: if smooth compactly supported `g_n → g` a.e., boundedly and with supports
in `B₁`, then `f = Re 𝒮g` is a bounded distributional solution with forcing `g`. -/
theorem isDistribSol_of_approx (hd : 1 ≤ d) {g : E d → ℝ} {gn : ℕ → E d → ℝ} {K : ℝ}
    (hgn : ∀ n, ContDiff ℝ ∞ (gn n)) (hgnc : ∀ n, HasCompactSupport (gn n))
    (hK : ∀ n y, |gn n y| ≤ K) (hs : ∀ n y, 1 ≤ ‖y‖ → gn n y = 0)
    (hlim : ∀ᵐ y, Tendsto (fun n => gn n y) atTop (𝓝 (g y))) :
    IsDistribSol (solF (fun y => (g y : ℂ))) (fun p => g p.2.1) ∧
      ∀ p, |solF (fun y => (g y : ℂ)) p| ≤ kinBd d K (K * (volume (Metric.ball (0 : E d) 1)).toReal) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 0)
  set C := kinBd d K (K * (volume (Metric.ball (0 : E d) 1)).toReal)
  set fn : ℕ → Pt d → ℝ := fun n => solF (fun y => (gn n y : ℂ))
  set f := solF (fun y => (g y : ℂ))
  have hlimf : ∀ p, Tendsto (fun n => fn n p) atTop (𝓝 (f p)) := fun p =>
    solF_tendsto hd (fun n => (hgn n).continuous.aestronglyMeasurable) hK hs hlim p
  have hfnC : ∀ n p, |fn n p| ≤ C := by
    intro n p
    have hint : Integrable (fun y => (gn n y : ℂ)) := by
      rw [← coe_toS (gn n) (hgn n) (hgnc n)]; exact (toS _ _ _).integrable
    refine (abs_solF_le hd hint (K := K) (fun y => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hK n y) p).trans ?_
    exact kinBd_mono hd hK0 (integral_nonneg fun y => norm_nonneg _)
      (integral_norm_le_of_bound (hK n) (hs n))
  have hfC : ∀ p, |f p| ≤ C := fun p =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (hlimf p)) (fun n => hfnC n p)
  have hfn_smooth : ∀ n, ContDiff ℝ ∞ (fn n) := fun n => by
    simp only [fn]; rw [← coe_toS (gn n) (hgn n) (hgnc n)]; exact solF_smooth hd _
  have hfn_sol : ∀ n, IsDistribSol (fn n) (fun p => gn n p.2.1) := fun n =>
    isDistribSol_of_KFP (hfn_smooth n) (hgn n).continuous (solF_KFP hd (gn n) (hgn n) (hgnc n))
  have hfm : AEStronglyMeasurable f := aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hfn_smooth n).continuous.aestronglyMeasurable) (Eventually.of_forall hlimf)
  refine ⟨⟨?_, fun φ hφ hφc => ?_⟩, hfC⟩
  · rw [locallyIntegrable_iff]
    intro Kc hKc
    exact IntegrableOn.of_bound hKc.measure_lt_top hfm.restrict C
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hfC p)
  · -- pass to the limit in the weak formulation
    set Lφ : Pt d → ℝ := fun p => -(dT φ p) - transport φ p - Matrix.trace (hessV φ p)
    have hLc : Continuous Lφ := by
      have hdφ : Differentiable ℝ φ := hφ.differentiable (by simp)
      have e : Lφ = fun p => -(fderiv ℝ φ p eT) - ∑ i, p.2.2 i * fderiv ℝ φ p (eX i) -
          ∑ i, fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) p (eV i) := by
        funext ⟨t, x, v⟩
        simp only [Lφ]
        rw [dT_eq_fderiv hdφ, transport_eq_fderiv hdφ]
        congr 1
        simp only [Matrix.trace, Matrix.diag]
        exact Finset.sum_congr rfl fun i _ => hessV_eq_fderiv hφ t x v i i
      rw [e]
      have c1 : ∀ w : Pt d, Continuous (fun p => fderiv ℝ φ p w) := fun w =>
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
      have c2 : ∀ i, Continuous (fun p => fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) p (eV i)) := fun i =>
        (((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous_fderiv
          (by simp)).clm_apply continuous_const
      have c3 : ∀ i : Fin d, Continuous (fun p : Pt d => p.2.2 i) := fun i =>
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).continuous.comp (continuous_snd.comp continuous_snd)
      exact ((c1 eT).neg.sub (continuous_finsetSum _ fun i _ => (c3 i).mul (c1 (eX i)))).sub
        (continuous_finsetSum _ fun i _ => c2 i)
    have hLcs : HasCompactSupport Lφ := by
      have hdφ : Differentiable ℝ φ := hφ.differentiable (by simp)
      apply HasCompactSupport.intro hφc
      intro p hp
      have hφ0 : ∀ᶠ q in 𝓝 p, φ q = 0 := by
        have : p ∉ tsupport φ := hp
        rw [notMem_tsupport_iff_eventuallyEq] at this
        exact this
      have hf0 : fderiv ℝ φ =ᶠ[𝓝 p] 0 := by
        filter_upwards [hφ0.eventually_nhds] with q hq
        have hq' : φ =ᶠ[𝓝 q] fun _ => (0 : ℝ) := hq
        rw [hq'.fderiv_eq]
        simp
      obtain ⟨t, x, v⟩ := p
      simp only [Lφ]
      rw [dT_eq_fderiv hdφ, transport_eq_fderiv hdφ]
      simp only [Matrix.trace, Matrix.diag]
      simp_rw [hessV_eq_fderiv hφ t x v]
      have h1 : fderiv ℝ φ (t, x, v) = 0 := hf0.eq_of_nhds
      have h2 : ∀ i, fderiv ℝ (fun q => fderiv ℝ φ q (eV i)) (t, x, v) = 0 := by
        intro i
        have : (fun q => fderiv ℝ φ q (eV i)) =ᶠ[𝓝 (t, x, v)] fun _ => 0 := by
          filter_upwards [hf0] with q hq
          rw [hq]; rfl
        rw [this.fderiv_eq]
        simp
      simp [h1, h2]
    have hLi : Integrable Lφ := hLc.integrable_of_hasCompactSupport hLcs
    have hlhs : Tendsto (fun n => ∫ p, fn n p * Lφ p) atTop (𝓝 (∫ p, f p * Lφ p)) := by
      apply tendsto_integral_of_dominated_convergence (fun p => C * |Lφ p|)
      · intro n
        exact ((hfn_smooth n).continuous.mul hLc).aestronglyMeasurable
      · exact hLi.abs.const_mul C
      · intro n
        filter_upwards with p
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hfnC n p) (abs_nonneg _)
      · filter_upwards with p
        exact (hlimf p).mul tendsto_const_nhds
    have hae : ∀ᵐ p : Pt d, Tendsto (fun n => gn n p.2.1) atTop (𝓝 (g p.2.1)) := by
      have h1 : Measure.QuasiMeasurePreserving (fun p : Pt d => p.2.1) volume volume :=
        Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd
      exact h1.ae hlim
    have hrhs : Tendsto (fun n => ∫ p, gn n p.2.1 * φ p) atTop (𝓝 (∫ p, g p.2.1 * φ p)) := by
      apply tendsto_integral_of_dominated_convergence (fun p => K * |φ p|)
      · intro n
        exact (((hgn n).continuous.comp (continuous_fst.comp continuous_snd)).mul
          hφ.continuous).aestronglyMeasurable
      · exact (hφ.continuous.integrable_of_hasCompactSupport hφc).abs.const_mul K
      · intro n
        filter_upwards with p
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hK n _) (abs_nonneg _)
      · filter_upwards [hae] with p hp
        exact hp.mul tendsto_const_nhds
    have heq : ∀ n, ∫ p, fn n p * Lφ p = ∫ p, gn n p.2.1 * φ p := fun n => (hfn_sol n).2 φ hφ hφc
    exact tendsto_nhds_unique (hlhs.congr heq) hrhs

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Distrib

-- ============================================================================
-- KineticCounterexamples/Endpoint/Criterion.lean
-- ============================================================================

section File_Endpoint_Criterion

/-!
# A criterion for `D_v² f ∉ L^∞_loc`

For a bounded forcing `g` supported in `B₁` and `f = Re 𝒮g`: if `D_v² f ∈ L^∞_loc` in the sense of
distributions, then there is `M` such that for every test function `θ ≥ 0` supported in `B̄₁`
`|∂_{v_{i₀} v_{i₁}} 𝒮(θ̌ ⋆ g)(0,0)| ≤ M ∫ θ`, where `(θ̌ ⋆ g)(y) = ∫ θ(x) g(y + x) dx`
(`hessV_bound_of_linfLoc`). The proof tests the distributional identity against
`φ(t,x,v) = α(t) θ(x) ρ_η(v)` and lets the velocity bump `ρ_η` concentrate.
-/

noncomputable section

open Real Complex MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ENNReal ContDiff Convolution

namespace KS

variable {d : ℕ}

/-! ### The smoothing `θ̌ ⋆ g` -/

/-- `(θ̌ ⋆ g)(y) = ∫ θ(x) g(y + x) dx`. -/
def thConv (θ g : E d → ℝ) : E d → ℝ :=
  (fun t => θ (-t)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure (E d))] g

lemma thConv_apply (θ g : E d → ℝ) (y : E d) : thConv θ g y = ∫ x, θ x * g (y + x) := by
  unfold thConv
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have := integral_neg_eq_self (fun x : E d => θ x * g (y + x)) (volume : Measure (E d))
  rw [← this]
  congr 1

lemma hasCompactSupport_of_ball {g : E d → ℝ} (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0) :
    HasCompactSupport g := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E d) 1)
  intro y hy
  apply hs
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  exact hy.le

lemma integrable_of_bound {g : E d → ℝ} (hgm : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K)
    (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0) : Integrable g := by
  have hb : IntegrableOn g (Metric.ball (0 : E d) 1) :=
    IntegrableOn.of_bound measure_ball_lt_top hgm.aestronglyMeasurable.restrict K
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hK y)
  refine hb.integrable_of_forall_notMem_eq_zero (fun y hy => ?_)
  have : 1 ≤ ‖y‖ := by simpa [Metric.mem_ball, dist_zero_right] using hy
  exact hs y this

lemma contDiff_thConv {θ g : E d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hgm : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0) :
    ContDiff ℝ ∞ (thConv θ g) := by
  unfold thConv
  exact HasCompactSupport.contDiff_convolution_left _ (hθc.comp_homeomorph (Homeomorph.neg (E d)))
    (hθ.comp contDiff_neg) (integrable_of_bound hgm hK hs).locallyIntegrable

lemma hasCompactSupport_thConv {θ g : E d → ℝ} (hθc : HasCompactSupport θ)
    (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0) : HasCompactSupport (thConv θ g) := by
  unfold thConv
  exact (hθc.comp_homeomorph (Homeomorph.neg (E d))).convolution _ (hasCompactSupport_of_ball hs)

lemma abs_thConv_le {θ g : E d → ℝ} (hθ0 : ∀ x, 0 ≤ θ x) (hθi : Integrable θ) {K : ℝ}
    (hK : ∀ y, |g y| ≤ K) (y : E d) : |thConv θ g y| ≤ K * ∫ x, θ x := by
  rw [thConv_apply, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => abs_nonneg _) (hθi.const_mul K) (Eventually.of_forall fun x => ?_))
  show |θ x * g (y + x)| ≤ K * θ x
  rw [abs_mul, abs_of_nonneg (hθ0 x), mul_comm]
  exact mul_le_mul_of_nonneg_right (hK _) (hθ0 x)

lemma thConv_eq_zero {θ g : E d → ℝ} (hθs : tsupport θ ⊆ Metric.closedBall 0 1)
    (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0) {y : E d} (hy : 2 ≤ ‖y‖) : thConv θ g y = 0 := by
  rw [thConv_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport θ
  · have hx1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hθs hx
    have : 1 ≤ ‖y + x‖ := by
      have := norm_sub_norm_le y (-x)
      rw [norm_neg, sub_neg_eq_add] at this
      linarith
    simp [hs _ this]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-! ### Measurability of the solution operator -/

lemma sm_heat_param {α : Type*} [MeasurableSpace α]
    {h : E d → ℂ} (hh : Measurable h) {τ : α → ℝ} (hτ : Measurable τ)
    {Z : α → E d} (hZ : Measurable Z) :
    StronglyMeasurable (fun a => heat (τ a) h (Z a)) := by
  unfold heat
  have hG : StronglyMeasurable (Function.uncurry fun (a : α) (y : E d) =>
      ((hk d (τ a) (Z a - y) : ℝ) : ℂ) * h y) := by
    apply Measurable.stronglyMeasurable
    exact (Complex.measurable_ofReal.comp (measurable_hk_uncurry.comp ((hτ.comp measurable_fst).prodMk
      ((hZ.comp measurable_fst).sub measurable_snd)))).mul (hh.comp measurable_snd)
  exact hG.integral_prod_right

lemma aesm_heat_param {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : E d → ℂ} (hh : Measurable h) {τ : α → ℝ} (hτ : Measurable τ)
    {Z : α → E d} (hZ : Measurable Z) :
    AEStronglyMeasurable (fun a => heat (τ a) h (Z a)) μ :=
  (sm_heat_param hh hτ hZ).aestronglyMeasurable

lemma sm_kin {h : E d → ℂ} (hh : Measurable h) :
    StronglyMeasurable (fun q : E d × E d => kin h q.1 q.2) := by
  unfold kin
  have := sm_heat_param (α := (E d × E d) × ℝ) hh (τ := fun a => a.2 ^ 3 / 3) (by fun_prop)
    (Z := fun a => a.1.1 - a.2 • a.1.2) (by fun_prop)
  exact (this : StronglyMeasurable (Function.uncurry fun (q : E d × E d) (s : ℝ) =>
    heat (s ^ 3 / 3) h (q.1 - s • q.2))).integral_prod_right

/-! ### The Fubini identity `∫ θ(x) 𝒮g(x,v) dx = 𝒮(θ̌⋆g)(0,v)` -/

lemma heat_thConv {θ g : E d → ℝ} (hθi : Integrable θ) (hgm : Measurable g) {K : ℝ}
    (hK : ∀ y, |g y| ≤ K) {τ : ℝ} (hτ : 0 < τ) (z : E d) :
    heat τ (fun y => (thConv θ g y : ℂ)) z = ∫ x, (θ x : ℂ) * heat τ (fun y => (g y : ℂ)) (z + x) := by
  unfold heat
  simp_rw [thConv_apply]
  -- swap the integrals
  have hint : Integrable (fun q : E d × E d =>
      ((hk d τ (z - q.1) : ℝ) : ℂ) * ((θ q.2 * g (q.1 + q.2) : ℝ) : ℂ)) (volume.prod volume) := by
    have hb : Integrable (fun q : E d × E d => hk d τ (z - q.1) * (|θ q.2| * K)) (volume.prod volume) :=
      (integrable_hk_sub hτ z).mul_prod (hθi.abs.mul_const K)
    refine hb.mono' ?_ (Eventually.of_forall fun q => ?_)
    · apply AEStronglyMeasurable.mul
      · exact (Complex.continuous_ofReal.comp ((continuous_hk τ).comp
          (continuous_const.sub continuous_fst))).aestronglyMeasurable
      · apply Continuous.comp_aestronglyMeasurable Complex.continuous_ofReal
        exact hθi.1.comp_snd.mul (hgm.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hk_nonneg hτ.le _), abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _))
        (hk_nonneg hτ.le _)
  have e1 : ∀ y, ((hk d τ (z - y) : ℝ) : ℂ) * ((∫ x, θ x * g (y + x) : ℝ) : ℂ) =
      ∫ x, ((hk d τ (z - y) : ℝ) : ℂ) * ((θ x * g (y + x) : ℝ) : ℂ) := by
    intro y
    rw [← integral_complex_ofReal, integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap hint]
  congr 1
  funext x
  rw [← integral_const_mul]
  have := integral_add_right_eq_self (μ := (volume : Measure (E d)))
    (fun y => ((θ x : ℝ) : ℂ) * ((((hk d τ (z + x - y)) : ℝ) : ℂ) * ((g y : ℝ) : ℂ))) x
  rw [← this]
  congr 1
  funext y
  rw [show z + x - (y + x) = z - y by abel]
  push_cast
  ring

theorem integral_theta_kin {θ g : E d → ℝ} (hd : 1 ≤ d) (hθi : Integrable θ)
    (hgm : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0) (v : E d) :
    ∫ x, (θ x : ℂ) * kin (fun y => (g y : ℂ)) x v = kin (fun y => (thConv θ g y : ℂ)) 0 v := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  set L := K * (volume (Metric.ball (0 : E d) 1)).toReal
  have hL0 : 0 ≤ L := mul_nonneg hK0 ENNReal.toReal_nonneg
  have hgC : AEStronglyMeasurable (fun y => (g y : ℂ)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hgm.aestronglyMeasurable
  have hgI : Integrable (fun y => (g y : ℂ)) := (integrable_of_bound hgm hK hs).ofReal
  unfold kin
  simp_rw [← integral_const_mul]
  have hint : Integrable (fun q : E d × ℝ => (θ q.1 : ℂ) * heat (q.2 ^ 3 / 3)
      (fun y => (g y : ℂ)) (q.1 - q.2 • v)) (volume.prod (volume.restrict (Ioi 0))) := by
    have hb : Integrable (fun q : E d × ℝ => |θ q.1| *
        min K ((4 * π * (q.2 ^ 3 / 3)) ^ (-(d : ℝ) / 2) * L))
        (volume.prod (volume.restrict (Ioi 0))) :=
      hθi.abs.mul_prod (integrableOn_kinBd hd hK0 hL0)
    refine hb.mono' ?_ ?_
    · apply AEStronglyMeasurable.mul
      · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hθi.1).comp_fst
      · exact aesm_heat_param (Complex.measurable_ofReal.comp hgm) (by fun_prop) (by fun_prop)
    · have hpos : ∀ᵐ q ∂((volume : Measure (E d)).prod (volume.restrict (Ioi (0 : ℝ)))),
          q.2 ∈ Ioi (0 : ℝ) :=
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [hpos] with q hq
      have hτ : (0 : ℝ) < q.2 ^ 3 / 3 := by
        have : 0 < q.2 := hq
        positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine le_min (norm_heat_le_sup hτ (fun y => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hK y) _) ?_
      refine (norm_heat_le_L1 hτ hgI _).trans ?_
      apply mul_le_mul_of_nonneg_left (integral_norm_le_of_bound hK hs)
      exact Real.rpow_nonneg (by positivity) _
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hτ : (0 : ℝ) < s ^ 3 / 3 := by
    have : 0 < s := hs
    positivity
  rw [heat_thConv hθi hgm hK hτ]
  congr 1
  funext x
  rw [zero_sub, neg_add_eq_sub]

/-- The real form: `∫ θ(x) f(t,x,v) dx = Re 𝒮(θ̌⋆g)(0,v)`. -/
theorem integral_theta_solF {θ g : E d → ℝ} (hd : 1 ≤ d) (hθi : Integrable θ)
    (hgm : Measurable g) {K : ℝ} (hK : ∀ y, |g y| ≤ K) (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0)
    (t : ℝ) (v : E d) :
    ∫ x, θ x * solF (fun y => (g y : ℂ)) (t, x, v) =
      solF (fun y => (thConv θ g y : ℂ)) (0, 0, v) := by
  unfold solF
  simp only
  rw [← integral_theta_kin hd hθi hgm hK hs v]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hbd : ∀ x, ‖kin (fun y => (g y : ℂ)) x v‖ ≤ kinBd d K (∫ y, ‖(g y : ℂ)‖) := fun x =>
    norm_kin_le hd (integrable_of_bound hgm hK hs).ofReal
      (fun y => by show ‖((g y : ℝ) : ℂ)‖ ≤ K; rw [Complex.norm_real, Real.norm_eq_abs]; exact hK y)
      x v
  have hI : Integrable (fun x => (θ x : ℂ) * kin (fun y => (g y : ℂ)) x v) := by
    refine (hθi.norm.mul_const (kinBd d K (∫ y, ‖(g y : ℂ)‖))).mono' ?_
      (Eventually.of_forall fun x => ?_)
    · apply AEStronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hθi.1)
      have := sm_kin (d := d) (Complex.measurable_ofReal.comp hgm)
      exact (this.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hbd x) (norm_nonneg _)
  have hre := ContinuousLinearMap.integral_comp_comm Complex.reCLM hI
  simp only [Complex.reCLM_apply] at hre
  rw [← hre]
  congr 1
  funext x
  simp

/-! ### Integration by parts twice on `ℝᵈ` -/

lemma ibp2_E {F ρ : E d → ℝ} (hF : ContDiff ℝ ∞ F) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (m m' : E d) :
    ∫ w, F w * fderiv ℝ (fun z => fderiv ℝ ρ z m) w m' =
      ∫ w, fderiv ℝ (fun z => fderiv ℝ F z m') w m * ρ w := by
  have hρ1 : ContDiff ℝ ∞ (fun z => fderiv ℝ ρ z m) :=
    (hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hF1 : ContDiff ℝ ∞ (fun z => fderiv ℝ F z m') :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hρc1 : HasCompactSupport (fun z => fderiv ℝ ρ z m) := hρc.fderiv_apply ℝ m
  have step1 : ∫ w, F w * fderiv ℝ (fun z => fderiv ℝ ρ z m) w m' =
      -∫ w, fderiv ℝ F w m' * fderiv ℝ ρ w m := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        hρ1.continuous).integrable_of_hasCompactSupport hρc1.mul_left
    · exact (hF.continuous.mul ((hρ1.continuous_fderiv (by simp)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (hρc1.fderiv_apply ℝ m').mul_left
    · exact (hF.continuous.mul hρ1.continuous).integrable_of_hasCompactSupport hρc1.mul_left
    · exact fun x _ => (hF.differentiable (by simp)) x
    · exact fun x _ => (hρ1.differentiable (by simp)) x
  have step2 : ∫ w, fderiv ℝ F w m' * fderiv ℝ ρ w m =
      -∫ w, fderiv ℝ (fun z => fderiv ℝ F z m') w m * ρ w := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact (((hF1.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        hρ.continuous).integrable_of_hasCompactSupport hρc.mul_left
    · exact (hF1.continuous.mul ((hρ.continuous_fderiv (by simp)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (hρc.fderiv_apply ℝ m).mul_left
    · exact (hF1.continuous.mul hρ.continuous).integrable_of_hasCompactSupport hρc.mul_left
    · exact fun x _ => (hF1.differentiable (by simp)) x
    · exact fun x _ => (hρ.differentiable (by simp)) x
  rw [step1, step2, neg_neg]

/-! ### The criterion -/

/-- A velocity bump of radius `η`. -/
def vbump (η : ℝ) (hη : 0 < η) : ContDiffBump (0 : E d) := ⟨η / 2, η, by linarith, by linarith⟩

/-- **Criterion.** If `D_v² f ∈ L^∞_loc` for `f = Re 𝒮g`, then the mixed velocity derivatives of the
smoothed solutions `𝒮(θ̌⋆g)` at the origin are bounded by `M ∫θ`, uniformly over test functions
`θ ≥ 0` supported in `B̄₁`. -/
theorem hessV_bound_of_linfLoc (hd : 1 ≤ d) {g : E d → ℝ} (hgm : Measurable g) {K : ℝ}
    (hK : ∀ y, |g y| ≤ K) (hs : ∀ y, 1 ≤ ‖y‖ → g y = 0) (i0 i1 : Fin d)
    (hL : HessVLinfLoc (solF (fun y => (g y : ℂ)))) :
    ∃ M : ℝ, ∀ θ : E d → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → (∀ x, 0 ≤ θ x) →
      tsupport θ ⊆ Metric.closedBall 0 1 →
      |hessV (solF (fun y => (thConv θ g y : ℂ))) (0, 0, 0) i0 i1| ≤ M * ∫ x, θ x := by
  obtain ⟨H, -, hHb, hHid⟩ := hL
  set Kc : Set (Pt d) := Icc (-1) 1 ×ˢ (Metric.closedBall (0 : E d) 1 ×ˢ Metric.closedBall (0 : E d) 1)
  have hKc : IsCompact Kc :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨M, hM⟩ := hHb Kc hKc
  set M' := max M 0
  refine ⟨M', fun θ hθ hθc hθ0 hθs => ?_⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hθi : Integrable θ := hθ.continuous.integrable_of_hasCompactSupport hθc
  set f := solF (fun y => (g y : ℂ))
  set C := kinBd d K (∫ y, ‖(g y : ℂ)‖)
  have hfC : ∀ p, |f p| ≤ C := fun p => abs_solF_le hd (integrable_of_bound hgm hK hs).ofReal
    (fun y => by show ‖((g y : ℝ) : ℂ)‖ ≤ K; rw [Complex.norm_real, Real.norm_eq_abs]; exact hK y) p
  have hfm : StronglyMeasurable (fun q : E d × E d => f (0, q.1, q.2)) := by
    have := sm_kin (d := d) (Complex.measurable_ofReal.comp hgm)
    exact (Complex.continuous_re.comp_stronglyMeasurable this)
  -- the smoothed forcing and the smooth function `v ↦ 𝒮(θ̌⋆g)(0,v)`
  set h := thConv θ g
  have hh : ContDiff ℝ ∞ h := contDiff_thConv hθ hθc hgm hK hs
  have hhc : HasCompactSupport h := hasCompactSupport_thConv hθc hs
  have hsol : ContDiff ℝ ∞ (solF (fun y => (h y : ℂ))) := by
    rw [← coe_toS h hh hhc]; exact solF_smooth hd _
  set Fv : E d → ℝ := fun v => solF (fun y => (h y : ℂ)) (0, 0, v)
  have hFv : ContDiff ℝ ∞ Fv := hsol.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  set G : E d → ℝ := fun v => fderiv ℝ (fun z => fderiv ℝ Fv z (ev i1)) v (ev i0)
  have hG0 : hessV (solF (fun y => (h y : ℂ))) (0, 0, 0) i0 i1 = G 0 := rfl
  have hGc : Continuous G :=
    (((hFv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous_fderiv
      (by simp)).clm_apply continuous_const
  -- the time bump
  set a : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  set α : ℝ → ℝ := a.normed volume
  have hα : ContDiff ℝ ∞ α := a.contDiff_normed
  have hαi : ∫ t, α t = 1 := a.integral_normed
  have har : a.rOut = 1 / 2 := rfl
  have hαs : ∀ t, α t ≠ 0 → t ∈ Icc (-1 : ℝ) 1 := by
    intro t ht
    have : t ∈ Function.support α := ht
    rw [a.support_normed_eq, har] at this
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
    constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
  -- the bound for each velocity bump
  have key : ∀ (η : ℝ) (hη : 0 < η), η ≤ 1 →
      |∫ w, G w * (vbump (d := d) η hη).normed volume w| ≤ M' * ∫ x, θ x := by
    intro η hη hη1
    set b : ContDiffBump (0 : E d) := vbump η hη
    set ρ : E d → ℝ := b.normed volume
    have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
    have hρc : HasCompactSupport ρ := b.hasCompactSupport_normed
    have hρi : ∫ w, ρ w = 1 := b.integral_normed
    have hρ0 : ∀ w, 0 ≤ ρ w := fun w => b.nonneg_normed w
    have hbr : b.rOut = η := rfl
    have hρs : ∀ w, ρ w ≠ 0 → w ∈ Metric.closedBall (0 : E d) 1 := by
      intro w hw
      have : w ∈ Function.support ρ := hw
      rw [b.support_normed_eq, hbr] at this
      simp only [Metric.mem_ball, Metric.mem_closedBall] at this ⊢
      linarith
    -- the test function
    set φ : Pt d → ℝ := fun p => α p.1 * θ p.2.1 * ρ p.2.2
    have hφ : ContDiff ℝ ∞ φ :=
      ((hα.comp contDiff_fst).mul (hθ.comp (contDiff_fst.comp contDiff_snd))).mul
        (hρ.comp (contDiff_snd.comp contDiff_snd))
    have hαc : HasCompactSupport α := a.hasCompactSupport_normed
    have hφc : HasCompactSupport φ := by
      apply HasCompactSupport.intro (IsCompact.prod hαc (IsCompact.prod hθc hρc))
      intro p hp
      simp only [φ]
      rw [Set.mem_prod, Set.mem_prod, not_and_or, not_and_or] at hp
      rcases hp with h1 | h1 | h1
      · have h1' : α p.1 = 0 := image_eq_zero_of_notMem_tsupport h1
        rw [h1']; ring
      · have h1' : θ p.2.1 = 0 := image_eq_zero_of_notMem_tsupport h1
        rw [h1']; ring
      · have h1' : ρ p.2.2 = 0 := image_eq_zero_of_notMem_tsupport h1
        rw [h1']; ring
    have hφ0 : ∀ p, 0 ≤ φ p := fun p =>
      mul_nonneg (mul_nonneg (a.nonneg_normed _) (hθ0 _)) (hρ0 _)
    -- `D_v² φ`
    set D2ρ : E d → ℝ := fun v => fderiv ℝ (fun z => fderiv ℝ ρ z (ev i0)) v (ev i1)
    have hD2ρc : Continuous D2ρ :=
      (((hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous_fderiv
        (by simp)).clm_apply continuous_const
    have hD2ρi : Integrable D2ρ := hD2ρc.integrable_of_hasCompactSupport
      ((hρc.fderiv_apply ℝ (ev i0)).fderiv_apply ℝ (ev i1))
    have hessφ : ∀ p : Pt d, hessV φ p i1 i0 = α p.1 * θ p.2.1 * D2ρ p.2.2 := by
      rintro ⟨t, x, v⟩
      unfold hessV
      simp only [φ]
      have hdρ : Differentiable ℝ ρ := hρ.differentiable (by simp)
      have e1 : ∀ w, fderiv ℝ (fun w' => α t * θ x * ρ w') w (ev i0) =
          α t * θ x * fderiv ℝ ρ w (ev i0) := by
        intro w
        rw [fderiv_const_mul (hdρ w)]
        simp
      simp_rw [e1]
      have hdρ1 : Differentiable ℝ (fun w => fderiv ℝ ρ w (ev i0)) :=
        ((hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
      rw [fderiv_const_mul (hdρ1 v)]
      simp [D2ρ]
    -- left-hand side of the distributional identity
    have hΦi : Integrable (fun q : E d × E d => θ q.1 * f (0, q.1, q.2) * D2ρ q.2)
        (volume.prod volume) := by
      have hb : Integrable (fun q : E d × E d => |θ q.1| * C * |D2ρ q.2|) (volume.prod volume) := by
        have := (hθi.abs.mul_const C).mul_prod hD2ρi.abs
        simpa [mul_assoc] using this
      refine hb.mono' ?_ (Eventually.of_forall fun q => ?_)
      · exact ((hθ.continuous.comp continuous_fst).aestronglyMeasurable.mul
          hfm.aestronglyMeasurable).mul (hD2ρc.comp continuous_snd).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul]
        gcongr
        exact hfC _
    have hLHS : ∫ p, f p * hessV φ p i1 i0 = ∫ w, G w * ρ w := by
      simp_rw [hessφ]
      have e1 : (fun p : Pt d => f p * (α p.1 * θ p.2.1 * D2ρ p.2.2)) =
          fun p => α p.1 * (θ p.2.1 * f (0, p.2.1, p.2.2) * D2ρ p.2.2) := by
        funext p; simp only [f, solF]; ring
      rw [e1]
      have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (E d × E d)))
        α (fun q : E d × E d => θ q.1 * f (0, q.1, q.2) * D2ρ q.2)
      rw [show (volume : Measure (Pt d)) = (volume : Measure ℝ).prod (volume : Measure (E d × E d))
        from rfl, hpm, hαi, one_mul]
      rw [show (volume : Measure (E d × E d)) = (volume : Measure (E d)).prod (volume : Measure (E d))
        from rfl, integral_prod_symm _ hΦi]
      simp_rw [integral_mul_const]
      have e2 : ∀ v, ∫ x, θ x * f (0, x, v) = Fv v := fun v =>
        integral_theta_solF hd hθi hgm hK hs 0 v
      simp_rw [e2]
      exact ibp2_E hFv hρ hρc (ev i0) (ev i1)
    -- right-hand side
    have hφi : ∫ p, φ p = ∫ x, θ x := by
      have e : ∫ p, φ p = ∫ p : Pt d, α p.1 * (fun q : E d × E d => θ q.1 * ρ q.2) p.2 := by
        congr 1; funext p; simp only [φ]; ring
      rw [e]
      have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (E d × E d)))
        α (fun q : E d × E d => θ q.1 * ρ q.2)
      rw [show (volume : Measure (Pt d)) = (volume : Measure ℝ).prod (volume : Measure (E d × E d))
        from rfl, hpm, hαi, one_mul]
      have hpm2 := integral_prod_mul (μ := (volume : Measure (E d))) (ν := (volume : Measure (E d)))
        θ ρ
      rw [show (volume : Measure (E d × E d)) = (volume : Measure (E d)).prod (volume : Measure (E d))
        from rfl, hpm2, hρi, mul_one]
    have hRHS : |∫ p, H p i1 i0 * φ p| ≤ M' * ∫ x, θ x := by
      rw [← hφi, ← integral_const_mul]
      have hφI : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hφI.const_mul M')
      · filter_upwards [hM] with p hp
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 p)]
        by_cases hφp : φ p = 0
        · rw [hφp]; simp
        · have hmem : p ∈ Kc := by
            obtain ⟨t, x, v⟩ := p
            simp only [φ] at hφp
            have h1 : α t ≠ 0 := fun h => hφp (by rw [h]; ring)
            have h2 : θ x ≠ 0 := fun h => hφp (by rw [h]; ring)
            have h3 : ρ v ≠ 0 := fun h => hφp (by rw [h]; ring)
            exact ⟨hαs t h1, hθs (subset_tsupport θ h2), hρs v h3⟩
          have hle : |H p i1 i0| ≤ M' := ((abs_le_frob _ _ _).trans (hp hmem)).trans (le_max_left _ _)
          exact mul_le_mul_of_nonneg_right hle (hφ0 p)
    rw [← hLHS, hHid φ hφ hφc i1 i0]
    exact hRHS
  -- let the velocity bump concentrate
  rw [hG0]
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨η₀, hη₀, hcont⟩ := Metric.continuousAt_iff.mp hGc.continuousAt δ hδ
  set η := min (η₀ / 2) 1
  have hη : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  set b : ContDiffBump (0 : E d) := vbump η hη
  set ρ : E d → ℝ := b.normed volume
  have hρi : ∫ w, ρ w = 1 := b.integral_normed
  have hρ0 : ∀ w, 0 ≤ ρ w := fun w => b.nonneg_normed w
  have hρI : Integrable ρ := b.integrable_normed
  have hGρ : Integrable (fun w => G w * ρ w) :=
    (hGc.mul b.continuous_normed).integrable_of_hasCompactSupport b.hasCompactSupport_normed.mul_left
  have hbr : b.rOut = η := rfl
  have hdiff : |(∫ w, G w * ρ w) - G 0| ≤ δ := by
    have e : (∫ w, G w * ρ w) - G 0 = ∫ w, (G w - G 0) * ρ w := by
      have h1 : ∫ w, (G w - G 0) * ρ w = ∫ w, (G w * ρ w - G 0 * ρ w) := by
        congr 1; funext w; ring
      rw [h1, integral_sub hGρ (hρI.const_mul (G 0)), integral_const_mul, hρi, mul_one]
    rw [e]
    calc |∫ w, (G w - G 0) * ρ w| ≤ ∫ w, δ * ρ w := by
          refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
            (Eventually.of_forall fun w => abs_nonneg _) (hρI.const_mul δ)
            (Eventually.of_forall fun w => ?_))
          show |(G w - G 0) * ρ w| ≤ δ * ρ w
          rw [abs_mul, abs_of_nonneg (hρ0 w)]
          by_cases hw : ρ w = 0
          · rw [hw]; simp
          · have : w ∈ Function.support ρ := hw
            rw [b.support_normed_eq, hbr] at this
            have hwd : dist w 0 < η₀ := by
              have : dist w 0 < η := this
              linarith [min_le_left (η₀ / 2) 1]
            have := hcont hwd
            rw [Real.dist_eq] at this
            exact mul_le_mul_of_nonneg_right this.le (hρ0 w)
      _ = δ := by rw [integral_const_mul, hρi, mul_one]
  have hk := key η hη hη1
  have : |G 0| ≤ |∫ w, G w * ρ w| + δ := by
    have := abs_sub_abs_le_abs_sub (∫ w, G w * ρ w) (G 0)
    rw [abs_sub_comm] at hdiff
    have h2 := abs_sub_abs_le_abs_sub (G 0) (∫ w, G w * ρ w)
    linarith
  linarith

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Criterion

-- ============================================================================
-- KineticCounterexamples/Endpoint/UFun.lean
-- ============================================================================

section File_Endpoint_UFun

/-!
# The function `u = η(x) x₁x₂ (-log|x|)^{1/2}` of Theorem 4.3 and its regularizations

With `q = |x|²` we write `(-log|x|)^{1/2} = ψ(q)`, `ψ(p) = √(-(1/2) log p)`, and
`η(x) = β(|x|²)` with a smooth `β`, `β = 1` on `(-∞, 1/64]`, `β = 0` on `[1/20, ∞)` (so
`η ∈ C_c^∞(B_{1/4})`, `η = 1` on `B_{1/8}`, `0 ≤ η ≤ 1`). The regularizations are
`U_c(x) = x₁x₂ Φ_c(|x|²)`, `Φ_c(q) = β(q) ψ(q + c)`, `c ≥ 0`; `U_0 = u`.

This file contains the one-variable calculus.
-/

noncomputable section

open Real Filter Topology Set
open scoped ContDiff

namespace KS

/-! ### `ψ(p) = √(-(1/2) log p)` -/

def psi (p : ℝ) : ℝ := √(-(1 / 2) * Real.log p)
def psi1 (p : ℝ) : ℝ := -1 / (4 * p * psi p)
def psi2 (p : ℝ) : ℝ := 1 / (4 * p ^ 2 * psi p) - 1 / (16 * p ^ 2 * psi p ^ 3)

lemma psi_arg_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < -(1 / 2) * Real.log p := by
  have := Real.log_neg hp hp1
  linarith

lemma psi_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < psi p :=
  Real.sqrt_pos.mpr (psi_arg_pos hp hp1)

lemma psi_sq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : psi p ^ 2 = -(1 / 2) * Real.log p :=
  Real.sq_sqrt (psi_arg_pos hp hp1).le

lemma hasDerivAt_psi {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : HasDerivAt psi (psi1 p) p := by
  have h1 : HasDerivAt (fun p => -(1 / 2) * Real.log p) (-(1 / 2) * p⁻¹) p :=
    (Real.hasDerivAt_log hp.ne').const_mul _
  have h2 := h1.sqrt (psi_arg_pos hp hp1).ne'
  have hψ := psi_pos hp hp1
  have e : psi1 p = -(1 / 2) * p⁻¹ / (2 * psi p) := by
    unfold psi1; field_simp; ring
  rw [e]; exact h2

lemma hasDerivAt_psi1 {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : HasDerivAt psi1 (psi2 p) p := by
  have hψ := psi_pos hp hp1
  have h1 : HasDerivAt (fun p => 4 * p * psi p) (4 * psi p + 4 * p * psi1 p) p := by
    have h0 : HasDerivAt (fun p : ℝ => 4 * p) 4 p := by
      simpa using (hasDerivAt_id p).const_mul (4 : ℝ)
    exact h0.mul (hasDerivAt_psi hp hp1)
  have h2 : HasDerivAt psi1
      ((0 * (4 * p * psi p) - -1 * (4 * psi p + 4 * p * psi1 p)) / (4 * p * psi p) ^ 2) p :=
    (hasDerivAt_const p (-1 : ℝ)).div h1 (by positivity)
  have e : psi2 p = (0 * (4 * p * psi p) - -1 * (4 * psi p + 4 * p * psi1 p)) /
      (4 * p * psi p) ^ 2 := by
    unfold psi2 psi1
    field_simp
    ring
  rw [e]; exact h2

lemma psi_antitone {p p' : ℝ} (hp : 0 < p) (hpp' : p ≤ p') : psi p' ≤ psi p := by
  unfold psi
  apply Real.sqrt_le_sqrt
  have := Real.log_le_log hp hpp'
  linarith

lemma continuousAt_psi {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : ContinuousAt psi p :=
  (hasDerivAt_psi hp hp1).continuousAt

lemma continuousAt_psi1 {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : ContinuousAt psi1 p :=
  (hasDerivAt_psi1 hp hp1).continuousAt

lemma continuousAt_psi2 {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : ContinuousAt psi2 p := by
  have hψ := psi_pos hp hp1
  have hc := continuousAt_psi hp hp1
  have ha : ContinuousAt (fun q : ℝ => 4 * q ^ 2 * psi q) p :=
    (continuousAt_const.mul (continuousAt_id.pow 2)).mul hc
  have hb : ContinuousAt (fun q : ℝ => 16 * q ^ 2 * psi q ^ 3) p :=
    (continuousAt_const.mul (continuousAt_id.pow 2)).mul (hc.pow 3)
  show ContinuousAt (fun q => 1 / (4 * q ^ 2 * psi q) - 1 / (16 * q ^ 2 * psi q ^ 3)) p
  exact (continuousAt_const.div ha (by positivity)).sub (continuousAt_const.div hb (by positivity))

/-- `ψ ≥ 1` for `p ≤ e^{-2}`, in particular for `p ≤ 1/8`. -/
lemma one_le_psi {p : ℝ} (hp : 0 < p) (hp8 : p ≤ 1 / 8) : 1 ≤ psi p := by
  unfold psi
  rw [Real.one_le_sqrt]
  have h1 : Real.log p ≤ Real.log (1 / 8) := Real.log_le_log hp hp8
  have h2 : Real.log (1 / 8) = -Real.log 8 := by rw [one_div, Real.log_inv]
  have h3 : (2 : ℝ) < Real.log 8 := by
    have : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [this, Real.log_pow]
    have := Real.log_two_gt_d9
    push_cast
    linarith
  linarith

/-! ### The cutoff `β` -/

def beta (q : ℝ) : ℝ := Real.smoothTransition ((1 / 20 - q) / (1 / 20 - 1 / 64))

lemma contDiff_beta : ContDiff ℝ ∞ beta := by
  unfold beta
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.sub contDiff_id).div_const _)

lemma beta_eq_one {q : ℝ} (hq : q ≤ 1 / 64) : beta q = 1 := by
  unfold beta
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

lemma beta_eq_zero {q : ℝ} (hq : 1 / 20 ≤ q) : beta q = 0 := by
  unfold beta
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

lemma beta_nonneg (q : ℝ) : 0 ≤ beta q := Real.smoothTransition.nonneg _
lemma beta_le_one (q : ℝ) : beta q ≤ 1 := Real.smoothTransition.le_one _

def beta1 (q : ℝ) : ℝ := deriv beta q
def beta2 (q : ℝ) : ℝ := deriv beta1 q

lemma contDiff_beta1 : ContDiff ℝ ∞ beta1 :=
  (contDiff_infty_iff_deriv.mp contDiff_beta).2

lemma hasDerivAt_beta (q : ℝ) : HasDerivAt beta (beta1 q) q :=
  ((contDiff_beta.differentiable (by simp)) q).hasDerivAt

lemma hasDerivAt_beta1 (q : ℝ) : HasDerivAt beta1 (beta2 q) q :=
  ((contDiff_beta1.differentiable (by simp)) q).hasDerivAt

lemma continuous_beta2 : Continuous beta2 := by
  have : ContDiff ℝ ∞ beta2 := (contDiff_infty_iff_deriv.mp contDiff_beta1).2
  exact this.continuous

lemma beta1_eq_zero_of_le {q : ℝ} (hq : q < 1 / 64) : beta1 q = 0 := by
  unfold beta1
  have : beta =ᶠ[𝓝 q] fun _ => 1 := by
    filter_upwards [Iio_mem_nhds hq] with q' hq'
    exact beta_eq_one (le_of_lt hq')
  rw [this.deriv_eq]; simp

lemma beta1_eq_zero_of_ge {q : ℝ} (hq : 1 / 20 < q) : beta1 q = 0 := by
  unfold beta1
  have : beta =ᶠ[𝓝 q] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hq] with q' hq'
    exact beta_eq_zero (le_of_lt hq')
  rw [this.deriv_eq]; simp

lemma beta1_eq_zero {q : ℝ} (hq : q ≤ 1 / 64 ∨ 1 / 20 ≤ q) : beta1 q = 0 := by
  have hc : Continuous beta1 := contDiff_beta1.continuous
  rcases hq with h | h
  · rcases lt_or_eq_of_le h with h' | h'
    · exact beta1_eq_zero_of_le h'
    · -- the boundary point by continuity
      have : Tendsto beta1 (𝓝[<] q) (𝓝 0) := by
        apply tendsto_nhdsWithin_congr (f := fun _ => (0 : ℝ))
        · intro x hx; exact (beta1_eq_zero_of_le (by rw [← h']; exact hx)).symm
        · exact tendsto_const_nhds
      exact tendsto_nhds_unique (hc.continuousWithinAt.tendsto) this
  · rcases lt_or_eq_of_le h with h' | h'
    · exact beta1_eq_zero_of_ge h'
    · have : Tendsto beta1 (𝓝[>] q) (𝓝 0) := by
        apply tendsto_nhdsWithin_congr (f := fun _ => (0 : ℝ))
        · intro x hx; exact (beta1_eq_zero_of_ge (by rw [h']; exact hx)).symm
        · exact tendsto_const_nhds
      exact tendsto_nhds_unique (hc.continuousWithinAt.tendsto) this

lemma beta2_eq_zero {q : ℝ} (hq : q < 1 / 64 ∨ 1 / 20 < q) : beta2 q = 0 := by
  unfold beta2
  rcases hq with h | h
  · have : beta1 =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with q' hq'
      exact beta1_eq_zero (Or.inl (le_of_lt hq'))
    rw [this.deriv_eq]; simp
  · have : beta1 =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h] with q' hq'
      exact beta1_eq_zero (Or.inr (le_of_lt hq'))
    rw [this.deriv_eq]; simp

lemma beta2_eq_zero' {q : ℝ} (hq : q ≤ 1 / 64 ∨ 1 / 20 ≤ q) : beta2 q = 0 := by
  rcases hq with h | h
  · rcases lt_or_eq_of_le h with h' | h'
    · exact beta2_eq_zero (Or.inl h')
    · have : Tendsto beta2 (𝓝[<] q) (𝓝 0) := by
        apply tendsto_nhdsWithin_congr (f := fun _ => (0 : ℝ))
        · intro x hx; exact (beta2_eq_zero (Or.inl (by rw [← h']; exact hx))).symm
        · exact tendsto_const_nhds
      exact tendsto_nhds_unique (continuous_beta2.continuousWithinAt.tendsto) this
  · rcases lt_or_eq_of_le h with h' | h'
    · exact beta2_eq_zero (Or.inr h')
    · have : Tendsto beta2 (𝓝[>] q) (𝓝 0) := by
        apply tendsto_nhdsWithin_congr (f := fun _ => (0 : ℝ))
        · intro x hx; exact (beta2_eq_zero (Or.inr (by rw [h']; exact hx))).symm
        · exact tendsto_const_nhds
      exact tendsto_nhds_unique (continuous_beta2.continuousWithinAt.tendsto) this

lemma exists_bound_beta12 : ∃ B : ℝ, 0 ≤ B ∧ ∀ q, |beta1 q| ≤ B ∧ |beta2 q| ≤ B := by
  have hc1 : Continuous beta1 := contDiff_beta1.continuous
  have hs : ∀ q, q ∉ Icc (1 / 64 : ℝ) (1 / 20) → beta1 q = 0 ∧ beta2 q = 0 := by
    intro q hq
    simp only [mem_Icc, not_and_or, not_le] at hq
    rcases hq with h | h
    · exact ⟨beta1_eq_zero (Or.inl h.le), beta2_eq_zero' (Or.inl h.le)⟩
    · exact ⟨beta1_eq_zero (Or.inr h.le), beta2_eq_zero' (Or.inr h.le)⟩
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (1 / 64 : ℝ)) (b := 1 / 20)).exists_bound_of_continuousOn
    hc1.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_Icc (a := (1 / 64 : ℝ)) (b := 1 / 20)).exists_bound_of_continuousOn
    continuous_beta2.continuousOn
  refine ⟨max (max B1 B2) 0, le_max_right _ _, fun q => ?_⟩
  by_cases hq : q ∈ Icc (1 / 64 : ℝ) (1 / 20)
  · have h1 := hB1 q hq
    have h2 := hB2 q hq
    rw [Real.norm_eq_abs] at h1 h2
    exact ⟨h1.trans ((le_max_left _ _).trans (le_max_left _ _)),
      h2.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · obtain ⟨h1, h2⟩ := hs q hq
    rw [h1, h2, abs_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_UFun

-- ============================================================================
-- KineticCounterexamples/Endpoint/UDeriv.lean
-- ============================================================================

section File_Endpoint_UDeriv

/-!
# The regularizations `U_c(x) = x_{i₀} x_{i₁} Φ_c(|x|²)` and their derivatives

`Φ_c(q) = β(q) ψ(q + c)`. For `0 < c < 1/2` the function `U_c` is smooth with compact support,
and we compute its first and second derivatives, its Laplacian
`ΔU_c = x_{i₀}x_{i₁} ((8 + 2d) Φ_c' + 4|x|² Φ_c'')` and its mixed derivative
`∂_{i₀}∂_{i₁} U_c = Φ_c + 2(x_{i₀}² + x_{i₁}²) Φ_c' + 4 x_{i₀}² x_{i₁}² Φ_c''`.
-/

noncomputable section

open Real Filter Topology Set MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace KS

variable {d : ℕ}

/-! ### `Φ_c` and its derivatives -/

def Phi (c q : ℝ) : ℝ := beta q * psi (q + c)
def Phi1 (c q : ℝ) : ℝ := beta1 q * psi (q + c) + beta q * psi1 (q + c)
def Phi2 (c q : ℝ) : ℝ :=
  beta2 q * psi (q + c) + 2 * (beta1 q * psi1 (q + c)) + beta q * psi2 (q + c)

lemma beta_eventually_zero {q : ℝ} (hq : 1 / 20 < q) : beta =ᶠ[𝓝 q] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds hq] with q' hq'
  exact beta_eq_zero (le_of_lt hq')

lemma beta1_eventually_zero {q : ℝ} (hq : 1 / 20 < q) : beta1 =ᶠ[𝓝 q] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds hq] with q' hq'
  exact beta1_eq_zero (Or.inr (le_of_lt hq'))

lemma Phi_eq_zero {c q : ℝ} (hq : 1 / 20 ≤ q) : Phi c q = 0 := by
  simp [Phi, beta_eq_zero hq]

lemma Phi1_eq_zero {c q : ℝ} (hq : 1 / 20 ≤ q) : Phi1 c q = 0 := by
  simp [Phi1, beta_eq_zero hq, beta1_eq_zero (Or.inr hq)]

lemma Phi2_eq_zero {c q : ℝ} (hq : 1 / 20 ≤ q) : Phi2 c q = 0 := by
  simp [Phi2, beta_eq_zero hq, beta1_eq_zero (Or.inr hq), beta2_eq_zero' (Or.inr hq)]

lemma Phi_eventually_zero {c q : ℝ} (hq : 1 / 20 < q) : Phi c =ᶠ[𝓝 q] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds hq] with q' hq'
  exact Phi_eq_zero (le_of_lt hq')

lemma Phi1_eventually_zero {c q : ℝ} (hq : 1 / 20 < q) : Phi1 c =ᶠ[𝓝 q] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds hq] with q' hq'
  exact Phi1_eq_zero (le_of_lt hq')

lemma hasDerivAt_Phi {c q : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hq : 0 ≤ q) :
    HasDerivAt (Phi c) (Phi1 c q) q := by
  rcases lt_or_ge q (1 / 2) with h | h
  · have h0 : 0 < q + c := by linarith
    have h1 : q + c < 1 := by linarith
    have hψ : HasDerivAt (fun q => psi (q + c)) (psi1 (q + c)) q :=
      HasDerivAt.comp_add_const q c (hasDerivAt_psi h0 h1)
    exact (hasDerivAt_beta q).mul hψ
  · have hq' : 1 / 20 < q := by linarith
    rw [Phi1_eq_zero hq'.le]
    exact (hasDerivAt_const q (0 : ℝ)).congr_of_eventuallyEq (Phi_eventually_zero hq')

lemma hasDerivAt_Phi1 {c q : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hq : 0 ≤ q) :
    HasDerivAt (Phi1 c) (Phi2 c q) q := by
  rcases lt_or_ge q (1 / 2) with h | h
  · have h0 : 0 < q + c := by linarith
    have h1 : q + c < 1 := by linarith
    have hψ : HasDerivAt (fun q => psi (q + c)) (psi1 (q + c)) q :=
      HasDerivAt.comp_add_const q c (hasDerivAt_psi h0 h1)
    have hψ1 : HasDerivAt (fun q => psi1 (q + c)) (psi2 (q + c)) q :=
      HasDerivAt.comp_add_const q c (hasDerivAt_psi1 h0 h1)
    have key : HasDerivAt (fun q => beta1 q * psi (q + c) + beta q * psi1 (q + c))
        (beta2 q * psi (q + c) + beta1 q * psi1 (q + c) +
          (beta1 q * psi1 (q + c) + beta q * psi2 (q + c))) q :=
      ((hasDerivAt_beta1 q).mul hψ).add ((hasDerivAt_beta q).mul hψ1)
    have e : Phi2 c q = beta2 q * psi (q + c) + beta1 q * psi1 (q + c) +
        (beta1 q * psi1 (q + c) + beta q * psi2 (q + c)) := by
      unfold Phi2; ring
    rw [e]; exact key
  · have hq' : 1 / 20 < q := by linarith
    rw [Phi2_eq_zero hq'.le]
    exact (hasDerivAt_const q (0 : ℝ)).congr_of_eventuallyEq (Phi1_eventually_zero hq')

lemma contDiffAt_psi {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : ContDiffAt ℝ ∞ psi p := by
  show ContDiffAt ℝ ∞ (fun p => √(-(1 / 2) * Real.log p)) p
  have hl : ContDiffAt ℝ ∞ Real.log p := Real.contDiffAt_log.mpr hp.ne'
  exact (contDiffAt_const.mul hl).sqrt (psi_arg_pos hp hp1).ne'

lemma contDiffAt_Phi {c q : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hq : 0 ≤ q) :
    ContDiffAt ℝ ∞ (Phi c) q := by
  rcases lt_or_ge q (1 / 2) with h | h
  · have h0 : 0 < q + c := by linarith
    have h1 : q + c < 1 := by linarith
    have hψ : ContDiffAt ℝ ∞ (psi ∘ fun q => q + c) q :=
      ContDiffAt.comp (g := psi) q (contDiffAt_psi h0 h1) (contDiffAt_id.add contDiffAt_const)
    exact contDiff_beta.contDiffAt.mul hψ
  · have hq' : 1 / 20 < q := by linarith
    exact contDiffAt_const.congr_of_eventuallyEq (Phi_eventually_zero hq')

/-! ### Calculus for `W(x) = x_{i₀} x_{i₁} Φ(|x|²)` -/

lemma ev_coord (i j : Fin d) : (ev i : E d) j = if j = i then 1 else 0 := by
  simp [ev, PiLp.single_apply]

lemma inner_ev' (ξ : E d) (i : Fin d) : ⟪ξ, ev i⟫ = ξ i := by
  simp [ev, EuclideanSpace.inner_single_right]

lemma inner_ev_ev' (i j : Fin d) : ⟪(ev j : E d), ev i⟫ = if i = j then 1 else 0 := by
  rw [inner_ev', ev_coord]

lemma hasFDerivAt_coordE (i : Fin d) (x : E d) :
    HasFDerivAt (fun z : E d => z i) (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).hasFDerivAt

lemma hasFDerivAt_nsq (x : E d) :
    HasFDerivAt (fun z : E d => ‖z‖ ^ 2) (2 • innerSL ℝ x) x :=
  (hasStrictFDerivAt_norm_sq x).hasFDerivAt

lemma hasFDerivAt_inner_right' (m y : E d) :
    HasFDerivAt (fun z : E d => ⟪z, m⟫) (innerSL ℝ m) y := by
  have := (innerSL ℝ m).hasFDerivAt (x := y)
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp [real_inner_comm]

variable (i0 i1 : Fin d)

/-- `W(x) = x_{i₀} x_{i₁} Φ(|x|²)`. -/
def Wf (Φ : ℝ → ℝ) (x : E d) : ℝ := x i0 * x i1 * Φ (‖x‖ ^ 2)

lemma fderiv_Wf_apply {Φ : ℝ → ℝ} {φ1 : ℝ} {x : E d} (h : HasDerivAt Φ φ1 (‖x‖ ^ 2))
    (m : E d) :
    fderiv ℝ (Wf i0 i1 Φ) x m =
      (m i0 * x i1 + x i0 * m i1) * Φ (‖x‖ ^ 2) + 2 * (x i0 * x i1) * φ1 * ⟪x, m⟫ := by
  have h0 := hasFDerivAt_coordE i0 x
  have h1 := hasFDerivAt_coordE i1 x
  have hΦ : HasFDerivAt (fun z : E d => Φ (‖z‖ ^ 2)) (φ1 • (2 • innerSL ℝ x)) x :=
    h.comp_hasFDerivAt x (hasFDerivAt_nsq x)
  have hW : HasFDerivAt (Wf i0 i1 Φ) _ x := (h0.mul h1).mul hΦ
  rw [hW.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply, PiLp.proj_apply, nsmul_eq_mul, Pi.mul_apply]
  push_cast
  ring

lemma differentiableAt_Wf {Φ : ℝ → ℝ} {φ1 : ℝ} {x : E d} (h : HasDerivAt Φ φ1 (‖x‖ ^ 2)) :
    DifferentiableAt ℝ (Wf i0 i1 Φ) x := by
  have h0 := hasFDerivAt_coordE i0 x
  have h1 := hasFDerivAt_coordE i1 x
  have hΦ : HasFDerivAt (fun z : E d => Φ (‖z‖ ^ 2)) (φ1 • (2 • innerSL ℝ x)) x :=
    h.comp_hasFDerivAt x (hasFDerivAt_nsq x)
  exact ((h0.mul h1).mul hΦ).differentiableAt

/-- The first derivative of `W` in the direction `m`, as a function of the base point. -/
def W1f (Φ Φ1 : ℝ → ℝ) (m : E d) (z : E d) : ℝ :=
  (m i0 * z i1 + z i0 * m i1) * Φ (‖z‖ ^ 2) + 2 * (z i0 * z i1) * Φ1 (‖z‖ ^ 2) * ⟪z, m⟫

lemma fderiv_Wf_eq {Φ Φ1 : ℝ → ℝ} (hΦ : ∀ q, 0 ≤ q → HasDerivAt Φ (Φ1 q) q) (m : E d) :
    (fun z => fderiv ℝ (Wf i0 i1 Φ) z m) = W1f i0 i1 Φ Φ1 m := by
  funext z
  exact fderiv_Wf_apply i0 i1 (hΦ _ (sq_nonneg _)) m

lemma fderiv2_Wf_apply {Φ Φ1 Φ2 : ℝ → ℝ} (hΦ : ∀ q, 0 ≤ q → HasDerivAt Φ (Φ1 q) q)
    (hΦ1 : ∀ q, 0 ≤ q → HasDerivAt Φ1 (Φ2 q) q) (x m m' : E d) :
    fderiv ℝ (fun z => fderiv ℝ (Wf i0 i1 Φ) z m) x m' =
      (m i0 * m' i1 + m' i0 * m i1) * Φ (‖x‖ ^ 2)
      + 2 * (m i0 * x i1 + x i0 * m i1) * Φ1 (‖x‖ ^ 2) * ⟪x, m'⟫
      + 2 * (m' i0 * x i1 + x i0 * m' i1) * Φ1 (‖x‖ ^ 2) * ⟪x, m⟫
      + 4 * (x i0 * x i1) * Φ2 (‖x‖ ^ 2) * ⟪x, m'⟫ * ⟪x, m⟫
      + 2 * (x i0 * x i1) * Φ1 (‖x‖ ^ 2) * ⟪m, m'⟫ := by
  rw [fderiv_Wf_eq i0 i1 hΦ m]
  have h0 := hasFDerivAt_coordE i0 x
  have h1 := hasFDerivAt_coordE i1 x
  have hq := hasFDerivAt_nsq x
  have hΦx : HasFDerivAt (fun z : E d => Φ (‖z‖ ^ 2)) (Φ1 (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x :=
    (hΦ _ (sq_nonneg _)).comp_hasFDerivAt x hq
  have hΦ1x : HasFDerivAt (fun z : E d => Φ1 (‖z‖ ^ 2)) (Φ2 (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x :=
    (hΦ1 _ (sq_nonneg _)).comp_hasFDerivAt x hq
  have hin := hasFDerivAt_inner_right' m x
  have hA : HasFDerivAt (fun z : E d => m i0 * z i1 + z i0 * m i1) _ x :=
    (h1.const_mul (m i0)).add (h0.mul_const (m i1))
  have hB : HasFDerivAt (fun z : E d => 2 * (z i0 * z i1)) _ x := (h0.mul h1).const_mul 2
  have hW : HasFDerivAt (W1f i0 i1 Φ Φ1 m) _ x := (hA.mul hΦx).add ((hB.mul hΦ1x).mul hin)
  rw [hW.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply, PiLp.proj_apply, nsmul_eq_mul, Pi.mul_apply]
  push_cast
  ring

lemma ev_self' (i : Fin d) : (ev i : E d) i = 1 := by rw [ev_coord, if_pos rfl]

/-- **The Laplacian of `W`.** -/
lemma lap_Wf {Φ Φ1 Φ2 : ℝ → ℝ} (hΦ : ∀ q, 0 ≤ q → HasDerivAt Φ (Φ1 q) q)
    (hΦ1 : ∀ q, 0 ≤ q → HasDerivAt Φ1 (Φ2 q) q) (hij : i0 ≠ i1) (x : E d) :
    ∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ (Wf i0 i1 Φ) z (ev i)) x (ev i) =
      x i0 * x i1 * ((8 + 2 * d) * Φ1 (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * Φ2 (‖x‖ ^ 2)) := by
  have e : ∀ i : Fin d, fderiv ℝ (fun z => fderiv ℝ (Wf i0 i1 Φ) z (ev i)) x (ev i) =
      2 * Φ (‖x‖ ^ 2) * ((ev i : E d) i0 * (ev i : E d) i1)
      + 4 * Φ1 (‖x‖ ^ 2) * x i1 * ((ev i : E d) i0 * x i)
      + 4 * Φ1 (‖x‖ ^ 2) * x i0 * ((ev i : E d) i1 * x i)
      + 4 * (x i0 * x i1) * Φ2 (‖x‖ ^ 2) * (x i * x i)
      + 2 * (x i0 * x i1) * Φ1 (‖x‖ ^ 2) := by
    intro i
    rw [fderiv2_Wf_apply i0 i1 hΦ hΦ1]
    have e1 : ⟪x, (ev i : E d)⟫ = x i := inner_ev' x i
    have e2 : ⟪(ev i : E d), (ev i : E d)⟫ = 1 := by rw [inner_ev', ev_self']
    rw [e1, e2]
    ring
  rw [Finset.sum_congr rfl (fun i _ => e i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have S1 : ∑ i : Fin d, (ev i : E d) i0 * (ev i : E d) i1 = 0 := by
    simp [ev_coord, Ne.symm hij, hij]
  have S2 : ∑ i : Fin d, (ev i : E d) i0 * x i = x i0 := by simp [ev_coord]
  have S3 : ∑ i : Fin d, (ev i : E d) i1 * x i = x i1 := by simp [ev_coord]
  have S4 : ∑ i : Fin d, x i * x i = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; congr 1; funext i; ring
  rw [S1, S2, S3, S4, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The mixed derivative of `W`.** -/
lemma mixed_Wf {Φ Φ1 Φ2 : ℝ → ℝ} (hΦ : ∀ q, 0 ≤ q → HasDerivAt Φ (Φ1 q) q)
    (hΦ1 : ∀ q, 0 ≤ q → HasDerivAt Φ1 (Φ2 q) q) (hij : i0 ≠ i1) (x : E d) :
    fderiv ℝ (fun z => fderiv ℝ (Wf i0 i1 Φ) z (ev i0)) x (ev i1) =
      Φ (‖x‖ ^ 2) + 2 * (x i0 ^ 2 + x i1 ^ 2) * Φ1 (‖x‖ ^ 2) +
        4 * (x i0 ^ 2 * x i1 ^ 2) * Φ2 (‖x‖ ^ 2) := by
  rw [fderiv2_Wf_apply i0 i1 hΦ hΦ1]
  have a1 : (ev i0 : E d) i1 = 0 := by rw [ev_coord, if_neg (Ne.symm hij)]
  have a2 : (ev i1 : E d) i0 = 0 := by rw [ev_coord, if_neg hij]
  have b1 : ⟪x, (ev i0 : E d)⟫ = x i0 := inner_ev' x i0
  have b2 : ⟪x, (ev i1 : E d)⟫ = x i1 := inner_ev' x i1
  have b3 : ⟪(ev i0 : E d), (ev i1 : E d)⟫ = 0 := by rw [inner_ev', a1]
  rw [ev_self', ev_self', a1, a2, b1, b2, b3]
  ring

/-! ### `U_c` -/

/-- `U_c = W` with `Φ = Φ_c`. -/
abbrev U (c : ℝ) : E d → ℝ := Wf i0 i1 (Phi c)

/-- The forcing `g_c = ΔU_c`. -/
def gU (c : ℝ) (x : E d) : ℝ :=
  x i0 * x i1 * ((8 + 2 * d) * Phi1 c (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * Phi2 c (‖x‖ ^ 2))

lemma contDiff_U {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) : ContDiff ℝ ∞ (U i0 i1 c) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h0 : ContDiffAt ℝ ∞ (fun z : E d => z i0) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i0).contDiff.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun z : E d => z i1) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i1).contDiff.contDiffAt
  have hq : ContDiffAt ℝ ∞ (fun z : E d => ‖z‖ ^ 2) x := (contDiff_norm_sq ℝ).contDiffAt
  have hΦ : ContDiffAt ℝ ∞ ((Phi c) ∘ fun z : E d => ‖z‖ ^ 2) x :=
    ContDiffAt.comp (g := Phi c) x (contDiffAt_Phi hc hc2 (sq_nonneg _)) hq
  exact (h0.mul h1).mul hΦ

lemma sq_le_of_quarter {x : E d} (hx : 1 / 4 ≤ ‖x‖) : 1 / 20 ≤ ‖x‖ ^ 2 := by nlinarith

lemma U_eq_zero {c : ℝ} {x : E d} (hx : 1 / 20 ≤ ‖x‖ ^ 2) : U i0 i1 c x = 0 := by
  simp [U, Wf, Phi_eq_zero hx]

lemma gU_eq_zero {c : ℝ} {x : E d} (hx : 1 / 20 ≤ ‖x‖ ^ 2) : gU i0 i1 c x = 0 := by
  simp [gU, Phi1_eq_zero hx, Phi2_eq_zero hx]

lemma hasCompactSupport_U (c : ℝ) : HasCompactSupport (U i0 i1 c) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E d) (1 / 4))
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact U_eq_zero i0 i1 (sq_le_of_quarter hx.le)

lemma hasCompactSupport_gU (c : ℝ) : HasCompactSupport (gU i0 i1 c) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E d) (1 / 4))
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact gU_eq_zero i0 i1 (sq_le_of_quarter hx.le)

lemma lap_U {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hij : i0 ≠ i1) (x : E d) :
    ∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ (U i0 i1 c) z (ev i)) x (ev i) = gU i0 i1 c x :=
  lap_Wf i0 i1 (fun q hq => hasDerivAt_Phi hc hc2 hq) (fun q hq => hasDerivAt_Phi1 hc hc2 hq) hij x

lemma mixed_U {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hij : i0 ≠ i1) (x : E d) :
    fderiv ℝ (fun z => fderiv ℝ (U i0 i1 c) z (ev i0)) x (ev i1) =
      Phi c (‖x‖ ^ 2) + 2 * (x i0 ^ 2 + x i1 ^ 2) * Phi1 c (‖x‖ ^ 2) +
        4 * (x i0 ^ 2 * x i1 ^ 2) * Phi2 c (‖x‖ ^ 2) :=
  mixed_Wf i0 i1 (fun q hq => hasDerivAt_Phi hc hc2 hq) (fun q hq => hasDerivAt_Phi1 hc hc2 hq) hij x

lemma contDiff_d2 {F : E d → ℝ} (hF : ContDiff ℝ ∞ F) (m m' : E d) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ (fun z => fderiv ℝ F z m) x m') := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ F z m) :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact (h1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma contDiff_gU {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hij : i0 ≠ i1) :
    ContDiff ℝ ∞ (gU i0 i1 c) := by
  have e : gU i0 i1 c = fun x =>
      ∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ (U i0 i1 c) z (ev i)) x (ev i) := by
    funext x; rw [lap_U i0 i1 hc hc2 hij]
  rw [e]
  exact ContDiff.sum fun i _ => contDiff_d2 (contDiff_U i0 i1 hc hc2) _ _

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_UDeriv

-- ============================================================================
-- KineticCounterexamples/Endpoint/UBounds.lean
-- ============================================================================

section File_Endpoint_UBounds

/-!
# Uniform bounds and limits for `U_c` and `g_c = ΔU_c`

* `|g_c| ≤ C` uniformly in `0 ≤ c ≤ 1/20` and `|U_c| ≤ 1`;
* `∂_{i₀}∂_{i₁} U_c(x) ≥ ψ(|x|² + c)/2` when `|x|² + c ≤ 1/64`;
* `U_c → U_0 = u` and `g_c → g_0 = g` pointwise as `c → 0`;
* `g = g_0` is continuous (it vanishes like `1/ψ(|x|²)` at the origin).
-/

noncomputable section

open Real Filter Topology Set MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace KS

variable {d : ℕ}

/-! ### Bounds for `ψ`, `ψ'`, `ψ''` -/

lemma psi_nonneg (p : ℝ) : 0 ≤ psi p := Real.sqrt_nonneg _

lemma mul_abs_psi1_le {p : ℝ} (hp : 0 < p) (hp8 : p ≤ 1 / 8) : p * |psi1 p| ≤ 1 / 4 := by
  have hψ := one_le_psi hp hp8
  have hpos : 0 < 4 * p * psi p := by positivity
  unfold psi1
  rw [abs_div, abs_neg, abs_one, abs_of_pos hpos, mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

lemma psi_mul_abs_psi1 {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : psi p * (p * |psi1 p|) = 1 / 4 := by
  have hψ := psi_pos hp hp1
  have hpos : 0 < 4 * p * psi p := by positivity
  unfold psi1
  rw [abs_div, abs_neg, abs_one, abs_of_pos hpos]
  field_simp

lemma psi2_nonneg {p : ℝ} (hp : 0 < p) (hp8 : p ≤ 1 / 8) : 0 ≤ psi2 p := by
  have hψ := one_le_psi hp hp8
  unfold psi2
  have hp2 : 0 < p ^ 2 := by positivity
  have h1 : 1 / (16 * p ^ 2 * psi p ^ 3) ≤ 1 / (4 * p ^ 2 * psi p) := by
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    have h3 : 0 ≤ 16 * psi p ^ 3 - 4 * psi p := by
      have hψ2 : 1 ≤ psi p ^ 2 := by nlinarith
      have e : 16 * psi p ^ 3 - 4 * psi p = 4 * psi p * (4 * psi p ^ 2 - 1) := by ring
      rw [e]
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg hp2.le h3]
  linarith

lemma psi2_le {p : ℝ} : psi2 p ≤ 1 / (4 * p ^ 2 * psi p) := by
  unfold psi2
  have : 0 ≤ 1 / (16 * p ^ 2 * psi p ^ 3) := by have := psi_nonneg p; positivity
  linarith

lemma sq_mul_abs_psi2_le {p : ℝ} (hp : 0 < p) (hp8 : p ≤ 1 / 8) : p ^ 2 * |psi2 p| ≤ 1 / 4 := by
  have hψ := one_le_psi hp hp8
  rw [abs_of_nonneg (psi2_nonneg hp hp8)]
  have h := psi2_le (p := p)
  have hpos : 0 < 4 * p ^ 2 * psi p := by positivity
  have h2 : p ^ 2 * (1 / (4 * p ^ 2 * psi p)) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
    nlinarith [sq_nonneg p]
  calc p ^ 2 * psi2 p ≤ p ^ 2 * (1 / (4 * p ^ 2 * psi p)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg p)
    _ ≤ 1 / 4 := h2

lemma psi_sq_mul_psi2_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    psi p * (p ^ 2 * psi2 p) ≤ 1 / 4 := by
  have hψ := psi_pos hp hp1
  have h := psi2_le (p := p)
  have e : psi p * (p ^ 2 * (1 / (4 * p ^ 2 * psi p))) = 1 / 4 := by field_simp
  calc psi p * (p ^ 2 * psi2 p) ≤ psi p * (p ^ 2 * (1 / (4 * p ^ 2 * psi p))) := by
        apply mul_le_mul_of_nonneg_left _ hψ.le
        exact mul_le_mul_of_nonneg_left h (sq_nonneg p)
    _ = 1 / 4 := e

lemma mul_psi_le_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : p * psi p ≤ 1 := by
  have hsq := psi_sq hp hp1
  have hlog : -Real.log p ≤ 1 / p := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at this
    rw [one_div]; linarith
  have h2 : (p * psi p) ^ 2 ≤ 1 := by
    rw [mul_pow, hsq]
    have e : p ^ 2 * (-(1 / 2) * Real.log p) = (p ^ 2 / 2) * (-Real.log p) := by ring
    rw [e]
    calc (p ^ 2 / 2) * (-Real.log p) ≤ (p ^ 2 / 2) * (1 / p) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = p / 2 := by field_simp
      _ ≤ 1 := by linarith
  have h0 : 0 ≤ p * psi p := mul_nonneg hp.le (psi_nonneg p)
  nlinarith

lemma le_psi_of_le_exp {p K : ℝ} (hp : 0 < p) (hK : 0 ≤ K) (hpK : p ≤ Real.exp (-2 * K ^ 2)) :
    K ≤ psi p := by
  have hlog : Real.log p ≤ -2 * K ^ 2 := by
    have := Real.log_le_log hp hpK
    rwa [Real.log_exp] at this
  unfold psi
  calc K = √(K ^ 2) := (Real.sqrt_sq hK).symm
    _ ≤ √(-(1 / 2) * Real.log p) := Real.sqrt_le_sqrt (by linarith)

lemma psi_sq_eps {ε : ℝ} (hε : 0 < ε) : psi (ε ^ 2) = √(Real.log (1 / ε)) := by
  unfold psi
  congr 1
  rw [Real.log_pow, Real.log_div one_ne_zero hε.ne', Real.log_one]
  push_cast
  ring

/-! ### Coordinates -/

variable (i0 i1 : Fin d)

lemma coord_sq_add_le (hij : i0 ≠ i1) (x : E d) : x i0 ^ 2 + x i1 ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => x i ^ 2)
    (Finset.subset_univ {i0, i1}) (fun i _ _ => sq_nonneg _)
  rw [Finset.sum_pair hij] at this
  exact this

lemma abs_coord_mul_le (hij : i0 ≠ i1) (x : E d) : |x i0 * x i1| ≤ ‖x‖ ^ 2 / 2 := by
  have h := coord_sq_add_le i0 i1 hij x
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i0 + x i1), sq_nonneg (x i0 - x i1)]

lemma coord_mul_eq_zero (hij : i0 ≠ i1) {x : E d} (hx : ‖x‖ ^ 2 = 0) : x i0 * x i1 = 0 := by
  have h := abs_coord_mul_le i0 i1 hij x
  rw [hx, zero_div] at h
  exact abs_nonpos_iff.mp h

/-! ### `|β'| ψ` and `|β''| ψ` -/

lemma beta12_psi_le {B : ℝ} (hB : ∀ q, |beta1 q| ≤ B ∧ |beta2 q| ≤ B) {q c : ℝ} (hc : 0 ≤ c) :
    |beta1 q| * psi (q + c) ≤ B * psi (1 / 64) ∧ |beta2 q| * psi (q + c) ≤ B * psi (1 / 64) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0).1
  rcases lt_or_ge q (1 / 64) with h | h
  · rw [beta1_eq_zero (Or.inl h.le), beta2_eq_zero' (Or.inl h.le), abs_zero, zero_mul]
    exact ⟨mul_nonneg hB0 (psi_nonneg _), mul_nonneg hB0 (psi_nonneg _)⟩
  · have hψ : psi (q + c) ≤ psi (1 / 64) := psi_antitone (by norm_num) (by linarith)
    exact ⟨mul_le_mul (hB q).1 hψ (psi_nonneg _) hB0, mul_le_mul (hB q).2 hψ (psi_nonneg _) hB0⟩

lemma abs_Phi1_le (c q : ℝ) : |Phi1 c q| ≤ |beta1 q| * psi (q + c) + |psi1 (q + c)| := by
  unfold Phi1
  have hb := beta_le_one q
  have hb0 := beta_nonneg q
  calc |beta1 q * psi (q + c) + beta q * psi1 (q + c)|
      ≤ |beta1 q * psi (q + c)| + |beta q * psi1 (q + c)| := abs_add_le _ _
    _ = |beta1 q| * psi (q + c) + beta q * |psi1 (q + c)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (psi_nonneg _), abs_of_nonneg hb0]
    _ ≤ |beta1 q| * psi (q + c) + |psi1 (q + c)| := by
        have := abs_nonneg (psi1 (q + c))
        nlinarith

lemma abs_Phi2_le (c q : ℝ) :
    |Phi2 c q| ≤ |beta2 q| * psi (q + c) + 2 * (|beta1 q| * |psi1 (q + c)|) + |psi2 (q + c)| := by
  unfold Phi2
  have hb := beta_le_one q
  have hb0 := beta_nonneg q
  calc |beta2 q * psi (q + c) + 2 * (beta1 q * psi1 (q + c)) + beta q * psi2 (q + c)|
      ≤ |beta2 q * psi (q + c)| + |2 * (beta1 q * psi1 (q + c))| + |beta q * psi2 (q + c)| :=
        abs_add_three _ _ _
    _ = |beta2 q| * psi (q + c) + 2 * (|beta1 q| * |psi1 (q + c)|) + beta q * |psi2 (q + c)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (psi_nonneg _), abs_of_nonneg hb0,
          abs_two]
    _ ≤ |beta2 q| * psi (q + c) + 2 * (|beta1 q| * |psi1 (q + c)|) + |psi2 (q + c)| := by
        have := abs_nonneg (psi2 (q + c))
        nlinarith

/-! ### The uniform bound for `g_c` -/

theorem exists_bound_gU (hij : i0 ≠ i1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c, 0 ≤ c → c ≤ 1 / 20 → ∀ x : E d, |gU i0 i1 c x| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_beta12
  set A := psi (1 / 64)
  have hA : 0 ≤ A := psi_nonneg _
  refine ⟨(8 + 2 * d) * (B * A + 1) + (B * A + B + 1), by positivity, fun c hc hc' x => ?_⟩
  have hC0 : 0 ≤ (8 + 2 * d) * (B * A + 1) + (B * A + B + 1) := by positivity
  set q := ‖x‖ ^ 2 with hqdef
  have hq0 : 0 ≤ q := sq_nonneg _
  rcases le_or_gt (1 / 20) q with hq | hq
  · rw [gU_eq_zero i0 i1 hq, abs_zero]; exact hC0
  rcases eq_or_lt_of_le hq0 with hq00 | hqpos
  · have hx : x i0 * x i1 = 0 := coord_mul_eq_zero i0 i1 hij hq00.symm
    simp only [gU, hx, zero_mul, abs_zero]
    exact hC0
  set p := q + c with hpdef
  have hp : 0 < p := by linarith
  have hp8 : p ≤ 1 / 8 := by linarith
  have hqp : q ≤ p := by linarith
  have hxy : |x i0 * x i1| ≤ q / 2 := abs_coord_mul_le i0 i1 hij x
  have hψ1 : p * |psi1 p| ≤ 1 / 4 := mul_abs_psi1_le hp hp8
  have hψ2 : p ^ 2 * |psi2 p| ≤ 1 / 4 := sq_mul_abs_psi2_le hp hp8
  obtain ⟨hb1, hb2⟩ := beta12_psi_le hB (q := q) hc
  have hB1 := (hB q).1
  have hΦ1 := abs_Phi1_le c q
  have hΦ2 := abs_Phi2_le c q
  have n1 := abs_nonneg (x i0 * x i1)
  have n2 := abs_nonneg (psi1 p)
  have n3 := abs_nonneg (psi2 p)
  have n4 := abs_nonneg (beta1 q)
  have n5 : 0 ≤ |beta1 q| * psi p := mul_nonneg n4 (psi_nonneg _)
  have n6 : 0 ≤ |beta2 q| * psi p := mul_nonneg (abs_nonneg _) (psi_nonneg _)
  -- the two pieces
  have T1 : |x i0 * x i1 * Phi1 c q| ≤ B * A + 1 := by
    rw [abs_mul]
    have s1 : |x i0 * x i1| * |Phi1 c q| ≤ (q / 2) * (|beta1 q| * psi p + |psi1 p|) :=
      mul_le_mul hxy hΦ1 (abs_nonneg _) (by positivity)
    have s2 : (q / 2) * (|beta1 q| * psi p) ≤ B * A := by
      calc (q / 2) * (|beta1 q| * psi p) ≤ 1 * (B * A) :=
            mul_le_mul (by linarith) hb1 n5 zero_le_one
        _ = B * A := one_mul _
    have s3 : (q / 2) * |psi1 p| ≤ 1 := by
      have : (q / 2) * |psi1 p| ≤ (p / 2) * |psi1 p| := mul_le_mul_of_nonneg_right (by linarith) n2
      linarith
    nlinarith
  have T2 : |x i0 * x i1 * (4 * q * Phi2 c q)| ≤ B * A + B + 1 := by
    rw [abs_mul (x i0 * x i1), abs_mul (4 * q), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * q)]
    have s1 : |x i0 * x i1| * (4 * q * |Phi2 c q|) ≤
        (q / 2) * (4 * q * (|beta2 q| * psi p + 2 * (|beta1 q| * |psi1 p|) + |psi2 p|)) :=
      mul_le_mul hxy (mul_le_mul_of_nonneg_left hΦ2 (by positivity)) (by positivity) (by positivity)
    have e : (q / 2) * (4 * q * (|beta2 q| * psi p + 2 * (|beta1 q| * |psi1 p|) + |psi2 p|)) =
        (2 * q ^ 2) * (|beta2 q| * psi p) + (4 * q * |beta1 q|) * (q * |psi1 p|) +
          2 * (q ^ 2 * |psi2 p|) := by ring
    have s2 : (2 * q ^ 2) * (|beta2 q| * psi p) ≤ B * A := by
      calc (2 * q ^ 2) * (|beta2 q| * psi p) ≤ 1 * (B * A) :=
            mul_le_mul (by nlinarith) hb2 n6 zero_le_one
        _ = B * A := one_mul _
    have s3 : (4 * q * |beta1 q|) * (q * |psi1 p|) ≤ B := by
      have h1 : q * |psi1 p| ≤ 1 / 4 := le_trans (mul_le_mul_of_nonneg_right hqp n2) hψ1
      have h2 : 4 * q * |beta1 q| ≤ 4 * B := by
        have := mul_le_mul_of_nonneg_left hB1 hq0
        nlinarith
      calc (4 * q * |beta1 q|) * (q * |psi1 p|) ≤ (4 * B) * (1 / 4) :=
            mul_le_mul h2 h1 (mul_nonneg hq0 n2) (by positivity)
        _ = B := by ring
    have s4 : 2 * (q ^ 2 * |psi2 p|) ≤ 1 := by
      have : q ^ 2 * |psi2 p| ≤ p ^ 2 * |psi2 p| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hqp 2) n3
      linarith
    linarith
  have e : gU i0 i1 c x =
      (8 + 2 * d) * (x i0 * x i1 * Phi1 c q) + x i0 * x i1 * (4 * q * Phi2 c q) := by
    simp only [gU, ← hqdef]; ring
  rw [e]
  have hd0 : (0 : ℝ) ≤ 8 + 2 * d := by positivity
  calc |(8 + 2 * d) * (x i0 * x i1 * Phi1 c q) + x i0 * x i1 * (4 * q * Phi2 c q)|
      ≤ |(8 + 2 * d) * (x i0 * x i1 * Phi1 c q)| + |x i0 * x i1 * (4 * q * Phi2 c q)| :=
        abs_add_le _ _
    _ = (8 + 2 * d) * |x i0 * x i1 * Phi1 c q| + |x i0 * x i1 * (4 * q * Phi2 c q)| := by
        rw [abs_mul, abs_of_nonneg hd0]
    _ ≤ (8 + 2 * d) * (B * A + 1) + (B * A + B + 1) := by
        have := mul_le_mul_of_nonneg_left T1 hd0
        linarith

/-! ### The bound for `U_c` -/

theorem abs_U_le (hij : i0 ≠ i1) {c : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1 / 20) (x : E d) :
    |U i0 i1 c x| ≤ 1 := by
  set q := ‖x‖ ^ 2 with hqdef
  have hq0 : 0 ≤ q := sq_nonneg _
  rcases le_or_gt (1 / 20) q with hq | hq
  · rw [U_eq_zero i0 i1 hq, abs_zero]; exact zero_le_one
  have hxy : |x i0 * x i1| ≤ q / 2 := abs_coord_mul_le i0 i1 hij x
  have e : U i0 i1 c x = x i0 * x i1 * (beta q * psi (q + c)) := by simp [U, Wf, Phi, ← hqdef]
  rw [e, abs_mul (x i0 * x i1), abs_mul (beta q), abs_of_nonneg (beta_nonneg _),
    abs_of_nonneg (psi_nonneg _)]
  have hb := beta_le_one q
  have hb0 := beta_nonneg q
  have hψ0 := psi_nonneg (q + c)
  rcases eq_or_lt_of_le (add_nonneg hq0 hc) with hp0 | hp
  · have hq00 : q = 0 := by linarith
    have : x i0 * x i1 = 0 := coord_mul_eq_zero i0 i1 hij hq00
    rw [this, abs_zero, zero_mul]; exact zero_le_one
  · have h1 := mul_psi_le_one hp (by linarith)
    calc |x i0 * x i1| * (beta q * psi (q + c)) ≤ (q / 2) * (1 * psi (q + c)) :=
          mul_le_mul hxy (mul_le_mul_of_nonneg_right hb hψ0) (mul_nonneg hb0 hψ0) (by positivity)
      _ ≤ ((q + c) / 2) * psi (q + c) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right (by linarith) hψ0
      _ ≤ 1 := by linarith

/-! ### Positivity of the mixed derivative near the origin -/

theorem mixed_U_ge (hij : i0 ≠ i1) {c : ℝ} (hc : 0 < c) {x : E d} (hx : ‖x‖ ^ 2 + c ≤ 1 / 64) :
    psi (‖x‖ ^ 2 + c) / 2 ≤ fderiv ℝ (fun z => fderiv ℝ (U i0 i1 c) z (ev i0)) x (ev i1) := by
  have hq0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hc2 : c < 1 / 2 := by linarith
  rw [mixed_U i0 i1 hc hc2 hij]
  set q := ‖x‖ ^ 2 with hqdef
  have hq64 : q ≤ 1 / 64 := by linarith
  set p := q + c with hpdef
  have hp : 0 < p := by linarith
  have hp8 : p ≤ 1 / 8 := by linarith
  have e0 : Phi c q = psi p := by simp [Phi, beta_eq_one hq64, hpdef]
  have e1 : Phi1 c q = psi1 p := by
    simp [Phi1, beta_eq_one hq64, beta1_eq_zero (Or.inl hq64), hpdef]
  have e2 : Phi2 c q = psi2 p := by
    simp [Phi2, beta_eq_one hq64, beta1_eq_zero (Or.inl hq64), beta2_eq_zero' (Or.inl hq64), hpdef]
  rw [e0, e1, e2]
  have hψ := one_le_psi hp hp8
  have hψ2 := psi2_nonneg hp hp8
  have hs := coord_sq_add_le i0 i1 hij x
  have key : -(1 / (2 * psi p)) ≤ 2 * (x i0 ^ 2 + x i1 ^ 2) * psi1 p := by
    have hpos : 0 < 4 * p * psi p := by positivity
    have e : 2 * (x i0 ^ 2 + x i1 ^ 2) * psi1 p = -(2 * (x i0 ^ 2 + x i1 ^ 2) / (4 * p * psi p)) := by
      unfold psi1; ring
    rw [e]
    apply neg_le_neg
    rw [div_le_div_iff₀ hpos (by positivity)]
    have : x i0 ^ 2 + x i1 ^ 2 ≤ p := by linarith
    nlinarith [psi_nonneg p]
  have h3 : 0 ≤ 4 * (x i0 ^ 2 * x i1 ^ 2) * psi2 p := by positivity
  have h4 : 1 / (2 * psi p) ≤ psi p / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_UBounds

-- ============================================================================
-- KineticCounterexamples/Endpoint/ULimits.lean
-- ============================================================================

section File_Endpoint_ULimits

/-!
# Limits as `c → 0`: `U_c → u`, `g_c → g`, and continuity of `g`

`u = U_0` and `g = g_0` (the formula for `ΔU_c` at `c = 0`, which is `Δu` away from the origin).
-/

noncomputable section

open Real Filter Topology Set MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace KS

variable {d : ℕ}

lemma continuousAt_Phi_joint {c q : ℝ} (h0 : 0 < q + c) (h1 : q + c < 1) :
    ContinuousAt (fun p : ℝ × ℝ => Phi p.1 p.2) (c, q) ∧
    ContinuousAt (fun p : ℝ × ℝ => Phi1 p.1 p.2) (c, q) ∧
    ContinuousAt (fun p : ℝ × ℝ => Phi2 p.1 p.2) (c, q) := by
  have hs : ContinuousAt (fun p : ℝ × ℝ => p.2 + p.1) (c, q) :=
    (continuous_snd.add continuous_fst).continuousAt
  have hψ : ContinuousAt (fun p : ℝ × ℝ => psi (p.2 + p.1)) (c, q) :=
    ContinuousAt.comp_of_eq (g := psi) (continuousAt_psi h0 h1) hs rfl
  have hψ1 : ContinuousAt (fun p : ℝ × ℝ => psi1 (p.2 + p.1)) (c, q) :=
    ContinuousAt.comp_of_eq (g := psi1) (continuousAt_psi1 h0 h1) hs rfl
  have hψ2 : ContinuousAt (fun p : ℝ × ℝ => psi2 (p.2 + p.1)) (c, q) :=
    ContinuousAt.comp_of_eq (g := psi2) (continuousAt_psi2 h0 h1) hs rfl
  have hb : ContinuousAt (fun p : ℝ × ℝ => beta p.2) (c, q) :=
    (contDiff_beta.continuous.comp continuous_snd).continuousAt
  have hb1 : ContinuousAt (fun p : ℝ × ℝ => beta1 p.2) (c, q) :=
    (contDiff_beta1.continuous.comp continuous_snd).continuousAt
  have hb2 : ContinuousAt (fun p : ℝ × ℝ => beta2 p.2) (c, q) :=
    (continuous_beta2.comp continuous_snd).continuousAt
  refine ⟨hb.mul hψ, (hb1.mul hψ).add (hb.mul hψ1), ?_⟩
  exact ((hb2.mul hψ).add (continuousAt_const.mul (hb1.mul hψ1))).add (hb.mul hψ2)

variable (i0 i1 : Fin d)

/-- `U_c → U_0` and `g_c → g_0` pointwise. -/
theorem tendsto_U_gU (hij : i0 ≠ i1) {cs : ℕ → ℝ} (hcs : Tendsto cs atTop (𝓝 0)) (x : E d) :
    Tendsto (fun n => U i0 i1 (cs n) x) atTop (𝓝 (U i0 i1 0 x)) ∧
    Tendsto (fun n => gU i0 i1 (cs n) x) atTop (𝓝 (gU i0 i1 0 x)) := by
  have eU : ∀ c, U i0 i1 c x = x i0 * x i1 * Phi c (‖x‖ ^ 2) := fun c => rfl
  have eg : ∀ c, gU i0 i1 c x = x i0 * x i1 * ((8 + 2 * d) * Phi1 c (‖x‖ ^ 2) +
      4 * ‖x‖ ^ 2 * Phi2 c (‖x‖ ^ 2)) := fun c => rfl
  simp only [eU, eg]
  have hq0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  rcases le_or_gt (1 / 20) (‖x‖ ^ 2) with hq | hq
  · simp only [Phi_eq_zero hq, Phi1_eq_zero hq, Phi2_eq_zero hq]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  rcases eq_or_lt_of_le hq0 with hq00 | hqpos
  · have hx : x i0 * x i1 = 0 := coord_mul_eq_zero i0 i1 hij hq00.symm
    simp only [hx, zero_mul]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  obtain ⟨h0, h1, h2⟩ := continuousAt_Phi_joint (c := 0) (q := ‖x‖ ^ 2) (by linarith)
    (by linarith)
  have hpair : Tendsto (fun n => (cs n, ‖x‖ ^ 2)) atTop (𝓝 ((0 : ℝ), ‖x‖ ^ 2)) :=
    hcs.prodMk_nhds tendsto_const_nhds
  have t0 := h0.tendsto.comp hpair
  have t1 := h1.tendsto.comp hpair
  have t2 := h2.tendsto.comp hpair
  have t0' : Tendsto (fun n => Phi (cs n) (‖x‖ ^ 2)) atTop (𝓝 (Phi 0 (‖x‖ ^ 2))) := t0
  have t1' : Tendsto (fun n => Phi1 (cs n) (‖x‖ ^ 2)) atTop (𝓝 (Phi1 0 (‖x‖ ^ 2))) := t1
  have t2' : Tendsto (fun n => Phi2 (cs n) (‖x‖ ^ 2)) atTop (𝓝 (Phi2 0 (‖x‖ ^ 2))) := t2
  exact ⟨t0'.const_mul _, (((t1'.const_mul _).add (t2'.const_mul _))).const_mul _⟩

/-! ### A sequence `c_n ↓ 0` -/

def cseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) / 100

lemma cseq_pos (n : ℕ) : 0 < cseq n := by unfold cseq; positivity

lemma cseq_le (n : ℕ) : cseq n ≤ 1 / 100 := by
  unfold cseq
  have h : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  exact div_le_div_of_nonneg_right h (by norm_num)

lemma tendsto_cseq : Tendsto cseq atTop (𝓝 0) := by
  have := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (100 : ℝ)
  rw [zero_div] at this
  exact this

lemma contDiff_U_cseq (n : ℕ) : ContDiff ℝ ∞ (U (d := d) i0 i1 (cseq n)) :=
  contDiff_U i0 i1 (cseq_pos n) (by linarith [cseq_le n])

/-- `u = U_0` is measurable (a pointwise limit of continuous functions). -/
lemma measurable_U0 (hij : i0 ≠ i1) : Measurable (U (d := d) i0 i1 0) := by
  have hc : ∀ n, Measurable (U (d := d) i0 i1 (cseq n)) := fun n =>
    (contDiff_U_cseq i0 i1 n).continuous.measurable
  exact measurable_of_tendsto_metrizable hc
    (tendsto_pi_nhds.mpr fun x => (tendsto_U_gU i0 i1 hij tendsto_cseq x).1)

/-! ### Continuity of `g = g_0` -/

lemma psi_mul_abs_gU0_le (hij : i0 ≠ i1) {x : E d} (hq0 : 0 < ‖x‖ ^ 2)
    (hq : ‖x‖ ^ 2 ≤ 1 / 64) : psi (‖x‖ ^ 2) * |gU i0 i1 0 x| ≤ 2 + d := by
  set q := ‖x‖ ^ 2 with hqdef
  have e1 : Phi1 0 q = psi1 q := by
    simp [Phi1, beta_eq_one hq, beta1_eq_zero (Or.inl hq)]
  have e2 : Phi2 0 q = psi2 q := by
    simp [Phi2, beta_eq_one hq, beta1_eq_zero (Or.inl hq), beta2_eq_zero' (Or.inl hq)]
  have e : gU i0 i1 0 x =
      (8 + 2 * d) * (x i0 * x i1 * psi1 q) + x i0 * x i1 * (4 * q * psi2 q) := by
    simp only [gU, ← hqdef, e1, e2]; ring
  rw [e]
  have hq1 : q < 1 := by linarith
  have hψ := psi_pos hq0 hq1
  have hxy : |x i0 * x i1| ≤ q / 2 := abs_coord_mul_le i0 i1 hij x
  have a1 := psi_mul_abs_psi1 hq0 hq1
  have a2 := psi_sq_mul_psi2_le hq0 hq1
  have hψ2 := psi2_nonneg hq0 (by linarith)
  have h8 : (0 : ℝ) ≤ 8 + 2 * d := by positivity
  have h4 : (0 : ℝ) ≤ 4 * q * psi2 q := by positivity
  set a := |x i0 * x i1|
  set α := |psi1 q|
  have hα : 0 ≤ α := abs_nonneg _
  have step1 : |(8 + 2 * d) * (x i0 * x i1 * psi1 q) + x i0 * x i1 * (4 * q * psi2 q)| ≤
      (8 + 2 * d) * (a * α) + a * (4 * q * psi2 q) := by
    calc _ ≤ |(8 + 2 * d) * (x i0 * x i1 * psi1 q)| + |x i0 * x i1 * (4 * q * psi2 q)| :=
          abs_add_le _ _
      _ = _ := by
          rw [abs_mul ((8 : ℝ) + 2 * d), abs_mul (x i0 * x i1) (psi1 q),
            abs_mul (x i0 * x i1) (4 * q * psi2 q), abs_of_nonneg h8, abs_of_nonneg h4]
  have k1 : a * (psi q * α) ≤ (q / 2) * (psi q * α) :=
    mul_le_mul_of_nonneg_right hxy (mul_nonneg hψ.le hα)
  have k2 : a * (psi q * (4 * q * psi2 q)) ≤ (q / 2) * (psi q * (4 * q * psi2 q)) :=
    mul_le_mul_of_nonneg_right hxy (mul_nonneg hψ.le h4)
  have k1' := mul_le_mul_of_nonneg_left k1 h8
  have r1 : (q / 2) * (psi q * α) = (1 / 2) * (psi q * (q * α)) := by ring
  have r2 : (q / 2) * (psi q * (4 * q * psi2 q)) = 2 * (psi q * (q ^ 2 * psi2 q)) := by ring
  have r3 : psi q * ((8 + 2 * d) * (a * α) + a * (4 * q * psi2 q)) =
      (8 + 2 * d) * (a * (psi q * α)) + a * (psi q * (4 * q * psi2 q)) := by ring
  have hd0 : (0 : ℝ) ≤ d := d.cast_nonneg
  calc psi q * |(8 + 2 * d) * (x i0 * x i1 * psi1 q) + x i0 * x i1 * (4 * q * psi2 q)|
      ≤ psi q * ((8 + 2 * d) * (a * α) + a * (4 * q * psi2 q)) :=
        mul_le_mul_of_nonneg_left step1 hψ.le
    _ ≤ 2 + d := by
        rw [r3]
        rw [r1, a1] at k1'
        rw [r2] at k2
        nlinarith

lemma continuousAt_gU0_zero (hij : i0 ≠ i1) : ContinuousAt (gU (d := d) i0 i1 0) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set K : ℝ := 2 + d with hK
  have hK0 : 0 < K := by positivity
  set M : ℝ := K / ε + 1 with hMdef
  have hM : 0 < M := by positivity
  have g00 : gU i0 i1 0 (0 : E d) = 0 := by simp [gU]
  refine ⟨min (1 / 8) (Real.exp (-M ^ 2)), by positivity, fun x hx => ?_⟩
  rw [dist_zero_right] at hx
  rw [g00, dist_zero_right, Real.norm_eq_abs]
  by_cases hx0 : x = 0
  · rw [hx0, g00, abs_zero]; exact hε
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hq0 : 0 < ‖x‖ ^ 2 := by positivity
  have hx1 : ‖x‖ < 1 / 8 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x‖ < Real.exp (-M ^ 2) := lt_of_lt_of_le hx (min_le_right _ _)
  have hq64 : ‖x‖ ^ 2 ≤ 1 / 64 := by
    have := pow_le_pow_left₀ (norm_nonneg x) hx1.le 2
    norm_num at this ⊢; linarith
  have hqexp : ‖x‖ ^ 2 ≤ Real.exp (-2 * M ^ 2) := by
    have h := pow_le_pow_left₀ (norm_nonneg x) hx2.le 2
    have e : Real.exp (-M ^ 2) ^ 2 = Real.exp (-2 * M ^ 2) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [e] at h; exact h
  have hψ := le_psi_of_le_exp hq0 hM.le hqexp
  have hb := psi_mul_abs_gU0_le i0 i1 hij hq0 hq64
  have hle : |gU i0 i1 0 x| ≤ K / M := by
    rw [le_div_iff₀ hM]
    calc |gU i0 i1 0 x| * M ≤ |gU i0 i1 0 x| * psi (‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hψ (abs_nonneg _)
      _ = psi (‖x‖ ^ 2) * |gU i0 i1 0 x| := mul_comm _ _
      _ ≤ K := hb
  have hKM : K / M < ε := by
    rw [div_lt_iff₀ hM]
    have : ε * M = K + ε := by rw [hMdef]; field_simp
    linarith
  linarith

/-- **`g ∈ C_c(ℝᵈ)`**: the forcing `g = Δu` is continuous. -/
theorem continuous_gU0 (hij : i0 ≠ i1) : Continuous (gU (d := d) i0 i1 0) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hn : Continuous (fun z : E d => ‖z‖ ^ 2) := continuous_norm.pow 2
  have hc0 : Continuous (fun z : E d => z i0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i0).continuous
  have hc1 : Continuous (fun z : E d => z i1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i1).continuous
  by_cases hx : x = 0
  · rw [hx]; exact continuousAt_gU0_zero i0 i1 hij
  have hqpos : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx; positivity
  rcases lt_or_ge (‖x‖ ^ 2) (1 / 2) with hq | hq
  · obtain ⟨-, h1, h2⟩ := continuousAt_Phi_joint (c := 0) (q := ‖x‖ ^ 2) (by linarith)
      (by linarith)
    have hm : ContinuousAt (fun z : E d => ((0 : ℝ), ‖z‖ ^ 2)) x :=
      (continuous_const.prodMk hn).continuousAt
    have t1 : ContinuousAt (fun z : E d => Phi1 0 (‖z‖ ^ 2)) x :=
      ContinuousAt.comp_of_eq (g := fun p : ℝ × ℝ => Phi1 p.1 p.2) h1 hm rfl
    have t2 : ContinuousAt (fun z : E d => Phi2 0 (‖z‖ ^ 2)) x :=
      ContinuousAt.comp_of_eq (g := fun p : ℝ × ℝ => Phi2 p.1 p.2) h2 hm rfl
    have k8 : ContinuousAt (fun _ : E d => (8 + 2 * (d : ℝ))) x := continuousAt_const
    have k4 : ContinuousAt (fun _ : E d => (4 : ℝ)) x := continuousAt_const
    have := (hc0.continuousAt.mul hc1.continuousAt).mul
      ((k8.mul t1).add ((k4.mul hn.continuousAt).mul t2))
    exact this
  · have hq' : 1 / 20 < ‖x‖ ^ 2 := by linarith
    have hev : gU i0 i1 0 =ᶠ[𝓝 x] fun _ => 0 := by
      have hopen : {z : E d | 1 / 20 < ‖z‖ ^ 2} ∈ 𝓝 x :=
        (isOpen_lt continuous_const hn).mem_nhds hq'
      filter_upwards [hopen] with z hz
      exact gU_eq_zero i0 i1 (le_of_lt hz)
    exact continuousAt_const.congr hev.symm

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_ULimits

-- ============================================================================
-- KineticCounterexamples/Endpoint/ThConvDeriv.lean
-- ============================================================================

section File_Endpoint_ThConvDeriv

/-!
# Derivatives of the smoothing `θ̌ ⋆ g` and limits under the integral

* `∂_m (θ̌ ⋆ g) = -(∂_mθ)ˇ ⋆ g` and `∂_m ∂_{m'} (θ̌ ⋆ g) = (∂_m ∂_{m'} θ)ˇ ⋆ g`
  for `θ ∈ C_c^∞` and `g ∈ L¹_loc`;
* integration by parts `(∂∂θ)ˇ ⋆ F = θ̌ ⋆ ∂∂F` for smooth `F`;
* dominated convergence for `θ̌ ⋆ G_n`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set
open scoped ContDiff Convolution

namespace KS

variable {d : ℕ}

lemma fderiv_comp_neg_apply {f : E d → ℝ} (x m : E d) :
    fderiv ℝ (fun t => f (-t)) x m = -fderiv ℝ f (-x) m := by
  have h := fderiv_comp_smul (𝕜 := ℝ) (f := f) (x := x) (-1 : ℝ)
  simp only [neg_smul, one_smul] at h
  rw [h]
  simp

/-- `∂_m (θ̌ ⋆ g)(y) = -((∂_m θ)ˇ ⋆ g)(y)`. -/
lemma fderiv_thConv_apply {θ g : E d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hg : LocallyIntegrable g) (y m : E d) :
    fderiv ℝ (thConv θ g) y m = -thConv (fun x => fderiv ℝ θ x m) g y := by
  set θ' : E d → ℝ := fun t => θ (-t) with hθ'def
  have hθ' : ContDiff ℝ ∞ θ' := hθ.comp contDiff_neg
  have hθc' : HasCompactSupport θ' := hθc.comp_homeomorph (Homeomorph.neg (E d))
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  have hD := hθc'.hasFDerivAt_convolution_left L (hθ'.of_le (by simp)) hg y
  have e1 : thConv θ g = θ' ⋆[L, volume] g := rfl
  rw [e1, hD.fderiv]
  have hint : ConvolutionExistsAt (fderiv ℝ θ') g y (L.precompL (E d)) volume :=
    (hθc'.fderiv ℝ).convolutionExists_left (L.precompL (E d))
      (hθ'.continuous_fderiv (by simp)) hg y
  rw [convolution_def, ContinuousLinearMap.integral_apply hint]
  unfold thConv
  rw [convolution_def, ← integral_neg]
  congr 1
  funext t
  simp only [ContinuousLinearMap.precompL_apply, hθ'def, fderiv_comp_neg_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, L]
  ring

lemma contDiff_fderiv_apply' {θ : E d → ℝ} (hθ : ContDiff ℝ ∞ θ) (m : E d) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ θ z m) :=
  (hθ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- `∂_m ∂_{m'} (θ̌ ⋆ g) = (∂_m ∂_{m'} θ)ˇ ⋆ g`. -/
lemma fderiv2_thConv_apply {θ g : E d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hg : LocallyIntegrable g) (y m m' : E d) :
    fderiv ℝ (fun z => fderiv ℝ (thConv θ g) z m') y m =
      thConv (fun x => fderiv ℝ (fun z => fderiv ℝ θ z m') x m) g y := by
  have hθ1 := contDiff_fderiv_apply' hθ m'
  have hθ1c : HasCompactSupport (fun z => fderiv ℝ θ z m') := hθc.fderiv_apply ℝ m'
  have e : (fun z => fderiv ℝ (thConv θ g) z m') =
      fun z => -thConv (fun x => fderiv ℝ θ x m') g z := by
    funext z; exact fderiv_thConv_apply hθ hθc hg z m'
  rw [e, fderiv_fun_neg, ContinuousLinearMap.neg_apply, fderiv_thConv_apply hθ1 hθ1c hg y m,
    neg_neg]

/-- Integration by parts: `((∂_{m'} ∂_m θ)ˇ ⋆ F)(y) = (θ̌ ⋆ ∂_m ∂_{m'} F)(y)` for smooth `F`. -/
lemma thConv_d2 {θ F : E d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hF : ContDiff ℝ ∞ F) (m m' y : E d) :
    thConv (fun x => fderiv ℝ (fun z => fderiv ℝ θ z m) x m') F y =
      thConv θ (fun w => fderiv ℝ (fun z => fderiv ℝ F z m') w m) y := by
  rw [thConv_apply, thConv_apply]
  have hFy : ContDiff ℝ ∞ (fun x => F (y + x)) := hF.comp (contDiff_const.add contDiff_id)
  have h := ibp2_E hFy hθ hθc m m'
  have e1 : ∀ w, fderiv ℝ (fun z => fderiv ℝ (fun x => F (y + x)) z m') w m =
      fderiv ℝ (fun z => fderiv ℝ F z m') (y + w) m := by
    intro w
    have e2 : (fun z => fderiv ℝ (fun x => F (y + x)) z m') = fun z => fderiv ℝ F (y + z) m' := by
      funext z; rw [fderiv_comp_add_left]
    rw [e2, fderiv_comp_add_left (f := fun z => fderiv ℝ F z m')]
  simp_rw [e1] at h
  calc ∫ x, fderiv ℝ (fun z => fderiv ℝ θ z m) x m' * F (y + x)
      = ∫ x, F (y + x) * fderiv ℝ (fun z => fderiv ℝ θ z m) x m' := by
        congr 1; funext x; ring
    _ = ∫ x, fderiv ℝ (fun z => fderiv ℝ F z m') (y + x) m * θ x := h
    _ = ∫ x, θ x * fderiv ℝ (fun z => fderiv ℝ F z m') (y + x) m := by
        congr 1; funext x; ring

/-- Dominated convergence for `θ̌ ⋆ G_n`. -/
lemma tendsto_thConv {θ : E d → ℝ} (hθi : Integrable θ) {G : ℕ → E d → ℝ} {G0 : E d → ℝ}
    {K : ℝ} (hGm : ∀ n, Measurable (G n)) (hK : ∀ n x, |G n x| ≤ K)
    (hlim : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (G0 x))) (y : E d) :
    Tendsto (fun n => thConv θ (G n) y) atTop (𝓝 (thConv θ G0 y)) := by
  simp_rw [thConv_apply]
  apply tendsto_integral_of_dominated_convergence (fun x => K * |θ x|)
  · intro n
    exact hθi.aestronglyMeasurable.mul ((hGm n).comp (measurable_const_add y)).aestronglyMeasurable
  · exact hθi.abs.const_mul K
  · intro n
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK n _) (abs_nonneg _)
  · filter_upwards with x
    exact (hlim (y + x)).const_mul (θ x)

/-- Linearity of `θ̌ ⋆ ·` over finite sums of continuous functions. -/
lemma thConv_sum {θ : E d → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ) {ι : Type*}
    (s : Finset ι) {G : ι → E d → ℝ} (hG : ∀ i, Continuous (G i)) (y : E d) :
    thConv θ (fun x => ∑ i ∈ s, G i x) y = ∑ i ∈ s, thConv θ (G i) y := by
  simp_rw [thConv_apply, Finset.mul_sum]
  rw [integral_finset_sum]
  intro i _
  exact (hθ.mul ((hG i).comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
    hθc.mul_right

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_ThConvDeriv

-- ============================================================================
-- KineticCounterexamples/Endpoint/Thm43.lean
-- ============================================================================

section File_Endpoint_Thm43

/-!
# Theorem 4.3 of Dong–Wang (continuous forcing, `D_v² f ∉ L^∞_loc`)

`u(x) = η(x) x₁x₂ (-log|x|)^{1/2}` (here `u = U_0`, `η = β(|x|²)`) and `g = Δu ∈ C_c(ℝᵈ)`
(here `g = g_0`).

* (i) `f = 𝒮g` is a bounded stationary distributional solution of
  `(∂_t + v·∇_x) f = Δ_v f + g` and `D_v² f ∉ L^∞_loc`;
* (ii) `g_ε = ΔU_{ε²} ∈ C_c^∞` with `|g_ε| ≤ C`, and `f_ε = 𝒮g_ε` are smooth bounded stationary
  solutions with `|f_ε| ≤ C` and `∂_{v₁v₂} f_ε(t,0,0) = -(log(1/ε))^{1/2}`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ENNReal ContDiff

namespace KS

variable {d : ℕ}

variable (i0 i1 : Fin d)

/-! ### The other order of the mixed derivative -/

lemma Wf_swap (Φ : ℝ → ℝ) : Wf (d := d) i1 i0 Φ = Wf i0 i1 Φ := by
  funext x; simp only [Wf]; ring

lemma mixed_U' {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hij : i0 ≠ i1) (x : E d) :
    fderiv ℝ (fun z => fderiv ℝ (U i0 i1 c) z (ev i1)) x (ev i0) =
      Phi c (‖x‖ ^ 2) + 2 * (x i0 ^ 2 + x i1 ^ 2) * Phi1 c (‖x‖ ^ 2) +
        4 * (x i0 ^ 2 * x i1 ^ 2) * Phi2 c (‖x‖ ^ 2) := by
  have h := mixed_Wf i1 i0 (fun q hq => hasDerivAt_Phi hc hc2 hq)
    (fun q hq => hasDerivAt_Phi1 hc hc2 hq) (Ne.symm hij) x
  rw [Wf_swap] at h
  rw [show U i0 i1 c = Wf i0 i1 (Phi c) from rfl, h]
  ring

lemma mixed_U'_zero {c : ℝ} (hc : 0 < c) (hc2 : c < 1 / 2) (hij : i0 ≠ i1) :
    fderiv ℝ (fun z => fderiv ℝ (U (d := d) i0 i1 c) z (ev i1)) 0 (ev i0) = psi c := by
  rw [mixed_U' i0 i1 hc hc2 hij]
  simp [Phi, beta_eq_one (by norm_num : (0 : ℝ) ≤ 1 / 64)]

/-! ### Basic facts on `u = U_0` and `g = g_0` -/

lemma U0_eq_zero_of {y : E d} (hy : 1 ≤ ‖y‖) : U i0 i1 0 y = 0 :=
  U_eq_zero i0 i1 (by nlinarith)

lemma gU_eq_zero_of {c : ℝ} {y : E d} (hy : 1 ≤ ‖y‖) : gU i0 i1 c y = 0 :=
  gU_eq_zero i0 i1 (by nlinarith)

lemma locallyIntegrable_U0 (hij : i0 ≠ i1) : LocallyIntegrable (U (d := d) i0 i1 0) :=
  (integrable_of_bound (measurable_U0 i0 i1 hij) (K := 1)
    (fun y => abs_U_le i0 i1 hij le_rfl (by norm_num) y)
    (fun y hy => U0_eq_zero_of i0 i1 hy)).locallyIntegrable

/-! ### `Δ(θ̌ ⋆ u) = θ̌ ⋆ g` -/

theorem lap_thConv_u (hij : i0 ≠ i1) {θ : E d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) (y : E d) :
    ∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ (thConv θ (U i0 i1 0)) z (ev i)) y (ev i) =
      thConv θ (gU i0 i1 0) y := by
  have huli := locallyIntegrable_U0 i0 i1 hij
  set θd : Fin d → E d → ℝ := fun i x => fderiv ℝ (fun z => fderiv ℝ θ z (ev i)) x (ev i)
    with hθd
  have e1 : ∀ i, fderiv ℝ (fun z => fderiv ℝ (thConv θ (U i0 i1 0)) z (ev i)) y (ev i) =
      thConv (θd i) (U i0 i1 0) y := fun i => fderiv2_thConv_apply hθ hθc huli y (ev i) (ev i)
  rw [Finset.sum_congr rfl (fun i _ => e1 i)]
  have hθi : Integrable θ := hθ.continuous.integrable_of_hasCompactSupport hθc
  have hθdi : ∀ i, Integrable (θd i) := fun i =>
    (contDiff_d2 hθ (ev i) (ev i)).continuous.integrable_of_hasCompactSupport
      ((hθc.fderiv_apply ℝ (ev i)).fderiv_apply ℝ (ev i))
  obtain ⟨Cg, hCg0, hCg⟩ := exists_bound_gU i0 i1 hij
  have hc2 : ∀ n, cseq n < 1 / 2 := fun n => by linarith [cseq_le n]
  have hc20 : ∀ n, cseq n ≤ 1 / 20 := fun n => by linarith [cseq_le n]
  have hL : Tendsto (fun n => ∑ i : Fin d, thConv (θd i) (U i0 i1 (cseq n)) y) atTop
      (𝓝 (∑ i : Fin d, thConv (θd i) (U i0 i1 0) y)) :=
    tendsto_finset_sum _ fun i _ => tendsto_thConv (hθdi i)
      (fun n => (contDiff_U_cseq i0 i1 n).continuous.measurable)
      (fun n x => abs_U_le i0 i1 hij (cseq_pos n).le (hc20 n) x)
      (fun x => (tendsto_U_gU i0 i1 hij tendsto_cseq x).1) y
  have hR : Tendsto (fun n => thConv θ (gU i0 i1 (cseq n)) y) atTop
      (𝓝 (thConv θ (gU i0 i1 0) y)) :=
    tendsto_thConv hθi
      (fun n => (contDiff_gU i0 i1 (cseq_pos n) (hc2 n) hij).continuous.measurable)
      (fun n x => hCg _ (cseq_pos n).le (hc20 n) x)
      (fun x => (tendsto_U_gU i0 i1 hij tendsto_cseq x).2) y
  have heq : ∀ n, ∑ i : Fin d, thConv (θd i) (U i0 i1 (cseq n)) y =
      thConv θ (gU i0 i1 (cseq n)) y := by
    intro n
    have hU := contDiff_U i0 i1 (cseq_pos n) (hc2 n)
    have e2 : ∀ i, thConv (θd i) (U i0 i1 (cseq n)) y =
        thConv θ (fun w => fderiv ℝ (fun z => fderiv ℝ (U i0 i1 (cseq n)) z (ev i)) w (ev i)) y :=
      fun i => thConv_d2 hθ hθc hU (ev i) (ev i) y
    rw [Finset.sum_congr rfl (fun i _ => e2 i),
      ← thConv_sum hθ.continuous hθc Finset.univ (fun i => (contDiff_d2 hU _ _).continuous) y]
    congr 1
    funext x
    exact lap_U i0 i1 (cseq_pos n) (hc2 n) hij x
  exact tendsto_nhds_unique (hL.congr heq) hR

/-! ### The mixed derivative of `θ̌ ⋆ u` at the origin -/

theorem mixed_thConv_u_ge (hij : i0 ≠ i1) {θ : E d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) (hθ0 : ∀ x, 0 ≤ θ x) {r : ℝ} (hr : 0 < r)
    (hr2 : 2 * r ^ 2 ≤ 1 / 64) (hθs : tsupport θ ⊆ Metric.closedBall 0 r) :
    psi (2 * r ^ 2) / 2 * ∫ x, θ x ≤
      fderiv ℝ (fun z => fderiv ℝ (thConv θ (U i0 i1 0)) z (ev i1)) 0 (ev i0) := by
  have huli := locallyIntegrable_U0 i0 i1 hij
  rw [fderiv2_thConv_apply hθ hθc huli 0 (ev i0) (ev i1)]
  set θm : E d → ℝ := fun x => fderiv ℝ (fun z => fderiv ℝ θ z (ev i1)) x (ev i0) with hθm
  have hθmi : Integrable θm :=
    (contDiff_d2 hθ (ev i1) (ev i0)).continuous.integrable_of_hasCompactSupport
      ((hθc.fderiv_apply ℝ (ev i1)).fderiv_apply ℝ (ev i0))
  have hc2 : ∀ n, cseq n < 1 / 2 := fun n => by linarith [cseq_le n]
  have hc20 : ∀ n, cseq n ≤ 1 / 20 := fun n => by linarith [cseq_le n]
  have hL : Tendsto (fun n => thConv θm (U i0 i1 (cseq n)) 0) atTop
      (𝓝 (thConv θm (U i0 i1 0) 0)) :=
    tendsto_thConv hθmi (fun n => (contDiff_U_cseq i0 i1 n).continuous.measurable)
      (fun n x => abs_U_le i0 i1 hij (cseq_pos n).le (hc20 n) x)
      (fun x => (tendsto_U_gU i0 i1 hij tendsto_cseq x).1) 0
  apply ge_of_tendsto hL
  have hev : ∀ᶠ n in atTop, cseq n < r ^ 2 := (tendsto_order.1 tendsto_cseq).2 _ (by positivity)
  filter_upwards [hev] with n hn
  have hU := contDiff_U i0 i1 (cseq_pos n) (hc2 n)
  rw [thConv_d2 hθ hθc hU (ev i1) (ev i0) 0, thConv_apply, ← integral_const_mul]
  set F : E d → ℝ := fun w => fderiv ℝ (fun z => fderiv ℝ (U i0 i1 (cseq n)) z (ev i0)) w (ev i1)
  have hFc : Continuous F := (contDiff_d2 hU (ev i0) (ev i1)).continuous
  have hθi : Integrable θ := hθ.continuous.integrable_of_hasCompactSupport hθc
  apply integral_mono (hθi.const_mul _)
  · exact (hθ.continuous.mul (hFc.comp (continuous_const.add continuous_id))).integrable_of_hasCompactSupport
      hθc.mul_right
  intro x
  simp only [zero_add]
  by_cases hx : x ∈ tsupport θ
  · have hxr : ‖x‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hθs hx
    have hx2 : ‖x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxr 2
    have hsum : ‖x‖ ^ 2 + cseq n ≤ 2 * r ^ 2 := by linarith
    have h1 := mixed_U_ge i0 i1 hij (cseq_pos n) (x := x) (by linarith)
    have h2 : psi (2 * r ^ 2) ≤ psi (‖x‖ ^ 2 + cseq n) :=
      psi_antitone (by have := cseq_pos n; positivity) hsum
    have h3 : psi (2 * r ^ 2) / 2 ≤ F x := le_trans (by linarith) h1
    calc psi (2 * r ^ 2) / 2 * θ x ≤ F x * θ x := mul_le_mul_of_nonneg_right h3 (hθ0 x)
      _ = θ x * F x := mul_comm _ _
  · rw [image_eq_zero_of_notMem_tsupport hx]; simp

/-! ### The velocity Hessian of the smoothed solution at the origin -/

theorem hessV_thConv_g (hd : 1 ≤ d) (hij : i0 ≠ i1) {θ : E d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) :
    hessV (solF (fun y => (thConv θ (gU i0 i1 0) y : ℂ))) (0, 0, 0) i0 i1 =
      -fderiv ℝ (fun z => fderiv ℝ (thConv θ (U i0 i1 0)) z (ev i1)) 0 (ev i0) := by
  set w := thConv θ (U i0 i1 0) with hwdef
  have hw : ContDiff ℝ ∞ w := contDiff_thConv hθ hθc (measurable_U0 i0 i1 hij) (K := 1)
    (fun y => abs_U_le i0 i1 hij le_rfl (by norm_num) y) (fun y hy => U0_eq_zero_of i0 i1 hy)
  have hwc : HasCompactSupport w := hasCompactSupport_thConv hθc (fun y hy => U0_eq_zero_of i0 i1 hy)
  set hS := toS w hw hwc
  have hlap : (fun y => (thConv θ (gU i0 i1 0) y : ℂ)) = ⇑(lapS hS) := by
    funext y
    rw [lapS_apply]
    simp_rw [hS, dS_dS_toS_apply w hw hwc]
    rw [← Complex.ofReal_sum, lap_thConv_u i0 i1 hij hθ hθc y]
  rw [hlap, hessV_solF hd (lapS hS) 0 0 0 i0 i1, hess0_kinF_lap hd hS 0 i0 i1,
    dS_dS_toS_apply w hw hwc]
  simp

/-! ### `D_v² f ∉ L^∞_loc` -/

theorem not_hessVLinfLoc (hd : 2 ≤ d) :
    ¬ HessVLinfLoc (solF (fun y => (gU (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ 0 y : ℂ))) := by
  intro hL
  have hd1 : 1 ≤ d := by omega
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨Cg, hCg0, hCg⟩ := exists_bound_gU i0 i1 hij
  obtain ⟨M, hM⟩ := hessV_bound_of_linfLoc hd1 (continuous_gU0 i0 i1 hij).measurable (K := Cg)
    (fun y => hCg 0 le_rfl (by norm_num) y) (fun y hy => gU_eq_zero_of i0 i1 hy) i0 i1 hL
  set M' := max M 0
  set K := 2 * M' + 1 with hKdef
  have hK : 0 < K := by positivity
  set r := Real.exp (-K ^ 2) / 12 with hrdef
  have hr : 0 < r := by positivity
  have he1 : Real.exp (-K ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hr1 : r ≤ 1 := by rw [hrdef]; linarith
  have hr2 : 2 * r ^ 2 ≤ 1 / 64 := by
    have : r ≤ 1 / 12 := by rw [hrdef]; linarith
    nlinarith
  have hrexp : 2 * r ^ 2 ≤ Real.exp (-2 * K ^ 2) := by
    have e : Real.exp (-2 * K ^ 2) = Real.exp (-K ^ 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e, hrdef]
    have h0 : 0 ≤ Real.exp (-K ^ 2) := (Real.exp_pos _).le
    nlinarith
  set b := vbump (d := d) r hr
  have hθ : ContDiff ℝ ∞ (⇑b) := b.contDiff
  have hθc : HasCompactSupport (⇑b) := b.hasCompactSupport
  have hθ0 : ∀ x, 0 ≤ b x := fun x => b.nonneg
  have hθs : tsupport (⇑b) ⊆ Metric.closedBall 0 r := by rw [b.tsupport_eq]; rfl
  have hθs1 : tsupport (⇑b) ⊆ Metric.closedBall 0 1 :=
    hθs.trans (Metric.closedBall_subset_closedBall hr1)
  have hθpos : 0 < ∫ x, b x := b.integral_pos
  have h1 := hM b hθ hθc hθ0 hθs1
  rw [hessV_thConv_g i0 i1 hd1 hij hθ hθc, abs_neg] at h1
  have h2 := mixed_thConv_u_ge i0 i1 hij hθ hθc hθ0 hr hr2 hθs
  have h3 : K ≤ psi (2 * r ^ 2) := le_psi_of_le_exp (by positivity) hK.le hrexp
  have h4 : K / 2 * ∫ x, b x ≤ psi (2 * r ^ 2) / 2 * ∫ x, b x :=
    mul_le_mul_of_nonneg_right (by linarith) hθpos.le
  have h5 := (le_abs_self _).trans h1
  have h6 : M * ∫ x, b x ≤ M' * ∫ x, b x := mul_le_mul_of_nonneg_right (le_max_left _ _) hθpos.le
  have h7 : K / 2 * (∫ x, b x) = M' * (∫ x, b x) + (1 / 2) * (∫ x, b x) := by rw [hKdef]; ring
  linarith

/-! ### Theorem 4.3 -/

/-- **Theorem 4.3 (i)** (Dong–Wang). For `d ≥ 2` there are `g ∈ C_c(ℝᵈ)` (independent of `v`) and a
bounded stationary distributional solution `f` of `(∂_t + v·∇_x) f = Δ_v f + g` on
`ℝ × ℝᵈ × ℝᵈ` such that `D_v² f ∉ L^∞_loc`. -/
theorem thm_4_3_i (d : ℕ) (hd : 2 ≤ d) :
    ∃ (g : E d → ℝ) (f : Pt d → ℝ),
      Continuous g ∧ HasCompactSupport g ∧
      (∀ t t' x v, f (t, x, v) = f (t', x, v)) ∧
      (∃ C : ℝ, ∀ p, |f p| ≤ C) ∧
      IsDistribSol f (fun p => g p.2.1) ∧
      ¬ HessVLinfLoc f := by
  have hd1 : 1 ≤ d := by omega
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨Cg, hCg0, hCg⟩ := exists_bound_gU i0 i1 hij
  have hc2 : ∀ n, cseq n < 1 / 2 := fun n => by linarith [cseq_le n]
  have hc20 : ∀ n, cseq n ≤ 1 / 20 := fun n => by linarith [cseq_le n]
  have happrox := isDistribSol_of_approx hd1 (g := gU i0 i1 0)
    (gn := fun n => gU i0 i1 (cseq n)) (K := Cg)
    (fun n => contDiff_gU i0 i1 (cseq_pos n) (hc2 n) hij)
    (fun n => hasCompactSupport_gU i0 i1 _)
    (fun n y => hCg _ (cseq_pos n).le (hc20 n) y)
    (fun n y hy => gU_eq_zero_of i0 i1 hy)
    (Eventually.of_forall fun y => (tendsto_U_gU i0 i1 hij tendsto_cseq y).2)
  exact ⟨gU i0 i1 0, solF (fun y => (gU i0 i1 0 y : ℂ)), continuous_gU0 i0 i1 hij,
    hasCompactSupport_gU i0 i1 0, solF_stationary _, ⟨_, happrox.2⟩, happrox.1,
    not_hessVLinfLoc hd⟩

/-- **Theorem 4.3 (ii)** (Dong–Wang). For `d ≥ 2` there is `C > 0` such that for every `0 < ε < 1/10`
there are `g_ε ∈ C_c^∞(ℝᵈ)` (independent of `v`) with `|g_ε| ≤ C` and a smooth stationary solution
`f_ε` of `(∂_t + v·∇_x) f_ε = Δ_v f_ε + g_ε` with `|f_ε| ≤ C` and
`∂_{v₁v₂} f_ε(t,0,0) = -(log(1/ε))^{1/2}`; in particular
`‖D_v² f_ε‖_{L^∞(B_{1/4}×B_{1/4})} ≥ (log(1/ε))^{1/2}`. -/
theorem thm_4_3_ii (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∃ (g : E d → ℝ) (f : Pt d → ℝ),
        ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ x, |g x| ≤ C) ∧
        ContDiff ℝ ∞ f ∧ (∀ t t' x v, f (t, x, v) = f (t', x, v)) ∧
        (∀ p, KFP f (fun _ => 1) (fun _ => 0) (fun p => g p.2.1) p) ∧
        (∀ p, |f p| ≤ C) ∧
        (∀ t, hessV f (t, 0, 0) ⟨0, by omega⟩ ⟨1, by omega⟩ = -√(Real.log (1 / ε))) ∧
        ENNReal.ofReal (√(Real.log (1 / ε))) ≤
          essSup (fun q : E d × E d => ENNReal.ofReal (frob (hessV f (0, q.1, q.2))))
            (volume.restrict (Metric.ball (0 : E d) (1 / 4) ×ˢ Metric.ball (0 : E d) (1 / 4))) := by
  have hd1 : 1 ≤ d := by omega
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨Cg, hCg0, hCg⟩ := exists_bound_gU i0 i1 hij
  set L := (volume (Metric.ball (0 : E d) 1)).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  set Cf := kinBd d Cg (Cg * L)
  refine ⟨max Cg Cf + 1, by
    have := le_max_left Cg Cf; linarith, fun ε hε hε' => ?_⟩
  set c := ε ^ 2 with hcdef
  have hc : 0 < c := by positivity
  have hc2 : c < 1 / 2 := by nlinarith
  have hc20 : c ≤ 1 / 20 := by nlinarith
  set g := gU i0 i1 c
  have hg : ContDiff ℝ ∞ g := contDiff_gU i0 i1 hc hc2 hij
  have hgc : HasCompactSupport g := hasCompactSupport_gU i0 i1 c
  have hgC : ∀ x, |g x| ≤ Cg := fun x => hCg c hc.le hc20 x
  set hS := toS g hg hgc
  have hcoe : (fun y => (g y : ℂ)) = ⇑hS := (coe_toS g hg hgc).symm
  -- `g = ΔU_c`
  have hU := contDiff_U i0 i1 hc hc2
  have hUc := hasCompactSupport_U i0 i1 c
  set hW := toS (U i0 i1 c) hU hUc
  have hlap : (fun y => (g y : ℂ)) = ⇑(lapS hW) := by
    funext y
    rw [lapS_apply]
    simp_rw [hW, dS_dS_toS_apply (U i0 i1 c) hU hUc]
    rw [← Complex.ofReal_sum, lap_U i0 i1 hc hc2 hij y]
  have hhess : ∀ t, hessV (solF (fun y => (g y : ℂ))) (t, 0, 0) i0 i1 = -√(Real.log (1 / ε)) := by
    intro t
    rw [hlap, hessV_solF hd1 (lapS hW) t 0 0 i0 i1, hess0_kinF_lap hd1 hW 0 i0 i1,
      dS_dS_toS_apply (U i0 i1 c) hU hUc, mixed_U'_zero i0 i1 hc hc2 hij, hcdef, psi_sq_eps hε]
    simp
  refine ⟨g, solF (fun y => (g y : ℂ)), hg, hgc,
    fun x => (hgC x).trans ((le_max_left _ _).trans (by linarith)), ?_, solF_stationary _,
    solF_KFP hd1 g hg hgc, ?_, hhess, ?_⟩
  · rw [hcoe]; exact solF_smooth hd1 hS
  · intro p
    have hint : Integrable (fun y => (g y : ℂ)) := by rw [hcoe]; exact hS.integrable
    have h1 := abs_solF_le hd1 hint (K := Cg) (fun y => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hgC y) p
    have h2 : ∫ y, ‖(g y : ℂ)‖ ≤ Cg * L :=
      integral_norm_le_of_bound hgC (fun y hy => gU_eq_zero_of i0 i1 hy)
    have h3 := kinBd_mono hd1 hCg0 (integral_nonneg fun y => norm_nonneg _) h2
    have h4 := le_max_right Cg Cf
    linarith
  · -- the `L^∞` formulation
    have hK := contDiff_kinF hd1 hS
    have hf : solF (fun y => (g y : ℂ)) = liftK (kinF ⇑hS) := by
      rw [hcoe]; exact solF_eq_liftK hd1 hS
    have hcont : Continuous (fun q : E d × E d =>
        ENNReal.ofReal (frob (hessV (solF (fun y => (g y : ℂ))) (0, q.1, q.2)))) := by
      rw [hf]
      exact ENNReal.continuous_ofReal.comp (continuous_frob fun i j => continuous_hessV_liftK hK i j)
    have hU' : IsOpen (Metric.ball (0 : E d) (1 / 4) ×ˢ Metric.ball (0 : E d) (1 / 4)) :=
      Metric.isOpen_ball.prod Metric.isOpen_ball
    have h0U : ((0 : E d), (0 : E d)) ∈
        Metric.ball (0 : E d) (1 / 4) ×ˢ Metric.ball (0 : E d) (1 / 4) := by
      simp [Metric.mem_ball]
    have hle := le_essSup_of_continuous (μ := (volume : Measure (E d × E d))) hU'
      (fun V hV hne => (hV.inter hU').measure_pos _ hne) hcont h0U
    refine le_trans ?_ hle
    apply ENNReal.ofReal_le_ofReal
    have := abs_le_frob (hessV (solF (fun y => (g y : ℂ))) (0, 0, 0)) i0 i1
    rw [hhess 0, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)] at this
    exact this

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Thm43

-- ============================================================================
-- KineticCounterexamples/Endpoint/Rem42Setup.lean
-- ============================================================================

section File_Endpoint_Rem42Setup

/-!
# Remark 4.2 of Dong–Wang: setup

* a radial cutoff `χ ∈ C_c^∞(B₁)`, `0 ≤ χ ≤ 1`, `χ = 1` on `B_{1/2}`;
* the forcing `g = χ sgn(x_{i₀} x_{i₁})` and its smooth approximations
  `g_n = χ σ(n x_{i₀}) σ(n x_{i₁})`;
* a general form of the logarithmic lower bound for `∂_{v_{i₀} v_{i₁}} 𝒮h(t,0,0)`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ENNReal ContDiff

namespace KS

variable {d : ℕ}

/-! ### A radial cutoff -/

def betaR (q : ℝ) : ℝ := Real.smoothTransition ((9 / 16 - q) / (9 / 16 - 1 / 4))

lemma contDiff_betaR : ContDiff ℝ ∞ betaR := by
  unfold betaR
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.sub contDiff_id).div_const _)

lemma betaR_eq_one {q : ℝ} (hq : q ≤ 1 / 4) : betaR q = 1 := by
  unfold betaR
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

lemma betaR_eq_zero {q : ℝ} (hq : 9 / 16 ≤ q) : betaR q = 0 := by
  unfold betaR
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

/-- The radial cutoff `χ(x) = β_R(|x|²)`. -/
def chiR (x : E d) : ℝ := betaR (‖x‖ ^ 2)

lemma contDiff_chiR : ContDiff ℝ ∞ (chiR (d := d)) :=
  contDiff_betaR.comp (contDiff_norm_sq ℝ)

lemma chiR_nonneg (x : E d) : 0 ≤ chiR x := Real.smoothTransition.nonneg _
lemma chiR_le_one (x : E d) : chiR x ≤ 1 := Real.smoothTransition.le_one _

lemma chiR_eq_one {x : E d} (hx : ‖x‖ ≤ 1 / 2) : chiR x = 1 := by
  apply betaR_eq_one
  have := pow_le_pow_left₀ (norm_nonneg x) hx 2
  norm_num at this ⊢; linarith

lemma chiR_eq_zero {x : E d} (hx : 3 / 4 ≤ ‖x‖) : chiR x = 0 := by
  apply betaR_eq_zero
  have := pow_le_pow_left₀ (by norm_num) hx 2
  norm_num at this ⊢; linarith

lemma chiR_of_norm_eq {x x' : E d} (h : ‖x‖ = ‖x'‖) : chiR x = chiR x' := by
  simp only [chiR, h]

lemma tsupport_chiR : tsupport (chiR (d := d)) ⊆ Metric.closedBall 0 (3 / 4) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra h
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at h
  exact hx (chiR_eq_zero h.le)

lemma hasCompactSupport_chiR : HasCompactSupport (chiR (d := d)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (3 / 4))
    ((subset_tsupport _).trans tsupport_chiR)

lemma tsupport_chiR_ball : tsupport (chiR (d := d)) ⊆ Metric.ball 0 1 :=
  tsupport_chiR.trans (Metric.closedBall_subset_ball (by norm_num))

/-! ### The sign function -/

lemma measurable_realSign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

lemma realSign_mul (a b : ℝ) : Real.sign (a * b) = Real.sign a * Real.sign b := by
  rcases lt_trichotomy a 0 with ha | ha | ha <;> rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg ha hb), Real.sign_of_neg ha, Real.sign_of_neg hb]
    norm_num
  · simp [hb]
  · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos ha hb), Real.sign_of_neg ha, Real.sign_of_pos hb]
    norm_num
  · simp [ha]
  · simp [ha]
  · simp [ha]
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb), Real.sign_of_pos ha, Real.sign_of_neg hb]
    norm_num
  · simp [hb]
  · rw [Real.sign_of_pos (mul_pos ha hb), Real.sign_of_pos ha, Real.sign_of_pos hb]
    norm_num

lemma abs_realSign_le (a : ℝ) : |Real.sign a| ≤ 1 := by
  rcases Real.sign_apply_eq a with h | h | h <;> rw [h] <;> norm_num

/-! ### The forcing `g = χ sgn(x_{i₀} x_{i₁})` -/

variable (i0 i1 : Fin d)

/-- `g(x) = χ(x) sgn(x_{i₀} x_{i₁})`. -/
def gR (x : E d) : ℝ := chiR x * Real.sign (x i0 * x i1)

lemma gR_eq (x : E d) : gR i0 i1 x = chiR x * Real.sign (x i0) * Real.sign (x i1) := by
  rw [gR, realSign_mul, mul_assoc]

lemma measurable_gR : Measurable (gR (d := d) i0 i1) := by
  unfold gR
  have h0 : Measurable (fun z : E d => z i0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i0).continuous.measurable
  have h1 : Measurable (fun z : E d => z i1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i1).continuous.measurable
  exact contDiff_chiR.continuous.measurable.mul (measurable_realSign.comp (h0.mul h1))

lemma abs_gR_le (x : E d) : |gR i0 i1 x| ≤ 1 := by
  rw [gR, abs_mul, abs_of_nonneg (chiR_nonneg x)]
  have := abs_realSign_le (x i0 * x i1)
  have := chiR_le_one x
  have := chiR_nonneg x
  nlinarith [abs_nonneg (Real.sign (x i0 * x i1))]

lemma gR_eq_zero {x : E d} (hx : 3 / 4 ≤ ‖x‖) : gR i0 i1 x = 0 := by
  rw [gR, chiR_eq_zero hx, zero_mul]

lemma integrable_gR : Integrable (gR (d := d) i0 i1) :=
  integrable_of_bound (measurable_gR i0 i1) (abs_gR_le i0 i1)
    (fun y hy => gR_eq_zero i0 i1 (by linarith))

/-! ### Smooth approximations `g_n = χ σ((n+1) x_{i₀}) σ((n+1) x_{i₁})` -/

def gRn (n : ℕ) (x : E d) : ℝ :=
  chiR x * sig (x i0 * ((n : ℝ) + 1)) * sig (x i1 * ((n : ℝ) + 1))

lemma contDiff_gRn (n : ℕ) : ContDiff ℝ ∞ (gRn (d := d) i0 i1 n) := by
  unfold gRn
  have h0 : ContDiff ℝ ∞ (fun z : E d => z i0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i0).contDiff
  have h1 : ContDiff ℝ ∞ (fun z : E d => z i1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i1).contDiff
  exact (contDiff_chiR.mul (contDiff_sig.comp (h0.mul contDiff_const))).mul
    (contDiff_sig.comp (h1.mul contDiff_const))

lemma gRn_eq_zero (n : ℕ) {x : E d} (hx : 3 / 4 ≤ ‖x‖) : gRn i0 i1 n x = 0 := by
  rw [gRn, chiR_eq_zero hx]; ring

lemma hasCompactSupport_gRn (n : ℕ) : HasCompactSupport (gRn (d := d) i0 i1 n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E d) (3 / 4))
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact gRn_eq_zero i0 i1 n hx.le

lemma abs_gRn_le (n : ℕ) (x : E d) : |gRn i0 i1 n x| ≤ 1 := by
  unfold gRn
  rw [abs_mul, abs_mul, abs_of_nonneg (chiR_nonneg x)]
  have h1 := abs_sig_le (x i0 * ((n : ℝ) + 1))
  have h2 := abs_sig_le (x i1 * ((n : ℝ) + 1))
  have h3 := chiR_le_one x
  have h4 := chiR_nonneg x
  have h5 := abs_nonneg (sig (x i0 * ((n : ℝ) + 1)))
  have h6 := abs_nonneg (sig (x i1 * ((n : ℝ) + 1)))
  calc chiR x * |sig (x i0 * ((n : ℝ) + 1))| * |sig (x i1 * ((n : ℝ) + 1))| ≤ 1 * 1 * 1 := by
        gcongr
    _ = 1 := by norm_num

lemma sig_of_le_neg_one {s : ℝ} (hs : s ≤ -1) : sig s = -1 := by
  unfold sig
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma sig_zero : sig 0 = 0 := by unfold sig; simp

/-- `σ((n+1) t) → sgn t`. -/
lemma tendsto_sig_mul (t : ℝ) :
    Tendsto (fun n : ℕ => sig (t * ((n : ℝ) + 1))) atTop (𝓝 (Real.sign t)) := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [Real.sign_of_neg ht]
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (-t))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (1 / (-t) : ℝ) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ (by linarith)] at hn'
    exact (sig_of_le_neg_one (by nlinarith)).symm
  · subst ht; simp [sig_zero]
  · rw [Real.sign_of_pos ht]
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / t)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (1 / t : ℝ) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ ht] at hn'
    exact (sig_of_one_le (by nlinarith)).symm

lemma tendsto_gRn (x : E d) :
    Tendsto (fun n => gRn i0 i1 n x) atTop (𝓝 (gR i0 i1 x)) := by
  rw [gR_eq]
  exact ((tendsto_const_nhds (x := chiR x)).mul (tendsto_sig_mul (x i0))).mul
    (tendsto_sig_mul (x i1))

/-! ### The general logarithmic lower bound -/

/-- If `P = y_{i₀} y_{i₁} h ≥ 0` everywhere and `P ≥ y_{i₀} y_{i₁}` on the dyadic boxes of sizes
`ε ≤ a ≤ 1/8`, then `∂_{v_{i₀} v_{i₁}} 𝒮h(t,0,0) ≥ c log(1/ε)`. -/
theorem hess_ge_of_P (hd : 2 ≤ d) {h : E d → ℝ} (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (hP0 : ∀ y : E d, 0 ≤ y ⟨0, by omega⟩ * y ⟨1, by omega⟩ * h y) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 10)
    (hbox : ∀ a : ℝ, ε ≤ a → a ≤ 1 / 8 → ∀ y ∈ dbox (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ a,
      y ⟨0, by omega⟩ * y ⟨1, by omega⟩ ≤ y ⟨0, by omega⟩ * y ⟨1, by omega⟩ * h y)
    (t : ℝ) :
    cbox d / (4 * Real.log 2) * Real.log (1 / ε) ≤
      hessV (solF (fun y => (h y : ℂ))) (t, 0, 0) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hI, hEq⟩ := hessV_solF_phys hd1 h hh hhc t i0 i1
  set P : E d → ℝ := fun y => y i0 * y i1 * h y with hP
  have e : ∀ s ∈ Ioi (0 : ℝ), s ^ 2 *
      ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d (s ^ 3 / 3)) z (ev i0)) y (ev i1) * h y =
      ∫ y, kerK d s y * P y := by
    intro s hs
    have hτ : (0 : ℝ) < s ^ 3 / 3 := by
      have : 0 < s := hs
      positivity
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [fderiv_fderiv_hk_ev hτ y hij]
    simp only [kerK, hP]
    ring
  rw [hEq, setIntegral_congr_fun measurableSet_Ioi e]
  have hI' : IntegrableOn (fun s => ∫ y, kerK d s y * P y) (Ioi 0) :=
    hI.congr_fun e measurableSet_Ioi
  have hPc : Continuous P := by
    have : Continuous h := hh.continuous
    have h0 : Continuous (fun z : E d => z i0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i0).continuous
    have h1 : Continuous (fun z : E d => z i1) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i1).continuous
    exact (h0.mul h1).mul this
  have hPi : ∀ s ∈ Ioi (0 : ℝ), Integrable (fun y => kerK d s y * P y) := by
    intro s hs
    have hks : Continuous (fun y => kerK d s y) := by
      unfold kerK
      exact continuous_const.mul ((continuous_hk _).div_const _)
    exact (hks.mul hPc).integrable_of_hasCompactSupport (hhc.mul_left.mul_left)
  have key := ofReal_integral_kerK hd1 P hPc.measurable hP0 hPi hI'
  obtain ⟨hm3, hm2, hmlog⟩ := mEps_spec hε hε'
  set m := mEps ε
  set S : Finset ℕ := Finset.Icc 2 (m - 1)
  have hbox' : ∀ k ∈ S, ∀ y ∈ dbox i0 i1 (1 / 2 ^ (k + 1)), y i0 * y i1 ≤ P y := by
    intro k hk y hy
    obtain ⟨hk2, hkm⟩ := Finset.mem_Icc.mp hk
    apply hbox _ _ _ y hy
    · have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [le_div_iff₀ (by positivity)]
      calc ε * 2 ^ (k + 1) ≤ ε * 2 ^ m := by gcongr
        _ ≤ ε * (1 / ε) := by gcongr
        _ = 1 := by field_simp
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ^ 3 ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  have hcard := lintegral_ge_card hd1 i0 i1 hij S P hbox'
  rw [← key] at hcard
  have hSc : (S.card : ℝ) = (m : ℝ) - 2 := by
    simp only [S, Nat.card_Icc]
    have : m - 1 + 1 - 2 = m - 2 := by omega
    rw [this, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hcb := cbox_pos hd1
  have hlhs : (S.card : ℝ≥0∞) * ENNReal.ofReal (cbox d) = ENNReal.ofReal (S.card * cbox d) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [hlhs] at hcard
  have hpos : 0 < (S.card : ℝ) * cbox d := by
    rw [hSc]
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have : (0 : ℝ) < m - 2 := by linarith
    positivity
  have hle : (S.card : ℝ) * cbox d ≤ ∫ s in Ioi (0 : ℝ), ∫ y, kerK d s y * P y := by
    rcases (ENNReal.ofReal_le_ofReal_iff'.mp hcard) with h | h
    · exact h
    · linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc cbox d / (4 * Real.log 2) * Real.log (1 / ε)
      ≤ cbox d / (4 * Real.log 2) * ((m + 1) * Real.log 2) := by
        gcongr
    _ = (m + 1) / 4 * cbox d := by field_simp
    _ ≤ (S.card : ℝ) * cbox d := by
        rw [hSc]
        have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
        gcongr
        linarith
    _ ≤ _ := hle

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Rem42Setup

-- ============================================================================
-- KineticCounterexamples/Endpoint/Rem42.lean
-- ============================================================================

section File_Endpoint_Rem42

/-!
# Remark 4.2 of Dong–Wang (bounded forcing `g = χ sgn(x₁x₂)`, `D_v² f ∉ L^∞_loc`)

For `g = χ sgn(x₁x₂)` (`χ` a radial cutoff, `χ ∈ C_c^∞(B₁)`, `0 ≤ χ ≤ 1`, `χ = 1` on `B_{1/2}`)
and `f = 𝒮g = ∫₀^∞ P_{s³/3} g(x - s v) ds`:

* `g ∈ L^∞ ∩ L¹`, `f ∈ L^∞`;
* `(∂_t + v·∇_x) f = Δ_v f + g` in the sense of distributions;
* `D_v² f ∉ L^∞_loc`.

The proof of the last point: by the criterion `hessV_bound_of_linfLoc`, it suffices to show that
the smoothed forcings `θ̌_r ⋆ g` (`θ_r` a normalized product bump at scale `r`) have
`∂_{v₁v₂} 𝒮(θ̌_r ⋆ g)(0,0,0) ≥ c log(1/r)`. For this we show, by reflecting in the coordinates
`x₁` and `x₂`, that `y₁y₂ (θ̌_r ⋆ g)(y) ≥ 0` everywhere, and `θ̌_r ⋆ g = 1` on the dyadic boxes of
sizes `≥ r`; then the counting argument of Theorem 4.1 applies.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ENNReal ContDiff

namespace KS

variable {d : ℕ}

/-! ### Coordinate reflections -/

/-- Reflection in the `i`-th coordinate. -/
def crefl (i : Fin d) : E d ≃ₗᵢ[ℝ] E d :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma crefl_apply (i : Fin d) (z : E d) (j : Fin d) :
    crefl i z j = if j = i then -z j else z j := by
  simp only [crefl, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> simp

lemma crefl_self (i : Fin d) (z : E d) : crefl i z i = -z i := by
  rw [crefl_apply, if_pos rfl]

lemma crefl_ne {i j : Fin d} (h : j ≠ i) (z : E d) : crefl i z j = z j := by
  rw [crefl_apply, if_neg h]

lemma integral_crefl (i : Fin d) (F : E d → ℝ) : ∫ z, F (crefl i z) = ∫ z, F z :=
  (crefl i).measurePreserving.integral_comp' (f := (crefl i).toMeasurableEquiv) F

lemma chiR_crefl (i : Fin d) (z : E d) : chiR (crefl i z) = chiR z :=
  chiR_of_norm_eq ((crefl i).norm_map z)

variable (i0 i1 : Fin d)

lemma gR_crefl0 (hij : i0 ≠ i1) (z : E d) : gR i0 i1 (crefl i0 z) = -gR i0 i1 z := by
  rw [gR_eq, gR_eq, chiR_crefl, crefl_self, crefl_ne (Ne.symm hij), Real.sign_neg]
  ring

lemma gR_crefl1 (hij : i0 ≠ i1) (z : E d) : gR i0 i1 (crefl i1 z) = -gR i0 i1 z := by
  rw [gR_eq, gR_eq, chiR_crefl, crefl_self, crefl_ne hij, Real.sign_neg]
  ring

/-- Continuous functions times `g` are integrable. -/
lemma integrable_cont_mul_gR {φ : E d → ℝ} (hφ : Continuous φ) :
    Integrable (fun z => φ z * gR i0 i1 z) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E d) 1).exists_bound_of_continuousOn
    hφ.continuousOn
  have hK : IntegrableOn (fun z => φ z * gR i0 i1 z) (Metric.closedBall 0 1) :=
    Integrable.bdd_mul (c := C) (integrable_gR i0 i1).integrableOn hφ.aestronglyMeasurable
      (ae_restrict_of_forall_mem Metric.isClosed_closedBall.measurableSet hC)
  refine hK.integrable_of_forall_notMem_eq_zero (fun z hz => ?_)
  have : 3 / 4 ≤ ‖z‖ := by
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz; linarith
  rw [gR_eq_zero i0 i1 this, mul_zero]

/-! ### The one-dimensional sign lemma -/

lemma rho_even {ρ : ℝ → ℝ} (hρ : ∀ s t, |s| ≤ |t| → ρ t ≤ ρ s) (t : ℝ) : ρ (-t) = ρ t :=
  le_antisymm (hρ _ _ (by rw [abs_neg])) (hρ _ _ (by rw [abs_neg]))

lemma mul_rho_diff_sign_nonneg {ρ : ℝ → ℝ} (hρ : ∀ s t, |s| ≤ |t| → ρ t ≤ ρ s) (y z : ℝ) :
    0 ≤ y * ((ρ (z - y) - ρ (z + y)) * Real.sign z) := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · rw [Real.sign_of_neg hz]
    rcases le_or_gt 0 y with hy | hy
    · have h : ρ (z - y) ≤ ρ (z + y) := hρ _ _ (sq_le_sq.mp (by nlinarith))
      nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
    · have h : ρ (z + y) ≤ ρ (z - y) := hρ _ _ (sq_le_sq.mp (by nlinarith))
      nlinarith [mul_nonneg (le_of_lt (neg_pos.mpr hy)) (sub_nonneg.mpr h)]
  · subst hz; simp
  · rw [Real.sign_of_pos hz]
    rcases le_or_gt 0 y with hy | hy
    · have h : ρ (z + y) ≤ ρ (z - y) := hρ _ _ (sq_le_sq.mp (by nlinarith))
      nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
    · have h : ρ (z - y) ≤ ρ (z + y) := hρ _ _ (sq_le_sq.mp (by nlinarith))
      nlinarith [mul_nonneg (le_of_lt (neg_pos.mpr hy)) (sub_nonneg.mpr h)]

/-! ### The sign of `y_{i₀} y_{i₁} (θ̌ ⋆ g)(y)` for product bumps -/

theorem thConv_gR_sign (hij : i0 ≠ i1) {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hρ : ∀ s t, |s| ≤ |t| → ρ t ≤ ρ s) (y : E d) :
    0 ≤ y i0 * y i1 * thConv (fun x => ∏ j, ρ (x j)) (gR i0 i1) y := by
  set g := gR (d := d) i0 i1
  -- translate
  have htr : thConv (fun x => ∏ j, ρ (x j)) g y = ∫ z, (∏ j, ρ (z j - y j)) * g z := by
    rw [thConv_apply]
    have := integral_sub_right_eq_self (μ := (volume : Measure (E d)))
      (fun x : E d => (∏ j, ρ (x j)) * g (y + x)) y
    rw [← this]
    congr 1
    funext z
    simp only [PiLp.sub_apply, add_sub_cancel]
  rw [htr]
  -- the building blocks
  set S : Finset (Fin d) := (Finset.univ.erase i0).erase i1
  set T : E d → ℝ := fun z => ∏ j ∈ S, ρ (z j - y j) with hT
  set A : E d → ℝ := fun z => ρ (z i0 - y i0) with hA
  set A' : E d → ℝ := fun z => ρ (z i0 + y i0) with hA'
  set B : E d → ℝ := fun z => ρ (z i1 - y i1) with hB
  set B' : E d → ℝ := fun z => ρ (z i1 + y i1) with hB'
  have hcoord : ∀ i : Fin d, Continuous (fun z : E d => z i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).continuous
  have cT : Continuous T := continuous_finset_prod _ fun j _ =>
    hρc.comp ((hcoord j).sub continuous_const)
  have cA : Continuous A := hρc.comp ((hcoord i0).sub continuous_const)
  have cA' : Continuous A' := hρc.comp ((hcoord i0).add continuous_const)
  have cB : Continuous B := hρc.comp ((hcoord i1).sub continuous_const)
  have cB' : Continuous B' := hρc.comp ((hcoord i1).add continuous_const)
  have hi1 : i1 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ i1⟩
  have hprod : ∀ z : E d, (∏ j, ρ (z j - y j)) = A z * (B z * T z) := by
    intro z
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
      ← Finset.mul_prod_erase (Finset.univ.erase i0) _ hi1]
  have hjS : ∀ j ∈ S, j ≠ i0 ∧ j ≠ i1 := fun j hj => by
    simp only [S, Finset.mem_erase] at hj
    exact ⟨hj.2.1, hj.1⟩
  -- reflection facts
  have T0 : ∀ z, T (crefl i0 z) = T z := fun z =>
    Finset.prod_congr rfl fun j hj => by rw [crefl_ne (hjS j hj).1]
  have T1 : ∀ z, T (crefl i1 z) = T z := fun z =>
    Finset.prod_congr rfl fun j hj => by rw [crefl_ne (hjS j hj).2]
  have A0 : ∀ z, A (crefl i0 z) = A' z := fun z => by
    simp only [hA, hA', crefl_self]
    rw [show -z i0 - y i0 = -(z i0 + y i0) by ring, rho_even hρ]
  have B0 : ∀ z, B (crefl i0 z) = B z := fun z => by
    simp only [hB, crefl_ne (Ne.symm hij)]
  have A1 : ∀ z, A (crefl i1 z) = A z := fun z => by simp only [hA, crefl_ne hij]
  have A'1 : ∀ z, A' (crefl i1 z) = A' z := fun z => by simp only [hA', crefl_ne hij]
  have B1 : ∀ z, B (crefl i1 z) = B' z := fun z => by
    simp only [hB, hB', crefl_self]
    rw [show -z i1 - y i1 = -(z i1 + y i1) by ring, rho_even hρ]
  have g0 : ∀ z, g (crefl i0 z) = -g z := gR_crefl0 i0 i1 hij
  have g1 : ∀ z, g (crefl i1 z) = -g z := gR_crefl1 i0 i1 hij
  -- integrability
  have I1 : Integrable (fun z => A z * B z * T z * g z) :=
    integrable_cont_mul_gR i0 i1 ((cA.mul cB).mul cT)
  have I1' : Integrable (fun z => A' z * B z * T z * g z) :=
    integrable_cont_mul_gR i0 i1 ((cA'.mul cB).mul cT)
  have I2 : Integrable (fun z => (A z - A' z) * B z * T z * g z) :=
    integrable_cont_mul_gR i0 i1 (((cA.sub cA').mul cB).mul cT)
  have I2' : Integrable (fun z => (A z - A' z) * B' z * T z * g z) :=
    integrable_cont_mul_gR i0 i1 (((cA.sub cA').mul cB').mul cT)
  -- first reflection
  have e1 : ∫ z, A z * B z * T z * g z = -∫ z, A' z * B z * T z * g z := by
    rw [← integral_crefl i0 (fun z => A z * B z * T z * g z), ← integral_neg]
    congr 1
    funext z
    rw [A0, B0, T0, g0]
    ring
  have e2 : ∫ z, (A z - A' z) * B z * T z * g z =
      (∫ z, A z * B z * T z * g z) - ∫ z, A' z * B z * T z * g z := by
    calc ∫ z, (A z - A' z) * B z * T z * g z
        = ∫ z, (A z * B z * T z * g z - A' z * B z * T z * g z) := by
          congr 1; funext z; ring
      _ = _ := integral_sub I1 I1'
  -- second reflection
  have e3 : ∫ z, (A z - A' z) * B z * T z * g z = -∫ z, (A z - A' z) * B' z * T z * g z := by
    rw [← integral_crefl i1 (fun z => (A z - A' z) * B z * T z * g z), ← integral_neg]
    congr 1
    funext z
    rw [A1, A'1, B1, T1, g1]
    ring
  have e4 : ∫ z, (A z - A' z) * (B z - B' z) * T z * g z =
      (∫ z, (A z - A' z) * B z * T z * g z) - ∫ z, (A z - A' z) * B' z * T z * g z := by
    calc ∫ z, (A z - A' z) * (B z - B' z) * T z * g z
        = ∫ z, ((A z - A' z) * B z * T z * g z - (A z - A' z) * B' z * T z * g z) := by
          congr 1; funext z; ring
      _ = _ := integral_sub I2 I2'
  have hmain : ∫ z, (∏ j, ρ (z j - y j)) * g z =
      (1 / 4) * ∫ z, (A z - A' z) * (B z - B' z) * T z * g z := by
    have : ∫ z, (∏ j, ρ (z j - y j)) * g z = ∫ z, A z * B z * T z * g z := by
      congr 1; funext z; rw [hprod]; ring
    rw [this]
    linarith [e1, e2, e3, e4]
  rw [hmain, ← mul_assoc, mul_comm (y i0 * y i1) (1 / 4), mul_assoc, ← integral_const_mul]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro z
  have k0 := mul_rho_diff_sign_nonneg hρ (y i0) (z i0)
  have k1 := mul_rho_diff_sign_nonneg hρ (y i1) (z i1)
  have hT0 : 0 ≤ T z := Finset.prod_nonneg fun j _ => hρ0 _
  have e : y i0 * y i1 * ((A z - A' z) * (B z - B' z) * T z * g z) =
      (y i0 * ((ρ (z i0 - y i0) - ρ (z i0 + y i0)) * Real.sign (z i0))) *
      (y i1 * ((ρ (z i1 - y i1) - ρ (z i1 + y i1)) * Real.sign (z i1))) * (T z * chiR z) := by
    simp only [g, gR_eq, hA, hA', hB, hB']
    ring
  show 0 ≤ y i0 * y i1 * ((A z - A' z) * (B z - B' z) * T z * g z)
  rw [e]
  exact mul_nonneg (mul_nonneg k0 k1) (mul_nonneg hT0 (chiR_nonneg z))

/-! ### The product bump -/

def rhoB (r t : ℝ) : ℝ := Real.smoothTransition (1 - t ^ 2 / r ^ 2)

lemma contDiff_rhoB (r : ℝ) : ContDiff ℝ ∞ (rhoB r) := by
  unfold rhoB
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp
    (contDiff_const.sub ((contDiff_id.pow 2).div_const _))

lemma rhoB_nonneg (r t : ℝ) : 0 ≤ rhoB r t := Real.smoothTransition.nonneg _

lemma rhoB_anti {r : ℝ} (hr : 0 < r) (s t : ℝ) (h : |s| ≤ |t|) : rhoB r t ≤ rhoB r s := by
  unfold rhoB
  apply Real.smoothTransition.monotone
  have h2 : s ^ 2 ≤ t ^ 2 := sq_le_sq.mpr h
  have : s ^ 2 / r ^ 2 ≤ t ^ 2 / r ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
  linarith

lemma rhoB_eq_zero {r t : ℝ} (hr : 0 < r) (ht : r ≤ |t|) : rhoB r t = 0 := by
  unfold rhoB
  apply Real.smoothTransition.zero_of_nonpos
  have h2 : r ^ 2 ≤ t ^ 2 := by
    have := pow_le_pow_left₀ hr.le ht 2
    rwa [sq_abs] at this
  have : 1 ≤ t ^ 2 / r ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma rhoB_zero (r : ℝ) : rhoB r 0 = 1 := by
  unfold rhoB
  simp [Real.smoothTransition.one]

/-- The product bump `θ_r(x) = ∏ⱼ ρ_r(x_j)`. -/
def thB (r : ℝ) (x : E d) : ℝ := ∏ j, rhoB r (x j)

lemma contDiff_thB (r : ℝ) : ContDiff ℝ ∞ (thB (d := d) r) :=
  contDiff_prod fun j _ => (contDiff_rhoB r).comp
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) j).contDiff

lemma thB_nonneg (r : ℝ) (x : E d) : 0 ≤ thB r x :=
  Finset.prod_nonneg fun j _ => rhoB_nonneg r _

lemma coord_lt_of_thB_ne_zero {r : ℝ} (hr : 0 < r) {x : E d} (hx : thB r x ≠ 0) (j : Fin d) :
    |x j| < r := by
  by_contra h
  push_neg at h
  exact hx (Finset.prod_eq_zero (Finset.mem_univ j) (rhoB_eq_zero hr h))

lemma norm_lt_of_thB_ne_zero {r : ℝ} (hr : 0 < r) (hd : 1 ≤ d) {x : E d} (hx : thB r x ≠ 0) :
    ‖x‖ < r * √d := by
  have hc := coord_lt_of_thB_ne_zero hr hx
  have h2 : ‖x‖ ^ 2 < (r * √d) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    calc ∑ j, x j ^ 2 < ∑ _j : Fin d, r ^ 2 :=
          Finset.sum_lt_sum_of_nonempty hne fun j _ => by
            have := hc j
            have h0 := abs_nonneg (x j)
            rw [← sq_abs]; nlinarith
      _ = r ^ 2 * d := by simp [Finset.sum_const, Finset.card_univ]; ring
  have : 0 ≤ r * √d := by positivity
  nlinarith [norm_nonneg x]

lemma tsupport_thB {r : ℝ} (hr : 0 < r) (hd : 1 ≤ d) :
    tsupport (thB (d := d) r) ⊆ Metric.closedBall 0 (r * √d) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (norm_lt_of_thB_ne_zero hr hd hx).le

lemma hasCompactSupport_thB {r : ℝ} (hr : 0 < r) (hd : 1 ≤ d) :
    HasCompactSupport (thB (d := d) r) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 _)
    ((subset_tsupport _).trans (tsupport_thB hr hd))

lemma thB_zero (r : ℝ) : thB (d := d) r 0 = 1 := by
  simp [thB, rhoB_zero]

lemma integral_thB_pos {r : ℝ} (hr : 0 < r) (hd : 1 ≤ d) : 0 < ∫ x, thB (d := d) r x :=
  (contDiff_thB r).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_thB hr hd) (fun x => thB_nonneg r x) (x := 0) (by rw [thB_zero]; norm_num)

/-- `θ̌_r ⋆ g = ∫ θ_r` on the dyadic boxes of size `a ≥ r`. -/
lemma thConv_thB_box (hij : i0 ≠ i1) {r a : ℝ} (hr : 0 < r) (hd : 1 ≤ d) (hra : r ≤ a)
    (ha : a ≤ 1 / 8) (hrd : r * √d ≤ 1 / 8) {y : E d} (hy : y ∈ dbox i0 i1 a) :
    thConv (thB r) (gR i0 i1) y = ∫ x, thB (d := d) r x := by
  have ha0 : 0 < a := lt_of_lt_of_le hr hra
  have hny := norm_sq_le_of_mem_dbox i0 i1 hij ha0 hy
  obtain ⟨h1, -, h3, -, -⟩ := hy
  rw [thConv_apply]
  congr 1
  funext x
  by_cases hx : thB r x = 0
  · rw [hx, zero_mul]
  · have hc0 := coord_lt_of_thB_ne_zero hr hx i0
    have hc1 := coord_lt_of_thB_ne_zero hr hx i1
    have hnx := norm_lt_of_thB_ne_zero hr hd hx
    have hp0 : 0 < (y + x) i0 := by
      rw [PiLp.add_apply]; have := neg_abs_le (x i0); linarith
    have hp1 : 0 < (y + x) i1 := by
      rw [PiLp.add_apply]; have := neg_abs_le (x i1); linarith
    have hn : ‖y + x‖ ≤ 1 / 2 := by
      have := norm_add_le y x
      linarith
    rw [gR, chiR_eq_one hn, Real.sign_of_pos (mul_pos hp0 hp1)]
    ring

/-! ### Remark 4.2 -/

/-- `D_v² f ∉ L^∞_loc` for `f = 𝒮g`, `g = χ sgn(x₁x₂)`. -/
theorem not_hessVLinfLoc_gR (hd : 2 ≤ d) :
    ¬ HessVLinfLoc (solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ))) := by
  intro hL
  have hd1 : 1 ≤ d := by omega
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨M, hM⟩ := hessV_bound_of_linfLoc hd1 (measurable_gR i0 i1) (K := 1) (abs_gR_le i0 i1)
    (fun y hy => gR_eq_zero i0 i1 (by linarith)) i0 i1 hL
  set c := cbox d / (4 * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := div_pos (cbox_pos hd1) (by positivity)
  set L := (max M 0 + 1) / c
  set r := min (1 / (16 * (√d + 1))) (Real.exp (-L)) with hrdef
  have hsd : 0 ≤ √(d : ℝ) := Real.sqrt_nonneg _
  have hr : 0 < r := lt_min (by positivity) (Real.exp_pos _)
  have hr1 : r ≤ 1 / (16 * (√d + 1)) := min_le_left _ _
  have hrd : r * √d ≤ 1 / 16 := by
    have h16 : 0 < 16 * (√(d : ℝ) + 1) := by positivity
    calc r * √d ≤ 1 / (16 * (√d + 1)) * √d := mul_le_mul_of_nonneg_right hr1 hsd
      _ ≤ 1 / 16 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ h16 (by norm_num)]
          nlinarith
  have hr10 : r < 1 / 10 := by
    have : 1 / (16 * (√(d : ℝ) + 1)) ≤ 1 / 16 := by
      apply div_le_div_of_nonneg_left zero_le_one (by norm_num); nlinarith
    linarith
  have hrL : L ≤ Real.log (1 / r) := by
    have h1 : r ≤ Real.exp (-L) := min_le_right _ _
    have h2 := Real.log_le_log hr h1
    rw [Real.log_exp] at h2
    rw [one_div, Real.log_inv]; linarith
  -- the normalized bump
  set I := ∫ x, thB (d := d) r x
  have hI : 0 < I := integral_thB_pos hr hd1
  set θ : E d → ℝ := fun x => thB r x / I with hθdef
  have hθ : ContDiff ℝ ∞ θ := (contDiff_thB r).div_const I
  have hsupp : Function.support θ ⊆ Function.support (thB (d := d) r) := fun x hx => by
    simp only [Function.mem_support, hθdef] at hx ⊢
    intro h; apply hx; rw [h, zero_div]
  have hθc : HasCompactSupport θ :=
    (hasCompactSupport_thB hr hd1).mono' (hsupp.trans (subset_tsupport _))
  have hθ0 : ∀ x, 0 ≤ θ x := fun x => div_nonneg (thB_nonneg r x) hI.le
  have hθs : tsupport θ ⊆ Metric.closedBall 0 1 := by
    have : tsupport θ ⊆ tsupport (thB (d := d) r) := closure_mono hsupp
    refine this.trans ((tsupport_thB hr hd1).trans (Metric.closedBall_subset_closedBall ?_))
    linarith
  have hθI : ∫ x, θ x = 1 := by
    simp only [hθdef]
    rw [integral_div, div_self hI.ne']
  have hconv : ∀ y, thConv θ (gR i0 i1) y = thConv (thB r) (gR i0 i1) y / I := by
    intro y
    rw [thConv_apply, thConv_apply, ← integral_div]
    congr 1; funext x; simp only [hθdef]; ring
  -- the smoothed forcing
  set h := thConv θ (gR i0 i1)
  have hh : ContDiff ℝ ∞ h := contDiff_thConv hθ hθc (measurable_gR i0 i1) (abs_gR_le i0 i1)
    (fun y hy => gR_eq_zero i0 i1 (by linarith))
  have hhc : HasCompactSupport h :=
    hasCompactSupport_thConv hθc (fun y hy => gR_eq_zero i0 i1 (by linarith))
  have hP0 : ∀ y : E d, 0 ≤ y i0 * y i1 * h y := by
    intro y
    have := thConv_gR_sign i0 i1 hij (contDiff_rhoB r).continuous (rhoB_nonneg r)
      (rhoB_anti hr) y
    rw [hconv, mul_div_assoc']
    exact div_nonneg this hI.le
  have hbox : ∀ a : ℝ, r ≤ a → a ≤ 1 / 8 → ∀ y ∈ dbox (d := d) i0 i1 a,
      y i0 * y i1 ≤ y i0 * y i1 * h y := by
    intro a hra ha y hy
    rw [hconv, thConv_thB_box i0 i1 hij hr hd1 hra ha (by linarith) hy, div_self hI.ne', mul_one]
  have hlow := hess_ge_of_P hd hh hhc hP0 hr hr10 hbox 0
  have hup := hM θ hθ hθc hθ0 hθs
  rw [hθI, mul_one] at hup
  have h1 : c * L ≤ c * Real.log (1 / r) := mul_le_mul_of_nonneg_left hrL hc.le
  have h2 : c * L = max M 0 + 1 := by simp only [L]; field_simp
  have h3 := (le_abs_self _).trans hup
  have h4 := le_max_left M 0
  linarith

/-- **Remark 4.2** (Dong–Wang). For `d ≥ 2`, the radial cutoff `χ` (`χ ∈ C_c^∞(B₁)`, `0 ≤ χ ≤ 1`,
`χ = 1` on `B_{1/2}`), `g = χ sgn(x₁x₂)` and `f = 𝒮g`: `g ∈ L^∞ ∩ L¹`, `f ∈ L^∞` is stationary,
`(∂_t + v·∇_x) f = Δ_v f + g` holds in the sense of distributions, and `D_v² f ∉ L^∞_loc`. -/
theorem rem_4_2 (d : ℕ) (hd : 2 ≤ d) :
    -- the cutoff
    (ContDiff ℝ ∞ (chiR (d := d)) ∧ HasCompactSupport (chiR (d := d)) ∧
      tsupport (chiR (d := d)) ⊆ Metric.ball 0 1 ∧ (∀ x : E d, 0 ≤ chiR x ∧ chiR x ≤ 1) ∧
      ∀ x : E d, ‖x‖ ≤ 1 / 2 → chiR x = 1) ∧
    -- `g = χ sgn(x₁ x₂) ∈ L^∞ ∩ L¹`
    (∀ x : E d, gR ⟨0, by omega⟩ ⟨1, by omega⟩ x =
      chiR x * Real.sign (x ⟨0, by omega⟩ * x ⟨1, by omega⟩)) ∧
    Integrable (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
    (∀ x : E d, |gR ⟨0, by omega⟩ ⟨1, by omega⟩ x| ≤ 1) ∧
    -- `f = 𝒮g`
    (∀ t t' x v, solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ)) (t, x, v) =
      solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ)) (t', x, v)) ∧
    (∃ C : ℝ, ∀ p, |solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ)) p| ≤ C) ∧
    IsDistribSol (solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ)))
      (fun p => gR ⟨0, by omega⟩ ⟨1, by omega⟩ p.2.1) ∧
    ¬ HessVLinfLoc (solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ))) := by
  have hd1 : 1 ≤ d := by omega
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have happrox := isDistribSol_of_approx hd1 (g := gR i0 i1) (gn := fun n => gRn i0 i1 n) (K := 1)
    (fun n => contDiff_gRn i0 i1 n) (fun n => hasCompactSupport_gRn i0 i1 n)
    (fun n y => abs_gRn_le i0 i1 n y) (fun n y hy => gRn_eq_zero i0 i1 n (by linarith))
    (Eventually.of_forall fun y => tendsto_gRn i0 i1 y)
  exact ⟨⟨contDiff_chiR, hasCompactSupport_chiR, tsupport_chiR_ball,
      fun x => ⟨chiR_nonneg x, chiR_le_one x⟩, fun x hx => chiR_eq_one hx⟩,
    fun x => rfl, integrable_gR i0 i1, abs_gR_le i0 i1, solF_stationary _, ⟨_, happrox.2⟩,
    happrox.1, not_hessVLinfLoc_gR hd⟩

/-! ### `∂_{v₁v₂} f(·,0) = ∂_{x₁x₂}(-Δ_x)^{-1} g` in the sense of distributions -/

/-- `∫₀^∞ s² F(s³/3) ds = ∫₀^∞ F(τ) dτ`. -/
lemma integral_s_tau (F : ℝ → ℝ) :
    ∫ s in Ioi (0 : ℝ), s ^ 2 * F (s ^ 3 / 3) = ∫ τ in Ioi (0 : ℝ), F τ := by
  have h1 := integral_comp_rpow_Ioi_of_pos (g := fun y => F (y / 3) / 3) (p := 3) (by norm_num)
  have h2 : ∫ x in Ioi (0 : ℝ), ((3 : ℝ) * x ^ ((3 : ℝ) - 1)) • (fun y => F (y / 3) / 3) (x ^ (3 : ℝ)) =
      ∫ s in Ioi (0 : ℝ), s ^ 2 * F (s ^ 3 / 3) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have e2 : x ^ ((3 : ℝ) - 1) = x ^ 2 := by
      rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e3 : x ^ (3 : ℝ) = x ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [smul_eq_mul, e2, e3]
    ring
  have h3 : ∫ y in Ioi (0 : ℝ), F (y / 3) / 3 = ∫ τ in Ioi (0 : ℝ), F τ := by
    have := integral_comp_mul_left_Ioi F 0 (b := 1 / 3) (by norm_num)
    rw [mul_zero, smul_eq_mul] at this
    rw [integral_div]
    have e : (fun y : ℝ => F (y / 3)) = fun y => F (1 / 3 * y) := by
      funext y; congr 1; ring
    rw [e, this]
    ring
  rw [← h2, h1, h3]

/-- **Remark 4.2, the Riesz-transform identity.** For every test function `θ ∈ C_c^∞(ℝᵈ)`, the
pairing `v ↦ ∫ θ(x) f(t,x,v) dx` is smooth and its mixed derivative at `v = 0` is
`∫₀^∞ ∂_{x₁x₂} P_τ (θ̌ ⋆ g)(0) dτ = ⟨∂_{x₁x₂}(-Δ_x)^{-1} g, θ⟩` (the heat-semigroup form of the
second-order Riesz transform; here `∂_{x₁x₂} P_τ h(0) = ∫ ∂₁∂₂G_τ(y) h(y) dy`). -/
theorem rem_4_2_riesz (hd : 2 ≤ d) {θ : E d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (t : ℝ) :
    ContDiff ℝ ∞ (fun v => ∫ x, θ x *
      solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ)) (t, x, v)) ∧
    fderiv ℝ (fun w => fderiv ℝ (fun w' => ∫ x, θ x *
        solF (fun y => (gR (d := d) ⟨0, by omega⟩ ⟨1, by omega⟩ y : ℂ)) (t, x, w')) w
        (ev ⟨1, by omega⟩)) 0 (ev ⟨0, by omega⟩) =
      ∫ τ in Ioi (0 : ℝ), ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d τ) z (ev ⟨0, by omega⟩)) y
        (ev ⟨1, by omega⟩) * thConv θ (gR ⟨0, by omega⟩ ⟨1, by omega⟩) y := by
  have hd1 : 1 ≤ d := by omega
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  set g := gR (d := d) i0 i1
  have hθi : Integrable θ := hθ.continuous.integrable_of_hasCompactSupport hθc
  have hs : ∀ y : E d, 1 ≤ ‖y‖ → g y = 0 := fun y hy => gR_eq_zero i0 i1 (by linarith)
  set h := thConv θ g
  have hh : ContDiff ℝ ∞ h := contDiff_thConv hθ hθc (measurable_gR i0 i1) (abs_gR_le i0 i1) hs
  have hhc : HasCompactSupport h := hasCompactSupport_thConv hθc hs
  have e : (fun v => ∫ x, θ x * solF (fun y => (g y : ℂ)) (t, x, v)) =
      fun v => solF (fun y => (h y : ℂ)) (0, 0, v) := by
    funext v
    exact integral_theta_solF hd1 hθi (measurable_gR i0 i1) (abs_gR_le i0 i1) hs t v
  have hsm : ContDiff ℝ ∞ (solF (fun y => (h y : ℂ))) := by
    rw [← coe_toS h hh hhc]; exact solF_smooth hd1 _
  refine ⟨?_, ?_⟩
  · rw [e]
    exact hsm.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  · rw [e]
    have hv := (hessV_solF_phys hd1 h hh hhc 0 i0 i1).2
    have hdef : hessV (solF (fun y => (h y : ℂ))) (0, 0, 0) i0 i1 =
        fderiv ℝ (fun w => fderiv ℝ (fun w' => solF (fun y => (h y : ℂ)) (0, 0, w')) w (ev i1))
          0 (ev i0) := rfl
    rw [← hdef, hv]
    exact integral_s_tau (fun τ => ∫ y, fderiv ℝ (fun z => fderiv ℝ (hk d τ) z (ev i0)) y
      (ev i1) * h y)

end KS

end -- (the file's `noncomputable section`)

end File_Endpoint_Rem42

-- ============================================================================
-- Axiom audit
-- ============================================================================

-- the one-dimensional profile (Section 2)
#print axioms KS.Jn_two_zero
#print axioms KS.Jn_two_sub
#print axioms KS.tendsto_Jn_two
#print axioms KS.IN_eq
#print axioms KS.C0_eq_Gamma
-- Sections 1–3
#print axioms KS.fN_solves
#print axioms KS.thm_2_1
#print axioms KS.thm_2_1_explicit
#print axioms KS.conj11_false
#print axioms KS.rem_2_2
#print axioms KS.prop_3_1
#print axioms KS.conj11_zero_false
#print axioms KS.semX_gN
-- Section 4: the solution operator and its properties
#print axioms KS.contDiff_kinF
#print axioms KS.kin_eq_kinF
#print axioms KS.kinF_equation
#print axioms KS.solF_smooth
#print axioms KS.solF_KFP
#print axioms KS.abs_solF_le
#print axioms KS.hess0_kinF_lap
#print axioms KS.hessV_solF_phys
#print axioms KS.kerK_integral
#print axioms KS.ofReal_integral_kerK
#print axioms KS.lintegral_ge_card
#print axioms KS.hess_gEps_ge
#print axioms KS.isDistribSol_of_KFP
#print axioms KS.isDistribSol_of_approx
#print axioms KS.integral_theta_solF
#print axioms KS.hessV_bound_of_linfLoc
#print axioms KS.fderiv2_thConv_apply
#print axioms KS.lap_U
#print axioms KS.mixed_U_ge
#print axioms KS.exists_bound_gU
#print axioms KS.continuous_gU0
#print axioms KS.lap_thConv_u
#print axioms KS.not_hessVLinfLoc
#print axioms KS.thConv_gR_sign
#print axioms KS.hess_ge_of_P
#print axioms KS.not_hessVLinfLoc_gR
-- Section 4: the main statements
#print axioms KS.thm_4_1
#print axioms KS.rem_4_2
#print axioms KS.rem_4_2_riesz
#print axioms KS.thm_4_3_i
#print axioms KS.thm_4_3_ii
