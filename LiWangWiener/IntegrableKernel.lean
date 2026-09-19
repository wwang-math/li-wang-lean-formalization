/-
# Integrable torus kernels and the physical velocity operator

Two independent generalizations of the v2.0 physical layer.

**(A) Admissible symbols instead of Wiener kernels.**  `kernelConv`, `kernelConvDeriv`, the
rotated-gradient velocity identities and physical divergence freedom were stated for a kernel
`K : Wiener1`.  Only the *weighted* coefficient bound `KernelBound κ A` is ever used, so all of
them are re-proved for an arbitrary admissible coefficient law `κ`, and the old statements are
recovered as the special case `κ = K.coeff` (with `A = ‖K‖`).

**(B) Genuinely integrable kernels.**  For `K : 𝕋² → ℂ` integrable for the normalised Haar
measure we define the *actual* Fourier coefficients `κ(k) = ∫ K(y) e_{-k}(y) dy` and the
*actual* convolution integral `(K * F)(x) = ∫ K(y) F(x-y) dy`, and prove that convolution with
`K` is exactly the Fourier multiplier by `κ` on synthesized Wiener states.  The exchange of
the synthesis series with the integral is justified by the fact that the synthesis series
converges in the uniform norm while `F ↦ ∫ K(y) F(x-y) dy` is a bounded functional of norm at
most `‖K‖_{L¹}`; no smoothness of `K` is used anywhere.

Differentiation of the velocity field is carried out **in the state variable**: the derivative
of `K * u` along a circle direction is `K * ∂ⱼu`, proved from the multiplier identity and the
torus differentiation transfer theorem, so the (possibly singular) kernel is never
differentiated.

What is **not** proved here: the paper's punctured smoothness and the two-sided Fourier
ellipticity lower bound at every nonzero frequency.  Those are recorded as explicit named
hypotheses in the last section and are *assumptions*, not conclusions.

Part of `LiWangWienerSourceResponsePacket` v3.0.
-/
import LiWangWiener.TorusDerivative
import LiWangWiener.PhysicalTransport
import LiWangWiener.Coefficients
import LiWangWiener.FractionalHeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.WienerModel

/-! ## (A) Velocity fields of a general admissible coefficient law -/

theorem norm_le_of_kernelBound {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (k : Gam) :
    ‖κ k‖ ≤ A :=
  le_trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_wt k)) (hA k)

theorem summable_symbolConv {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1) :
    Summable fun k => wt k * ‖κ k * u.coeff k‖ := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => ?_) (u.summable_wt.mul_left A)
  rw [norm_mul]
  calc wt k * (‖κ k‖ * ‖u.coeff k‖) = ‖κ k‖ * (wt k * ‖u.coeff k‖) := by ring
    _ ≤ A * (wt k * ‖u.coeff k‖) :=
        mul_le_mul_of_nonneg_right (norm_le_of_kernelBound hA k)
          (mul_nonneg (wt_pos k).le (norm_nonneg _))

/-- The Fourier realization of `κ ∗ u` for an admissible coefficient law `κ`. -/
noncomputable def symbolConv {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1) :
    Wiener1 :=
  Wiener1.mk (fun k => κ k * u.coeff k) (summable_symbolConv hA u)

@[simp] theorem symbolConv_coeff {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1)
    (k : Gam) : (symbolConv hA u).coeff k = κ k * u.coeff k := rfl

/-- Compatibility with the v2.0 Wiener-kernel convolution. -/
theorem symbolConv_eq_kernelConv (K u : Wiener1) :
    symbolConv (K.kernelBound) u = kernelConv K u :=
  Wiener1.coeff_injective rfl

theorem summable_symbolConvDeriv {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1)
    (j : Fin 2) :
    Summable fun k => wt k * ‖twoPiI * ((k j : ℤ) : ℂ) * (κ k * u.coeff k)‖ := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => ?_) ((u.summable_wt.mul_left A).mul_left (2 * Real.pi))
  simp only [norm_mul, norm_twoPiI, Complex.norm_intCast]
  have h1 : |((k j : ℤ) : ℝ)| ≤ wt k := abs_coe_le_wt j k
  have hKn : (0:ℝ) ≤ ‖κ k‖ := norm_nonneg _
  have hstep : |((k j : ℤ) : ℝ)| * ‖κ k‖ ≤ A :=
    le_trans (mul_le_mul_of_nonneg_right h1 hKn) (hA k)
  have hpi := twoPi_nonneg
  have hwu : (0:ℝ) ≤ wt k * ‖u.coeff k‖ := by
    exact mul_nonneg (wt_pos k).le (norm_nonneg _)
  calc wt k * (2 * Real.pi * |((k j : ℤ) : ℝ)| * (‖κ k‖ * ‖u.coeff k‖))
      = 2 * Real.pi * (|((k j : ℤ) : ℝ)| * ‖κ k‖) * (wt k * ‖u.coeff k‖) := by ring
    _ ≤ 2 * Real.pi * A * (wt k * ‖u.coeff k‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hpi) hwu
    _ = 2 * Real.pi * (A * (wt k * ‖u.coeff k‖)) := by ring

/-- `∂ⱼ(κ ∗ u)` as an element of the first-order space: the weighted bound on `κ` buys the
extra derivative, no membership of `κ` in the Wiener algebra is needed. -/
noncomputable def symbolConvDeriv {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1)
    (j : Fin 2) : Wiener1 :=
  Wiener1.mk (fun k => twoPiI * ((k j : ℤ) : ℂ) * (κ k * u.coeff k))
    (summable_symbolConvDeriv hA u j)

@[simp] theorem symbolConvDeriv_coeff {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1)
    (j : Fin 2) (k : Gam) :
    (symbolConvDeriv hA u j).coeff k = twoPiI * ((k j : ℤ) : ℂ) * (κ k * u.coeff k) := rfl

theorem symbolConvDeriv_eq_kernelConvDeriv (K u : Wiener1) (j : Fin 2) :
    symbolConvDeriv (K.kernelBound) u j = kernelConvDeriv K u j :=
  Wiener1.coeff_injective rfl

theorem incl_symbolConvDeriv {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1)
    (j : Fin 2) : incl (symbolConvDeriv hA u j) = fourierDeriv j (symbolConv hA u) := by
  ext k; rfl

/-- **`R_κ(u)₀ = -∂₂(κ ∗ u)` for an arbitrary admissible coefficient law.** -/
theorem velocity_eq_symbolConvDeriv_zero {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A)
    (u : Wiener1) :
    velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd ⟨A, hA⟩) 0 (incl u)
      = incl (-(symbolConvDeriv hA u 1)) := by
  ext k
  show rotatedGradientSymbol κ 0 k * (incl u) k
      = -(twoPiI * ((k 1 : ℤ) : ℂ) * (κ k * u.coeff k))
  show (-twoPiI * ((k 1 : ℤ) : ℂ) * κ k) * u.coeff k
      = -(twoPiI * ((k 1 : ℤ) : ℂ) * (κ k * u.coeff k))
  ring

/-- **`R_κ(u)₁ = ∂₁(κ ∗ u)` for an arbitrary admissible coefficient law.** -/
theorem velocity_eq_symbolConvDeriv_one {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A)
    (u : Wiener1) :
    velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd ⟨A, hA⟩) 1 (incl u)
      = incl (symbolConvDeriv hA u 0) := by
  ext k
  show rotatedGradientSymbol κ 1 k * (incl u) k
      = twoPiI * ((k 0 : ℤ) : ℂ) * (κ k * u.coeff k)
  show (twoPiI * ((k 0 : ℤ) : ℂ) * κ k) * u.coeff k
      = twoPiI * ((k 0 : ℤ) : ℂ) * (κ k * u.coeff k)
  ring

/-- Divergence freedom of the velocity field of an admissible coefficient law, as an identity
of Fourier states. -/
theorem div_velocity_symbol_eq_zero {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1) :
    fourierDeriv 0 (-(symbolConvDeriv hA u 1)) + fourierDeriv 1 (symbolConvDeriv hA u 0) = 0 := by
  ext k
  show twoPiI * ((k 0 : ℤ) : ℂ) * ((-(symbolConvDeriv hA u 1)).coeff k)
      + twoPiI * ((k 1 : ℤ) : ℂ) * ((symbolConvDeriv hA u 0).coeff k) = 0
  show twoPiI * ((k 0 : ℤ) : ℂ) * (-(twoPiI * ((k 1 : ℤ) : ℂ) * (κ k * u.coeff k)))
      + twoPiI * ((k 1 : ℤ) : ℂ) * (twoPiI * ((k 0 : ℤ) : ℂ) * (κ k * u.coeff k)) = 0
  ring

/-- **Actual physical differentiability of the velocity components** of an admissible
coefficient law: each component is differentiable along each circle direction at every point
of the torus, and the derivative is the synthesis of the corresponding Fourier derivative. -/
theorem hasDerivAt_synth_symbol_velocity {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A)
    (u : Wiener1) (x : Torus2) (i j : Fin 2) :
    HasDerivAt (fun s : ℝ => synth (incl (symbolConvDeriv hA u j)) (torusShift x i s))
      (synth (fourierDeriv i (symbolConvDeriv hA u j)) x) 0 :=
  hasDerivAt_synth_torus (symbolConvDeriv hA u j) x i

/-- **Physical divergence freedom on the torus for an arbitrary admissible coefficient law.**
The `K : Wiener1` restriction of v2.0 is unnecessary. -/
theorem div_synth_velocity_symbol_eq_zero {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A)
    (u : Wiener1) (x : Torus2) :
    deriv (fun s : ℝ => synth (incl (-(symbolConvDeriv hA u 1))) (torusShift x 0 s)) 0
      + deriv (fun s : ℝ => synth (incl (symbolConvDeriv hA u 0)) (torusShift x 1 s)) 0 = 0 := by
  rw [deriv_synth_torus, deriv_synth_torus]
  have h : synth (fourierDeriv 0 (-(symbolConvDeriv hA u 1)))
      + synth (fourierDeriv 1 (symbolConvDeriv hA u 0)) = 0 := by
    rw [← map_add, div_velocity_symbol_eq_zero, map_zero]
  have hx := congrArg (fun F : C(Torus2, ℂ) => F x) h
  simpa using hx

/-! ## (B) Genuinely integrable kernels: actual Fourier coefficients -/

section IntegrableKernels

variable {K : Torus2 → ℂ}

theorem integrable_kernel_mul_emode (hK : Integrable K (volume : Measure Torus2)) (k : Gam) :
    Integrable (fun y : Torus2 => K y * emode k y) (volume : Measure Torus2) :=
  hK.mul_bdd (c := 1) (emode k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => le_of_eq (norm_emode_apply k y))

/-- The **actual Fourier coefficients** of an integrable kernel:
`κ(k) = ∫_{𝕋²} K(y) e_{-k}(y) dy`. -/
noncomputable def kernelCoeff (K : Torus2 → ℂ) (k : Gam) : ℂ :=
  ∫ y : Torus2, K y * emode (-k) y

/-- Every Fourier coefficient of an integrable kernel is bounded by its `L¹` norm; in
particular the zero coefficient is finite. -/
theorem norm_kernelCoeff_le (hK : Integrable K (volume : Measure Torus2)) (k : Gam) :
    ‖kernelCoeff K k‖ ≤ ∫ y : Torus2, ‖K y‖ := by
  have h1 : ‖kernelCoeff K k‖ ≤ ∫ y : Torus2, ‖K y * emode (-k) y‖ :=
    norm_integral_le_integral_norm _
  have h2 : (∫ y : Torus2, ‖K y * emode (-k) y‖) = ∫ y : Torus2, ‖K y‖ :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [norm_mul, norm_emode_apply, mul_one])
  rwa [h2] at h1

theorem kernelCoeff_bdd (hK : Integrable K (volume : Measure Torus2)) :
    ∃ M : ℝ, ∀ k, ‖kernelCoeff K k‖ ≤ M :=
  ⟨_, norm_kernelCoeff_le hK⟩

/-- Reality: a real integrable kernel has conjugate-symmetric Fourier coefficients. -/
theorem kernelCoeff_conjSymmetric {K : Torus2 → ℝ}
    (hK : Integrable (fun y : Torus2 => ((K y : ℝ) : ℂ)) (volume : Measure Torus2)) :
    ConjSymmetric (kernelCoeff fun y : Torus2 => ((K y : ℝ) : ℂ)) := by
  intro k
  have hc : (∫ y : Torus2, conj (((K y : ℝ) : ℂ) * emode (-k) y))
      = ∫ y : Torus2, ((K y : ℝ) : ℂ) * emode k y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show conj (((K y : ℝ) : ℂ) * emode (-k) y) = ((K y : ℝ) : ℂ) * emode k y
    rw [map_mul, Complex.conj_ofReal, emode_neg_apply, Complex.conj_conj]
  have hconj : conj (kernelCoeff (fun y : Torus2 => ((K y : ℝ) : ℂ)) k)
      = ∫ y : Torus2, conj (((K y : ℝ) : ℂ) * emode (-k) y) :=
    (integral_conj (μ := (volume : Measure Torus2))
      (f := fun y : Torus2 => ((K y : ℝ) : ℂ) * emode (-k) y)).symm
  show kernelCoeff (fun y : Torus2 => ((K y : ℝ) : ℂ)) (-k)
      = conj (kernelCoeff (fun y : Torus2 => ((K y : ℝ) : ℂ)) k)
  rw [hconj, hc, kernelCoeff, neg_neg]

/-! ### The convolution integral -/

/-- The Fourier monomials split a difference of circle points. -/
theorem fourier_sub_point {T : ℝ} (n : ℤ) (a b : AddCircle T) :
    fourier n (a - b) = fourier n a * fourier (-n) b := by
  have h : (n • (a - b) : AddCircle T) = n • a + (-n) • b := by
    rw [smul_sub, neg_smul]; abel
  rw [fourier_apply, fourier_apply, fourier_apply, h, AddCircle.toCircle_add, Circle.coe_mul]

/-- The monomials split a difference of torus points: `e_k(x - y) = e_k(x) e_{-k}(y)`. -/
theorem emode_sub_apply (k : Gam) (x y : Torus2) :
    emode k (x - y) = emode k x * emode (-k) y := by
  have e0 : (x - y) 0 = x 0 - y 0 := rfl
  have e1 : (x - y) 1 = x 1 - y 1 := rfl
  have h0 : ((-k) 0 : ℤ) = -(k 0) := rfl
  have h1 : ((-k) 1 : ℤ) = -(k 1) := rfl
  show fourier (k 0) ((x - y) 0) * fourier (k 1) ((x - y) 1)
      = (fourier (k 0) (x 0) * fourier (k 1) (x 1))
        * (fourier ((-k) 0) (y 0) * fourier ((-k) 1) (y 1))
  rw [e0, e1, h0, h1, fourier_sub_point, fourier_sub_point]
  ring

/-- The **actual convolution integral** `(K ∗ F)(x) = ∫ K(y) F(x-y) dy`. -/
noncomputable def torusConv (K : Torus2 → ℂ) (F : C(Torus2, ℂ)) (x : Torus2) : ℂ :=
  ∫ y : Torus2, K y * F (x - y)

theorem continuous_shift_apply (F : C(Torus2, ℂ)) (x : Torus2) :
    Continuous fun y : Torus2 => F (x - y) :=
  F.continuous.comp (continuous_const.sub continuous_id)

theorem integrable_kernel_mul_shift (hK : Integrable K (volume : Measure Torus2))
    (F : C(Torus2, ℂ)) (x : Torus2) :
    Integrable (fun y : Torus2 => K y * F (x - y)) (volume : Measure Torus2) :=
  hK.mul_bdd (c := ‖F‖) (continuous_shift_apply F x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => F.norm_coe_le_norm _)

theorem norm_torusConv_le (hK : Integrable K (volume : Measure Torus2)) (F : C(Torus2, ℂ))
    (x : Torus2) : ‖torusConv K F x‖ ≤ (∫ y : Torus2, ‖K y‖) * ‖F‖ := by
  have h1 : ‖torusConv K F x‖ ≤ ∫ y : Torus2, ‖K y * F (x - y)‖ :=
    norm_integral_le_integral_norm _
  have h2 : (∫ y : Torus2, ‖K y * F (x - y)‖) ≤ ∫ y : Torus2, ‖K y‖ * ‖F‖ := by
    refine integral_mono ((integrable_kernel_mul_shift hK F x).norm) (hK.norm.mul_const ‖F‖)
      (fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm _) (norm_nonneg _)
  have h3 : (∫ y : Torus2, ‖K y‖ * ‖F‖) = (∫ y : Torus2, ‖K y‖) * ‖F‖ :=
    integral_mul_const _ _
  linarith [h1, h2, h3.le, h3.ge]

/-- Convolution with a fixed integrable kernel, as a bounded linear functional on
`C(𝕋², ℂ)` of norm at most `‖K‖_{L¹}`.  This is what justifies exchanging the synthesis
series with the convolution integral. -/
noncomputable def torusConvCLM (hK : Integrable K (volume : Measure Torus2)) (x : Torus2) :
    C(Torus2, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => torusConv K F x
      map_add' := fun F G => by
        have h : ∀ y : Torus2, K y * (F + G) (x - y) = K y * F (x - y) + K y * G (x - y) :=
          fun y => by simp only [ContinuousMap.add_apply]; ring
        show (∫ y : Torus2, K y * (F + G) (x - y)) = _
        rw [integral_congr_ae (Filter.Eventually.of_forall h)]
        exact integral_add (integrable_kernel_mul_shift hK F x)
          (integrable_kernel_mul_shift hK G x)
      map_smul' := fun c F => by
        have h : ∀ y : Torus2, K y * (c • F) (x - y) = c * (K y * F (x - y)) :=
          fun y => by simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring
        show (∫ y : Torus2, K y * (c • F) (x - y)) = c • ∫ y : Torus2, K y * F (x - y)
        rw [integral_congr_ae (Filter.Eventually.of_forall h), smul_eq_mul]
        exact integral_const_mul c (fun y : Torus2 => K y * F (x - y)) }
    (∫ y : Torus2, ‖K y‖) (fun F => norm_torusConv_le hK F x)

@[simp] theorem torusConvCLM_apply (hK : Integrable K (volume : Measure Torus2)) (x : Torus2)
    (F : C(Torus2, ℂ)) : torusConvCLM hK x F = torusConv K F x := rfl

/-- Convolution acts on a Fourier monomial by multiplication with its Fourier coefficient. -/
theorem torusConv_emode (hK : Integrable K (volume : Measure Torus2)) (k : Gam) (x : Torus2) :
    torusConv K (emode k) x = kernelCoeff K k * emode k x := by
  have h : ∀ y : Torus2, K y * emode k (x - y) = emode k x * (K y * emode (-k) y) := by
    intro y
    rw [emode_sub_apply]
    ring
  have hcm := integral_const_mul (μ := (volume : Measure Torus2)) (emode k x)
    (fun y : Torus2 => K y * emode (-k) y)
  rw [torusConv, integral_congr_ae (Filter.Eventually.of_forall h)]
  exact hcm.trans (mul_comm _ _)

/-- **Coefficient multiplication.**  The actual convolution integral of an integrable kernel
against a synthesized Wiener state equals the synthesis of the multiplied coefficients.  The
sum/integral exchange is justified: the synthesis series converges in the uniform norm and
`torusConvCLM` is a bounded functional. -/
theorem torusConv_synth (hK : Integrable K (volume : Measure Torus2)) (a : Wiener)
    (x : Torus2) :
    torusConv K (synth a) x = synth (mult (kernelCoeff K) (kernelCoeff_bdd hK) a) x := by
  have hmap := ContinuousLinearMap.map_tsum (torusConvCLM hK x) (summable_synth a)
  have hL : torusConv K (synth a) x = ∑' k : Gam, a k * (kernelCoeff K k * emode k x) := by
    calc torusConv K (synth a) x = torusConvCLM hK x (∑' k : Gam, (a k) • emode k) :=
          congrArg (torusConvCLM hK x) (synth_def a)
      _ = ∑' k : Gam, torusConvCLM hK x ((a k) • emode k) := hmap
      _ = ∑' k : Gam, a k * (kernelCoeff K k * emode k x) := by
          refine tsum_congr fun k => ?_
          rw [map_smul, smul_eq_mul, torusConvCLM_apply, torusConv_emode hK]
  rw [hL, synth_apply]
  refine tsum_congr fun k => ?_
  show a k * (kernelCoeff K k * emode k x) = (kernelCoeff K k * a k) * emode k x
  ring

/-! ### The velocity field of an integrable kernel -/

variable {A : ℝ}

theorem incl_symbolConv_eq_mult (hK : Integrable K (volume : Measure Torus2))
    (hA : KernelBound (kernelCoeff K) A) (u : Wiener1) :
    incl (symbolConv hA u) = mult (kernelCoeff K) (kernelCoeff_bdd hK) (incl u) := by
  ext k; rfl

/-- The convolution of an `A¹` state with an integrable kernel whose coefficients satisfy the
weighted bound is the synthesis of an `A¹` state. -/
theorem torusConv_synth_incl (hK : Integrable K (volume : Measure Torus2))
    (hA : KernelBound (kernelCoeff K) A) (u : Wiener1) (x : Torus2) :
    torusConv K (synth (incl u)) x = synth (incl (symbolConv hA u)) x := by
  rw [torusConv_synth hK (incl u) x, incl_symbolConv_eq_mult hK hA u]

/-- **Differentiation under the integral, in the state variable.**  Along each circle
direction the actual convolution integral is differentiable and its derivative is the
convolution with the Fourier derivative of the state.  The kernel is never differentiated. -/
theorem hasDerivAt_torusConv_state (hK : Integrable K (volume : Measure Torus2))
    (hA : KernelBound (kernelCoeff K) A) (u : Wiener1) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => torusConv K (synth (incl u)) (torusShift x j s))
      (torusConv K (synth (fourierDeriv j u)) x) 0 := by
  have hfun : (fun s : ℝ => torusConv K (synth (incl u)) (torusShift x j s))
      = fun s : ℝ => synth (incl (symbolConv hA u)) (torusShift x j s) := by
    funext s
    exact torusConv_synth_incl hK hA u _
  have hmulti : mult (kernelCoeff K) (kernelCoeff_bdd hK) (fourierDeriv j u)
      = fourierDeriv j (symbolConv hA u) := by
    ext k
    show kernelCoeff K k * (twoPiI * ((k j : ℤ) : ℂ) * u.coeff k)
        = twoPiI * ((k j : ℤ) : ℂ) * (kernelCoeff K k * u.coeff k)
    ring
  have hval : torusConv K (synth (fourierDeriv j u)) x
      = synth (fourierDeriv j (symbolConv hA u)) x := by
    rw [torusConv_synth hK (fourierDeriv j u) x, hmulti]
  rw [hfun, hval]
  exact hasDerivAt_synth_torus (symbolConv hA u) x j

/-- **The rotated-gradient velocity identity for an integrable kernel.**  The first velocity
component is minus the second directional derivative of the actual convolution integral. -/
theorem velocity_integrableKernel_zero (hK : Integrable K (volume : Measure Torus2))
    (hA : KernelBound (kernelCoeff K) A) (u : Wiener1) (x : Torus2) :
    synth (velocity (rotatedGradientSymbol (kernelCoeff K))
        (rotatedGradientSymbol_bdd ⟨A, hA⟩) 0 (incl u)) x
      = -(deriv (fun s : ℝ => torusConv K (synth (incl u)) (torusShift x 1 s)) 0) := by
  rw [velocity_eq_symbolConvDeriv_zero hA u,
    (hasDerivAt_torusConv_state hK hA u x 1).deriv]
  have hmulti : mult (kernelCoeff K) (kernelCoeff_bdd hK) (fourierDeriv 1 u)
      = incl (symbolConvDeriv hA u 1) := by
    ext k
    show kernelCoeff K k * (twoPiI * ((k 1 : ℤ) : ℂ) * u.coeff k)
        = twoPiI * ((k 1 : ℤ) : ℂ) * (kernelCoeff K k * u.coeff k)
    ring
  have hval : torusConv K (synth (fourierDeriv 1 u)) x
      = synth (incl (symbolConvDeriv hA u 1)) x := by
    rw [torusConv_synth hK (fourierDeriv 1 u) x, hmulti]
  rw [hval]
  simp only [map_neg, ContinuousMap.neg_apply]

/-- **The rotated-gradient velocity identity for an integrable kernel**, second component. -/
theorem velocity_integrableKernel_one (hK : Integrable K (volume : Measure Torus2))
    (hA : KernelBound (kernelCoeff K) A) (u : Wiener1) (x : Torus2) :
    synth (velocity (rotatedGradientSymbol (kernelCoeff K))
        (rotatedGradientSymbol_bdd ⟨A, hA⟩) 1 (incl u)) x
      = deriv (fun s : ℝ => torusConv K (synth (incl u)) (torusShift x 0 s)) 0 := by
  rw [velocity_eq_symbolConvDeriv_one hA u,
    (hasDerivAt_torusConv_state hK hA u x 0).deriv]
  have hmulti : mult (kernelCoeff K) (kernelCoeff_bdd hK) (fourierDeriv 0 u)
      = incl (symbolConvDeriv hA u 0) := by
    ext k
    show kernelCoeff K k * (twoPiI * ((k 0 : ℤ) : ℂ) * u.coeff k)
        = twoPiI * ((k 0 : ℤ) : ℂ) * (kernelCoeff K k * u.coeff k)
    ring
  rw [torusConv_synth hK (fourierDeriv 0 u) x, hmulti]

end IntegrableKernels

/-! ## Weighted multiplier bounds from Fourier decay -/

/-- An explicitly stated **nonzero-mode upper Fourier decay** hypothesis. -/
def NonzeroModeDecay (κ : Gam → ℂ) (D : ℝ) : Prop := ∀ k : Gam, k ≠ 0 → wt k * ‖κ k‖ ≤ D

/-- **The weighted multiplier bound follows from nonzero-mode decay plus a finite zero
coefficient.** -/
theorem kernelBound_of_decay {κ : Gam → ℂ} {D C₀ : ℝ} (hD : NonzeroModeDecay κ D)
    (h0 : ‖κ 0‖ ≤ C₀) : KernelBound κ (max D C₀) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    have hw : wt (0 : Gam) = 1 := by
      simp [wt]
    rw [hw, one_mul]
    exact le_trans h0 (le_max_right _ _)
  · exact le_trans (hD k hk) (le_max_left _ _)

theorem isAdmissibleKernel_of_decay {κ : Gam → ℂ} {D C₀ : ℝ} (hD : NonzeroModeDecay κ D)
    (h0 : ‖κ 0‖ ≤ C₀) : IsAdmissibleKernel κ :=
  ⟨max D C₀, kernelBound_of_decay hD h0⟩

/-- For a genuinely integrable kernel the zero coefficient is automatically finite, so the
nonzero-mode decay hypothesis alone gives the weighted multiplier bound. -/
theorem isAdmissibleKernel_kernelCoeff_of_decay {K : Torus2 → ℂ}
    (hK : Integrable K (volume : Measure Torus2)) {D : ℝ}
    (hD : NonzeroModeDecay (kernelCoeff K) D) : IsAdmissibleKernel (kernelCoeff K) :=
  isAdmissibleKernel_of_decay hD (norm_kernelCoeff_le hK 0)

/-! ## Comparison of the two frequency weights

The internal weight is `wt k = 1 + |k₀| + |k₁|`; the paper's convention uses the Euclidean
length `|k| = absK k`.  They are comparable at every nonzero frequency, with the explicit
constants below.  Nothing in this development treats them as literally the same. -/

theorem absK_le_l1 (k : Gam) : absK k ≤ |((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)| := by
  have hsq : sqNorm k ≤ (|((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)|) ^ 2 := by
    have h0 := sq_abs ((k 0 : ℤ) : ℝ)
    have h1 := sq_abs ((k 1 : ℤ) : ℝ)
    have hab : 0 ≤ |((k 0 : ℤ) : ℝ)| * |((k 1 : ℤ) : ℝ)| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simp only [sqNorm]
    nlinarith
  have h := Real.sqrt_le_sqrt hsq
  rw [absK]
  rwa [Real.sqrt_sq (by positivity)] at h

/-- The Euclidean length never exceeds the internal weight. -/
theorem absK_le_wt (k : Gam) : absK k ≤ wt k := by
  have h := absK_le_l1 k
  have h1 : |((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)| ≤ wt k := by
    show _ ≤ 1 + |((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)|
    linarith
  linarith

/-- At every nonzero frequency the internal weight is at most three Euclidean lengths. -/
theorem wt_le_three_absK {k : Gam} (hk : k ≠ 0) : wt k ≤ 3 * absK k := by
  have h1 := l1_le_two_absK k
  have h2 := one_le_absK hk
  show 1 + |((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)| ≤ 3 * absK k
  linarith

/-! ## Fourier magnitude bounds

The predicate below constrains only the **magnitudes** `‖κ k‖`.  It is deliberately *not*
called an ellipticity condition: it is satisfied by the zero law (with `c = D = 0`) and by
sign-reversed laws, as the regressions at the end of this section show. -/

/-- A two-sided bound on the **magnitudes** of the Fourier coefficients at nonzero
frequencies, in the internal weight `wt`.  This is a magnitude condition only: it says
nothing about the sign or the argument of `κ k`. -/
def FourierMagnitudeBounds (κ : Gam → ℂ) (c D : ℝ) : Prop :=
  ∀ k : Gam, k ≠ 0 → c / wt k ≤ ‖κ k‖ ∧ wt k * ‖κ k‖ ≤ D

theorem FourierMagnitudeBounds.nonzeroModeDecay {κ : Gam → ℂ} {c D : ℝ}
    (h : FourierMagnitudeBounds κ c D) : NonzeroModeDecay κ D :=
  fun k hk => (h k hk).2

theorem FourierMagnitudeBounds.isAdmissibleKernel {κ : Gam → ℂ} {c D C₀ : ℝ}
    (h : FourierMagnitudeBounds κ c D) (h0 : ‖κ 0‖ ≤ C₀) : IsAdmissibleKernel κ :=
  isAdmissibleKernel_of_decay h.nonzeroModeDecay h0

/-! ### Regressions: magnitude bounds are strictly weaker than ellipticity -/

/-- The zero coefficient law satisfies the magnitude bounds with `c = D = 0`. -/
theorem fourierMagnitudeBounds_zero : FourierMagnitudeBounds (fun _ : Gam => (0 : ℂ)) 0 0 := by
  intro k _
  refine ⟨?_, ?_⟩ <;> simp

/-- The sign-reversed example law satisfies the magnitude bounds with `c = D = 1`. -/
theorem fourierMagnitudeBounds_neg_exampleKernel :
    FourierMagnitudeBounds (fun k => -exampleKernel k) 1 1 := by
  intro k _
  have hw : (0:ℝ) < wt k := wt_pos k
  have hn : ‖-exampleKernel k‖ = (wt k)⁻¹ := by
    rw [norm_neg]
    show ‖(((wt k)⁻¹ : ℝ) : ℂ)‖ = (wt k)⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [hn, one_div]
  · rw [hn, mul_inv_cancel₀ (ne_of_gt hw)]

/-- Every coefficient of the sign-reversed example law has **strictly negative** real part, so
the magnitude bounds carry no ordered information. -/
theorem neg_exampleKernel_re_neg (k : Gam) : ((-exampleKernel k : ℂ)).re < 0 := by
  have hw : (0:ℝ) < wt k := wt_pos k
  show (-(((wt k)⁻¹ : ℝ) : ℂ)).re < 0
  simp only [Complex.neg_re, Complex.ofReal_re]
  have : (0:ℝ) < (wt k)⁻¹ := by positivity
  linarith

/-! ## The paper's ordered ellipticity, kept separate

The Li–Wang paper additionally requires punctured smoothness of the kernel and a two-sided
**ordered** bound on its *real* Fourier coefficients at every nonzero frequency, in the
Euclidean frequency length.  Only weaker magnitude/upper consequences of that condition are
used by the Wiener multiplier theory above; punctured smoothness is not formalized anywhere in
this development, and the ordered condition itself is always a hypothesis, never a
conclusion. -/

/-- **The paper's ordered ellipticity condition.**  The Fourier coefficients are real and, at
every nonzero frequency, pinched between `c/|k|` and `D/|k|` as an *ordered* inequality
between real numbers, with `0 < c ≤ D` and `|k|` the Euclidean length.  This is a named
*assumption*: nothing in this development proves it for a kernel arising from the paper. -/
structure OrderedFourierEllipticity (κ : Gam → ℂ) (c D : ℝ) : Prop where
  c_pos : 0 < c
  c_le_D : c ≤ D
  isReal : ∀ k : Gam, (κ k).im = 0
  lower : ∀ k : Gam, k ≠ 0 → c / absK k ≤ (κ k).re
  upper : ∀ k : Gam, k ≠ 0 → (κ k).re ≤ D / absK k

namespace OrderedFourierEllipticity

variable {κ : Gam → ℂ} {c D : ℝ}

theorem D_pos (h : OrderedFourierEllipticity κ c D) : 0 < D := lt_of_lt_of_le h.c_pos h.c_le_D

/-- Ordered ellipticity forces a **strictly positive** real coefficient at every nonzero
frequency — which is exactly the information the magnitude predicate discards. -/
theorem re_pos (h : OrderedFourierEllipticity κ c D) {k : Gam} (hk : k ≠ 0) : 0 < (κ k).re := by
  have habs : 0 < absK k := lt_of_lt_of_le zero_lt_one (one_le_absK hk)
  exact lt_of_lt_of_le (div_pos h.c_pos habs) (h.lower k hk)

theorem norm_eq_re (h : OrderedFourierEllipticity κ c D) {k : Gam} (hk : k ≠ 0) :
    ‖κ k‖ = (κ k).re := by
  have hz : κ k = ((κ k).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [h.isReal k]
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h.re_pos hk)]
  simp

/-- The magnitude consequence, in the Euclidean length. -/
theorem norm_bounds (h : OrderedFourierEllipticity κ c D) {k : Gam} (hk : k ≠ 0) :
    c / absK k ≤ ‖κ k‖ ∧ ‖κ k‖ ≤ D / absK k := by
  rw [h.norm_eq_re hk]
  exact ⟨h.lower k hk, h.upper k hk⟩

/-- **The justified weaker magnitude bounds**, in the internal weight, with the explicit
comparison constants of `absK_le_wt` and `wt_le_three_absK`. -/
theorem fourierMagnitudeBounds (h : OrderedFourierEllipticity κ c D) :
    FourierMagnitudeBounds κ c (3 * D) := by
  intro k hk
  have habs : 0 < absK k := lt_of_lt_of_le zero_lt_one (one_le_absK hk)
  have hw : 0 < wt k := wt_pos k
  obtain ⟨hlo, hhi⟩ := h.norm_bounds hk
  refine ⟨?_, ?_⟩
  · exact le_trans (div_le_div_of_nonneg_left h.c_pos.le habs (absK_le_wt k)) hlo
  · calc wt k * ‖κ k‖ ≤ (3 * absK k) * (D / absK k) :=
          mul_le_mul (wt_le_three_absK hk) hhi (norm_nonneg _) (by positivity)
      _ = 3 * D := by field_simp
      _ ≤ 3 * D := le_rfl

theorem nonzeroModeDecay (h : OrderedFourierEllipticity κ c D) : NonzeroModeDecay κ (3 * D) :=
  h.fourierMagnitudeBounds.nonzeroModeDecay

theorem isAdmissibleKernel (h : OrderedFourierEllipticity κ c D) {C₀ : ℝ} (h0 : ‖κ 0‖ ≤ C₀) :
    IsAdmissibleKernel κ :=
  h.fourierMagnitudeBounds.isAdmissibleKernel h0

end OrderedFourierEllipticity

/-- The sign-reversed example law is **not** ordered elliptic: its real parts are negative. -/
theorem not_orderedFourierEllipticity_neg_exampleKernel {c D : ℝ} :
    ¬ OrderedFourierEllipticity (fun k => -exampleKernel k) c D := by
  intro h
  have hk : (unitFreq 0 : Gam) ≠ 0 := unitFreq_ne_zero 0
  exact absurd (h.re_pos hk) (not_lt.2 (neg_exampleKernel_re_neg (unitFreq 0)).le)

/-- The zero law is **not** ordered elliptic either. -/
theorem not_orderedFourierEllipticity_zero {c D : ℝ} :
    ¬ OrderedFourierEllipticity (fun _ : Gam => (0 : ℂ)) c D := by
  intro h
  have hk : (unitFreq 0 : Gam) ≠ 0 := unitFreq_ne_zero 0
  have := h.re_pos hk
  simp at this

/-- A genuine positive witness of the ordered condition: the example coefficient law
`κ(k) = 1/(1+|k₀|+|k₁|)` is ordered elliptic with `c = 1/3`, `D = 1`. -/
theorem orderedFourierEllipticity_exampleKernel :
    OrderedFourierEllipticity exampleKernel (1/3) 1 where
  c_pos := by norm_num
  c_le_D := by norm_num
  isReal := fun k => by
    show (((wt k)⁻¹ : ℝ) : ℂ).im = 0
    simp
  lower := fun k hk => by
    have hw : (0:ℝ) < wt k := wt_pos k
    have habs : 0 < absK k := lt_of_lt_of_le zero_lt_one (one_le_absK hk)
    have h3 : wt k ≤ 3 * absK k := wt_le_three_absK hk
    show (1:ℝ)/3 / absK k ≤ (((wt k)⁻¹ : ℝ) : ℂ).re
    rw [Complex.ofReal_re, div_le_iff₀ habs, inv_mul_eq_div, le_div_iff₀ hw]
    linarith
  upper := fun k hk => by
    have hw : (0:ℝ) < wt k := wt_pos k
    have habs : 0 < absK k := lt_of_lt_of_le zero_lt_one (one_le_absK hk)
    have hle : absK k ≤ wt k := absK_le_wt k
    show (((wt k)⁻¹ : ℝ) : ℂ).re ≤ 1 / absK k
    rw [Complex.ofReal_re, inv_eq_one_div]
    exact div_le_div_of_nonneg_left zero_le_one habs hle

end LiWang.WienerModel
