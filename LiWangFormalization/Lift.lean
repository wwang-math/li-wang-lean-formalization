/-
# The periodic lift to `ℝ²` and the differentiation transfer

The synthesized function is lifted to a `ℤ²`-periodic function on `ℝ²`, and we prove by a
genuine termwise-differentiation argument (Mathlib's `hasDerivAt_tsum`, i.e. locally uniform
convergence of the differentiated series) that the Fourier derivative `∂ⱼ` of the
coefficients **is** the `j`-th coordinate partial derivative of the lifted function.

Nothing here defines the physical derivative to be the Fourier multiplier: the derivative is
Mathlib's `HasDerivAt` for the lifted function of a real variable, and the identification is
a theorem.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.PhysicalTransport
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.Formalization

/-! ## The projection `ℝ² → 𝕋²` and the periodic lift -/

/-- The quotient projection `ℝ² → 𝕋²`. -/
def torusProj : C(Fin 2 → ℝ, Torus2) :=
  ⟨fun y j => ((y j : ℝ) : Circ),
    continuous_pi fun j => (AddCircle.continuous_mk' _).comp (continuous_apply j)⟩

@[simp] theorem torusProj_apply (y : Fin 2 → ℝ) (j : Fin 2) :
    torusProj y j = ((y j : ℝ) : Circ) := rfl

/-- The `ℤ²`-periodic lift of the synthesized function to `ℝ²`. -/
noncomputable def lift (a : Wiener) : (Fin 2 → ℝ) → ℂ := fun y => synth a (torusProj y)

theorem lift_def (a : Wiener) (y : Fin 2 → ℝ) : lift a y = synth a (torusProj y) := rfl

/-- The (complexified) dot product `k · y`. -/
noncomputable def dotc (k : Gam) (y : Fin 2 → ℝ) : ℂ := ∑ i : Fin 2, ((k i : ℤ) : ℂ) * ((y i : ℝ) : ℂ)

/-- The plane wave `e_k(y) = exp(2πi k·y)` on `ℝ²`. -/
noncomputable def planeMode (k : Gam) (y : Fin 2 → ℝ) : ℂ := Complex.exp (twoPiI * dotc k y)

theorem emode_torusProj (k : Gam) (y : Fin 2 → ℝ) : emode k (torusProj y) = planeMode k y := by
  show fourier (k 0) ((y 0 : ℝ) : Circ) * fourier (k 1) ((y 1 : ℝ) : Circ) = _
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  show _ = twoPiI * ∑ i : Fin 2, ((k i : ℤ) : ℂ) * ((y i : ℝ) : ℂ)
  rw [Fin.sum_univ_two]
  simp only [twoPiI]
  push_cast
  ring

theorem norm_planeMode (k : Gam) (y : Fin 2 → ℝ) : ‖planeMode k y‖ = 1 := by
  rw [← emode_torusProj]; exact norm_emode_apply k _

theorem summable_lift (a : Wiener) (y : Fin 2 → ℝ) :
    Summable fun k => a k * planeMode k y := by
  refine Summable.of_norm_bounded (wiener_summable a) (fun k => ?_)
  rw [norm_mul, norm_planeMode, mul_one]

/-- The lifted function is the plane-wave series. -/
theorem lift_apply (a : Wiener) (y : Fin 2 → ℝ) : lift a y = ∑' k, a k * planeMode k y := by
  rw [lift_def, synth_apply]
  exact tsum_congr fun k => by rw [emode_torusProj]

/-! ## Periodicity -/

theorem coe_add_intCast (x : ℝ) (n : ℤ) : ((x + (n : ℝ) : ℝ) : Circ) = ((x : ℝ) : Circ) := by
  refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
  have h : (x + (n : ℝ)) - x = n • (1 : ℝ) := by simp
  rw [h]
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨n, rfl⟩

theorem torusProj_add_int (y : Fin 2 → ℝ) (n : Gam) :
    torusProj (fun j => y j + ((n j : ℤ) : ℝ)) = torusProj y := by
  ext j
  exact coe_add_intCast (y j) (n j)

/-- **The lift is `ℤ²`-periodic.** -/
theorem lift_periodic (a : Wiener) (y : Fin 2 → ℝ) (n : Gam) :
    lift a (fun j => y j + ((n j : ℤ) : ℝ)) = lift a y := by
  rw [lift_def, lift_def, torusProj_add_int]

/-! ## Termwise differentiation -/

/-- The part of `k · y` not involving the `j`-th coordinate. -/
noncomputable def restc (k : Gam) (y : Fin 2 → ℝ) (j : Fin 2) : ℂ :=
  dotc k y - ((k j : ℤ) : ℂ) * ((y j : ℝ) : ℂ)

theorem dotc_update (k : Gam) (y : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    dotc k (Function.update y j s) = ((k j : ℤ) : ℂ) * (s : ℂ) + restc k y j := by
  simp only [dotc, restc, Fin.sum_univ_two]
  fin_cases j <;>
    · simp only [Function.update_apply, Fin.isValue]
      norm_num
      try ring

theorem hasDerivAt_planeMode_update (k : Gam) (y : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => planeMode k (Function.update y j t))
      (twoPiI * ((k j : ℤ) : ℂ) * planeMode k (Function.update y j s)) s := by
  have hfun : (fun t : ℝ => planeMode k (Function.update y j t))
      = fun t : ℝ => Complex.exp ((twoPiI * ((k j : ℤ) : ℂ)) * (t : ℂ) + twoPiI * restc k y j) := by
    funext t
    rw [planeMode, dotc_update]
    ring_nf
  have hlin : HasDerivAt
      (fun t : ℝ => (twoPiI * ((k j : ℤ) : ℂ)) * (t : ℂ) + twoPiI * restc k y j)
      (twoPiI * ((k j : ℤ) : ℂ)) s := by
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    simpa using ((h0.const_mul (twoPiI * ((k j : ℤ) : ℂ))).add_const
      (twoPiI * restc k y j))
  have := hlin.cexp
  rw [hfun]
  convert this using 1
  rw [planeMode, dotc_update]
  ring_nf

theorem norm_deriv_bound (u : Wiener1) (k : Gam) (j : Fin 2) (y : Fin 2 → ℝ) (s : ℝ) :
    ‖twoPiI * ((k j : ℤ) : ℂ) * (u.coeff k * planeMode k (Function.update y j s))‖
      ≤ 2 * Real.pi * (wt k * ‖u.coeff k‖) := by
  rw [norm_mul, norm_mul, norm_mul, norm_twoPiI, Complex.norm_intCast, norm_planeMode,
    mul_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (abs_coe_le_wt j k) (norm_nonneg _)) twoPi_nonneg

/-- **The differentiation transfer theorem.**  The `j`-th coordinate partial derivative of
the lifted synthesized function equals the lift of the Fourier derivative.  The proof is a
genuine termwise differentiation: Mathlib's `hasDerivAt_tsum` with the uniform summable
majorant `2π (1+|k₀|+|k₁|) |u(k)|`. -/
theorem hasDerivAt_lift (u : Wiener1) (y : Fin 2 → ℝ) (j : Fin 2) :
    HasDerivAt (fun t : ℝ => lift (incl u) (Function.update y j t))
      (lift (fourierDeriv j u) y) (y j) := by
  set g : Gam → ℝ → ℂ := fun k t => u.coeff k * planeMode k (Function.update y j t) with hg
  set g' : Gam → ℝ → ℂ :=
    fun k t => twoPiI * ((k j : ℤ) : ℂ) * (u.coeff k * planeMode k (Function.update y j t))
    with hg'
  have hderiv : ∀ (k : Gam) (t : ℝ), HasDerivAt (g k) (g' k t) t := by
    intro k t
    simpa [hg, hg', mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_planeMode_update k y j t).const_mul (u.coeff k))
  have hbound : ∀ (k : Gam) (t : ℝ), ‖g' k t‖ ≤ 2 * Real.pi * (wt k * ‖u.coeff k‖) :=
    fun k t => norm_deriv_bound u k j y t
  have hu : Summable fun k : Gam => 2 * Real.pi * (wt k * ‖u.coeff k‖) :=
    u.summable_wt.mul_left _
  have h0 : Summable fun k : Gam => g k (y j) := by
    have hy : Function.update y j (y j) = y := Function.update_eq_self j y
    simpa [hg, hy] using summable_lift (incl u) y
  have hmain := hasDerivAt_tsum hu hderiv hbound h0 (y j)
  have hL : (fun t : ℝ => lift (incl u) (Function.update y j t)) = fun t => ∑' k, g k t := by
    funext t
    rw [lift_apply]
    rfl
  have hR : (∑' k, g' k (y j)) = lift (fourierDeriv j u) y := by
    rw [lift_apply]
    refine tsum_congr fun k => ?_
    have hy : Function.update y j (y j) = y := Function.update_eq_self j y
    show twoPiI * ((k j : ℤ) : ℂ) * (u.coeff k * planeMode k (Function.update y j (y j)))
        = (fourierDeriv j u) k * planeMode k y
    rw [hy, fourierDeriv_apply]
    ring
  rw [hL, ← hR]
  exact hmain

/-- The same statement in `deriv` form: `∂ⱼ (lift (synth (incl u))) = lift (synth (∂ⱼ u))`. -/
theorem deriv_lift (u : Wiener1) (y : Fin 2 → ℝ) (j : Fin 2) :
    deriv (fun t : ℝ => lift (incl u) (Function.update y j t)) (y j)
      = lift (fourierDeriv j u) y := (hasDerivAt_lift u y j).deriv

/-- The lifted Fourier derivative is again periodic, so the identity descends to a statement
about `ℤ²`-periodic functions on `ℝ²`. -/
theorem lift_fourierDeriv_periodic (u : Wiener1) (y : Fin 2 → ℝ) (n : Gam) (j : Fin 2) :
    lift (fourierDeriv j u) (fun i => y i + ((n i : ℤ) : ℝ))
      = lift (fourierDeriv j u) y := lift_periodic _ y n

end LiWang.Formalization
