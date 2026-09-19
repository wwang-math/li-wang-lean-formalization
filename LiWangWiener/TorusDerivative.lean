/-
# The differentiation transfer, stated on the torus

`Lift.lean` proves the differentiation-transfer theorem for the `ℤ²`-periodic lift to `ℝ²`.
Here we push it down to `𝕋²` itself, by differentiating along the natural one-parameter
family of translations in the `j`-th circle direction:

  `s ↦ F (x + s e_j)` ,   `x : 𝕋²` , `s : ℝ`.

This is a genuine statement about the synthesized function on the torus: no smooth structure
on the quotient is needed, only the group translation and Mathlib's `HasDerivAt` for a real
variable.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.Lift

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-- Translation of a torus point by `s` in the `j`-th coordinate direction. -/
noncomputable def torusShift (x : Torus2) (j : Fin 2) (s : ℝ) : Torus2 :=
  Function.update x j (x j + ((s : ℝ) : Circ))

@[simp] theorem torusShift_zero (x : Torus2) (j : Fin 2) : torusShift x j 0 = x := by
  funext i
  by_cases h : i = j
  · subst h; simp [torusShift]
  · simp [torusShift, h]

/-- Every torus point has a real representative in each coordinate. -/
theorem exists_torusProj (x : Torus2) : ∃ y : Fin 2 → ℝ, torusProj y = x := by
  choose y hy using fun i => Quotient.exists_rep (x i)
  exact ⟨y, by funext i; exact hy i⟩

theorem torusShift_torusProj (y : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    torusShift (torusProj y) j s = torusProj (Function.update y j (y j + s)) := by
  funext i
  simp only [torusShift, torusProj_apply, Function.update_apply]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    exact (AddCircle.coe_add 1 (y i) s).symm
  · simp only [if_neg h]

/-- **The differentiation transfer theorem on the torus.**  The derivative of the
synthesized function along the `j`-th circle direction is the synthesis of the Fourier
derivative.  The physical derivative here is Mathlib's `HasDerivAt` for a real parameter;
the identification with the Fourier multiplier is a theorem, not a definition. -/
theorem hasDerivAt_synth_torus (u : Wiener1) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => synth (incl u) (torusShift x j s))
      (synth (fourierDeriv j u) x) 0 := by
  obtain ⟨y, hy⟩ := exists_torusProj x
  subst hy
  have hshift : (fun s : ℝ => synth (incl u) (torusShift (torusProj y) j s))
      = fun s : ℝ => lift (incl u) (Function.update y j (y j + s)) := by
    funext s
    rw [torusShift_torusProj]
    rfl
  have hbase := hasDerivAt_lift u y j
  have hinner : HasDerivAt (fun s : ℝ => y j + s) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add (y j)
  have hbase' : HasDerivAt (fun t : ℝ => lift (incl u) (Function.update y j t))
      (lift (fourierDeriv j u) y) (y j + 0) := by simpa using hbase
  have hcomp := HasDerivAt.scomp (0 : ℝ) hbase' hinner
  rw [hshift]
  simpa [lift_def] using hcomp

/-- The `deriv` form of the torus statement. -/
theorem deriv_synth_torus (u : Wiener1) (x : Torus2) (j : Fin 2) :
    deriv (fun s : ℝ => synth (incl u) (torusShift x j s)) 0
      = synth (fourierDeriv j u) x := (hasDerivAt_synth_torus u x j).deriv

/-- The same statement for the real synthesis of a real state: the directional derivative of
the real-valued function on `𝕋²` is the real synthesis of the Fourier derivative. -/
theorem hasDerivAt_re_synth_torus (u : Wiener1) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => (synth (incl u) (torusShift x j s)).re)
      ((synth (fourierDeriv j u) x).re) 0 :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_synth_torus u x j)

/-! ### Second-order derivatives and physical divergence freedom -/

theorem summable_kernelConvDeriv (K u : Wiener1) (j : Fin 2) :
    Summable fun k => wt k * ‖twoPiI * ((k j : ℤ) : ℂ) * (K.coeff k * u.coeff k)‖ := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => ?_) ((u.summable_wt.mul_left ‖K‖).mul_left (2 * Real.pi))
  simp only [norm_mul, norm_twoPiI, Complex.norm_intCast]
  have hKb : wt k * ‖K.coeff k‖ ≤ ‖K‖ := K.kernelBound k
  have h1 : |((k j : ℤ) : ℝ)| ≤ wt k := abs_coe_le_wt j k
  have hKn : (0:ℝ) ≤ ‖K.coeff k‖ := norm_nonneg _
  have hun : (0:ℝ) ≤ ‖u.coeff k‖ := norm_nonneg _
  have hw : (0:ℝ) < wt k := wt_pos k
  have hstep : |((k j : ℤ) : ℝ)| * ‖K.coeff k‖ ≤ ‖K‖ :=
    le_trans (mul_le_mul_of_nonneg_right h1 hKn) hKb
  have hpi := twoPi_nonneg
  have hwu : (0:ℝ) ≤ wt k * ‖u.coeff k‖ := by positivity
  calc wt k * (2 * Real.pi * |((k j : ℤ) : ℝ)| * (‖K.coeff k‖ * ‖u.coeff k‖))
      = 2 * Real.pi * (|((k j : ℤ) : ℝ)| * ‖K.coeff k‖) * (wt k * ‖u.coeff k‖) := by ring
    _ ≤ 2 * Real.pi * ‖K‖ * (wt k * ‖u.coeff k‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hpi) hwu
    _ = 2 * Real.pi * (‖K‖ * (wt k * ‖u.coeff k‖)) := by ring

/-- `∂ⱼ(K * u)` as an element of the **first-order** space: a genuine `Wiener1` kernel buys
one extra derivative, so the velocity field is itself differentiable. -/
noncomputable def kernelConvDeriv (K u : Wiener1) (j : Fin 2) : Wiener1 :=
  Wiener1.mk (fun k => twoPiI * ((k j : ℤ) : ℂ) * (K.coeff k * u.coeff k))
    (summable_kernelConvDeriv K u j)

@[simp] theorem kernelConvDeriv_coeff (K u : Wiener1) (j : Fin 2) (k : Gam) :
    (kernelConvDeriv K u j).coeff k = twoPiI * ((k j : ℤ) : ℂ) * (K.coeff k * u.coeff k) := rfl

theorem incl_kernelConvDeriv (K u : Wiener1) (j : Fin 2) :
    incl (kernelConvDeriv K u j) = fourierDeriv j (kernelConv K u) := by
  ext k; rfl

/-- The velocity components of a genuine `Wiener1` kernel lie in the first-order space. -/
theorem velocity_eq_kernelConvDeriv_zero (K u : Wiener1) :
    velocity (rotatedGradientSymbol K.coeff) (rotatedGradientSymbol_bdd K.isAdmissibleKernel)
        0 (incl u) = incl (-(kernelConvDeriv K u 1)) := by
  rw [map_neg, incl_kernelConvDeriv]
  exact velocity_rotatedGradient_zero K u

theorem velocity_eq_kernelConvDeriv_one (K u : Wiener1) :
    velocity (rotatedGradientSymbol K.coeff) (rotatedGradientSymbol_bdd K.isAdmissibleKernel)
        1 (incl u) = incl (kernelConvDeriv K u 0) := by
  rw [incl_kernelConvDeriv]
  exact velocity_rotatedGradient_one K u

/-- **Frequency-side divergence freedom of the velocity field.**  This is an identity of
Fourier states, `∂₁(R_K u)₀ + ∂₂(R_K u)₁ = 0` in the Wiener algebra; it is *not* by itself the
statement about the physical field.  The genuinely physical statement — the sum of the two
directional derivatives of the synthesized velocity components vanishes at every point of the
torus — is `div_synth_velocity_eq_zero` immediately below, and it is a separate theorem
obtained from this one through the differentiation transfer theorem. -/
theorem div_velocity_eq_zero (K u : Wiener1) :
    fourierDeriv 0 (-(kernelConvDeriv K u 1)) + fourierDeriv 1 (kernelConvDeriv K u 0) = 0 := by
  ext k
  show twoPiI * ((k 0 : ℤ) : ℂ) * ((-(kernelConvDeriv K u 1)).coeff k)
      + twoPiI * ((k 1 : ℤ) : ℂ) * ((kernelConvDeriv K u 0).coeff k) = 0
  show twoPiI * ((k 0 : ℤ) : ℂ) * (-(twoPiI * ((k 1 : ℤ) : ℂ) * (K.coeff k * u.coeff k)))
      + twoPiI * ((k 1 : ℤ) : ℂ) * (twoPiI * ((k 0 : ℤ) : ℂ) * (K.coeff k * u.coeff k)) = 0
  ring

/-- **Physical divergence freedom on the torus**: the sum of the two directional derivatives
of the synthesized velocity components vanishes identically. -/
theorem div_synth_velocity_eq_zero (K u : Wiener1) (x : Torus2) :
    deriv (fun s : ℝ => synth (incl (-(kernelConvDeriv K u 1))) (torusShift x 0 s)) 0
      + deriv (fun s : ℝ => synth (incl (kernelConvDeriv K u 0)) (torusShift x 1 s)) 0 = 0 := by
  rw [deriv_synth_torus, deriv_synth_torus]
  have h : synth (fourierDeriv 0 (-(kernelConvDeriv K u 1)))
      + synth (fourierDeriv 1 (kernelConvDeriv K u 0)) = 0 := by
    rw [← map_add, div_velocity_eq_zero, map_zero]
  have hx := congrArg (fun F : C(Torus2, ℂ) => F x) h
  simpa using hx

end LiWang.WienerModel
