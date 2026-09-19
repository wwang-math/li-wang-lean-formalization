/-
# The physical transport commuting diagram

`synth` intertwines the coefficient transport form with the pointwise product
`∑ⱼ (R_m u)ⱼ · ∂ⱼ v` of continuous functions on `𝕋²`, and the coefficient quadratic residual
with its physical counterpart.

Two kernel tiers are treated separately and honestly:

* **tier (a)** an *admissible multiplier coefficient law* `m` satisfying the uniform bound
  `IsBddSymbol m`.  This is enough to produce a continuous velocity field after
  multiplication by Wiener data, but such an `m` need not itself be a synthesizable kernel.
* **tier (b)** a *genuine `Wiener1` kernel* `K`.  Then `K` itself synthesizes, its
  coefficient law is automatically admissible, and the literal identity
  `R_K u = ∇^⊥(K * u)` holds with `K * u` realized as the Fourier product `κ(k) u(k)`.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.RealSynthesis

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## The commuting diagram -/

/-- **The physical transport commuting diagram.**  Synthesis turns the coefficient transport
form into the pointwise sum of products `∑ⱼ (R_m u)ⱼ · ∂ⱼ v` on the torus. -/
theorem synth_transport (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v : Wiener1) :
    synth (transport m hm u v)
      = ∑ j : Fin 2, synth (velocity m hm j (incl u)) * synth (fourierDeriv j v) := by
  rw [transport_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => synth_conv _ _

/-- The pointwise form: at every point of the torus the synthesized transport term is the
Euclidean dot product `R_m(u)(x) · ∇v(x)`. -/
theorem synth_transport_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v : Wiener1)
    (x : Torus2) :
    synth (transport m hm u v) x
      = ∑ j : Fin 2, synth (velocity m hm j (incl u)) x * synth (fourierDeriv j v) x := by
  rw [synth_transport]
  simp [ContinuousMap.mul_apply]

/-- **The quadratic residual commutes with synthesis.** -/
theorem synth_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u : Wiener1) :
    synth (quadResidual m hm u)
      = ∑ j : Fin 2, synth (velocity m hm j (incl u)) * synth (fourierDeriv j u) :=
  synth_transport m hm u u

/-- The physical quadratic residual: the continuous function on `𝕋²` obtained by
synthesizing the coefficient quadratic residual. -/
noncomputable def physQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (u : Wiener1) : C(Torus2, ℂ) := synth (quadResidual m hm u)

theorem physQuadResidual_eq (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u : Wiener1) :
    physQuadResidual m hm u
      = ∑ j : Fin 2, synth (velocity m hm j (incl u)) * synth (fourierDeriv j u) :=
  synth_quadResidual m hm u

@[simp] theorem physQuadResidual_zero (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) :
    physQuadResidual m hm 0 = 0 := by
  rw [physQuadResidual, quadResidual_zero, map_zero]

/-- The rotated-gradient specialization: the literal physical transport term
`R_K(u) · ∇v` for the source-faithful symbol. -/
theorem synth_transport_rotatedGradient {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (u v : Wiener1) :
    synth (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) u v)
      = ∑ j : Fin 2,
          synth (velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) j (incl u))
            * synth (fourierDeriv j v) :=
  synth_transport _ _ u v

/-! ## Tier (b): a genuine `Wiener1` kernel -/

/-- Every coefficient of a first-order Wiener element is bounded by its norm. -/
theorem Wiener1.norm_coeff_le (u : Wiener1) (k : Gam) : ‖u.coeff k‖ ≤ ‖u‖ :=
  le_trans (le_trans (le_of_eq (by rw [← incl_apply])) (wiener_norm_apply_le (incl u) k))
    (norm_incl_apply_le u)

/-- Every coefficient family of a first-order Wiener element satisfies the explicit weighted
kernel bound with constant `‖K‖`; in particular a genuine `Wiener1` kernel is admissible. -/
theorem Wiener1.kernelBound (K : Wiener1) : KernelBound K.coeff ‖K‖ := by
  intro k
  rw [Wiener1.norm_eq]
  exact K.summable_wt.le_tsum k (fun j _ => mul_nonneg (wt_pos j).le (norm_nonneg _))

theorem Wiener1.isAdmissibleKernel (K : Wiener1) : IsAdmissibleKernel K.coeff :=
  ⟨‖K‖, K.kernelBound⟩

theorem summable_kernelConv (K u : Wiener1) :
    Summable fun k => wt k * ‖K.coeff k * u.coeff k‖ := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => ?_) (u.summable_wt.mul_left ‖K‖)
  rw [norm_mul]
  calc wt k * (‖K.coeff k‖ * ‖u.coeff k‖) = ‖K.coeff k‖ * (wt k * ‖u.coeff k‖) := by ring
    _ ≤ ‖K‖ * (wt k * ‖u.coeff k‖) :=
        mul_le_mul_of_nonneg_right (K.norm_coeff_le k)
          (mul_nonneg (wt_pos k).le (norm_nonneg _))

/-- The Fourier realization of the torus convolution `K * u`: the coefficient family
`k ↦ κ(k) u(k)`.  Since v3.0 the *actual* convolution integral is available as
`LiWang.WienerModel.torusConv` (`IntegrableKernel.lean`), and `LiWang.WienerModel.torusConv_synth` proves that it
agrees with this coefficient law on synthesized states; `LiWang.WienerModel.symbolConv_eq_kernelConv`
identifies this definition with the general admissible-symbol version. -/
noncomputable def kernelConv (K u : Wiener1) : Wiener1 :=
  Wiener1.mk (fun k => K.coeff k * u.coeff k) (summable_kernelConv K u)

@[simp] theorem kernelConv_coeff (K u : Wiener1) (k : Gam) :
    (kernelConv K u).coeff k = K.coeff k * u.coeff k := rfl

/-- **`R_K(u)₀ = -∂₂(K * u)`.**  The first component of the rotated gradient, with the
corrected sign. -/
theorem velocity_rotatedGradient_zero (K u : Wiener1) :
    velocity (rotatedGradientSymbol K.coeff) (rotatedGradientSymbol_bdd K.isAdmissibleKernel)
        0 (incl u)
      = -(fourierDeriv 1 (kernelConv K u)) := by
  ext k
  show rotatedGradientSymbol K.coeff 0 k * (incl u) k
      = -(twoPiI * ((k 1 : ℤ) : ℂ) * (kernelConv K u).coeff k)
  show (-twoPiI * ((k 1 : ℤ) : ℂ) * K.coeff k) * u.coeff k
      = -(twoPiI * ((k 1 : ℤ) : ℂ) * (K.coeff k * u.coeff k))
  ring

/-- **`R_K(u)₁ = ∂₁(K * u)`.** -/
theorem velocity_rotatedGradient_one (K u : Wiener1) :
    velocity (rotatedGradientSymbol K.coeff) (rotatedGradientSymbol_bdd K.isAdmissibleKernel)
        1 (incl u)
      = fourierDeriv 0 (kernelConv K u) := by
  ext k
  show rotatedGradientSymbol K.coeff 1 k * (incl u) k
      = twoPiI * ((k 0 : ℤ) : ℂ) * (kernelConv K u).coeff k
  show (twoPiI * ((k 0 : ℤ) : ℂ) * K.coeff k) * u.coeff k
      = twoPiI * ((k 0 : ℤ) : ℂ) * (K.coeff k * u.coeff k)
  ring

/-- **Frequency-side divergence freedom of the velocity field.**  The Fourier symbol of
`∂₁(R_K u)₀ + ∂₂(R_K u)₁` annihilates every frequency.  This is a statement about
coefficients only; the divergence of the *physical* velocity field on the torus is
`div_synth_velocity_eq_zero` (`TorusDerivative.lean`), and for a general admissible
coefficient law `div_synth_velocity_symbol_eq_zero` (`IntegrableKernel.lean`). -/
theorem rotatedGradient_velocity_div_zero {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (u : Wiener1) (k : Gam) :
    twoPiI * ((k 0 : ℤ) : ℂ)
        * (velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) 0 (incl u)) k
      + twoPiI * ((k 1 : ℤ) : ℂ)
        * (velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) 1 (incl u)) k
      = 0 := by
  show twoPiI * ((k 0 : ℤ) : ℂ) * (rotatedGradientSymbol κ 0 k * u.coeff k)
      + twoPiI * ((k 1 : ℤ) : ℂ) * (rotatedGradientSymbol κ 1 k * u.coeff k) = 0
  show twoPiI * ((k 0 : ℤ) : ℂ) * ((-twoPiI * ((k 1 : ℤ) : ℂ) * κ k) * u.coeff k)
      + twoPiI * ((k 1 : ℤ) : ℂ) * ((twoPiI * ((k 0 : ℤ) : ℂ) * κ k) * u.coeff k) = 0
  ring

/-- Reality of the velocity field: for a conjugate-symmetric kernel the velocity components
of a real state are again conjugate symmetric. -/
theorem conjSymmetric_rotatedGradient_velocity_of_real {κ : Gam → ℂ}
    (hb : IsAdmissibleKernel κ) (hc : ConjSymmetric κ) (j : Fin 2) {u : Wiener1}
    (hu : ConjSymmetric u.coeff) :
    ConjSymmetric
      ((velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) j (incl u) :
        Wiener) : Gam → ℂ) :=
  conjSymmetric_rotatedGradientVelocity hb hc j hu.incl

/-! ## A genuine finite-support kernel

`exampleKernel k = (1 + |k₀| + |k₁|)⁻¹` of the coefficient layer is an *admissible
multiplier coefficient law* only: it satisfies the weighted pointwise bound, hence defines a
bounded Fourier multiplier, but it is **not** claimed to be an element of the Wiener algebra
and therefore is not automatically synthesizable.  The kernel below is a genuine `Wiener1`
element with finite support, so tier (b) applies to it and its physical synthesis is a bona
fide continuous function on `𝕋²`. -/

/-- A nonzero conjugate-symmetric **finite-support** kernel: the real cosine mode at the
unit frequency `e₀`. -/
noncomputable def finiteKernel : Wiener1 := cosMode1 (unitFreq 0)

theorem finiteKernel_conjSymmetric : ConjSymmetric finiteKernel.coeff :=
  cosMode1_conjSymmetric _

theorem finiteKernel_ne_zero : finiteKernel ≠ 0 := cosMode1_ne_zero _

theorem finiteKernel_admissible : IsAdmissibleKernel finiteKernel.coeff :=
  finiteKernel.isAdmissibleKernel

theorem incl_cosMode1 (k₀ : Gam) : incl (cosMode1 k₀) = wdirac k₀ + wdirac (-k₀) := by
  rw [cosMode1, map_add, incl_dirac1, incl_dirac1]

/-- The finite-support kernel synthesizes to the genuine continuous function
`e_{k₀} + e_{-k₀}` on the torus. -/
theorem synth_finiteKernel : synth (incl finiteKernel) = emode (unitFreq 0) + emode (-unitFreq 0) := by
  rw [finiteKernel, incl_cosMode1, synth_add, synth_wdirac, synth_wdirac]

/-- Its synthesis is real valued. -/
theorem synth_finiteKernel_real (x : Torus2) :
    conj (synth (incl finiteKernel) x) = synth (incl finiteKernel) x :=
  conj_synth_apply (finiteKernel_conjSymmetric.incl) x

end LiWang.WienerModel
