/-
# The paper-facing quadratic residual certificate

Everything the packet proves about one admissible, conjugate-symmetric scalar kernel `κ`,
bundled into a single structure.  The **hypotheses stay visible**: the only inputs are an
explicit weighted bound `KernelBound κ A` and conjugate symmetry `ConjSymmetric κ`.  No
field of the structure is assumed; each is discharged by a theorem of the packet.  In
particular the pointwise transport identity is a *conclusion*, never an input.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.Coefficients
import LiWangFormalization.TorusDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.Formalization

/-- The `j`-th velocity component of an admissible kernel. -/
noncomputable def kernelVelocity {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (j : Fin 2) :
    Wiener →L[ℂ] Wiener :=
  velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) j

/-- The coefficient-level transport form of an admissible kernel. -/
noncomputable def kernelCoeffTransport {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) :
    Wiener1 →L[ℂ] Wiener1 →L[ℂ] Wiener :=
  transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)

theorem kernelVelocity_apply {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (j : Fin 2)
    (a : Wiener) (k : Gam) : (kernelVelocity hb j a) k = rotatedGradientSymbol κ j k * a k := rfl

/-- **The paper-facing quadratic residual certificate.**

Inputs (visible hypotheses): a scalar kernel coefficient law `κ`, an explicit weighted
bound `KernelBound κ A`, and the reality condition `ConjSymmetric κ`.

Outputs (all proved, none assumed): the corrected rotated-gradient symbol vanishes at zero
frequency, is uniformly bounded by `2πA`, is real, and is divergence free in frequency
space; real states have real velocities and real synthesized profiles; the physical
transport term is the pointwise dot product `R_K(u)·∇v` on the torus; the Fourier
derivative is the genuine coordinate derivative of the periodic lift; and the real
quadratic residual vanishes to second order at the origin with the symmetrized transport
form as its exact second Fréchet derivative. -/
structure PaperFacingQuadraticResidualCertificate {κ : Gam → ℂ} {A : ℝ}
    (hb : KernelBound κ A) (hc : ConjSymmetric κ) : Prop where
  /-- The velocity symbol vanishes at zero frequency. -/
  symbol_zero_freq : ∀ j : Fin 2, rotatedGradientSymbol κ j 0 = 0
  /-- The velocity symbol obeys the explicit uniform bound `2πA` derived from `hb`. -/
  symbol_bound : ∀ (j : Fin 2) (k : Gam), ‖rotatedGradientSymbol κ j k‖ ≤ 2 * Real.pi * A
  /-- The velocity symbol is real (conjugate symmetric). -/
  symbol_real : IsRealSymbol (rotatedGradientSymbol κ)
  /-- Frequency-space divergence freedom `k₀m₀(k) + k₁m₁(k) = 0`. -/
  symbol_divFree : ∀ k : Gam, ((k 0 : ℤ) : ℂ) * rotatedGradientSymbol κ 0 k
      + ((k 1 : ℤ) : ℂ) * rotatedGradientSymbol κ 1 k = 0
  /-- A real state has a real-valued synthesized profile on the torus. -/
  state_real : ∀ (u : RealWiener1) (x : Torus2),
      conj (synth (incl u.val) x) = synth (incl u.val) x
  /-- A real state has conjugate-symmetric velocity coefficients. -/
  velocity_real : ∀ (u : RealWiener1) (j : Fin 2),
      ConjSymmetric ((kernelVelocity ⟨A, hb⟩ j (incl u.val) : Wiener) : Gam → ℂ)
  /-- The physical divergence of the velocity field vanishes at every frequency. -/
  velocity_divFree : ∀ (u : Wiener1) (k : Gam),
      twoPiI * ((k 0 : ℤ) : ℂ) * (kernelVelocity ⟨A, hb⟩ 0 (incl u)) k
        + twoPiI * ((k 1 : ℤ) : ℂ) * (kernelVelocity ⟨A, hb⟩ 1 (incl u)) k = 0
  /-- **Pointwise physical transport**: at every point of the torus the synthesized
  transport term is the Euclidean dot product `R_K(u)(x) · ∇v(x)`. -/
  pointwise_transport : ∀ (u v : Wiener1) (x : Torus2),
      synth (kernelCoeffTransport ⟨A, hb⟩ u v) x
        = ∑ j : Fin 2, synth (kernelVelocity ⟨A, hb⟩ j (incl u)) x * synth (fourierDeriv j v) x
  /-- The Fourier derivative is the genuine coordinate partial derivative of the periodic
  lift of the synthesized function. -/
  derivative_transfer : ∀ (u : Wiener1) (y : Fin 2 → ℝ) (j : Fin 2),
      HasDerivAt (fun t : ℝ => lift (incl u) (Function.update y j t))
        (lift (fourierDeriv j u) y) (y j)
  /-- The same transfer **on the torus itself**: the derivative of the synthesized function
  along the `j`-th circle direction is the synthesis of the Fourier derivative. -/
  torus_derivative_transfer : ∀ (u : Wiener1) (x : Torus2) (j : Fin 2),
      HasDerivAt (fun s : ℝ => synth (incl u) (torusShift x j s))
        (synth (fourierDeriv j u) x) 0
  /-- The lift is `ℤ²`-periodic. -/
  lift_periodic : ∀ (u : Wiener1) (y : Fin 2 → ℝ) (n : Gam),
      lift (incl u) (fun i => y i + ((n i : ℤ) : ℝ)) = lift (incl u) y
  /-- `Q(0) = 0`. -/
  residual_zero : kernelQuadResidual (⟨A, hb⟩ : IsAdmissibleKernel κ) hc 0 = 0
  /-- `DQ(0) = 0`. -/
  residual_fderiv_zero :
      fderiv ℝ (kernelQuadResidual (⟨A, hb⟩ : IsAdmissibleKernel κ) hc) 0 = 0
  /-- `Q` is `C²` over `ℝ`. -/
  residual_contDiff : ContDiff ℝ 2 (kernelQuadResidual (⟨A, hb⟩ : IsAdmissibleKernel κ) hc)
  /-- The exact second Fréchet derivative at the origin. -/
  residual_second_deriv : ∀ h₁ h₂ : RealWiener1,
      fderiv ℝ (fderiv ℝ (kernelQuadResidual (⟨A, hb⟩ : IsAdmissibleKernel κ) hc)) 0 h₁ h₂
        = kernelTransport (⟨A, hb⟩ : IsAdmissibleKernel κ) hc h₁ h₂
          + kernelTransport (⟨A, hb⟩ : IsAdmissibleKernel κ) hc h₂ h₁
  /-- The explicit operator-norm bound of the real transport form. -/
  transport_norm_bound :
      ‖kernelTransport (⟨A, hb⟩ : IsAdmissibleKernel κ) hc‖ ≤ 4 * Real.pi * (2 * Real.pi * A)

/-- **The certificate holds for every admissible conjugate-symmetric kernel.** -/
theorem paperFacingCertificate {κ : Gam → ℂ} {A : ℝ} (hb : KernelBound κ A)
    (hc : ConjSymmetric κ) : PaperFacingQuadraticResidualCertificate hb hc where
  symbol_zero_freq j := rotatedGradientSymbol_zero_freq κ j
  symbol_bound j k := rotatedGradientSymbol_norm_le hb j k
  symbol_real := rotatedGradientSymbol_isRealSymbol hc
  symbol_divFree k := rotatedGradientSymbol_divFree κ k
  state_real u x := conj_synth_apply (u.conjSymmetric.incl) x
  velocity_real u j := conjSymmetric_rotatedGradientVelocity ⟨A, hb⟩ hc j (u.conjSymmetric.incl)
  velocity_divFree u k := rotatedGradient_velocity_div_zero ⟨A, hb⟩ u k
  pointwise_transport u v x := synth_transport_apply _ _ u v x
  derivative_transfer u y j := hasDerivAt_lift u y j
  torus_derivative_transfer u x j := hasDerivAt_synth_torus u x j
  lift_periodic u y n := LiWang.Formalization.lift_periodic (incl u) y n
  residual_zero := quad_zero _
  residual_fderiv_zero := fderiv_quad_zero _
  residual_contDiff := contDiff_quad _ 2
  residual_second_deriv h₁ h₂ := fderiv_fderiv_kernelQuadResidual_apply _ _ h₁ h₂
  transport_norm_bound :=
    norm_realTransport_le _ (rotatedGradientSymbol_isRealSymbol hc)
      (fun j k => rotatedGradientSymbol_norm_le hb j k)

/-- **The two-kernel polarization identity, paper facing.** -/
theorem paperFacingPolarization {κ₁ κ₂ : Gam → ℂ} {A₁ A₂ : ℝ}
    (hb₁ : KernelBound κ₁ A₁) (hb₂ : KernelBound κ₂ A₂)
    (hc₁ : ConjSymmetric κ₁) (hc₂ : ConjSymmetric κ₂) (g₁ g₂ : RealWiener1) :
    fderiv ℝ (fderiv ℝ (fun x =>
        kernelQuadResidual (⟨A₁, hb₁⟩ : IsAdmissibleKernel κ₁) hc₁ x
          - kernelQuadResidual (⟨A₂, hb₂⟩ : IsAdmissibleKernel κ₂) hc₂ x)) 0 g₁ g₂
      = kernelTransport (IsAdmissibleKernel.sub (⟨A₁, hb₁⟩ : IsAdmissibleKernel κ₁)
          (⟨A₂, hb₂⟩ : IsAdmissibleKernel κ₂)) (hc₁.sub hc₂) g₁ g₂
        + kernelTransport (IsAdmissibleKernel.sub (⟨A₁, hb₁⟩ : IsAdmissibleKernel κ₁)
          (⟨A₂, hb₂⟩ : IsAdmissibleKernel κ₂)) (hc₁.sub hc₂) g₂ g₁ :=
  realKernelPolarization _ _ _ _ g₁ g₂

/-- The certificate instantiated at the concrete finite-support kernel. -/
theorem finiteKernel_certificate :
    PaperFacingQuadraticResidualCertificate finiteKernel.kernelBound
      finiteKernel_conjSymmetric :=
  paperFacingCertificate _ _

end LiWang.Formalization
