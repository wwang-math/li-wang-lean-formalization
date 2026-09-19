/-
# A certificate for the local mild solution

A single `Prop`-valued record collecting, for the source-faithful velocity
`R_κ = ∇^⊥(κ ∗ ·)`, everything that has been proved about the local solution: it exists on a
positive time interval, is bounded and continuous, is real, has a real jointly continuous
physical field on `𝕋²` with directional derivatives, has a velocity field that is divergence
free both in frequency and — after synthesis — as an actual pair of directional derivatives on
the torus, obeys the pointwise transport identity, satisfies the **mild** (Duhamel) equation,
and is unique and stable.  "Satisfies the equation" always means the mild equation: no
classical or strong solution concept is asserted anywhere in this record.

Every field is *discharged* by a theorem; the two visible hypotheses are the weighted kernel
bound `KernelBound κ A` and the reality of the kernel and of the datum.  No field assumes the
mild equation, the transport identity, or any conclusion in disguised form.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.PhysicalSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-- Everything proved about the local mild solution of
`∂t θ + ∇^⊥(κ ∗ θ) · ∇θ + (-Δ)^α θ = 0`, `θ(0) = θ₀`, packaged as one record. -/
structure LocalMildSolutionCertificate {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ} {A : ℝ}
    (hb : KernelBound κ A) (hc : ConjSymmetric κ) (u₀ : Wiener1)
    (h₀ : ConjSymmetric u₀.coeff) (T : ℝ) (u : ℝ → Wiener1) : Prop where
  /-- The existence time is positive. -/
  time_pos : 0 < T
  /-- On `[0,T]` the contraction factor of the Duhamel map is at most `1/2`. -/
  contraction_small : ∀ t ∈ Set.Icc (0:ℝ) T,
    8 * Real.pi * (2 * Real.pi * A) * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2
  /-- The state is a continuous curve of first-order Fourier data. -/
  curve_continuous : Continuous u
  /-- It starts at the datum. -/
  initial_value : u 0 = u₀
  /-- It stays in the ball of radius `2‖θ₀‖+1`. -/
  curve_bounded : ∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1
  /-- It stays real (conjugate symmetric). -/
  state_real : ∀ t, ConjSymmetric (u t).coeff
  /-- Its synthesis is a jointly continuous field on `ℝ × 𝕋²`. -/
  field_continuous : Continuous fun p : ℝ × Torus2 => physField u p.1 p.2
  /-- That field is real valued. -/
  field_real : ∀ (t : ℝ) (x : Torus2), ((physField u t x : ℝ) : ℂ) = synth (incl (u t)) x
  /-- The field is differentiable along each circle direction, with the Fourier derivative
  as derivative. -/
  field_derivative : ∀ (t : ℝ) (x : Torus2) (j : Fin 2),
    HasDerivAt (fun s : ℝ => physField u t (torusShift x j s))
      ((synth (fourierDeriv j (u t)) x).re) 0
  /-- The velocity symbol is divergence free in frequency. -/
  symbol_divFree : ∀ k : Gam, ((k 0 : ℤ) : ℂ) * rotatedGradientSymbol κ 0 k
      + ((k 1 : ℤ) : ℂ) * rotatedGradientSymbol κ 1 k = 0
  /-- The velocity field of the state is real at every time. -/
  velocity_real : ∀ (t : ℝ) (j : Fin 2),
    ConjSymmetric ((velocity (rotatedGradientSymbol κ)
      (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) j (incl (u t)) : Wiener) :
        Gam → ℂ)
  /-- The nonlinearity is the pointwise dot product `R(θ) · ∇θ` on the torus. -/
  pointwise_transport : ∀ (t : ℝ) (x : Torus2),
    synth (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u t) x
      = ∑ j : Fin 2, synth (velocity (rotatedGradientSymbol κ)
          (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) j (incl (u t))) x
          * synth (fourierDeriv j (u t)) x
  /-- The mild (Duhamel) equation holds on `[0,T]`. -/
  mild_equation : ∀ t ∈ Set.Icc (0:ℝ) T,
    u t = heatFlow1 α t u₀
      - duhamelIntegral hα.le t
          (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u)
  /-- Any other bounded continuous mild solution with the same datum agrees with it. -/
  uniqueness : ∀ v : ℝ → Wiener1, Continuous v → (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
    (∀ t ∈ Set.Icc (0:ℝ) T, v t = heatFlow1 α t u₀
      - duhamelIntegral hα.le t
          (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) v)) →
    ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t
  /-- Solutions depend Lipschitz-continuously on the datum. -/
  stability : ∀ (v₀ : Wiener1) (v : ℝ → Wiener1), Continuous v →
    (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
    (∀ t ∈ Set.Icc (0:ℝ) T, v t = heatFlow1 α t v₀
      - duhamelIntegral hα.le t
          (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) v)) →
    ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t - v t‖ ≤ 2 * ‖u₀ - v₀‖

/-- **The certificate is inhabited.** -/
theorem exists_localMildSolutionCertificate {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ} {A : ℝ}
    (hb : KernelBound κ A) (hc : ConjSymmetric κ) {u₀ : Wiener1}
    (h₀ : ConjSymmetric u₀.coeff) :
    ∃ (T : ℝ) (u : ℝ → Wiener1), LocalMildSolutionCertificate hα hb hc u₀ h₀ T u := by
  obtain ⟨T, hT, hsmall, u, huc, hu0, hub, hur, hfc, hfr, -, heq⟩ :=
    exists_local_physical_mild_solution hα hb hc h₀
  refine ⟨T, u, ?_⟩
  exact
    { time_pos := hT
      contraction_small := hsmall
      curve_continuous := huc
      initial_value := hu0
      curve_bounded := hub
      state_real := hur
      field_continuous := hfc
      field_real := hfr
      field_derivative := fun t x j => hasDerivAt_physField u t x j
      symbol_divFree := rotatedGradientSymbol_divFree κ
      velocity_real := fun t j =>
        conjSymmetric_rotatedGradientVelocity ⟨A, hb⟩ hc j (hur t).incl
      pointwise_transport := fun t x =>
        synth_quadCurve_apply (rotatedGradientSymbol_bdd ⟨A, hb⟩) u t x
      mild_equation := heq
      uniqueness := fun v hv hRv hev =>
        mild_solution_unique hα (rotatedGradientSymbol_bdd ⟨A, hb⟩)
          (fun j k => rotatedGradientSymbol_norm_le hb j k) u₀ hT.le hsmall huc hv hub hRv
          heq hev
      stability := fun v₀ v hv hRv hev =>
        mild_solution_stability hα (rotatedGradientSymbol_bdd ⟨A, hb⟩)
          (fun j k => rotatedGradientSymbol_norm_le hb j k) u₀ v₀ hT.le hsmall huc hv hub hRv
          heq hev }

/-- The certificate for the explicit finite-support kernel and datum. -/
theorem exists_concrete_localMildSolutionCertificate :
    ∃ (T : ℝ) (u : ℝ → Wiener1),
      LocalMildSolutionCertificate concreteAlpha finiteKernel.kernelBound
        finiteKernel_conjSymmetric finiteKernel finiteKernel_conjSymmetric T u :=
  exists_localMildSolutionCertificate concreteAlpha finiteKernel.kernelBound
    finiteKernel_conjSymmetric finiteKernel_conjSymmetric

end LiWang.WienerModel
