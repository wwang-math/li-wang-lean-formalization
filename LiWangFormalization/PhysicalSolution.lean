/-
# The local mild solution as a physical field on the torus

The solution produced by `SolutionReality.lean` is a curve of Fourier coefficients.  This
module synthesizes it: `θ(t, x) = Re ∑_k u(t)_k e^{2πi k·x}` is a **real-valued** function on
`ℝ × 𝕋²`, jointly continuous in time and space, whose Fourier coefficients satisfy the mild
equation.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.SolutionReality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology

namespace LiWang.Formalization

/-- The physical field attached to a curve of Fourier coefficients. -/
noncomputable def physField (u : ℝ → Wiener1) (t : ℝ) (x : Torus2) : ℝ :=
  (synth (incl (u t)) x).re

/-- Synthesis of a continuous curve is continuous into `C(𝕋², ℂ)`. -/
theorem continuous_synth_curve {u : ℝ → Wiener1} (hu : Continuous u) :
    Continuous fun t : ℝ => synth (incl (u t)) :=
  (synth.continuous.comp incl.continuous).comp hu

/-- **The physical field is jointly continuous in time and space.** -/
theorem continuous_physField {u : ℝ → Wiener1} (hu : Continuous u) :
    Continuous fun p : ℝ × Torus2 => physField u p.1 p.2 := by
  have hpair : Continuous fun p : ℝ × Torus2 => ((synth (incl (u p.1)), p.2) :
      C(Torus2, ℂ) × Torus2) :=
    ((continuous_synth_curve hu).comp continuous_fst).prodMk continuous_snd
  have heval : Continuous fun p : C(Torus2, ℂ) × Torus2 => p.1 p.2 :=
    continuous_eval
  exact Complex.continuous_re.comp (heval.comp hpair)

/-- The physical field of a real curve really is the value of the synthesized function. -/
theorem ofReal_physField {u : ℝ → Wiener1} (hu : ∀ t, ConjSymmetric (u t).coeff) (t : ℝ)
    (x : Torus2) : ((physField u t x : ℝ) : ℂ) = synth (incl (u t)) x :=
  ofReal_re_synth (hu t).incl x

theorem physField_im {u : ℝ → Wiener1} (hu : ∀ t, ConjSymmetric (u t).coeff) (t : ℝ)
    (x : Torus2) : (synth (incl (u t)) x).im = 0 :=
  synth_im_eq_zero (hu t).incl x

/-- Every Fourier coefficient of the physical field is recovered by the coefficient
functional; in particular the field determines the curve. -/
theorem coeff_physField {u : ℝ → Wiener1} (hu : ∀ t, ConjSymmetric (u t).coeff) (t : ℝ)
    (k : Gam) :
    coeffCLM k ⟨fun x => ((physField u t x : ℝ) : ℂ),
      Complex.continuous_ofReal.comp
        ((Complex.continuous_re.comp (synth (incl (u t))).continuous))⟩
      = (u t).coeff k := by
  have hfun : (⟨fun x => ((physField u t x : ℝ) : ℂ),
      Complex.continuous_ofReal.comp
        ((Complex.continuous_re.comp (synth (incl (u t))).continuous))⟩ : C(Torus2, ℂ))
      = synth (incl (u t)) := by
    ext x
    exact ofReal_physField hu t x
  rw [hfun, coeffCLM_synth, incl_apply]

/-- **The local mild solution as a physical field.**  For a real kernel coefficient law and a
real initial field there is a positive time `T`, a curve `u` of Fourier coefficients solving
the mild equation on `[0,T]`, and the associated physical field `θ(t,x)` on `ℝ × 𝕋²`, which
is jointly continuous, real valued, and has `u(t)` as its Fourier coefficients at every
time. -/
theorem exists_local_physical_mild_solution {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ} {A : ℝ}
    (hb : KernelBound κ A) (hc : ConjSymmetric κ) {u₀ : Wiener1}
    (h₀ : ConjSymmetric u₀.coeff) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * (2 * Real.pi * A) * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      (∀ t, ConjSymmetric (u t).coeff) ∧
      (Continuous fun p : ℝ × Torus2 => physField u p.1 p.2) ∧
      (∀ t x, ((physField u t x : ℝ) : ℂ) = synth (incl (u t)) x) ∧
      (∀ x, physField u 0 x = (synth (incl u₀) x).re) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀
          - duhamelIntegral hα.le t
              (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u) := by
  obtain ⟨T, hT, hsmall, u, huc, hu0, hub, hur, heq⟩ :=
    exists_local_mild_solution_real_rotatedGradient hα hb hc h₀
  refine ⟨T, hT, hsmall, u, huc, hu0, hub, hur, continuous_physField huc,
    fun t x => ofReal_physField hur t x, fun x => ?_, heq⟩
  rw [physField, hu0]

/-! ## The physical form of the equation along a curve -/

/-- The physical field has a directional derivative along each circle direction at every
time, given by the Fourier derivative of the state. -/
theorem hasDerivAt_physField (u : ℝ → Wiener1) (t : ℝ) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => physField u t (torusShift x j s))
      ((synth (fourierDeriv j (u t)) x).re) 0 :=
  hasDerivAt_re_synth_torus (u t) x j

/-- **The nonlinearity of the equation, pointwise on the torus**: at every time the
synthesized transport term is the dot product of the synthesized velocity with the
synthesized gradient. -/
theorem synth_quadCurve_apply {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (u : ℝ → Wiener1)
    (t : ℝ) (x : Torus2) :
    synth (quadCurve hm u t) x
      = ∑ j : Fin 2, synth (velocity m hm j (incl (u t))) x
          * synth (fourierDeriv j (u t)) x :=
  synth_transport_apply m hm (u t) (u t) x

/-! ## A completely concrete instance

Nothing above is vacuous: the hypotheses are satisfied by an explicit nonzero real kernel and
an explicit nonzero real initial field. -/

theorem concreteAlpha : (1:ℝ) / 2 < 3 / 4 := by norm_num

/-- A nonzero state has a nonzero physical field. -/
theorem exists_physField_ne_zero {u : ℝ → Wiener1} (hu : ∀ t, ConjSymmetric (u t).coeff)
    {t : ℝ} (h : u t ≠ 0) : ∃ x : Torus2, physField u t x ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ x : Torus2, physField u t x = 0 := by
    intro x
    by_contra hx
    exact hcon ⟨x, hx⟩
  refine h (incl_injective ?_)
  have hz : synth (incl (u t)) = synth (incl (0 : Wiener1)) := by
    ext x
    rw [map_zero, map_zero]
    have hx := ofReal_physField hu t x
    rw [← hx, hcon' x]
    simp
  exact synth_injective hz

/-- The velocity field generated by a genuine (summable) kernel along a curve is divergence
free on the torus at every time. -/
theorem solution_velocity_divFree (K : Wiener1) (u : ℝ → Wiener1) (t : ℝ) (x : Torus2) :
    deriv (fun s : ℝ => synth (incl (-(kernelConvDeriv K (u t) 1))) (torusShift x 0 s)) 0
      + deriv (fun s : ℝ => synth (incl (kernelConvDeriv K (u t) 0)) (torusShift x 1 s)) 0
      = 0 :=
  div_synth_velocity_eq_zero K (u t) x

/-- **A concrete local solution.**  Dissipation exponent `α = 3/4`, velocity
`R_κ = ∇^⊥(κ ∗ ·)` for the explicit finite-support real kernel `κ = e_{(1,0)} + e_{(-1,0)}`,
and the same real field as initial datum.  The resulting physical field on `ℝ × 𝕋²` is
jointly continuous and real valued, and its initial value is nonzero. -/
theorem exists_concrete_local_physical_solution :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = finiteKernel ∧ u 0 ≠ 0 ∧
      (∀ t, ConjSymmetric (u t).coeff) ∧
      (Continuous fun p : ℝ × Torus2 => physField u p.1 p.2) ∧
      (∃ x : Torus2, physField u 0 x ≠ 0) ∧
      (∀ (t : ℝ) (x : Torus2),
        deriv (fun s : ℝ =>
            synth (incl (-(kernelConvDeriv finiteKernel (u t) 1))) (torusShift x 0 s)) 0
          + deriv (fun s : ℝ =>
              synth (incl (kernelConvDeriv finiteKernel (u t) 0)) (torusShift x 1 s)) 0
          = 0) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 (3 / 4) t finiteKernel
          - duhamelIntegral concreteAlpha.le t
              (quadCurve (rotatedGradientSymbol_bdd finiteKernel_admissible) u) := by
  obtain ⟨T, hT, -, u, huc, hu0, -, hur, hcont, -, -, heq⟩ :=
    exists_local_physical_mild_solution concreteAlpha finiteKernel.kernelBound
      finiteKernel_conjSymmetric finiteKernel_conjSymmetric
  have hne : u 0 ≠ 0 := by rw [hu0]; exact finiteKernel_ne_zero
  exact ⟨T, hT, u, huc, hu0, hne, hur, hcont, exists_physField_ne_zero hur hne,
    fun t x => solution_velocity_divFree finiteKernel u t x, heq⟩

end LiWang.Formalization
