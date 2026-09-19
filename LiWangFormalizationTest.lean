/-
Test / regression file for `LiWangFormalizationExactPaperInterfacePacket` v11.0.

Run with

    lake env lean LiWangFormalizationTest.lean

It re-checks the statement of every principal theorem by `example`, exercises the physical
synthesis on explicit finite-mode data, prints the axiom dependencies of the headline
results, and runs a whole-namespace axiom audit.
-/
import LiWangFormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LiWang.Formalization
open scoped ComplexConjugate BigOperators
open BoundedContinuousFunction
open Filter Topology
open MeasureTheory

namespace LiWangTest

/-! ### 1. The v1.1 coefficient layer still works -/

example : CompleteSpace Wiener := inferInstance
example : CompleteSpace Wiener1 := inferInstance
example : CompleteSpace RealWiener := inferInstance
example : CompleteSpace RealWiener1 := inferInstance
example (a : Wiener) : ‖a‖ = ∑' k, ‖a k‖ := wiener_norm_eq a
example (u : Wiener1) : ‖u‖ = ∑' k, wt k * ‖u.coeff k‖ := Wiener1.norm_eq u
example (a b : Wiener) : ‖conv a b‖ ≤ ‖a‖ * ‖b‖ := norm_conv_le a b
example (j : Fin 2) : ‖fourierDeriv j‖ ≤ 2 * Real.pi := norm_fourierDeriv_le j
example (j : Fin 2) : Real.pi ≤ ‖fourierDeriv j‖ := pi_le_norm_fourierDeriv j
example : ¬ IsRealSymbol testSymbolNoI := not_isRealSymbol_testSymbolNoI
example (κ : Gam → ℂ) (k : Gam) :
    ((k 0 : ℤ) : ℂ) * rotatedGradientSymbol κ 0 k
      + ((k 1 : ℤ) : ℂ) * rotatedGradientSymbol κ 1 k = 0 := rotatedGradientSymbol_divFree κ k
example {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsBddSymbol m₁) (h₂ : IsBddSymbol m₂)
    (r₁ : IsRealSymbol m₁) (r₂ : IsRealSymbol m₂) (g₁ g₂ : RealWiener1) :
    fderiv ℝ (fderiv ℝ (fun x => realQuadResidual m₁ h₁ r₁ x - realQuadResidual m₂ h₂ r₂ x))
        0 g₁ g₂
      = realTransport (m₁ - m₂) (h₁.sub h₂) (r₁.sub r₂) g₁ g₂
        + realTransport (m₁ - m₂) (h₁.sub h₂) (r₁.sub r₂) g₂ g₁ :=
  realLiWangPolarization h₁ h₂ r₁ r₂ g₁ g₂

/-! ### 2. Physical Fourier synthesis -/

example : CompactSpace Torus2 := inferInstance
noncomputable example : NormedRing C(Torus2, ℂ) := inferInstance
example (a : Wiener) : ‖synth a‖ ≤ ‖a‖ := norm_synth_apply_le a
example : ‖synth‖ ≤ 1 := norm_synth_le
example (a : Wiener) (x : Torus2) : synth a x = ∑' k, a k * emode k x := synth_apply a x
example (a b : Wiener) : synth (a + b) = synth a + synth b := synth_add a b
example (c : ℂ) (a : Wiener) : synth (c • a) = c • synth a := synth_smul c a
example : synth (0 : Wiener) = 0 := synth_zero
example (k : Gam) (x : Torus2) : ‖emode k x‖ = 1 := norm_emode_apply k x

/-- Explicit finite-mode tests. -/
example (k₀ : Gam) : synth (wdirac k₀) = emode k₀ := synth_wdirac k₀
example : synth (wdirac (0 : Gam)) = 1 := synth_zero_mode
example (k₀ k₁ : Gam) : synth (wdirac k₀ + wdirac k₁) = emode k₀ + emode k₁ :=
  synth_two_modes k₀ k₁
example (k₀ : Gam) (x : Torus2) :
    synth (wdirac k₀) x = fourier (k₀ 0) (x 0) * fourier (k₀ 1) (x 1) :=
  synth_wdirac_apply k₀ x

/-- Coefficient recovery and injectivity. -/
example (a : Wiener) (k : Gam) : coeffCLM k (synth a) = a k := coeffCLM_synth a k
example : Function.Injective (synth : Wiener → C(Torus2, ℂ)) := synth_injective
example (a : Wiener) : synth a = 0 ↔ a = 0 := synth_eq_zero_iff a
example (k : Gam) : (∫ x : Torus2, emode k x) = if k = 0 then 1 else 0 := integral_emode k

/-! ### 3. The convolution–product theorem -/

example (a b : Wiener) : synth (conv a b) = synth a * synth b := synth_conv a b
example (a b : Wiener) (x : Torus2) : synth (conv a b) x = synth a x * synth b x :=
  synth_conv_apply a b x

/-- Regression on two nontrivial Dirac modes: frequencies **add**. -/
example (p q : Gam) : conv (wdirac p) (wdirac q) = wdirac (p + q) := conv_wdirac_wdirac p q
example (p q : Gam) : synth (conv (wdirac p) (wdirac q)) = emode (p + q) :=
  synth_conv_wdirac p q
example (p q : Gam) :
    synth (conv (wdirac p) (wdirac q)) = synth (wdirac p) * synth (wdirac q) :=
  synth_conv_wdirac_eq_mul p q
/-- Sign regression: `e_p · e_{-p} = 1`. -/
example (p : Gam) : synth (conv (wdirac p) (wdirac (-p))) = 1 := synth_conv_wdirac_neg p
example : synth (conv (wdirac (unitFreq 0)) (wdirac (unitFreq 1)))
    = emode (unitFreq 0 + unitFreq 1) := synth_conv_unitFreq
example : (unitFreq 0 + unitFreq 1 : Gam) 0 = 1 ∧ (unitFreq 0 + unitFreq 1 : Gam) 1 = 1 :=
  unitFreq_sum_apply

/-! ### 4. Differentiation transfer -/

example (a : Wiener) (y : Fin 2 → ℝ) : lift a y = ∑' k, a k * planeMode k y := lift_apply a y
example (a : Wiener) (y : Fin 2 → ℝ) (n : Gam) :
    lift a (fun j => y j + ((n j : ℤ) : ℝ)) = lift a y := lift_periodic a y n

/-- The Fourier derivative is the genuine coordinate derivative of the periodic lift. -/
example (u : Wiener1) (y : Fin 2 → ℝ) (j : Fin 2) :
    HasDerivAt (fun t : ℝ => lift (incl u) (Function.update y j t))
      (lift (fourierDeriv j u) y) (y j) := hasDerivAt_lift u y j

example (u : Wiener1) (y : Fin 2 → ℝ) (j : Fin 2) :
    deriv (fun t : ℝ => lift (incl u) (Function.update y j t)) (y j)
      = lift (fourierDeriv j u) y := deriv_lift u y j

/-- **The differentiation transfer stated on the torus itself.** -/
example (u : Wiener1) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => synth (incl u) (torusShift x j s))
      (synth (fourierDeriv j u) x) 0 := hasDerivAt_synth_torus u x j

example (u : Wiener1) (x : Torus2) (j : Fin 2) :
    deriv (fun s : ℝ => synth (incl u) (torusShift x j s)) 0
      = synth (fourierDeriv j u) x := deriv_synth_torus u x j

example (u : Wiener1) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => (synth (incl u) (torusShift x j s)).re)
      ((synth (fourierDeriv j u) x).re) 0 := hasDerivAt_re_synth_torus u x j

example (x : Torus2) (j : Fin 2) : torusShift x j 0 = x := torusShift_zero x j

/-- **Physical divergence freedom on the torus** for a genuine `Wiener1` kernel. -/
example (K u : Wiener1) (x : Torus2) :
    deriv (fun s : ℝ => synth (incl (-(kernelConvDeriv K u 1))) (torusShift x 0 s)) 0
      + deriv (fun s : ℝ => synth (incl (kernelConvDeriv K u 0)) (torusShift x 1 s)) 0 = 0 :=
  div_synth_velocity_eq_zero K u x

example (K u : Wiener1) :
    fourierDeriv 0 (-(kernelConvDeriv K u 1)) + fourierDeriv 1 (kernelConvDeriv K u 0) = 0 :=
  div_velocity_eq_zero K u

example (K u : Wiener1) :
    velocity (rotatedGradientSymbol K.coeff) (rotatedGradientSymbol_bdd K.isAdmissibleKernel)
        0 (incl u) = incl (-(kernelConvDeriv K u 1)) := velocity_eq_kernelConvDeriv_zero K u

/-! ### 5. Reality transfer and the velocity operator -/

example {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) (x : Torus2) :
    conj (synth a x) = synth a x := conj_synth_apply ha x
example (a : RealWiener) (x : Torus2) : ((realSynth a x : ℝ) : ℂ) = synth a.val x :=
  ofReal_realSynth a x
example : ‖realSynth‖ ≤ 1 := norm_realSynth_le
example : Function.Injective (realSynth : RealWiener → C(Torus2, ℝ)) := realSynth_injective

/-- Tier (b): a genuine `Wiener1` kernel gives the literal `R_K u = ∇^⊥(K * u)`. -/
example (K u : Wiener1) :
    velocity (rotatedGradientSymbol K.coeff) (rotatedGradientSymbol_bdd K.isAdmissibleKernel)
        0 (incl u) = -(fourierDeriv 1 (kernelConv K u)) := velocity_rotatedGradient_zero K u
example (K u : Wiener1) :
    velocity (rotatedGradientSymbol K.coeff) (rotatedGradientSymbol_bdd K.isAdmissibleKernel)
        1 (incl u) = fourierDeriv 0 (kernelConv K u) := velocity_rotatedGradient_one K u
example (K : Wiener1) : IsAdmissibleKernel K.coeff := K.isAdmissibleKernel

/-- The genuine finite-support kernel: nonzero, conjugate symmetric, synthesizable. -/
example : finiteKernel ≠ 0 := finiteKernel_ne_zero
example : ConjSymmetric finiteKernel.coeff := finiteKernel_conjSymmetric
example : synth (incl finiteKernel) = emode (unitFreq 0) + emode (-unitFreq 0) :=
  synth_finiteKernel
example (x : Torus2) :
    conj (synth (incl finiteKernel) x) = synth (incl finiteKernel) x :=
  synth_finiteKernel_real x

/-! ### 6. The physical transport commuting diagram -/

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v : Wiener1) :
    synth (transport m hm u v)
      = ∑ j : Fin 2, synth (velocity m hm j (incl u)) * synth (fourierDeriv j v) :=
  synth_transport m hm u v

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v : Wiener1) (x : Torus2) :
    synth (transport m hm u v) x
      = ∑ j : Fin 2, synth (velocity m hm j (incl u)) x * synth (fourierDeriv j v) x :=
  synth_transport_apply m hm u v x

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u : Wiener1) :
    synth (quadResidual m hm u)
      = ∑ j : Fin 2, synth (velocity m hm j (incl u)) * synth (fourierDeriv j u) :=
  synth_quadResidual m hm u

example {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (u : Wiener1) (k : Gam) :
    twoPiI * ((k 0 : ℤ) : ℂ)
        * (velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) 0 (incl u)) k
      + twoPiI * ((k 1 : ℤ) : ℂ)
        * (velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) 1 (incl u)) k = 0 :=
  rotatedGradient_velocity_div_zero hb u k

/-! ### 7. The paper-facing certificate -/

example {κ : Gam → ℂ} {A : ℝ} (hb : KernelBound κ A) (hc : ConjSymmetric κ) :
    PaperFacingQuadraticResidualCertificate hb hc := paperFacingCertificate hb hc

example : PaperFacingQuadraticResidualCertificate finiteKernel.kernelBound
    finiteKernel_conjSymmetric := finiteKernel_certificate

/-! ### 8. Spacetime -/

section Spacetime
variable {T : ℝ}

example : CompleteSpace (Curve0 T) := inferInstance

example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) :
    ‖(spacetimeTransport m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T)‖
      ≤ 4 * Real.pi * C := norm_spacetimeTransport_le hm hr hC

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    spacetimeQuadResidual m hm hr (0 : Curve1 T) = 0 := spacetimeQuadResidual_zero m hm hr

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    fderiv ℝ (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T) 0 = 0 :=
  fderiv_spacetimeQuadResidual_zero m hm hr

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    ContDiff ℝ 2 (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T) :=
  contDiff_two_spacetimeQuadResidual m hm hr

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    AnalyticOnNhd ℝ (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T) Set.univ :=
  analyticOnNhd_spacetimeQuadResidual m hm hr _

example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (H₁ H₂ : Curve1 T) :
    fderiv ℝ (fderiv ℝ (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T)) 0 H₁ H₂
      = spacetimeTransport m hm hr H₁ H₂ + spacetimeTransport m hm hr H₂ H₁ :=
  fderiv_fderiv_spacetimeQuadResidual m hm hr H₁ H₂

/-- Synthesis commutes with the spacetime residual at every time. -/
example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (U : Curve1 T) (t : TimeI T) (x : Torus2) :
    ((realSynth ((spacetimeQuadResidual m hm hr U) t) x : ℝ) : ℂ)
      = ∑ j : Fin 2, synth (velocity m hm j (incl (U t).val)) x
          * synth (fourierDeriv j (U t).val) x :=
  synth_spacetimeQuadResidual m hm hr U t x

end Spacetime

/-! ### 9. Fractional heat -/

example (α : ℝ) {t : ℝ} (ht : 0 ≤ t) : ‖heatOp α ht‖ ≤ 1 := norm_heatOp_le α ht
example (α : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (a : Wiener) :
    heatOp α hs (heatOp α ht a) = heatOp α (add_nonneg hs ht) a := heatOp_heatOp α hs ht a
example {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    (1 + r) * Real.exp (-(s * r)) ≤ 1 + 1 / s := one_add_mul_exp_le hs hr
example {β s u : ℝ} (hβ : 1 ≤ β) (hs : 0 < s) (hu : 0 ≤ u) :
    u * Real.exp (-(s * u ^ β)) ≤ s ^ (-(1 / β)) := mul_exp_neg_rpow_le hβ hs hu
example {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) :
    ‖heatSmooth hα ht a‖ ≤ (1 + t ^ (-(1 / (2 * α))) / Real.pi) * ‖a‖ :=
  norm_heatSmooth_le_sharp hα ht a
example {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) :
    ‖heatSmoothCLM hα ht‖ ≤ 1 + t ^ (-(1 / (2 * α))) / Real.pi :=
  norm_heatSmoothCLM_le_sharp hα ht
example {α : ℝ} (hα : 1 / 2 < α) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => 1 + t ^ (-(1 / (2 * α))) / Real.pi)
      MeasureTheory.volume 0 T := intervalIntegrable_heatConst hα T
example {α t : ℝ} (ht : 0 ≤ t) {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric ((heatOp α ht a : Wiener) : Gam → ℂ) := conjSymmetric_heatOp ht ha

/-! ### 9b. Strong continuity and the Duhamel integral -/

-- the heat orbit is norm continuous in time
example (α : ℝ) (a : Wiener) : Continuous fun t : ℝ => heatFlow α t a :=
  continuous_heatFlow α a

example {α t : ℝ} (ht : 0 ≤ t) (a : Wiener) : heatFlow α t a = heatOp α ht a :=
  heatFlow_eq ht a

-- the smoothing operator is jointly continuous away from `t = 0`
example {α : ℝ} (hα : 1 / 2 ≤ α) {t₀ : ℝ} (ht₀ : 0 < t₀) (a₀ : Wiener) :
    ContinuousAt (fun p : ℝ × Wiener => heatSmoothFun hα p.1 p.2) (t₀, a₀) :=
  continuousAt_heatSmoothFun hα ht₀ a₀

-- the heat flow contracts the *first-order* norm as well
example {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (u : Wiener1) :
    ‖heatSmoothFun hα t (incl u)‖ ≤ ‖u‖ := norm_heatSmoothFun_incl_le hα ht u

-- the Duhamel integrand is integrable up to the singular time
example {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t) {g : ℝ → Wiener} (hg : Continuous g)
    {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) :
    IntervalIntegrable (duhamelIntegrand hα.le t g) MeasureTheory.volume 0 t :=
  intervalIntegrable_duhamelIntegrand hα ht hg hM

-- the explicit value of the time integral of the smoothing constant
example {α : ℝ} (hα : 1 / 2 < α) (t : ℝ) :
    (∫ s in (0:ℝ)..t, (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi)) = duhamelConst α t :=
  integral_heatConst hα t

-- the Duhamel bound
example {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t) {g : ℝ → Wiener} {M : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) :
    ‖duhamelIntegral hα.le t g‖ ≤ M * duhamelConst α t :=
  norm_duhamelIntegral_le hα ht hM

-- the mild map, its self-map bound and its contraction bound
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {u : ℝ → Wiener1} {R : ℝ}
    (hR : ∀ s, ‖u s‖ ≤ R) {t : ℝ} (ht : 0 < t) :
    ‖mildMap hα.le hm u₀ u t‖ ≤ ‖u₀‖ + (4 * Real.pi * C * R * R) * duhamelConst α t :=
  norm_mildMap_le hα hm hC u₀ hR ht

example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {R : ℝ} (hR : 0 < R) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧ ∀ (u v : ℝ → Wiener1), Continuous u → Continuous v →
      (∀ s, ‖u s‖ ≤ R) → (∀ s, ‖v s‖ ≤ R) → ∀ (D : ℝ), (∀ s, ‖u s - v s‖ ≤ D) →
        ∀ t ∈ Set.Icc (0:ℝ) T,
          ‖mildMap hα.le hm u₀ u t - mildMap hα.le hm u₀ v t‖ ≤ D / 2 :=
  exists_local_contraction hα hm hC hR u₀

/-! ### 9c. Continuity in time of the Duhamel term and of the mild map -/

-- the reflected form of the Duhamel integral
example {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) {t : ℝ} (ht : 0 ≤ t) :
    duhamelIntegral hα t g = ∫ r in (0:ℝ)..t, duhamelKernel hα g t r :=
  duhamelIntegral_eq_reflected hα g ht

-- the Duhamel term is a continuous curve
example {α : ℝ} (hα : 1 / 2 < α) {g : ℝ → Wiener} (hg : Continuous g) {M : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) : Continuous fun t : ℝ => duhamelIntegral hα.le t g :=
  continuous_duhamelIntegral hα hg hM

-- the first-order heat flow: identity at `t = 0`, contractive, strongly continuous
example (α : ℝ) (u : Wiener1) : heatFlow1 α 0 u = u := heatFlow1_zero α u
example (α t : ℝ) (u : Wiener1) : ‖heatFlow1 α t u‖ ≤ ‖u‖ := norm_heatFlow1_le α t u
example (α : ℝ) (u : Wiener1) : Continuous fun t : ℝ => heatFlow1 α t u :=
  continuous_heatFlow1 α u

-- the mild map starts at the datum and is a continuous curve
example {α : ℝ} (hα : 1 / 2 ≤ α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (u₀ : Wiener1)
    (u : ℝ → Wiener1) : mildMap1 hα hm u₀ u 0 = u₀ := mildMap1_zero hα hm u₀ u

example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {u : ℝ → Wiener1} (hu : Continuous u) {R : ℝ}
    (hR : ∀ s, ‖u s‖ ≤ R) : Continuous fun t : ℝ => mildMap1 hα.le hm u₀ u t :=
  continuous_mildMap1 hα hm hC u₀ hu hR

/-! ### 9d. The local mild solution -/

-- clamping and extension
example {T : ℝ} (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) : Continuous (extendCurve hT U) :=
  continuous_extendCurve hT U

-- **local existence of a mild solution**
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * C * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u) :=
  exists_local_mild_solution hα hm hC u₀

-- the same for the source-faithful rotated-gradient velocity
example {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ} {A : ℝ} (hb : KernelBound κ A)
    (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * (2 * Real.pi * A) * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀
          - duhamelIntegral hα.le t
              (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u) :=
  exists_local_mild_solution_rotatedGradient hα hb u₀

-- **uniqueness** where the contraction factor is at most `1/2`
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {R T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2)
    {u v : ℝ → Wiener1} (hu : Continuous u) (hv : Continuous v)
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R)
    (heu : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u))
    (hev : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm v)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t :=
  mild_solution_unique hα hm hC u₀ hT hsmall hu hv hRu hRv heu hev

-- **local well-posedness**: existence and uniqueness on one interval
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
        (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) ∧
      (∀ u v : ℝ → Wiener1, Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ 2 * ‖u₀‖ + 1) → (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          v t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t) :=
  exists_local_mild_solution_unique hα hm hC u₀

-- **continuous dependence on the datum**
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ v₀ : Wiener1) {R T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2)
    {u v : ℝ → Wiener1} (hu : Continuous u) (hv : Continuous v)
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R)
    (heu : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u))
    (hev : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = heatFlow1 α t v₀ - duhamelIntegral hα.le t (quadCurve hm v)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t - v t‖ ≤ 2 * ‖u₀ - v₀‖ :=
  mild_solution_stability hα hm hC u₀ v₀ hT hsmall hu hv hRu hRv heu hev

-- **Hadamard local well-posedness**
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧
      (∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
        (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) ∧
      (∀ u v : ℝ → Wiener1, Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ 2 * ‖u₀‖ + 1) → (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          v t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t) ∧
      (∀ (v₀ : Wiener1) (u v : ℝ → Wiener1), Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ 2 * ‖u₀‖ + 1) → (∀ s, ‖v s‖ ≤ 2 * ‖u₀‖ + 1) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T,
          v t = heatFlow1 α t v₀ - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t - v t‖ ≤ 2 * ‖u₀ - v₀‖) :=
  exists_local_well_posed hα hm hC u₀

/-! ### 9e. Reality of the mild solution -/

-- the Duhamel integral of a real source is real
example {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t) {g : ℝ → Wiener} (hgc : Continuous g)
    {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) (hg : ∀ s, ConjSymmetric ((g s : Gam → ℂ))) :
    ConjSymmetric (duhamelIntegral hα.le t g).coeff :=
  conjSymmetric_duhamelIntegral hα ht hgc hM hg

-- the mild map preserves reality
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u₀ : Wiener1}
    (h₀ : ConjSymmetric u₀.coeff) {u : ℝ → Wiener1} (huc : Continuous u) {R : ℝ}
    (hR : ∀ s, ‖u s‖ ≤ R) (hu : ∀ s, ConjSymmetric (u s).coeff) {t : ℝ} (ht : 0 ≤ t) :
    ConjSymmetric (mildMap1 hα.le hm u₀ u t).coeff :=
  conjSymmetric_mildMap1 hα hm hr hC h₀ huc hR hu ht

-- **the local mild solution of a real datum is real**
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u₀ : Wiener1}
    (h₀ : ConjSymmetric u₀.coeff) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * C * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      (∀ t, ConjSymmetric (u t).coeff) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u) :=
  exists_local_mild_solution_real hα hm hr hC h₀

-- the paper-facing version: real kernel, real datum, `∇^⊥(κ ∗ ·)` velocity
example {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ} {A : ℝ} (hb : KernelBound κ A)
    (hc : ConjSymmetric κ) {u₀ : Wiener1} (h₀ : ConjSymmetric u₀.coeff) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * (2 * Real.pi * A) * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      (∀ t, ConjSymmetric (u t).coeff) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀
          - duhamelIntegral hα.le t
              (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u) :=
  exists_local_mild_solution_real_rotatedGradient hα hb hc h₀

/-! ### 9f. The solution as a physical field on the torus -/

example {u : ℝ → Wiener1} (hu : Continuous u) :
    Continuous fun p : ℝ × Torus2 => physField u p.1 p.2 := continuous_physField hu

example {u : ℝ → Wiener1} (hu : ∀ t, ConjSymmetric (u t).coeff) (t : ℝ) (x : Torus2) :
    ((physField u t x : ℝ) : ℂ) = synth (incl (u t)) x := ofReal_physField hu t x

-- **the paper-facing physical statement**
example {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ} {A : ℝ} (hb : KernelBound κ A)
    (hc : ConjSymmetric κ) {u₀ : Wiener1} (h₀ : ConjSymmetric u₀.coeff) :
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
              (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u) :=
  exists_local_physical_mild_solution hα hb hc h₀

-- the physical form of the equation along a curve
example (u : ℝ → Wiener1) (t : ℝ) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => physField u t (torusShift x j s))
      ((synth (fourierDeriv j (u t)) x).re) 0 := hasDerivAt_physField u t x j

example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (u : ℝ → Wiener1) (t : ℝ) (x : Torus2) :
    synth (quadCurve hm u t) x
      = ∑ j : Fin 2, synth (velocity m hm j (incl (u t))) x
          * synth (fourierDeriv j (u t)) x := synth_quadCurve_apply hm u t x

/-! ### 9g. The forced equation -/

example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {F : ℝ → Wiener} (hF : Continuous F) {MF : ℝ}
    (hMF : ∀ s, ‖F s‖ ≤ MF) :
    ∃ T : ℝ, 0 < T ∧ ∃ (u : ℝ → Wiener1) (R : ℝ), Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ R) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm u) :=
  exists_local_mild_solution_forced hα hm hC u₀ hF hMF

example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {F : ℝ → Wiener} (hF : Continuous F) {MF : ℝ}
    (hMF : ∀ s, ‖F s‖ ≤ MF) :
    ∃ (T : ℝ) (R : ℝ), 0 < T ∧
      (∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧ (∀ t, ‖u t‖ ≤ R) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm u)) ∧
      (∀ u v : ℝ → Wiener1, Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ R) → (∀ s, ‖v s‖ ≤ R) →
        (∀ t ∈ Set.Icc (0:ℝ) T, u t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T, v t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t) :=
  exists_local_forced_well_posed hα hm hC u₀ hF hMF

-- the abstract affine fixed point behind both cases
example {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (A : ℝ → Wiener1) (hA : Continuous A) {a : ℝ}
    (haA : ∀ t, ‖A t‖ ≤ a) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T,
      (8 * Real.pi * C * (2 * a + 1) + 4 * Real.pi * C * (2 * a + 1) * (2 * a + 1))
        * duhamelConst α t ≤ 1 / 2) :
    (∀ V : TimeI T →ᵇ Wiener1, ‖V‖ ≤ 2 * a + 1 →
        ‖affineCurveMap hα hm hC A hA hT V‖ ≤ 2 * a + 1) ∧
    ∃ U : TimeI T →ᵇ Wiener1, ‖U‖ ≤ 2 * a + 1 ∧
      affineCurveMap hα hm hC A hA hT U = U ∧
      Tendsto (fun n : ℕ => (affineCurveMap hα hm hC A hA hT)^[n] 0) atTop (𝓝 U) :=
  exists_affineCurve_fixedPoint hα hm hC A hA haA hT hsmall

-- **the source-faithful nonlinearity is not identically zero**
example {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (hκ : κ (unitFreq 0) ≠ 0) :
    transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) ≠ 0 :=
  transport_rotatedGradient_ne_zero hb hκ

example : transport (rotatedGradientSymbol finiteKernel.coeff)
    (rotatedGradientSymbol_bdd finiteKernel_admissible) ≠ 0 := transport_finiteKernel_ne_zero

-- the local-solution certificate
example {α : ℝ} (hα : 1 / 2 < α) {κ : Gam → ℂ} {A : ℝ} (hb : KernelBound κ A)
    (hc : ConjSymmetric κ) {u₀ : Wiener1} (h₀ : ConjSymmetric u₀.coeff) :
    ∃ (T : ℝ) (u : ℝ → Wiener1), LocalMildSolutionCertificate hα hb hc u₀ h₀ T u :=
  exists_localMildSolutionCertificate hα hb hc h₀

example : ∃ (T : ℝ) (u : ℝ → Wiener1),
    LocalMildSolutionCertificate concreteAlpha finiteKernel.kernelBound
      finiteKernel_conjSymmetric finiteKernel finiteKernel_conjSymmetric T u :=
  exists_concrete_localMildSolutionCertificate

-- **a completely concrete instance**: α = 3/4, explicit real kernel and datum
example :
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
              (quadCurve (rotatedGradientSymbol_bdd finiteKernel_admissible) u) :=
  exists_concrete_local_physical_solution

/-! ### 12. v3.0: the Duhamel operator on a fixed interval -/

section V3
variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

example (hα : 1 / 2 < α) (hT : 0 ≤ T) :
    ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ ≤ duhamelConst α T := norm_duhamelOp_le hα hT

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (V : Curve0 T) (t : TimeI T) :
    ((duhamelOp hα hT V) t).val = duhamelIntegral hα.le (t : ℝ) (sourceFun hT V) :=
  duhamelOp_apply_val hα hT V t

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (V : Curve0 T) :
    (duhamelOp hα hT V) ⟨0, ⟨le_rfl, hT⟩⟩ = 0 := duhamelOp_zero_time hα hT V

-- independence of the extension outside `[0,T]`
example (hα : 1 / 2 < α) (hT : 0 ≤ T) (V : Curve0 T) {g : ℝ → Wiener}
    (hg : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) T), g s = (V ⟨s, hs⟩).val) (t : TimeI T) :
    ((duhamelOp hα hT V) t).val = duhamelIntegral hα.le (t : ℝ) g :=
  duhamelOp_eq_of_agrees hα hT V hg t

-- the concrete quadratic operator `B_K = J_T ∘ N_K`
example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (U V : Curve1 T) :
    sourceQuad hα hT m hm hr U V = duhamelOp hα hT (spacetimeTransport m hm hr U V) := rfl

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) :
    ‖(sourceQuad hα hT m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve1 T)‖
      ≤ duhamelConst α T * (4 * Real.pi * C) := norm_sourceQuad_le hα hT hm hr hC

/-! ### 13. v3.0: the source-to-solution map -/

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    sourceSolution hα hT hm hr (0 : Curve0 T) = 0 := sourceSolution_zero hα hT hm hr

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    ContDiffAt ℝ 2 (sourceSolution hα hT hm hr) (0 : Curve0 T) :=
  contDiffAt_sourceSolution hα hT hm hr

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    ∀ᶠ f in nhds (0 : Curve0 T),
      sourceSolution hα hT hm hr f
        + sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f)
            (sourceSolution hα hT hm hr f) = duhamelOp hα hT f :=
  eventually_sourceSolution_eq hα hT hm hr

-- existence on an explicit ball, for a prescribed horizon
example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) {b : ℝ}
    (hb : ‖(sourceQuad hα hT m hm hr)‖ ≤ b) (hb0 : 0 ≤ b) (f : Curve0 T)
    (hf : ‖duhamelOp hα hT f‖ ≤ 1 / (8 * (b + 1))) :
    ∃ u : Curve1 T, ‖u‖ ≤ 1 / (4 * (b + 1)) ∧
      u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f :=
  exists_mild_curve_of_small hα hT hm hr hb hb0 f hf

-- the pointwise (v2-style) form of the equation
example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {u : Curve1 T} {f : Curve0 T}
    (h : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (t : TimeI T) :
    (u t).val = duhamelIntegral hα.le (t : ℝ) (sourceFun hT f)
      - duhamelIntegral hα.le (t : ℝ)
          (fun s => transport m hm (u (clampT hT s)).val (u (clampT hT s)).val) :=
  mild_pointwise_of_curve hα hT hm hr h t

/-! ### 14. v3.0: the source variations -/

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T)
      = (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T) := fderiv_sourceSolution_zero hα hT hm hr

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (h₁ h₂ : Curve0 T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = -(duhamelOp hα hT
            (spacetimeTransport m hm hr (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
              + spacetimeTransport m hm hr (duhamelOp hα hT h₂) (duhamelOp hα hT h₁))) :=
  fderiv_fderiv_sourceSolution_apply' hα hT hm hr h₁ h₂

example (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁)
    (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) :
    fderiv ℝ (sourceSolution hα hT hm₁ hr₁) (0 : Curve0 T)
      = fderiv ℝ (sourceSolution hα hT hm₂ hr₂) (0 : Curve0 T) :=
  fderiv_sourceSolution_kernel_independent hα hT hm₁ hr₁ hm₂ hr₂

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) : SourceResponseCertificate hα hT hm hr hC :=
  sourceResponseCertificate hα hT hm hr hC

end V3

/-! ### 15. v3.0: the symmetrized (Hessian) non-degeneracy -/

example {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (a b k : Gam) :
    (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) (dirac1 a) (dirac1 b)) k
      = if k = a + b then ∑ j : Fin 2, rotatedGradientSymbol κ j a * (twoPiI * ((b j : ℤ) : ℂ))
        else 0 := transport_dirac1 _ _ a b k

example :
    fderiv ℂ (fderiv ℂ (quadResidual (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible)))
      0 (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1)) ≠ 0 :=
  fderiv_fderiv_quadResidual_finiteKernel_ne_zero

-- the cancellation regression: ordered ≠ 0 but symmetrized = 0
example :
    (transport (rotatedGradientSymbol exampleKernel)
        (rotatedGradientSymbol_bdd exampleKernel_admissible)
        (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))
      + transport (rotatedGradientSymbol exampleKernel)
        (rotatedGradientSymbol_bdd exampleKernel_admissible)
        (dirac1 (unitFreq 1)) (dirac1 (unitFreq 0))) (unitFreq 0 + unitFreq 1) = 0 :=
  transport_exampleKernel_symmetrized_eq_zero

example :
    (quadResidual (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible) realPacket)
      (unitFreq 0 + unitFreq 1) = twoPiI * twoPiI := quadResidual_realPacket_coeff

example : quadResidual (rotatedGradientSymbol finiteKernel.coeff)
    (rotatedGradientSymbol_bdd finiteKernel_admissible) realPacket ≠ 0 :=
  quadResidual_realPacket_ne_zero

-- the single cosine has zero self-advection
example : quadResidual (rotatedGradientSymbol finiteKernel.coeff)
    (rotatedGradientSymbol_bdd finiteKernel_admissible) finiteKernel = 0 :=
  quadResidual_finiteKernel_self_zero

-- a nonzero REAL second derivative at the two-mode real packet
example :
    fderiv ℝ (fderiv ℝ (realQuadResidual (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric))) 0
      realPacketR realPacketR ≠ 0 :=
  fderiv_fderiv_realQuadResidual_realPacket_ne_zero

/-! ### 16. v3.0: the coefficient evolution equation -/

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    deriv (fun r : ℝ => (curveState hT u r).coeff k) t
        + (((4 * Real.pi ^ 2 * (((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2)) ^ α : ℝ) : ℂ)
            * (curveState hT u t).coeff k
        + (quadCurve hm (curveState hT u) t) k
      = (sourceFun hT f t) k :=
  coeff_evolution_of_mild hα hT hm hr hC hmild k ht0 htT

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    curveState hT u 0 = 0 := curveState_initial_of_mild hα hT hm hr hmild

/-! ### 17. v3.0: the weak coefficient and weak physical equations -/

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T, (-((curveState hT u t).coeff k) * deriv φ t
        + (fracSymbol α k : ℂ) * (curveState hT u t).coeff k * φ t
        + (quadCurve hm (curveState hT u) t) k * φ t
        - (sourceFun hT f t) k * φ t)) = 0 :=
  weak_coeff_of_mild_contDiff hα hT hm hr hC hmild k hφ hsupp

-- the genuinely physical weak equation, tested against a finite Fourier polynomial
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (F : Finset Gam) (c : Gam → ℂ) {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T,
        (-(spacePair (incl (curveState hT u t)) (trigPoly F c)) * ψ t
          + (spacePair (incl (curveState hT u t)) (fracLapPoly α F c)) * φ t
          + (spacePair (quadCurve hm (curveState hT u) t) (trigPoly F c)) * φ t
          - (spacePair (sourceFun hT f t) (trigPoly F c)) * φ t)) = 0 :=
  weak_physical_of_mild hα hT hm hr hC hmild F c hφ hψ hφderiv hsupp

-- the spatial pairing really is an integral over the torus
example (a : Wiener) (F : Finset Gam) (c : Gam → ℂ) :
    (∫ x : Torus2, synth a x * trigPoly F c x) = ∑ j ∈ F, c j * a (-j) :=
  integral_synth_mul_trigPoly a F c

/-! ### 18. v3.0: the evolution equations of the source variations -/

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) (k : Gam) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt
      (fun r : ℝ =>
        (curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) r).coeff k)
      ((sourceFun hT h t) k - (fracSymbol α k : ℂ)
        * (curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).coeff k) t :=
  hasDerivAt_coeff_fderiv_sourceSolution hα hT hm hr h k ht0 htT

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = duhamelOp hα hT (secondVariationSource hα hT hm hr h₁ h₂) :=
  fderiv_fderiv_sourceSolution_eq_duhamelOp hα hT hm hr h₁ h₂

/-! ### 19. v3.0: integrable torus kernels -/

-- the actual convolution integral of an integrable kernel is the Fourier multiplier
example {K : Torus2 → ℂ} (hK : MeasureTheory.Integrable K
      (MeasureTheory.volume : MeasureTheory.Measure Torus2)) (a : Wiener) (x : Torus2) :
    (∫ y : Torus2, K y * synth a (x - y))
      = synth (mult (kernelCoeff K) (kernelCoeff_bdd hK) a) x :=
  torusConv_synth hK a x

-- the rotated-gradient velocity identity, by differentiation in the state variable
example {K : Torus2 → ℂ} (hK : MeasureTheory.Integrable K
      (MeasureTheory.volume : MeasureTheory.Measure Torus2)) {A : ℝ}
    (hA : KernelBound (kernelCoeff K) A) (u : Wiener1) (x : Torus2) :
    synth (velocity (rotatedGradientSymbol (kernelCoeff K))
        (rotatedGradientSymbol_bdd ⟨A, hA⟩) 0 (incl u)) x
      = -(deriv (fun s : ℝ => torusConv K (synth (incl u)) (torusShift x 1 s)) 0) :=
  velocity_integrableKernel_zero hK hA u x

-- the weighted multiplier bound really follows from nonzero-mode decay plus a finite mean
example {K : Torus2 → ℂ} (hK : MeasureTheory.Integrable K
      (MeasureTheory.volume : MeasureTheory.Measure Torus2)) {D : ℝ}
    (hD : NonzeroModeDecay (kernelCoeff K) D) : IsAdmissibleKernel (kernelCoeff K) :=
  isAdmissibleKernel_kernelCoeff_of_decay hK hD

-- physical divergence freedom without the `K : Wiener1` restriction
example {κ : Gam → ℂ} {A : ℝ} (hA : KernelBound κ A) (u : Wiener1) (x : Torus2) :
    deriv (fun s : ℝ => synth (incl (-(symbolConvDeriv hA u 1))) (torusShift x 0 s)) 0
      + deriv (fun s : ℝ => synth (incl (symbolConvDeriv hA u 0)) (torusShift x 1 s)) 0 = 0 :=
  div_synth_velocity_symbol_eq_zero hA u x

-- the corrected kernel predicates
example (k : Gam) : absK k ≤ wt k := absK_le_wt k
example {k : Gam} (hk : k ≠ 0) : wt k ≤ 3 * absK k := wt_le_three_absK hk

-- the magnitude predicate is strictly weaker than ordered ellipticity
example : FourierMagnitudeBounds (fun _ : Gam => (0 : ℂ)) 0 0 := fourierMagnitudeBounds_zero
example : FourierMagnitudeBounds (fun k => -exampleKernel k) 1 1 :=
  fourierMagnitudeBounds_neg_exampleKernel
example (k : Gam) : ((-exampleKernel k : ℂ)).re < 0 := neg_exampleKernel_re_neg k
example {c D : ℝ} : ¬ OrderedFourierEllipticity (fun k => -exampleKernel k) c D :=
  not_orderedFourierEllipticity_neg_exampleKernel
example {c D : ℝ} : ¬ OrderedFourierEllipticity (fun _ : Gam => (0 : ℂ)) c D :=
  not_orderedFourierEllipticity_zero

-- a genuine positive witness of the ordered condition, and the justified weaker bounds
example : OrderedFourierEllipticity exampleKernel (1/3) 1 := orderedFourierEllipticity_exampleKernel
example {κ : Gam → ℂ} {c D : ℝ} (h : OrderedFourierEllipticity κ c D) :
    FourierMagnitudeBounds κ c (3 * D) := h.fourierMagnitudeBounds
example {κ : Gam → ℂ} {c D : ℝ} (h : OrderedFourierEllipticity κ c D) {k : Gam} (hk : k ≠ 0) :
    0 < (κ k).re := h.re_pos hk

-- the finite-support test kernel is outside the elliptic class, in either formulation
example {c D : ℝ} : ¬ OrderedFourierEllipticity finiteKernel.coeff c D :=
  finiteKernel_not_orderedFourierEllipticity
example {c D : ℝ} (hc : 0 < c) : ¬ FourierMagnitudeBounds finiteKernel.coeff c D :=
  finiteKernel_not_fourierMagnitudeBounds hc
example : NonzeroModeDecay finiteKernel.coeff ‖finiteKernel‖ := finiteKernel_nonzeroModeDecay

/-! ### 20. v3.0: a nonzero mixed second source response -/

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 < T) {g : Curve0 T}
    (h : duhamelOp hα hT.le g = 0) : g = 0 := eq_zero_of_duhamelOp_eq_zero hα hT h

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 < T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le
        (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric)))
      (0 : Curve0 T) (packetSource T) (packetSource T) ≠ 0 :=
  fderiv_fderiv_sourceSolution_packet_ne_zero hα hT

/-! ### 21. v4.0: the physical `L²` identification and Parseval -/

example (a : Wiener) : (∫ x : Torus2, ‖synth a x‖ ^ 2) = ∑' k : Gam, ‖a k‖ ^ 2 :=
  integral_norm_sq_synth a

example (a b : Wiener) : (inner ℂ (synthL2 a) (synthL2 b) : ℂ) = ∑' k : Gam, conj (a k) * b k :=
  inner_synthL2 a b

example (a : Wiener) : ‖synthL2 a‖ ^ 2 = ∑' k : Gam, ‖a k‖ ^ 2 := norm_synthL2_sq a

example : Orthonormal ℂ (fun k : Gam => synthL2 (wdirac k)) := orthonormal_synthL2_wdirac

-- the coefficient ℓ² space embeds isometrically in the physical L²
example (c : Wiener2) : ‖coeffL2 c‖ = ‖c‖ := norm_coeffL2 c
example (a : Wiener) : coeffL2 (toWiener2 a) = synthL2 a := coeffL2_toWiener2 a

/-! ### 22. v4.0: the `L²`-in-time estimate and the strong equation -/

-- the scalar energy estimate, with constant one
example {T lam : ℝ} (hT : 0 ≤ T) (hlam : 0 < lam) {w g : ℝ → ℂ}
    (hw : Continuous w) (hg : Continuous g) (hw0 : w 0 = 0)
    (hderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt w (g t - (lam : ℂ) * w t) t) :
    lam ^ 2 * (∫ t in (0:ℝ)..T, ‖w t‖ ^ 2) ≤ ∫ t in (0:ℝ)..T, ‖g t‖ ^ 2 :=
  energy_estimate hT hlam hw hg hw0 hderiv

-- the zero mode is handled separately: λ₀ = 0
example {α : ℝ} (hα : 0 < α) : fracSymbol α (0 : Gam) = 0 := fracSymbol_zero_eq hα

-- the per-mode estimate, valid at every frequency including zero
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam) :
    (fracSymbol α k) ^ 2
        * (∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2)
      ≤ ∫ t in (0:ℝ)..T, ‖(sourceFun hT g t) k‖ ^ 2 :=
  integral_fracSymbol_sq_coeff_duhamelOp_le hα hT g k

-- the summed L²-in-time estimate on the fractional multiplier
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    (∑' k : Gam, (fracSymbol α k) ^ 2
        * ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2)
      ≤ T * ‖g‖ ^ 2 := tsum_integral_fracSymbol_sq_le hα hT g

-- almost-everywhere square summability (the Tonelli interchange)
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      Summable fun k : Gam =>
        ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 :=
  ae_summable_fracSymbol_sq hα hT g

-- the strong equation in integrated Bochner form, with the trace at zero
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) :
    incl (curveState hT (duhamelOp hα hT g) t) + fracTimeIntegral hα hT g t
      = ∫ s in (0:ℝ)..t, sourceFun hT g s := strong_equation_integrated hα hT g t

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam) :
    (curveState hT (duhamelOp hα hT g) 0).coeff k = 0 := coeff_duhamelOp_initial hα hT g k

-- H^{2α} regularity almost everywhere, not inferred from A¹
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α) (curveState hT (duhamelOp hα hT g) t).coeff :=
  ae_memSobolev_duhamelOp hα hT g

-- applied to the nonlinear state and to both responses
example {α T : ℝ} {m : Fin 2 → Gam → ℂ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    u = duhamelOp hα hT (f - spacetimeTransport m hm hr u u) :=
  mild_curve_eq_duhamelOp hα hT hm hr hmild

example {α T : ℝ} {m : Fin 2 → Gam → ℂ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) :
    ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α)
        (curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).coeff :=
  ae_memSobolev_firstResponse hα hT hm hr h

example {α T : ℝ} {m : Fin 2 → Gam → ℂ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α)
        (curveState hT (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr))
          (0 : Curve0 T) h₁ h₂) t).coeff :=
  ae_memSobolev_secondResponse hα hT hm hr h₁ h₂

/-! ### 23. v4.0: localized sources and the observation maps -/

-- the localized sources form an honest ℝ-submodule
noncomputable example {T : ℝ} (hT : 0 ≤ T) (W : Set Torus2) : Submodule ℝ (Curve0 T) :=
  localizedSources hT W

-- compact support inside W × (0,T) is strictly stronger than vanishing outside W
example {T : ℝ} {hT : 0 ≤ T} {W : Set Torus2} {V : Curve0 T}
    (h : CompactlySupportedIn hT W V) : SourceSupportedIn hT W V := h.supportedIn

-- the observation maps are the actual physical maps, and bounded linear
example {T : ℝ} (hT : 0 ≤ T) (t : TimeI T) (u : Curve1 T) :
    statePhysCLM hT t u = statePhys hT u (t : ℝ) := statePhysCLM_apply hT t u
example {T : ℝ} (hT : 0 ≤ T) (u : Curve1 T) (t : TimeI T) :
    ‖statePhys hT u (t : ℝ)‖ ≤ ‖u‖ := norm_statePhys_le hT u t
example {T : ℝ} (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) (hT : 0 ≤ T)
    (t : TimeI T) (u : Curve1 T) :
    velocityPhysCLM m hm j hT t u = velocityPhys m hm j hT u (t : ℝ) :=
  velocityPhysCLM_apply m hm j hT t u

-- a common neighbourhood of the zero source for two kernels
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (hr₂ : IsRealSymbol m₂) (W : Set Torus2) :
    ∃ ε > 0, BothMildOn hα hT W hm₁ hr₁ hm₂ hr₂ ε :=
  exists_bothMildOn hα hT W hm₁ hr₁ hm₂ hr₂

-- the bridge, and non-vacuity conditional on the one missing profile
example {T : ℝ} (hT : 0 ≤ T) {W : Set Torus2} (a : RealWiener) {χ : ℝ → ℝ}
    (hχ : Continuous χ) (ha : ∀ x ∉ W, synth a.val x = 0) :
    productSource hT a hχ ∈ localizedSources hT W :=
  productSource_mem_localizedSources hT a hχ ha

example {T : ℝ} (hT : 0 < T) {W : Set Torus2} (h : HasLocalizedProfile W) :
    ∃ V ∈ localizedSources hT.le W, V ≠ 0 := exists_nonzero_localizedSource hT h

/-! ### 24. v4.0: local cancellation on the observation region -/

-- a state vanishing on an open set has vanishing spatial derivatives there
example {W : Set Torus2} (hW : IsOpen W) {v : Wiener1}
    (hv : ∀ x ∈ W, synth (incl v) x = 0) (j : Fin 2) {x : Torus2} (hx : x ∈ W) :
    synth (fourierDeriv j v) x = 0 := synth_fourierDeriv_eq_zero_of_vanishes hW hv j hx

-- the physical transport terms agree on W
example {W : Set Torus2} (hW : IsOpen W) {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁)
    (hm₂ : IsBddSymbol m₂) {u₁ u₂ : Wiener1}
    (hstate : ∀ x ∈ W, synth (incl u₁) x = synth (incl u₂) x)
    (hvel : ∀ (j : Fin 2), ∀ x ∈ W,
      synth (velocity m₁ hm₁ j (incl u₁)) x = synth (velocity m₂ hm₂ j (incl u₂)) x)
    {x : Torus2} (hx : x ∈ W) :
    synth (transport m₁ hm₁ u₁ u₁) x = synth (transport m₂ hm₂ u₂ u₂) x :=
  synth_transport_congr_on hW hm₁ hm₂ hstate hvel hx

-- the source cancels: the difference is a Duhamel response
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (hr₂ : IsRealSymbol m₂) {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT f)
    (h₂ : u₂ + sourceQuad hα hT m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT f) :
    u₁ - u₂ = duhamelOp hα hT
      (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) :=
  diff_eq_duhamelOp hα hT hm₁ hr₁ hm₂ hr₂ h₁ h₂

/-! ### 25. v4.0: the conditional UCP bridge and the generated-source identity -/

-- the external hypothesis is a Prop, never an axiom
example (α : ℝ) (W : Set Torus2) : Prop := FractionalUCP α W

-- injectivity of the Duhamel operator, used to derive the generated identity
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 < T) {g : Curve0 T}
    (h : duhamelOp hα hT.le g = 0) : g = 0 := eq_zero_of_duhamelOp_eq_zero hα hT h

-- polarization
example {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {B : E →L[ℝ] E →L[ℝ] F} {a b : E}
    (ha : quad B a = 0) (hb : quad B b = 0) (hab : quad B (a + b) = 0) :
    B a b + B b a = 0 := polarization_of_quad_zero ha hb hab

/-! ### 26. v4.0: the Section 6 tested output -/

-- the pairing is the actual integral over the torus
example (A B : Wiener) : wpair A B = ∫ x : Torus2, synth A x * synth B x :=
  wpair_eq_integral A B

-- the rotated-gradient symbol is divergence free
example (κ : Gam → ℂ) : IsDivFreeSymbol (rotatedGradientSymbol κ) :=
  rotatedGradientSymbol_isDivFree κ

-- spatial integration by parts: skew-adjointness of the transport form
example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hdiv : IsDivFreeSymbol m)
    (a b ψ : Wiener1) :
    wpair (transport m hm a b) (incl ψ) = - wpair (incl b) (transport m hm a ψ) :=
  wpair_transport_skew hm hdiv a b ψ

-- the tested symmetrized interaction, with its exact sign
example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hdiv : IsDivFreeSymbol m)
    (v₁ v₂ ψ : Wiener1) :
    wpair (transport m hm v₁ v₂ + transport m hm v₂ v₁) (incl ψ)
      = -(wpair (incl v₂) (transport m hm v₁ ψ)) - wpair (incl v₁) (transport m hm v₂ ψ) :=
  wpair_symmetrized_transport hm hdiv v₁ v₂ ψ

/-! ### 27. v5.0: smoothness discharges summability, and Fourier inversion -/

-- the Fourier coefficients of a smooth doubly periodic function are absolutely summable:
-- smoothness *proves* membership in the Wiener algebra, it is not assumed
example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) : Summable fun k : Gam => ‖pcoeff G k‖ :=
  summable_norm_pcoeff h

-- the decay estimate behind it
example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Gam,
      ‖pcoeff G k‖ ≤ C * (decayWeight (k 0) * decayWeight (k 1)) := exists_pcoeff_decay h

-- two genuine integrations by parts in each variable (boundary terms cancel by periodicity)
example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    pcoeff (pd1 (pd1 G)) k = (twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2 * pcoeff G k := pcoeff_pd1_two h k

example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    pcoeff (pd0 (pd0 G)) k = (twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2 * pcoeff G k := pcoeff_pd0_two h k

-- synthesis recovers the prescribed physical source
example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (y : Fin 2 → ℝ) :
    lift (wienerOfSmooth G h) y = G (y 0, y 1) := lift_wienerOfSmooth h y

example {a : Wiener} (h : SmoothWiener a) :
    wienerOfSmooth (planeLift a) (isSmoothPeriodic_planeLift h) = a := wienerOfSmooth_planeLift h

/-! ### 28. v5.0: an actual nonzero smooth compactly supported source -/

-- a nonzero real smooth spatial bump supported in a compact subset of any nonempty open `W`
example {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (a : RealWiener) (K : Set Torus2),
      a ≠ 0 ∧ SmoothWiener a.val ∧ IsCompact K ∧ K ⊆ W ∧ ∀ x ∉ K, synth a.val x = 0 :=
  exists_smooth_localized_profile hW hne

-- a genuinely `C^∞` compactly supported time bump in `(0,T)`
example {T : ℝ} (hT : 0 < T) : ∃ χ : ℝ → ℝ, IsSmoothTimeBump T χ ∧ χ (T / 2) = 1 :=
  exists_smooth_time_bump hT

-- the spatial profiles form a real vector space
noncomputable example (W : Set Torus2) : Submodule ℝ RealWiener := smoothProfiles W

-- the space-time source space is a real vector space, and the product source is a nonzero
-- member which is compactly supported strictly inside `W × (0,T)`
noncomputable example {T : ℝ} (hT : 0 < T) (W : Set Torus2) : Submodule ℝ (Curve0 T) :=
  smoothSources hT W

example {T : ℝ} (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ V ∈ smoothSources hT W, V ≠ 0 ∧ CompactlySupportedIn hT.le W V :=
  exists_nonzero_smoothSource hT hW hne

-- compact support strictly inside `W × (0,T)`, and the inclusion in the localized class
example {T : ℝ} (hT : 0 < T) (W : Set Torus2) :
    smoothSources hT W ≤ compactlySupportedSources hT W :=
  smoothSources_le_compactlySupported hT W

example {T : ℝ} (hT : 0 < T) (W : Set Torus2) :
    smoothSources hT W ≤ localizedSources hT.le W := smoothSources_le_localizedSources hT W

-- realness (conjugate symmetry) of the coefficients of a real smooth profile
example {G : ℝ × ℝ → ℂ} (hre : ∀ p, conj (G p) = G p) : ConjSymmetric (pcoeff G) :=
  conjSymmetric_pcoeff hre

-- the source map preserves zero, addition and real scaling
example : wienerOfSmooth (0 : ℝ × ℝ → ℂ) ⟨contDiff_const, fun _ => rfl, fun _ => rfl⟩ = 0 :=
  (wienerOfSmooth_eq_zero_iff _).2 (fun _ => rfl)

example {G H : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G) (hH : IsSmoothPeriodic H)
    (hGH : IsSmoothPeriodic (G + H)) :
    wienerOfSmooth (G + H) hGH = wienerOfSmooth G hG + wienerOfSmooth H hH :=
  wienerOfSmooth_add hG hH hGH

example {G : ℝ × ℝ → ℂ} (r : ℝ) (hG : IsSmoothPeriodic G)
    (hrG : IsSmoothPeriodic ((r : ℂ) • G)) :
    wienerOfSmooth ((r : ℂ) • G) hrG = (r : ℂ) • wienerOfSmooth G hG :=
  wienerOfSmooth_smul r hG hrG

-- the source curve is continuous in the Wiener norm, not merely coefficientwise
example {T : ℝ} (hT : 0 < T) {G : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G)
    (hre : ∀ p, conj (G p) = G p) {χ : ℝ → ℝ} (hχ : IsSmoothTimeBump T χ) :
    Continuous fun t : TimeI T => smoothSourceCurve hT hG hre hχ t :=
  continuous_smoothSourceCurve hT hG hre hχ

-- and its physical field is the prescribed smooth source
example {T : ℝ} (hT : 0 < T) {G : ℝ × ℝ → ℂ} (hG : IsSmoothPeriodic G)
    (hre : ∀ p, conj (G p) = G p) {χ : ℝ → ℝ} (hχ : IsSmoothTimeBump T χ) (s : ℝ)
    (y : Fin 2 → ℝ) :
    sourcePhys hT.le (smoothSourceCurve hT hG hre hχ) s (torusProj y)
      = ((χ ((clampT hT.le s : TimeI T) : ℝ) : ℝ) : ℂ) * G (y 0, y 1) :=
  smoothSourceCurve_physical hT hG hre hχ s y

/-! ### 29. v5.0: the exact measured-source quantifiers -/

-- the generated-source identity assuming measured-map agreement **only** on the smooth class
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ smoothSources hT W) (hh₂ : h₂ ∈ smoothSources hT W) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₁ hr₁)) (0 : Curve0 T) h₁ h₂
      = fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₂ hr₂)) (0 : Curve0 T) h₁ h₂ :=
  fderiv_fderiv_sourceSolution_eq_on_smooth hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hε hmild hobs hh₁ hh₂

-- the smooth-class hypothesis is strictly weaker than the v4.0 one
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 < T) (W : Set Torus2) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {ε : ℝ} (h : MeasuredMapsAgree hα hT.le W hm₁ hr₁ hm₂ hr₂ ε) :
    MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε :=
  measuredMapsAgreeOn_smooth_of_localized hα hT W hm₁ hr₁ hm₂ hr₂ h

-- the common mild neighbourhood is derived, not assumed
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (A : Submodule ℝ (Curve0 T)) :
    ∃ ε > 0, BothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A ε :=
  exists_bothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A

/-! ### 30. v5.0: real primitive graph membership and the real-only UCP boundary -/

example {α : ℝ} (hα : 0 < α) {v : Wiener1} {F : Wiener}
    (hrel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k) : MemSobolev (2 * α) v.coeff :=
  memSobolev_of_coeff_rel hα hrel

example {α : ℝ} {v : Wiener1} {F : Wiener}
    (hrel : ∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k) :
    synthL2 F = fracLapRep (α := α) v.coeff (summable_norm_sq_frac_of_coeff_rel hrel) :=
  synthL2_eq_fracLapRep hrel

example {T : ℝ} (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) :
    ConjSymmetric (timePrimitive hT u t).coeff := conjSymmetric_timePrimitive hT u t

example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) :
    ConjSymmetric ((fracTimeIntegral hα hT g t : Wiener) : Gam → ℂ) :=
  conjSymmetric_fracTimeIntegral hα hT g t

example {W : Set Torus2} (hW : MeasurableSet W) {a : Wiener} (h : ∀ x ∈ W, synth a x = 0) :
    (synthL2 a : Torus2 → ℂ) =ᵐ[(volume : Measure Torus2).restrict W] 0 :=
  aeRestrict_synthL2_eq_zero hW h

example {a b : Wiener} (h : synthL2 a = synthL2 b) : a = b := eq_of_synthL2_eq h

-- the real-only UCP boundary already implies the complex predicate used by the bridge
example {α : ℝ} (hα : 0 < α) {W : Set Torus2} (hW : MeasurableSet W)
    (h : RealFractionalUCP α W) : FractionalUCP α W := fractionalUCP_of_real hα hW h

-- `fracTimeIntegral` is the fractional multiplier applied to the time primitive
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    (fracTimeIntegral hα hT g t) k
      = (fracSymbol α k : ℂ) * (timePrimitive hT (duhamelOp hα hT g) t).coeff k :=
  fracTimeIntegral_is_frac_of_primitive hα hT g k ht

/-! ### 31. v5.0: two-state continuity with a fixed test, and the exterior limit -/

-- the bounded velocity multiplier on the physical `L²` carrier, and its consistency
noncomputable example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2) :
    Wiener2 →L[ℂ] Wiener2 := velocityW2 m hm j

example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2) (a : Wiener) :
    coeffL2 (velocityW2 m hm j (toWiener2 a)) = synthL2 (velocity m hm j a) :=
  coeffL2_velocityW2 m hm j a

example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (j : Fin 2) (a : Wiener) : ‖synthL2 (velocity m hm j a)‖ ≤ C * ‖synthL2 a‖ :=
  norm_synthL2_velocity_le hm hC j a

-- the tested interaction is a bounded bilinear form in the two state arguments
noncomputable example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (ψ : Wiener1) : Wiener1 →L[ℂ] Wiener1 →L[ℂ] ℂ :=
  sideInteractionCLM m hm hC ψ

-- **two-state continuity with a fixed test**, quantitatively, in the physical `L²` norms
example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (ψ u₁ u v₁ v : Wiener1) :
    ‖sideInteraction m hm ψ u₁ v₁ - sideInteraction m hm ψ u v‖
      ≤ 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl v₁)‖ * ‖synthL2 (incl (u₁ - u))‖)))
        + 2 * ((2 * Real.pi * ‖ψ‖) * (C * (‖synthL2 (incl (v₁ - v))‖ * ‖synthL2 (incl u)‖))) :=
  norm_sideInteraction_sub_le hm hC ψ u₁ u v₁ v

-- the spatial-integral form is the Section 6 coefficient pairing
example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ u v : Wiener1) :
    sideInteraction m hm ψ u v = wpair (incl v) (transport m hm u ψ) :=
  sideInteraction_eq_wpair m hm ψ u v

-- the exterior test: field and first derivatives vanish on all of `closure W`
example {W : Set Torus2} {ψ : Wiener1} (h : IsExteriorTest W ψ) (j : Fin 2) {x : Torus2}
    (hx : x ∈ closure W) : synth (fourierDeriv j ψ) x = 0 := h.deriv_vanishes j hx

-- and the full-torus pairing equals its restriction to `E = (closure W)ᶜ`
example {W : Set Torus2} {ψ : Wiener1} (h : IsExteriorTest W ψ) (m : Fin 2 → Gam → ℂ)
    (hm : IsBddSymbol m) (u v : Wiener1) :
    sideInteraction m hm ψ u v
      = ∑ j : Fin 2, ∫ x in (closure W)ᶜ,
          synth (incl v) x * synth (velocity m hm j (incl u)) x * synth (fourierDeriv j ψ) x :=
  sideInteraction_eq_exterior h m hm u v

-- the actual iterated space-time integral of the generated pair vanishes
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {h₁ h₂ : Curve0 T}
    (hgen : spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
          (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
        + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
          (duhamelOp hα hT h₂) (duhamelOp hα hT h₁) = 0)
    (ψ : Wiener1) (φ : ℝ → ℂ) :
    spacetimeTestedInteraction hT (m₁ - m₂) (hm₁.sub hm₂) ψ φ
      (duhamelOp hα hT h₁) (duhamelOp hα hT h₂) = 0 :=
  spacetimeTestedInteraction_eq_zero hα hT hm₁ hr₁ hm₂ hr₂ hdiv hgen ψ φ

-- the **corrected** Runge-shaped statement: the two states vary, `ψ` is fixed
example {W : Set Torus2} {ψ : Wiener1} (hψ : IsExteriorTest W ψ) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (hdiv : IsDivFreeSymbol m)
    {u v : ℕ → Wiener1} {U V : Wiener1}
    (hzero : ∀ n : ℕ, transport m hm (u n) (v n) + transport m hm (v n) (u n) = 0)
    (hu : ExteriorStateConvergence W m hm u U) (hv : ExteriorStateConvergence W m hm v V) :
    testedInteraction m hm ψ U V = 0 :=
  tested_symmetrized_state_limit hψ hm hC hdiv hzero hu hv

-- the obstruction: a global physical `L²` limit inherits the vanishing
example {S : Set Torus2} (hS : MeasurableSet S) {a : ℕ → Wiener} {A : Wiener}
    (hvan : ∀ n : ℕ, ∀ x ∈ S, synth (a n) x = 0)
    (hconv : Tendsto (fun n => ‖synthL2 (a n - A)‖) atTop (nhds 0)) :
    ∀ᵐ x ∂((volume : Measure Torus2).restrict S), synth A x = 0 :=
  ae_eq_zero_of_tendsto_physicalL2 hS hvan hconv

-- the measured region and the exterior are disjoint
example (W : Set Torus2) : Disjoint W ((closure W)ᶜ) := disjoint_measured_exterior W

/-! ### 32. v5.0: smooth profiles are first-order, and the proved nonlocality obstruction -/

-- four integrations by parts in each variable give the weighted summability
example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) : Summable fun k : Gam => wt k * ‖pcoeff G k‖ :=
  summable_wt_norm_pcoeff h

-- so a smooth profile is an actual **first-order** state
noncomputable example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) : Wiener1 := wiener1OfSmooth G h

example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    incl (wiener1OfSmooth G h) = wienerOfSmooth G h := incl_wiener1OfSmooth G h

example {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (u : Wiener1) (K : Set Torus2),
      u ≠ 0 ∧ SmoothWiener (incl u) ∧ IsCompact K ∧ K ⊆ W ∧
      ∀ x ∉ K, synth (incl u) x = 0 :=
  exists_smooth_localized_profile1 hW hne

-- the exterior energy is a norm, so the uniform bound is not an extra assumption
example (E : Set Torus2) (a b : Wiener) :
    Real.sqrt (extL2sq E (a + b)) ≤ Real.sqrt (extL2sq E a) + Real.sqrt (extL2sq E b) :=
  sqrt_extL2sq_add_le E a b

example (W : Set Torus2) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {u : ℕ → Wiener1}
    {U : Wiener1}
    (hstate : Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (incl (u n - U)))) atTop (nhds 0))
    (hvel : ∀ j : Fin 2,
      Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U)))))
        atTop (nhds 0)) :
    ExteriorStateConvergence W m hm u U :=
  ExteriorStateConvergence.of_state_velocity W hm hstate hvel

-- global physical `L²` convergence supplies every exterior hypothesis
example (W : Set Torus2) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {u : ℕ → Wiener1}
    {U : Wiener1} (hconv : Tendsto (fun n => ‖synthL2 (incl (u n - U))‖) atTop (nhds 0)) :
    ExteriorStateConvergence W m hm u U := exteriorStateConvergence_of_global W hm hconv

-- **the obstruction, proved**: a nonzero state vanishing on the exterior whose velocity
-- vanishes nowhere
example {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (k₀ : Gam) (u : Wiener1), u ≠ 0 ∧
      (∀ x ∈ (closure W)ᶜ, synth (incl u) x = 0) ∧
      ∀ (j : Fin 2) (x : Torus2),
        synth (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) j (incl u)) x ≠ 0 :=
  exists_exterior_nonlocality hW hne

-- hence exterior convergence of the scalar states does not imply exterior convergence of the
-- velocities of the full states
example {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) (hE : ((closure W)ᶜ).Nonempty) :
    ∃ (k₀ : Gam) (u : ℕ → Wiener1) (U : Wiener1),
      Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (incl (u n - U)))) atTop (nhds 0)
        ∧ ¬ ExteriorStateConvergence W (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) u U :=
  exists_state_conv_without_velocity_conv hW hne hE

-- the positive half: the source-region contribution vanishes, and the second state argument
-- enters only through its exterior restriction
example {W : Set Torus2} {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (m : Fin 2 → Gam → ℂ)
    (hm : IsBddSymbol m) (j : Fin 2) (u v : Wiener1) :
    (∫ x in closure W, synth (incl v) x * synth (velocity m hm j (incl u)) x
        * synth (fourierDeriv j ψ) x) = 0 :=
  setIntegral_source_region_eq_zero hψ m hm j u v

example {W : Set Torus2} {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (m : Fin 2 → Gam → ℂ)
    (hm : IsBddSymbol m) (u v v' : Wiener1)
    (h : ∀ x ∈ (closure W)ᶜ, synth (incl v) x = synth (incl v') x) :
    sideInteraction m hm ψ u v = sideInteraction m hm ψ u v' :=
  sideInteraction_congr_exterior hψ m hm u v v' h

-- global convergence would supply the remaining analytic input
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) (A : Submodule ℝ (Curve0 T)) (t : ℝ) {U : Wiener1} {g : ℕ → Curve0 T}
    (hg : ∀ n : ℕ, g n ∈ A)
    (hconv : Tendsto (fun n => ‖synthL2 (incl (curveState hT (duhamelOp hα hT (g n)) t - U))‖)
      atTop (nhds 0)) :
    GeneratedExteriorApproximation hα hT W m hm A t U :=
  generatedExteriorApproximation_of_global hα hT W hm A t hg hconv

/-! ### 33. v5.0: recovery on open sets, the exterior energy budget, and the reduction -/

-- a continuous physical field vanishing a.e. on an open region vanishes there identically
example {W : Set Torus2} (hW : IsOpen W) {a : Wiener}
    (h : (synthL2 a : Torus2 → ℂ) =ᵐ[(volume : Measure Torus2).restrict W] 0) :
    ∀ x ∈ W, synth a x = 0 := eq_zero_on_of_aeRestrict hW h

-- so the real and the complex unique-continuation boundaries are **equivalent**
example {α : ℝ} (hα : 0 < α) {W : Set Torus2} (hW : IsOpen W) :
    RealFractionalUCP α W ↔ FractionalUCP α W := realFractionalUCP_iff_fractionalUCP hα hW

-- the exterior energy budget
example {S : Set Torus2} (hS : MeasurableSet S) (a : Wiener) :
    extL2sq S a + extL2sq Sᶜ a = ‖synthL2 a‖ ^ 2 := extL2sq_add_compl hS a

example {W : Set Torus2} (hW : IsOpen W) (a : Wiener) :
    extL2sq W a + extL2sq (closure W \ W) a = extL2sq (closure W) a :=
  extL2sq_closure_split hW a

-- CORRECTED in v6.0: for the continuous fields of this theorem the boundary strip carries no
-- energy, so the exterior energy is exactly the global physical `L²` energy.  (The global
-- energy is still uncontrolled; this is not a convergence statement.)
example {W : Set Torus2} {a : Wiener} (h : ∀ x ∈ W, synth a x = 0) :
    ∀ x ∈ closure W, synth a x = 0 := synth_eq_zero_on_closure h

example {W : Set Torus2} (hW : IsOpen W) {a : Wiener} (h : ∀ x ∈ W, synth a x = 0) :
    extL2sq (closure W \ W) a = 0 := extL2sq_boundary_strip_eq_zero hW h

example {W : Set Torus2} (hW : IsOpen W) {a : Wiener} (h : ∀ x ∈ W, synth a x = 0) :
    extL2sq (closure W)ᶜ a = ‖synthL2 a‖ ^ 2 := extL2sq_exterior_of_vanishes_on hW h

-- the reduction: source-norm convergence supplies every exterior hypothesis
example {α T : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) (A : Submodule ℝ (Curve0 T)) (t : ℝ) {g : ℕ → Curve0 T}
    {gLim : Curve0 T} (hg : ∀ n : ℕ, g n ∈ A)
    (hconv : Tendsto (fun n => ‖g n - gLim‖) atTop (nhds 0)) :
    GeneratedExteriorApproximation hα hT W m hm A t
      (curveState hT (duhamelOp hα hT gLim) t) :=
  generatedExteriorApproximation_of_source_tendsto hα hT W hm A t hg hconv

/-! ### 9b. v6.0: admissible sources, test separation, terminal control

Exercised below: a **nonempty proper open** `W` on the torus really exists; smooth time bumps
on an arbitrary prescribed subinterval (not just the `T/2`-centred one); both separation
lemmas; the jointly smooth real space-time representative; positive-time `ℓ² → A¹` smoothing
with its `FractionalUCP` graph relation and its time derivative; the approximation theorem for
the actual generated states at positive time with a real target and actual admissible controls;
and the zero-time limitation.
-/

-- a nonempty **proper** open region of the torus, and one with nonempty exterior
example : ∃ W : Set Torus2, IsOpen W ∧ W.Nonempty ∧ W ≠ Set.univ := by
  obtain ⟨W, hW, hne, hE⟩ := exists_open_nonempty_with_exterior
  obtain ⟨y, hy⟩ := hE
  refine ⟨W, hW, hne, fun hc => hy ?_⟩
  rw [hc]
  exact subset_closure (by trivial)

example : ∃ W : Set Torus2, IsOpen W ∧ W.Nonempty ∧ ((closure W)ᶜ).Nonempty :=
  exists_open_nonempty_with_exterior

-- a `C^∞` time bump supported in an **arbitrary** prescribed interval of `(0,T)`
example {T c d : ℝ} (hc : 0 < c) (hcd : c < d) (hdT : d < T) :
    ∃ χ : ℝ → ℝ, IsSmoothTimeBump T χ ∧ (∀ t, 0 ≤ χ t) ∧
      (∀ t ∉ Set.Ioo c d, χ t = 0) ∧ χ ((c + d) / 2) = 1 :=
  exists_smooth_time_bump_on hc hcd hdT

-- concretely: a bump living in the last quarter of `(0,T)`, far from `T/2`
example {T : ℝ} (hT : 0 < T) :
    ∃ χ : ℝ → ℝ, IsSmoothTimeBump T χ ∧ (∀ t, 0 ≤ χ t) ∧
      (∀ t ∉ Set.Ioo (3*T/4) (7*T/8), χ t = 0) ∧ χ ((3*T/4 + 7*T/8) / 2) = 1 :=
  exists_smooth_time_bump_on (by linarith) (by linarith) (by linarith)

example {T T' : ℝ} {χ : ℝ → ℝ} (h : IsSmoothTimeBump T χ) (hTT' : T ≤ T') :
    IsSmoothTimeBump T' χ := h.mono hTT'

-- the two test separation lemmas
example {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ χ : ℝ → ℝ, IsSmoothTimeBump T χ → (∫ t in (0:ℝ)..T, χ t * f t) = 0) :
    ∀ t ∈ Set.Icc (0:ℝ) T, f t = 0 := eq_zero_of_forall_time_bump hT hf h

example {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ} (hf : Continuous f)
    (h : ∀ χ : ℝ → ℝ, IsSmoothTimeBump T χ → (∫ t in (0:ℝ)..T, (χ t : ℂ) * f t) = 0) :
    ∀ t ∈ Set.Icc (0:ℝ) T, f t = 0 := eq_zero_of_forall_time_bump_complex hT hf h

example {W : Set Torus2} (hW : IsOpen W) {v : Torus2 → ℂ} (hv : Continuous v)
    (h : ∀ a ∈ smoothProfiles W, (∫ x : Torus2, v x * synth a.val x) = 0) :
    ∀ x ∈ W, v x = 0 := eq_zero_on_of_forall_smoothProfile hW hv h

-- the normalized smooth bump used to build them
example {W : Set Torus2} (hW : IsOpen W) {w : Torus2} (hw : w ∈ W) :
    ∃ (a : RealWiener) (K : Set Torus2), SmoothWiener a.val ∧ IsCompact K ∧ K ⊆ W ∧
      (∀ x ∉ K, synth a.val x = 0) ∧
      (∀ x : Torus2, (synth a.val x).im = 0 ∧ 0 ≤ (synth a.val x).re) ∧
      synth a.val w = 1 := exists_smooth_bump_at hW hw

-- nontrivial admissible controls exist for every nonempty open `W` and every `T > 0`
example {T : ℝ} (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ V ∈ smoothSources hT W, V ≠ 0 ∧ CompactlySupportedIn hT.le W V :=
  exists_nonzero_smoothSource hT hW hne

-- every admissible source has a jointly smooth real representative in `W × (0,T)`
example {T : ℝ} (hT : 0 < T) {W : Set Torus2} {V : Curve0 T} (hV : V ∈ smoothSources hT W) :
    ∃ Φ : ℝ × (ℝ × ℝ) → ℂ, SmoothSpacetimeRep hT W V Φ := exists_smoothSpacetimeRep hT hV

-- positive-time smoothing of an `ℓ²` datum, and the exact `FractionalUCP` graph relation
example {α r : ℝ} (hα : 1/2 ≤ α) (hr : 0 < r) (y : Wiener2) (k : Gam) :
    (fracHeat2 hα hr y) k = ((fracSymbol α k : ℝ) : ℂ) * (heat2 hα hr y).coeff k :=
  fracHeat2_coeff_rel hα hr y k

example {α r : ℝ} (hα : 1/2 ≤ α) (hr : 0 < r) {y : Wiener2} (h : heat2 hα hr y = 0) : y = 0 :=
  eq_zero_of_heat2_eq_zero hα hr h

-- the zero Fourier mode survives: `fracSymbol α 0 = 0`, so the heat symbol there is `1`
example {α r : ℝ} (hα : 1/2 ≤ α) (hr : 0 < r) (y : Wiener2) :
    (heat2 hα hr y).coeff 0 = heatSymbol α r 0 * y 0 := heat2_coeff hα hr y 0

-- term-by-term differentiation in time
example {α r : ℝ} (hα : 1/2 ≤ α) (hr : 0 < r) (y : Wiener2) (x : Torus2) :
    HasDerivAt (heatField α y x) (-(synth (fracHeat2 hα hr y) x)) r :=
  hasDerivAt_heatField hα hr y x

-- the pairing is continuous across `r = 0` even though the `A¹` norm of `heat2` is not
example (α : ℝ) (y : Wiener2) (a : Wiener) : Continuous (heatPair α y a) :=
  continuous_heatPair α y a

-- the UCP step
example {α : ℝ} (hα : 1/2 ≤ α) {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {y : Wiener2} {τ : ℝ} (hτ : 0 < τ)
    (h : ∀ a ∈ smoothProfiles W, ∀ r ∈ Set.Icc (0:ℝ) τ, heatPair α y a.val r = 0) :
    y = 0 := eq_zero_of_heatPair_vanishes hα hW hUCP hτ h

-- **the approximation theorem for the actual generated states**
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n, g n ∈ smoothSources hT W) ∧
      Tendsto (fun n =>
          ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖)
        atTop (nhds 0) :=
  exists_smoothSources_terminal_tendsto hα hT hW hUCP hτ0 hτT U

-- the zero-time limitation: every generated state vanishes at `t = 0` …
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    curveState hT (duhamelOp hα hT g) 0 = 0 := terminal_zero_time hα hT g

-- … so at `t = 0` no nonzero target is even approached
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 ≤ T) {U : RealWiener1} (hU : U.val ≠ 0)
    (g : Curve0 T) : curveState hT (duhamelOp hα hT g) 0 - U.val ≠ 0 := by
  rw [terminal_zero_time hα hT g, zero_sub, neg_ne_zero]
  exact hU

-- Task 4: exterior state *and full-state velocity* convergence, derived
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n : ℕ, g n ∈ smoothSources hT W) ∧
      ExteriorStateConvergence W m hm
        (fun n => curveState hT.le (duhamelOp hα hT.le (g n)) τ) U.val :=
  exists_exteriorStateConvergence_terminal hα hT hW hUCP hm hτ0 hτT U

example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) (U : RealWiener1) :
    GeneratedExteriorApproximation hα hT.le W m hm (smoothSources hT W) τ U.val :=
  generatedExteriorApproximation_terminal hα hT hW hUCP hm hτ0 hτT U

-- Task 5: the downstream theorem — no approximation, convergence or density input
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {C : ℝ} (hC : ∀ j k, ‖(m₁ - m₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (U V : RealWiener1) :
    testedInteraction (m₁ - m₂) (hm₁.sub hm₂) ψ U.val V.val = 0 :=
  tested_interaction_real_targets hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC hτ0 hτT hobs hψ U V

/-! ### 9c. v6.0: from the terminal identity to the kernel

The approximation theorem makes *every* real state a target, so the symmetrized tested identity
extends by bilinearity to all states, and evaluating on Fourier–Dirac states turns it into an
explicit constraint on the symbol difference.  For the paper's rotated-gradient symbols this
forces the Fourier coefficients of the kernel difference to be constant off zero, hence — by the
symbol bound — zero.
-/

-- bilinearity, and the extension from real targets to all states
example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (ψ u u' v : Wiener1) :
    testedInteraction m hm ψ (u + u') v
      = testedInteraction m hm ψ u v + testedInteraction m hm ψ u' v :=
  testedInteraction_add_left m hm ψ u u' v

example {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (ψ : Wiener1)
    (h : ∀ U V : RealWiener1, testedInteraction m hm ψ U.val V.val = 0) (u v : Wiener1) :
    testedInteraction m hm ψ u v = 0 :=
  testedInteraction_eq_zero_of_real_states hm ψ h u v

-- the exact value on Fourier–Dirac states
example (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (ψ : Wiener1) (k l : Gam) :
    testedInteraction m hm ψ (dirac1 k) (dirac1 l)
      = twoPiI * ψ.coeff (-(k + l))
          * ∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ) * (m j k + m j l) :=
  testedInteraction_dirac1 m hm ψ k l

-- nonzero exterior tests exist, and every frequency carries one
example {W : Set Torus2} (hE : ((closure W)ᶜ).Nonempty) :
    ∃ ψ : Wiener1, IsExteriorTest W ψ ∧ ψ ≠ 0 := exists_exteriorTest_ne_zero hE

example {W : Set Torus2} (hE : ((closure W)ᶜ).Nonempty) (n : Gam) :
    ∃ ψ : Wiener1, IsExteriorTest W ψ ∧ ψ.coeff n ≠ 0 :=
  exists_exteriorTest_coeff_ne_zero hE n

example {W : Set Torus2} {ψ : Wiener1} (h : IsExteriorTest W ψ) (p : Gam) :
    IsExteriorTest W (shift1 p ψ) := isExteriorTest_shift1 h p

-- the mode constraint on the symbol difference
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {C : ℝ} (hC : ∀ j k, ‖(m₁ - m₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (k l : Gam) :
    ∑ j : Fin 2, (((-(k + l)) j : ℤ) : ℂ) * ((m₁ - m₂) j k + (m₁ - m₂) j l) = 0 :=
  symbol_mode_identity_all hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hdiv hC hτ0 hτT hobs k l

-- and, for the rotated-gradient symbols, recovery of the velocity operator
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W) {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : κ₁ k = κ₂ k :=
  kernel_diff_eq_zero hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT hobs hk

example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W) {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ :=
  rotatedGradientSymbol_eq_of_measured hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT hobs

-- faithfulness: agreement of the measured maps is *equivalent* to equality of the symbols
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W) {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    (∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
      ↔ rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ :=
  measuredMapsAgreeOn_iff hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hτ0 hτT

-- the explicit witness pair, so the separation is not vacuous
example : IsBddSymbol (rotatedGradientSymbol finiteKernel.coeff)
      ∧ IsRealSymbol (rotatedGradientSymbol finiteKernel.coeff)
      ∧ IsBddSymbol (rotatedGradientSymbol (0 : Gam → ℂ))
      ∧ IsRealSymbol (rotatedGradientSymbol (0 : Gam → ℂ)) :=
  finiteKernel_symbol_admissible

example : rotatedGradientSymbol finiteKernel.coeff ≠ rotatedGradientSymbol (0 : Gam → ℂ) :=
  rotatedGradientSymbol_finiteKernel_ne_zero

example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hm₁ : IsBddSymbol (rotatedGradientSymbol finiteKernel.coeff))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol finiteKernel.coeff))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol (0 : Gam → ℂ)))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol (0 : Gam → ℂ))) :
    ¬ ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε :=
  finiteKernel_vs_zero_measured_differ hα hT hW hE hUCP hτ0 hτT hm₁ hr₁ hm₂ hr₂

-- the paper's elliptic class lands inside the packet's symbol hypotheses
example {κ : Gam → ℂ} {c D : ℝ} (h : OrderedFourierEllipticity κ c D) : IsAdmissibleKernel κ :=
  orderedEllipticity_admissible h

example {κ : Gam → ℂ} {c D : ℝ} (hell : OrderedFourierEllipticity κ c D)
    (hcs : ConjSymmetric κ) :
    IsBddSymbol (rotatedGradientSymbol κ) ∧ IsRealSymbol (rotatedGradientSymbol κ) :=
  orderedEllipticity_symbol hell hcs

-- two real `A¹` kernels with the same measured data agree off the zero mode …
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Wiener1} (hcs₁ : ConjSymmetric K₁.coeff) (hcs₂ : ConjSymmetric K₂.coeff)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₁)
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₂) (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : K₁.coeff k = K₂.coeff k :=
  kernel_determined_of_wiener1 hα hT hW hE hUCP hcs₁ hcs₂ hτ0 hτT hobs hk

-- … and therefore induce the same velocity operator
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Wiener1} (hcs₁ : ConjSymmetric K₁.coeff) (hcs₂ : ConjSymmetric K₂.coeff)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₁)
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel)
      (rotatedGradientSymbol_isRealSymbol hcs₂) (smoothSources hT W) ε)
    (j : Fin 2) :
    velocity (rotatedGradientSymbol K₁.coeff) (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel) j
      = velocity (rotatedGradientSymbol K₂.coeff)
          (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel) j :=
  velocity_determined_of_wiener1 hα hT hW hE hUCP hcs₁ hcs₂ hτ0 hτT hobs j

-- the same for the paper's ordered-elliptic class
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ} {c₁ D₁ c₂ D₂ : ℝ}
    (hell₁ : OrderedFourierEllipticity κ₁ c₁ D₁) (hcs₁ : ConjSymmetric κ₁)
    (hell₂ : OrderedFourierEllipticity κ₂ c₂ D₂) (hcs₂ : ConjSymmetric κ₂)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁))
      (rotatedGradientSymbol_isRealSymbol hcs₁)
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂))
      (rotatedGradientSymbol_isRealSymbol hcs₂) (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : κ₁ k = κ₂ k :=
  kernel_determined_of_orderedEllipticity hα hT hW hE hUCP hell₁ hcs₁ hell₂ hcs₂ hτ0 hτT hobs hk

-- the portable UCP parameter is satisfiable, and is not trivially true
example (α : ℝ) : FractionalUCP α (Set.univ : Set Torus2) := fractionalUCP_univ α
example (α : ℝ) : ¬ FractionalUCP α (∅ : Set Torus2) := not_fractionalUCP_empty α

-- the measurement hypothesis quantifies over a nonzero family at every radius
example {T : ℝ} (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty)
    {ε : ℝ} (hε : 0 < ε) : ∃ V ∈ smoothSources hT W, V ≠ 0 ∧ ‖V‖ < ε :=
  exists_nonzero_smoothSource_norm_lt hT hW hne hε

-- the controls really are switched off before the terminal time
example {T : ℝ} (hT : 0 < T) (W : Set Torus2) {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    {V : Curve0 T} (hV : V ∈ smoothSourcesBefore hT W τ) :
    ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < τ ∧
      ∀ t ∉ Set.Icc t₀ t₁, sourceFun hT.le V t = 0 :=
  smoothSourcesBefore_timeSupport hT W hτ hτT hV

example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n, g n ∈ smoothSourcesBefore hT W τ) ∧
      Tendsto (fun n =>
          ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖)
        atTop (nhds 0) :=
  exists_smoothSourcesBefore_terminal_tendsto hα hT hW hUCP hτ0 hτT U

/-! ### 9d. v6.0: the approximation theorem has unconditional, non-degenerate content -/

-- the quantity driven to zero is a faithful norm
example (u : Wiener1) : ‖synthL2 (incl u)‖ = 0 ↔ u = 0 := norm_synthL2_incl_eq_zero_iff u

-- nonzero real targets exist (concretely, the packet's finiteKernel)
example : ∃ U : RealWiener1, ‖synthL2 (incl U.val)‖ ≠ 0 := exists_nonzero_realWiener1

-- the control class is nontrivial
example {T : ℝ} (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) : ∃ V ∈ smoothSourcesBefore hT W τ, V ≠ 0 :=
  exists_nonzero_smoothSourceBefore hT hW hne hτ0 hτT

-- the zero control fails for every nonzero target
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 ≤ T) (τ : ℝ) {U : RealWiener1}
    (hU : ‖synthL2 (incl U.val)‖ ≠ 0) :
    ¬ Tendsto
        (fun _ : ℕ => ‖synthL2 (incl (curveState hT (duhamelOp hα hT (0 : Curve0 T)) τ - U.val))‖)
        atTop (nhds 0) :=
  not_tendsto_zero_control hα hT τ hU

-- an instance of the approximation theorem with NO undischarged hypothesis
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 < T) {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (U : RealWiener1) :
    ∃ g : ℕ → Curve0 T, (∀ n, g n ∈ smoothSourcesBefore hT (Set.univ : Set Torus2) τ) ∧
      Tendsto (fun n =>
          ‖synthL2 (incl (curveState hT.le (duhamelOp hα hT.le (g n)) τ - U.val))‖)
        atTop (nhds 0) :=
  exists_terminal_tendsto_univ hα hT hτ0 hτT U

/-! ### 9e. v6.0: the two restrictions in the recovery theorem are forced, not artefacts -/

-- the rotated gradient ignores the zero Fourier mode
example {κ₁ κ₂ : Gam → ℂ} (h : ∀ k : Gam, k ≠ 0 → κ₁ k = κ₂ k) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ :=
  rotatedGradientSymbol_congr_of_ne_zero h

-- so two DISTINCT admissible real kernels can have identical measured maps at every radius:
-- "equal off the zero mode" is exactly sharp
example {α T : ℝ} (hα : 1/2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) :
    ∃ (κ₁ κ₂ : Gam → ℂ) (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
      (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
      (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
      (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂)),
      κ₁ ≠ κ₂ ∧ MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε :=
  measurement_cannot_see_zero_mode hα hT W A ε

-- and a dense measured region admits no nonzero exterior test, so `(closure W)ᶜ ≠ ∅` is needed
example {W : Set Torus2} (hWd : closure W = Set.univ) {ψ : Wiener1} (h : IsExteriorTest W ψ) :
    ψ = 0 := exteriorTest_eq_zero_of_dense hWd h

end LiWangTest


/-! ### 9g. v7.0: the physical PDE bridge

The genuine `L²(𝕋²)`-valued fractional-Laplacian field and its identification with
`fracTimeIntegral`; the physical equation with its initial trace, absolutely continuous
representative and mean balance for a **nonzero-mean** control; unconditional uniqueness of
the physical solution; and the physical observation map feeding the existing recovery
theorem. -/

section PhysicalBridge

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! #### v7.0 step 1: the genuine physical fractional-Laplacian field -/

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    AEStronglyMeasurable (fracFieldW2 hα hT g)
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) :=
  aestronglyMeasurable_fracFieldW2 hα hT g

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    (∫⁻ s in Set.Ioc (0:ℝ) T, ENNReal.ofReal (‖fracFieldW2 hα hT g s‖ ^ 2))
      ≤ ENNReal.ofReal (T * ‖g‖ ^ 2) :=
  lintegral_norm_sq_fracFieldW2_le hα hT g

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    IntegrableOn (fracFieldW2 hα hT g) (Set.Ioc (0:ℝ) T) volume :=
  integrableOn_fracFieldW2 hα hT g

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)), FracSummableAt hα hT g t :=
  ae_fracSummable hα hT g

/-- **Regression: the physical fractional multiplier.**  Off the explicit null set the Fourier
coefficients of the constructed field are `λ_k` times those of the state. -/
theorem physical_multiplier_check (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {t : ℝ}
    (h : FracSummableAt hα hT g t) (k : Gam) :
    (fracFieldW2 hα hT g t) k
      = (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k :=
  fracFieldW2_apply h k

/-- **Regression: the multiplier normalization.**  `λ_k = (4π²|k|²)^α`, so `λ = (4π²)^α` at a
unit frequency and `λ = 0` at the zero mode. -/
theorem fracSymbol_unitFreq (a : ℝ) (j : Fin 2) :
    fracSymbol a (unitFreq j) = (4 * Real.pi ^ 2) ^ a := by
  have h : sqNorm (unitFreq j) = 1 := by
    fin_cases j <;> · simp [sqNorm, unitFreq]
  rw [fracSymbol, h, mul_one]

theorem fracSymbol_zero_mode (ha : 0 < α) : fracSymbol α (0 : Gam) = 0 := fracSymbol_zero_eq ha

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    synthL2 (fracTimeIntegral hα hT g t) = ∫ s in (0:ℝ)..t, physFracField hα hT g s :=
  synthL2_fracTimeIntegral hα hT g ht

/-! #### v7.0 step 2: the physical PDE, the initial trace and the mean balance -/

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    physState hT u t + (∫ s in (0:ℝ)..t, physTransport hm hT u s)
        + ∫ s in (0:ℝ)..t, mildFracField hα hT hm hr u f s
      = ∫ s in (0:ℝ)..t, physSource hT f s :=
  physical_pde_integrated hα hT hm hr hmild ht

/-- **Regression: the initial trace is a genuine trace.** -/
theorem physical_initial_trace (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    Continuous (physState hT u) ∧ physState hT u 0 = 0 :=
  ⟨continuous_physState hT u, physState_initial_of_mild hα hT hm hr hmild⟩

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) (ht' : t' ∈ Set.Icc (0:ℝ) T) (htt : t' ≤ t) :
    ‖physState hT u t - physState hT u t'‖ ≤ ∫ s in t'..t, ‖physRHS hα hT hm hr u f s‖ :=
  norm_physState_sub_le hα hT hm hr hmild ht ht' htt

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (Λ : TorusL2 →L[ℝ] ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.Ioo (0:ℝ) T →
      HasDerivAt (fun r : ℝ => Λ (physState hT u r)) (Λ (physRHS hα hT hm hr u f t)) t :=
  ae_hasDerivAt_pairing_physState hα hT hm hr hmild Λ

/-- **Regression: sign and normalization of the transport term.**  The physical transport field
is the pointwise dot product of the velocity field with the gradient. -/
theorem physical_transport_pointwise (hm : IsBddSymbol m) (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) :
    (physTransport hm hT u t : Torus2 → ℂ)
      =ᵐ[(volume : Measure Torus2)] fun x =>
        ∑ j : Fin 2,
          synth (velocity m hm j (incl (curveState hT u t))) x
            * synth (fourierDeriv j (curveState hT u t)) x :=
  physTransport_apply_ae hm hT u t

/-! #### A genuinely nonzero-mean forcing -/

theorem conjSymmetric_wdirac_zero :
    ConjSymmetric ((wdirac (0 : Gam) : Wiener) : Gam → ℂ) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [diracFun]
  · have hnk : -k ≠ 0 := fun h => hk (neg_eq_zero.1 h)
    simp [diracFun, hk, hnk]

/-- The constant real profile `1` on the torus: a state with **mean one**. -/
noncomputable def unitProfile : RealWiener :=
  RealWiener.mk (wdirac (0 : Gam)) conjSymmetric_wdirac_zero

/-- A **nonzero-mean** control: the constant-in-time source with spatial mean `1`. -/
noncomputable def unitMeanSource (T : ℝ) : Curve0 T :=
  BoundedContinuousFunction.const (TimeI T) unitProfile

/-- **Regression: the forcing really has nonzero mean.**  No mean-zero normalization is
imposed anywhere in the mean-balance theorem. -/
theorem unitMeanSource_mean (hT : 0 ≤ T) (s : ℝ) :
    (sourceFun hT (unitMeanSource T) s) 0 = 1 ∧ (1 : ℂ) ≠ 0 := by
  refine ⟨?_, one_ne_zero⟩
  show (wdirac (0 : Gam)) 0 = 1
  simp [diracFun]

/-- **Regression: the mean balance for a nonzero-mean forcing.**  For the constant unit-mean
control the spatial mean of the state at time `t` is exactly `t`. -/
theorem meanBalance_unitMeanSource (hα : 1 / 2 < α) (hT : 0 ≤ T) {κ : Gam → ℂ}
    (hb : IsAdmissibleKernel κ) (hr : IsRealSymbol (rotatedGradientSymbol κ)) {u : Curve1 T}
    (hmild : u + sourceQuad hα hT (rotatedGradientSymbol κ)
        (rotatedGradientSymbol_bdd hb) hr u u = duhamelOp hα hT (unitMeanSource T))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT u t).coeff 0 = (t : ℂ) := by
  rw [coeff_zero_balance_of_mild hα hT hb hr hmild ht]
  have hone : ∀ s : ℝ, (sourceFun hT (unitMeanSource T) s) 0 = 1 :=
    fun s => (unitMeanSource_mean hT s).1
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1 : ℂ)) (fun s _ => hone s),
    intervalIntegral.integral_const, sub_zero]
  exact (Complex.real_smul (x := t) (z := 1)).trans (mul_one _)

/-- **Regression: the physical mean balance.** -/
theorem physical_mean_balance (hα : 1 / 2 < α) (hT : 0 ≤ T) {κ : Gam → ℂ}
    (hb : IsAdmissibleKernel κ) (hr : IsRealSymbol (rotatedGradientSymbol κ)) {u : Curve1 T}
    {f : Curve0 T}
    (hmild : u + sourceQuad hα hT (rotatedGradientSymbol κ)
        (rotatedGradientSymbol_bdd hb) hr u u = duhamelOp hα hT f)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    torusMean (physState hT u t) = ∫ s in (0:ℝ)..t, torusMean (physSource hT f s) :=
  mean_balance_physical hα hT hb hr hmild ht

example {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (u v : Wiener1) :
    (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) u v) (0 : Gam) = 0 :=
  transport_rotatedGradient_zero_mode hb u v

example (a : Wiener) : torusMean (synthL2 a) = a 0 := torusMean_synthL2 a

/-! #### v7.0 step 3: uniqueness and the comparison theorem -/

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {u v : Curve1 T} (f : Curve0 T)
    (heu : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hev : v + sourceQuad hα hT m hm hr v v = duhamelOp hα hT f) : u = v :=
  mild_curve_unique hα hT hm hr hC f heu hev

example {lam : ℝ} {w g : ℝ → ℂ} (hw : Continuous w) (hg : Continuous g)
    (heq : ∀ t ∈ Set.Icc (0:ℝ) T,
      w t + (lam : ℂ) * (∫ s in (0:ℝ)..t, w s) = ∫ s in (0:ℝ)..t, g s)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    w t = scalarDuhamel lam g t := integrated_equation_converse hw hg heq ht

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {θ : Curve1 T} {f : Curve0 T}
    (hmild : θ + sourceQuad hα hT m hm hr θ θ = duhamelOp hα hT f) :
    IsPhysicalSolution hα hT hm f θ := isPhysicalSolution_of_mild hα hT hm hr hmild

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {θ : Curve1 T} {f : Curve0 T} (h : IsPhysicalSolution hα hT hm f θ) :
    θ + sourceQuad hα hT m hm hr θ θ = duhamelOp hα hT f :=
  mild_of_isPhysicalSolution hα hT hm hr h

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {f : Curve0 T} {u θ : Curve1 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hθ : IsPhysicalSolution hα hT hm f θ) : θ = u :=
  eq_of_isPhysicalSolution hα hT hm hr hC hmild hθ

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {f : Curve0 T} {θ : Curve1 T} (h : IsPhysicalSolution hα hT hm f θ) :
    (∑' k : Gam, (fracSymbol α k) ^ 2 * ∫ t in (0:ℝ)..T, ‖(curveState hT θ t).coeff k‖ ^ 2)
      ≤ T * ‖f - spacetimeTransport m hm hr θ θ‖ ^ 2 :=
  energy_of_isPhysicalSolution hα hT hm hr h

example (hT : 0 ≤ T) (θ : Curve1 T) (t : ℝ) : ‖physState hT θ t‖ ≤ ‖θ‖ :=
  norm_physState_le hT θ t

/-- **Regression: the initial trace is not an extra assumption.**  The weak equation at `t = 0`
already forces it. -/
theorem physical_trace_forced (hT : 0 ≤ T) (hm : IsBddSymbol m) (f : Curve0 T) (θ : Curve1 T)
    (hw : ∀ (P : C(Torus2, ℂ)) (F : Finset Gam) (c : Gam → ℂ), P = trigPoly F c →
      ∀ t ∈ Set.Icc (0:ℝ) T,
        spacePair (incl (curveState hT θ t)) P
          + (∫ s in (0:ℝ)..t, spacePair (incl (curveState hT θ s)) (fracLapPoly α F c))
          + (∫ s in (0:ℝ)..t, spacePair (quadCurve hm (curveState hT θ) s) P)
          = ∫ s in (0:ℝ)..t, spacePair (sourceFun hT f s) P) :
    curveState hT θ 0 = 0 :=
  curveState_zero_of_weak (α := α) hT hm f θ hw

/-! #### v7.0 step 4: the physical observation map and the recovery specialization -/

/-- **Regression: physical and mild observations agree.** -/
theorem physical_mild_observation_agree (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {f : Curve0 T} {u θ : Curve1 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hθ : IsPhysicalSolution hα hT hm f θ) (W : Set Torus2) (j : Fin 2) (t : ℝ) (x : W) :
    obsState hT W θ t x = obsState hT W u t x
      ∧ obsVelocity m hm j hT W θ t x = obsVelocity m hm j hT W u t x :=
  ⟨physicalObs_state_eq hα hT hm hr hC hmild hθ W t x,
    physicalObs_velocity_eq hα hT hm hr hC hmild hθ W j t x⟩

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T))
    (hphys : ∃ ε > 0, PhysicalObsAgreeOn hα hT W hm₁ hm₂ A ε) :
    ∃ ε > 0, MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε :=
  exists_measuredMapsAgreeOn_of_physical hα hT W hm₁ hr₁ hm₂ hr₂ A hphys

/-- **Regression: the physical and the mild measurement hypotheses are equivalent.**  The
physical hypothesis is therefore neither secretly stronger nor secretly weaker. -/
theorem physical_measurement_faithful (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T)) :
    (∃ ε > 0, PhysicalObsAgreeOn hα hT W hm₁ hm₂ A ε)
      ↔ ∃ ε > 0, MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε :=
  exists_physicalObsAgreeOn_iff_measured hα hT W hm₁ hr₁ hm₂ hr₂ A

example (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W) {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, PhysicalObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ :=
  rotatedGradientSymbol_eq_of_physical hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT hobs

example (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {K₁ K₂ : Wiener1}
    (hcs₁ : ConjSymmetric K₁.coeff) (hcs₂ : ConjSymmetric K₂.coeff)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, PhysicalObsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel)
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel) (smoothSources hT W) ε)
    {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (j : Fin 2) {x : Torus2}
    (hx : x ∈ (closure W)ᶜ) :
    (∀ y ∈ closure W, synth (incl ψ) y = 0)
      ∧ synth (velocity (rotatedGradientSymbol K₁.coeff)
          (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel) j (incl ψ)) x
        = synth (velocity (rotatedGradientSymbol K₂.coeff)
          (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel) j (incl ψ)) x :=
  paper_exterior_velocity_eq_wiener1 hα hT hW hUCP hcs₁ hcs₂ hτ0 hτT hobs hψ j hx

/-- **Regression: realness.**  The observed state is a real-valued function on the torus, and
so is each component of the observed velocity for a real kernel. -/
theorem physical_observation_real (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) (x : Torus2) :
    conj (synth (incl (curveState hT u t)) x) = synth (incl (curveState hT u t)) x :=
  conj_synth_apply ((u (clampT hT t)).conjSymmetric.incl) x

theorem physical_velocity_real {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (hc : ConjSymmetric κ)
    (hT : 0 ≤ T) (u : Curve1 T) (j : Fin 2) (t : ℝ) (x : Torus2) :
    conj (synth (velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) j
          (incl (curveState hT u t))) x)
      = synth (velocity (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) j
          (incl (curveState hT u t))) x :=
  conj_synth_apply
    (conjSymmetric_rotatedGradient_velocity_of_real hb hc j (u (clampT hT t)).conjSymmetric) x

/-- **Regression: the physical divergence-free property of the observed velocity.** -/
theorem physical_velocity_divergence_free (K u : Wiener1) (x : Torus2) :
    deriv (fun s : ℝ => synth (incl (-(kernelConvDeriv K u 1))) (torusShift x 0 s)) 0
      + deriv (fun s : ℝ => synth (incl (kernelConvDeriv K u 0)) (torusShift x 1 s)) 0 = 0 :=
  div_synth_velocity_eq_zero K u x

/-- **Regression: sign and normalization of the velocity operator.** -/
theorem velocity_sign_normalization (K ψ : Wiener1) (x : Torus2) :
    synth (velocity (rotatedGradientSymbol K.coeff)
        (rotatedGradientSymbol_bdd K.isAdmissibleKernel) 0 (incl ψ)) x
          = -deriv (fun s : ℝ => synth (incl (kernelConv K ψ)) (torusShift x 1 s)) 0
      ∧ synth (velocity (rotatedGradientSymbol K.coeff)
        (rotatedGradientSymbol_bdd K.isAdmissibleKernel) 1 (incl ψ)) x
          = deriv (fun s : ℝ => synth (incl (kernelConv K ψ)) (torusShift x 0 s)) 0 :=
  velocity_eq_physical_rotatedGradient K ψ x

example (ψ : Wiener1) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => synth (incl ψ) (torusShift x j s))
      (synth (fourierDeriv j ψ) x) 0 := test_fourier_normalization ψ x j

end PhysicalBridge

/-! ### 9h. v8.0: the Sobolev solution class and its compatibility with Curve1

Completeness of the trigonometric system in the packet's own `L²(𝕋²)`; the fully proved
`H³ ⊂ A¹` lattice embedding and the `A¹`-valued continuous representative of an
essentially bounded Sobolev solution; a Sobolev solution predicate stated on
`ℝ → TorusL2` with **no** `A¹` content, whose representative is proved to satisfy the v7
`IsPhysicalSolution`; the higher-weight (tame) estimates that give existence and `H³`
regularity for the small sources actually used; the physical Sobolev observation
hypothesis and its almost-everywhere-to-pointwise upgrade; and an explicitly constructed
nontrivial Sobolev solution with nonzero terminal mean. -/

section SobolevBridge

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! #### v8.0 step 0: completeness of the trigonometric system in `L²(𝕋²)` -/

example (a : Wiener) (k : Gam) : l2coeff k (synthL2 a) = a k := l2coeff_synthL2 a k

example {u v : TorusL2} (h : ∀ k : Gam, l2coeff k u = l2coeff k v) : u = v :=
  torusL2_ext_of_forall_l2coeff h

/-- **Regression: an `L²` state is its own Fourier synthesis.** -/
theorem fourier_completeness_check {w : Wiener1} {θ : TorusL2}
    (h : ∀ k : Gam, l2coeff k θ = w.coeff k) : synthL2 (incl w) = θ :=
  synthL2_incl_eq_of_coeff h

/-! #### v8.0 step 1: the `H³ ⊂ A¹` embedding and the time-continuity bridge -/

example : Summable (fun k : Gam => wt k ^ 2 / rho k ^ 3) := summable_wtsq_div_rho3

example {c : Gam → ℂ} (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2) :
    Summable fun k => wt k * ‖c k‖ := summable_wt_mul_norm h

/-- **Regression: the constructed `A¹` element has exactly the given coefficients.** -/
theorem sobToWiener1_coeff_check {c : Gam → ℂ}
    (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2) : (sobToWiener1 h).coeff = c := rfl

/-- **Regression: representative agreement.**  The physical synthesis of the constructed `A¹`
element is the given `L²(𝕋²)` state. -/
theorem representative_agreement {c : Gam → ℂ} (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2)
    {θ : TorusL2} (hθ : ∀ k : Gam, l2coeff k θ = c k) :
    synthL2 (incl (sobToWiener1 h)) = θ := synthL2_sobToWiener1 h hθ

example {a : ℝ → Gam → ℂ} (hcont : ∀ k, Continuous fun t => a t k)
    (hsum : ∀ t, Summable fun k => rho k ^ 3 * ‖a t k‖ ^ 2)
    {M : ℝ} (hM : ∀ t, (∑' k : Gam, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) :
    Continuous fun t => sobToWiener1 (hsum t) := continuous_sobToWiener1_curve hcont hsum hM

/-- **Regression: an almost-everywhere `H³` bound is upgraded to every time, endpoints
included.** -/
theorem ae_bound_upgrade {T : ℝ} (hT : 0 < T) {a : ℝ → Gam → ℂ}
    (hcont : ∀ k, Continuous fun t => a t k) {M : ℝ}
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖a t k‖ ^ 2) ≤ M :=
  forall_finset_sum_le_of_ae hT hcont hae

/-! #### v8.0 step 2: the Sobolev solution class and its `A¹` representative -/

noncomputable example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) {M : ℝ} {f : Curve0 T}
    {θ : ℝ → TorusL2} (h : IsSobolevSolution hα hT hm M f θ) : Curve1 T := h.curve

/-- **Regression: the representative agrees with the Sobolev solution in `L²(𝕋²)`.** -/
theorem sobolev_representative_agreement (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (h : IsSobolevSolution hα hT hm M f θ)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    synthL2 (incl (curveState hT h.curve s)) = θ s := h.synthL2_curveState hs

/-- **Regression: endpoint trace.**  The initial trace is the trace of the continuous
representative at `t = 0`, not an almost-everywhere statement. -/
theorem sobolev_endpoint_trace (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (h : IsSobolevSolution hα hT hm M f θ) :
    curveState hT h.curve 0 = 0 ∧ synthL2 (incl (curveState hT h.curve 0)) = θ 0 :=
  ⟨h.curveState_initial, h.synthL2_curveState ⟨le_rfl, hT⟩⟩

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (h : IsSobolevSolution hα hT hm M f θ) :
    IsPhysicalSolution hα hT hm f h.curve := h.isPhysicalSolution_curve

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (h : IsSobolevSolution hα hT hm M f θ) :
    h.curve + sourceQuad hα hT m hm hr h.curve h.curve = duhamelOp hα hT f := h.mild_curve hr

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {M₁ M₂ : ℝ} {f : Curve0 T} {θ₁ θ₂ : ℝ → TorusL2}
    (h₁ : IsSobolevSolution hα hT hm M₁ f θ₁) (h₂ : IsSobolevSolution hα hT hm M₂ f θ₂)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) : θ₁ s = θ₂ s :=
  sobolev_solution_unique hr hC h₁ h₂ hs

/-- **Regression: nonzero-mean forcing is preserved by the Sobolev bridge.** -/
theorem sobolev_mean_balance (hα : 1 / 2 < α) (hT : 0 ≤ T) {κ : Gam → ℂ}
    (hb : IsAdmissibleKernel κ) (hr : IsRealSymbol (rotatedGradientSymbol κ)) {M : ℝ}
    {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsSobolevSolution hα hT (rotatedGradientSymbol_bdd hb) M f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    l2coeff 0 (θ t) = ∫ s in (0:ℝ)..t, (sourceFun hT f s) 0 := h.mean_balance hb hr ht

/-! #### v8.0 step 2b: entering the class from data given on `[0,T]` -/

example {T : ℝ} (hT : 0 ≤ T) (θ : ℝ → TorusL2) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    sobClamp hT θ t = θ t := sobClamp_of_mem hT θ ht

/-- **Regression: an almost-everywhere `H³` bound on `[0,T]` really produces the `bound` field
of the solution class**, endpoints and common null set included. -/
theorem ae_bound_enters_the_class {T : ℝ} (hT : 0 < T) {θ : ℝ → TorusL2} {M : ℝ}
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T))
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) :
    ∀ t : ℝ, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (sobClamp hT.le θ t)‖ ^ 2) ≤ M :=
  bound_sobClamp_of_ae hT hcont hae

/-- **Regression: the representative of the clamped extension represents the original data** at
every time of `[0,T]`. -/
theorem clamped_representative_agreement (hα : 1 / 2 < α) {T : ℝ} {hT : 0 ≤ T}
    (hm : IsBddSymbol m) {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsSobolevSolution hα hT hm M f (sobClamp hT θ)) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    synthL2 (incl (curveState hT h.curve s)) = θ s :=
  synthL2_curveState_sobClamp h hs

/-! #### v8.0 step 3: higher regularity of the constructed small-source solution -/

example {r : ℕ} {R : ℝ} {a : Gam → ℂ} (h : WB r R a) : Summable fun k => wt k ^ r * ‖a k‖ :=
  h.summable

/-- **Regression: the tame convolution bound** — the high weight enters linearly. -/
theorem tame_convolution {r : ℕ} {a b : Gam → ℂ} {Ra R0a Rb R0b : ℝ}
    (ha : WB r Ra a) (ha0 : WB 0 R0a a) (hb : WB r Rb b) (hb0 : WB 0 R0b b) :
    WB r (2 ^ r * (Ra * R0b + R0a * Rb)) (convFun a b) := WB.conv_tame ha ha0 hb hb0

/-- **Regression: the Duhamel operator gains one Wiener weight.** -/
theorem duhamel_weight_gain (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {r : ℕ} {S : ℝ}
    (hS : ∀ s : ℝ, WB r S (fun k => (sourceFun hT g s) k))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    WB (r + 1) (S * duhamelConst α T) (curveState hT (duhamelOp hα hT g) t).coeff :=
  WB_duhamel hα hT g hS ht

/-- **Regression: a `wt³` bound gives the `H³` bound.** -/
theorem wb3_gives_sobolev {R : ℝ} {c : Gam → ℂ} (h : WB 3 R c) (F : Finset Gam) :
    (∑ k ∈ F, rho k ^ 3 * ‖c k‖ ^ 2) ≤ R ^ 2 := sobBound_of_WB3 h F

example (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (A : Submodule ℝ (Curve0 T))
    (hA : ∀ f ∈ A, HasHigherBound hT f) :
    ∃ ε > 0, SobolevExistence hα hT hm A ε :=
  exists_sobolevExistence_of_higherBound hα hT hm hr hC A hA

/-! #### v8.0 step 4: the Sobolev observation bridge and the recovery corollary -/

example (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁) (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    (A : Submodule ℝ (Curve0 T))
    (hex₁ : ∃ ε > 0, SobolevExistence hα hT.le hm₁ A ε)
    (hex₂ : ∃ ε > 0, SobolevExistence hα hT.le hm₂ A ε)
    (hobs : ∃ ε > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ A ε) :
    ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ A ε :=
  exists_measuredMapsAgreeOn_of_sobolev hα hT hW hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ A hex₁ hex₂ hobs

/-- **Regression: Sobolev/physical observation compatibility.**  The observed state of a Sobolev
solution is a representative of its `L²` class, and is continuous in space and in time. -/
theorem sobolev_observation_compatible (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (h : IsSobolevSolution hα hT hm M f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (x : Torus2) (j : Fin 2) :
    ((fun y => h.obsState t y) =ᵐ[(volume : Measure Torus2)] (θ t : Torus2 → ℂ))
      ∧ Continuous (fun s : ℝ => h.obsState s x)
      ∧ Continuous (fun y : Torus2 => h.obsState t y)
      ∧ Continuous (fun s : ℝ => h.obsVel j s x) :=
  ⟨h.obsState_ae ht, h.continuous_obsState x, h.continuous_obsState_space t,
    h.continuous_obsVel j x⟩

/-- **Regression: the almost-everywhere/pointwise upgrade is proved, not defined away.** -/
theorem ae_to_pointwise_upgrade {W : Set Torus2} (hW : IsOpen W) {g₁ g₂ : Torus2 → ℂ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hae : ∀ᵐ x ∂((volume : Measure Torus2).restrict W), g₁ x = g₂ x) :
    ∀ x ∈ W, g₁ x = g₂ x :=
  forall_eq_of_ae_eq_open (μ := (volume : Measure Torus2)) hW hg₁ hg₂ hae

example (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖rotatedGradientSymbol κ₁ j k‖ ≤ C₁)
    (hC₂ : ∀ j k, ‖rotatedGradientSymbol κ₂ j k‖ ≤ C₂)
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hex₁ : ∃ ε > 0, SobolevExistence hα hT.le hm₁ (smoothSources hT W) ε)
    (hex₂ : ∃ ε > 0, SobolevExistence hα hT.le hm₂ (smoothSources hT W) ε)
    (hobs : ∃ ε > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε)
    (ψ : Wiener1) (j : Fin 2) {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    synth (velocity (rotatedGradientSymbol κ₁) hm₁ j (incl ψ)) x
      = synth (velocity (rotatedGradientSymbol κ₂) hm₂ j (incl ψ)) x :=
  paper_exterior_velocity_eq_sobolev hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hC hτ0 hτT
    hex₁ hex₂ hobs ψ j hx

/-! #### v8.0 step 3b: the higher-weight hypothesis is discharged on the smooth source space -/

example (n : ℤ) : (1 + |(n : ℝ)|) ^ 2 * decayWeight4 n ≤ 4 * decayWeight n :=
  weighted_sq_decayWeight4_le n

example {a : Wiener} (h : SmoothWiener a) : Summable fun k : Gam => wt k ^ 2 * ‖a k‖ :=
  summable_wtsq_norm_of_smoothWiener h

/-- **Regression: every smooth source really has the higher-weight bound.**  Nothing about the
paper's forward theory is assumed here. -/
theorem smooth_sources_have_higher_bound {T : ℝ} (hT : 0 < T) (W : Set Torus2)
    {V : Curve0 T} (hV : V ∈ smoothSources hT W) : HasHigherBound hT.le V :=
  hasHigherBound_of_mem_smoothSources hT W hV

/-- **Regression: the solution class is inhabited over the class the recovery theorem uses**, by
a genuinely nonzero smooth source. -/
theorem sobolev_class_inhabited (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (f : Curve0 T) (M : ℝ) (θ : ℝ → TorusL2),
      f ∈ smoothSources hT W ∧ f ≠ 0 ∧ IsSobolevSolution hα hT.le hm M f θ :=
  exists_nonzero_smoothSource_sobolevSolution hα hT hm hr hC hW hne

/-- **Regression: Sobolev existence on the smooth source space is proved, not hypothesized.** -/
theorem sobolev_existence_is_proved (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (W : Set Torus2) : ∃ ε > 0, SobolevExistence hα hT.le hm (smoothSources hT W) ε :=
  exists_sobolevExistence_smoothSources hα hT hm hr hC W

/-- **Regression: the recovery theorem on the paper's Sobolev solutions, with the existence
hypotheses discharged.**  The remaining inputs are the portable `FractionalUCP` and the
measurement hypothesis itself. -/
theorem paper_recovery_sobolev_smooth (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖rotatedGradientSymbol κ₁ j k‖ ≤ C₁)
    (hC₂ : ∀ j k, ‖rotatedGradientSymbol κ₂ j k‖ ≤ C₂)
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε)
    (ψ : Wiener1) (j : Fin 2) {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    synth (velocity (rotatedGradientSymbol κ₁) hm₁ j (incl ψ)) x
      = synth (velocity (rotatedGradientSymbol κ₂) hm₂ j (incl ψ)) x :=
  paper_exterior_velocity_eq_sobolev_smooth hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hC hτ0 hτT
    hobs ψ j hx

/-! #### v8.0: a constructed nontrivial Sobolev solution -/

/-- **Regression: an actual constructed solution.**  The mean-mode control, its mild solution,
its Sobolev regularity, and its nonzero terminal mean — nothing is assumed. -/
theorem constructed_solution_example (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    (meanSolution hα hT.le + sourceQuad hα hT.le m hm hr (meanSolution hα hT.le)
        (meanSolution hα hT.le) = duhamelOp hα hT.le (meanSource hT.le))
      ∧ IsSobolevSolution hα hT.le hm (‖meanSolution hα hT.le‖ ^ 2) (meanSource hT.le)
          (mildPhysState hT.le (meanSolution hα hT.le))
      ∧ l2coeff 0 (mildPhysState hT.le (meanSolution hα hT.le) T) = (T : ℂ)
      ∧ l2coeff 0 (mildPhysState hT.le (meanSolution hα hT.le) T) ≠ 0 :=
  ⟨meanSolution_mild hα hT.le hm hr, isSobolevSolution_meanSolution hα hT.le hm hr,
    meanSolution_terminal_mean hα hT.le, meanSolution_terminal_mean_ne_zero hα hT⟩

/-- **Regression: the constructed source really has nonzero spatial mean.** -/
theorem constructed_source_nonzero_mean (hT : 0 ≤ T) (s : ℝ) :
    (sourceFun hT (meanSource hT) s) 0 = 1 ∧ (1 : ℂ) ≠ 0 := by
  refine ⟨?_, one_ne_zero⟩
  rw [sourceFun_meanSource hT s 0, diracFun, if_pos rfl]

end SobolevBridge

/-! ### 9i. v9.0: exact paper-map alignment

The Li–Wang forward energy package at `s = 3` (`L^∞_t H³ ∩ L²_t H^{3+α} ∩ L^∞_t L^q` with
`0 < 1/q < α − 1/2`), proved for the constructed small-source solution by one more tame Picard
bootstrap; the paper-facing solution class on `ℝ → L²(𝕋²)` and the two bridges to the v8.0
Sobolev class; the canonical source-to-solution map (1.6), its single-valuedness, and the
theorem that equality of the two maps implies the v8.0 measurement relation; the inclusion of
the packet's smooth source family into the paper's `C_c^∞(W × (0,T))`; and the paper-shaped
exterior endpoint on the genuine torus convolution. -/

section PaperAlignment

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! #### v9.0 step 1: the `s = 3` forward energy package -/

example {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    Summable fun k : Gam => wt k ^ 3 * ‖pcoeff G k‖ := summable_wt_cube_norm_pcoeff h

/-- **Regression: the third-order source bound holds on the whole smooth source family.** -/
theorem smooth_sources_have_third_bound {T : ℝ} (hT : 0 < T) (W : Set Torus2) {V : Curve0 T}
    (hV : V ∈ smoothSources hT W) : HasHigherBound3 hT.le V :=
  hasHigherBound3_of_mem_smoothSources hT W hV

/-- **Regression: a `wtʳ` bound is an `Hʳ` bound, for every `r`.** -/
theorem wb_gives_sobolev {r : ℕ} {R : ℝ} {c : Gam → ℂ} (h : WB r R c) (F : Finset Gam) :
    (∑ k ∈ F, rho k ^ r * ‖c k‖ ^ 2) ≤ R ^ 2 := sobBound_of_WB h F

/-- **Regression: `H⁴ ⊂ H^{3+α}`.**  This is where the paper's upper bound `α < 1` is used. -/
theorem sobolev_four_embeds (hα1 : α ≤ 1) {R : ℝ} {c : Gam → ℂ} (h : WB 4 R c) :
    MemSobolev (3 + α) c ∧ sobEnergy (3 + α) c ≤ R ^ 2 :=
  ⟨memSobolev_of_WB4 hα1 h, sobEnergy_le_of_WB4 hα1 h⟩

/-- **Regression: the genuine `L²(0,T;H^{3+α})` estimate**, with measurability and integrability
proved, not a pointwise-in-time restatement. -/
theorem l2_time_sobolev (hα1 : α ≤ 1) {T : ℝ} {hT : 0 ≤ T} {u : Curve1 T} {R : ℝ}
    (h4 : ∀ t ∈ Set.Icc (0:ℝ) T, WB 4 R (curveState hT u t).coeff) :
    ((∫⁻ t in Set.Ioc (0:ℝ) T,
        ENNReal.ofReal (sobEnergy (3 + α) (curveState hT u t).coeff))
      ≤ ENNReal.ofReal (T * R ^ 2))
      ∧ IntegrableOn (fun t : ℝ => sobEnergy (3 + α) (curveState hT u t).coeff)
          (Set.Ioc (0:ℝ) T) volume :=
  ⟨lintegral_sobEnergy_le hα1 h4, integrableOn_sobEnergy hα1 (WB_curveState_all h4)⟩

example {r : ℕ} {R : ℝ} {c : Gam → ℂ} (h : WB r R c) :
    Summable (fun k : Gam => rho k ^ r * ‖c k‖ ^ 2)
      ∧ (∑' k : Gam, rho k ^ r * ‖c k‖ ^ 2) ≤ R ^ 2 :=
  ⟨summable_rho_pow_of_WB h, tsum_rho_pow_le_of_WB h⟩

example {T : ℝ} {hT : 0 ≤ T} {f : Curve0 T} (h : HasHigherBound3 hT f) : HasHigherBound hT f :=
  h.toHasHigherBound

/-- **Regression: the paper's exponent inequality `0 < 1/q < α − 1/2` is satisfied**, and `q` is
a genuine Lebesgue exponent. -/
theorem paper_exponent_admissible (hα : 1 / 2 < α) (hα1 : α < 1) :
    4 < paperExp α ∧ 0 < 1 / paperExp α ∧ 1 / paperExp α < α - 1 / 2 :=
  ⟨four_lt_paperExp hα hα1, inv_paperExp_pos hα, inv_paperExp_lt hα⟩

/-- **Regression: the uniform `L^q(𝕋²)` bound of a synthesized state.** -/
theorem lq_bound (p : ENNReal) (a : Wiener) :
    eLpNorm ((synthL2 a : Torus2 → ℂ)) p (volume : Measure Torus2) ≤ ENNReal.ofReal ‖a‖
      ∧ MemLp ((synthL2 a : Torus2 → ℂ)) p (volume : Measure Torus2) :=
  ⟨eLpNorm_synthL2_le p a, memLp_synthL2 p a⟩

/-! #### v9.0 step 2: the paper-facing solution class, and both bridges -/

/-- **Regression: the constructed small-source solution is a Li–Wang `s = 3` solution.** -/
theorem paper_solution_of_mild (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ} (hT : 0 < T)
    {hm : IsBddSymbol m} {hr : IsRealSymbol m} {f : Curve0 T} {u : Curve1 T} {R4 : ℝ}
    (hmild : u + sourceQuad hα hT.le m hm hr u u = duhamelOp hα hT.le f)
    (h4 : ∀ t ∈ Set.Icc (0:ℝ) T, WB 4 R4 (curveState hT.le u t).coeff) :
    IsPaperSolution hα hT hm (R4 ^ 2) (T * R4 ^ 2) ‖u‖ f (mildPhysState hT.le u) :=
  isPaperSolution_mild hα1 hT hmild h4

/-- **Regression: a paper solution is a v8.0 Sobolev solution, with `L²` equality on `[0,T]`.** -/
theorem paper_to_sobolev (hα : 1 / 2 < α) {T : ℝ} {hT : 0 < T} {hm : IsBddSymbol m}
    {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (h : IsPaperSolution hα hT hm M N K f θ) :
    IsSobolevSolution hα hT.le hm M f (sobClamp hT.le θ)
      ∧ ∀ s ∈ Set.Icc (0:ℝ) T,
        synthL2 (incl (curveState hT.le h.isSobolevSolution.curve s)) = θ s :=
  ⟨h.isSobolevSolution, fun _ hs => h.synthL2_curveState hs⟩

/-- **Regression: the `H^{3+α}` energy of a paper solution is a genuine convergent sum and is
measurable in time** — `tsum = 0` is never read as evidence of summability. -/
theorem paper_energy_is_genuine (hα : 1 / 2 < α) {T : ℝ} {hT : 0 < T} {hm : IsBddSymbol m}
    {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (h : IsPaperSolution hα hT hm M N K f θ) :
    (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
        MemSobolev (3 + α) (fun k => l2coeff k (θ t)))
      ∧ AEMeasurable (fun t : ℝ => ENNReal.ofReal (sobEnergy (3 + α) (fun k => l2coeff k (θ t))))
          ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T))
      ∧ 4 < paperExp α :=
  ⟨h.sob3a, h.aemeasurable_energy, h.exp_admissible.1⟩

/-- **Regression: uniqueness inside the paper class**, by reuse of the v8.0 theorem. -/
theorem paper_solution_unique (hα : 1 / 2 < α) {T : ℝ} {hT : 0 < T} {hm : IsBddSymbol m}
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {M₁ N₁ K₁ M₂ N₂ K₂ : ℝ} {f : Curve0 T} {θ₁ θ₂ : ℝ → TorusL2}
    (h₁ : IsPaperSolution hα hT hm M₁ N₁ K₁ f θ₁)
    (h₂ : IsPaperSolution hα hT hm M₂ N₂ K₂ f θ₂) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    θ₁ s = θ₂ s := IsPaperSolution.unique hr hC h₁ h₂ hs

/-- **Regression: the nonzero-mean balance is proved for the paper class, not assumed.** -/
theorem paper_mean_balance (hα : 1 / 2 < α) {T : ℝ} {hT : 0 < T} {κ : Gam → ℂ}
    (hb : IsAdmissibleKernel κ) (hr : IsRealSymbol (rotatedGradientSymbol κ))
    {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsPaperSolution hα hT (rotatedGradientSymbol_bdd hb) M N K f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    l2coeff 0 (θ t) = ∫ s in (0:ℝ)..t, (sourceFun hT.le f s) 0 :=
  IsPaperSolution.mean_balance hb hr h ht

/-! #### v9.0 step 3: the canonical source-to-solution map -/

/-- **Regression: paper existence on the smooth source family is proved, not assumed.** -/
theorem paper_existence_is_proved (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ} (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (W : Set Torus2) : ∃ ε > 0, PaperExistence hα hT hm (smoothSources hT W) ε :=
  exists_paperExistence_smoothSources hα hα1 hT hm hr hC W

/-- **Regression: the canonical map is single-valued** — the observations do not depend on the
chosen witness, because uniqueness is used. -/
theorem paper_map_single_valued (hα : 1 / 2 < α) {T : ℝ} {hT : 0 < T} {hm : IsBddSymbol m}
    {A : Submodule ℝ (Curve0 T)} {ε : ℝ} (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) {M N K : ℝ} {θ : ℝ → TorusL2}
    (h : IsPaperSolution hα hT hm M N K f θ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    paperSol hex hf hs t = θ t
      ∧ ∀ j : Fin 2, ((paperObsVel hex hf hs j t : Torus2 → ℂ))
          =ᵐ[(volume : Measure Torus2)] fun x => h.isSobolevSolution.obsVel j t x :=
  ⟨paperSol_eq hr hC hex hf hs h ht, fun j => paperObsVel_ae hr hC hex hf hs h j t⟩

/-- **Regression: equality of the canonical paper maps implies the v8.0 measurement
relation.**  This is what removes the largest conclusion-adjacent hypothesis from the
capstone. -/
theorem paper_maps_give_sobolev_relation (hα : 1 / 2 < α) {T : ℝ} {hT : 0 < T}
    {W : Set Torus2} {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁) (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    {A : Submodule ℝ (Curve0 T)} {ε : ℝ} (hε : 0 < ε)
    (hex₁ : PaperExistence hα hT hm₁ A ε) (hex₂ : PaperExistence hα hT hm₂ A ε)
    (hagree : PaperObsMapsAgree hα hT W hm₁ hm₂ A ε hex₁ hex₂) :
    SobolevObsAgreeOn hα hT.le W hm₁ hm₂ A ε
      ∧ ∃ ε' > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ A ε' :=
  ⟨sobolevObsAgreeOn_of_paperMapsAgree hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hex₁ hex₂ hagree,
    exists_sobolevObsAgreeOn_of_paperMapsAgree hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hε hex₁ hex₂ hagree⟩

/-- **Regression: the paper class is inhabited over the recovery class**, by a nonzero smooth
source. -/
theorem paper_class_inhabited (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ} (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (f : Curve0 T) (M N K : ℝ) (θ : ℝ → TorusL2),
      f ∈ smoothSources hT W ∧ f ≠ 0 ∧ IsPaperSolution hα hT hm M N K f θ :=
  exists_nonzero_smoothSource_paperSolution hα hα1 hT hm hr hC hW hne

/-! #### v9.0 step 4: the source family is inside the paper's `C_c^∞(W × (0,T))` -/

/-- **Regression: every smooth source of the packet is an admissible paper source.** -/
theorem smooth_sources_are_paper_sources {T : ℝ} (hT : 0 < T) {W : Set Torus2} {V : Curve0 T}
    (hV : V ∈ smoothSources hT W) : IsPaperSource hT W V :=
  isPaperSource_of_mem_smoothSources hT hV

example {T : ℝ} {hT : 0 < T} {W : Set Torus2} {V : Curve0 T} (h : IsPaperSource hT W V) :
    ∃ Φ : ℝ × (ℝ × ℝ) → ℂ, (∀ q, conj (Φ q) = Φ q) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ y : Fin 2 → ℝ,
        sourcePhys hT.le V t (torusProj y) = Φ (t, (y 0, y 1)))
      ∧ (∃ K : Set Torus2, IsCompact K ∧ K ⊆ W ∧
          ∀ (t : ℝ) (y : Fin 2 → ℝ), torusProj y ∉ K → Φ (t, (y 0, y 1)) = 0)
      ∧ (∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ < T ∧ ∀ t ∉ Set.Icc t₀ t₁, ∀ p, Φ (t, p) = 0) :=
  sourcePhys_eq_of_isPaperSource h

/-! #### v9.0 step 5: the paper-shaped endpoint -/

/-- **Regression: the exterior test profile enters the `A¹` carrier exactly.** -/
theorem exterior_profile_roundtrip {a : RealWiener} (ha : SmoothWiener a.val) (x : Torus2)
    (k : Gam) :
    incl (exteriorProfile ha) = a.val
      ∧ synth (incl (exteriorProfile ha)) x = synth a.val x
      ∧ (exteriorProfile ha).coeff k = a.val k :=
  ⟨incl_exteriorProfile ha, synth_exteriorProfile ha x, coeff_exteriorProfile ha k⟩

/-- **Regression: the paper-shaped endpoint.**  From equality of the canonical paper
source-to-solution maps: the genuine convolution velocities agree at every exterior point, and
the kernels agree off the zero mode.  The kernel hypotheses are exactly what the proof uses —
integrability, reality, and the weighted Fourier decay bound. -/
theorem paper_endpoint (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁) (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) {ε : ℝ} (hε : 0 < ε)
    (hex₁ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩) (smoothSources hT W) ε)
    (hex₂ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (smoothSources hT W) ε)
    (hagree : PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (smoothSources hT W) ε hex₁ hex₂)
    {a : RealWiener} (ha : SmoothWiener a.val)
    (hsupp : ∀ y ∈ closure W, synth a.val y = 0)
    {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    (∀ y ∈ closure W, synth (incl (exteriorProfile ha)) y = 0)
      ∧ (∀ y : Torus2, synth (incl (exteriorProfile ha)) y = synth a.val y)
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
      ∧ ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k :=
  paper_exterior_velocity_eq_of_paperMapsAgree hα hT hW hUCP hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂
    hτ0 hτT hε hex₁ hex₂ hagree ha hsupp hx

/-- **Regression: the same endpoint for the packet's paper-kernel class.** -/
theorem paper_endpoint_elliptic (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {c₁ D₁ c₂ D₂ : ℝ}
    (hell₁ : OrderedFourierEllipticity (kernelCoeff K₁) c₁ D₁)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁))
    (hell₂ : OrderedFourierEllipticity (kernelCoeff K₂) c₂ D₂)
    (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) {ε : ℝ} (hε : 0 < ε)
    (hex₁ : PaperExistence hα hT
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁)) (smoothSources hT W) ε)
    (hex₂ : PaperExistence hα hT
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂)) (smoothSources hT W) ε)
    (hagree : PaperObsMapsAgree hα hT W
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁))
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂))
      (smoothSources hT W) ε hex₁ hex₂)
    {a : RealWiener} (ha : SmoothWiener a.val)
    (hsupp : ∀ y ∈ closure W, synth a.val y = 0)
    {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k :=
  (paper_exterior_velocity_eq_of_paperMapsAgree_elliptic hα hT hW hUCP hK₁ hK₂ hell₁ hcs₁
    hell₂ hcs₂ hτ0 hτT hε hex₁ hex₂ hagree ha hsupp hx).2.2.2.2

end PaperAlignment

/-! ### 9j. v10.0: the paper's source class, realized

The essential-supremum entry into the `s = 3` class; the spatial partial derivatives of a
jointly smooth space-time function and the resulting time-uniform Fourier decay; the
realization of an arbitrary real `C_c^∞(W × (0,T))` datum as an actual `Curve0 T` source, with
an exact round trip; the paper source class `paperSources hT W`, existence of paper solutions on
all of it, and the restriction of the measurement hypothesis along the inclusion of the packet's
smooth sources; and the endpoint with the measurement datum stated on the paper's own source
class. -/

section PaperSourceRealization

open scoped ContDiff

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! #### v10.0 step 1: the paper class from an essential-supremum bound -/

/-- **Regression: an almost-everywhere `H³` bound on `[0,T]` suffices**, for a state whose
Fourier coordinates are only continuous *relative to* `[0,T]`. -/
theorem ae_energy_enters_paper_class {T : ℝ} (hT : 0 < T) {θ : ℝ → TorusL2} {M : ℝ}
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T))
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M :=
  forall_finset_sum_le_of_ae_on hT hcont hae

/-- **Regression: the continuity field is stated in weak-`L²` form**, which `L²`-norm continuity
implies — and which, *inside the class*, is equivalent to it: the uniform `H³` bound upgrades the
coefficientwise continuity back to norm continuity, so the restatement changes no solution. -/
theorem paper_class_continuity_equivalent {T : ℝ} {θ : ℝ → TorusL2}
    (h : ContinuousOn θ (Set.Icc (0:ℝ) T)) (k : Gam) :
    ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T) :=
  coeff_continuousOn_of_continuousOn h k

theorem paper_class_forces_norm_continuity (hα : 1 / 2 < α) {T : ℝ} {hT : 0 < T}
    {hm : IsBddSymbol m} {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsPaperSolution hα hT hm M N K f θ) : ContinuousOn θ (Set.Icc (0:ℝ) T) := h.continuousOn'

/-! #### v10.0 step 2: spatial partials of a jointly smooth space-time function -/

example {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) (t : ℝ) :
    slice (spd0 Φ) t = pd0 (slice Φ t) ∧ slice (spd1 Φ) t = pd1 (slice Φ t) :=
  ⟨slice_spd0 h t, slice_spd1 h t⟩

example {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (spd0 Φ) ∧ ContDiff ℝ ∞ (spd1 Φ) := ⟨contDiff_spd0 h, contDiff_spd1 h⟩

/-- **Regression: the fourth-order Fourier decay of the slices holds with a constant
independent of time.** -/
theorem uniform_decay_in_time {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y)))
    {a₀ a₁ : ℝ} (ha01 : a₀ ≤ a₁) (hav : ∀ t ∉ Set.Icc a₀ a₁, ∀ p, Φ (t, p) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (k : Gam),
      ‖pcoeff (slice Φ t) k‖ ≤ C * (decayWeight4 (k 0) * decayWeight4 (k 1)) :=
  exists_uniform_pcoeff_decay4 hsm hper0 hper1 ha01 hav

example {Φ : ℝ × (ℝ × ℝ) → ℂ} (hc : Continuous Φ) (k : Gam) :
    Continuous fun t : ℝ => pcoeff (slice Φ t) k := continuous_pcoeff_slice hc k

/-- **Regression: the Wiener element of the slice is continuous in time**, in the `ℓ¹` norm —
the analytic heart of the realization. -/
theorem wiener_slice_continuous {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y)))
    {a₀ a₁ : ℝ} (ha01 : a₀ ≤ a₁) (hav : ∀ t ∉ Set.Icc a₀ a₁, ∀ p, Φ (t, p) = 0) :
    Continuous fun t : ℝ =>
      wienerOfSmooth (slice Φ t) (isSmoothPeriodic_slice hsm hper0 hper1 t) :=
  continuous_wienerSlice hsm hper0 hper1 ha01 hav

/-! #### v10.0 step 3: realizing a `C_c^∞(W × (0,T))` datum as a `Curve0 T` source -/

/-- **Regression: the round trip is exact.**  The physical field of the realized source is the
given paper datum at every time of `[0,T]` and every point of the torus. -/
theorem paper_datum_round_trip {T : ℝ} {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (y : Fin 2 → ℝ) :
    sourcePhys hT.le (paperCurve h) t (torusProj y) = Φ (t, (y 0, y 1))
      ∧ SmoothSpacetimeRep hT W (paperCurve h) Φ
      ∧ IsPaperSource hT W (paperCurve h)
      ∧ paperCurve h ∈ paperSources hT W :=
  ⟨sourcePhys_paperCurve h ht y, smoothSpacetimeRep_paperCurve h, isPaperSource_paperCurve h,
    paperCurve_mem_paperSources h⟩

example {T : ℝ} {hT : 0 < T} {W : Set Torus2} {V : Curve0 T} :
    IsPaperSource hT W V ↔ ∃ Φ : ℝ × (ℝ × ℝ) → ℂ, IsPaperField hT W Φ ∧
      SmoothSpacetimeRep hT W V Φ := isPaperSource_iff_exists_paperField

/-! #### v10.0 step 4: the paper source class and existence on it -/

/-- **Regression: the packet's smooth sources are a subclass of the paper's.** -/
theorem paper_sources_contain_smooth {T : ℝ} (hT : 0 < T) (W : Set Torus2) :
    smoothSources hT W ≤ paperSources hT W := smoothSources_le_paperSources hT W

/-- **Regression: every admissible paper source carries the third-order bound.** -/
theorem paper_sources_have_third_bound {T : ℝ} {hT : 0 < T} {W : Set Torus2} {V : Curve0 T}
    (h : IsPaperSource hT W V) : HasHigherBound3 hT.le V := hasHigherBound3_of_isPaperSource h

/-- **Regression: paper solutions exist on the whole paper source class.** -/
theorem paper_existence_on_full_class (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ} (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (W : Set Torus2) : ∃ ε > 0, PaperExistence hα hT hm (paperSources hT W) ε :=
  exists_paperExistence_paperSources hα hα1 hT hm hr hC W

/-- **Regression: equality of the paper maps restricts to a smaller source class**, by
uniqueness of the canonical solutions. -/
theorem paper_maps_restrict {hα : 1 / 2 < α} {T : ℝ} {hT : 0 < T} {W : Set Torus2}
    {m₁ m₂ : Fin 2 → Gam → ℂ} {hm₁ : IsBddSymbol m₁} {hm₂ : IsBddSymbol m₂}
    (hr₁ : IsRealSymbol m₁) {C₁ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁)
    (hr₂ : IsRealSymbol m₂) {C₂ : ℝ} (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    {A B : Submodule ℝ (Curve0 T)} (hAB : A ≤ B) {ε : ℝ}
    (hexA₁ : PaperExistence hα hT hm₁ A ε) (hexB₁ : PaperExistence hα hT hm₁ B ε)
    (hexA₂ : PaperExistence hα hT hm₂ A ε) (hexB₂ : PaperExistence hα hT hm₂ B ε)
    (h : PaperObsMapsAgree hα hT W hm₁ hm₂ B ε hexB₁ hexB₂) :
    PaperObsMapsAgree hα hT W hm₁ hm₂ A ε hexA₁ hexA₂ :=
  paperObsMapsAgree_mono hr₁ hC₁ hr₂ hC₂ hAB hexA₁ hexB₁ hexA₂ hexB₂ h

/-! #### v10.0 step 5: the endpoint from the paper's own source-to-solution map -/

/-- **Regression: the paper-shaped conclusion, with the measurement hypothesis stated on all of
`C_c^∞(W × (0,T))`.** -/
theorem paper_endpoint_full (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁) (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) {ε : ℝ} (hε : 0 < ε)
    (hexP₁ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩) (paperSources hT W) ε)
    (hexP₂ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε)
    (hagree : PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε hexP₁ hexP₂)
    {a : RealWiener} (ha : SmoothWiener a.val)
    (hsupp : ∀ y ∈ closure W, synth a.val y = 0)
    {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    (∀ y ∈ closure W, synth (incl (exteriorProfile ha)) y = 0)
      ∧ (∀ y : Torus2, synth (incl (exteriorProfile ha)) y = synth a.val y)
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
      ∧ ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k :=
  paper_exterior_velocity_eq_of_paperMapsAgree_full hα hT hW hUCP hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂
    hτ0 hτT hε hexP₁ hexP₂ hagree ha hsupp hx

end PaperSourceRealization

/-! ### 9k. v11.0: exact paper interfaces

The paper-facing solution class now starts from the Bochner/weak formulation without a
continuity field; coefficient continuity and strong `L²` continuity are consequences.  The
inverse endpoint now quantifies over a physical real `C_c^∞(W^e)` field, and the class of such
tests is constructively nonempty whenever the exterior is nonempty. -/

section ExactPaperInterfaces

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-- **Regression: coordinate continuity is derived, not supplied.** -/
theorem energy_solution_forces_coordinate_continuity
    {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m}
    {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsPaperEnergySolution hα hT hm M N K f θ) (k : Gam) :
    ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0 : ℝ) T) :=
  h.coeff_continuousOn k

/-- **Regression: the weak energy solution has a strongly continuous `L²` representative.** -/
theorem energy_solution_forces_strong_continuity
    {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m}
    {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsPaperEnergySolution hα hT hm M N K f θ) :
    ContinuousOn θ (Set.Icc (0 : ℝ) T) :=
  h.continuousOn

/-- **Regression: the continuity-free and canonical representative classes coincide.** -/
example {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m}
    {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} :
    IsPaperEnergySolution hα hT hm M N K f θ ↔
      IsPaperSolution hα hT hm M N K f θ :=
  isPaperEnergySolution_iff_isPaperSolution

/-- **Regression: a physical paper test is reconstructed pointwise from its coefficients.** -/
example {W : Set Torus2} {G : ℝ × ℝ → ℂ} (hG : IsPaperExteriorField W G)
    (y : Fin 2 → ℝ) :
    paperExteriorTorusField hG (torusProj y) = G (y 0, y 1) :=
  paperExteriorTorusField_torusProj hG y

/-- **Regression: the physical exterior test class is non-vacuous.** -/
theorem physical_exterior_tests_exist {W : Set Torus2}
    (hne : ((closure W)ᶜ).Nonempty) :
    ∃ (G : ℝ × ℝ → ℂ) (hG : IsPaperExteriorField W G),
      paperExteriorTorusField hG ≠ 0 :=
  exists_nonzero_paperExteriorField hne

end ExactPaperInterfaces

/-! ### 10. Axiom audit -/

-- v1.1 headline results
#print axioms LiWang.Formalization.norm_conv_le
#print axioms LiWang.Formalization.norm_transport_le
#print axioms LiWang.Formalization.fderiv_fderiv_quadResidual_apply
#print axioms LiWang.Formalization.realLiWangPolarization
#print axioms LiWang.Formalization.realKernelPolarization
#print axioms LiWang.Formalization.testSymbolNoI_reality_failure

-- v2.0: synthesis
#print axioms LiWang.Formalization.norm_synth_le
#print axioms LiWang.Formalization.synth_apply
#print axioms LiWang.Formalization.synth_wdirac
#print axioms LiWang.Formalization.coeffCLM_synth
#print axioms LiWang.Formalization.synth_injective
#print axioms LiWang.Formalization.integral_emode

-- v2.0: the convolution–product theorem
#print axioms LiWang.Formalization.tsum_character_mul
#print axioms LiWang.Formalization.synth_conv
#print axioms LiWang.Formalization.conv_wdirac_wdirac

-- v2.0: differentiation transfer
#print axioms LiWang.Formalization.hasDerivAt_lift
#print axioms LiWang.Formalization.deriv_lift
#print axioms LiWang.Formalization.lift_periodic

-- v2.0: the torus-quotient differentiation statement
#print axioms LiWang.Formalization.hasDerivAt_synth_torus
#print axioms LiWang.Formalization.deriv_synth_torus
#print axioms LiWang.Formalization.hasDerivAt_re_synth_torus
#print axioms LiWang.Formalization.div_velocity_eq_zero
#print axioms LiWang.Formalization.div_synth_velocity_eq_zero

-- v2.0: reality and the velocity operator
#print axioms LiWang.Formalization.conj_synth_apply
#print axioms LiWang.Formalization.realSynth_injective
#print axioms LiWang.Formalization.velocity_rotatedGradient_zero
#print axioms LiWang.Formalization.velocity_rotatedGradient_one
#print axioms LiWang.Formalization.rotatedGradient_velocity_div_zero
#print axioms LiWang.Formalization.synth_finiteKernel

-- v2.0: the physical transport diagram and the certificate
#print axioms LiWang.Formalization.synth_transport
#print axioms LiWang.Formalization.synth_transport_apply
#print axioms LiWang.Formalization.synth_quadResidual
#print axioms LiWang.Formalization.paperFacingCertificate
#print axioms LiWang.Formalization.paperFacingPolarization
#print axioms LiWang.Formalization.finiteKernel_certificate

-- v2.0: spacetime
#print axioms LiWang.Formalization.norm_spacetimeTransport_le
#print axioms LiWang.Formalization.fderiv_spacetimeQuadResidual_zero
#print axioms LiWang.Formalization.fderiv_fderiv_spacetimeQuadResidual
#print axioms LiWang.Formalization.analyticOnNhd_spacetimeQuadResidual
#print axioms LiWang.Formalization.spacetimeLiWangPolarization
#print axioms LiWang.Formalization.spacetimeKernelPolarization
#print axioms LiWang.Formalization.synth_spacetimeQuadResidual

-- v2.0: fractional heat
#print axioms LiWang.Formalization.norm_heatOp_le
#print axioms LiWang.Formalization.heatOp_heatOp
#print axioms LiWang.Formalization.one_add_mul_exp_le
#print axioms LiWang.Formalization.mul_exp_neg_rpow_le
#print axioms LiWang.Formalization.norm_heatSmooth_le_sharp
#print axioms LiWang.Formalization.intervalIntegrable_heatConst
#print axioms LiWang.Formalization.norm_duhamel_integrand_le

-- v2.0: strong continuity, the Duhamel integral and the mild map
#print axioms LiWang.Formalization.continuous_heatFlow
#print axioms LiWang.Formalization.continuousAt_heatSmoothFun
#print axioms LiWang.Formalization.norm_heatSmoothFun_incl_le
#print axioms LiWang.Formalization.intervalIntegrable_duhamelIntegrand
#print axioms LiWang.Formalization.integral_heatConst
#print axioms LiWang.Formalization.norm_duhamelIntegral_le
#print axioms LiWang.Formalization.norm_duhamelIntegral_sub_le
#print axioms LiWang.Formalization.norm_mildMap_le
#print axioms LiWang.Formalization.norm_mildMap_sub_le
#print axioms LiWang.Formalization.exists_local_contraction

-- v2.0: continuity in time of the Duhamel term (the previously missing lemma)
#print axioms LiWang.Formalization.duhamelIntegral_eq_reflected
#print axioms LiWang.Formalization.intervalIntegrable_duhamelKernel_long
#print axioms LiWang.Formalization.tendsto_duhamelIntegral
#print axioms LiWang.Formalization.continuous_duhamelIntegral
#print axioms LiWang.Formalization.continuous_heatFlow1
#print axioms LiWang.Formalization.mildMap1_zero
#print axioms LiWang.Formalization.continuous_mildMap1

-- v2.0: the local mild solution (Banach fixed point)
#print axioms LiWang.Formalization.duhamelConst_mono
#print axioms LiWang.Formalization.mildCurveMap
#print axioms LiWang.Formalization.exists_local_mild_solution
#print axioms LiWang.Formalization.exists_local_mild_solution_rotatedGradient
#print axioms LiWang.Formalization.duhamelIntegral_quadCurve_congr
#print axioms LiWang.Formalization.mild_solution_unique
#print axioms LiWang.Formalization.exists_local_mild_solution_unique
#print axioms LiWang.Formalization.mild_solution_stability
#print axioms LiWang.Formalization.exists_local_well_posed

-- v2.0: reality of the mild solution
#print axioms LiWang.Formalization.coeff_intervalIntegral
#print axioms LiWang.Formalization.conjSymmetric_duhamelIntegral
#print axioms LiWang.Formalization.conjSymmetric_mildMap1
#print axioms LiWang.Formalization.exists_local_mild_solution_real
#print axioms LiWang.Formalization.exists_local_mild_solution_real_rotatedGradient

-- v2.0: the solution as a physical field on the torus
#print axioms LiWang.Formalization.continuous_physField
#print axioms LiWang.Formalization.coeff_physField
#print axioms LiWang.Formalization.exists_local_physical_mild_solution
#print axioms LiWang.Formalization.hasDerivAt_physField
#print axioms LiWang.Formalization.synth_quadCurve_apply
#print axioms LiWang.Formalization.exists_physField_ne_zero
#print axioms LiWang.Formalization.solution_velocity_divFree
#print axioms LiWang.Formalization.exists_concrete_local_physical_solution
#print axioms LiWang.Formalization.exists_affineCurve_fixedPoint
#print axioms LiWang.Formalization.affine_solution_unique
#print axioms LiWang.Formalization.exists_local_mild_solution_forced
#print axioms LiWang.Formalization.forced_mild_solution_unique
#print axioms LiWang.Formalization.exists_local_forced_well_posed
#print axioms LiWang.Formalization.transport_rotatedGradient_dirac
#print axioms LiWang.Formalization.transport_rotatedGradient_ne_zero
#print axioms LiWang.Formalization.transport_finiteKernel_ne_zero
#print axioms LiWang.Formalization.exists_localMildSolutionCertificate
#print axioms LiWang.Formalization.exists_concrete_localMildSolutionCertificate

-- v3.0: the Duhamel operator, the source-to-solution map and its variations
#print axioms LiWang.Formalization.duhamelOp
#print axioms LiWang.Formalization.norm_duhamelOp_le
#print axioms LiWang.Formalization.duhamelOp_eq_of_agrees
#print axioms LiWang.Formalization.norm_sourceQuad_le
#print axioms LiWang.Formalization.sourceSolution
#print axioms LiWang.Formalization.sourceSolution_zero
#print axioms LiWang.Formalization.eventually_sourceSolution_eq
#print axioms LiWang.Formalization.contDiffAt_sourceSolution
#print axioms LiWang.Formalization.fderiv_sourceSolution_zero
#print axioms LiWang.Formalization.exists_mild_curve_of_small
#print axioms LiWang.Formalization.mild_curve_unique_ball
#print axioms LiWang.Formalization.mild_curve_lipschitz
#print axioms LiWang.Formalization.mild_pointwise_of_curve
#print axioms LiWang.Formalization.fderiv_fderiv_sourceSolution_apply'
#print axioms LiWang.Formalization.fderiv_fderiv_sourceSolution_sub
#print axioms LiWang.Formalization.sourceResponseCertificate

-- v3.0: symmetrized non-degeneracy and the cancellation regression
#print axioms LiWang.Formalization.transport_dirac1
#print axioms LiWang.Formalization.transport_rotatedGradient_symmetrized
#print axioms LiWang.Formalization.fderiv_fderiv_quadResidual_finiteKernel_ne_zero
#print axioms LiWang.Formalization.transport_exampleKernel_symmetrized_eq_zero
#print axioms LiWang.Formalization.quadResidual_realPacket_coeff
#print axioms LiWang.Formalization.quadResidual_realPacket_ne_zero
#print axioms LiWang.Formalization.transport_cosMode1_self
#print axioms LiWang.Formalization.fderiv_fderiv_realQuadResidual_realPacket_ne_zero

-- v3.0: the coefficient evolution equation, the weak formulations and the variation ODEs
#print axioms LiWang.Formalization.coeff_duhamelIntegral
#print axioms LiWang.Formalization.hasDerivAt_scalarDuhamel
#print axioms LiWang.Formalization.coeff_mild_eq_scalarDuhamel
#print axioms LiWang.Formalization.hasDerivAt_coeff_of_mild
#print axioms LiWang.Formalization.coeff_evolution_of_mild
#print axioms LiWang.Formalization.coeff_initial_of_mild
#print axioms LiWang.Formalization.curveState_initial_of_mild
#print axioms LiWang.Formalization.integral_test_of_hasDerivAt
#print axioms LiWang.Formalization.weak_coeff_of_mild
#print axioms LiWang.Formalization.weak_coeff_of_mild_contDiff
#print axioms LiWang.Formalization.hasDerivAt_coeff_duhamelOp
#print axioms LiWang.Formalization.weak_coeff_duhamelOp
#print axioms LiWang.Formalization.hasDerivAt_coeff_fderiv_sourceSolution
#print axioms LiWang.Formalization.hasDerivAt_coeff_fderiv_fderiv_sourceSolution
#print axioms LiWang.Formalization.fderiv_fderiv_sourceSolution_eq_duhamelOp
#print axioms LiWang.Formalization.integral_synth_mul_trigPoly
#print axioms LiWang.Formalization.weak_physical_of_mild
#print axioms LiWang.Formalization.weak_physical_fderiv_sourceSolution
#print axioms LiWang.Formalization.weak_physical_fderiv_fderiv_sourceSolution

-- v3.0: integrable torus kernels
#print axioms LiWang.Formalization.kernelCoeff
#print axioms LiWang.Formalization.norm_kernelCoeff_le
#print axioms LiWang.Formalization.kernelCoeff_conjSymmetric
#print axioms LiWang.Formalization.emode_sub_apply
#print axioms LiWang.Formalization.torusConvCLM
#print axioms LiWang.Formalization.torusConv_emode
#print axioms LiWang.Formalization.torusConv_synth
#print axioms LiWang.Formalization.hasDerivAt_torusConv_state
#print axioms LiWang.Formalization.velocity_integrableKernel_zero
#print axioms LiWang.Formalization.velocity_integrableKernel_one
#print axioms LiWang.Formalization.kernelBound_of_decay
#print axioms LiWang.Formalization.isAdmissibleKernel_kernelCoeff_of_decay
#print axioms LiWang.Formalization.div_synth_velocity_symbol_eq_zero
#print axioms LiWang.Formalization.symbolConv_eq_kernelConv
#print axioms LiWang.Formalization.symbolConvDeriv_eq_kernelConvDeriv
#print axioms LiWang.Formalization.absK_le_wt
#print axioms LiWang.Formalization.wt_le_three_absK
#print axioms LiWang.Formalization.fourierMagnitudeBounds_zero
#print axioms LiWang.Formalization.fourierMagnitudeBounds_neg_exampleKernel
#print axioms LiWang.Formalization.neg_exampleKernel_re_neg
#print axioms LiWang.Formalization.not_orderedFourierEllipticity_neg_exampleKernel
#print axioms LiWang.Formalization.orderedFourierEllipticity_exampleKernel
#print axioms LiWang.Formalization.OrderedFourierEllipticity.fourierMagnitudeBounds
#print axioms LiWang.Formalization.finiteKernel_not_orderedFourierEllipticity
#print axioms LiWang.Formalization.finiteKernel_not_fourierMagnitudeBounds

-- v3.0: injectivity of the Duhamel operator and the nonzero second source response
#print axioms LiWang.Formalization.expWindow_pos
#print axioms LiWang.Formalization.eq_zero_of_duhamelOp_eq_zero
#print axioms LiWang.Formalization.curveState_duhamelOp_packetSource
#print axioms LiWang.Formalization.secondVariationSource_packet_ne_zero
#print axioms LiWang.Formalization.fderiv_fderiv_sourceSolution_packet_ne_zero

-- v4.0: the physical L² identification
#print axioms LiWang.Formalization.synth_conjRefl_apply
#print axioms LiWang.Formalization.integral_norm_sq_synth
#print axioms LiWang.Formalization.inner_synthL2
#print axioms LiWang.Formalization.norm_synthL2_sq
#print axioms LiWang.Formalization.orthonormal_synthL2_wdirac
#print axioms LiWang.Formalization.coeffL2
#print axioms LiWang.Formalization.norm_coeffL2
#print axioms LiWang.Formalization.coeffL2_toWiener2

-- v4.0: the L²-in-time estimate, the strong equation and H^{2α}
#print axioms LiWang.Formalization.hasDerivAt_normSq_comp
#print axioms LiWang.Formalization.energy_estimate
#print axioms LiWang.Formalization.fracSymbol_zero_eq
#print axioms LiWang.Formalization.integral_fracSymbol_sq_coeff_duhamelOp_le
#print axioms LiWang.Formalization.tsum_integral_source_sq_le
#print axioms LiWang.Formalization.tsum_integral_fracSymbol_sq_le
#print axioms LiWang.Formalization.integrated_equation
#print axioms LiWang.Formalization.coeff_duhamelOp_integrated
#print axioms LiWang.Formalization.ae_summable_of_summable_integral
#print axioms LiWang.Formalization.ae_summable_fracSymbol_sq
#print axioms LiWang.Formalization.memSobolev_two_alpha
#print axioms LiWang.Formalization.ae_memSobolev_duhamelOp
#print axioms LiWang.Formalization.norm_fracLapRep_sq
#print axioms LiWang.Formalization.strong_equation_integrated
#print axioms LiWang.Formalization.coeff_fracTimeIntegral
#print axioms LiWang.Formalization.mild_curve_eq_duhamelOp
#print axioms LiWang.Formalization.tsum_integral_fracSymbol_sq_mild_le
#print axioms LiWang.Formalization.ae_memSobolev_mild
#print axioms LiWang.Formalization.ae_memSobolev_firstResponse
#print axioms LiWang.Formalization.ae_memSobolev_secondResponse

-- v4.0: localized sources and observations
#print axioms LiWang.Formalization.localizedSources
#print axioms LiWang.Formalization.CompactlySupportedIn.supportedIn
#print axioms LiWang.Formalization.statePhysCLM
#print axioms LiWang.Formalization.statePhysCLM_apply
#print axioms LiWang.Formalization.velocityPhysCLM
#print axioms LiWang.Formalization.norm_velocityPhys_le
#print axioms LiWang.Formalization.exists_bothMildOn
#print axioms LiWang.Formalization.productSource_mem_localizedSources
#print axioms LiWang.Formalization.productSource_compactlySupported
#print axioms LiWang.Formalization.exists_nonzero_compactlySupported_source
#print axioms LiWang.Formalization.exists_nonzero_localizedSource

-- v4.0: local cancellation
#print axioms LiWang.Formalization.synth_fourierDeriv_eq_zero_of_vanishes
#print axioms LiWang.Formalization.synth_transport_congr_on
#print axioms LiWang.Formalization.diff_eq_duhamelOp
#print axioms LiWang.Formalization.coeff_timePrimitive
#print axioms LiWang.Formalization.coeff_fracTimeIntegral_eq
#print axioms LiWang.Formalization.local_cancellation
#print axioms LiWang.Formalization.local_cancellation_window

-- v4.0: the conditional UCP bridge
#print axioms LiWang.Formalization.curve_eq_of_ucp
#print axioms LiWang.Formalization.transport_diff_self_eq_zero
#print axioms LiWang.Formalization.polarization_of_quad_zero
#print axioms LiWang.Formalization.transport_diff_duhamelOp_self_eq_zero
#print axioms LiWang.Formalization.quad_transport_diff_sourceSolution_eq_zero
#print axioms LiWang.Formalization.generated_source_identity
#print axioms LiWang.Formalization.fderiv_fderiv_sourceSolution_eq_on_localized

-- v4.0: the Section 6 output
#print axioms LiWang.Formalization.wpair_eq_integral
#print axioms LiWang.Formalization.wpair_conv_eq_wtriple
#print axioms LiWang.Formalization.wtriple_leibniz
#print axioms LiWang.Formalization.rotatedGradientSymbol_isDivFree
#print axioms LiWang.Formalization.sum_wtriple_divFree
#print axioms LiWang.Formalization.wpair_transport_skew
#print axioms LiWang.Formalization.wpair_symmetrized_transport
#print axioms LiWang.Formalization.tested_symmetrized_eq_zero
#print axioms LiWang.Formalization.section6_spacetime_output
#print axioms LiWang.Formalization.norm_wpair_transport_sub_le
#print axioms LiWang.Formalization.tested_symmetrized_limit

-- v5.0: smooth periodic Fourier theory (smoothness discharges summability)
#print axioms LiWang.Formalization.percoeff_deriv
#print axioms LiWang.Formalization.percoeff_deriv_two
#print axioms LiWang.Formalization.norm_percoeff_le_of_deriv_two
#print axioms LiWang.Formalization.pcoeff_eq_swap
#print axioms LiWang.Formalization.pcoeff_pd0_two
#print axioms LiWang.Formalization.pcoeff_pd1_two
#print axioms LiWang.Formalization.exists_pcoeff_decay
#print axioms LiWang.Formalization.summable_norm_pcoeff
#print axioms LiWang.Formalization.tsum_percoeff_chi
#print axioms LiWang.Formalization.lift_wienerOfSmooth

-- v5.0: actual smooth compactly supported sources
#print axioms LiWang.Formalization.exists_circle_radius
#print axioms LiWang.Formalization.circProfile_center
#print axioms LiWang.Formalization.circProfile_ne_zero_dist
#print axioms LiWang.Formalization.exists_smooth_localized_profile
#print axioms LiWang.Formalization.smoothProfiles
#print axioms LiWang.Formalization.exists_nonzero_smoothProfile
#print axioms LiWang.Formalization.exists_smooth_time_bump
#print axioms LiWang.Formalization.compactlySupportedSources
#print axioms LiWang.Formalization.smoothSources
#print axioms LiWang.Formalization.smoothSources_le_compactlySupported
#print axioms LiWang.Formalization.smoothSources_le_localizedSources
#print axioms LiWang.Formalization.exists_nonzero_smoothSource
#print axioms LiWang.Formalization.smoothSourceCurve_physical
#print axioms LiWang.Formalization.wienerOfSmooth_add
#print axioms LiWang.Formalization.wienerOfSmooth_smul
#print axioms LiWang.Formalization.conjSymmetric_pcoeff

-- v5.0: the corrected measurement quantifiers
#print axioms LiWang.Formalization.exists_bothMildOnSub
#print axioms LiWang.Formalization.MeasuredMapsAgreeOn.mono
#print axioms LiWang.Formalization.quad_transport_diff_sourceSolution_eq_zero_on
#print axioms LiWang.Formalization.generated_source_identity_on
#print axioms LiWang.Formalization.fderiv_fderiv_sourceSolution_eq_on
#print axioms LiWang.Formalization.generated_source_identity_smooth
#print axioms LiWang.Formalization.fderiv_fderiv_sourceSolution_eq_on_smooth
#print axioms LiWang.Formalization.measuredMapsAgreeOn_smooth_of_localized

-- v5.0: the real-carrier primitive interface and the real-only UCP boundary
#print axioms LiWang.Formalization.memSobolev_of_coeff_rel
#print axioms LiWang.Formalization.synthL2_eq_fracLapRep
#print axioms LiWang.Formalization.conjSymmetric_timePrimitive
#print axioms LiWang.Formalization.conjSymmetric_fracTimeIntegral
#print axioms LiWang.Formalization.aeRestrict_synthL2_eq_zero
#print axioms LiWang.Formalization.eq_of_synthL2_eq
#print axioms LiWang.Formalization.wiener1_eq_of_synthL2_incl_eq
#print axioms LiWang.Formalization.realFractionalGraph_of_pointwise
#print axioms LiWang.Formalization.realFractionalGraph_timePrimitive
#print axioms LiWang.Formalization.fractionalUCP_of_real
#print axioms LiWang.Formalization.curve_eq_of_realUCP
#print axioms LiWang.Formalization.fracTimeIntegral_is_frac_of_primitive

-- v5.0: two-state continuity with a fixed test
#print axioms LiWang.Formalization.velocityW2
#print axioms LiWang.Formalization.norm_velocityW2_le
#print axioms LiWang.Formalization.coeffL2_velocityW2
#print axioms LiWang.Formalization.norm_synthL2_velocity_le
#print axioms LiWang.Formalization.norm_integral_triple_le
#print axioms LiWang.Formalization.norm_sideInteraction_le
#print axioms LiWang.Formalization.sideInteractionCLM
#print axioms LiWang.Formalization.norm_sideInteraction_sub_le
#print axioms LiWang.Formalization.norm_testedInteraction_sub_le
#print axioms LiWang.Formalization.sideInteraction_eq_wpair
#print axioms LiWang.Formalization.testedInteraction_eq_zero_of_generated
#print axioms LiWang.Formalization.IsExteriorTest.deriv_vanishes
#print axioms LiWang.Formalization.sideInteraction_eq_exterior
#print axioms LiWang.Formalization.continuous_testedInteractionTime
#print axioms LiWang.Formalization.spacetimeTestedInteraction_eq_iterated
#print axioms LiWang.Formalization.spacetimeTestedInteraction_eq_zero

-- v5.0: the isolated nonlocal state-approximation step
#print axioms LiWang.Formalization.norm_setIntegral_mul_le
#print axioms LiWang.Formalization.norm_setIntegral_triple_le
#print axioms LiWang.Formalization.extL2sq_le_global
#print axioms LiWang.Formalization.norm_sideInteraction_exterior_le
#print axioms LiWang.Formalization.tendsto_sideInteraction_exterior
#print axioms LiWang.Formalization.tested_symmetrized_state_limit
#print axioms LiWang.Formalization.extL2sq_eq_zero_of_tendsto_physicalL2
#print axioms LiWang.Formalization.ae_eq_zero_of_tendsto_physicalL2
#print axioms LiWang.Formalization.disjoint_measured_exterior
#print axioms LiWang.Formalization.tested_interaction_target_eq_zero
#print axioms LiWang.Formalization.testedInteraction_generated_smooth_eq_zero
#print axioms LiWang.Formalization.spacetimeTestedInteraction_generated_smooth_eq_zero



-- v5.0: smooth profiles are first-order states; the proved nonlocality obstruction
#print axioms LiWang.Formalization.pcoeff_pd0_four
#print axioms LiWang.Formalization.pcoeff_pd1_four
#print axioms LiWang.Formalization.exists_pcoeff_decay4
#print axioms LiWang.Formalization.summable_wt_norm_pcoeff
#print axioms LiWang.Formalization.wiener1OfSmooth
#print axioms LiWang.Formalization.incl_wiener1OfSmooth
#print axioms LiWang.Formalization.exists_smooth_localized_profile1
#print axioms LiWang.Formalization.sqrt_extL2sq_eq_norm_restL2
#print axioms LiWang.Formalization.sqrt_extL2sq_add_le
#print axioms LiWang.Formalization.ExteriorStateConvergence.of_state_velocity
#print axioms LiWang.Formalization.exists_exteriorStateConvergence_terminal
#print axioms LiWang.Formalization.velocity_modeSymbol
#print axioms LiWang.Formalization.exists_exterior_nonlocality
#print axioms LiWang.Formalization.extL2sq_velocity_modeSymbol
#print axioms LiWang.Formalization.exists_state_conv_without_velocity_conv
#print axioms LiWang.Formalization.setIntegral_source_region_eq_zero
#print axioms LiWang.Formalization.sideInteraction_congr_exterior
#print axioms LiWang.Formalization.generatedExteriorApproximation_of_global


-- v5.0: recovery on open regions, the exterior energy budget, and the source-side reduction
#print axioms LiWang.Formalization.eq_zero_on_of_aeRestrict
#print axioms LiWang.Formalization.realFractionalUCP_iff_fractionalUCP
#print axioms LiWang.Formalization.extL2sq_univ
#print axioms LiWang.Formalization.extL2sq_add_compl
#print axioms LiWang.Formalization.extL2sq_closure_split
#print axioms LiWang.Formalization.extL2sq_exterior_of_vanishes_on
#print axioms LiWang.Formalization.norm_synthL2_incl_curveState_le
#print axioms LiWang.Formalization.generatedExteriorApproximation_of_source_tendsto

-- v6.0: prescribed-interval bumps, test separation, terminal control, exterior convergence
#print axioms LiWang.Formalization.synth_eq_zero_on_closure
#print axioms LiWang.Formalization.extL2sq_boundary_strip_eq_zero
#print axioms LiWang.Formalization.exists_smooth_bump_at
#print axioms LiWang.Formalization.exists_smooth_time_bump_on
#print axioms LiWang.Formalization.eq_zero_of_forall_time_bump
#print axioms LiWang.Formalization.eq_zero_on_of_forall_smoothProfile
#print axioms LiWang.Formalization.exists_smoothSpacetimeRep
#print axioms LiWang.Formalization.summable_gam_wt_frac_heat
#print axioms LiWang.Formalization.hasDerivAt_heatField
#print axioms LiWang.Formalization.eq_zero_of_heatPair_vanishes
#print axioms LiWang.Formalization.pairY_terminal_productSource
#print axioms LiWang.Formalization.eq_zero_of_orthogonal_terminal
#print axioms LiWang.Formalization.mem_closure_of_orthogonal_trivial
#print axioms LiWang.Formalization.exists_smoothSourcesBefore_terminal_tendsto
#print axioms LiWang.Formalization.smoothSourcesBefore_timeSupport
#print axioms LiWang.Formalization.exists_smoothSources_terminal_tendsto
#print axioms LiWang.Formalization.fractionalUCP_univ
#print axioms LiWang.Formalization.not_fractionalUCP_empty
#print axioms LiWang.Formalization.exists_nonzero_smoothSource_norm_lt
#print axioms LiWang.Formalization.norm_synthL2_incl_eq_zero_iff
#print axioms LiWang.Formalization.exists_nonzero_realWiener1
#print axioms LiWang.Formalization.exists_nonzero_smoothSourceBefore
#print axioms LiWang.Formalization.not_tendsto_zero_control
#print axioms LiWang.Formalization.exists_terminal_tendsto_univ
#print axioms LiWang.Formalization.unconditional_nontrivial_approximation
#print axioms LiWang.Formalization.rotatedGradientSymbol_congr_of_ne_zero
#print axioms LiWang.Formalization.measurement_cannot_see_zero_mode
#print axioms LiWang.Formalization.exteriorTest_eq_zero_of_dense
#print axioms LiWang.Formalization.terminal_zero_time
#print axioms LiWang.Formalization.exists_exteriorStateConvergence_terminal
#print axioms LiWang.Formalization.generatedExteriorApproximation_terminal
#print axioms LiWang.Formalization.tested_interaction_real_targets

-- v6.0: the kernel-side consequences
#print axioms LiWang.Formalization.testedInteraction_eq_zero_of_real_states
#print axioms LiWang.Formalization.testedInteraction_dirac1
#print axioms LiWang.Formalization.exists_exteriorTest_ne_zero
#print axioms LiWang.Formalization.symbol_mode_identity
#print axioms LiWang.Formalization.kernel_reflection_identity
#print axioms LiWang.Formalization.isExteriorTest_shift1
#print axioms LiWang.Formalization.exists_exteriorTest_coeff_ne_zero
#print axioms LiWang.Formalization.symbol_mode_identity_all
#print axioms LiWang.Formalization.kernel_fourier_eq
#print axioms LiWang.Formalization.kernel_diff_eq_zero
#print axioms LiWang.Formalization.rotatedGradientSymbol_eq_of_measured
#print axioms LiWang.Formalization.exists_open_nonempty_with_exterior
#print axioms LiWang.Formalization.measuredMapsAgreeOn_of_symbol_eq
#print axioms LiWang.Formalization.measuredMapsAgreeOn_iff
#print axioms LiWang.Formalization.finiteKernel_vs_zero_measured_differ
#print axioms LiWang.Formalization.orderedEllipticity_symbol
#print axioms LiWang.Formalization.kernel_determined_of_wiener1
#print axioms LiWang.Formalization.velocity_determined_of_wiener1
#print axioms LiWang.Formalization.kernel_determined_of_orderedEllipticity


-- v7.0: the physical PDE bridge
#print axioms LiWang.Formalization.aestronglyMeasurable_fracFieldW2
#print axioms LiWang.Formalization.lintegral_norm_sq_fracFieldW2_le
#print axioms LiWang.Formalization.integrableOn_fracFieldW2
#print axioms LiWang.Formalization.fracFieldW2_apply
#print axioms LiWang.Formalization.physFracField_eq_fracLapRep
#print axioms LiWang.Formalization.w2_fracTimeIntegral
#print axioms LiWang.Formalization.synthL2_fracTimeIntegral
#print axioms LiWang.Formalization.phys_duhamel_integrated
#print axioms LiWang.Formalization.physical_pde_integrated
#print axioms LiWang.Formalization.physState_initial_of_mild
#print axioms LiWang.Formalization.physState_eq_integral_physRHS
#print axioms LiWang.Formalization.physState_sub_eq_integral
#print axioms LiWang.Formalization.norm_physState_sub_le
#print axioms LiWang.Formalization.ae_hasDerivAt_pairing_physState
#print axioms LiWang.Formalization.physTransport_apply_ae
#print axioms LiWang.Formalization.torusMean_synthL2
#print axioms LiWang.Formalization.transport_rotatedGradient_zero_mode
#print axioms LiWang.Formalization.coeff_zero_duhamelOp
#print axioms LiWang.Formalization.coeff_zero_balance_of_mild
#print axioms LiWang.Formalization.mean_balance_physical
#print axioms LiWang.Formalization.norm_duhamelIntegral_le_of_vanishing
#print axioms LiWang.Formalization.exists_absorption_window
#print axioms LiWang.Formalization.mild_curve_unique
#print axioms LiWang.Formalization.integrated_equation_converse
#print axioms LiWang.Formalization.isPhysicalSolution_of_mild
#print axioms LiWang.Formalization.mild_of_isPhysicalSolution
#print axioms LiWang.Formalization.physical_solution_unique
#print axioms LiWang.Formalization.eq_of_isPhysicalSolution
#print axioms LiWang.Formalization.energy_of_isPhysicalSolution
#print axioms LiWang.Formalization.norm_physState_le
#print axioms LiWang.Formalization.curveState_zero_of_weak
#print axioms LiWang.Formalization.ae_memSobolev_of_isPhysicalSolution
#print axioms LiWang.Formalization.physicalObs_state_eq
#print axioms LiWang.Formalization.physicalObs_velocity_eq
#print axioms LiWang.Formalization.exists_measuredMapsAgreeOn_of_physical
#print axioms LiWang.Formalization.exists_physicalObsAgreeOn_of_measured
#print axioms LiWang.Formalization.exists_physicalObsAgreeOn_iff_measured
#print axioms LiWang.Formalization.rotatedGradientSymbol_eq_of_physical
#print axioms LiWang.Formalization.kernel_determined_of_wiener1_physical
#print axioms LiWang.Formalization.kernel_determined_of_orderedEllipticity_physical
#print axioms LiWang.Formalization.paper_exterior_velocity_eq
#print axioms LiWang.Formalization.paper_exterior_velocity_eq_wiener1
#print axioms LiWang.Formalization.test_fourier_normalization
#print axioms LiWang.Formalization.velocity_eq_physical_rotatedGradient

-- v8.0: Sobolev compatibility
#print axioms LiWang.Formalization.l2coeff_synthL2
#print axioms LiWang.Formalization.torusL2_ext_of_forall_l2coeff
#print axioms LiWang.Formalization.synthL2_incl_eq_of_coeff
#print axioms LiWang.Formalization.summable_wtsq_div_rho3
#print axioms LiWang.Formalization.summable_wt_mul_norm
#print axioms LiWang.Formalization.synthL2_sobToWiener1
#print axioms LiWang.Formalization.continuous_sobToWiener1_curve
#print axioms LiWang.Formalization.forall_le_of_ae_le
#print axioms LiWang.Formalization.forall_finset_sum_le_of_ae
#print axioms LiWang.Formalization.sobClamp_of_mem
#print axioms LiWang.Formalization.bound_sobClamp_of_ae
#print axioms LiWang.Formalization.isSobolevSolution_sobClamp
#print axioms LiWang.Formalization.synthL2_curveState_sobClamp
#print axioms LiWang.Formalization.exists_nonzero_smoothSource_sobolevSolution
#print axioms LiWang.Formalization.synthL2_sobCurve
#print axioms LiWang.Formalization.IsSobolevSolution.synthL2_curveState
#print axioms LiWang.Formalization.IsSobolevSolution.curveState_initial
#print axioms LiWang.Formalization.IsSobolevSolution.isPhysicalSolution_curve
#print axioms LiWang.Formalization.IsSobolevSolution.mild_curve
#print axioms LiWang.Formalization.IsSobolevSolution.mean_balance
#print axioms LiWang.Formalization.sobolev_solution_unique
#print axioms LiWang.Formalization.forall_eq_of_ae_eq_open
#print axioms LiWang.Formalization.forall_eq_of_ae_eq_time
#print axioms LiWang.Formalization.IsSobolevSolution.obsState_ae
#print axioms LiWang.Formalization.IsSobolevSolution.continuous_obsState
#print axioms LiWang.Formalization.IsSobolevSolution.obsVel_integrableKernel
#print axioms LiWang.Formalization.exists_measuredMapsAgreeOn_of_sobolev
#print axioms LiWang.Formalization.rotatedGradientSymbol_eq_of_sobolev
#print axioms LiWang.Formalization.paper_exterior_velocity_eq_sobolev
#print axioms LiWang.Formalization.WB.conv_tame
#print axioms LiWang.Formalization.WB_duhamel
#print axioms LiWang.Formalization.sobBound_of_WB3
#print axioms LiWang.Formalization.WB_picard_uniform
#print axioms LiWang.Formalization.WB_mild_of_picard
#print axioms LiWang.Formalization.WB3_of_mild
#print axioms LiWang.Formalization.isSobolevSolution_mild
#print axioms LiWang.Formalization.exists_sobolevExistence_of_higherBound
#print axioms LiWang.Formalization.meanSolution_mild
#print axioms LiWang.Formalization.isSobolevSolution_meanSolution
#print axioms LiWang.Formalization.meanSolution_terminal_mean_ne_zero
#print axioms LiWang.Formalization.weighted_sq_decayWeight4_le
#print axioms LiWang.Formalization.summable_wtsq_norm_of_smoothWiener
#print axioms LiWang.Formalization.hasHigherBound_of_mem_smoothSources
#print axioms LiWang.Formalization.exists_sobolevExistence_smoothSources
#print axioms LiWang.Formalization.paper_exterior_velocity_eq_sobolev_smooth

-- v9.0: exact paper-map alignment
#print axioms LiWang.Formalization.summable_wt_cube_norm_pcoeff
#print axioms LiWang.Formalization.summable_wt3_norm_of_smoothWiener
#print axioms LiWang.Formalization.hasHigherBound3_of_mem_smoothSources
#print axioms LiWang.Formalization.sobBound_of_WB
#print axioms LiWang.Formalization.sobWeight_le_rho_pow
#print axioms LiWang.Formalization.memSobolev_of_WB4
#print axioms LiWang.Formalization.sobEnergy_le_of_WB4
#print axioms LiWang.Formalization.measurable_sobEnergy
#print axioms LiWang.Formalization.lintegral_sobEnergy_le
#print axioms LiWang.Formalization.integrableOn_sobEnergy
#print axioms LiWang.Formalization.inv_paperExp_lt
#print axioms LiWang.Formalization.eLpNorm_synthL2_le
#print axioms LiWang.Formalization.memLp_synthL2
#print axioms LiWang.Formalization.WB4_of_mild
#print axioms LiWang.Formalization.paperState_of_mem
#print axioms LiWang.Formalization.isPaperSolution_mild
#print axioms LiWang.Formalization.IsPaperSolution.isSobolevSolution
#print axioms LiWang.Formalization.IsPaperSolution.synthL2_curveState
#print axioms LiWang.Formalization.IsPaperSolution.unique
#print axioms LiWang.Formalization.IsPaperSolution.mean_balance
#print axioms LiWang.Formalization.paperSol_eq
#print axioms LiWang.Formalization.paperObsVel_eq
#print axioms LiWang.Formalization.paperObsVel_ae
#print axioms LiWang.Formalization.curveState_congr
#print axioms LiWang.Formalization.sobolevObsAgreeOn_of_paperMapsAgree
#print axioms LiWang.Formalization.exists_paperExistence_of_higherBound3
#print axioms LiWang.Formalization.exists_paperExistence_smoothSources
#print axioms LiWang.Formalization.isPaperSource_of_mem_smoothSources
#print axioms LiWang.Formalization.sourcePhys_eq_of_isPaperSource
#print axioms LiWang.Formalization.paperObsState_ae_packet
#print axioms LiWang.Formalization.paperObsVel_ae_packet
#print axioms LiWang.Formalization.incl_exteriorProfile
#print axioms LiWang.Formalization.synth_exteriorProfile
#print axioms LiWang.Formalization.exteriorProfile_vanishes
#print axioms LiWang.Formalization.paper_exterior_velocity_eq_of_paperMapsAgree
#print axioms LiWang.Formalization.paper_exterior_velocity_eq_of_paperMapsAgree_elliptic
#print axioms LiWang.Formalization.coeff_exteriorProfile
#print axioms LiWang.Formalization.aemeasurable_sobEnergy_of_continuousOn
#print axioms LiWang.Formalization.IsPaperSolution.aemeasurable_energy
#print axioms LiWang.Formalization.IsPaperSolution.exp_admissible
#print axioms LiWang.Formalization.exists_sobolevObsAgreeOn_of_paperMapsAgree
#print axioms LiWang.Formalization.exists_nonzero_smoothSource_paperSolution
#print axioms LiWang.Formalization.HasHigherBound3.toHasHigherBound
#print axioms LiWang.Formalization.summable_rho_pow_of_WB
#print axioms LiWang.Formalization.four_lt_paperExp

-- v10.0: the paper's source class, realized
#print axioms LiWang.Formalization.forall_le_of_ae_le_on
#print axioms LiWang.Formalization.forall_finset_sum_le_of_ae_on
#print axioms LiWang.Formalization.isPaperSolution_of_ae
#print axioms LiWang.Formalization.coeff_continuousOn_of_continuousOn
#print axioms LiWang.Formalization.IsPaperSolution.continuousOn'
#print axioms LiWang.Formalization.slice_spd0
#print axioms LiWang.Formalization.slice_spd1
#print axioms LiWang.Formalization.contDiff_spd0
#print axioms LiWang.Formalization.exists_uniform_box_bound
#print axioms LiWang.Formalization.pcoeff_decay4_of_bounds
#print axioms LiWang.Formalization.exists_uniform_pcoeff_decay4
#print axioms LiWang.Formalization.continuous_pcoeff_slice
#print axioms LiWang.Formalization.continuous_wienerSlice
#print axioms LiWang.Formalization.paperCurve
#print axioms LiWang.Formalization.sourceFun_paperCurve
#print axioms LiWang.Formalization.sourcePhys_paperCurve
#print axioms LiWang.Formalization.smoothSpacetimeRep_paperCurve
#print axioms LiWang.Formalization.isPaperSource_paperCurve
#print axioms LiWang.Formalization.isPaperSource_iff_exists_paperField
#print axioms LiWang.Formalization.exists_uniform_wt_bound
#print axioms LiWang.Formalization.exists_uniform_WB3
#print axioms LiWang.Formalization.sourceFun_eq_of_rep
#print axioms LiWang.Formalization.hasHigherBound3_of_isPaperSource
#print axioms LiWang.Formalization.smoothSources_le_paperSources
#print axioms LiWang.Formalization.paperCurve_mem_paperSources
#print axioms LiWang.Formalization.exists_paperExistence_paperSources
#print axioms LiWang.Formalization.paperObsMapsAgree_mono
#print axioms LiWang.Formalization.exists_paperExistence_pair
#print axioms LiWang.Formalization.paper_exterior_velocity_eq_of_paperMapsAgree_full
#print axioms LiWang.Formalization.exists_radius_paper_endpoint

-- v11.0: continuity-free solutions and physical exterior tests
#print axioms LiWang.Formalization.l2TrigPair_mode
#print axioms LiWang.Formalization.IsPaperEnergySolution.coeff_continuousOn
#print axioms LiWang.Formalization.IsPaperEnergySolution.energy3_everywhere
#print axioms LiWang.Formalization.IsPaperEnergySolution.toPaperSolution
#print axioms LiWang.Formalization.IsPaperEnergySolution.continuousOn
#print axioms LiWang.Formalization.IsPaperSolution.toPaperEnergySolution
#print axioms LiWang.Formalization.isPaperEnergySolution_iff_isPaperSolution
#print axioms LiWang.Formalization.isPaperEnergySolution_mild
#print axioms LiWang.Formalization.paperExteriorTorusField_torusProj
#print axioms LiWang.Formalization.paperExteriorTorusField_zero_on_closure
#print axioms LiWang.Formalization.exists_paperExteriorField_at
#print axioms LiWang.Formalization.exists_nonzero_paperExteriorField
#print axioms LiWang.Formalization.paper_exact_endpoint_from_energy_maps
#print axioms LiWang.Formalization.exists_radius_paper_exact_endpoint

/-! ### 11. Whole-namespace audit

Covers **every** non-internal declaration of `LiWang.Formalization` and rejects, with a hard
error that fails this file:

* any axiom outside `[propext, Classical.choice, Quot.sound]` — in particular `sorryAx`
  (from `sorry`/`admit`) and `Lean.ofReduceBool`/`Lean.trustCompiler` (from `native_decide`);
* `unsafe` and `partial` declarations;
* `@[extern]` and `@[implemented_by]` compiler shortcuts;
* any declaration left in the bare `LiWang` namespace outside `LiWang.Formalization`
  (namespace-collision hygiene for platform integration).
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let root : Name := `LiWang
  let ns : Name := `LiWang.Formalization
  let mut bad : Array (Name × Array Name) := #[]
  let mut unsafeDecls : Array Name := #[]
  let mut partialDecls : Array Name := #[]
  let mut shortcutDecls : Array Name := #[]
  let mut strayDecls : Array Name := #[]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if root.isPrefixOf n && !n.isInternal then
      if !ns.isPrefixOf n then
        strayDecls := strayDecls.push n
    if ns.isPrefixOf n && !n.isInternal then
      count := count + 1
      if ci.isUnsafe then unsafeDecls := unsafeDecls.push n
      match ci with
      | .defnInfo v => if v.safety == DefinitionSafety.partial then
                         partialDecls := partialDecls.push n
      | _ => pure ()
      if Lean.isExtern env n then shortcutDecls := shortcutDecls.push n
      if (Lean.Compiler.getImplementedBy? env n).isSome then
        shortcutDecls := shortcutDecls.push n
      let ax ← Lean.collectAxioms n
      let extra := ax.filter (fun a => !(allowed.contains a))
      if !extra.isEmpty then bad := bad.push (n, extra)
  logInfo m!"scanned {count} non-internal declarations in namespace `LiWang.Formalization`"
  if strayDecls.isEmpty then
    logInfo "no declarations left in the bare `LiWang` namespace outside `LiWang.Formalization`"
  else throwError "stray top-level `LiWang` declarations: {strayDecls}"
  if unsafeDecls.isEmpty then logInfo "no `unsafe` declarations"
    else throwError "unsafe declarations: {unsafeDecls}"
  if partialDecls.isEmpty then logInfo "no `partial` declarations"
    else throwError "partial declarations: {partialDecls}"
  if shortcutDecls.isEmpty then logInfo "no `@[extern]`/`@[implemented_by]` shortcuts"
    else throwError "compiler shortcuts: {shortcutDecls}"
  if bad.isEmpty then
    logInfo "OK: every declaration depends only on [propext, Classical.choice, Quot.sound]"
  else throwError "declarations with unexpected axioms: {bad}"
