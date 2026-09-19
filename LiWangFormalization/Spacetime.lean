/-
# The spacetime lift

Continuous curves of real Fourier states on the compact time interval `[0,T]`, with the
transport form and the quadratic residual lifted pointwise in time.

Curves are modelled as `TimeI T →ᵇ E`, bounded continuous maps.  On the compact interval
`[0,T]` this is the same thing as `C(TimeI T, E)` — Mathlib provides the isometric
equivalence `ContinuousMap.equivBoundedOfCompact` — but the bounded-continuous model carries
the metric uniformity, which is what the operator-norm machinery needs on iterated spaces of
continuous linear maps.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.Certificate
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open BoundedContinuousFunction

namespace LiWang.Formalization

/-- The compact time interval `[0,T]`. -/
abbrev TimeI (T : ℝ) : Type := Set.Icc (0 : ℝ) T

/-- Continuous curves of real first-order Fourier states. -/
abbrev Curve1 (T : ℝ) : Type := TimeI T →ᵇ RealWiener1

/-- Continuous curves of real Fourier states. -/
abbrev Curve0 (T : ℝ) : Type := TimeI T →ᵇ RealWiener

variable {T : ℝ}

example : CompactSpace (TimeI T) := inferInstance
example : CompleteSpace (Curve0 T) := inferInstance

/-- Continuous curves may be built from continuous maps on the compact interval. -/
noncomputable def curveOfContinuous (f : TimeI T → RealWiener1) (hf : Continuous f) :
    Curve1 T := mkOfCompact ⟨f, hf⟩

@[simp] theorem curveOfContinuous_apply (f : TimeI T → RealWiener1) (hf : Continuous f)
    (t : TimeI T) : curveOfContinuous f hf t = f t := rfl

/-! ## The spacetime transport form -/

theorem continuous_realTransport_curve {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (U V : Curve1 T) :
    Continuous fun t : TimeI T => realTransport m hm hr (U t) (V t) := by
  have hc : Continuous fun t : TimeI T => realTransport m hm hr (U t) :=
    (realTransport m hm hr).continuous.comp U.continuous
  exact hc.clm_apply V.continuous

/-- The spacetime transport form as a real bilinear map on curves. -/
noncomputable def spacetimeTransportLm (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : Curve1 T →ₗ[ℝ] Curve1 T →ₗ[ℝ] Curve0 T :=
  LinearMap.mk₂ ℝ
    (fun U V => mkOfCompact ⟨fun t => realTransport m hm hr (U t) (V t),
      continuous_realTransport_curve hm hr U V⟩)
    (fun U₁ U₂ V => by
      ext t
      show realTransport m hm hr ((U₁ + U₂) t) (V t)
          = realTransport m hm hr (U₁ t) (V t) + realTransport m hm hr (U₂ t) (V t)
      rw [BoundedContinuousFunction.add_apply, map_add, ContinuousLinearMap.add_apply])
    (fun r U V => by
      ext t
      show realTransport m hm hr ((r • U) t) (V t) = r • realTransport m hm hr (U t) (V t)
      rw [BoundedContinuousFunction.smul_apply, map_smul, ContinuousLinearMap.smul_apply])
    (fun U V₁ V₂ => by
      ext t
      show realTransport m hm hr (U t) ((V₁ + V₂) t)
          = realTransport m hm hr (U t) (V₁ t) + realTransport m hm hr (U t) (V₂ t)
      rw [BoundedContinuousFunction.add_apply, map_add])
    (fun r U V => by
      ext t
      show realTransport m hm hr (U t) ((r • V) t) = r • realTransport m hm hr (U t) (V t)
      rw [BoundedContinuousFunction.smul_apply, map_smul])

@[simp] theorem spacetimeTransportLm_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (U V : Curve1 T) (t : TimeI T) :
    spacetimeTransportLm m hm hr U V t = realTransport m hm hr (U t) (V t) := rfl

theorem norm_spacetimeTransportLm_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (U V : Curve1 T) :
    ‖(spacetimeTransportLm m hm hr U V : Curve0 T)‖ ≤ 4 * Real.pi * C * ‖U‖ * ‖V‖ := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_
  have h1 : ‖U t‖ ≤ ‖U‖ := U.norm_coe_le_norm t
  have h2 : ‖V t‖ ≤ ‖V‖ := V.norm_coe_le_norm t
  have hpos : (0:ℝ) ≤ 4 * Real.pi * C := by positivity
  calc ‖(spacetimeTransportLm m hm hr U V : Curve0 T) t‖
      = ‖realTransport m hm hr (U t) (V t)‖ := rfl
    _ ≤ 4 * Real.pi * C * ‖U t‖ * ‖V t‖ := norm_realTransport_apply_le hm hr hC _ _
    _ ≤ 4 * Real.pi * C * ‖U‖ * ‖V‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hpos) h2 (norm_nonneg _) (by positivity)

/-- **The spacetime transport form** on continuous curves of real Fourier states. -/
noncomputable def spacetimeTransport (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T :=
  LinearMap.mkContinuousOfExistsBound₂ (spacetimeTransportLm m hm hr)
    ⟨4 * Real.pi * Classical.choose hm, fun U V =>
      norm_spacetimeTransportLm_le hm hr (Classical.choose_spec hm) U V⟩

@[simp] theorem spacetimeTransport_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (U V : Curve1 T) (t : TimeI T) :
    spacetimeTransport m hm hr U V t = realTransport m hm hr (U t) (V t) := rfl

/-- **The spacetime norm estimate.** -/
theorem norm_spacetimeTransport_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) :
    ‖(spacetimeTransport m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T)‖
      ≤ 4 * Real.pi * C := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) (fun U V => ?_)
  exact norm_spacetimeTransportLm_le hm hr hC U V

theorem spacetimeTransport_sub {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₁ : IsRealSymbol m₁) (hr₂ : IsRealSymbol m₂) :
    (spacetimeTransport m₁ hm₁ hr₁ : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T)
        - spacetimeTransport m₂ hm₂ hr₂
      = spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) := by
  refine ContinuousLinearMap.ext fun U => ContinuousLinearMap.ext fun V => ?_
  ext t
  show realTransport m₁ hm₁ hr₁ (U t) (V t) - realTransport m₂ hm₂ hr₂ (U t) (V t)
      = realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) (U t) (V t)
  rw [← realTransport_sub hm₁ hm₂ hr₁ hr₂, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply]

/-! ## The spacetime quadratic residual -/

/-- **The spacetime quadratic residual** `Q(U)(t) = N(U(t), U(t))`. -/
noncomputable def spacetimeQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : Curve1 T → Curve0 T := quad (spacetimeTransport m hm hr)

/-- **The spacetime residual is the real residual at every time.** -/
theorem spacetimeQuadResidual_time (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (U : Curve1 T) (t : TimeI T) :
    (spacetimeQuadResidual m hm hr U) t = realQuadResidual m hm hr (U t) := rfl

theorem spacetimeQuadResidual_val (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (U : Curve1 T) (t : TimeI T) :
    ((spacetimeQuadResidual m hm hr U) t).val = quadResidual m hm (U t).val := rfl

/-- **Physical synthesis commutes with the spacetime residual at every time**: at each time
`t` and each point `x` of the torus the synthesized spacetime residual is the Euclidean dot
product `R_m(u(t))(x) · ∇u(t)(x)`. -/
theorem synth_spacetimeQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (U : Curve1 T) (t : TimeI T) (x : Torus2) :
    ((realSynth ((spacetimeQuadResidual m hm hr U) t) x : ℝ) : ℂ)
      = ∑ j : Fin 2, synth (velocity m hm j (incl (U t).val)) x
          * synth (fourierDeriv j (U t).val) x := by
  rw [ofReal_realSynth, spacetimeQuadResidual_val]
  exact synth_transport_apply m hm (U t).val (U t).val x

theorem spacetimeQuadResidual_zero (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    spacetimeQuadResidual m hm hr (0 : Curve1 T) = 0 := quad_zero _

/-- **The first spacetime derivative at zero vanishes.** -/
theorem fderiv_spacetimeQuadResidual_zero (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    fderiv ℝ (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T) 0 = 0 := fderiv_quad_zero _

theorem contDiff_spacetimeQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (n : WithTop ℕ∞) :
    ContDiff ℝ n (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T) := contDiff_quad _ n

theorem contDiff_two_spacetimeQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    ContDiff ℝ 2 (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T) := contDiff_quad _ 2

/-- **Analyticity of the spacetime residual**, as a genuine `AnalyticOnNhd` statement. -/
theorem analyticOnNhd_spacetimeQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (s : Set (Curve1 T)) :
    AnalyticOnNhd ℝ (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T) s :=
  analyticOnNhd_quad _ s

/-- **The exact spacetime mixed second derivative.** -/
theorem fderiv_fderiv_spacetimeQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (H₁ H₂ : Curve1 T) :
    fderiv ℝ (fderiv ℝ (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T)) 0 H₁ H₂
      = spacetimeTransport m hm hr H₁ H₂ + spacetimeTransport m hm hr H₂ H₁ := by
  have hq : (spacetimeQuadResidual m hm hr : Curve1 T → Curve0 T)
      = quad (spacetimeTransport m hm hr) := rfl
  rw [hq, fderiv_fderiv_quad]
  simp

/-- **The spacetime two-symbol polarization identity.** -/
theorem spacetimeLiWangPolarization {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₁ : IsRealSymbol m₁) (hr₂ : IsRealSymbol m₂)
    (G₁ G₂ : Curve1 T) :
    fderiv ℝ (fderiv ℝ (fun X : Curve1 T =>
        spacetimeQuadResidual m₁ hm₁ hr₁ X - spacetimeQuadResidual m₂ hm₂ hr₂ X)) 0 G₁ G₂
      = spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) G₁ G₂
        + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) G₂ G₁ := by
  have hfun : (fun X : Curve1 T =>
        spacetimeQuadResidual m₁ hm₁ hr₁ X - spacetimeQuadResidual m₂ hm₂ hr₂ X)
      = quad (spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)) := by
    funext X
    rw [← spacetimeTransport_sub hm₁ hm₂ hr₁ hr₂]
    rfl
  rw [hfun, fderiv_fderiv_quad]
  simp

/-- **The spacetime two-kernel polarization identity.** -/
theorem spacetimeKernelPolarization {κ₁ κ₂ : Gam → ℂ} (hb₁ : IsAdmissibleKernel κ₁)
    (hb₂ : IsAdmissibleKernel κ₂) (hc₁ : ConjSymmetric κ₁) (hc₂ : ConjSymmetric κ₂)
    (G₁ G₂ : Curve1 T) :
    fderiv ℝ (fderiv ℝ (fun X : Curve1 T =>
        spacetimeQuadResidual (rotatedGradientSymbol κ₁) (rotatedGradientSymbol_bdd hb₁)
            (rotatedGradientSymbol_isRealSymbol hc₁) X
          - spacetimeQuadResidual (rotatedGradientSymbol κ₂) (rotatedGradientSymbol_bdd hb₂)
            (rotatedGradientSymbol_isRealSymbol hc₂) X)) 0 G₁ G₂
      = spacetimeTransport (rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂)
          ((rotatedGradientSymbol_bdd hb₁).sub (rotatedGradientSymbol_bdd hb₂))
          ((rotatedGradientSymbol_isRealSymbol hc₁).sub
            (rotatedGradientSymbol_isRealSymbol hc₂)) G₁ G₂
        + spacetimeTransport (rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂)
          ((rotatedGradientSymbol_bdd hb₁).sub (rotatedGradientSymbol_bdd hb₂))
          ((rotatedGradientSymbol_isRealSymbol hc₁).sub
            (rotatedGradientSymbol_isRealSymbol hc₂)) G₂ G₁ :=
  spacetimeLiWangPolarization _ _ _ _ G₁ G₂

end LiWang.Formalization
