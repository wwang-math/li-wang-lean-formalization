/-
Velocity symbols, bounded Fourier multipliers, the transport form
`N_m(u,v) = ∑ⱼ (R_m u)ⱼ ⋆ ∂ⱼ v`, the quadratic residual `Q_m(u) = N_m(u,u)`, its Fréchet
derivatives, analyticity, and the Li–Wang polarization identity.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import LiWangFormalization.FirstOrder
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.Formalization

/-! ## 4. Velocity symbols and Fourier multipliers -/

/-- A velocity symbol `m : Fin 2 → Γ → ℂ` is *admissible* if it is uniformly bounded. -/
def IsBddSymbol (m : Fin 2 → Gam → ℂ) : Prop := ∃ C : ℝ, ∀ j k, ‖m j k‖ ≤ C

theorem IsBddSymbol.component {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2) :
    ∃ C : ℝ, ∀ k, ‖m j k‖ ≤ C := by
  obtain ⟨C, hC⟩ := hm; exact ⟨C, fun k => hC j k⟩

theorem IsBddSymbol.sub {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsBddSymbol m₁) (h₂ : IsBddSymbol m₂) :
    IsBddSymbol (m₁ - m₂) := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun j k => ?_⟩
  calc ‖(m₁ - m₂) j k‖ = ‖m₁ j k - m₂ j k‖ := rfl
    _ ≤ ‖m₁ j k‖ + ‖m₂ j k‖ := norm_sub_le _ _
    _ ≤ C₁ + C₂ := add_le_add (hC₁ j k) (hC₂ j k)

theorem nonneg_of_symbol_bound {m : Fin 2 → Gam → ℂ} {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) :
    0 ≤ C := le_trans (norm_nonneg (m 0 0)) (hC 0 0)

theorem summable_mult (μ : Gam → ℂ) {C : ℝ} (hC : ∀ k, ‖μ k‖ ≤ C) (a : Wiener) :
    Summable fun k => ‖μ k * a k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((wiener_summable a).mul_left C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)

/-- A bounded Fourier multiplier as a linear map on the Wiener algebra. -/
noncomputable def multLm (μ : Gam → ℂ) (hμ : ∃ C : ℝ, ∀ k, ‖μ k‖ ≤ C) : Wiener →ₗ[ℂ] Wiener where
  toFun a := wmk (fun k => μ k * a k) (summable_mult μ (Classical.choose_spec hμ) a)
  map_add' _ _ := by ext k; simp only [wmk_apply, lp.coeFn_add, Pi.add_apply]; ring
  map_smul' c a := by
    ext k
    simp only [wmk_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem norm_multLm_apply_le (μ : Gam → ℂ) (hμ : ∃ C : ℝ, ∀ k, ‖μ k‖ ≤ C) {C : ℝ}
    (hC : ∀ k, ‖μ k‖ ≤ C) (a : Wiener) : ‖multLm μ hμ a‖ ≤ C * ‖a‖ := by
  rw [wiener_norm_eq, wiener_norm_eq a, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_mult μ (Classical.choose_spec hμ) a)
    ((wiener_summable a).mul_left C)
  show ‖μ k * a k‖ ≤ C * ‖a k‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)

/-- **A uniformly bounded symbol defines a bounded Fourier multiplier** on the Wiener
algebra. -/
noncomputable def mult (μ : Gam → ℂ) (hμ : ∃ C : ℝ, ∀ k, ‖μ k‖ ≤ C) : Wiener →L[ℂ] Wiener :=
  LinearMap.mkContinuousOfExistsBound (multLm μ hμ)
    ⟨Classical.choose hμ, fun a => norm_multLm_apply_le μ hμ (Classical.choose_spec hμ) a⟩

@[simp] theorem mult_apply (μ : Gam → ℂ) (hμ : ∃ C : ℝ, ∀ k, ‖μ k‖ ≤ C) (a : Wiener) (k : Gam) :
    (mult μ hμ a) k = μ k * a k := rfl

theorem norm_mult_apply_le (μ : Gam → ℂ) (hμ : ∃ C : ℝ, ∀ k, ‖μ k‖ ≤ C) {C : ℝ}
    (hC : ∀ k, ‖μ k‖ ≤ C) (a : Wiener) : ‖mult μ hμ a‖ ≤ C * ‖a‖ :=
  norm_multLm_apply_le μ hμ hC a

theorem norm_mult_le (μ : Gam → ℂ) (hμ : ∃ C : ℝ, ∀ k, ‖μ k‖ ≤ C) {C : ℝ}
    (hC : ∀ k, ‖μ k‖ ≤ C) : ‖mult μ hμ‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ (le_trans (norm_nonneg (μ 0)) (hC 0))
    (fun a => norm_mult_apply_le μ hμ hC a)

/-- The `j`-th component `(R_m)ⱼ` of the velocity operator, as a bounded Fourier
multiplier on the Wiener algebra. -/
noncomputable def velocity (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) :
    Wiener →L[ℂ] Wiener := mult (m j) (hm.component j)

@[simp] theorem velocity_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (a : Wiener) (k : Gam) : (velocity m hm j a) k = m j k * a k := rfl

theorem norm_velocity_apply_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (a : Wiener) : ‖velocity m hm j a‖ ≤ C * ‖a‖ :=
  norm_mult_apply_le _ _ (fun k => hC j k) a

theorem norm_velocity_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (j : Fin 2) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) : ‖velocity m hm j‖ ≤ C :=
  norm_mult_le _ _ (fun k => hC j k)

theorem velocity_sub {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsBddSymbol m₁) (h₂ : IsBddSymbol m₂)
    (j : Fin 2) (a : Wiener) :
    velocity m₁ h₁ j a - velocity m₂ h₂ j a = velocity (m₁ - m₂) (h₁.sub h₂) j a := by
  ext k
  simp only [lp.coeFn_sub, Pi.sub_apply, velocity_apply]
  show m₁ j k * a k - m₂ j k * a k = (m₁ j - m₂ j) k * a k
  simp only [Pi.sub_apply]
  ring

/-! ## 5. The quadratic transport term -/

/-- The `j`-th summand `(R_m u)ⱼ ⋆ ∂ⱼ v` of the transport form. -/
noncomputable def transportComp (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) :
    Wiener1 →L[ℂ] Wiener1 →L[ℂ] Wiener :=
  ContinuousLinearMap.bilinearComp convCLM ((velocity m hm j).comp incl) (fourierDeriv j)

@[simp] theorem transportComp_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (u v : Wiener1) :
    transportComp m hm j u v = conv (velocity m hm j (incl u)) (fourierDeriv j v) := rfl

/-- **The Li–Wang transport form** `N_m(u,v) = ∑ⱼ (R_m u)ⱼ ⋆ ∂ⱼ v`, as a continuous
bilinear map `A¹ × A¹ → A`. -/
noncomputable def transport (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) :
    Wiener1 →L[ℂ] Wiener1 →L[ℂ] Wiener :=
  ∑ j : Fin 2, transportComp m hm j

theorem transport_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v : Wiener1) :
    transport m hm u v = ∑ j : Fin 2, conv (velocity m hm j (incl u)) (fourierDeriv j v) := by
  simp only [transport, ContinuousLinearMap.sum_apply, transportComp_apply]

/-- The explicit Fourier-coefficient formula for the transport form. -/
theorem transport_apply_coeff (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v : Wiener1)
    (k : Gam) :
    (transport m hm u v) k =
      ∑ j : Fin 2, ∑' p : Gam,
        (m j p * u.coeff p) * (twoPiI * (((k - p) j : ℤ) : ℂ) * v.coeff (k - p)) := by
  rw [transport_apply]
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, conv_apply, velocity_apply, incl_apply, fourierDeriv_apply]

/-- **The transport form is bounded**, with the explicit estimate
`‖N_m(u,v)‖ ≤ 4πC ‖u‖ ‖v‖`. -/
theorem norm_transport_apply_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (u v : Wiener1) :
    ‖transport m hm u v‖ ≤ 4 * Real.pi * C * ‖u‖ * ‖v‖ := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hbound : ∀ j : Fin 2, ‖conv (velocity m hm j (incl u)) (fourierDeriv j v)‖
      ≤ (C * ‖u‖) * (2 * Real.pi * ‖v‖) := by
    intro j
    refine (norm_conv_le _ _).trans ?_
    have h1 : ‖velocity m hm j (incl u)‖ ≤ C * ‖u‖ :=
      (norm_velocity_apply_le hm j hC (incl u)).trans
        (mul_le_mul_of_nonneg_left (norm_incl_apply_le u) hC0)
    have h2 : ‖fourierDeriv j v‖ ≤ 2 * Real.pi * ‖v‖ := norm_fourierDeriv_apply_le j v
    exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
  rw [transport_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 2, ‖conv (velocity m hm j (incl u)) (fourierDeriv j v)‖
      ≤ ∑ _j : Fin 2, (C * ‖u‖) * (2 * Real.pi * ‖v‖) :=
        Finset.sum_le_sum (fun j _ => hbound j)
    _ = 4 * Real.pi * C * ‖u‖ * ‖v‖ := by rw [Fin.sum_univ_two]; ring

/-- **Operator-norm bound for the transport form.** -/
theorem norm_transport_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) : ‖transport m hm‖ ≤ 4 * Real.pi * C := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) (fun u v => ?_)
  exact norm_transport_apply_le hm hC u v

/-- Linearity of the transport form in the symbol. -/
theorem transport_sub {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsBddSymbol m₁) (h₂ : IsBddSymbol m₂) :
    transport m₁ h₁ - transport m₂ h₂ = transport (m₁ - m₂) (h₁.sub h₂) := by
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.sub_apply, transport_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← conv_sub_left, velocity_sub]

/-! ## 6. Quadratic maps attached to continuous bilinear maps -/

section Quadratic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The quadratic map `x ↦ B x x` attached to a continuous bilinear map `B`. -/
def quad (B : E →L[𝕜] E →L[𝕜] F) : E → F := fun x => B x x

@[simp] theorem quad_apply (B : E →L[𝕜] E →L[𝕜] F) (x : E) : quad B x = B x x := rfl

theorem quad_zero (B : E →L[𝕜] E →L[𝕜] F) : quad B 0 = 0 := by simp [quad]

theorem hasFDerivAt_quad (B : E →L[𝕜] E →L[𝕜] F) (x : E) :
    HasFDerivAt (quad B) (B x + B.flip x) x := by
  have h1 : HasFDerivAt (fun y : E => B y) B x := B.hasFDerivAt
  have h2 : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id 𝕜 E) x := hasFDerivAt_id x
  simpa using h1.clm_apply h2

theorem fderiv_quad (B : E →L[𝕜] E →L[𝕜] F) (x : E) :
    fderiv 𝕜 (quad B) x = B x + B.flip x := (hasFDerivAt_quad B x).fderiv

theorem fderiv_quad_eq (B : E →L[𝕜] E →L[𝕜] F) : fderiv 𝕜 (quad B) = ⇑(B + B.flip) := by
  funext x; rw [fderiv_quad]; rfl

theorem fderiv_quad_zero (B : E →L[𝕜] E →L[𝕜] F) : fderiv 𝕜 (quad B) 0 = 0 := by
  rw [fderiv_quad]; simp

theorem fderiv_fderiv_quad (B : E →L[𝕜] E →L[𝕜] F) (x : E) :
    fderiv 𝕜 (fderiv 𝕜 (quad B)) x = B + B.flip := by
  rw [fderiv_quad_eq]; exact ContinuousLinearMap.fderiv _

theorem contDiff_quad (B : E →L[𝕜] E →L[𝕜] F) (n : WithTop ℕ∞) : ContDiff 𝕜 n (quad B) := by
  have hb : IsBoundedBilinearMap 𝕜 (fun p : E × E => B p.1 p.2) := B.isBoundedBilinearMap
  have h1 : ContDiff 𝕜 n (fun p : E × E => B p.1 p.2) := hb.contDiff
  exact ContDiff.comp₂ h1 contDiff_id contDiff_id

theorem iteratedFDeriv_two_quad (B : E →L[𝕜] E →L[𝕜] F) (x h₁ h₂ : E) :
    iteratedFDeriv 𝕜 2 (quad B) x ![h₁, h₂] = B h₁ h₂ + B h₂ h₁ := by
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_quad]
  simp

/-- The exact second-order Taylor expansion of a quadratic map: there is no remainder. -/
theorem quad_add (B : E →L[𝕜] E →L[𝕜] F) (x h : E) :
    quad B (x + h) = quad B x + (B x h + B h x) + B h h := by
  simp only [quad, map_add, ContinuousLinearMap.add_apply]
  abel

/-- **Analyticity of a quadratic map**, as a genuine Mathlib `AnalyticOnNhd` statement.
It is obtained from `ContDiff 𝕜 (⊤ : WithTop ℕ∞)`, i.e. from the analyticity index `ω`,
*not* from `C^∞`. -/
theorem analyticOnNhd_quad (B : E →L[𝕜] E →L[𝕜] F) (s : Set E) :
    AnalyticOnNhd 𝕜 (quad B) s := (contDiff_quad B (⊤ : WithTop ℕ∞)).analyticOnNhd

theorem analyticAt_quad (B : E →L[𝕜] E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 (quad B) x :=
  analyticOnNhd_quad B Set.univ x (Set.mem_univ x)

end Quadratic

/-! ## 7. The quadratic residual `Q_m` and its derivatives -/

/-- **The Li–Wang quadratic residual** `Q_m(u) = N_m(u,u)`. -/
noncomputable def quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) : Wiener1 → Wiener :=
  quad (transport m hm)

theorem quadResidual_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u : Wiener1) :
    quadResidual m hm u = transport m hm u u := rfl

/-- `Q_m(0) = 0`. -/
theorem quadResidual_zero (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) :
    quadResidual m hm 0 = 0 := quad_zero _

theorem hasFDerivAt_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (x : Wiener1) :
    HasFDerivAt (quadResidual m hm) (transport m hm x + (transport m hm).flip x) x :=
  hasFDerivAt_quad _ x

theorem fderiv_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (x : Wiener1) :
    fderiv ℂ (quadResidual m hm) x = transport m hm x + (transport m hm).flip x :=
  fderiv_quad _ x

/-- `DQ_m(0) = 0`. -/
theorem fderiv_quadResidual_zero (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) :
    fderiv ℂ (quadResidual m hm) 0 = 0 := fderiv_quad_zero _

/-- `Q_m` is `C^n` for every smoothness index `n : WithTop ℕ∞`. -/
theorem contDiff_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (n : WithTop ℕ∞) :
    ContDiff ℂ n (quadResidual m hm) := contDiff_quad _ n

theorem contDiff_two_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) :
    ContDiff ℂ 2 (quadResidual m hm) := contDiff_quad _ 2

/-- `Q_m` is `C^∞`.  (Note: `(⊤ : ℕ∞)` is the `C^∞` index; it is *not* the analyticity
index.  `C^∞` does not imply analyticity in general — for the genuine analyticity
statement see `LiWang.Formalization.analyticOnNhd_quadResidual` below.) -/
theorem contDiff_top_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) :
    ContDiff ℂ (⊤ : ℕ∞) (quadResidual m hm) := contDiff_quad _ _

/-- **Analyticity of `Q_m`**, as a genuine Mathlib `AnalyticOnNhd` statement.  This is *not*
inferred from `C^∞`; it is obtained from `ContDiff ℂ (⊤ : WithTop ℕ∞)` (the analyticity
index `ω`, which in this Mathlib is by definition analyticity together with a Taylor
series), via `ContDiff.analyticOnNhd`. -/
theorem analyticOnNhd_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (s : Set Wiener1) : AnalyticOnNhd ℂ (quadResidual m hm) s :=
  analyticOnNhd_quad _ s

theorem analyticAt_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (x : Wiener1) :
    AnalyticAt ℂ (quadResidual m hm) x := analyticAt_quad _ x

/-- **`Q_m` has a convergent power series expansion at every point.** -/
theorem hasFPowerSeriesAt_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (x : Wiener1) :
    ∃ p : FormalMultilinearSeries ℂ Wiener1 Wiener, HasFPowerSeriesAt (quadResidual m hm) p x :=
  analyticAt_quad _ x

/-- The exact (finite, remainder-free) second-order Taylor expansion of `Q_m`:
`Q_m(x + h) = Q_m(x) + (N_m(x,h) + N_m(h,x)) + N_m(h,h)`. -/
theorem quadResidual_add (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (x h : Wiener1) :
    quadResidual m hm (x + h)
      = quadResidual m hm x + (transport m hm x h + transport m hm h x)
        + transport m hm h h := quad_add _ x h

/-- **The mixed second derivative of the quadratic residual.**
`D²Q_m(0)[h₁,h₂] = N_m(h₁,h₂) + N_m(h₂,h₁)`. -/
theorem fderiv_fderiv_quadResidual_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (h₁ h₂ : Wiener1) :
    fderiv ℂ (fderiv ℂ (quadResidual m hm)) 0 h₁ h₂
      = transport m hm h₁ h₂ + transport m hm h₂ h₁ := by
  have hq : quadResidual m hm = quad (transport m hm) := rfl
  rw [hq, fderiv_fderiv_quad]
  simp

/-- The same statement in terms of Mathlib's iterated Fréchet derivative. -/
theorem iteratedFDeriv_two_quadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (h₁ h₂ : Wiener1) :
    iteratedFDeriv ℂ 2 (quadResidual m hm) 0 ![h₁, h₂]
      = transport m hm h₁ h₂ + transport m hm h₂ h₁ :=
  iteratedFDeriv_two_quad _ 0 h₁ h₂

/-- The transport form does not depend on which uniform bound is used to witness
admissibility of the symbol. -/
theorem transport_proof_irrel (m : Fin 2 → Gam → ℂ) (h h' : IsBddSymbol m) :
    transport m h = transport m h' := rfl

/-- **Summary: the concrete quadratic residual realization.**  For every uniformly bounded
velocity symbol `m` the quadratic residual `Q_m` vanishes to second order at the origin,
is smooth, the underlying transport form `N_m` is a continuous bilinear map with the
explicit bound `‖N_m‖ ≤ 4πC`, and the second derivative of `Q_m` at the origin is the
symmetrization of `N_m`. -/
theorem quadResidual_realization {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) :
    quadResidual m hm 0 = 0
      ∧ fderiv ℂ (quadResidual m hm) 0 = 0
      ∧ ContDiff ℂ (⊤ : ℕ∞) (quadResidual m hm)
      ∧ ‖transport m hm‖ ≤ 4 * Real.pi * C
      ∧ (∀ h₁ h₂ : Wiener1, fderiv ℂ (fderiv ℂ (quadResidual m hm)) 0 h₁ h₂
          = transport m hm h₁ h₂ + transport m hm h₂ h₁) :=
  ⟨quadResidual_zero m hm, fderiv_quadResidual_zero m hm, contDiff_top_quadResidual m hm,
    norm_transport_le hm hC, fderiv_fderiv_quadResidual_apply m hm⟩

/-! ## 8. The Li–Wang polarization identity -/

/-- **The Li–Wang polarization identity.**  For two admissible velocity symbols
`m₁`, `m₂` the second derivative at the origin of the difference of the quadratic
residuals is the symmetrization of the transport form of the *difference symbol*:
`D²(Q_{m₁} - Q_{m₂})(0)[h₁,h₂] = N_{m₁-m₂}(h₁,h₂) + N_{m₁-m₂}(h₂,h₁)`. -/
theorem liWang_polarization {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsBddSymbol m₁)
    (h₂ : IsBddSymbol m₂) (g₁ g₂ : Wiener1) :
    fderiv ℂ (fderiv ℂ (fun x => quadResidual m₁ h₁ x - quadResidual m₂ h₂ x)) 0 g₁ g₂
      = transport (m₁ - m₂) (h₁.sub h₂) g₁ g₂ + transport (m₁ - m₂) (h₁.sub h₂) g₂ g₁ := by
  have hfun : (fun x => quadResidual m₁ h₁ x - quadResidual m₂ h₂ x)
      = quad (transport (m₁ - m₂) (h₁.sub h₂)) := by
    funext x
    rw [← transport_sub h₁ h₂]
    rfl
  rw [hfun, fderiv_fderiv_quad]
  simp

/-- The polarization identity in terms of the iterated Fréchet derivative. -/
theorem liWang_polarization_iteratedFDeriv {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsBddSymbol m₁)
    (h₂ : IsBddSymbol m₂) (g₁ g₂ : Wiener1) :
    iteratedFDeriv ℂ 2 (fun x => quadResidual m₁ h₁ x - quadResidual m₂ h₂ x) 0 ![g₁, g₂]
      = transport (m₁ - m₂) (h₁.sub h₂) g₁ g₂ + transport (m₁ - m₂) (h₁.sub h₂) g₂ g₁ := by
  have hfun : (fun x => quadResidual m₁ h₁ x - quadResidual m₂ h₂ x)
      = quad (transport (m₁ - m₂) (h₁.sub h₂)) := by
    funext x
    rw [← transport_sub h₁ h₂]
    rfl
  rw [hfun]
  exact iteratedFDeriv_two_quad _ 0 g₁ g₂

end LiWang.Formalization
