/-
# The first and second source variations

For the source-to-solution map `S_K = Ψ⁻¹ ∘ J_T` of `SourceSolution.lean` we compute the
actual Fréchet variations at the zero source:

    DS_K(0)[h]      = J_T h ,
    D²S_K(0)[h₁,h₂] = -( B_K(J_T h₁, J_T h₂) + B_K(J_T h₂, J_T h₁) )
                    = -J_T ( N_K(J_T h₁, J_T h₂) + N_K(J_T h₂, J_T h₁) ) .

The proof differentiates the mild identity `S = J - B(S,S)`, which holds on a neighbourhood of
the zero source, twice; no candidate map is assumed.

Part of `LiWangWienerSourceResponsePacket` v3.0.
-/
import LiWangWiener.SourceSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal
open Filter Topology BoundedContinuousFunction ContinuousLinearMap

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## Differentiability of the solution map near the zero source -/

theorem eventually_differentiableAt_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    ∀ᶠ f in 𝓝 (0 : Curve0 T), DifferentiableAt ℝ (sourceSolution hα hT hm hr) f := by
  have h := (contDiffAt_sourceSolution hα hT hm hr).eventually (by decide)
  filter_upwards [h] with f hf
  exact hf.differentiableAt (by norm_num)

/-- On a neighbourhood of the zero source, the derivative of `S` satisfies the differentiated
mild equation. -/
theorem eventually_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    fderiv ℝ (sourceSolution hα hT hm hr) =ᶠ[𝓝 (0 : Curve0 T)]
      fun f => (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)
        - ((sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f)
            + (sourceQuad hα hT m hm hr).flip (sourceSolution hα hT hm hr f)).comp
              (fderiv ℝ (sourceSolution hα hT hm hr) f)) := by
  have hmild := (eventually_sourceSolution_eq hα hT hm hr).eventually_nhds
  filter_upwards [hmild, eventually_differentiableAt_sourceSolution hα hT hm hr] with f hf hdf
  -- near `f`, `S g = J g - quad B (S g)`
  have hEq : sourceSolution hα hT hm hr =ᶠ[𝓝 f]
      fun g => duhamelOp hα hT g - quad (sourceQuad hα hT m hm hr) (sourceSolution hα hT hm hr g) := by
    filter_upwards [hf] with g hg
    rw [show quad (sourceQuad hα hT m hm hr) (sourceSolution hα hT hm hr g)
        = sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr g)
            (sourceSolution hα hT hm hr g) from rfl, ← hg]
    abel
  have hcomp : HasFDerivAt
      (fun g => quad (sourceQuad hα hT m hm hr) (sourceSolution hα hT hm hr g))
      ((sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f)
        + (sourceQuad hα hT m hm hr).flip (sourceSolution hα hT hm hr f)).comp
          (fderiv ℝ (sourceSolution hα hT hm hr) f)) f :=
    (hasFDerivAt_quad (sourceQuad hα hT m hm hr) (sourceSolution hα hT hm hr f)).comp f
      hdf.hasFDerivAt
  have hsub : HasFDerivAt
      (fun g => duhamelOp hα hT g - quad (sourceQuad hα hT m hm hr) (sourceSolution hα hT hm hr g))
      ((duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)
        - ((sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f)
            + (sourceQuad hα hT m hm hr).flip (sourceSolution hα hT hm hr f)).comp
              (fderiv ℝ (sourceSolution hα hT hm hr) f))) f :=
    (duhamelOp hα hT).hasFDerivAt.sub hcomp
  exact hEq.fderiv_eq.trans hsub.fderiv

/-! ## The second variation -/

/-- **The exact second source variation.** -/
theorem fderiv_fderiv_sourceSolution_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T)
      = -(((compL ℝ (Curve0 T) (Curve1 T) (Curve1 T)).flip
            (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)).comp
          (((sourceQuad hα hT m hm hr) + (sourceQuad hα hT m hm hr).flip).comp
            (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T))) := by
  -- the map `A f = B (S f) + B.flip (S f)` and its derivative at `0`
  have hS0 : sourceSolution hα hT hm hr (0 : Curve0 T) = 0 := sourceSolution_zero hα hT hm hr
  have hA : HasFDerivAt
      (fun f => (sourceQuad hα hT m hm hr) (sourceSolution hα hT hm hr f)
        + (sourceQuad hα hT m hm hr).flip (sourceSolution hα hT hm hr f))
      ((((sourceQuad hα hT m hm hr) + (sourceQuad hα hT m hm hr).flip)).comp
        (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)) (0 : Curve0 T) := by
    have hlin : HasFDerivAt
        (fun u : Curve1 T => (sourceQuad hα hT m hm hr) u + (sourceQuad hα hT m hm hr).flip u)
        ((sourceQuad hα hT m hm hr) + (sourceQuad hα hT m hm hr).flip)
        (sourceSolution hα hT hm hr (0 : Curve0 T)) :=
      ((sourceQuad hα hT m hm hr) + (sourceQuad hα hT m hm hr).flip).hasFDerivAt
    exact hlin.comp (0 : Curve0 T) (hasFDerivAt_sourceSolution_zero hα hT hm hr)
  -- the map `C f = fderiv S f` and its derivative at `0`
  have hC : HasFDerivAt (fderiv ℝ (sourceSolution hα hT hm hr))
      (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T)) (0 : Curve0 T) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) :=
      (contDiffAt_sourceSolution hα hT hm hr).fderiv_right (m := 1) (by norm_num)
    exact (h1.differentiableAt (by norm_num)).hasFDerivAt
  -- differentiate the right-hand side of the differentiated mild equation
  have hprod := hA.clm_comp hC
  have hconst : HasFDerivAt
      (fun _ : Curve0 T => (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)) 0 (0 : Curve0 T) :=
    hasFDerivAt_const (𝕜 := ℝ) (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T) (0 : Curve0 T)
  have hrhs : HasFDerivAt
      (fun f : Curve0 T => (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)
        - ((sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f)
            + (sourceQuad hα hT m hm hr).flip (sourceSolution hα hT hm hr f)).comp
              (fderiv ℝ (sourceSolution hα hT hm hr) f)))
      (0 - (((compL ℝ (Curve0 T) (Curve1 T) (Curve1 T))
              ((sourceQuad hα hT m hm hr) (sourceSolution hα hT hm hr 0)
                + (sourceQuad hα hT m hm hr).flip (sourceSolution hα hT hm hr 0))).comp
            (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T))
          + ((compL ℝ (Curve0 T) (Curve1 T) (Curve1 T)).flip
              (fderiv ℝ (sourceSolution hα hT hm hr) 0)).comp
            ((((sourceQuad hα hT m hm hr) + (sourceQuad hα hT m hm hr).flip)).comp
              (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)))) (0 : Curve0 T) :=
    hconst.sub hprod
  have hkey := ((eventually_fderiv_sourceSolution hα hT hm hr).fderiv_eq).trans hrhs.fderiv
  rw [hkey, hS0, map_zero, map_zero, add_zero, map_zero,
    fderiv_sourceSolution_zero hα hT hm hr]
  simp only [ContinuousLinearMap.zero_comp, zero_add]
  abel

/-- **The second source variation, applied to two sources.** -/
theorem fderiv_fderiv_sourceSolution_apply (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = -(sourceQuad hα hT m hm hr (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
          + sourceQuad hα hT m hm hr (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)) := by
  rw [fderiv_fderiv_sourceSolution_zero hα hT hm hr]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.add_apply]

/-- The second variation, written with the transport form pulled out of the Duhamel
operator: `D²S(0)[h₁,h₂] = -J_T(N_K(J h₁, J h₂) + N_K(J h₂, J h₁))`. -/
theorem fderiv_fderiv_sourceSolution_apply' (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = -(duhamelOp hα hT
            (spacetimeTransport m hm hr (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
              + spacetimeTransport m hm hr (duhamelOp hα hT h₂) (duhamelOp hα hT h₁))) := by
  rw [fderiv_fderiv_sourceSolution_apply hα hT hm hr h₁ h₂, map_add]
  rfl

/-- **Symmetry of the second variation.** -/
theorem fderiv_fderiv_sourceSolution_symm (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₂ h₁ := by
  rw [fderiv_fderiv_sourceSolution_apply hα hT hm hr h₁ h₂,
    fderiv_fderiv_sourceSolution_apply hα hT hm hr h₂ h₁, add_comm]

/-! ## Pointwise-in-time form of the variations -/

/-- **The first variation, in Fourier coefficients at each time.** -/
theorem fderiv_sourceSolution_zero_val (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) (t : TimeI T) :
    ((fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).val
      = duhamelIntegral hα.le (t : ℝ) (sourceFun hT h) := by
  rw [fderiv_sourceSolution_zero hα hT hm hr, duhamelOp_apply_val]

/-- **The second variation, in Fourier coefficients at each time.** -/
theorem fderiv_fderiv_sourceSolution_val (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) (t : TimeI T) :
    ((fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂) t).val
      = -(duhamelIntegral hα.le (t : ℝ)
            (fun s => transport m hm ((duhamelOp hα hT h₁) (clampT hT s)).val
              ((duhamelOp hα hT h₂) (clampT hT s)).val)
          + duhamelIntegral hα.le (t : ℝ)
            (fun s => transport m hm ((duhamelOp hα hT h₂) (clampT hT s)).val
              ((duhamelOp hα hT h₁) (clampT hT s)).val)) := by
  have hval : ∀ w : RealWiener1, (-w).val = -w.val := fun _ => rfl
  rw [fderiv_fderiv_sourceSolution_apply hα hT hm hr h₁ h₂,
    BoundedContinuousFunction.neg_apply, hval, BoundedContinuousFunction.add_apply,
    RealWiener1.val_add, sourceQuad_val hα hT hm hr, sourceQuad_val hα hT hm hr]

/-! ## Zero initial traces and bounds -/

theorem fderiv_sourceSolution_zero_initial (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) :
    (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) ⟨0, ⟨le_rfl, hT⟩⟩ = 0 := by
  rw [fderiv_sourceSolution_zero hα hT hm hr]
  exact duhamelOp_zero_time hα hT h

theorem fderiv_fderiv_sourceSolution_initial (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂)
      ⟨0, ⟨le_rfl, hT⟩⟩ = 0 := by
  rw [fderiv_fderiv_sourceSolution_apply hα hT hm hr h₁ h₂]
  have hval : ∀ w : Curve1 T, (-w) ⟨0, ⟨le_rfl, hT⟩⟩ = -(w ⟨0, ⟨le_rfl, hT⟩⟩) := fun _ => rfl
  rw [hval, BoundedContinuousFunction.add_apply, sourceQuad_apply, sourceQuad_apply,
    duhamelOp_zero_time hα hT, duhamelOp_zero_time hα hT, add_zero, neg_zero]

theorem norm_fderiv_sourceSolution_apply_le (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) :
    ‖fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h‖ ≤ duhamelConst α T * ‖h‖ := by
  rw [fderiv_sourceSolution_zero hα hT hm hr]
  exact norm_duhamelCurve_le hα hT h

theorem norm_fderiv_fderiv_sourceSolution_le (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {b : ℝ}
    (hb : ‖(sourceQuad hα hT m hm hr)‖ ≤ b) (h₁ h₂ : Curve0 T) :
    ‖fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂‖
      ≤ 2 * b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖) := by
  have hb0 : (0:ℝ) ≤ b := le_trans (norm_nonneg (sourceQuad hα hT m hm hr)) hb
  have hG0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  have hJ1 : ‖duhamelOp hα hT h₁‖ ≤ duhamelConst α T * ‖h₁‖ := norm_duhamelCurve_le hα hT h₁
  have hJ2 : ‖duhamelOp hα hT h₂‖ ≤ duhamelConst α T * ‖h₂‖ := norm_duhamelCurve_le hα hT h₂
  have hn1 : (0:ℝ) ≤ duhamelConst α T * ‖h₁‖ := by positivity
  have hn2 : (0:ℝ) ≤ duhamelConst α T * ‖h₂‖ := by positivity
  have hbound : ∀ x y : Curve1 T, ‖x‖ ≤ duhamelConst α T * ‖h₁‖ →
      ‖y‖ ≤ duhamelConst α T * ‖h₂‖ →
      ‖sourceQuad hα hT m hm hr x y‖
        ≤ b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖) := by
    intro x y hx hy
    refine le_trans ((sourceQuad hα hT m hm hr).le_opNorm₂ x y) ?_
    have h1 : ‖(sourceQuad hα hT m hm hr)‖ * ‖x‖ ≤ b * (duhamelConst α T * ‖h₁‖) :=
      le_trans (mul_le_mul_of_nonneg_right hb (norm_nonneg x))
        (mul_le_mul_of_nonneg_left hx hb0)
    calc ‖(sourceQuad hα hT m hm hr)‖ * ‖x‖ * ‖y‖
        ≤ (b * (duhamelConst α T * ‖h₁‖)) * ‖y‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
      _ ≤ (b * (duhamelConst α T * ‖h₁‖)) * (duhamelConst α T * ‖h₂‖) :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖) := by ring
  have hswap : ‖sourceQuad hα hT m hm hr (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)‖
      ≤ b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖) := by
    refine le_trans ((sourceQuad hα hT m hm hr).le_opNorm₂ _ _) ?_
    have h1 : ‖(sourceQuad hα hT m hm hr)‖ * ‖duhamelOp hα hT h₂‖
        ≤ b * (duhamelConst α T * ‖h₂‖) :=
      le_trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hJ2 hb0)
    calc ‖(sourceQuad hα hT m hm hr)‖ * ‖duhamelOp hα hT h₂‖ * ‖duhamelOp hα hT h₁‖
        ≤ (b * (duhamelConst α T * ‖h₂‖)) * ‖duhamelOp hα hT h₁‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ (b * (duhamelConst α T * ‖h₂‖)) * (duhamelConst α T * ‖h₁‖) :=
          mul_le_mul_of_nonneg_left hJ1 (by positivity)
      _ = b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖) := by ring
  rw [fderiv_fderiv_sourceSolution_apply hα hT hm hr h₁ h₂, norm_neg]
  refine le_trans (norm_add_le _ _) ?_
  have := hbound _ _ hJ1 hJ2
  have hsum := add_le_add this hswap
  calc ‖sourceQuad hα hT m hm hr (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)‖
        + ‖sourceQuad hα hT m hm hr (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)‖
      ≤ b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖)
        + b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖) := hsum
    _ = 2 * b * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖) := by ring

/-! ## Kernel dependence -/

/-- **The first response does not depend on the kernel.** -/
theorem fderiv_sourceSolution_kernel_independent (hα : 1 / 2 < α) (hT : 0 ≤ T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) :
    fderiv ℝ (sourceSolution hα hT hm₁ hr₁) (0 : Curve0 T)
      = fderiv ℝ (sourceSolution hα hT hm₂ hr₂) (0 : Curve0 T) := by
  rw [fderiv_sourceSolution_zero hα hT hm₁ hr₁, fderiv_sourceSolution_zero hα hT hm₂ hr₂]

/-- **The difference of the two second responses is governed by the difference of the actual
transport operators.** -/
theorem fderiv_fderiv_sourceSolution_sub (hα : 1 / 2 < α) (hT : 0 ≤ T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (h₁ h₂ : Curve0 T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm₁ hr₁)) (0 : Curve0 T) h₁ h₂
        - fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm₂ hr₂)) (0 : Curve0 T) h₁ h₂
      = -(duhamelOp hα hT
            (spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
                (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
              + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
                (duhamelOp hα hT h₂) (duhamelOp hα hT h₁))) := by
  have hsub : (spacetimeTransport m₁ hm₁ hr₁ : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T)
      - spacetimeTransport m₂ hm₂ hr₂
      = spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) :=
    spacetimeTransport_sub hm₁ hm₂ hr₁ hr₂
  have e₁ : spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
      = spacetimeTransport m₁ hm₁ hr₁ (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
        - spacetimeTransport m₂ hm₂ hr₂ (duhamelOp hα hT h₁) (duhamelOp hα hT h₂) := by
    rw [← hsub]; rfl
  have e₂ : spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)
      = spacetimeTransport m₁ hm₁ hr₁ (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)
        - spacetimeTransport m₂ hm₂ hr₂ (duhamelOp hα hT h₂) (duhamelOp hα hT h₁) := by
    rw [← hsub]; rfl
  have key : spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
      + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)
      = (spacetimeTransport m₁ hm₁ hr₁ (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
          + spacetimeTransport m₁ hm₁ hr₁ (duhamelOp hα hT h₂) (duhamelOp hα hT h₁))
        - (spacetimeTransport m₂ hm₂ hr₂ (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
          + spacetimeTransport m₂ hm₂ hr₂ (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)) := by
    rw [e₁, e₂]; abel
  rw [fderiv_fderiv_sourceSolution_apply' hα hT hm₁ hr₁ h₁ h₂,
    fderiv_fderiv_sourceSolution_apply' hα hT hm₂ hr₂ h₁ h₂, key, map_sub]
  abel

end LiWang.WienerModel
