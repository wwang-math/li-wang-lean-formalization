/-
# The evolution equations satisfied by the source variations

The first and second source responses of the forced solution map are Duhamel terms, hence
they satisfy *linear* coefficient evolution equations at interior times:

    d/dt (DS(0)[h])_k(t) + λ_k (DS(0)[h])_k(t) = h_k(t) ,
    d/dt (D²S(0)[h₁,h₂])_k(t) + λ_k (D²S(0)[h₁,h₂])_k(t)
      = -(N_K(J h₁, J h₂) + N_K(J h₂, J h₁))_k(t) ,

together with vanishing initial traces and the corresponding weak formulations against
`C¹` time test functions supported in `(0,T)`.

Part of `LiWangFormalizationSourceResponsePacket` v3.0.
-/
import LiWangFormalization.CoefficientODE
import LiWangFormalization.SourceVariations

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## The first variation -/

/-- The first response is the Duhamel curve of the perturbation itself. -/
theorem curveState_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) :
    curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h)
      = curveState hT (duhamelOp hα hT h) := by
  rw [fderiv_sourceSolution_zero hα hT hm hr]

/-- **The coefficient evolution of the first source response**:
`d/dt (DS(0)[h])_k(t) + λ_k (DS(0)[h])_k(t) = h_k(t)` at every interior time. -/
theorem hasDerivAt_coeff_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h : Curve0 T) (k : Gam)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt
      (fun r : ℝ =>
        (curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) r).coeff k)
      ((sourceFun hT h t) k - (fracSymbol α k : ℂ)
        * (curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).coeff k) t := by
  rw [curveState_fderiv_sourceSolution hα hT hm hr h]
  exact hasDerivAt_coeff_duhamelOp hα hT h k ht0 htT

/-- The first response starts at zero in every coefficient. -/
theorem coeff_fderiv_sourceSolution_initial (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) (k : Gam) :
    (curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) 0).coeff k = 0 := by
  rw [curveState_fderiv_sourceSolution hα hT hm hr h]
  exact coeff_duhamelOp_initial hα hT h k

/-- **The weak linear equation for the first source response.** -/
theorem weak_coeff_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) (k : Gam)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T,
        (-((curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).coeff k)
            * ψ t
          + (fracSymbol α k : ℂ)
              * (curveState hT
                  (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).coeff k * φ t
          - (sourceFun hT h t) k * φ t)) = 0 := by
  rw [curveState_fderiv_sourceSolution hα hT hm hr h]
  exact weak_coeff_duhamelOp hα hT h k hφ hψ hφderiv hsupp

/-! ## The second variation -/

/-- The source driving the second response: minus the symmetrised transport of the two
first responses. -/
noncomputable def secondVariationSource (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) : Curve0 T :=
  -(spacetimeTransport m hm hr (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
    + spacetimeTransport m hm hr (duhamelOp hα hT h₂) (duhamelOp hα hT h₁))

/-- Pointwise description of the second-variation source: it is exactly
`-(N_K(J h₁, J h₂) + N_K(J h₂, J h₁))` at each time. -/
theorem sourceFun_secondVariationSource (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) (s : ℝ) :
    sourceFun hT (secondVariationSource hα hT hm hr h₁ h₂) s
      = -(transport m hm ((duhamelOp hα hT h₁) (clampT hT s)).val
            ((duhamelOp hα hT h₂) (clampT hT s)).val
          + transport m hm ((duhamelOp hα hT h₂) (clampT hT s)).val
            ((duhamelOp hα hT h₁) (clampT hT s)).val) := rfl

/-- **The second response is a genuine Duhamel term** for the symmetrised transport source. -/
theorem fderiv_fderiv_sourceSolution_eq_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = duhamelOp hα hT (secondVariationSource hα hT hm hr h₁ h₂) := by
  rw [fderiv_fderiv_sourceSolution_apply' hα hT hm hr h₁ h₂, secondVariationSource, map_neg]

theorem curveState_fderiv_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    curveState hT (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂)
      = curveState hT (duhamelOp hα hT (secondVariationSource hα hT hm hr h₁ h₂)) := by
  rw [fderiv_fderiv_sourceSolution_eq_duhamelOp hα hT hm hr h₁ h₂]

/-- **The coefficient evolution of the second source response**: at every interior time,

    `d/dt (D²S(0)[h₁,h₂])_k(t) + λ_k (D²S(0)[h₁,h₂])_k(t)
        = -(N_K(J h₁, J h₂) + N_K(J h₂, J h₁))_k(t)`. -/
theorem hasDerivAt_coeff_fderiv_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) (k : Gam)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt
      (fun r : ℝ =>
        (curveState hT
          (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂) r).coeff k)
      (-((transport m hm ((duhamelOp hα hT h₁) (clampT hT t)).val
              ((duhamelOp hα hT h₂) (clampT hT t)).val
            + transport m hm ((duhamelOp hα hT h₂) (clampT hT t)).val
              ((duhamelOp hα hT h₁) (clampT hT t)).val) k)
        - (fracSymbol α k : ℂ)
          * (curveState hT
              (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr))
                (0 : Curve0 T) h₁ h₂) t).coeff k) t := by
  rw [curveState_fderiv_fderiv_sourceSolution hα hT hm hr h₁ h₂]
  have hbase := hasDerivAt_coeff_duhamelOp hα hT (secondVariationSource hα hT hm hr h₁ h₂) k
    ht0 htT
  have hsrc : (sourceFun hT (secondVariationSource hα hT hm hr h₁ h₂) t) k
      = -((transport m hm ((duhamelOp hα hT h₁) (clampT hT t)).val
              ((duhamelOp hα hT h₂) (clampT hT t)).val
            + transport m hm ((duhamelOp hα hT h₂) (clampT hT t)).val
              ((duhamelOp hα hT h₁) (clampT hT t)).val) k) := by
    rw [sourceFun_secondVariationSource hα hT hm hr h₁ h₂ t]
    simp only [lp.coeFn_neg, Pi.neg_apply]
  rwa [hsrc] at hbase

/-- The second response starts at zero in every coefficient. -/
theorem coeff_fderiv_fderiv_sourceSolution_initial (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) (k : Gam) :
    (curveState hT
      (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂) 0).coeff k = 0 := by
  rw [curveState_fderiv_fderiv_sourceSolution hα hT hm hr h₁ h₂]
  exact coeff_duhamelOp_initial hα hT _ k

/-- **The weak linear equation for the second source response.** -/
theorem weak_coeff_fderiv_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) (k : Gam)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T,
        (-((curveState hT (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr))
              (0 : Curve0 T) h₁ h₂) t).coeff k) * ψ t
          + (fracSymbol α k : ℂ)
              * (curveState hT (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr))
                  (0 : Curve0 T) h₁ h₂) t).coeff k * φ t
          - (sourceFun hT (secondVariationSource hα hT hm hr h₁ h₂) t) k * φ t)) = 0 := by
  rw [curveState_fderiv_fderiv_sourceSolution hα hT hm hr h₁ h₂]
  exact weak_coeff_duhamelOp hα hT (secondVariationSource hα hT hm hr h₁ h₂) k hφ hψ hφderiv hsupp

end LiWang.Formalization
