/-
# The Duhamel operator on a fixed time interval

Fix `T > 0` and `1/2 < α`.  On the real curve spaces

    X_T = C_b([0,T], A¹_ℝ)   (`Curve1 T`),      Y_T = C_b([0,T], A_ℝ)   (`Curve0 T`),

this module builds the **bounded linear Duhamel operator**

    J_T : Y_T →L[ℝ] X_T ,   (J_T f)(t) = ∫₀^t e^{-(t-s)(-Δ)^α} f(s) ds ,

out of the Bochner integral already constructed in `Duhamel.lean` / `MildSolution.lean`.  The
source curve is extended to all of `ℝ` by clamping the time; the value of `J_T` does not
depend on the extension (`duhamelIntegral_congr`).  Composing `J_T` with the spacetime
transport form gives the concrete continuous bilinear map

    B_K : X_T × X_T → X_T ,   B_K(u,v) = J_T (N_K(u,v)) ,

which is the quadratic part of the forced mild equation.

Part of `LiWangWienerSourceResponsePacket` v3.0.
-/
import LiWangWiener.ForcedSolution
import LiWangWiener.SolutionReality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal
open Filter Topology MeasureTheory BoundedContinuousFunction

namespace LiWang.WienerModel

/-! ## Linearity and locality of the Duhamel integral -/

theorem heatSmoothFun_add {α t : ℝ} (hα : 1 / 2 ≤ α) (a b : Wiener) :
    heatSmoothFun hα t (a + b) = heatSmoothFun hα t a + heatSmoothFun hα t b := by
  by_cases ht : 0 < t
  · rw [heatSmoothFun_eq hα ht, heatSmoothFun_eq hα ht, heatSmoothFun_eq hα ht]
    exact map_add (heatSmoothCLM hα ht) a b
  · rw [heatSmoothFun_of_nonpos hα (not_lt.1 ht), heatSmoothFun_of_nonpos hα (not_lt.1 ht),
      heatSmoothFun_of_nonpos hα (not_lt.1 ht), add_zero]

theorem heatSmoothFun_real_smul {α t : ℝ} (hα : 1 / 2 ≤ α) (r : ℝ) (a : Wiener) :
    heatSmoothFun hα t (r • a) = r • heatSmoothFun hα t a := by
  by_cases ht : 0 < t
  · apply Wiener1.coeff_injective
    funext k
    have hL : (heatSmoothFun hα t (r • a)).coeff k = heatSymbol α t k * ((r • a : Wiener) k) :=
      heatSmoothFun_coeff hα ht _ k
    have hR : (r • heatSmoothFun hα t a).coeff k = r • (heatSymbol α t k * (a k)) := by
      show r • (heatSmoothFun hα t a).coeff k = r • (heatSymbol α t k * (a k))
      rw [heatSmoothFun_coeff hα ht]
    have hsm : ((r • a : Wiener) k) = r • (a k) := by
      simp only [lp.coeFn_smul, Pi.smul_apply]
      rfl
    rw [hL, hR, hsm, mul_smul_comm]
  · rw [heatSmoothFun_of_nonpos hα (not_lt.1 ht), heatSmoothFun_of_nonpos hα (not_lt.1 ht)]
    exact (smul_zero r).symm

theorem duhamelIntegral_add {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g h : ℝ → Wiener} (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) (hN : ∀ s, ‖h s‖ ≤ N) :
    duhamelIntegral hα.le t (fun s => g s + h s)
      = duhamelIntegral hα.le t g + duhamelIntegral hα.le t h := by
  rw [duhamelIntegral, duhamelIntegral, duhamelIntegral,
    ← intervalIntegral.integral_add (intervalIntegrable_duhamelIntegrand hα ht hg hM)
      (intervalIntegrable_duhamelIntegrand hα ht hh hN)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  show heatSmoothFun hα.le (t - s) (g s + h s)
    = heatSmoothFun hα.le (t - s) (g s) + heatSmoothFun hα.le (t - s) (h s)
  exact heatSmoothFun_add hα.le (g s) (h s)

theorem duhamelIntegral_real_smul {α : ℝ} (hα : 1 / 2 ≤ α) (t : ℝ) (r : ℝ)
    (g : ℝ → Wiener) :
    duhamelIntegral hα t (fun s => r • g s) = r • duhamelIntegral hα t g := by
  rw [duhamelIntegral, duhamelIntegral]
  have hcongr : (∫ s in (0:ℝ)..t, duhamelIntegrand hα t (fun s => r • g s) s)
      = ∫ s in (0:ℝ)..t, r • duhamelIntegrand hα t g s := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    show heatSmoothFun hα (t - s) (r • g s) = r • heatSmoothFun hα (t - s) (g s)
    exact heatSmoothFun_real_smul hα r (g s)
  rw [hcongr]
  exact intervalIntegral.integral_smul r (fun s => duhamelIntegrand hα t g s)

/-- **Locality of the Duhamel integral**: it only sees the source on `[0,t]`. -/
theorem duhamelIntegral_congr {α : ℝ} (hα : 1 / 2 ≤ α) {t : ℝ} (ht : 0 ≤ t)
    {g g' : ℝ → Wiener} (hgg : ∀ s ∈ Set.Icc (0:ℝ) t, g s = g' s) :
    duhamelIntegral hα t g = duhamelIntegral hα t g' := by
  rw [duhamelIntegral, duhamelIntegral]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [Set.uIcc_of_le ht] at hs
  show heatSmoothFun hα (t - s) (g s) = heatSmoothFun hα (t - s) (g' s)
  rw [hgg s hs]

/-! ## The clamped extension of a source curve -/

/-- The source curve extended to all of `ℝ` by clamping the time to `[0,T]`. -/
noncomputable def sourceFun {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T) (s : ℝ) : Wiener :=
  (V (clampT hT s)).val

theorem continuous_sourceFun {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T) :
    Continuous (sourceFun hT V) :=
  RealWiener.isometry_val.continuous.comp (V.continuous.comp (continuous_clampT hT))

theorem norm_sourceFun_le {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T) (s : ℝ) :
    ‖sourceFun hT V s‖ ≤ ‖V‖ := V.norm_coe_le_norm _

theorem conjSymmetric_sourceFun {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T) (s : ℝ) :
    ConjSymmetric ((sourceFun hT V s : Wiener) : Gam → ℂ) :=
  (V (clampT hT s)).conjSymmetric

theorem sourceFun_coe {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T) (t : TimeI T) :
    sourceFun hT V (t : ℝ) = (V t).val := by
  have h : clampT hT (t : ℝ) = t := Subtype.ext (clampT_coe hT t.2.1 t.2.2)
  rw [sourceFun, h]

theorem sourceFun_add {T : ℝ} (hT : 0 ≤ T) (V W : Curve0 T) (s : ℝ) :
    sourceFun hT (V + W) s = sourceFun hT V s + sourceFun hT W s := rfl

theorem sourceFun_smul {T : ℝ} (hT : 0 ≤ T) (r : ℝ) (V : Curve0 T) (s : ℝ) :
    sourceFun hT (r • V) s = r • sourceFun hT V s := rfl

/-! ## The Duhamel operator -/

/-- The value of the Duhamel operator at one time. -/
noncomputable def duhamelCurveFun {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (V : Curve0 T) (t : TimeI T) : RealWiener1 :=
  RealWiener1.mk (duhamelIntegral hα.le (t : ℝ) (sourceFun hT V))
    (conjSymmetric_duhamelIntegral hα t.2.1 (continuous_sourceFun hT V)
      (fun s => norm_sourceFun_le hT V s) (conjSymmetric_sourceFun hT V))

@[simp] theorem duhamelCurveFun_val {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (V : Curve0 T) (t : TimeI T) :
    (duhamelCurveFun hα hT V t).val = duhamelIntegral hα.le (t : ℝ) (sourceFun hT V) := rfl

theorem continuous_duhamelCurveFun {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (V : Curve0 T) : Continuous (duhamelCurveFun hα hT V) := by
  refine (RealWiener1.isometry_val.isUniformInducing.isInducing.continuous_iff).2 ?_
  have h : Continuous fun t : ℝ => duhamelIntegral hα.le t (sourceFun hT V) :=
    continuous_duhamelIntegral hα (continuous_sourceFun hT V)
      (fun s => norm_sourceFun_le hT V s)
  exact h.comp continuous_subtype_val

/-- The Duhamel operator, as a map of curves. -/
noncomputable def duhamelCurve {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (V : Curve0 T) : Curve1 T :=
  curveOfContinuous (duhamelCurveFun hα hT V) (continuous_duhamelCurveFun hα hT V)

@[simp] theorem duhamelCurve_apply {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (V : Curve0 T) (t : TimeI T) :
    duhamelCurve hα hT V t = duhamelCurveFun hα hT V t := rfl

theorem duhamelCurve_add {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) (V W : Curve0 T) :
    duhamelCurve hα hT (V + W) = duhamelCurve hα hT V + duhamelCurve hα hT W := by
  ext t
  apply RealWiener1.val_injective
  show duhamelIntegral hα.le (t : ℝ) (sourceFun hT (V + W))
    = (duhamelCurveFun hα hT V t + duhamelCurveFun hα hT W t).val
  rw [RealWiener1.val_add, duhamelCurveFun_val, duhamelCurveFun_val]
  have hEq : (fun s => sourceFun hT (V + W) s)
      = fun s => sourceFun hT V s + sourceFun hT W s := by
    funext s; exact sourceFun_add hT V W s
  rw [show sourceFun hT (V + W) = fun s => sourceFun hT V s + sourceFun hT W s from hEq]
  exact duhamelIntegral_add hα t.2.1 (continuous_sourceFun hT V) (continuous_sourceFun hT W)
    (fun s => norm_sourceFun_le hT V s) (fun s => norm_sourceFun_le hT W s)

theorem duhamelCurve_smul {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) (r : ℝ)
    (V : Curve0 T) : duhamelCurve hα hT (r • V) = r • duhamelCurve hα hT V := by
  ext t
  apply RealWiener1.val_injective
  show duhamelIntegral hα.le (t : ℝ) (sourceFun hT (r • V))
    = (r • duhamelCurveFun hα hT V t).val
  rw [RealWiener1.val_smul, duhamelCurveFun_val]
  have hEq : (fun s => sourceFun hT (r • V) s) = fun s => r • sourceFun hT V s := by
    funext s; exact sourceFun_smul hT r V s
  rw [show sourceFun hT (r • V) = fun s => r • sourceFun hT V s from hEq]
  exact duhamelIntegral_real_smul hα.le (t : ℝ) r (sourceFun hT V)

theorem norm_duhamelCurve_le {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T) :
    ‖duhamelCurve hα hT V‖ ≤ duhamelConst α T * ‖V‖ := by
  have hV0 : (0:ℝ) ≤ ‖V‖ := norm_nonneg _
  have hG0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  refine (norm_le (by positivity)).2 (fun t => ?_)
  show ‖duhamelCurveFun hα hT V t‖ ≤ duhamelConst α T * ‖V‖
  show ‖duhamelIntegral hα.le (t : ℝ) (sourceFun hT V)‖ ≤ duhamelConst α T * ‖V‖
  refine le_trans (norm_duhamelIntegral_le hα t.2.1 (fun s => norm_sourceFun_le hT V s)) ?_
  calc ‖V‖ * duhamelConst α (t : ℝ)
      ≤ ‖V‖ * duhamelConst α T :=
        mul_le_mul_of_nonneg_left (duhamelConst_mono hα t.2.1 t.2.2) hV0
    _ = duhamelConst α T * ‖V‖ := mul_comm _ _

/-- **The Duhamel operator** `J_T : Y_T →L[ℝ] X_T`. -/
noncomputable def duhamelOp {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) :
    Curve0 T →L[ℝ] Curve1 T :=
  LinearMap.mkContinuous
    { toFun := duhamelCurve hα hT
      map_add' := duhamelCurve_add hα hT
      map_smul' := fun r V => duhamelCurve_smul hα hT r V }
    (duhamelConst α T) (fun V => norm_duhamelCurve_le hα hT V)

@[simp] theorem duhamelOp_apply {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T)
    (t : TimeI T) :
    (duhamelOp hα hT V) t = duhamelCurveFun hα hT V t := rfl

/-- **Evaluation identity**: the Duhamel operator is the actual Bochner integral. -/
theorem duhamelOp_apply_val {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T)
    (t : TimeI T) :
    ((duhamelOp hα hT V) t).val = duhamelIntegral hα.le (t : ℝ) (sourceFun hT V) := rfl

/-- **The operator norm bound** `‖J_T‖ ≤ duhamelConst α T`. -/
theorem norm_duhamelOp_le {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) :
    ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ ≤ duhamelConst α T :=
  LinearMap.mkContinuous_norm_le _ (duhamelConst_nonneg hα hT) _

/-- **Zero initial value**: the Duhamel term vanishes at `t = 0`. -/
theorem duhamelOp_zero_time {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T) :
    (duhamelOp hα hT V) ⟨0, ⟨le_rfl, hT⟩⟩ = 0 := by
  apply RealWiener1.val_injective
  rw [duhamelOp_apply_val]
  show duhamelIntegral hα.le (0:ℝ) (sourceFun hT V) = (0 : RealWiener1).val
  rw [duhamelIntegral, intervalIntegral.integral_same, RealWiener1.val_zero]

/-- **Independence of the extension.**  Any continuous bounded source that agrees with `V` on
`[0,T]` gives the same Duhamel value at every time of `[0,T]`. -/
theorem duhamelOp_eq_of_agrees {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) (V : Curve0 T)
    {g : ℝ → Wiener} (hg : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) T), g s = (V ⟨s, hs⟩).val)
    (t : TimeI T) :
    ((duhamelOp hα hT V) t).val = duhamelIntegral hα.le (t : ℝ) g := by
  rw [duhamelOp_apply_val]
  refine duhamelIntegral_congr hα.le t.2.1 (fun s hs => ?_)
  have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, le_trans hs.2 t.2.2⟩
  rw [sourceFun]
  have hclamp : clampT hT s = ⟨s, hsT⟩ := Subtype.ext (clampT_coe hT hsT.1 hsT.2)
  rw [hclamp, hg s hsT]

/-! ## The quadratic part `B_K = J_T ∘ N_K` -/

/-- **The concrete quadratic operator of the mild equation**, `B_K(u,v) = J_T(N_K(u,v))`. -/
noncomputable def sourceQuad {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve1 T :=
  (ContinuousLinearMap.compL ℝ (Curve1 T) (Curve0 T) (Curve1 T)
    (duhamelOp hα hT)).comp (spacetimeTransport m hm hr)

@[simp] theorem sourceQuad_apply {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) (U V : Curve1 T) :
    sourceQuad hα hT m hm hr U V = duhamelOp hα hT (spacetimeTransport m hm hr U V) := rfl

theorem sourceQuad_apply_time {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) (U V : Curve1 T)
    (t : TimeI T) :
    (sourceQuad hα hT m hm hr U V t).val
      = duhamelIntegral hα.le (t : ℝ) (sourceFun hT (spacetimeTransport m hm hr U V)) := rfl

/-- **The norm of the quadratic operator.** -/
theorem norm_sourceQuad_le {α : ℝ} (hα : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T)
    {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) :
    ‖(sourceQuad hα hT m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve1 T)‖
      ≤ duhamelConst α T * (4 * Real.pi * C) := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hG0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  have hpi := Real.pi_pos
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) (fun U V => ?_)
  have h1 : ‖sourceQuad hα hT m hm hr U V‖
      ≤ duhamelConst α T * ‖spacetimeTransport m hm hr U V‖ := by
    rw [sourceQuad_apply]
    exact norm_duhamelCurve_le hα hT _
  have h2 : ‖spacetimeTransport m hm hr U V‖ ≤ 4 * Real.pi * C * ‖U‖ * ‖V‖ := by
    refine le_trans (ContinuousLinearMap.le_opNorm₂ _ U V) ?_
    have := norm_spacetimeTransport_le (T := T) hm hr hC
    have hUV : (0:ℝ) ≤ ‖U‖ * ‖V‖ := by positivity
    calc ‖(spacetimeTransport m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T)‖ * ‖U‖ * ‖V‖
        = ‖(spacetimeTransport m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T)‖
            * (‖U‖ * ‖V‖) := by ring
      _ ≤ (4 * Real.pi * C) * (‖U‖ * ‖V‖) := mul_le_mul_of_nonneg_right this hUV
      _ = 4 * Real.pi * C * ‖U‖ * ‖V‖ := by ring
  calc ‖sourceQuad hα hT m hm hr U V‖
      ≤ duhamelConst α T * ‖spacetimeTransport m hm hr U V‖ := h1
    _ ≤ duhamelConst α T * (4 * Real.pi * C * ‖U‖ * ‖V‖) :=
        mul_le_mul_of_nonneg_left h2 hG0
    _ = duhamelConst α T * (4 * Real.pi * C) * ‖U‖ * ‖V‖ := by ring

end LiWang.WienerModel
