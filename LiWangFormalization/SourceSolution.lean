/-
# The source-to-solution map

Fix `T > 0` and `1/2 < α`.  With zero initial datum the forced mild equation reads

    u + B_K(u,u) = J_T f ,

with `J_T` and `B_K` the concrete operators of `DuhamelOperator.lean`.  Writing
`Ψ(u) = u + B_K(u,u)` — a genuine quadratic polynomial map of curves with `DΨ(0) = id` — the
inverse function theorem produces a `C²` local inverse, and

    S_K(f) = Ψ⁻¹(J_T f)

is the **source-to-solution map**.  Everything here is for one prescribed horizon `T`: the
source neighbourhood shrinks, never the time interval.

Part of `LiWangFormalizationSourceResponsePacket` v3.0.
-/
import LiWangFormalization.DuhamelOperator
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal
open Filter Topology BoundedContinuousFunction

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## The state map `Ψ(u) = u + B_K(u,u)` -/

/-- The state map of the forced mild equation with zero initial datum. -/
noncomputable def stateMap (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) : Curve1 T :=
  u + quad (sourceQuad hα hT m hm hr) u

theorem stateMap_apply (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) :
    stateMap hα hT hm hr u = u + sourceQuad hα hT m hm hr u u := rfl

@[simp] theorem stateMap_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : stateMap hα hT hm hr (0 : Curve1 T) = 0 := by
  rw [stateMap, quad_zero, add_zero]

theorem contDiff_stateMap (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (n : WithTop ℕ∞) :
    ContDiff ℝ n (stateMap hα hT hm hr) :=
  contDiff_id.add (contDiff_quad (sourceQuad hα hT m hm hr) n)

theorem hasFDerivAt_stateMap_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    HasFDerivAt (stateMap hα hT hm hr)
      ((ContinuousLinearEquiv.refl ℝ (Curve1 T) : Curve1 T ≃L[ℝ] Curve1 T) :
        Curve1 T →L[ℝ] Curve1 T) (0 : Curve1 T) := by
  have hq := hasFDerivAt_quad (sourceQuad hα hT m hm hr) (0 : Curve1 T)
  have hz : (sourceQuad hα hT m hm hr) 0 + (sourceQuad hα hT m hm hr).flip 0 = 0 := by
    rw [map_zero, map_zero, add_zero]
  rw [hz] at hq
  have h := (hasFDerivAt_id (0 : Curve1 T)).add hq
  rw [add_zero] at h
  simpa only [ContinuousLinearEquiv.coe_refl] using h

/-! ## The local inverse and the source-to-solution map -/

theorem two_ne_zero_withTop : (2 : WithTop ℕ∞) ≠ 0 := by decide

/-- The local inverse of the state map, produced by the inverse function theorem. -/
noncomputable def stateInverse (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : Curve1 T → Curve1 T :=
  ((contDiff_stateMap hα hT hm hr 2).contDiffAt).localInverse
    (hasFDerivAt_stateMap_zero hα hT hm hr) two_ne_zero_withTop

theorem stateInverse_stateMap_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : stateInverse hα hT hm hr (0 : Curve1 T) = 0 := by
  have h := ((contDiff_stateMap hα hT hm hr 2).contDiffAt).localInverse_apply_image
    (hasFDerivAt_stateMap_zero hα hT hm hr) two_ne_zero_withTop
  rw [stateMap_zero] at h
  exact h

theorem contDiffAt_stateInverse (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : ContDiffAt ℝ 2 (stateInverse hα hT hm hr) (0 : Curve1 T) := by
  have h := ((contDiff_stateMap hα hT hm hr 2).contDiffAt).to_localInverse
    (hasFDerivAt_stateMap_zero hα hT hm hr) two_ne_zero_withTop
  rw [stateMap_zero] at h
  exact h

theorem hasStrictFDerivAt_stateInverse (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    HasStrictFDerivAt (stateInverse hα hT hm hr)
      (ContinuousLinearMap.id ℝ (Curve1 T)) (0 : Curve1 T) := by
  have hs := ((contDiff_stateMap hα hT hm hr 2).contDiffAt).hasStrictFDerivAt'
    (hasFDerivAt_stateMap_zero hα hT hm hr) two_ne_zero_withTop
  have h := hs.to_localInverse
  rw [stateMap_zero] at h
  simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl] using h

theorem eventually_stateMap_stateInverse (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    ∀ᶠ v in 𝓝 (0 : Curve1 T), stateMap hα hT hm hr (stateInverse hα hT hm hr v) = v := by
  have hs := ((contDiff_stateMap hα hT hm hr 2).contDiffAt).hasStrictFDerivAt'
    (hasFDerivAt_stateMap_zero hα hT hm hr) two_ne_zero_withTop
  have h := hs.eventually_right_inverse
  rw [stateMap_zero] at h
  exact h

/-- **The source-to-solution map** `S_K = Ψ⁻¹ ∘ J_T`. -/
noncomputable def sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (f : Curve0 T) : Curve1 T :=
  stateInverse hα hT hm hr (duhamelOp hα hT f)

@[simp] theorem sourceSolution_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : sourceSolution hα hT hm hr (0 : Curve0 T) = 0 := by
  rw [sourceSolution, map_zero, stateInverse_stateMap_zero]

/-- **The mild equation holds on a neighbourhood of the zero source.** -/
theorem eventually_sourceSolution_eq (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    ∀ᶠ f in 𝓝 (0 : Curve0 T),
      sourceSolution hα hT hm hr f
        + sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f)
            (sourceSolution hα hT hm hr f) = duhamelOp hα hT f := by
  have hJ : Tendsto (duhamelOp hα hT : Curve0 T → Curve1 T) (𝓝 0) (𝓝 0) := by
    have hc := (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T).continuous.tendsto (0 : Curve0 T)
    rwa [map_zero] at hc
  exact hJ.eventually (eventually_stateMap_stateInverse hα hT hm hr)

theorem contDiffAt_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    ContDiffAt ℝ 2 (sourceSolution hα hT hm hr) (0 : Curve0 T) := by
  have hJ : ContDiffAt ℝ 2 (duhamelOp hα hT : Curve0 T → Curve1 T) 0 :=
    (duhamelOp hα hT).contDiff.contDiffAt
  have hΦ : ContDiffAt ℝ 2 (stateInverse hα hT hm hr) ((duhamelOp hα hT) (0 : Curve0 T)) := by
    rw [map_zero]
    exact contDiffAt_stateInverse hα hT hm hr
  exact hΦ.comp _ hJ

/-- **The first source variation**: `DS_K(0) = J_T`. -/
theorem hasFDerivAt_sourceSolution_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    HasFDerivAt (sourceSolution hα hT hm hr)
      (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T) (0 : Curve0 T) := by
  have hΦ : HasFDerivAt (stateInverse hα hT hm hr) (ContinuousLinearMap.id ℝ (Curve1 T))
      ((duhamelOp hα hT) (0 : Curve0 T)) := by
    rw [map_zero]
    exact (hasStrictFDerivAt_stateInverse hα hT hm hr).hasFDerivAt
  have h := hΦ.comp (0 : Curve0 T) (duhamelOp hα hT).hasFDerivAt
  simpa only [ContinuousLinearMap.id_comp] using h

theorem fderiv_sourceSolution_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) :
    fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T)
      = (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T) :=
  (hasFDerivAt_sourceSolution_zero hα hT hm hr).fderiv

/-! ## Explicit ball estimates: uniqueness, stability, existence

These are elementary consequences of the quadratic structure and hold for a *prescribed*
horizon `T`; only the size of the source is restricted. -/

theorem norm_quad_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) (u v : E) :
    ‖quad B u - quad B v‖ ≤ ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [quad_sub_quad B u v]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖B (u - v) u‖ ≤ ‖B‖ * ‖u - v‖ * ‖u‖ := B.le_opNorm₂ _ _
  have h2 : ‖B v (u - v)‖ ≤ ‖B‖ * ‖v‖ * ‖u - v‖ := B.le_opNorm₂ _ _
  have hr : ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖
      = ‖B‖ * ‖u - v‖ * ‖u‖ + ‖B‖ * ‖v‖ * ‖u - v‖ := by ring
  rw [hr]
  exact add_le_add h1 h2

/-- **Uniqueness in an explicit ball.** -/
theorem mild_curve_unique_ball (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {b r : ℝ} (hb : ‖(sourceQuad hα hT m hm hr)‖ ≤ b)
    (hbr : 2 * b * r ≤ 1 / 2) {u v : Curve1 T} (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r)
    (f : Curve0 T)
    (heu : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hev : v + sourceQuad hα hT m hm hr v v = duhamelOp hα hT f) : u = v := by
  have hb0 : (0:ℝ) ≤ b := le_trans (norm_nonneg (sourceQuad hα hT m hm hr)) hb
  have hdiff : u - v = -(quad (sourceQuad hα hT m hm hr) u - quad (sourceQuad hα hT m hm hr) v) := by
    have h : u + quad (sourceQuad hα hT m hm hr) u = v + quad (sourceQuad hα hT m hm hr) v := by
      rw [show quad (sourceQuad hα hT m hm hr) u = sourceQuad hα hT m hm hr u u from rfl,
        show quad (sourceQuad hα hT m hm hr) v = sourceQuad hα hT m hm hr v v from rfl, heu, hev]
    have := sub_eq_zero.2 h
    rw [show u + quad (sourceQuad hα hT m hm hr) u - (v + quad (sourceQuad hα hT m hm hr) v)
      = (u - v) + (quad (sourceQuad hα hT m hm hr) u - quad (sourceQuad hα hT m hm hr) v) from by
        abel] at this
    linear_combination (norm := abel) this
  have hsum : ‖u‖ + ‖v‖ ≤ 2 * r := by linarith
  have hd0 : (0:ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have hnn : (0:ℝ) ≤ ‖u‖ + ‖v‖ := by positivity
  have h1 : ‖(sourceQuad hα hT m hm hr)‖ * (‖u‖ + ‖v‖) ≤ b * (2 * r) :=
    le_trans (mul_le_mul_of_nonneg_right hb hnn) (mul_le_mul_of_nonneg_left hsum hb0)
  have hnorm : ‖u - v‖ ≤ (2 * b * r) * ‖u - v‖ := by
    calc ‖u - v‖ = ‖quad (sourceQuad hα hT m hm hr) u - quad (sourceQuad hα hT m hm hr) v‖ := by
          rw [hdiff, norm_neg]
      _ ≤ ‖(sourceQuad hα hT m hm hr)‖ * (‖u‖ + ‖v‖) * ‖u - v‖ :=
          norm_quad_sub_le (sourceQuad hα hT m hm hr) u v
      _ ≤ (b * (2 * r)) * ‖u - v‖ := mul_le_mul_of_nonneg_right h1 hd0
      _ = (2 * b * r) * ‖u - v‖ := by ring
  have hd0 : (0:ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have : ‖u - v‖ ≤ (1/2) * ‖u - v‖ := le_trans hnorm (mul_le_mul_of_nonneg_right hbr hd0)
  have hzero : ‖u - v‖ = 0 := le_antisymm (by linarith) hd0
  exact sub_eq_zero.1 (norm_eq_zero.1 hzero)

/-- **Lipschitz dependence on the source** inside an explicit ball. -/
theorem mild_curve_lipschitz (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {b r : ℝ} (hb : ‖(sourceQuad hα hT m hm hr)‖ ≤ b)
    (hbr : 2 * b * r ≤ 1 / 2) {u v : Curve1 T} (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r)
    (f g : Curve0 T)
    (heu : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hev : v + sourceQuad hα hT m hm hr v v = duhamelOp hα hT g) :
    ‖u - v‖ ≤ 2 * (duhamelConst α T * ‖f - g‖) := by
  have hb0 : (0:ℝ) ≤ b := le_trans (norm_nonneg (sourceQuad hα hT m hm hr)) hb
  have hd0 : (0:ℝ) ≤ ‖u - v‖ := norm_nonneg _
  have hsplit : u - v = (duhamelOp hα hT (f - g))
      - (quad (sourceQuad hα hT m hm hr) u - quad (sourceQuad hα hT m hm hr) v) := by
    have hq : ∀ w : Curve1 T, quad (sourceQuad hα hT m hm hr) w = sourceQuad hα hT m hm hr w w :=
      fun _ => rfl
    rw [hq, hq, map_sub]
    rw [← heu, ← hev]
    abel
  have hquad : ‖quad (sourceQuad hα hT m hm hr) u - quad (sourceQuad hα hT m hm hr) v‖
      ≤ (1/2) * ‖u - v‖ := by
    refine le_trans (norm_quad_sub_le (sourceQuad hα hT m hm hr) u v) ?_
    have hsum : ‖u‖ + ‖v‖ ≤ 2 * r := by linarith
    have hnn : (0:ℝ) ≤ ‖u‖ + ‖v‖ := by positivity
    have h1 : ‖(sourceQuad hα hT m hm hr)‖ * (‖u‖ + ‖v‖) ≤ b * (2 * r) :=
      le_trans (mul_le_mul_of_nonneg_right hb hnn) (mul_le_mul_of_nonneg_left hsum hb0)
    calc ‖(sourceQuad hα hT m hm hr)‖ * (‖u‖ + ‖v‖) * ‖u - v‖
        ≤ (b * (2 * r)) * ‖u - v‖ := mul_le_mul_of_nonneg_right h1 hd0
      _ = (2 * b * r) * ‖u - v‖ := by ring
      _ ≤ (1/2) * ‖u - v‖ := mul_le_mul_of_nonneg_right hbr hd0
  have hJ : ‖duhamelOp hα hT (f - g)‖ ≤ duhamelConst α T * ‖f - g‖ :=
    norm_duhamelCurve_le hα hT (f - g)
  have hstep : ‖u - v‖ ≤ duhamelConst α T * ‖f - g‖ + (1/2) * ‖u - v‖ := by
    calc ‖u - v‖ = ‖(duhamelOp hα hT (f - g))
            - (quad (sourceQuad hα hT m hm hr) u - quad (sourceQuad hα hT m hm hr) v)‖ := by
          rw [← hsplit]
      _ ≤ ‖duhamelOp hα hT (f - g)‖
            + ‖quad (sourceQuad hα hT m hm hr) u - quad (sourceQuad hα hT m hm hr) v‖ :=
          norm_sub_le _ _
      _ ≤ duhamelConst α T * ‖f - g‖ + (1/2) * ‖u - v‖ := add_le_add hJ hquad
  linarith

/-- **Existence in an explicit ball**, for any prescribed horizon `T`: only the source is
required to be small. -/
theorem exists_mild_curve_of_small (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {b : ℝ} (hb : ‖(sourceQuad hα hT m hm hr)‖ ≤ b) (hb0 : 0 ≤ b)
    (f : Curve0 T) (hf : ‖duhamelOp hα hT f‖ ≤ 1 / (8 * (b + 1))) :
    ∃ u : Curve1 T, ‖u‖ ≤ 1 / (4 * (b + 1)) ∧
      u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f := by
  set r : ℝ := 1 / (4 * (b + 1)) with hrdef
  have hb1 : (0:ℝ) < b + 1 := by linarith
  have hr0 : (0:ℝ) < r := by simp only [hrdef]; positivity
  have hbr : b * r ≤ 1 / 4 := by
    rw [hrdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the contraction
  set Θ : Curve1 T → Curve1 T := fun u => duhamelOp hα hT f - sourceQuad hα hT m hm hr u u
    with hΘ
  have hmaps : Set.MapsTo Θ (Metric.closedBall (0 : Curve1 T) r)
      (Metric.closedBall (0 : Curve1 T) r) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
    have hq : ‖sourceQuad hα hT m hm hr u u‖ ≤ b * r * r := by
      refine le_trans ((sourceQuad hα hT m hm hr).le_opNorm₂ u u) ?_
      have h1 : ‖(sourceQuad hα hT m hm hr)‖ * ‖u‖ ≤ b * r :=
        le_trans (mul_le_mul_of_nonneg_right hb (norm_nonneg u))
          (mul_le_mul_of_nonneg_left hu hb0)
      calc ‖(sourceQuad hα hT m hm hr)‖ * ‖u‖ * ‖u‖ ≤ (b * r) * ‖u‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg u)
        _ ≤ (b * r) * r := mul_le_mul_of_nonneg_left hu (by positivity)
        _ = b * r * r := by ring
    have hq2 : b * r * r ≤ (1/4) * r := mul_le_mul_of_nonneg_right hbr hr0.le
    have hval : r / 2 = 1 / (8 * (b + 1)) := by
      rw [hrdef]
      field_simp
      ring
    have hf2 : ‖duhamelOp hα hT f‖ ≤ r / 2 := by
      rw [hval]; exact hf
    calc ‖Θ u‖ ≤ ‖duhamelOp hα hT f‖ + ‖sourceQuad hα hT m hm hr u u‖ := norm_sub_le _ _
      _ ≤ r / 2 + (1/4) * r := add_le_add hf2 (le_trans hq hq2)
      _ ≤ r := by linarith
  have hlip : LipschitzWith (1 / 2 : ℝ≥0) (hmaps.restrict Θ _ _) := by
    refine LipschitzWith.of_dist_le_mul (fun u v => ?_)
    have hu := u.2
    have hv := v.2
    rw [Metric.mem_closedBall, dist_zero_right] at hu hv
    have hK : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [Subtype.dist_eq, Subtype.dist_eq, hK, dist_eq_norm, dist_eq_norm]
    have hsub : Θ u.1 - Θ v.1
        = -(quad (sourceQuad hα hT m hm hr) u.1 - quad (sourceQuad hα hT m hm hr) v.1) := by
      simp only [hΘ, quad]
      abel
    have hval : ‖(hmaps.restrict Θ _ _ u : Curve1 T) - (hmaps.restrict Θ _ _ v : Curve1 T)‖
        = ‖quad (sourceQuad hα hT m hm hr) u.1 - quad (sourceQuad hα hT m hm hr) v.1‖ := by
      show ‖Θ u.1 - Θ v.1‖ = _
      rw [hsub, norm_neg]
    rw [hval]
    refine le_trans (norm_quad_sub_le (sourceQuad hα hT m hm hr) u.1 v.1) ?_
    have hsum : ‖u.1‖ + ‖v.1‖ ≤ 2 * r := by linarith
    have hnn : (0:ℝ) ≤ ‖u.1‖ + ‖v.1‖ := by positivity
    have hd0 : (0:ℝ) ≤ ‖u.1 - v.1‖ := norm_nonneg _
    have h1 : ‖(sourceQuad hα hT m hm hr)‖ * (‖u.1‖ + ‖v.1‖) ≤ b * (2 * r) :=
      le_trans (mul_le_mul_of_nonneg_right hb hnn) (mul_le_mul_of_nonneg_left hsum hb0)
    calc ‖(sourceQuad hα hT m hm hr)‖ * (‖u.1‖ + ‖v.1‖) * ‖u.1 - v.1‖
        ≤ (b * (2 * r)) * ‖u.1 - v.1‖ := mul_le_mul_of_nonneg_right h1 hd0
      _ = 2 * (b * r) * ‖u.1 - v.1‖ := by ring
      _ ≤ 2 * (1/4) * ‖u.1 - v.1‖ :=
          mul_le_mul_of_nonneg_right (by linarith) hd0
      _ = 1 / 2 * ‖u.1 - v.1‖ := by ring
  have hsc : IsComplete (Metric.closedBall (0 : Curve1 T) r) :=
    Metric.isClosed_closedBall.isComplete
  have h0 : (0 : Curve1 T) ∈ Metric.closedBall (0 : Curve1 T) r := by
    rw [Metric.mem_closedBall, dist_self]; exact hr0.le
  obtain ⟨u, humem, hfix, -, -⟩ :=
    ContractingWith.exists_fixedPoint' hsc hmaps ⟨by norm_num, hlip⟩ h0 (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at humem
  refine ⟨u, humem, ?_⟩
  have hfix' : duhamelOp hα hT f - sourceQuad hα hT m hm hr u u = u := hfix
  have hrw : u + sourceQuad hα hT m hm hr u u
      = (duhamelOp hα hT f - sourceQuad hα hT m hm hr u u)
        + sourceQuad hα hT m hm hr u u := by rw [hfix']
  rw [hrw]
  abel

/-! ## The pointwise (v2-style) form of the equation -/

/-- The quadratic term, evaluated in Fourier coefficients at one time: it is the actual
Duhamel integral of the actual transport term. -/
theorem sourceQuad_val (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (U V : Curve1 T) (t : TimeI T) :
    (sourceQuad hα hT m hm hr U V t).val
      = duhamelIntegral hα.le (t : ℝ)
          (fun s => transport m hm (U (clampT hT s)).val (V (clampT hT s)).val) := by
  rw [sourceQuad_apply, duhamelOp_apply_val]
  congr 1

/-- **The curve equation is the pointwise mild equation.**  For every time of `[0,T]` and in
actual Fourier coefficients. -/
theorem mild_pointwise_of_curve (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (h : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (t : TimeI T) :
    (u t).val = duhamelIntegral hα.le (t : ℝ) (sourceFun hT f)
      - duhamelIntegral hα.le (t : ℝ)
          (fun s => transport m hm (u (clampT hT s)).val (u (clampT hT s)).val) := by
  have ht := congrArg (fun W : Curve1 T => (W t).val) h
  simp only [BoundedContinuousFunction.add_apply, RealWiener1.val_add] at ht
  rw [sourceQuad_val hα hT hm hr u u t, duhamelOp_apply_val] at ht
  rw [← ht]
  abel

/-- Conversely, the pointwise identity gives the curve equation. -/
theorem curve_of_mild_pointwise (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (h : ∀ t : TimeI T, (u t).val = duhamelIntegral hα.le (t : ℝ) (sourceFun hT f)
      - duhamelIntegral hα.le (t : ℝ)
          (fun s => transport m hm (u (clampT hT s)).val (u (clampT hT s)).val)) :
    u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f := by
  ext t
  apply RealWiener1.val_injective
  rw [BoundedContinuousFunction.add_apply, RealWiener1.val_add,
    sourceQuad_val hα hT hm hr u u t, duhamelOp_apply_val, h t]
  abel

/-! ## Agreement of the two constructions -/

/-- Near the zero source, the implicit-function solution `S_K(f)` is small. -/
theorem eventually_norm_sourceSolution_le (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {r : ℝ} (hr0 : 0 < r) :
    ∀ᶠ f in 𝓝 (0 : Curve0 T), ‖sourceSolution hα hT hm hr f‖ ≤ r := by
  have hc : ContinuousAt (sourceSolution hα hT hm hr) 0 :=
    (contDiffAt_sourceSolution hα hT hm hr).continuousAt
  have h0 : sourceSolution hα hT hm hr (0 : Curve0 T) = 0 := sourceSolution_zero hα hT hm hr
  have hmem : Metric.closedBall (0 : Curve1 T) r ∈ 𝓝 (sourceSolution hα hT hm hr 0) := by
    rw [h0]
    exact Metric.closedBall_mem_nhds _ hr0
  have := hc.preimage_mem_nhds hmem
  filter_upwards [this] with f hf
  rwa [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hf

/-- **Agreement**: any solution lying in the uniqueness ball coincides with `S_K(f)`. -/
theorem sourceSolution_eq_of_mem_ball (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {b r : ℝ} (hb : ‖(sourceQuad hα hT m hm hr)‖ ≤ b)
    (hbr : 2 * b * r ≤ 1 / 2) {f : Curve0 T} {u : Curve1 T}
    (hfS : sourceSolution hα hT hm hr f
      + sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f) (sourceSolution hα hT hm hr f)
        = duhamelOp hα hT f)
    (hSr : ‖sourceSolution hα hT hm hr f‖ ≤ r) (hur : ‖u‖ ≤ r)
    (hu : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    u = sourceSolution hα hT hm hr f :=
  mild_curve_unique_ball hα hT hm hr hb hbr hur hSr f hu hfS

end LiWang.Formalization
