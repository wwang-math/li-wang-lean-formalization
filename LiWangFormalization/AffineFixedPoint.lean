/-
# The abstract affine fixed point

The Banach fixed-point construction behind the local mild solution, carried out once for a
map of the shape

    Φ(u)(t) = A(t) - ∫₀^t e^{-(t-s)(-Δ)^α} N_m(u(s), u(s)) ds ,

where the **affine part** `A` is an arbitrary bounded continuous curve.  Taking
`A(t) = e^{-t(-Δ)^α}θ₀` gives the unforced equation (`LocalSolution.lean`); taking
`A(t) = e^{-t(-Δ)^α}θ₀ + ∫₀^t e^{-(t-s)(-Δ)^α}f(s)ds` gives the forced one
(`ForcedSolution.lean`).

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.MildSolution
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal
open Filter Topology MeasureTheory BoundedContinuousFunction

namespace LiWang.Formalization

/-! ## Clamping and extension of curves -/

/-- Clamp a real time to the compact interval `[0,T]`. -/
noncomputable def clampT {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : TimeI T :=
  ⟨min (max t 0) T, ⟨le_min (le_max_right t 0) hT, min_le_right _ _⟩⟩

theorem clampT_coe {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (h0 : 0 ≤ t) (htT : t ≤ T) :
    (clampT hT t : ℝ) = t := by
  simp only [clampT]
  rw [max_eq_left h0, min_eq_left htT]

theorem continuous_clampT {T : ℝ} (hT : 0 ≤ T) : Continuous (clampT hT) :=
  Continuous.subtype_mk ((continuous_id.max continuous_const).min continuous_const) _

/-- Extend a curve on `[0,T]` to all of `ℝ` by clamping the time variable. -/
noncomputable def extendCurve {T : ℝ} (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) (t : ℝ) : Wiener1 :=
  U (clampT hT t)

theorem continuous_extendCurve {T : ℝ} (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) :
    Continuous (extendCurve hT U) :=
  U.continuous.comp (continuous_clampT hT)

theorem norm_extendCurve_le {T : ℝ} (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) (t : ℝ) :
    ‖extendCurve hT U t‖ ≤ ‖U‖ := U.norm_coe_le_norm _

theorem extendCurve_coe {T : ℝ} (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) (t : TimeI T) :
    extendCurve hT U (t : ℝ) = U t := by
  rw [extendCurve]
  congr 1
  exact Subtype.ext (clampT_coe hT t.2.1 t.2.2)

theorem dist_extendCurve_le {T : ℝ} (hT : 0 ≤ T) (U V : TimeI T →ᵇ Wiener1) (t : ℝ) :
    ‖extendCurve hT U t - extendCurve hT V t‖ ≤ dist U V := by
  rw [← dist_eq_norm]
  exact dist_coe_le_dist _

/-- The Duhamel constant is monotone in time. -/
theorem duhamelConst_mono {α : ℝ} (hα : 1 / 2 < α) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    duhamelConst α t ≤ duhamelConst α T := by
  have hα0 : (0:ℝ) < α := by linarith
  have h2α : (1:ℝ) < 2 * α := by linarith
  have hβ : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
  have hexp : (0:ℝ) ≤ 1 - 1 / (2 * α) := by linarith
  have hpow : t ^ (1 - 1 / (2 * α)) ≤ T ^ (1 - 1 / (2 * α)) := Real.rpow_le_rpow ht htT hexp
  have hden : 0 < Real.pi * (1 - 1 / (2 * α)) := by
    have := Real.pi_pos
    have h1 : (0:ℝ) < 1 - 1 / (2 * α) := by linarith
    positivity
  have hdiv : t ^ (1 - 1 / (2 * α)) / (Real.pi * (1 - 1 / (2 * α)))
      ≤ T ^ (1 - 1 / (2 * α)) / (Real.pi * (1 - 1 / (2 * α))) :=
    div_le_div_of_nonneg_right hpow hden.le
  simp only [duhamelConst]
  linarith


/-- The Duhamel constant is nonnegative. -/
theorem duhamelConst_nonneg {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ duhamelConst α t := by
  have hα0 : (0:ℝ) < α := by linarith
  have h2α : (1:ℝ) < 2 * α := by linarith
  have hβ : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
  have h1 : (0:ℝ) ≤ t ^ (1 - 1 / (2 * α)) := Real.rpow_nonneg ht _
  have h2 : (0:ℝ) ≤ t ^ (1 - 1 / (2 * α)) / (Real.pi * (1 - 1 / (2 * α))) := by
    refine div_nonneg h1 ?_
    have h3 : (0:ℝ) < 1 - 1 / (2 * α) := by linarith
    positivity
  simp only [duhamelConst]
  linarith

/-! ## The affine mild map -/

/-- The mild map with an abstract affine part. -/
noncomputable def affineMildMap {α : ℝ} (hα : 1 / 2 ≤ α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) (A : ℝ → Wiener1) (u : ℝ → Wiener1) (t : ℝ) : Wiener1 :=
  A t - duhamelIntegral hα t (quadCurve hm u)

theorem continuous_affineMildMap {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {A : ℝ → Wiener1}
    (hA : Continuous A) {u : ℝ → Wiener1} (hu : Continuous u) {R : ℝ}
    (hR : ∀ s, ‖u s‖ ≤ R) :
    Continuous fun t : ℝ => affineMildMap hα.le hm A u t :=
  hA.sub (continuous_duhamelIntegral hα (continuous_quadCurve hm hu)
    (fun s => norm_quadCurve_le hm hC hR s))

theorem norm_affineMildMap_le {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {A : ℝ → Wiener1} {a : ℝ}
    (haA : ∀ t, ‖A t‖ ≤ a) {u : ℝ → Wiener1} {R : ℝ} (hR : ∀ s, ‖u s‖ ≤ R) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖affineMildMap hα.le hm A u t‖ ≤ a + (4 * Real.pi * C * R * R) * duhamelConst α t := by
  refine le_trans (norm_sub_le _ _) (add_le_add (haA t) ?_)
  exact norm_duhamelIntegral_le hα ht (fun s => norm_quadCurve_le hm hC hR s)

theorem norm_affineMildMap_sub_le {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (A : ℝ → Wiener1)
    {u v : ℝ → Wiener1} (hu : Continuous u) (hv : Continuous v) {R : ℝ}
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R) {D : ℝ} (hD : ∀ s, ‖u s - v s‖ ≤ D)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖affineMildMap hα.le hm A u t - affineMildMap hα.le hm A v t‖
      ≤ (8 * Real.pi * C * R * D) * duhamelConst α t := by
  have hcancel : affineMildMap hα.le hm A u t - affineMildMap hα.le hm A v t
      = -(duhamelIntegral hα.le t (quadCurve hm u)
          - duhamelIntegral hα.le t (quadCurve hm v)) := by
    simp only [affineMildMap]
    abel
  rw [hcancel, norm_neg]
  refine norm_duhamelIntegral_sub_le hα ht (continuous_quadCurve hm hu)
    (continuous_quadCurve hm hv) (fun s => norm_quadCurve_le hm hC hRu s)
    (fun s => norm_quadCurve_le hm hC hRv s) (fun s => ?_)
  exact le_trans (norm_quadCurve_sub_le hm hC hRu hRv s)
    (mul_le_mul_of_nonneg_left (hD s) (by
      have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
      have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hRu 0)
      have hpi := Real.pi_pos
      positivity))

/-- The affine mild map as a map of bounded continuous curves on `[0,T]`. -/
noncomputable def affineCurveMap {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (A : ℝ → Wiener1)
    (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) : TimeI T →ᵇ Wiener1 :=
  mkOfCompact ⟨fun t : TimeI T => affineMildMap hα.le hm A (extendCurve hT U) (t : ℝ),
    (continuous_affineMildMap hα hm hC hA (continuous_extendCurve hT U)
      (fun s => norm_extendCurve_le hT U s)).comp continuous_subtype_val⟩

@[simp] theorem affineCurveMap_apply {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (A : ℝ → Wiener1)
    (hA : Continuous A) {T : ℝ} (hT : 0 ≤ T) (U : TimeI T →ᵇ Wiener1) (t : TimeI T) :
    affineCurveMap hα hm hC A hA hT U t
      = affineMildMap hα.le hm A (extendCurve hT U) (t : ℝ) := rfl

/-! ## The fixed point -/

/-- **The abstract contraction argument.**  If the affine part is bounded by `a` and the
Duhamel constant is small enough on `[0,T]`, then the affine mild map maps the ball of radius
`2a+1` of curves into itself and has a fixed point there, reached by the Banach iterates
started at `0`. -/
theorem exists_affineCurve_fixedPoint {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (A : ℝ → Wiener1)
    (hA : Continuous A) {a : ℝ} (haA : ∀ t, ‖A t‖ ≤ a) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T,
      (8 * Real.pi * C * (2 * a + 1) + 4 * Real.pi * C * (2 * a + 1) * (2 * a + 1))
        * duhamelConst α t ≤ 1 / 2) :
    (∀ V : TimeI T →ᵇ Wiener1, ‖V‖ ≤ 2 * a + 1 →
        ‖affineCurveMap hα hm hC A hA hT V‖ ≤ 2 * a + 1) ∧
    ∃ U : TimeI T →ᵇ Wiener1, ‖U‖ ≤ 2 * a + 1 ∧
      affineCurveMap hα hm hC A hA hT U = U ∧
      Tendsto (fun n : ℕ => (affineCurveMap hα hm hC A hA hT)^[n] 0) atTop (𝓝 U) := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hpi := Real.pi_pos
  have ha0 : (0:ℝ) ≤ a := le_trans (norm_nonneg _) (haA 0)
  set R : ℝ := 2 * a + 1 with hRdef
  have hR1 : (1:ℝ) ≤ R := by simp only [hRdef]; linarith
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hquad : ∀ t ∈ Set.Icc (0:ℝ) T,
      (4 * Real.pi * C * R * R) * duhamelConst α t ≤ 1 / 2 := by
    intro t ht
    have h := hsmall t ht
    have hg : 0 ≤ duhamelConst α t := by
      have h1 : (0:ℝ) ≤ t ^ (1 - 1 / (2 * α)) := Real.rpow_nonneg ht.1 _
      have hα0 : (0:ℝ) < α := by linarith
      have h2α : (1:ℝ) < 2 * α := by linarith
      have hβ : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
      have h2 : (0:ℝ) ≤ t ^ (1 - 1 / (2 * α)) / (Real.pi * (1 - 1 / (2 * α))) := by
        apply div_nonneg h1
        have : (0:ℝ) < 1 - 1 / (2 * α) := by linarith
        positivity
      simp only [duhamelConst]
      linarith [ht.1]
    have hnn : 0 ≤ (8 * Real.pi * C * R) * duhamelConst α t := by positivity
    nlinarith [hnn]
  have hlin : ∀ t ∈ Set.Icc (0:ℝ) T,
      (8 * Real.pi * C * R) * duhamelConst α t ≤ 1 / 2 := by
    intro t ht
    have h := hsmall t ht
    have hg : 0 ≤ duhamelConst α t := by
      have h1 : (0:ℝ) ≤ t ^ (1 - 1 / (2 * α)) := Real.rpow_nonneg ht.1 _
      have hα0 : (0:ℝ) < α := by linarith
      have h2α : (1:ℝ) < 2 * α := by linarith
      have hβ : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
      have h2 : (0:ℝ) ≤ t ^ (1 - 1 / (2 * α)) / (Real.pi * (1 - 1 / (2 * α))) := by
        apply div_nonneg h1
        have : (0:ℝ) < 1 - 1 / (2 * α) := by linarith
        positivity
      simp only [duhamelConst]
      linarith [ht.1]
    have hnn : 0 ≤ (4 * Real.pi * C * R * R) * duhamelConst α t := by positivity
    nlinarith [hnn]
  have hsc : IsComplete (Metric.closedBall (0 : TimeI T →ᵇ Wiener1) R) :=
    Metric.isClosed_closedBall.isComplete
  have hmaps : Set.MapsTo (affineCurveMap hα hm hC A hA hT)
      (Metric.closedBall (0 : TimeI T →ᵇ Wiener1) R)
      (Metric.closedBall (0 : TimeI T →ᵇ Wiener1) R) := by
    intro U hU
    rw [Metric.mem_closedBall, dist_zero_right] at hU ⊢
    refine (norm_le hR0.le).2 (fun t => ?_)
    have hRU : ∀ x : ℝ, ‖extendCurve hT U x‖ ≤ R := fun x =>
      le_trans (norm_extendCurve_le hT U x) hU
    have hb := norm_affineMildMap_le hα hm hC haA hRU t.2.1
    have h2 := hquad (t : ℝ) t.2
    have happ : affineCurveMap hα hm hC A hA hT U t
        = affineMildMap hα.le hm A (extendCurve hT U) (t : ℝ) := rfl
    rw [happ]
    simp only [hRdef] at hb ⊢
    linarith
  have hballmaps : ∀ V : TimeI T →ᵇ Wiener1, ‖V‖ ≤ R →
      ‖affineCurveMap hα hm hC A hA hT V‖ ≤ R := by
    intro V hV
    have hmem : V ∈ Metric.closedBall (0 : TimeI T →ᵇ Wiener1) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hV
    have := hmaps hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hlip : LipschitzWith (1 / 2 : ℝ≥0)
      (hmaps.restrict (affineCurveMap hα hm hC A hA hT) _ _) := by
    refine LipschitzWith.of_dist_le_mul (fun U V => ?_)
    have hU := U.2
    have hV := V.2
    rw [Metric.mem_closedBall, dist_zero_right] at hU hV
    have hRU : ∀ x : ℝ, ‖extendCurve hT U.1 x‖ ≤ R := fun x =>
      le_trans (norm_extendCurve_le hT U.1 x) hU
    have hRV : ∀ x : ℝ, ‖extendCurve hT V.1 x‖ ≤ R := fun x =>
      le_trans (norm_extendCurve_le hT V.1 x) hV
    have hD : ∀ x : ℝ, ‖extendCurve hT U.1 x - extendCurve hT V.1 x‖ ≤ dist U.1 V.1 :=
      fun x => dist_extendCurve_le hT U.1 V.1 x
    have hd0 : (0:ℝ) ≤ dist U.1 V.1 := dist_nonneg
    have hK : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [Subtype.dist_eq, Subtype.dist_eq, hK]
    refine (dist_le (by positivity)).2 (fun t => ?_)
    rw [dist_eq_norm]
    have hb := norm_affineMildMap_sub_le hα hm hC A (continuous_extendCurve hT U.1)
      (continuous_extendCurve hT V.1) hRU hRV hD t.2.1
    have h2 : (8 * Real.pi * C * R * dist U.1 V.1) * duhamelConst α (t : ℝ)
        ≤ 1 / 2 * dist U.1 V.1 := by
      have hs := hlin (t : ℝ) t.2
      calc (8 * Real.pi * C * R * dist U.1 V.1) * duhamelConst α (t : ℝ)
          = dist U.1 V.1 * ((8 * Real.pi * C * R) * duhamelConst α (t : ℝ)) := by ring
        _ ≤ dist U.1 V.1 * (1 / 2) := mul_le_mul_of_nonneg_left hs hd0
        _ = 1 / 2 * dist U.1 V.1 := by ring
    have happ : ∀ W : Metric.closedBall (0 : TimeI T →ᵇ Wiener1) R,
        (hmaps.restrict (affineCurveMap hα hm hC A hA hT) _ _ W : TimeI T →ᵇ Wiener1) t
          = affineMildMap hα.le hm A (extendCurve hT W.1) (t : ℝ) := fun W => rfl
    rw [happ U, happ V]
    linarith
  have h0s : (0 : TimeI T →ᵇ Wiener1) ∈ Metric.closedBall (0 : TimeI T →ᵇ Wiener1) R := by
    rw [Metric.mem_closedBall, dist_self]
    exact hR0.le
  obtain ⟨U, hUmem, hfix, htend, -⟩ :=
    ContractingWith.exists_fixedPoint' hsc hmaps ⟨by norm_num, hlip⟩ h0s (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at hUmem
  exact ⟨hballmaps, U, hUmem, hfix, htend⟩

/-! ## Uniqueness for the abstract affine equation -/

/-- The Duhamel term only sees the curve on `[0,t]`. -/
theorem duhamelIntegral_quadCurve_congr {α : ℝ} (hα : 1 / 2 ≤ α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {t : ℝ} (ht : 0 ≤ t) {w w' : ℝ → Wiener1}
    (hww : ∀ s ∈ Set.Icc (0:ℝ) t, w s = w' s) :
    duhamelIntegral hα t (quadCurve hm w) = duhamelIntegral hα t (quadCurve hm w') := by
  rw [duhamelIntegral, duhamelIntegral]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [Set.uIcc_of_le ht] at hs
  show heatSmoothFun hα (t - s) (quadCurve hm w s)
    = heatSmoothFun hα (t - s) (quadCurve hm w' s)
  rw [quadCurve, quadCurve, hww s hs]

/-- **Uniqueness for the affine equation** on a time interval where the contraction factor is
at most `1/2`: two bounded continuous curves with the same affine part coincide on `[0,T]`. -/
theorem affine_solution_unique {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (A : ℝ → Wiener1) {R T : ℝ}
    (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2)
    {u v : ℝ → Wiener1} (hu : Continuous u) (hv : Continuous v)
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R)
    (heu : ∀ t ∈ Set.Icc (0:ℝ) T, u t = A t - duhamelIntegral hα.le t (quadCurve hm u))
    (hev : ∀ t ∈ Set.Icc (0:ℝ) T, v t = A t - duhamelIntegral hα.le t (quadCurve hm v)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t := by
  have hUc : Continuous fun t : TimeI T => u (t : ℝ) := hu.comp continuous_subtype_val
  have hVc : Continuous fun t : TimeI T => v (t : ℝ) := hv.comp continuous_subtype_val
  set Ur : TimeI T →ᵇ Wiener1 := mkOfCompact ⟨fun t : TimeI T => u (t : ℝ), hUc⟩ with hUrdef
  set Vr : TimeI T →ᵇ Wiener1 := mkOfCompact ⟨fun t : TimeI T => v (t : ℝ), hVc⟩ with hVrdef
  have hD0 : (0:ℝ) ≤ dist Ur Vr := dist_nonneg
  have hextu : ∀ s : ℝ, extendCurve hT Ur s = u ((clampT hT s : ℝ)) := fun _ => rfl
  have hextv : ∀ s : ℝ, extendCurve hT Vr s = v ((clampT hT s : ℝ)) := fun _ => rfl
  have hagree_u : ∀ s ∈ Set.Icc (0:ℝ) T, extendCurve hT Ur s = u s := by
    intro s hs; rw [hextu, clampT_coe hT hs.1 hs.2]
  have hagree_v : ∀ s ∈ Set.Icc (0:ℝ) T, extendCurve hT Vr s = v s := by
    intro s hs; rw [hextv, clampT_coe hT hs.1 hs.2]
  have hRU : ∀ s : ℝ, ‖extendCurve hT Ur s‖ ≤ R := fun s => by rw [hextu]; exact hRu _
  have hRV : ∀ s : ℝ, ‖extendCurve hT Vr s‖ ≤ R := fun s => by rw [hextv]; exact hRv _
  have hdiff : ∀ s : ℝ, ‖extendCurve hT Ur s - extendCurve hT Vr s‖ ≤ dist Ur Vr :=
    fun s => dist_extendCurve_le hT Ur Vr s
  have hkey : ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t - v t‖ ≤ dist Ur Vr / 2 := by
    intro t ht
    have hsub : ∀ s ∈ Set.Icc (0:ℝ) t, u s = extendCurve hT Ur s := fun s hs =>
      (hagree_u s ⟨hs.1, le_trans hs.2 ht.2⟩).symm
    have hsubv : ∀ s ∈ Set.Icc (0:ℝ) t, v s = extendCurve hT Vr s := fun s hs =>
      (hagree_v s ⟨hs.1, le_trans hs.2 ht.2⟩).symm
    have hequ : u t = affineMildMap hα.le hm A (extendCurve hT Ur) t := by
      rw [heu t ht, duhamelIntegral_quadCurve_congr hα.le hm ht.1 hsub]
      rfl
    have heqv : v t = affineMildMap hα.le hm A (extendCurve hT Vr) t := by
      rw [hev t ht, duhamelIntegral_quadCurve_congr hα.le hm ht.1 hsubv]
      rfl
    rw [hequ, heqv]
    refine le_trans (norm_affineMildMap_sub_le hα hm hC A (continuous_extendCurve hT Ur)
      (continuous_extendCurve hT Vr) hRU hRV hdiff ht.1) ?_
    have hs := hsmall t ht
    calc (8 * Real.pi * C * R * dist Ur Vr) * duhamelConst α t
        = dist Ur Vr * ((8 * Real.pi * C * R) * duhamelConst α t) := by ring
      _ ≤ dist Ur Vr * (1 / 2) := mul_le_mul_of_nonneg_left hs hD0
      _ = dist Ur Vr / 2 := by ring
  have hDle : dist Ur Vr ≤ dist Ur Vr / 2 := by
    refine (dist_le (by linarith : (0:ℝ) ≤ dist Ur Vr / 2)).2 (fun t => ?_)
    rw [dist_eq_norm]
    exact hkey (t : ℝ) t.2
  have hDzero : dist Ur Vr = 0 := le_antisymm (by linarith) hD0
  intro t ht
  have h := hkey t ht
  rw [hDzero, zero_div] at h
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm h (norm_nonneg _)))

end LiWang.Formalization
