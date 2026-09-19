/-
# Strong continuity of the fractional heat semigroup, and the Duhamel integral

This module continues the fractional-heat analysis of `FractionalHeat.lean` towards a mild
(Duhamel) formulation.  It proves

* strong continuity in time of the heat semigroup on the Wiener algebra,
* continuity in time of the smoothing operator `Wiener → Wiener1` away from `t = 0`,
* interval integrability of the Duhamel integrand `s ↦ e^{-(t-s)L} g(s)`, whose singularity
  at `s = t` is integrable exactly because `1/2 < α`,
* the Duhamel integral itself, with an explicit norm bound and an explicit Lipschitz
  estimate in the source curve.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.FractionalHeat
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter Topology

namespace LiWang.Formalization

/-! ## The heat flow as a total function of time

`heatOp` carries the hypothesis `0 ≤ t` in its type, which makes it awkward to speak of
continuity in `t`.  We therefore clamp negative times to `0`. -/

/-- The fractional heat flow, as a total function of `t : ℝ` (negative times are clamped). -/
noncomputable def heatFlow (α t : ℝ) (a : Wiener) : Wiener :=
  heatOp α (le_max_right t 0) a

theorem heatFlow_apply (α t : ℝ) (a : Wiener) (k : Gam) :
    (heatFlow α t a) k = heatSymbol α (max t 0) k * a k := rfl

theorem heatFlow_eq {α t : ℝ} (ht : 0 ≤ t) (a : Wiener) :
    heatFlow α t a = heatOp α ht a := by
  ext k
  rw [heatFlow_apply, heatOp_apply, max_eq_left ht]

theorem norm_heatFlow_le (α t : ℝ) (a : Wiener) : ‖heatFlow α t a‖ ≤ ‖a‖ :=
  norm_heatOp_apply_le α (le_max_right t 0) a

/-- The scalar symbol is continuous in time. -/
theorem continuous_heatSymbol_max (α : ℝ) (k : Gam) :
    Continuous fun t : ℝ => heatSymbol α (max t 0) k := by
  have h : Continuous fun t : ℝ => Real.exp (-(max t 0 * fracSymbol α k)) :=
    Real.continuous_exp.comp (((continuous_id.max continuous_const).mul continuous_const).neg)
  exact Complex.continuous_ofReal.comp h

/-- **Strong continuity of the fractional heat semigroup** on the Wiener algebra:
for each fixed datum the orbit `t ↦ e^{-tL}a` is norm continuous. -/
theorem continuous_heatFlow (α : ℝ) (a : Wiener) :
    Continuous fun t : ℝ => heatFlow α t a := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hnorm : ∀ t : ℝ, ‖heatFlow α t a - heatFlow α t₀ a‖
      = ∑' k : Gam, ‖heatSymbol α (max t 0) k * a k - heatSymbol α (max t₀ 0) k * a k‖ := by
    intro t
    rw [wiener_norm_eq]
    refine tsum_congr fun k => ?_
    rw [lp.coeFn_sub]
    rfl
  have hlim : Tendsto (fun t : ℝ =>
      ∑' k : Gam, ‖heatSymbol α (max t 0) k * a k - heatSymbol α (max t₀ 0) k * a k‖)
      (𝓝 t₀) (𝓝 0) := by
    have hzero : (∑' _k : Gam, (0:ℝ)) = 0 := tsum_zero
    have h := tendsto_tsum_of_dominated_convergence
      (𝓕 := 𝓝 t₀) (β := Gam) (G := ℝ)
      (f := fun t k => ‖heatSymbol α (max t 0) k * a k - heatSymbol α (max t₀ 0) k * a k‖)
      (g := fun _ : Gam => (0:ℝ)) (bound := fun k => 2 * ‖a k‖)
      ((wiener_summable a).mul_left 2)
      (fun k => by
        have hc : Continuous fun t : ℝ =>
            ‖heatSymbol α (max t 0) k * a k - heatSymbol α (max t₀ 0) k * a k‖ :=
          (((continuous_heatSymbol_max α k).mul continuous_const).sub continuous_const).norm
        exact hc.tendsto' t₀ 0 (by simp))
      (Eventually.of_forall (fun t k => by
        simp only [norm_norm]
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_mul, two_mul]
        gcongr
        · exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_heatSymbol_le_one (le_max_right t 0) k)
        · exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_heatSymbol_le_one (le_max_right t₀ 0) k)))
    rwa [hzero] at h
  have h0 : Tendsto (fun t : ℝ => heatFlow α t a - heatFlow α t₀ a) (𝓝 t₀) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa only [hnorm] using hlim)
  have h1 := h0.add_const (heatFlow α t₀ a)
  rw [ContinuousAt]
  simpa using h1

/-! ## The smoothing operator as a total function of time -/

theorem Wiener1.coeff_sub (u v : Wiener1) : (u - v).coeff = u.coeff - v.coeff := rfl

/-- Monotonicity of the heat symbol in time. -/
theorem norm_heatSymbol_mono {α s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) (k : Gam) :
    ‖heatSymbol α t k‖ ≤ ‖heatSymbol α s k‖ := by
  rw [norm_heatSymbol, norm_heatSymbol, Real.exp_le_exp]
  have hfs := fracSymbol_nonneg α k
  nlinarith

/-- The smoothing operator `Wiener → Wiener1`, as a total function of `t : ℝ`
(`t ≤ 0` gives `0`, which is never used). -/
noncomputable def heatSmoothFun {α : ℝ} (hα : 1 / 2 ≤ α) (t : ℝ) (a : Wiener) : Wiener1 :=
  if h : 0 < t then heatSmooth hα h a else 0

theorem heatSmoothFun_eq {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) :
    heatSmoothFun hα t a = heatSmooth hα ht a := dif_pos ht

theorem heatSmoothFun_coeff {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) (k : Gam) :
    (heatSmoothFun hα t a).coeff k = heatSymbol α t k * a k := by
  rw [heatSmoothFun_eq hα ht a, heatSmooth_coeff]

theorem heatSmoothFun_of_nonpos {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : t ≤ 0) (a : Wiener) :
    heatSmoothFun hα t a = 0 := dif_neg (not_lt.2 ht)

/-- The smoothing operator is linear in the datum, with the sharp bound. -/
theorem norm_heatSmoothFun_sub_le {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a b : Wiener) :
    ‖heatSmoothFun hα t a - heatSmoothFun hα t b‖
      ≤ (1 + t ^ (-(1 / (2 * α))) / Real.pi) * ‖a - b‖ := by
  have hlin : heatSmoothFun hα t a - heatSmoothFun hα t b = heatSmooth hα ht (a - b) := by
    rw [heatSmoothFun_eq hα ht, heatSmoothFun_eq hα ht]
    have h : heatSmoothCLM hα ht (a - b) = heatSmoothCLM hα ht a - heatSmoothCLM hα ht b :=
      map_sub _ _ _
    exact h.symm
  rw [hlin]
  exact norm_heatSmooth_le_sharp hα ht (a - b)

/-- **Continuity in time of the smoothing operator**, away from `t = 0`. -/
theorem tendsto_heatSmoothFun_time {α : ℝ} (hα : 1 / 2 ≤ α) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (a : Wiener) :
    Tendsto (fun t : ℝ => heatSmoothFun hα t a) (𝓝 t₀) (𝓝 (heatSmoothFun hα t₀ a)) := by
  have hhalf : 0 < t₀ / 2 := by linarith
  have hev : ∀ᶠ t : ℝ in 𝓝 t₀, t₀ / 2 < t := eventually_gt_nhds (by linarith)
  -- the norm of the difference, as a tsum, on the relevant neighbourhood
  have hnorm : ∀ᶠ t : ℝ in 𝓝 t₀,
      ‖heatSmoothFun hα t a - heatSmoothFun hα t₀ a‖
        = ∑' k : Gam, wt k * ‖heatSymbol α t k * a k - heatSymbol α t₀ k * a k‖ := by
    filter_upwards [hev] with t htt
    have ht : 0 < t := lt_trans hhalf htt
    rw [Wiener1.norm_eq]
    refine tsum_congr fun k => ?_
    rw [Wiener1.coeff_sub]
    show wt k * ‖(heatSmoothFun hα t a).coeff k - (heatSmoothFun hα t₀ a).coeff k‖ = _
    rw [heatSmoothFun_coeff hα ht, heatSmoothFun_coeff hα ht₀]
  -- Tannery
  have hlim : Tendsto (fun t : ℝ =>
      ∑' k : Gam, wt k * ‖heatSymbol α t k * a k - heatSymbol α t₀ k * a k‖) (𝓝 t₀) (𝓝 0) := by
    have hzero : (∑' _k : Gam, (0:ℝ)) = 0 := tsum_zero
    have hbound : Summable fun k : Gam => 2 * (wt k * ‖heatSymbol α (t₀ / 2) k * a k‖) :=
      (summable_heatSmooth hα hhalf a).mul_left 2
    have h := tendsto_tsum_of_dominated_convergence
      (𝓕 := 𝓝 t₀) (β := Gam) (G := ℝ)
      (f := fun t k => wt k * ‖heatSymbol α t k * a k - heatSymbol α t₀ k * a k‖)
      (g := fun _ : Gam => (0:ℝ))
      (bound := fun k => 2 * (wt k * ‖heatSymbol α (t₀ / 2) k * a k‖))
      hbound
      (fun k => by
        have hc : Continuous fun t : ℝ =>
            wt k * ‖heatSymbol α t k * a k - heatSymbol α t₀ k * a k‖ := by
          have hs : Continuous fun t : ℝ => heatSymbol α t k := by
            have : Continuous fun t : ℝ => Real.exp (-(t * fracSymbol α k)) :=
              Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg)
            exact Complex.continuous_ofReal.comp this
          exact continuous_const.mul (((hs.mul continuous_const).sub continuous_const).norm)
        exact hc.tendsto' t₀ 0 (by simp))
      (by
        filter_upwards [hev] with t htt k
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_pos k).le (norm_nonneg _))]
        have ht : (0:ℝ) ≤ t := le_of_lt (lt_trans hhalf htt)
        have h1 : ‖heatSymbol α t k * a k‖ ≤ ‖heatSymbol α (t₀ / 2) k * a k‖ := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_right
            (norm_heatSymbol_mono hhalf.le htt.le k) (norm_nonneg _)
        have h2 : ‖heatSymbol α t₀ k * a k‖ ≤ ‖heatSymbol α (t₀ / 2) k * a k‖ := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_right
            (norm_heatSymbol_mono hhalf.le (by linarith) k) (norm_nonneg _)
        have hsub : ‖heatSymbol α t k * a k - heatSymbol α t₀ k * a k‖
            ≤ 2 * ‖heatSymbol α (t₀ / 2) k * a k‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          rw [two_mul]
          exact add_le_add h1 h2
        have hw := (wt_pos k).le
        calc wt k * ‖heatSymbol α t k * a k - heatSymbol α t₀ k * a k‖
            ≤ wt k * (2 * ‖heatSymbol α (t₀ / 2) k * a k‖) :=
              mul_le_mul_of_nonneg_left hsub hw
          _ = 2 * (wt k * ‖heatSymbol α (t₀ / 2) k * a k‖) := by ring
        )
    rwa [hzero] at h
  have h0 : Tendsto (fun t : ℝ => heatSmoothFun hα t a - heatSmoothFun hα t₀ a) (𝓝 t₀) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    exact hlim.congr' (hnorm.mono fun t h => h.symm)
  have h1 := h0.add_const (heatSmoothFun hα t₀ a)
  simpa using h1

/-- The non-sharp smoothing bound, for the total function. -/
theorem norm_heatSmoothFun_sub_le' {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a b : Wiener) :
    ‖heatSmoothFun hα t a - heatSmoothFun hα t b‖ ≤ (1 + 1 / (Real.pi * t)) * ‖a - b‖ := by
  have hlin : heatSmoothFun hα t a - heatSmoothFun hα t b = heatSmooth hα ht (a - b) := by
    rw [heatSmoothFun_eq hα ht, heatSmoothFun_eq hα ht]
    exact (map_sub (heatSmoothCLM hα ht) a b).symm
  rw [hlin]
  exact norm_heatSmooth_le hα ht (a - b)

/-- **Joint continuity** of `(t, a) ↦ e^{-tL} a` as a `Wiener1`-valued map, for `t > 0`. -/
theorem continuousAt_heatSmoothFun {α : ℝ} (hα : 1 / 2 ≤ α) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (a₀ : Wiener) :
    ContinuousAt (fun p : ℝ × Wiener => heatSmoothFun hα p.1 p.2) (t₀, a₀) := by
  have hhalf : 0 < t₀ / 2 := by linarith
  set C : ℝ := 1 + 1 / (Real.pi * (t₀ / 2)) with hC
  have hCnn : 0 ≤ C := by
    have : 0 ≤ 1 / (Real.pi * (t₀ / 2)) := by positivity
    simp only [hC]; linarith
  have hev : ∀ᶠ p : ℝ × Wiener in 𝓝 (t₀, a₀), t₀ / 2 < p.1 := by
    have h : ∀ᶠ t : ℝ in 𝓝 t₀, t₀ / 2 < t := eventually_gt_nhds (by linarith)
    exact (continuous_fst.tendsto (t₀, a₀)) h
  -- the majorant
  have hmaj : Tendsto (fun p : ℝ × Wiener =>
      C * ‖p.2 - a₀‖ + ‖heatSmoothFun hα p.1 a₀ - heatSmoothFun hα t₀ a₀‖)
      (𝓝 (t₀, a₀)) (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ × Wiener => C * ‖p.2 - a₀‖) (𝓝 (t₀, a₀)) (𝓝 0) := by
      have hb : Tendsto (fun p : ℝ × Wiener => ‖p.2 - a₀‖) (𝓝 (t₀, a₀)) (𝓝 0) := by
        have hc : Continuous fun p : ℝ × Wiener => ‖p.2 - a₀‖ :=
          (continuous_snd.sub continuous_const).norm
        have h := hc.tendsto (t₀, a₀)
        simpa using h
      simpa using hb.const_mul C
    have h2 : Tendsto (fun p : ℝ × Wiener =>
        ‖heatSmoothFun hα p.1 a₀ - heatSmoothFun hα t₀ a₀‖) (𝓝 (t₀, a₀)) (𝓝 0) := by
      have hb : Tendsto (fun t : ℝ => ‖heatSmoothFun hα t a₀ - heatSmoothFun hα t₀ a₀‖)
          (𝓝 t₀) (𝓝 0) := by
        have := (tendsto_heatSmoothFun_time hα ht₀ a₀).sub
          (tendsto_const_nhds (x := heatSmoothFun hα t₀ a₀))
        simpa using this.norm
      exact hb.comp (continuous_fst.tendsto (t₀, a₀))
    have := h1.add h2
    simpa using this
  have hsq : Tendsto (fun p : ℝ × Wiener =>
      ‖heatSmoothFun hα p.1 p.2 - heatSmoothFun hα t₀ a₀‖) (𝓝 (t₀, a₀)) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
    filter_upwards [hev] with p hp
    have hp1 : 0 < p.1 := lt_trans hhalf hp
    refine le_trans (norm_sub_le_norm_sub_add_norm_sub _ (heatSmoothFun hα p.1 a₀) _) ?_
    refine add_le_add ?_ le_rfl
    refine le_trans (norm_heatSmoothFun_sub_le' hα hp1 p.2 a₀) ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hmono : 1 / (Real.pi * p.1) ≤ 1 / (Real.pi * (t₀ / 2)) := by
      have hpi := Real.pi_pos
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hp.le hpi.le
    simp only [hC]; linarith
  have h0 : Tendsto (fun p : ℝ × Wiener =>
      heatSmoothFun hα p.1 p.2 - heatSmoothFun hα t₀ a₀) (𝓝 (t₀, a₀)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hsq
  have h1 := h0.add_const (heatSmoothFun hα t₀ a₀)
  rw [ContinuousAt]
  simpa using h1

/-! ## The Duhamel integrand -/

/-- The Duhamel integrand `s ↦ e^{-(t-s)L} g(s)`, valued in the first-order space. -/
noncomputable def duhamelIntegrand {α : ℝ} (hα : 1 / 2 ≤ α) (t : ℝ) (g : ℝ → Wiener)
    (s : ℝ) : Wiener1 :=
  heatSmoothFun hα (t - s) (g s)

theorem duhamelIntegrand_of_le {α : ℝ} (hα : 1 / 2 ≤ α) {t s : ℝ} (hst : t ≤ s)
    (g : ℝ → Wiener) : duhamelIntegrand hα t g s = 0 :=
  heatSmoothFun_of_nonpos hα (by linarith) _

/-- **The pointwise Duhamel bound** with the sharp smoothing constant. -/
theorem norm_duhamelIntegrand_le {α : ℝ} (hα : 1 / 2 ≤ α) {t s : ℝ} (hst : s < t)
    (g : ℝ → Wiener) :
    ‖duhamelIntegrand hα t g s‖
      ≤ (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi) * ‖g s‖ := by
  have hts : 0 < t - s := by linarith
  rw [duhamelIntegrand, heatSmoothFun_eq hα hts]
  exact norm_heatSmooth_le_sharp hα hts (g s)

/-- The Duhamel integrand is continuous strictly before the singular time. -/
theorem continuousAt_duhamelIntegrand {α : ℝ} (hα : 1 / 2 ≤ α) {t s₀ : ℝ} (hst : s₀ < t)
    {g : ℝ → Wiener} (hg : Continuous g) :
    ContinuousAt (duhamelIntegrand hα t g) s₀ := by
  have hts : 0 < t - s₀ := by linarith
  have hpair : ContinuousAt (fun s : ℝ => ((t - s, g s) : ℝ × Wiener)) s₀ :=
    ((continuous_const.sub continuous_id).continuousAt).prodMk hg.continuousAt
  have hcomp : ContinuousAt ((fun p : ℝ × Wiener => heatSmoothFun hα p.1 p.2) ∘
      (fun s : ℝ => ((t - s, g s) : ℝ × Wiener))) s₀ :=
    ContinuousAt.comp (by simpa using continuousAt_heatSmoothFun hα hts (g s₀)) hpair
  exact hcomp

theorem continuousOn_duhamelIntegrand {α : ℝ} (hα : 1 / 2 ≤ α) {t : ℝ}
    {g : ℝ → Wiener} (hg : Continuous g) :
    ContinuousOn (duhamelIntegrand hα t g) (Set.Ioo 0 t) := fun _s hs =>
  (continuousAt_duhamelIntegrand hα hs.2 hg).continuousWithinAt

/-- **Interval integrability of the Duhamel integrand.**  The singularity at `s = t` is
integrable precisely because `1/2 < α`. -/
theorem intervalIntegrable_duhamelIntegrand {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ → Wiener} (hg : Continuous g) {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) :
    IntervalIntegrable (duhamelIntegrand hα.le t g) MeasureTheory.volume 0 t := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  -- the majorant
  have hmaj : IntervalIntegrable
      (fun s : ℝ => M * (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi))
      MeasureTheory.volume 0 t := by
    have hbase : IntervalIntegrable (fun r : ℝ => 1 + r ^ (-(1 / (2 * α))) / Real.pi)
        MeasureTheory.volume 0 t := intervalIntegrable_heatConst hα t
    have hsub := hbase.comp_sub_left t
    simp only [sub_zero, sub_self] at hsub
    exact (hsub.symm).const_mul M
  have hmajOn : MeasureTheory.IntegrableOn
      (fun s : ℝ => M * (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi))
      (Set.Ioc 0 t) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hmaj
  -- measurability
  have hset : MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) t)
      = MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) t) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  have hmeas : MeasureTheory.AEStronglyMeasurable (duhamelIntegrand hα.le t g)
      (MeasureTheory.volume.restrict (Set.Ioc 0 t)) := by
    rw [← hset]
    exact (continuousOn_duhamelIntegrand hα.le hg).aestronglyMeasurable measurableSet_Ioo
  refine MeasureTheory.Integrable.mono' hmajOn hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
  rcases lt_or_eq_of_le hs.2 with hlt | heq
  · refine le_trans (norm_duhamelIntegrand_le hα.le hlt g) ?_
    have h1 : (0:ℝ) ≤ (t - s) ^ (-(1 / (2 * α))) := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ (t - s) ^ (-(1 / (2 * α))) / Real.pi := div_nonneg h1 Real.pi_pos.le
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM s) (by linarith)
  · have hts : t - s = 0 := by rw [heq]; ring
    rw [duhamelIntegrand_of_le hα.le heq.ge g, norm_zero]
    refine mul_nonneg hMnn ?_
    have h1 : (0:ℝ) ≤ (t - s) ^ (-(1 / (2 * α))) := by
      rw [hts]; exact Real.rpow_nonneg le_rfl _
    have h2 : 0 ≤ (t - s) ^ (-(1 / (2 * α))) / Real.pi := div_nonneg h1 Real.pi_pos.le
    linarith

/-! ## The Duhamel integral -/

/-- The constant `∫₀^t (1 + (t-s)^{-1/(2α)}/π) ds = t + t^{1-1/(2α)}/(π(1-1/(2α)))`. -/
noncomputable def duhamelConst (α t : ℝ) : ℝ :=
  t + t ^ (1 - 1 / (2 * α)) / (Real.pi * (1 - 1 / (2 * α)))

/-- The explicit value of the time integral of the smoothing constant. -/
theorem integral_heatConst {α : ℝ} (hα : 1 / 2 < α) (t : ℝ) :
    (∫ s in (0:ℝ)..t, (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi)) = duhamelConst α t := by
  have hα0 : (0:ℝ) < α := by linarith
  have h2α : (1:ℝ) < 2 * α := by linarith
  have hβ : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
  have hβ0 : (0:ℝ) < 1 / (2 * α) := by positivity
  rw [intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => 1 + r ^ (-(1 / (2 * α))) / Real.pi) t]
  simp only [sub_self, sub_zero]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegrable_time_singularity hα t).div_const Real.pi)]
  rw [intervalIntegral.integral_div, integral_rpow (Or.inl (by linarith))]
  have h1 : (0:ℝ) ^ (-(1 / (2 * α)) + 1) = 0 := Real.zero_rpow (by intro h; linarith [h])
  rw [h1]
  have h2 : -(1 / (2 * α)) + 1 = 1 - 1 / (2 * α) := by ring
  rw [h2]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, duhamelConst]
  have hne : (1 : ℝ) - 1 / (2 * α) ≠ 0 := by intro h; linarith [h]
  field_simp
  ring

/-- **The Duhamel integral** `∫₀^t e^{-(t-s)L} g(s) ds`, valued in the first-order space. -/
noncomputable def duhamelIntegral {α : ℝ} (hα : 1 / 2 ≤ α) (t : ℝ) (g : ℝ → Wiener) : Wiener1 :=
  ∫ s in (0:ℝ)..t, duhamelIntegrand hα t g s

/-- **The Duhamel bound.**  The mild-solution integral of a bounded continuous source is
controlled in the *first-order* space with the explicit constant
`t + t^{1-1/(2α)}/(π(1-1/(2α)))`. -/
theorem norm_duhamelIntegral_le {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ → Wiener} {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) :
    ‖duhamelIntegral hα.le t g‖ ≤ M * duhamelConst α t := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hmaj : IntervalIntegrable
      (fun s : ℝ => M * (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi))
      MeasureTheory.volume 0 t := by
    have hbase : IntervalIntegrable (fun r : ℝ => 1 + r ^ (-(1 / (2 * α))) / Real.pi)
        MeasureTheory.volume 0 t := intervalIntegrable_heatConst hα t
    have hsub := hbase.comp_sub_left t
    simp only [sub_zero, sub_self] at hsub
    exact (hsub.symm).const_mul M
  have hbound : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      s ∈ Set.Ioc 0 t → ‖duhamelIntegrand hα.le t g s‖
        ≤ M * (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi) := by
    refine MeasureTheory.ae_of_all _ fun s hs => ?_
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · refine le_trans (norm_duhamelIntegrand_le hα.le hlt g) ?_
      have h1 : (0:ℝ) ≤ (t - s) ^ (-(1 / (2 * α))) := Real.rpow_nonneg (by linarith) _
      have h2 : 0 ≤ (t - s) ^ (-(1 / (2 * α))) / Real.pi := div_nonneg h1 Real.pi_pos.le
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM s) (by linarith)
    · have hts : t - s = 0 := by rw [heq]; ring
      rw [duhamelIntegrand_of_le hα.le heq.ge g, norm_zero]
      refine mul_nonneg hMnn ?_
      have h1 : (0:ℝ) ≤ (t - s) ^ (-(1 / (2 * α))) := by
        rw [hts]; exact Real.rpow_nonneg le_rfl _
      have h2 : 0 ≤ (t - s) ^ (-(1 / (2 * α))) / Real.pi := div_nonneg h1 Real.pi_pos.le
      linarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le ht hbound hmaj
  refine le_trans hle ?_
  rw [intervalIntegral.integral_const_mul, integral_heatConst hα t]

/-! ## Linearity of the Duhamel integral in the source, and the Lipschitz estimate -/

theorem duhamelIntegrand_sub {α : ℝ} (hα : 1 / 2 ≤ α) (t : ℝ) (g h : ℝ → Wiener) (s : ℝ) :
    duhamelIntegrand hα t g s - duhamelIntegrand hα t h s
      = duhamelIntegrand hα t (fun r => g r - h r) s := by
  by_cases hts : 0 < t - s
  · simp only [duhamelIntegrand, heatSmoothFun_eq hα hts]
    exact (map_sub (heatSmoothCLM hα hts) (g s) (h s)).symm
  · rw [duhamelIntegrand_of_le hα (by linarith : t ≤ s) g,
      duhamelIntegrand_of_le hα (by linarith : t ≤ s) h,
      duhamelIntegrand_of_le hα (by linarith : t ≤ s) (fun r => g r - h r), sub_zero]

theorem duhamelIntegral_sub {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g h : ℝ → Wiener} (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) (hN : ∀ s, ‖h s‖ ≤ N) :
    duhamelIntegral hα.le t g - duhamelIntegral hα.le t h
      = duhamelIntegral hα.le t (fun s => g s - h s) := by
  rw [duhamelIntegral, duhamelIntegral, duhamelIntegral,
    ← intervalIntegral.integral_sub (intervalIntegrable_duhamelIntegrand hα ht hg hM)
      (intervalIntegrable_duhamelIntegrand hα ht hh hN)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact duhamelIntegrand_sub hα.le t g h s

/-- **The Duhamel operator is Lipschitz in the source curve**, with the same explicit
constant. -/
theorem norm_duhamelIntegral_sub_le {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g h : ℝ → Wiener} (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) (hN : ∀ s, ‖h s‖ ≤ N) {D : ℝ} (hD : ∀ s, ‖g s - h s‖ ≤ D) :
    ‖duhamelIntegral hα.le t g - duhamelIntegral hα.le t h‖ ≤ D * duhamelConst α t := by
  rw [duhamelIntegral_sub hα ht hg hh hM hN]
  exact norm_duhamelIntegral_le hα ht hD

/-! ## The mild (Duhamel) map for the quadratic active-scalar nonlinearity -/

/-- The difference of a quadratic map at two points, exactly. -/
theorem quad_sub_quad {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (B : E →L[𝕜] E →L[𝕜] F) (x y : E) :
    quad B x - quad B y = B (x - y) x + B y (x - y) := by
  simp only [quad, map_sub, ContinuousLinearMap.sub_apply]
  abel

/-- The quadratic residual along a curve. -/
noncomputable def quadCurve {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (u : ℝ → Wiener1)
    (s : ℝ) : Wiener :=
  transport m hm (u s) (u s)

theorem continuous_quadCurve {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {u : ℝ → Wiener1}
    (hu : Continuous u) : Continuous (quadCurve hm u) :=
  (((transport m hm).continuous).comp hu).clm_apply hu

theorem norm_quadCurve_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {u : ℝ → Wiener1} {R : ℝ} (hR : ∀ s, ‖u s‖ ≤ R) (s : ℝ) :
    ‖quadCurve hm u s‖ ≤ 4 * Real.pi * C * R * R := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR s)
  refine le_trans (norm_transport_apply_le hm hC (u s) (u s)) ?_
  have hpi := Real.pi_pos
  have h1 : ‖u s‖ ≤ R := hR s
  have hn : (0:ℝ) ≤ ‖u s‖ := norm_nonneg _
  gcongr

/-- **The quadratic nonlinearity is locally Lipschitz**, with the explicit constant
`8πC R` on the ball of radius `R`. -/
theorem norm_quadCurve_sub_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {u v : ℝ → Wiener1} {R : ℝ}
    (hu : ∀ s, ‖u s‖ ≤ R) (hv : ∀ s, ‖v s‖ ≤ R) (s : ℝ) :
    ‖quadCurve hm u s - quadCurve hm v s‖ ≤ 8 * Real.pi * C * R * ‖u s - v s‖ := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hu s)
  have hkey : quadCurve hm u s - quadCurve hm v s
      = transport m hm (u s - v s) (u s) + transport m hm (v s) (u s - v s) := by
    have := quad_sub_quad (transport m hm) (u s) (v s)
    simpa only [quad, quadCurve] using this
  rw [hkey]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖transport m hm (u s - v s) (u s)‖ ≤ 4 * Real.pi * C * ‖u s - v s‖ * R := by
    refine le_trans (norm_transport_apply_le hm hC _ _) ?_
    have hpi := Real.pi_pos
    have := hu s
    gcongr
  have h2 : ‖transport m hm (v s) (u s - v s)‖ ≤ 4 * Real.pi * C * R * ‖u s - v s‖ := by
    refine le_trans (norm_transport_apply_le hm hC _ _) ?_
    have hpi := Real.pi_pos
    have := hv s
    gcongr
  have h3 : 4 * Real.pi * C * ‖u s - v s‖ * R = 4 * Real.pi * C * R * ‖u s - v s‖ := by ring
  rw [h3] at h1
  linarith

/-! ## The heat flow contracts the first-order norm -/

/-- The fractional heat flow is a contraction of the **weighted** (first-order) norm as
well: `‖e^{-tL}u‖_{A¹} ≤ ‖u‖_{A¹}`. -/
theorem norm_heatSmoothFun_incl_le {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (u : Wiener1) :
    ‖heatSmoothFun hα t (incl u)‖ ≤ ‖u‖ := by
  rw [heatSmoothFun_eq hα ht, Wiener1.norm_eq, Wiener1.norm_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_heatSmooth hα ht (incl u))
    u.summable_wt
  rw [heatSmooth_coeff, incl_apply, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (wt_pos k).le
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_heatSymbol_le_one ht.le k)

/-! ## The mild (Duhamel) map -/

/-- **The mild solution map** for the quadratic active-scalar equation
`∂_t θ + N_m(θ, θ) + (-Δ)^α θ = 0`:
`Φ(u)(t) = e^{-tL} u₀ - ∫₀^t e^{-(t-s)L} N_m(u(s), u(s)) ds`. -/
noncomputable def mildMap {α : ℝ} (hα : 1 / 2 ≤ α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (u₀ : Wiener1) (u : ℝ → Wiener1) (t : ℝ) : Wiener1 :=
  heatSmoothFun hα t (incl u₀) - duhamelIntegral hα t (quadCurve hm u)

/-- **The self-map estimate**: on the ball of radius `R`, the mild map is bounded by
`‖u₀‖ + 4πC R² · (t + t^{1-1/(2α)}/(π(1-1/(2α))))`. -/
theorem norm_mildMap_le {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {u : ℝ → Wiener1} {R : ℝ}
    (hR : ∀ s, ‖u s‖ ≤ R) {t : ℝ} (ht : 0 < t) :
    ‖mildMap hα.le hm u₀ u t‖ ≤ ‖u₀‖ + (4 * Real.pi * C * R * R) * duhamelConst α t := by
  refine le_trans (norm_sub_le _ _) ?_
  refine add_le_add (norm_heatSmoothFun_incl_le hα.le ht u₀) ?_
  exact norm_duhamelIntegral_le hα ht.le (fun s => norm_quadCurve_le hm hC hR s)

/-- **The contraction estimate**: two curves in the ball of radius `R` are mapped to states
whose distance is at most `8πC R · (sup‖u - v‖) · duhamelConst α t`. -/
theorem norm_mildMap_sub_le {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {u v : ℝ → Wiener1}
    (hu : Continuous u) (hv : Continuous v) {R : ℝ}
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R) {D : ℝ} (hD : ∀ s, ‖u s - v s‖ ≤ D)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖mildMap hα.le hm u₀ u t - mildMap hα.le hm u₀ v t‖
      ≤ (8 * Real.pi * C * R * D) * duhamelConst α t := by
  have hcancel : mildMap hα.le hm u₀ u t - mildMap hα.le hm u₀ v t
      = -(duhamelIntegral hα.le t (quadCurve hm u)
          - duhamelIntegral hα.le t (quadCurve hm v)) := by
    simp only [mildMap]
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

/-! ## Smallness of the Duhamel constant for short times -/

theorem tendsto_duhamelConst {α : ℝ} (hα : 1 / 2 < α) :
    Tendsto (duhamelConst α) (𝓝 0) (𝓝 0) := by
  have hα0 : (0:ℝ) < α := by linarith
  have h2α : (1:ℝ) < 2 * α := by linarith
  have hβ : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
  have hexp : (0:ℝ) < 1 - 1 / (2 * α) := by linarith
  have h1 : Tendsto (fun t : ℝ => t ^ (1 - 1 / (2 * α))) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (1 - 1 / (2 * α))) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)
    have h0 : (0:ℝ) ^ (1 - 1 / (2 * α)) = 0 := Real.zero_rpow (ne_of_gt hexp)
    have := hc.tendsto
    rwa [h0] at this
  have h2 : Tendsto (fun t : ℝ =>
      t + t ^ (1 - 1 / (2 * α)) / (Real.pi * (1 - 1 / (2 * α)))) (𝓝 0) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝 (0:ℝ)) (𝓝 0) := tendsto_id
    have := hid.add (h1.div_const (Real.pi * (1 - 1 / (2 * α))))
    simpa using this
  exact h2.congr (fun t => rfl)

/-- **Local-in-time smallness.**  For any prescribed size `ε > 0` there is a positive time
horizon on which the Duhamel constant stays below `ε`.  Combined with
`norm_mildMap_sub_le`, this is the smallness needed to make the mild map a contraction. -/
theorem exists_duhamelConst_lt {α : ℝ} (hα : 1 / 2 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t ∈ Set.Icc (0:ℝ) T, duhamelConst α t < ε := by
  have h := (tendsto_duhamelConst hα).eventually_lt_const hε
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, H⟩ := h
  refine ⟨δ / 2, by linarith, fun t ht => ?_⟩
  refine H ?_
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2]

/-- **The local contraction package.**  Given a symbol bound `C` and a radius `R`, there is a
positive time horizon on which the mild map contracts distances by a factor `1/2`. -/
theorem exists_local_contraction {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {R : ℝ} (hR : 0 < R)
    (u₀ : Wiener1) :
    ∃ T : ℝ, 0 < T ∧ ∀ (u v : ℝ → Wiener1), Continuous u → Continuous v →
      (∀ s, ‖u s‖ ≤ R) → (∀ s, ‖v s‖ ≤ R) → ∀ (D : ℝ), (∀ s, ‖u s - v s‖ ≤ D) →
        ∀ t ∈ Set.Icc (0:ℝ) T,
          ‖mildMap hα.le hm u₀ u t - mildMap hα.le hm u₀ v t‖ ≤ D / 2 := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hpi := Real.pi_pos
  set L : ℝ := 8 * Real.pi * C * R + 1 with hL
  have hLpos : 0 < L := by simp only [hL]; positivity
  obtain ⟨T, hT, hsmall⟩ := exists_duhamelConst_lt hα (ε := 1 / (2 * L)) (by positivity)
  refine ⟨T, hT, fun u v hu hv hRu hRv D hD t ht => ?_⟩
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD 0)
  have hbase := norm_mildMap_sub_le hα hm hC u₀ hu hv hRu hRv hD ht.1
  refine le_trans hbase ?_
  have hlt : duhamelConst α t < 1 / (2 * L) := hsmall t ht
  have hcoef : (0:ℝ) ≤ 8 * Real.pi * C * R * D := by positivity
  have hstep : (8 * Real.pi * C * R * D) * duhamelConst α t
      ≤ (8 * Real.pi * C * R * D) * (1 / (2 * L)) :=
    mul_le_mul_of_nonneg_left hlt.le hcoef
  refine le_trans hstep ?_
  have h2L : (0:ℝ) < 2 * L := by positivity
  rw [mul_one_div, div_le_iff₀ h2L]
  have hexpand : D / 2 * (2 * L) = D * L := by ring
  rw [hexpand, hL]
  have hring : D * (8 * Real.pi * C * R + 1) = 8 * Real.pi * C * R * D + D := by ring
  rw [hring]
  linarith

end LiWang.Formalization
