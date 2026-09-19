/-
# Continuity in time of the Duhamel term

The remaining analytic ingredient of a local mild-solution argument: the Duhamel term

    F(t) = ∫₀^t e^{-(t-s)(-Δ)^α} g(s) ds

is continuous in `t` as a curve in the first-order Wiener space.  The time variable occurs
both in the integration limit and in the (endpoint-singular) kernel, so the proof passes to
the reflected variable `r = t - s` and applies dominated convergence on a fixed interval.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.Duhamel

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

/-- The Duhamel integrand in the reflected variable `r = t - s`, extended by zero past the
integration limit. -/
noncomputable def duhamelKernel {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) (t r : ℝ) :
    Wiener1 :=
  if r ≤ t then heatSmoothFun hα r (g (t - r)) else 0

theorem duhamelKernel_of_le {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) {t r : ℝ} (h : r ≤ t) :
    duhamelKernel hα g t r = heatSmoothFun hα r (g (t - r)) := if_pos h

theorem duhamelKernel_of_gt {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) {t r : ℝ} (h : t < r) :
    duhamelKernel hα g t r = 0 := if_neg (not_le.2 h)

/-- The reflected integrand agrees with the Duhamel integrand after `s ↦ t - s`. -/
theorem duhamelKernel_sub {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) (t s : ℝ) (hs : 0 ≤ s) :
    duhamelKernel hα g t (t - s) = duhamelIntegrand hα t g s := by
  have hle : t - s ≤ t := by linarith
  have hid : t - (t - s) = s := by ring
  rw [duhamelKernel_of_le hα g hle, duhamelIntegrand, hid]

theorem duhamelKernel_eq {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) {t r : ℝ} (hr : r ≤ t) :
    duhamelIntegrand hα t g (t - r) = duhamelKernel hα g t r := by
  have hid : t - (t - r) = r := by ring
  rw [duhamelKernel_of_le hα g hr, duhamelIntegrand, hid]

/-- **The reflected form of the Duhamel integral**: `∫₀^t e^{-(t-s)L}g(s) ds
= ∫₀^t e^{-rL} g(t-r) dr`. -/
theorem duhamelIntegral_eq_reflected {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) {t : ℝ}
    (ht : 0 ≤ t) :
    duhamelIntegral hα t g = ∫ r in (0:ℝ)..t, duhamelKernel hα g t r := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := (0:ℝ)) (b := t) (f := fun r : ℝ => duhamelKernel hα g t r) t
  simp only [sub_self, sub_zero] at h
  rw [duhamelIntegral, ← h]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [Set.uIcc_of_le ht] at hs
  exact (duhamelKernel_sub hα g t s hs.1).symm

/-- The reflected integrand is interval integrable. -/
theorem intervalIntegrable_duhamelKernel {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ → Wiener} (hg : Continuous g) {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) :
    IntervalIntegrable (duhamelKernel hα.le g t) volume 0 t := by
  have hbase := intervalIntegrable_duhamelIntegrand hα ht hg hM
  have h := hbase.comp_sub_left t
  simp only [sub_self, sub_zero] at h
  refine (h.symm).congr (fun r hr => ?_)
  rcases Set.mem_uIoc.1 hr with h1 | h1
  · exact duhamelKernel_eq hα.le g h1.2
  · exact absurd (lt_of_lt_of_le h1.1 (le_trans h1.2 ht)) (lt_irrefl t)

/-- The reflected integrand vanishes past the integration limit, so the integral may be taken
over any longer interval. -/
theorem duhamelIntegral_eq_reflected_long {α : ℝ} (hα : 1 / 2 < α) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) {g : ℝ → Wiener} (hg : Continuous g) {M : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) :
    duhamelIntegral hα.le t g = ∫ r in (0:ℝ)..T, duhamelKernel hα.le g t r := by
  have hgt : ∀ r ∈ Set.uIoc t T, t < r := by
    intro r hr
    rcases Set.mem_uIoc.1 hr with h | h
    · exact h.1
    · exact absurd (lt_of_lt_of_le h.1 (le_trans h.2 htT)) (lt_irrefl T)
  have hint0t : IntervalIntegrable (duhamelKernel hα.le g t) volume 0 t :=
    intervalIntegrable_duhamelKernel hα ht hg hM
  have hinttT : IntervalIntegrable (duhamelKernel hα.le g t) volume t T := by
    refine (intervalIntegrable_const (c := (0 : Wiener1))).congr ?_
    intro r hr
    exact (duhamelKernel_of_gt hα.le g (hgt r hr)).symm
  have htT0 : (∫ r in t..T, duhamelKernel hα.le g t r) = 0 := by
    have hcongr : (∫ r in t..T, duhamelKernel hα.le g t r) = ∫ _r in t..T, (0 : Wiener1) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr => ?_)
      exact duhamelKernel_of_gt hα.le g (hgt r hr)
    rw [hcongr, intervalIntegral.integral_zero]
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint0t hinttT
  rw [htT0, add_zero] at hadd
  rw [duhamelIntegral_eq_reflected hα.le g ht, hadd]

/-- For non-positive times the Duhamel integral vanishes. -/
theorem duhamelIntegral_of_nonpos {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) {t : ℝ}
    (ht : t ≤ 0) : duhamelIntegral hα t g = 0 := by
  have hzero : ∀ s ∈ Set.uIcc (0:ℝ) t, duhamelIntegrand hα t g s = 0 := by
    intro s hs
    rw [Set.uIcc_of_ge ht] at hs
    exact duhamelIntegrand_of_le hα hs.1 g
  rw [duhamelIntegral, intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]

theorem duhamelKernel_eq_zero_of_neg {α : ℝ} (hα : 1 / 2 ≤ α) (g : ℝ → Wiener) {t T : ℝ}
    (ht : t < 0) (hT : 0 ≤ T) (r : ℝ) (hr : r ∈ Set.uIoc (0:ℝ) T) :
    duhamelKernel hα g t r = 0 := by
  have hr0 : 0 < r := by
    rcases Set.mem_uIoc.1 hr with h | h
    · exact h.1
    · exact absurd (lt_of_lt_of_le h.1 (le_trans h.2 hT)) (lt_irrefl T)
  exact duhamelKernel_of_gt hα g (lt_trans ht hr0)

/-- Interval integrability of the reflected integrand on any interval containing `[0,t]`. -/
theorem intervalIntegrable_duhamelKernel_long {α : ℝ} (hα : 1 / 2 < α) {t T : ℝ}
    (htT : t ≤ T) (hT : 0 ≤ T) {g : ℝ → Wiener} (hg : Continuous g) {M : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) :
    IntervalIntegrable (duhamelKernel hα.le g t) volume 0 T := by
  rcases le_or_gt 0 t with ht | ht
  · have hgt : ∀ r ∈ Set.uIoc t T, t < r := by
      intro r hr
      rcases Set.mem_uIoc.1 hr with h | h
      · exact h.1
      · exact absurd (lt_of_lt_of_le h.1 (le_trans h.2 htT)) (lt_irrefl T)
    have hinttT : IntervalIntegrable (duhamelKernel hα.le g t) volume t T :=
      (intervalIntegrable_const (c := (0 : Wiener1))).congr
        (fun r hr => (duhamelKernel_of_gt hα.le g (hgt r hr)).symm)
    exact (intervalIntegrable_duhamelKernel hα ht hg hM).trans hinttT
  · exact (intervalIntegrable_const (c := (0 : Wiener1))).congr
      (fun r hr => (duhamelKernel_eq_zero_of_neg hα.le g ht hT r hr).symm)

/-- The reflected form of the Duhamel integral over a fixed longer interval, valid for every
time `t ≤ T`. -/
theorem duhamelIntegral_eq_long {α : ℝ} (hα : 1 / 2 < α) {t T : ℝ} (htT : t ≤ T)
    (hT : 0 ≤ T) {g : ℝ → Wiener} (hg : Continuous g) {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) :
    duhamelIntegral hα.le t g = ∫ r in (0:ℝ)..T, duhamelKernel hα.le g t r := by
  rcases le_or_gt 0 t with ht | ht
  · exact duhamelIntegral_eq_reflected_long hα ht htT hg hM
  · rw [duhamelIntegral_of_nonpos hα.le g ht.le]
    have hcongr : (∫ r in (0:ℝ)..T, duhamelKernel hα.le g t r) = ∫ _r in (0:ℝ)..T,
        (0 : Wiener1) :=
      intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr =>
        duhamelKernel_eq_zero_of_neg hα.le g ht hT r hr)
    rw [hcongr, intervalIntegral.integral_zero]

/-- The uniform bound on the reflected integrand. -/
theorem norm_duhamelKernel_le {α : ℝ} (hα : 1 / 2 ≤ α) {g : ℝ → Wiener} {M : ℝ}
    (hM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖duhamelKernel hα g t r‖ ≤ M * (1 + r ^ (-(1 / (2 * α))) / Real.pi) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hc : 0 ≤ 1 + r ^ (-(1 / (2 * α))) / Real.pi := by
    have h1 : (0:ℝ) ≤ r ^ (-(1 / (2 * α))) := Real.rpow_nonneg hr.le _
    have h2 : 0 ≤ r ^ (-(1 / (2 * α))) / Real.pi := div_nonneg h1 Real.pi_pos.le
    linarith
  by_cases h : r ≤ t
  · rw [duhamelKernel_of_le hα g h, heatSmoothFun_eq hα hr]
    refine le_trans (norm_heatSmooth_le_sharp hα hr (g (t - r))) ?_
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM _) hc
  · rw [duhamelKernel_of_gt hα g (not_le.1 h), norm_zero]
    exact mul_nonneg hMnn hc

/-- Pointwise (in the reflected variable) continuity in time of the integrand. -/
theorem tendsto_duhamelKernel {α : ℝ} (hα : 1 / 2 ≤ α) {g : ℝ → Wiener} (hg : Continuous g)
    {t₀ r : ℝ} (hr : 0 < r) (hne : r ≠ t₀) :
    Tendsto (fun t : ℝ => duhamelKernel hα g t r) (𝓝 t₀) (𝓝 (duhamelKernel hα g t₀ r)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `r < t₀`: the kernel is the smoothing of a continuous curve
    have hev : ∀ᶠ t : ℝ in 𝓝 t₀, r ≤ t := (eventually_gt_nhds hlt).mono fun t ht => ht.le
    have hlim : Tendsto (fun t : ℝ => heatSmoothFun hα r (g (t - r))) (𝓝 t₀)
        (𝓝 (heatSmoothFun hα r (g (t₀ - r)))) := by
      have hcont : Continuous fun t : ℝ => heatSmoothFun hα r (g (t - r)) := by
        have h1 : Continuous fun t : ℝ => g (t - r) := hg.comp (continuous_id.sub continuous_const)
        have h2 : Continuous fun a : Wiener => heatSmoothFun hα r a := by
          have : (fun a : Wiener => heatSmoothFun hα r a) = fun a => heatSmoothCLM hα hr a := by
            funext a; rw [heatSmoothFun_eq hα hr]; rfl
          rw [this]
          exact (heatSmoothCLM hα hr).continuous
        exact h2.comp h1
      exact hcont.tendsto t₀
    rw [duhamelKernel_of_le hα g hlt.le]
    refine hlim.congr' ?_
    filter_upwards [hev] with t ht
    exact (duhamelKernel_of_le hα g ht).symm
  · -- `t₀ < r`: the kernel vanishes near `t₀`
    have hev : ∀ᶠ t : ℝ in 𝓝 t₀, t < r := eventually_lt_nhds hgt
    have hzero : duhamelKernel hα g t₀ r = 0 := duhamelKernel_of_gt hα g hgt
    rw [hzero]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with t ht
    exact (duhamelKernel_of_gt hα g ht).symm

/-! ## Continuity in time of the Duhamel term -/

/-- **The Duhamel term is continuous in time.**  This is the lemma that was missing from
`Duhamel.lean`: the time variable occurs both in the integration limit and in the
endpoint-singular kernel, and the proof goes through the reflected variable and dominated
convergence on the fixed interval `[0,T]`. -/
theorem tendsto_duhamelIntegral {α : ℝ} (hα : 1 / 2 < α) {g : ℝ → Wiener} (hg : Continuous g)
    {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) (t₀ : ℝ) :
    Tendsto (fun t : ℝ => duhamelIntegral hα.le t g) (𝓝 t₀)
      (𝓝 (duhamelIntegral hα.le t₀ g)) := by
  set T : ℝ := max t₀ 0 + 1 with hTdef
  have hT : (0:ℝ) ≤ T := by
    have h := le_max_right t₀ 0
    simp only [hTdef]; linarith
  have ht₀T : t₀ < T := by
    have h := le_max_left t₀ 0
    simp only [hTdef]; linarith
  have hevT : ∀ᶠ t : ℝ in 𝓝 t₀, t ≤ T :=
    (eventually_lt_nhds ht₀T).mono fun t h => h.le
  have hset : ∀ t : ℝ, t ≤ T →
      duhamelIntegral hα.le t g = ∫ r in Set.Ioc (0:ℝ) T, duhamelKernel hα.le g t r := by
    intro t ht
    rw [duhamelIntegral_eq_long hα ht hT hg hM, intervalIntegral.integral_of_le hT]
  have hbound_int : Integrable (fun r : ℝ => M * (1 + r ^ (-(1 / (2 * α))) / Real.pi))
      (volume.restrict (Set.Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      ((intervalIntegrable_heatConst hα T).const_mul M)
  have hmeas : ∀ᶠ t : ℝ in 𝓝 t₀, AEStronglyMeasurable (duhamelKernel hα.le g t)
      (volume.restrict (Set.Ioc 0 T)) := by
    filter_upwards [hevT] with t ht
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      (intervalIntegrable_duhamelKernel_long hα ht hT hg hM)).aestronglyMeasurable
  have hbd : ∀ᶠ t : ℝ in 𝓝 t₀, ∀ᵐ r ∂(volume.restrict (Set.Ioc (0:ℝ) T)),
      ‖duhamelKernel hα.le g t r‖ ≤ M * (1 + r ^ (-(1 / (2 * α))) / Real.pi) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact norm_duhamelKernel_le hα.le hM t hr.1
  have hne : ∀ᵐ r : ℝ, r ≠ t₀ := by
    rw [MeasureTheory.ae_iff]
    simp
  have hlim : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0:ℝ) T)),
      Tendsto (fun t : ℝ => duhamelKernel hα.le g t r) (𝓝 t₀)
        (𝓝 (duhamelKernel hα.le g t₀ r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with r hr hrne
    exact tendsto_duhamelKernel hα.le hg hr.1 hrne
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (0:ℝ) T)) (l := 𝓝 t₀)
    (F := fun t : ℝ => duhamelKernel hα.le g t) (f := duhamelKernel hα.le g t₀)
    (bound := fun r : ℝ => M * (1 + r ^ (-(1 / (2 * α))) / Real.pi))
    hmeas hbd hbound_int hlim
  rw [hset t₀ ht₀T.le]
  refine hdct.congr' ?_
  filter_upwards [hevT] with t ht
  exact (hset t ht).symm

/-- **The Duhamel term is a continuous curve.** -/
theorem continuous_duhamelIntegral {α : ℝ} (hα : 1 / 2 < α) {g : ℝ → Wiener}
    (hg : Continuous g) {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) :
    Continuous fun t : ℝ => duhamelIntegral hα.le t g :=
  continuous_iff_continuousAt.2 fun t₀ => tendsto_duhamelIntegral hα hg hM t₀

/-! ## The heat flow on the first-order space, and continuity of the mild map -/

theorem summable_heatFlow1 (α t : ℝ) (u : Wiener1) :
    Summable fun k => wt k * ‖heatSymbol α (max t 0) k * u.coeff k‖ := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => ?_) u.summable_wt
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (wt_pos k).le
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_heatSymbol_le_one (le_max_right t 0) k)

/-- The fractional heat flow **on the first-order space**, as a total function of time.
Unlike `heatSmoothFun`, this is continuous through `t = 0`, where it is the identity. -/
noncomputable def heatFlow1 (α t : ℝ) (u : Wiener1) : Wiener1 :=
  Wiener1.mk (fun k => heatSymbol α (max t 0) k * u.coeff k) (summable_heatFlow1 α t u)

@[simp] theorem heatFlow1_coeff (α t : ℝ) (u : Wiener1) (k : Gam) :
    (heatFlow1 α t u).coeff k = heatSymbol α (max t 0) k * u.coeff k := rfl

theorem heatFlow1_zero (α : ℝ) (u : Wiener1) : heatFlow1 α 0 u = u := by
  apply Wiener1.coeff_injective
  funext k
  rw [heatFlow1_coeff]
  have h : heatSymbol α (max (0:ℝ) 0) k = 1 := by
    rw [max_self, heatSymbol]
    norm_num
  rw [h, one_mul]

theorem norm_heatFlow1_le (α t : ℝ) (u : Wiener1) : ‖heatFlow1 α t u‖ ≤ ‖u‖ := by
  rw [Wiener1.norm_eq, Wiener1.norm_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_heatFlow1 α t u) u.summable_wt
  rw [heatFlow1_coeff, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (wt_pos k).le
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_heatSymbol_le_one (le_max_right t 0) k)

/-- For positive times the first-order heat flow is the smoothing operator applied to the
inclusion. -/
theorem heatFlow1_eq_heatSmoothFun {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (u : Wiener1) :
    heatFlow1 α t u = heatSmoothFun hα t (incl u) := by
  apply Wiener1.coeff_injective
  funext k
  rw [heatFlow1_coeff, heatSmoothFun_coeff hα ht, incl_apply, max_eq_left ht.le]

/-- **Strong continuity of the heat flow on the first-order space.** -/
theorem continuous_heatFlow1 (α : ℝ) (u : Wiener1) :
    Continuous fun t : ℝ => heatFlow1 α t u := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hnorm : ∀ t : ℝ, ‖heatFlow1 α t u - heatFlow1 α t₀ u‖
      = ∑' k : Gam, wt k * ‖heatSymbol α (max t 0) k * u.coeff k
          - heatSymbol α (max t₀ 0) k * u.coeff k‖ := by
    intro t
    rw [Wiener1.norm_eq]
    exact tsum_congr fun k => by rw [Wiener1.coeff_sub]; rfl
  have hlim : Tendsto (fun t : ℝ => ∑' k : Gam, wt k * ‖heatSymbol α (max t 0) k * u.coeff k
      - heatSymbol α (max t₀ 0) k * u.coeff k‖) (𝓝 t₀) (𝓝 0) := by
    have hzero : (∑' _k : Gam, (0:ℝ)) = 0 := tsum_zero
    have h := tendsto_tsum_of_dominated_convergence
      (𝓕 := 𝓝 t₀) (β := Gam) (G := ℝ)
      (f := fun t k => wt k * ‖heatSymbol α (max t 0) k * u.coeff k
        - heatSymbol α (max t₀ 0) k * u.coeff k‖)
      (g := fun _ : Gam => (0:ℝ)) (bound := fun k => 2 * (wt k * ‖u.coeff k‖))
      (u.summable_wt.mul_left 2)
      (fun k => by
        have hc : Continuous fun t : ℝ => wt k * ‖heatSymbol α (max t 0) k * u.coeff k
            - heatSymbol α (max t₀ 0) k * u.coeff k‖ :=
          continuous_const.mul ((((continuous_heatSymbol_max α k).mul
            continuous_const).sub continuous_const).norm)
        exact hc.tendsto' t₀ 0 (by simp))
      (Filter.Eventually.of_forall fun t k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_pos k).le (norm_nonneg _))]
        have h1 : ‖heatSymbol α (max t 0) k * u.coeff k‖ ≤ ‖u.coeff k‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_heatSymbol_le_one (le_max_right t 0) k)
        have h2 : ‖heatSymbol α (max t₀ 0) k * u.coeff k‖ ≤ ‖u.coeff k‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_heatSymbol_le_one (le_max_right t₀ 0) k)
        have hsub : ‖heatSymbol α (max t 0) k * u.coeff k
            - heatSymbol α (max t₀ 0) k * u.coeff k‖ ≤ 2 * ‖u.coeff k‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          rw [two_mul]
          exact add_le_add h1 h2
        calc wt k * ‖heatSymbol α (max t 0) k * u.coeff k
              - heatSymbol α (max t₀ 0) k * u.coeff k‖
            ≤ wt k * (2 * ‖u.coeff k‖) := mul_le_mul_of_nonneg_left hsub (wt_pos k).le
          _ = 2 * (wt k * ‖u.coeff k‖) := by ring)
    rwa [hzero] at h
  have h0 : Tendsto (fun t : ℝ => heatFlow1 α t u - heatFlow1 α t₀ u) (𝓝 t₀) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa only [hnorm] using hlim)
  have h1 := h0.add_const (heatFlow1 α t₀ u)
  rw [ContinuousAt]
  simpa using h1

/-- **The mild map with the corrected linear part**: `Φ(u)(t) = e^{-tL}u₀ - ∫₀^t
e^{-(t-s)L} N_m(u(s),u(s)) ds`, where the linear part is taken in the first-order space so
that the whole curve is continuous through `t = 0`. -/
noncomputable def mildMap1 {α : ℝ} (hα : 1 / 2 ≤ α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (u₀ : Wiener1) (u : ℝ → Wiener1) (t : ℝ) : Wiener1 :=
  heatFlow1 α t u₀ - duhamelIntegral hα t (quadCurve hm u)

theorem mildMap1_eq {α : ℝ} (hα : 1 / 2 ≤ α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (u₀ : Wiener1) (u : ℝ → Wiener1) {t : ℝ} (ht : 0 < t) :
    mildMap1 hα hm u₀ u t = mildMap hα hm u₀ u t := by
  rw [mildMap1, mildMap, heatFlow1_eq_heatSmoothFun hα ht]

theorem mildMap1_zero {α : ℝ} (hα : 1 / 2 ≤ α) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (u₀ : Wiener1) (u : ℝ → Wiener1) : mildMap1 hα hm u₀ u 0 = u₀ := by
  rw [mildMap1, heatFlow1_zero, duhamelIntegral, intervalIntegral.integral_same, sub_zero]

/-- **The mild map sends a bounded continuous curve to a continuous curve.**  This is what a
fixed-point argument needs, and it is exactly what was missing in `Duhamel.lean`. -/
theorem continuous_mildMap1 {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1) {u : ℝ → Wiener1}
    (hu : Continuous u) {R : ℝ} (hR : ∀ s, ‖u s‖ ≤ R) :
    Continuous fun t : ℝ => mildMap1 hα.le hm u₀ u t := by
  have hg : Continuous (quadCurve hm u) := continuous_quadCurve hm hu
  have hM : ∀ s, ‖quadCurve hm u s‖ ≤ 4 * Real.pi * C * R * R :=
    fun s => norm_quadCurve_le hm hC hR s
  exact (continuous_heatFlow1 α u₀).sub (continuous_duhamelIntegral hα hg hM)

end LiWang.WienerModel
