/-
# Prescribed-interval smooth time bumps and the two test-separation lemmas

This module supplies the *duality* tools required to convert an orthogonality statement
against the admissible source family `smoothSources hT W` into a pointwise vanishing
statement.  Concretely it provides:

* `exists_smooth_time_bump_at` / `exists_smooth_time_bump_on` — a genuine `C^∞` bump
  supported in **any** prescribed nonempty interval compactly contained in `(0,T)`,
  together with the nonnegativity and normalization facts actually used later
  (the v5.0 `exists_smooth_time_bump` only produced the bump centred at `T/2`);
* `eq_zero_of_forall_time_bump` — the **time test separation lemma**: a continuous real
  function whose integral against every such bump vanishes is identically zero on `[0,T]`;
* `eq_zero_on_of_forall_smoothProfile` — the **spatial test separation lemma** on `W`,
  built from the smooth localized profiles of `SmoothSource`: a continuous function whose
  spatial integral against every smooth profile supported in `W` vanishes is zero on `W`.

Both separation lemmas are proved from scratch (positivity of the measure of nonempty open
sets on the torus, and strict positivity of the interval integral of a continuous function
that is positive somewhere and nonnegative everywhere).  No density assumption is used.

Part of `LiWangFormalizationTerminalControlPacket` v6.0.
-/
import LiWangFormalization.SmoothSpacetimeSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.Formalization

/-! ## 1. Smooth time bumps on a prescribed interval -/

/-- The `C^∞` bump centred at `s₀`, equal to `1` on `[s₀ - ρ/2, s₀ + ρ/2]` and vanishing
outside `(s₀ - ρ, s₀ + ρ)`. -/
noncomputable def timeBumpAt (s₀ ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump s₀ :=
  ⟨ρ / 2, ρ, by linarith, by linarith⟩

theorem timeBumpAt_zero {s₀ ρ : ℝ} (hρ : 0 < ρ) {t : ℝ} (h : ρ ≤ |t - s₀|) :
    timeBumpAt s₀ ρ hρ t = 0 := by
  refine (timeBumpAt s₀ ρ hρ).zero_of_le_dist ?_
  show ρ ≤ |t - s₀|
  exact h

theorem timeBumpAt_one {s₀ ρ : ℝ} (hρ : 0 < ρ) {t : ℝ} (h : |t - s₀| ≤ ρ / 2) :
    timeBumpAt s₀ ρ hρ t = 1 := by
  refine (timeBumpAt s₀ ρ hρ).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall]
  exact h

theorem timeBumpAt_nonneg {s₀ ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) : 0 ≤ timeBumpAt s₀ ρ hρ t :=
  (timeBumpAt s₀ ρ hρ).nonneg

/-- **A `C^∞` time bump centred at a prescribed interior point.**  It is nonnegative,
identically `1` on the half-radius interval, and supported in `[s₀-ρ, s₀+ρ] ⊂ (0,T)`. -/
theorem exists_smooth_time_bump_at {T s₀ ρ : ℝ} (hρ : 0 < ρ)
    (h0 : 0 < s₀ - ρ) (h1 : s₀ + ρ < T) :
    ∃ χ : ℝ → ℝ, IsSmoothTimeBump T χ ∧ (∀ t, 0 ≤ χ t) ∧
      (∀ t, ρ ≤ |t - s₀| → χ t = 0) ∧ (∀ t, |t - s₀| ≤ ρ / 2 → χ t = 1) := by
  have hout : ∀ t ∉ Set.Icc (s₀ - ρ) (s₀ + ρ), ρ ≤ |t - s₀| := by
    intro t ht
    rcases not_and_or.1 (fun h : s₀ - ρ ≤ t ∧ t ≤ s₀ + ρ => ht ⟨h.1, h.2⟩) with h | h
    · have := not_le.1 h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have := not_le.1 h
      rw [abs_of_nonneg (by linarith)]; linarith
  refine ⟨timeBumpAt s₀ ρ hρ, ⟨(timeBumpAt s₀ ρ hρ).contDiff,
      ⟨s₀ - ρ, s₀ + ρ, h0, by linarith, h1, fun t ht => timeBumpAt_zero hρ (hout t ht)⟩⟩,
    timeBumpAt_nonneg hρ, fun t ht => timeBumpAt_zero hρ ht,
    fun t ht => timeBumpAt_one hρ ht⟩

/-- **A `C^∞` time bump supported in a prescribed interval `(c,d)` compactly contained in
`(0,T)`**, nonnegative and equal to `1` at the midpoint. -/
theorem exists_smooth_time_bump_on {T c d : ℝ} (hc : 0 < c) (hcd : c < d) (hdT : d < T) :
    ∃ χ : ℝ → ℝ, IsSmoothTimeBump T χ ∧ (∀ t, 0 ≤ χ t) ∧
      (∀ t ∉ Set.Ioo c d, χ t = 0) ∧ χ ((c + d) / 2) = 1 := by
  have hρ : (0:ℝ) < (d - c) / 2 := by linarith
  obtain ⟨χ, hbump, hnn, hzero, hone⟩ :=
    exists_smooth_time_bump_at (T := T) (s₀ := (c + d) / 2) (ρ := (d - c) / 2) hρ
      (by linarith) (by linarith)
  refine ⟨χ, hbump, hnn, fun t ht => hzero t ?_, hone _ (by rw [sub_self, abs_zero]; positivity)⟩
  rcases not_and_or.1 (fun h : c < t ∧ t < d => ht ⟨h.1, h.2⟩) with h | h
  · have := not_lt.1 h
    rw [abs_of_nonpos (by linarith)]; linarith
  · have := not_lt.1 h
    rw [abs_of_nonneg (by linarith)]; linarith

/-! ## 2. Time test separation -/

/-- Auxiliary half of the time separation lemma: a continuous function all of whose smooth
time-bump integrals vanish cannot be strictly positive at an interior point. -/
theorem not_pos_of_forall_time_bump {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ χ : ℝ → ℝ, IsSmoothTimeBump T χ → (∫ t in (0:ℝ)..T, χ t * f t) = 0)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0:ℝ) T) : ¬ (0 < f s₀) := by
  intro hpos
  have hUopen : IsOpen (Set.Ioo (0:ℝ) T ∩ {t | 0 < f t}) :=
    isOpen_Ioo.inter (isOpen_lt continuous_const hf)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUopen s₀ ⟨hs₀, hpos⟩
  set ρ : ℝ := ε / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hsub : ∀ t, |t - s₀| ≤ ρ → t ∈ Set.Ioo (0:ℝ) T ∩ {t | 0 < f t} := by
    intro t ht
    refine hball ?_
    rw [Metric.mem_ball]
    show |t - s₀| < ε
    rw [hρdef] at ht; linarith
  have hL := hsub (s₀ - ρ) (by rw [show s₀ - ρ - s₀ = -ρ by ring, abs_neg, abs_of_pos hρ])
  have hR := hsub (s₀ + ρ) (by rw [show s₀ + ρ - s₀ = ρ by ring, abs_of_pos hρ])
  have h0 : 0 < s₀ - ρ := hL.1.1
  have h1 : s₀ + ρ < T := hR.1.2
  obtain ⟨χ, hbump, hnn, hzero, hone⟩ := exists_smooth_time_bump_at (T := T) hρ h0 h1
  set F : ℝ → ℝ := fun t => χ t * f t with hFdef
  have hFc : Continuous F := hbump.continuous.mul hf
  have hInt : ∀ u v : ℝ, IntervalIntegrable F volume u v := fun u v =>
    hFc.intervalIntegrable u v
  -- the outer pieces vanish
  have hI1 : (∫ t in (0:ℝ)..(s₀ - ρ), F t) = 0 := by
    have heq : Set.EqOn F 0 (Set.uIcc (0:ℝ) (s₀ - ρ)) := by
      intro t ht
      rw [Set.uIcc_of_le h0.le] at ht
      show χ t * f t = 0
      rw [hzero t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]), zero_mul]
    rw [intervalIntegral.integral_congr heq]
    simp
  have hI3 : (∫ t in (s₀ + ρ)..T, F t) = 0 := by
    have heq : Set.EqOn F 0 (Set.uIcc (s₀ + ρ) T) := by
      intro t ht
      rw [Set.uIcc_of_le h1.le] at ht
      show χ t * f t = 0
      rw [hzero t (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.1]), zero_mul]
    rw [intervalIntegral.integral_congr heq]
    simp
  -- the middle piece is strictly positive
  have hmid : 0 < ∫ t in (s₀ - ρ/2)..(s₀ + ρ/2), F t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hInt _ _) (fun x hx => ?_)
      (by linarith)
    have hx2 : |x - s₀| ≤ ρ / 2 := by
      rcases le_total x s₀ with hle | hlt
      · rw [abs_of_nonpos (by linarith)]; linarith [hx.1]
      · rw [abs_of_nonneg (by linarith)]; linarith [hx.2]
    have hfx : 0 < f x := (hsub x (by linarith)).2
    show 0 < χ x * f x
    rw [hone x hx2, one_mul]
    exact hfx
  have hleft : 0 ≤ ∫ t in (s₀ - ρ)..(s₀ - ρ/2), F t := by
    refine intervalIntegral.integral_nonneg (by linarith) (fun u hu => ?_)
    have hu2 : |u - s₀| ≤ ρ := by
      rw [abs_of_nonpos (by linarith [hu.2])]; linarith [hu.1]
    exact mul_nonneg (hnn u) (hsub u hu2).2.le
  have hright : 0 ≤ ∫ t in (s₀ + ρ/2)..(s₀ + ρ), F t := by
    refine intervalIntegral.integral_nonneg (by linarith) (fun u hu => ?_)
    have hu2 : |u - s₀| ≤ ρ := by
      rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2]
    exact mul_nonneg (hnn u) (hsub u hu2).2.le
  -- reassemble
  have hA : (∫ t in (s₀ - ρ)..(s₀ - ρ/2), F t) + (∫ t in (s₀ - ρ/2)..(s₀ + ρ/2), F t)
      = ∫ t in (s₀ - ρ)..(s₀ + ρ/2), F t :=
    intervalIntegral.integral_add_adjacent_intervals (hInt _ _) (hInt _ _)
  have hB : (∫ t in (s₀ - ρ)..(s₀ + ρ/2), F t) + (∫ t in (s₀ + ρ/2)..(s₀ + ρ), F t)
      = ∫ t in (s₀ - ρ)..(s₀ + ρ), F t :=
    intervalIntegral.integral_add_adjacent_intervals (hInt _ _) (hInt _ _)
  have hC : (∫ t in (0:ℝ)..(s₀ - ρ), F t) + (∫ t in (s₀ - ρ)..(s₀ + ρ), F t)
      = ∫ t in (0:ℝ)..(s₀ + ρ), F t :=
    intervalIntegral.integral_add_adjacent_intervals (hInt _ _) (hInt _ _)
  have hD : (∫ t in (0:ℝ)..(s₀ + ρ), F t) + (∫ t in (s₀ + ρ)..T, F t)
      = ∫ t in (0:ℝ)..T, F t :=
    intervalIntegral.integral_add_adjacent_intervals (hInt _ _) (hInt _ _)
  have htotal : (∫ t in (0:ℝ)..T, F t) = 0 := h χ hbump
  linarith

/-- **Time test separation.**  If a continuous real function integrates to zero against every
`C^∞` bump compactly supported in `(0,T)`, it vanishes on all of `[0,T]`. -/
theorem eq_zero_of_forall_time_bump {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ χ : ℝ → ℝ, IsSmoothTimeBump T χ → (∫ t in (0:ℝ)..T, χ t * f t) = 0) :
    ∀ t ∈ Set.Icc (0:ℝ) T, f t = 0 := by
  have hneg : ∀ χ : ℝ → ℝ, IsSmoothTimeBump T χ → (∫ t in (0:ℝ)..T, χ t * (-f) t) = 0 := by
    intro χ hχ
    have : (∫ t in (0:ℝ)..T, χ t * (-f) t) = -(∫ t in (0:ℝ)..T, χ t * f t) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      show χ t * (-f t) = -(χ t * f t)
      ring
    rw [this, h χ hχ, neg_zero]
  have hopen : ∀ s ∈ Set.Ioo (0:ℝ) T, f s = 0 := by
    intro s hs
    have h1 := not_pos_of_forall_time_bump hf h hs
    have h2 := not_pos_of_forall_time_bump hf.neg hneg hs
    have h2' : ¬ (0 < -f s) := h2
    rcases lt_trichotomy (f s) 0 with hlt | heq | hgt
    · exact absurd (by linarith : (0:ℝ) < -f s) h2'
    · exact heq
    · exact absurd hgt h1
  have hclosed : IsClosed {t : ℝ | f t = 0} := isClosed_eq hf continuous_const
  have hsub : Set.Ioo (0:ℝ) T ⊆ {t : ℝ | f t = 0} := hopen
  have := closure_minimal hsub hclosed
  rw [closure_Ioo (ne_of_lt hT)] at this
  exact this

/-- A bump for a shorter horizon is a bump for a longer one. -/
theorem IsSmoothTimeBump.mono {T T' : ℝ} {χ : ℝ → ℝ} (h : IsSmoothTimeBump T χ)
    (hTT' : T ≤ T') : IsSmoothTimeBump T' χ := by
  obtain ⟨t₀, t₁, h0, h01, h1, hv⟩ := h.supp
  exact ⟨h.smooth, ⟨t₀, t₁, h0, h01, lt_of_lt_of_le h1 hTT', hv⟩⟩

/-- **Time test separation, complex-valued form.** -/
theorem eq_zero_of_forall_time_bump_complex {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ}
    (hf : Continuous f)
    (h : ∀ χ : ℝ → ℝ, IsSmoothTimeBump T χ → (∫ t in (0:ℝ)..T, (χ t : ℂ) * f t) = 0) :
    ∀ t ∈ Set.Icc (0:ℝ) T, f t = 0 := by
  have hproj : ∀ (L : ℂ →L[ℝ] ℝ), (∀ r : ℝ, ∀ z : ℂ, L ((r : ℂ) * z) = r * L z) →
      ∀ χ : ℝ → ℝ, IsSmoothTimeBump T χ → (∫ t in (0:ℝ)..T, χ t * L (f t)) = 0 := by
    intro L hL χ hχ
    have hint : IntervalIntegrable (fun t => (χ t : ℂ) * f t) volume 0 T :=
      ((Complex.continuous_ofReal.comp hχ.continuous).mul hf).intervalIntegrable 0 T
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm L hint
    rw [h χ hχ, map_zero] at hcomm
    have hcongr : (∫ t in (0:ℝ)..T, χ t * L (f t))
        = ∫ t in (0:ℝ)..T, L ((χ t : ℂ) * f t) :=
      intervalIntegral.integral_congr (f := fun t : ℝ => χ t * L (f t))
        (g := fun t : ℝ => L ((χ t : ℂ) * f t)) (fun t _ => (hL (χ t) (f t)).symm)
    rw [hcongr]
    exact hcomm
  have hre := hproj Complex.reCLM (fun r z => by
    show ((r : ℂ) * z).re = r * z.re
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero])
  have him := hproj Complex.imCLM (fun r z => by
    show ((r : ℂ) * z).im = r * z.im
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero])
  intro t ht
  have h1 := eq_zero_of_forall_time_bump hT (Complex.continuous_re.comp hf) hre t ht
  have h2 := eq_zero_of_forall_time_bump hT (Complex.continuous_im.comp hf) him t ht
  exact Complex.ext (by simpa using h1) (by simpa using h2)

/-! ## 3. Spatial test separation on `W` -/

theorem smoothProfiles_mono {V W : Set Torus2} (hVW : V ⊆ W) :
    smoothProfiles V ≤ smoothProfiles W := by
  rintro a ⟨hsa, K, hKc, hKV, hvan⟩
  exact ⟨hsa, K, hKc, hKV.trans hVW, hvan⟩

/-- **Spatial test separation on `W`.**  A continuous function on the torus whose integral
against every smooth profile compactly supported in `W` vanishes is identically zero on `W`.

The proof uses the smooth localized bumps of `exists_smooth_bump_at`: a nonnegative real
profile equal to `1` at a prescribed point of `W` and supported in a compact subset of the
open set where the (rotated) test function has positive real part. -/
theorem eq_zero_on_of_forall_smoothProfile {W : Set Torus2} (hW : IsOpen W)
    {v : Torus2 → ℂ} (hv : Continuous v)
    (h : ∀ a ∈ smoothProfiles W, (∫ x : Torus2, v x * synth a.val x) = 0) :
    ∀ x ∈ W, v x = 0 := by
  intro x₀ hx₀
  by_contra hne
  -- the open set on which `v` has positive component along `v x₀`
  set u : Torus2 → ℝ := fun x => (conj (v x₀) * v x).re with hudef
  have huc : Continuous u := by
    have : Continuous fun x : Torus2 => conj (v x₀) * v x := continuous_const.mul hv
    exact Complex.continuous_re.comp this
  have hu0 : 0 < u x₀ := by
    have : conj (v x₀) * v x₀ = ((‖v x₀‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; norm_cast
    rw [hudef]
    show 0 < (conj (v x₀) * v x₀).re
    rw [this, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.2 hne) 2
  set V : Set Torus2 := W ∩ {x | 0 < u x} with hVdef
  have hVopen : IsOpen V := hW.inter (isOpen_lt continuous_const huc)
  have hx₀V : x₀ ∈ V := ⟨hx₀, hu0⟩
  obtain ⟨a, K, hsm, hKc, hKV, hvan, hre, haone⟩ := exists_smooth_bump_at hVopen hx₀V
  have haV : a ∈ smoothProfiles V := ⟨hsm, K, hKc, hKV, hvan⟩
  have haW : a ∈ smoothProfiles W :=
    smoothProfiles_mono (W := W) (V := V) Set.inter_subset_left haV
  -- the rotated real integrand
  set F : Torus2 → ℝ := fun x => u x * (synth a.val x).re with hFdef
  have hFc : Continuous F := huc.mul (Complex.continuous_re.comp (synth a.val).continuous)
  have hFnn : 0 ≤ F := by
    intro x
    by_cases hx : x ∈ K
    · exact mul_nonneg (hKV hx).2.le (hre x).2
    · show 0 ≤ u x * (synth a.val x).re
      rw [hvan x hx]
      simp
  have hFint : Integrable F (volume : Measure Torus2) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the integral of `F` is the real part of a vanishing integral
  have hgint : Integrable (fun x : Torus2 => conj (v x₀) * (v x * synth a.val x))
      (volume : Measure Torus2) :=
    ((continuous_const.mul (hv.mul (synth a.val).continuous))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFeq : ∀ x : Torus2, F x = Complex.reCLM (conj (v x₀) * (v x * synth a.val x)) := by
    intro x
    have hrx : synth a.val x = (((synth a.val x).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [(hre x).1]
    show u x * (synth a.val x).re = (conj (v x₀) * (v x * synth a.val x)).re
    rw [hrx]
    rw [show conj (v x₀) * (v x * (((synth a.val x).re : ℝ) : ℂ))
        = (conj (v x₀) * v x) * (((synth a.val x).re : ℝ) : ℂ) by ring]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hzero : (∫ x : Torus2, F x) = 0 := by
    rw [show (∫ x : Torus2, F x)
        = ∫ x : Torus2, Complex.reCLM (conj (v x₀) * (v x * synth a.val x)) from
      integral_congr_ae (Filter.Eventually.of_forall hFeq)]
    rw [ContinuousLinearMap.integral_comp_comm Complex.reCLM hgint]
    have hpull : (∫ x : Torus2, conj (v x₀) * (v x * synth a.val x))
        = conj (v x₀) * ∫ x : Torus2, v x * synth a.val x :=
      integral_const_mul (μ := (volume : Measure Torus2)) (conj (v x₀))
        (fun x => v x * synth a.val x)
    rw [hpull, h a haW, mul_zero]
    simp
  -- but `F` is nonnegative with a positive value, so its integral is positive
  have hx₀F : 0 < F x₀ := by
    show 0 < u x₀ * (synth a.val x₀).re
    rw [haone]
    simpa using hu0
  have hopenF : IsOpen {x : Torus2 | 0 < F x} := isOpen_lt continuous_const hFc
  have hposF := hopenF.measure_pos (volume : Measure Torus2) ⟨x₀, hx₀F⟩
  have hmono : {x : Torus2 | 0 < F x} ⊆ Function.support F := fun x hx => ne_of_gt hx
  have hsupp := lt_of_lt_of_le hposF (measure_mono hmono)
  have := (integral_pos_iff_support_of_nonneg hFnn hFint).2 hsupp
  rw [hzero] at this
  exact lt_irrefl 0 this

end LiWang.Formalization
