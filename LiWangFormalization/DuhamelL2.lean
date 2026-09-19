/-
# `L²`-in-time control of the fractional multiplier along the Duhamel response

For a source curve `g` and its Duhamel response `u = J_T g`, every Fourier coefficient
satisfies the scalar equation `u_k' + λ_k u_k = g_k` with `u_k(0) = 0`
(`CoefficientODE.lean`).  A pointwise **energy estimate** for that scalar equation gives

    λ_k² ∫₀^T |u_k(t)|² dt  ≤  ∫₀^T |g_k(t)|² dt      (every `k`, including `k = 0`),

with no constant, and the zero mode handled separately: `λ_0 = 0`, so the inequality is
trivial there and no division by `λ` ever occurs.  Summation over `k` (through finite partial
sums, so no interchange is assumed) gives the concrete estimate

    ∑_k λ_k² ∫₀^T |u_k(t)|² dt  ≤  ∑_k ∫₀^T |g_k(t)|² dt  ≤  T ‖g‖² .

Part of `LiWangFormalizationObservationBridgePacket` v4.0.
-/
import LiWangFormalization.CoefficientODE

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace LiWang.Formalization

/-! ## The derivative of the squared modulus -/

theorem hasDerivAt_normSq_comp {w : ℝ → ℂ} {w' : ℂ} {t : ℝ} (h : HasDerivAt w w' t) :
    HasDerivAt (fun s => ‖w s‖ ^ 2) (2 * (conj (w t) * w').re) t := by
  have hre : HasDerivAt (fun s => (w s).re) w'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have him : HasDerivAt (fun s => (w s).im) w'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  have hsq : HasDerivAt (fun s => (w s).re * (w s).re + (w s).im * (w s).im)
      (w'.re * (w t).re + (w t).re * w'.re + (w'.im * (w t).im + (w t).im * w'.im)) t :=
    (hre.mul hre).add (him.mul him)
  have hfun : (fun s => ‖w s‖ ^ 2)
      = fun s => (w s).re * (w s).re + (w s).im * (w s).im := by
    funext s
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hfun]
  convert hsq using 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-! ## The scalar energy estimate -/

/-- **The energy estimate for `w' + λ w = g` with `w(0) = 0`.**  No constant, and no
smallness or sign assumption beyond `λ > 0`. -/
theorem energy_estimate {T lam : ℝ} (hT : 0 ≤ T) (hlam : 0 < lam) {w g : ℝ → ℂ}
    (hw : Continuous w) (hg : Continuous g) (hw0 : w 0 = 0)
    (hderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt w (g t - (lam : ℂ) * w t) t) :
    lam ^ 2 * (∫ t in (0:ℝ)..T, ‖w t‖ ^ 2) ≤ ∫ t in (0:ℝ)..T, ‖g t‖ ^ 2 := by
  set E : ℝ → ℝ := fun t => ‖w t‖ ^ 2 with hE
  set P : ℝ → ℝ := fun t => 2 * (conj (w t) * g t).re with hP
  set D : ℝ → ℝ := fun t => P t - 2 * lam * E t with hD
  have hEcont : Continuous E := (hw.norm).pow 2
  have hPcont : Continuous P :=
    continuous_const.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp hw).mul hg))
  have hDcont : Continuous D := hPcont.sub ((continuous_const.mul hEcont))
  -- the derivative of the energy on the open interval
  have hEderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivWithinAt E (D t) (Set.Ioi t) t := by
    intro t ht
    have h := hasDerivAt_normSq_comp (hderiv t ht)
    have hval : 2 * (conj (w t) * (g t - (lam : ℂ) * w t)).re = D t := by
      have hcc : conj (w t) * w t = ((‖w t‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']; norm_cast
      have hexp : (conj (w t) * (g t - (lam : ℂ) * w t))
          = conj (w t) * g t - (lam : ℂ) * ((‖w t‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hcc]; ring
      have hre2 : ((lam : ℂ) * ((‖w t‖ ^ 2 : ℝ) : ℂ)).re = lam * ‖w t‖ ^ 2 := by
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
      rw [hexp, Complex.sub_re, hre2]
      show 2 * ((conj (w t) * g t).re - lam * ‖w t‖ ^ 2) = D t
      simp only [hD, hE, hP]
      ring
    rw [hval] at h
    exact h.hasDerivWithinAt
  -- the fundamental theorem of calculus
  have hFTC : (∫ t in (0:ℝ)..T, D t) = E T - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hEcont.continuousOn hEderiv
      (hDcont.intervalIntegrable 0 T)
  have hE0 : E 0 = 0 := by rw [hE]; simp [hw0]
  have hET : 0 ≤ E T := by positivity
  have hDint : 0 ≤ ∫ t in (0:ℝ)..T, D t := by rw [hFTC, hE0, sub_zero]; exact hET
  -- split the integral
  have hsplit : (∫ t in (0:ℝ)..T, D t)
      = (∫ t in (0:ℝ)..T, P t) - 2 * lam * ∫ t in (0:ℝ)..T, E t := by
    have h1 := intervalIntegral.integral_sub (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := T)
      (f := P) (g := fun t => (2 * lam) * E t) (hPcont.intervalIntegrable 0 T)
      (((continuous_const.mul hEcont : Continuous fun t => (2 * lam) * E t)).intervalIntegrable 0 T)
    have h2 := intervalIntegral.integral_const_mul (μ := (volume : Measure ℝ)) (a := (0:ℝ))
      (b := T) (2 * lam) E
    calc (∫ t in (0:ℝ)..T, D t) = ∫ t in (0:ℝ)..T, (P t - (2 * lam) * E t) := rfl
      _ = (∫ t in (0:ℝ)..T, P t) - ∫ t in (0:ℝ)..T, (2 * lam) * E t := h1
      _ = (∫ t in (0:ℝ)..T, P t) - 2 * lam * ∫ t in (0:ℝ)..T, E t := by rw [h2]
  -- Young's inequality, pointwise
  have hyoung : ∀ t ∈ Set.Icc (0:ℝ) T, P t ≤ lam * E t + (1 / lam) * ‖g t‖ ^ 2 := by
    intro t _
    have h1 : (conj (w t) * g t).re ≤ ‖conj (w t) * g t‖ := Complex.re_le_norm _
    have h2 : ‖conj (w t) * g t‖ = ‖w t‖ * ‖g t‖ := by
      rw [norm_mul, RCLike.norm_conj]
    have ha : (0:ℝ) ≤ ‖w t‖ := norm_nonneg _
    have hb : (0:ℝ) ≤ ‖g t‖ := norm_nonneg _
    have hkey : 2 * (‖w t‖ * ‖g t‖) ≤ lam * ‖w t‖ ^ 2 + (1 / lam) * ‖g t‖ ^ 2 := by
      have hexp : lam * (lam * ‖w t‖ ^ 2 + (1 / lam) * ‖g t‖ ^ 2)
          = lam ^ 2 * ‖w t‖ ^ 2 + ‖g t‖ ^ 2 := by
        field_simp
      have hmul : lam * (2 * (‖w t‖ * ‖g t‖))
          ≤ lam * (lam * ‖w t‖ ^ 2 + (1 / lam) * ‖g t‖ ^ 2) := by
        rw [hexp]
        nlinarith [sq_nonneg (lam * ‖w t‖ - ‖g t‖)]
      exact le_of_mul_le_mul_left hmul hlam
    have hstep : (conj (w t) * g t).re ≤ ‖w t‖ * ‖g t‖ := by
      rw [← h2]; exact h1
    calc P t = 2 * (conj (w t) * g t).re := rfl
      _ ≤ 2 * (‖w t‖ * ‖g t‖) := by linarith
      _ ≤ lam * E t + (1 / lam) * ‖g t‖ ^ 2 := hkey
  have hPle : (∫ t in (0:ℝ)..T, P t)
      ≤ lam * (∫ t in (0:ℝ)..T, E t) + (1 / lam) * ∫ t in (0:ℝ)..T, ‖g t‖ ^ 2 := by
    have hRcont : Continuous fun t : ℝ => lam * E t + (1 / lam) * ‖g t‖ ^ 2 :=
      (continuous_const.mul hEcont).add (continuous_const.mul ((hg.norm).pow 2))
    have hmono := intervalIntegral.integral_mono_on (μ := (volume : Measure ℝ)) hT
      (hPcont.intervalIntegrable 0 T) (hRcont.intervalIntegrable 0 T) hyoung
    have hadd := intervalIntegral.integral_add (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := T)
      (f := fun t : ℝ => lam * E t) (g := fun t : ℝ => (1 / lam) * ‖g t‖ ^ 2)
      ((continuous_const.mul hEcont : Continuous fun t : ℝ => lam * E t).intervalIntegrable 0 T)
      ((continuous_const.mul ((hg.norm).pow 2) :
        Continuous fun t : ℝ => (1 / lam) * ‖g t‖ ^ 2).intervalIntegrable 0 T)
    have hc1 := intervalIntegral.integral_const_mul (μ := (volume : Measure ℝ)) (a := (0:ℝ))
      (b := T) lam E
    have hc2 := intervalIntegral.integral_const_mul (μ := (volume : Measure ℝ)) (a := (0:ℝ))
      (b := T) (1 / lam) (fun t : ℝ => ‖g t‖ ^ 2)
    have hsplit2 : (∫ t in (0:ℝ)..T, (lam * E t + (1 / lam) * ‖g t‖ ^ 2))
        = lam * (∫ t in (0:ℝ)..T, E t) + (1 / lam) * ∫ t in (0:ℝ)..T, ‖g t‖ ^ 2 := by
      rw [hadd, hc1, hc2]
    rw [hsplit2] at hmono
    exact hmono
  -- combine
  have hfinal : lam * (∫ t in (0:ℝ)..T, E t) ≤ (1 / lam) * ∫ t in (0:ℝ)..T, ‖g t‖ ^ 2 := by
    rw [hsplit] at hDint
    linarith
  have hmul := mul_le_mul_of_nonneg_left hfinal hlam.le
  rw [← mul_assoc, ← mul_assoc] at hmul
  have hcancel : lam * (1 / lam) = 1 := by field_simp
  rw [hcancel, one_mul] at hmul
  calc lam ^ 2 * (∫ t in (0:ℝ)..T, ‖w t‖ ^ 2) = lam * lam * ∫ t in (0:ℝ)..T, E t := by
        rw [hE]; ring
    _ ≤ ∫ t in (0:ℝ)..T, ‖g t‖ ^ 2 := hmul

/-! ## The fractional symbol at the zero mode -/

theorem fracSymbol_pos {α : ℝ} {k : Gam} (hk : k ≠ 0) : 0 < fracSymbol α k := by
  have h1 : (0:ℝ) < 4 * Real.pi ^ 2 * sqNorm k := by
    have := one_le_sqNorm hk
    have hpi := Real.pi_pos
    positivity
  exact Real.rpow_pos_of_pos h1 α

/-- **The zero mode.**  `λ₀ = 0`, so no division by `λ` is ever performed there and the
energy estimate holds trivially. -/
theorem fracSymbol_zero_eq {α : ℝ} (hα : 0 < α) : fracSymbol α (0 : Gam) = 0 := by
  have hs : sqNorm (0 : Gam) = 0 := by
    show (((0 : Gam) 0 : ℤ) : ℝ) ^ 2 + (((0 : Gam) 1 : ℤ) : ℝ) ^ 2 = 0
    norm_num
  rw [fracSymbol, hs, mul_zero, Real.zero_rpow (ne_of_gt hα)]

/-! ## The per-mode estimate for the Duhamel response -/

variable {α T : ℝ}

/-- **The `L²`-in-time energy estimate for one Fourier mode of the Duhamel response.**  The
zero mode is included: there `λ₀ = 0` and the inequality is trivial. -/
theorem integral_fracSymbol_sq_coeff_duhamelOp_le (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (g : Curve0 T) (k : Gam) :
    (fracSymbol α k) ^ 2
        * (∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2)
      ≤ ∫ t in (0:ℝ)..T, ‖(sourceFun hT g t) k‖ ^ 2 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hgcont : Continuous fun r : ℝ => (sourceFun hT g r) k :=
    continuous_wiener_coeff k (continuous_sourceFun hT g)
  have hRnn : 0 ≤ ∫ t in (0:ℝ)..T, ‖(sourceFun hT g t) k‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun t _ => by positivity)
  by_cases hk : k = 0
  · subst hk
    rw [fracSymbol_zero_eq hα0]
    simpa using hRnn
  · have hpos : 0 < fracSymbol α k := fracSymbol_pos hk
    refine energy_estimate hT hpos (continuous_coeff_curveState hT _ k) hgcont
      (coeff_duhamelOp_initial hα hT g k) ?_
    intro t ht
    exact hasDerivAt_coeff_duhamelOp hα hT g k ht.1 ht.2

/-! ## Summation over the frequencies -/

theorem finset_sum_norm_le (a : Wiener) (F : Finset Gam) : ∑ k ∈ F, ‖a k‖ ≤ ‖a‖ := by
  rw [wiener_norm_eq]
  exact Summable.sum_le_tsum F (fun i _ => norm_nonneg _) (wiener_summable a)

theorem finset_sum_norm_sq_le (a : Wiener) (F : Finset Gam) : ∑ k ∈ F, ‖a k‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have h1 : ∑ k ∈ F, ‖a k‖ ^ 2 ≤ (∑ k ∈ F, ‖a k‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
  have h2 : (∑ k ∈ F, ‖a k‖) ≤ ‖a‖ := finset_sum_norm_le a F
  have h3 : (0:ℝ) ≤ ∑ k ∈ F, ‖a k‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  nlinarith

/-- Every finite partial sum of the mode-wise `L²`-in-time energies of the source is bounded
by `T ‖g‖²`.  No interchange of sum and integral is assumed: the sums here are finite. -/
theorem finset_sum_integral_source_sq_le (hT : 0 ≤ T) (g : Curve0 T) (F : Finset Gam) :
    ∑ k ∈ F, (∫ t in (0:ℝ)..T, ‖(sourceFun hT g t) k‖ ^ 2) ≤ T * ‖g‖ ^ 2 := by
  have hcont : ∀ k : Gam, Continuous fun t : ℝ => ‖(sourceFun hT g t) k‖ ^ 2 := fun k =>
    ((continuous_wiener_coeff k (continuous_sourceFun hT g)).norm).pow 2
  have hswap := intervalIntegral.integral_finset_sum (μ := (volume : Measure ℝ)) (a := (0:ℝ))
    (b := T) (s := F) (f := fun (k : Gam) (t : ℝ) => ‖(sourceFun hT g t) k‖ ^ 2)
    (fun k _ => (hcont k).intervalIntegrable 0 T)
  have hptwise : ∀ t ∈ Set.Icc (0:ℝ) T,
      (∑ k ∈ F, ‖(sourceFun hT g t) k‖ ^ 2) ≤ ‖g‖ ^ 2 := by
    intro t _
    refine le_trans (finset_sum_norm_sq_le (sourceFun hT g t) F) ?_
    have h := norm_sourceFun_le hT g t
    have h0 : (0:ℝ) ≤ ‖sourceFun hT g t‖ := norm_nonneg _
    nlinarith
  have hsumcont : Continuous fun t : ℝ => ∑ k ∈ F, ‖(sourceFun hT g t) k‖ ^ 2 :=
    continuous_finset_sum F (fun k _ => hcont k)
  have hmono := intervalIntegral.integral_mono_on (μ := (volume : Measure ℝ)) hT
    (hsumcont.intervalIntegrable 0 T) (intervalIntegrable_const) hptwise
  rw [← hswap]
  refine le_trans hmono ?_
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

theorem summable_integral_source_sq (hT : 0 ≤ T) (g : Curve0 T) :
    Summable fun k : Gam => ∫ t in (0:ℝ)..T, ‖(sourceFun hT g t) k‖ ^ 2 :=
  summable_of_sum_le (fun k => intervalIntegral.integral_nonneg hT (fun t _ => by positivity))
    (fun F => finset_sum_integral_source_sq_le hT g F)

theorem tsum_integral_source_sq_le (hT : 0 ≤ T) (g : Curve0 T) :
    (∑' k : Gam, ∫ t in (0:ℝ)..T, ‖(sourceFun hT g t) k‖ ^ 2) ≤ T * ‖g‖ ^ 2 := by
  refine tsum_le_of_sum_le' (by positivity) ?_
  intro F
  exact finset_sum_integral_source_sq_le hT g F

/-- **The concrete `L²`-in-time estimate on the fractional multiplier of the Duhamel
response.**  With `λ_k = (4π²|k|²)^α` and `u = J_T g`,

    `∑_k λ_k² ∫₀^T |u_k(t)|² dt ≤ ∑_k ∫₀^T |g_k(t)|² dt ≤ T ‖g‖²`. -/
theorem summable_integral_fracSymbol_sq (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    Summable fun k : Gam => (fracSymbol α k) ^ 2
      * ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_integral_source_sq hT g)
  · have h1 : (0:ℝ) ≤ (fracSymbol α k) ^ 2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT (fun t _ => by positivity)
    exact mul_nonneg h1 h2
  · exact integral_fracSymbol_sq_coeff_duhamelOp_le hα hT g k

theorem tsum_integral_fracSymbol_sq_le (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    (∑' k : Gam, (fracSymbol α k) ^ 2
        * ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2)
      ≤ T * ‖g‖ ^ 2 := by
  refine le_trans ?_ (tsum_integral_source_sq_le hT g)
  exact Summable.tsum_le_tsum (fun k => integral_fracSymbol_sq_coeff_duhamelOp_le hα hT g k)
    (summable_integral_fracSymbol_sq hα hT g) (summable_integral_source_sq hT g)

/-! ## The integrated (Bochner) form of the strong equation -/

/-- **The integrated strong equation for one mode.**  If `w' + λ w = g` on the open interval
with `w(0) = 0`, then `w(t) + λ ∫₀ᵗ w = ∫₀ᵗ g` at every time of the closed interval.  This is
the coefficient form of `u(t) + ∫₀ᵗ (-Δ)^α u = ∫₀ᵗ g` in the Bochner sense. -/
theorem integrated_equation {T lam : ℝ} {w g : ℝ → ℂ} (hw : Continuous w) (hg : Continuous g)
    (hw0 : w 0 = 0)
    (hderiv : ∀ s ∈ Set.Ioo (0:ℝ) T, HasDerivAt w (g s - (lam : ℂ) * w s) s)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    w t + (lam : ℂ) * (∫ s in (0:ℝ)..t, w s) = ∫ s in (0:ℝ)..t, g s := by
  set Φ : ℝ → ℂ := fun r => w r + (lam : ℂ) * (∫ s in (0:ℝ)..r, w s) - ∫ s in (0:ℝ)..r, g s
    with hΦ
  have hWint : Continuous fun r : ℝ => ∫ s in (0:ℝ)..r, w s :=
    intervalIntegral.continuous_primitive (fun a b => hw.intervalIntegrable a b) 0
  have hGint : Continuous fun r : ℝ => ∫ s in (0:ℝ)..r, g s :=
    intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0
  have hΦcont : Continuous Φ := (hw.add (continuous_const.mul hWint)).sub hGint
  have hΦderiv : ∀ r ∈ Set.Ioo (0:ℝ) t, HasDerivWithinAt Φ 0 (Set.Ioi r) r := by
    intro r hr
    have hrT : r ∈ Set.Ioo (0:ℝ) T := ⟨hr.1, lt_of_lt_of_le hr.2 ht.2⟩
    have hW : HasDerivAt (fun q : ℝ => ∫ s in (0:ℝ)..q, w s) (w r) r :=
      intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 r)
        (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt
    have hG : HasDerivAt (fun q : ℝ => ∫ s in (0:ℝ)..q, g s) (g r) r :=
      intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
        (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
    have hsum := ((hderiv r hrT).add ((hW.const_mul (lam : ℂ)))).sub hG
    have hzero : (g r - (lam : ℂ) * w r) + (lam : ℂ) * w r - g r = 0 := by ring
    rw [hzero] at hsum
    exact hsum.hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    hΦcont.continuousOn hΦderiv (intervalIntegrable_const (c := (0 : ℂ)))
  have hΦ0 : Φ 0 = 0 := by
    simp only [hΦ, hw0, intervalIntegral.integral_same]
    ring
  rw [intervalIntegral.integral_zero, hΦ0, sub_zero] at hFTC
  have hzero : (w t + (lam : ℂ) * (∫ s in (0:ℝ)..t, w s)) - ∫ s in (0:ℝ)..t, g s = 0 := by
    have := hFTC.symm
    rw [hΦ] at this
    exact this
  exact sub_eq_zero.mp hzero

/-- **The integrated strong equation for the Duhamel response**, coefficient by coefficient. -/
theorem coeff_duhamelOp_integrated (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT (duhamelOp hα hT g) t).coeff k
        + (fracSymbol α k : ℂ)
            * ∫ s in (0:ℝ)..t, (curveState hT (duhamelOp hα hT g) s).coeff k
      = ∫ s in (0:ℝ)..t, (sourceFun hT g s) k :=
  integrated_equation (continuous_coeff_curveState hT _ k)
    (continuous_wiener_coeff k (continuous_sourceFun hT g))
    (coeff_duhamelOp_initial hα hT g k)
    (fun s hs => hasDerivAt_coeff_duhamelOp hα hT g k hs.1 hs.2) ht

/-! ## Almost-everywhere square summability -/

/-- If a family of continuous nonnegative functions has summable time integrals, then for
almost every time the family itself is summable.  This is the (Tonelli) interchange used to
pass from the mode-wise `L²`-in-time estimate to pointwise-in-time square summability. -/
theorem ae_summable_of_summable_integral {T : ℝ} (hT : 0 ≤ T) {F : Gam → ℝ → ℝ}
    (hcont : ∀ k, Continuous (F k)) (hnn : ∀ k t, 0 ≤ F k t)
    (hsum : Summable fun k => ∫ t in (0:ℝ)..T, F k t) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)), Summable fun k => F k t := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T) with hμ
  set G : Gam → ℝ → ℝ≥0∞ := fun k t => ENNReal.ofReal (F k t) with hG
  have hmeas : ∀ k, AEMeasurable (G k) μ := fun k =>
    (ENNReal.measurable_ofReal.comp (hcont k).measurable).aemeasurable
  have hlint : ∀ k, (∫⁻ t, G k t ∂μ) = ENNReal.ofReal (∫ t in (0:ℝ)..T, F k t) := by
    intro k
    rw [intervalIntegral.integral_of_le hT]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((hcont k).integrableOn_Ioc) (Filter.Eventually.of_forall (fun t => hnn k t))).symm
  have hfin : (∑' k : Gam, ∫⁻ t, G k t ∂μ) ≠ ⊤ := by
    have hrw : (∑' k : Gam, ∫⁻ t, G k t ∂μ)
        = ∑' k : Gam, ENNReal.ofReal (∫ t in (0:ℝ)..T, F k t) := tsum_congr hlint
    rw [hrw, ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => intervalIntegral.integral_nonneg hT (fun t _ => hnn k t)) hsum]
    exact ENNReal.ofReal_ne_top
  have htot : (∫⁻ t, (∑' k : Gam, G k t) ∂μ) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum hmeas]
    exact hfin
  have hae : ∀ᵐ t ∂μ, (∑' k : Gam, G k t) < ⊤ := by
    refine MeasureTheory.ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htot
  filter_upwards [hae] with t htlt
  have hne : (∑' k : Gam, ((F k t).toNNReal : ℝ≥0∞)) ≠ ⊤ := by
    have hcast : ∀ k : Gam, ((F k t).toNNReal : ℝ≥0∞) = G k t := fun k => rfl
    rw [tsum_congr hcast]
    exact ne_of_lt htlt
  have hnn2 : Summable fun k : Gam => (F k t).toNNReal :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 hne
  have hcoe : Summable fun k : Gam => (((F k t).toNNReal : ℝ)) := NNReal.summable_coe.2 hnn2
  have heq : (fun k : Gam => (((F k t).toNNReal : ℝ))) = fun k : Gam => F k t := by
    funext k
    exact Real.coe_toNNReal _ (hnn k t)
  rwa [heq] at hcoe

/-- **Pointwise-in-time square summability of the fractional multiplier.**  For almost every
`t ∈ (0,T]`, the family `k ↦ λ_k u_k(t)` is square summable, so `(-Δ)^α u(t)` has an actual
`ℓ²` coefficient family.  This does **not** say `λ_k u_k(t)` is summable (it need not be), and
it is not inferred from `u(t) ∈ A¹`. -/
theorem ae_summable_fracSymbol_sq (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      Summable fun k : Gam =>
        ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
  set F : Gam → ℝ → ℝ := fun k t =>
    ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 with hF
  have hcont : ∀ k, Continuous (F k) := fun k =>
    (((continuous_const.mul (continuous_coeff_curveState hT _ k))).norm).pow 2
  have hnn : ∀ k t, 0 ≤ F k t := fun k t => by positivity
  have hrw : ∀ k : Gam, (∫ t in (0:ℝ)..T, F k t)
      = (fracSymbol α k) ^ 2
        * ∫ t in (0:ℝ)..T, ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
    intro k
    have hpt : ∀ t : ℝ, F k t
        = (fracSymbol α k) ^ 2 * ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
      intro t
      rw [hF]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have hc := intervalIntegral.integral_const_mul (μ := (volume : Measure ℝ)) (a := (0:ℝ))
      (b := T) ((fracSymbol α k) ^ 2)
      (fun t : ℝ => ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2)
    calc (∫ t in (0:ℝ)..T, F k t)
        = ∫ t in (0:ℝ)..T,
            (fracSymbol α k) ^ 2 * ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
          exact intervalIntegral.integral_congr (fun t _ => hpt t)
      _ = _ := hc
  have hsum : Summable fun k : Gam => ∫ t in (0:ℝ)..T, F k t := by
    have := summable_integral_fracSymbol_sq hα hT g
    exact (funext hrw ▸ this)
  exact ae_summable_of_summable_integral hT hcont hnn hsum

end LiWang.Formalization
