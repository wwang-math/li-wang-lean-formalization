/-
# Smooth `ℤ²`-periodic functions on the plane and their Fourier coefficients

This module supplies the analytic input that was missing in v4.0: **smoothness discharges
absolute summability**.  Concretely, for a `C^∞` function `G : ℝ² → ℂ` which is `1`-periodic in
each variable we

* define the honest Fourier coefficient `pcoeff G k` as an iterated integral of `G` against
  `e^{-2πi k·y}` over the fundamental square `[0,1]²`;
* prove the decay estimate `|pcoeff G k| ≤ C · b(k₀) · b(k₁)` with `b(n) = (2π|n|)^{-2}` for
  `n ≠ 0`, by **two genuine integrations by parts in each variable** (the boundary terms cancel
  by periodicity), together with a Fubini exchange to reach the first variable;
* deduce `Summable (fun k => ‖pcoeff G k‖)`, i.e. membership of the coefficient family in the
  Wiener algebra, and build `wienerOfSmooth G h : Wiener`;
* prove **Fourier inversion**: the periodic lift of `wienerOfSmooth G h` is `G` itself.  The
  proof is two applications of Mathlib's one-dimensional inversion theorem
  `has_pointwise_sum_fourier_series_of_summable` joined by a `tsum` Fubini.

Nothing here is assumed: the only hypotheses are smoothness and periodicity of `G`.

Part of `LiWangFormalizationSmoothObservationPacket` v5.0.
-/
import LiWangFormalization.Coefficients
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.Formalization

/-! ## 1. The one-dimensional character `χ_n(y) = e^{2πi n y}` -/

/-- The one-dimensional Fourier character on the line. -/
noncomputable def chi (n : ℤ) (y : ℝ) : ℂ := Complex.exp (twoPiI * (n : ℂ) * (y : ℂ))

theorem chi_eq_fourier (n : ℤ) (y : ℝ) : chi n y = fourier n ((y : ℝ) : Circ) := by
  rw [fourier_coe_apply, chi]
  congr 1
  simp only [twoPiI]
  push_cast
  ring

@[simp] theorem norm_chi (n : ℤ) (y : ℝ) : ‖chi n y‖ = 1 := by
  rw [chi_eq_fourier]; exact norm_fourier_apply n _

@[simp] theorem chi_zero_arg (n : ℤ) : chi n 0 = 1 := by
  simp [chi]

@[simp] theorem chi_one_arg (n : ℤ) : chi n 1 = 1 := by
  have h : twoPiI * (n : ℂ) * ((1 : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [twoPiI]; push_cast; ring
  rw [chi, h, Complex.exp_int_mul_two_pi_mul_I]

theorem continuous_chi (n : ℤ) : Continuous (chi n) := by
  unfold chi
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal).const_mul _)

theorem hasDerivAt_chi (n : ℤ) (y : ℝ) :
    HasDerivAt (chi n) (twoPiI * (n : ℂ) * chi n y) y := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => twoPiI * (n : ℂ) * (t : ℂ)) (twoPiI * (n : ℂ)) y := by
    simpa using h0.const_mul (twoPiI * (n : ℂ))
  have h2 := h1.cexp
  have e : (fun t : ℝ => Complex.exp (twoPiI * (n : ℂ) * (t : ℂ))) = chi n := rfl
  rw [e] at h2
  have e2 : Complex.exp (twoPiI * (n : ℂ) * (y : ℂ)) * (twoPiI * (n : ℂ))
      = twoPiI * (n : ℂ) * chi n y := by rw [chi]; ring
  rwa [e2] at h2

theorem chi_mul_chi (k : Gam) (y : Fin 2 → ℝ) :
    chi (k 0) (y 0) * chi (k 1) (y 1) = planeMode k y := by
  rw [chi, chi, ← Complex.exp_add, planeMode]
  congr 1
  simp only [dotc, Fin.sum_univ_two]
  ring

/-! ## 2. The one-dimensional Fourier coefficient over the fundamental period -/

/-- The `n`-th Fourier coefficient of `φ : ℝ → ℂ` computed on the period `[0,1]`. -/
noncomputable def percoeff (φ : ℝ → ℂ) (n : ℤ) : ℂ := ∫ y in (0:ℝ)..1, φ y * chi (-n) y

theorem percoeff_const_mul (c : ℂ) (φ : ℝ → ℂ) (n : ℤ) :
    percoeff (fun y => c * φ y) n = c * percoeff φ n := by
  have e : (fun y : ℝ => (c * φ y) * chi (-n) y) = fun y : ℝ => c * (φ y * chi (-n) y) := by
    funext y; ring
  rw [percoeff, percoeff, e]
  exact intervalIntegral.integral_const_mul (μ := (volume : Measure ℝ)) (a := 0) (b := 1)
    c (fun y => φ y * chi (-n) y)

theorem percoeff_congr {φ ψ : ℝ → ℂ} (h : ∀ y, φ y = ψ y) (n : ℤ) :
    percoeff φ n = percoeff ψ n := by
  rw [show φ = ψ from funext h]

/-- The elementary bound `|percoeff φ n| ≤ C` from a bound on the period. -/
theorem norm_percoeff_le {φ : ℝ → ℂ} {C : ℝ}
    (hC : ∀ y ∈ Set.uIoc (0:ℝ) 1, ‖φ y‖ ≤ C) (n : ℤ) : ‖percoeff φ n‖ ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := C) (f := fun y => φ y * chi (-n) y)
    (fun x hx => by rw [norm_mul, norm_chi, mul_one]; exact hC x hx)
  simpa [percoeff] using h

/-- Periodicity is inherited by the derivative. -/
theorem periodic_of_hasDerivAt {φ φ' : ℝ → ℂ} (hd : ∀ y, HasDerivAt φ (φ' y) y)
    (hper : ∀ y, φ (y + 1) = φ y) (y : ℝ) : φ' (y + 1) = φ' y := by
  have h2 : HasDerivAt (fun t : ℝ => φ (t + 1)) (φ' (y + 1)) y := (hd (y + 1)).comp_add_const y 1
  have e : (fun t : ℝ => φ (t + 1)) = φ := funext hper
  rw [e] at h2
  exact h2.unique (hd y)

/-- **Integration by parts on the period.**  The boundary terms cancel by periodicity, so the
Fourier coefficient of the derivative is `2πin` times that of the function. -/
theorem percoeff_deriv {φ φ' : ℝ → ℂ} (hd : ∀ y, HasDerivAt φ (φ' y) y)
    (hc' : Continuous φ') (hper : ∀ y, φ (y + 1) = φ y) (n : ℤ) :
    percoeff φ' n = twoPiI * (n : ℂ) * percoeff φ n := by
  have hcφ : Continuous φ := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hA : Continuous fun y : ℝ => φ' y * chi (-n) y := hc'.mul (continuous_chi (-n))
  have hB : Continuous fun y : ℝ => φ y * (twoPiI * ((-n : ℤ) : ℂ) * chi (-n) y) :=
    hcφ.mul (continuous_const.mul (continuous_chi (-n)))
  have hIA : IntervalIntegrable (fun y : ℝ => φ' y * chi (-n) y) volume 0 1 :=
    hA.intervalIntegrable 0 1
  have hIB : IntervalIntegrable
      (fun y : ℝ => φ y * (twoPiI * ((-n : ℤ) : ℂ) * chi (-n) y)) volume 0 1 :=
    hB.intervalIntegrable 0 1
  have hdψ : ∀ y ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => φ t * chi (-n) t)
        (φ' y * chi (-n) y + φ y * (twoPiI * ((-n : ℤ) : ℂ) * chi (-n) y)) y :=
    fun y _ => (hd y).mul (hasDerivAt_chi (-n) y)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hdψ (hIA.add hIB)
  have hbdry : φ 1 * chi (-n) 1 - φ 0 * chi (-n) 0 = 0 := by
    have h1 : φ 1 = φ 0 := by have := hper 0; rwa [zero_add] at this
    rw [chi_one_arg, chi_zero_arg, h1, sub_self]
  rw [hbdry] at key
  have hB' : (∫ y in (0:ℝ)..1, φ y * (twoPiI * ((-n : ℤ) : ℂ) * chi (-n) y))
      = (twoPiI * ((-n : ℤ) : ℂ)) * percoeff φ n := by
    have e : (fun y : ℝ => φ y * (twoPiI * ((-n : ℤ) : ℂ) * chi (-n) y))
        = fun y : ℝ => (twoPiI * ((-n : ℤ) : ℂ)) * (φ y * chi (-n) y) := by
      funext y; ring
    rw [e, percoeff]
    exact intervalIntegral.integral_const_mul (μ := (volume : Measure ℝ)) (a := 0) (b := 1)
      (twoPiI * ((-n : ℤ) : ℂ)) (fun y => φ y * chi (-n) y)
  rw [intervalIntegral.integral_add hIA hIB, hB'] at key
  have hn : ((-n : ℤ) : ℂ) = -(n : ℂ) := by push_cast; ring
  rw [hn] at key
  rw [percoeff]
  linear_combination key

/-- Two integrations by parts. -/
theorem percoeff_deriv_two {φ φ' φ'' : ℝ → ℂ} (hd : ∀ y, HasDerivAt φ (φ' y) y)
    (hd' : ∀ y, HasDerivAt φ' (φ'' y) y) (hc'' : Continuous φ'')
    (hper : ∀ y, φ (y + 1) = φ y) (n : ℤ) :
    percoeff φ'' n = (twoPiI * (n : ℂ)) ^ 2 * percoeff φ n := by
  have hc' : Continuous φ' := continuous_iff_continuousAt.2 fun y => (hd' y).continuousAt
  have hper' : ∀ y, φ' (y + 1) = φ' y := periodic_of_hasDerivAt hd hper
  rw [percoeff_deriv hd' hc'' hper' n, percoeff_deriv hd hc' hper n]
  ring

/-- The decay of the Fourier coefficient of a periodic twice-differentiable function. -/
theorem norm_percoeff_le_of_deriv_two {φ φ' φ'' : ℝ → ℂ} (hd : ∀ y, HasDerivAt φ (φ' y) y)
    (hd' : ∀ y, HasDerivAt φ' (φ'' y) y) (hc'' : Continuous φ'')
    (hper : ∀ y, φ (y + 1) = φ y) {C : ℝ} (hC : ∀ y ∈ Set.uIoc (0:ℝ) 1, ‖φ'' y‖ ≤ C)
    {n : ℤ} (hn : n ≠ 0) :
    ‖percoeff φ n‖ ≤ C / (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
  have hkey := percoeff_deriv_two hd hd' hc'' hper n
  have hnorm : ‖(twoPiI * (n : ℂ)) ^ 2‖ = (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
    rw [norm_pow, norm_mul, norm_twoPiI, Complex.norm_intCast]
  have hnpos : (0:ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hpos : (0:ℝ) < (2 * Real.pi * |(n : ℝ)|) ^ 2 := pow_pos (mul_pos hpi hnpos) 2
  have hkn := congrArg norm hkey
  rw [norm_mul, hnorm] at hkn
  rw [le_div_iff₀ hpos, mul_comm, ← hkn]
  exact norm_percoeff_le hC n



/-! ## 3. Smooth `ℤ²`-periodic functions of two real variables -/

/-- The partial derivative of `G : ℝ² → ℂ` in the first variable. -/
noncomputable def pd0 (G : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => fderiv ℝ G p (1, 0)

/-- The partial derivative of `G : ℝ² → ℂ` in the second variable. -/
noncomputable def pd1 (G : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => fderiv ℝ G p (0, 1)

/-- `G : ℝ² → ℂ` is `C^∞` and `1`-periodic in each variable; equivalently, it is the
**Euclidean smooth periodic lift** of a smooth function of the normalized two-torus. -/
structure IsSmoothPeriodic (G : ℝ × ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ G
  per0 : ∀ p : ℝ × ℝ, G (p.1 + 1, p.2) = G p
  per1 : ∀ p : ℝ × ℝ, G (p.1, p.2 + 1) = G p

namespace IsSmoothPeriodic

theorem continuous {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) : Continuous G := h.smooth.continuous

end IsSmoothPeriodic

theorem contDiff_pd0 {G : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (pd0 G) :=
  (h.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_pd1 {G : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (pd1 G) :=
  (h.fderiv_right (by simp)).clm_apply contDiff_const

theorem hasDerivAt_pd0 {G : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ G) (y0 y1 : ℝ) :
    HasDerivAt (fun t : ℝ => G (t, y1)) (pd0 G (y0, y1)) y0 := by
  have hG : HasFDerivAt G (fderiv ℝ G (y0, y1)) (y0, y1) :=
    (h.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hin : HasDerivAt (fun t : ℝ => (t, y1)) ((1 : ℝ), (0 : ℝ)) y0 :=
    (hasDerivAt_id y0).prodMk (hasDerivAt_const y0 y1)
  exact hG.comp_hasDerivAt y0 hin

theorem hasDerivAt_pd1 {G : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ G) (y0 y1 : ℝ) :
    HasDerivAt (fun t : ℝ => G (y0, t)) (pd1 G (y0, y1)) y1 := by
  have hG : HasFDerivAt G (fderiv ℝ G (y0, y1)) (y0, y1) :=
    (h.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hin : HasDerivAt (fun t : ℝ => (y0, t)) ((0 : ℝ), (1 : ℝ)) y1 :=
    (hasDerivAt_const y1 y0).prodMk (hasDerivAt_id y1)
  exact hG.comp_hasDerivAt y1 hin

namespace IsSmoothPeriodic

/-- The first partial derivative of a smooth doubly periodic function is again one. -/
theorem pd0' {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) : IsSmoothPeriodic (pd0 G) := by
  refine ⟨contDiff_pd0 h.smooth, ?_, ?_⟩
  · intro p
    exact periodic_of_hasDerivAt (fun t => hasDerivAt_pd0 h.smooth t p.2)
      (fun t => h.per0 (t, p.2)) p.1
  · intro p
    have e : (fun s : ℝ => G (s, p.2 + 1)) = fun s : ℝ => G (s, p.2) :=
      funext fun s => h.per1 (s, p.2)
    have h1 : HasDerivAt (fun s : ℝ => G (s, p.2 + 1)) (pd0 G (p.1, p.2 + 1)) p.1 :=
      hasDerivAt_pd0 h.smooth p.1 (p.2 + 1)
    rw [e] at h1
    exact h1.unique (hasDerivAt_pd0 h.smooth p.1 p.2)

/-- The second partial derivative of a smooth doubly periodic function is again one. -/
theorem pd1' {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) : IsSmoothPeriodic (pd1 G) := by
  refine ⟨contDiff_pd1 h.smooth, ?_, ?_⟩
  · intro p
    have e : (fun s : ℝ => G (p.1 + 1, s)) = fun s : ℝ => G (p.1, s) :=
      funext fun s => h.per0 (p.1, s)
    have h1 : HasDerivAt (fun s : ℝ => G (p.1 + 1, s)) (pd1 G (p.1 + 1, p.2)) p.2 :=
      hasDerivAt_pd1 h.smooth (p.1 + 1) p.2
    rw [e] at h1
    exact h1.unique (hasDerivAt_pd1 h.smooth p.1 p.2)
  · intro p
    exact periodic_of_hasDerivAt (fun t => hasDerivAt_pd1 h.smooth p.1 t)
      (fun t => h.per1 (p.1, t)) p.2

end IsSmoothPeriodic

/-! ## 4. The two-dimensional Fourier coefficient -/

/-- The `k`-th Fourier coefficient of `G : ℝ² → ℂ` over the fundamental square, computed as the
iterated integral in the order `dy₁ dy₀`. -/
noncomputable def pcoeff (G : ℝ × ℝ → ℂ) (k : Gam) : ℂ :=
  percoeff (fun y0 => percoeff (fun y1 => G (y0, y1)) (k 1)) (k 0)

/-- The same coefficient computed in the order `dy₀ dy₁`. -/
noncomputable def pcoeffSwap (G : ℝ × ℝ → ℂ) (k : Gam) : ℂ :=
  percoeff (fun y1 => percoeff (fun y0 => G (y0, y1)) (k 0)) (k 1)

theorem uIoc_zero_one : Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 := Set.uIoc_of_le (by norm_num)

/-- A continuous function is bounded on the fundamental square. -/
theorem exists_box_bound {G : ℝ × ℝ → ℂ} (hG : Continuous G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1, ‖G (y0, y1)‖ ≤ C := by
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1).Nonempty :=
    ⟨(0, 0), Set.mem_prod.2 ⟨by norm_num, by norm_num⟩⟩
  obtain ⟨p, _, hmax⟩ := hK.exists_isMaxOn hne (Continuous.continuousOn hG.norm)
  refine ⟨max 0 ‖G p‖, le_max_left _ _, fun y0 hy0 y1 hy1 => ?_⟩
  refine le_trans ?_ (le_max_right 0 ‖G p‖)
  rw [uIoc_zero_one] at hy0 hy1
  exact isMaxOn_iff.1 hmax (y0, y1)
    (Set.mem_prod.2 ⟨Set.Ioc_subset_Icc_self hy0, Set.Ioc_subset_Icc_self hy1⟩)

theorem norm_pcoeff_le {G : ℝ × ℝ → ℂ} {C : ℝ}
    (hb : ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1, ‖G (y0, y1)‖ ≤ C) (k : Gam) :
    ‖pcoeff G k‖ ≤ C :=
  norm_percoeff_le (fun y0 hy0 => norm_percoeff_le (fun y1 hy1 => hb y0 hy0 y1 hy1) (k 1)) (k 0)

theorem norm_pcoeffSwap_le {G : ℝ × ℝ → ℂ} {C : ℝ}
    (hb : ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1, ‖G (y0, y1)‖ ≤ C) (k : Gam) :
    ‖pcoeffSwap G k‖ ≤ C :=
  norm_percoeff_le (fun y1 hy1 => norm_percoeff_le (fun y0 hy0 => hb y0 hy0 y1 hy1) (k 0)) (k 1)

/-- **Fubini for the fundamental square**: the two iterated orders agree. -/
theorem pcoeff_eq_swap {G : ℝ × ℝ → ℂ} (hG : Continuous G) (k : Gam) :
    pcoeff G k = pcoeffSwap G k := by
  have hc0 : Continuous fun p : ℝ × ℝ => chi (-(k 0)) p.1 :=
    (continuous_chi _).comp continuous_fst
  have hc1 : Continuous fun p : ℝ × ℝ => chi (-(k 1)) p.2 :=
    (continuous_chi _).comp continuous_snd
  have hFc : Continuous fun p : ℝ × ℝ => G p * chi (-(k 1)) p.2 * chi (-(k 0)) p.1 :=
    (hG.mul hc1).mul hc0
  have hInt : Integrable
      (Function.uncurry fun y0 y1 => G (y0, y1) * chi (-(k 1)) y1 * chi (-(k 0)) y0)
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact IntegrableOn.mono_set
      (hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hswap := MeasureTheory.integral_integral_swap hInt
  have hle : (0:ℝ) ≤ 1 := by norm_num
  have hL : pcoeff G k
      = ∫ y0 in Set.Ioc (0:ℝ) 1, ∫ y1 in Set.Ioc (0:ℝ) 1,
          G (y0, y1) * chi (-(k 1)) y1 * chi (-(k 0)) y0 := by
    rw [pcoeff, percoeff, ← intervalIntegral.integral_of_le hle]
    refine intervalIntegral.integral_congr (fun y0 _ => ?_)
    rw [percoeff, ← intervalIntegral.integral_of_le hle]
    exact (intervalIntegral.integral_mul_const (μ := (volume : Measure ℝ)) (a := 0) (b := 1)
      (chi (-(k 0)) y0) (fun y1 => G (y0, y1) * chi (-(k 1)) y1)).symm
  have hR : pcoeffSwap G k
      = ∫ y1 in Set.Ioc (0:ℝ) 1, ∫ y0 in Set.Ioc (0:ℝ) 1,
          G (y0, y1) * chi (-(k 1)) y1 * chi (-(k 0)) y0 := by
    rw [pcoeffSwap, percoeff, ← intervalIntegral.integral_of_le hle]
    refine intervalIntegral.integral_congr (fun y1 _ => ?_)
    rw [← intervalIntegral.integral_of_le hle]
    have hm := intervalIntegral.integral_mul_const (μ := (volume : Measure ℝ)) (a := (0:ℝ))
      (b := 1) (chi (-(k 1)) y1) (fun y0 => G (y0, y1) * chi (-(k 0)) y0)
    rw [percoeff]
    refine Eq.trans hm.symm ?_
    exact intervalIntegral.integral_congr (fun y0 _ => by ring)
  rw [hL, hR, hswap]

/-! ## 5. Two integrations by parts in each variable -/

theorem continuous_partial_pd1 {G : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ G) (y0 : ℝ) :
    Continuous fun t : ℝ => G (y0, t) :=
  h.continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_partial_pd0 {G : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ G) (y1 : ℝ) :
    Continuous fun t : ℝ => G (t, y1) :=
  h.continuous.comp (continuous_id.prodMk continuous_const)

/-- Two integrations by parts in the **second** variable. -/
theorem pcoeff_pd1_two {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    pcoeff (pd1 (pd1 G)) k = (twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2 * pcoeff G k := by
  have hinner : ∀ y0 : ℝ, percoeff (fun y1 => pd1 (pd1 G) (y0, y1)) (k 1)
      = (twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2 * percoeff (fun y1 => G (y0, y1)) (k 1) := by
    intro y0
    exact percoeff_deriv_two (fun t => hasDerivAt_pd1 h.smooth y0 t)
      (fun t => hasDerivAt_pd1 (contDiff_pd1 h.smooth) y0 t)
      (continuous_partial_pd1 (contDiff_pd1 (contDiff_pd1 h.smooth)) y0)
      (fun t => h.per1 (y0, t)) (k 1)
  rw [pcoeff, pcoeff, percoeff_congr hinner (k 0), percoeff_const_mul]

/-- Two integrations by parts in the **first** variable, in the swapped order. -/
theorem pcoeffSwap_pd0_two {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    pcoeffSwap (pd0 (pd0 G)) k = (twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2 * pcoeffSwap G k := by
  have hinner : ∀ y1 : ℝ, percoeff (fun y0 => pd0 (pd0 G) (y0, y1)) (k 0)
      = (twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2 * percoeff (fun y0 => G (y0, y1)) (k 0) := by
    intro y1
    exact percoeff_deriv_two (fun t => hasDerivAt_pd0 h.smooth t y1)
      (fun t => hasDerivAt_pd0 (contDiff_pd0 h.smooth) t y1)
      (continuous_partial_pd0 (contDiff_pd0 (contDiff_pd0 h.smooth)) y1)
      (fun t => h.per0 (t, y1)) (k 0)
  rw [pcoeffSwap, pcoeffSwap, percoeff_congr hinner (k 1), percoeff_const_mul]

/-- Two integrations by parts in the **first** variable. -/
theorem pcoeff_pd0_two {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    pcoeff (pd0 (pd0 G)) k = (twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2 * pcoeff G k := by
  rw [pcoeff_eq_swap (contDiff_pd0 (contDiff_pd0 h.smooth)).continuous,
    pcoeff_eq_swap h.continuous, pcoeffSwap_pd0_two h]

/-! ## 6. The decay estimate and summability -/

/-- The weight `b(n) = (2π|n|)^{-2}` for `n ≠ 0`, and `b(0) = 1`. -/
noncomputable def decayWeight (n : ℤ) : ℝ :=
  if n = 0 then 1 else 1 / (2 * Real.pi * |(n : ℝ)|) ^ 2

theorem decayWeight_zero : decayWeight 0 = 1 := by simp [decayWeight]

theorem decayWeight_of_ne {n : ℤ} (hn : n ≠ 0) :
    decayWeight n = 1 / (2 * Real.pi * |(n : ℝ)|) ^ 2 := by rw [decayWeight, if_neg hn]

theorem decayWeight_pos (n : ℤ) : 0 < decayWeight n := by
  by_cases hn : n = 0
  · rw [decayWeight, if_pos hn]; norm_num
  · rw [decayWeight_of_ne hn]
    have hnpos : (0:ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hpi : (0:ℝ) < 2 * Real.pi := by positivity
    exact one_div_pos.2 (pow_pos (mul_pos hpi hnpos) 2)

theorem summable_decayWeight : Summable decayWeight := by
  have hmaj : Summable fun n : ℤ => (if n = 0 then (1:ℝ) else 0) + 1 / ((n : ℝ) ^ 2) := by
    refine Summable.add ?_ (Real.summable_one_div_int_pow.2 (by norm_num))
    exact summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) (fun b hb => by
      rw [if_neg (by simpa using hb)])
  refine Summable.of_nonneg_of_le (fun n => (decayWeight_pos n).le) (fun n => ?_) hmaj
  by_cases hn : n = 0
  · subst hn; simp [decayWeight]
  · rw [decayWeight_of_ne hn, if_neg hn, zero_add]
    have hnpos : (0:ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hpi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
    have hsq : ((n : ℝ)) ^ 2 ≤ (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
      have h1 : |(n:ℝ)| ≤ 2 * Real.pi * |(n:ℝ)| := by nlinarith
      have h2 : ((n:ℝ)) ^ 2 = |(n:ℝ)| ^ 2 := (sq_abs _).symm
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact one_div_le_one_div_of_le (by positivity) hsq

/-- A norm bound transferred through an exact multiplicative factor. -/
theorem norm_le_div_of_factor {z u w : ℂ} {r C : ℝ} (hr : 0 < r) (hru : ‖u‖ = r)
    (hw : w = u * z) (hC : ‖w‖ ≤ C) : ‖z‖ ≤ C / r := by
  rw [le_div_iff₀ hr]
  calc ‖z‖ * r = ‖u * z‖ := by rw [norm_mul, hru]; ring
    _ = ‖w‖ := by rw [hw]
    _ ≤ C := hC

theorem norm_twoPiI_pow_two (n : ℤ) :
    ‖(twoPiI * ((n : ℤ) : ℂ)) ^ 2‖ = (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
  rw [norm_pow, norm_mul, norm_twoPiI, Complex.norm_intCast]

theorem twoPiI_pow_two_pos {n : ℤ} (hn : n ≠ 0) : (0:ℝ) < (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
  have hnpos : (0:ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  exact pow_pos (mul_pos hpi hnpos) 2

/-- **The decay estimate.**  For a smooth doubly periodic `G` there is a constant `C` with
`|pcoeff G k| ≤ C · b(k₀) · b(k₁)`; the proof uses two genuine integrations by parts in each
variable, the boundary terms cancelling by periodicity. -/
theorem exists_pcoeff_decay {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Gam,
      ‖pcoeff G k‖ ≤ C * (decayWeight (k 0) * decayWeight (k 1)) := by
  obtain ⟨C0, hC0, hb0⟩ := exists_box_bound h.continuous
  obtain ⟨C1, hC1, hb1⟩ := exists_box_bound (contDiff_pd0 (contDiff_pd0 h.smooth)).continuous
  obtain ⟨C2, hC2, hb2⟩ := exists_box_bound (contDiff_pd1 (contDiff_pd1 h.smooth)).continuous
  obtain ⟨C3, hC3, hb3⟩ := exists_box_bound
    (contDiff_pd0 (contDiff_pd0 (contDiff_pd1 (contDiff_pd1 h.smooth)))).continuous
  refine ⟨max (max C0 C1) (max C2 C3), le_trans hC0 (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun k => ?_⟩
  set C := max (max C0 C1) (max C2 C3) with hCdef
  have hCC0 : C0 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC1 : C1 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCC2 : C2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCC3 : C3 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases h0 : k 0 = 0 <;> by_cases h1 : k 1 = 0
  · rw [h0, h1, decayWeight_zero, mul_one, mul_one]
    exact le_trans (norm_pcoeff_le hb0 k) hCC0
  · rw [h0, decayWeight_zero, one_mul, decayWeight_of_ne h1]
    have hr := twoPiI_pow_two_pos h1
    have := norm_le_div_of_factor hr (norm_twoPiI_pow_two (k 1)) (pcoeff_pd1_two h k)
      (norm_pcoeff_le hb2 k)
    calc ‖pcoeff G k‖ ≤ C2 / (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2 := this
      _ ≤ C * (1 / (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hCC2 (by positivity)
  · rw [h1, decayWeight_zero, mul_one, decayWeight_of_ne h0]
    have hr := twoPiI_pow_two_pos h0
    have := norm_le_div_of_factor hr (norm_twoPiI_pow_two (k 0)) (pcoeff_pd0_two h k)
      (norm_pcoeff_le hb1 k)
    calc ‖pcoeff G k‖ ≤ C1 / (2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2 := this
      _ ≤ C * (1 / (2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hCC1 (by positivity)
  · rw [decayWeight_of_ne h0, decayWeight_of_ne h1]
    have hfac : pcoeff (pd0 (pd0 (pd1 (pd1 G)))) k
        = ((twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2 * (twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2) * pcoeff G k := by
      rw [pcoeff_pd0_two (h.pd1'.pd1') k, pcoeff_pd1_two h k]
      ring
    have hru : ‖(twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2 * (twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2‖
        = (2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2 * (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2 := by
      rw [norm_mul, norm_twoPiI_pow_two, norm_twoPiI_pow_two]
    have hr : (0:ℝ) < (2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2
        * (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2 :=
      mul_pos (twoPiI_pow_two_pos h0) (twoPiI_pow_two_pos h1)
    have hmain := norm_le_div_of_factor hr hru hfac (norm_pcoeff_le hb3 k)
    calc ‖pcoeff G k‖
        ≤ C3 / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2
            * (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) := hmain
      _ = C3 * (1 / (2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2
            * (1 / (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2)) := by
          field_simp
      _ ≤ C * (1 / (2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2
            * (1 / (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2)) :=
          mul_le_mul_of_nonneg_right hCC3 (by positivity)


/-! ## 7. Membership in the Wiener algebra -/

theorem gam_mk_zero (m n : ℤ) : (![m, n] : Gam) 0 = m := rfl
theorem gam_mk_one (m n : ℤ) : (![m, n] : Gam) 1 = n := rfl

theorem summable_gam_of_prod {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n) :
    Summable (fun k : Gam => f (k 0) * g (k 1)) := by
  have hp : Summable fun p : ℤ × ℤ => f p.1 * g p.2 := hf.mul_of_nonneg hg hf0 hg0
  exact (Equiv.summable_iff (finTwoArrowEquiv ℤ)
    (f := fun p : ℤ × ℤ => f p.1 * g p.2)).2 hp

/-- **Smoothness discharges summability.**  The Fourier coefficients of a smooth doubly
periodic function are absolutely summable, i.e. they lie in the Wiener algebra. -/
theorem summable_norm_pcoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    Summable fun k : Gam => ‖pcoeff G k‖ := by
  obtain ⟨C, hC, hbd⟩ := exists_pcoeff_decay h
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd ?_
  have hs := summable_gam_of_prod (f := fun n => C * decayWeight n) (g := decayWeight)
    (summable_decayWeight.mul_left C) summable_decayWeight
    (fun n => mul_nonneg hC (decayWeight_pos n).le) (fun n => (decayWeight_pos n).le)
  exact hs.congr (fun k => by ring)

/-- The Wiener-algebra element attached to a smooth doubly periodic function. -/
noncomputable def wienerOfSmooth (G : ℝ × ℝ → ℂ) (h : IsSmoothPeriodic G) : Wiener :=
  wmk (pcoeff G) (summable_norm_pcoeff h)

@[simp] theorem wienerOfSmooth_coeff (G : ℝ × ℝ → ℂ) (h : IsSmoothPeriodic G) (k : Gam) :
    (wienerOfSmooth G h) k = pcoeff G k := rfl

/-! ## 8. Integer periodicity and global bounds -/

theorem periodic_int_add {φ : ℝ → ℂ} (hper : ∀ y, φ (y + 1) = φ y) (y : ℝ) (n : ℤ) :
    φ (y + (n : ℝ)) = φ y := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have e : y + (((i : ℤ) + 1 : ℤ) : ℝ) = (y + ((i : ℤ) : ℝ)) + 1 := by push_cast; ring
      rw [e, hper, ih]
  | pred i ih =>
      have e : (y + ((-(i : ℤ) - 1 : ℤ) : ℝ)) + 1 = y + ((-(i : ℤ) : ℤ) : ℝ) := by
        push_cast; ring
      have := hper (y + ((-(i : ℤ) - 1 : ℤ) : ℝ))
      rw [e] at this
      rw [← this, ih]

theorem exists_int_shift (t : ℝ) : ∃ n : ℤ, t - (n : ℝ) ∈ Set.Ioc (0:ℝ) 1 := by
  refine ⟨⌈t⌉ - 1, ?_, ?_⟩
  · have h := Int.ceil_lt_add_one t
    push_cast
    linarith
  · have h := Int.le_ceil t
    push_cast
    linarith

theorem IsSmoothPeriodic.per0_int {F : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic F) (p : ℝ × ℝ) (n : ℤ) :
    F (p.1 + (n : ℝ), p.2) = F p :=
  periodic_int_add (φ := fun t : ℝ => F (t, p.2)) (fun t => h.per0 (t, p.2)) p.1 n

theorem IsSmoothPeriodic.per1_int {F : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic F) (p : ℝ × ℝ) (n : ℤ) :
    F (p.1, p.2 + (n : ℝ)) = F p :=
  periodic_int_add (φ := fun t : ℝ => F (p.1, t)) (fun t => h.per1 (p.1, t)) p.2 n

/-- A smooth doubly periodic function is globally bounded. -/
theorem exists_global_bound {F : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖F p‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_box_bound h.continuous
  refine ⟨C, hC, fun p => ?_⟩
  obtain ⟨n0, hn0⟩ := exists_int_shift p.1
  obtain ⟨n1, hn1⟩ := exists_int_shift p.2
  have e1 : F (p.1 - (n0 : ℝ), p.2 - (n1 : ℝ)) = F (p.1 - (n0 : ℝ), p.2) := by
    have := h.per1_int (p.1 - (n0 : ℝ), p.2 - (n1 : ℝ)) n1
    simpa using this.symm
  have e2 : F (p.1 - (n0 : ℝ), p.2) = F p := by
    have := h.per0_int (p.1 - (n0 : ℝ), p.2) n0
    simpa using this.symm
  rw [← e2, ← e1]
  exact hb _ (by rw [uIoc_zero_one]; exact hn0) _ (by rw [uIoc_zero_one]; exact hn1)

/-! ## 9. One-dimensional Fourier inversion -/

theorem liftIoc_apply_of_periodic {φ : ℝ → ℂ} (hper : ∀ y, φ (y + 1) = φ y) (y : ℝ) :
    AddCircle.liftIoc (1:ℝ) 0 φ ((y : ℝ) : Circ) = φ y := by
  obtain ⟨n, hn⟩ := exists_int_shift y
  have hcoe : (((y - (n : ℝ)) : ℝ) : Circ) = ((y : ℝ) : Circ) := by
    have e : y - (n : ℝ) = y + (((-n : ℤ)) : ℝ) := by push_cast; ring
    rw [e]
    exact coe_add_intCast y (-n)
  rw [← hcoe, AddCircle.liftIoc_zero_coe_apply hn]
  have e : y - (n : ℝ) = y + (((-n : ℤ)) : ℝ) := by push_cast; ring
  rw [e, periodic_int_add hper y (-n)]

theorem fourierCoeff_liftIoc_eq_percoeff {φ : ℝ → ℂ} (hper : ∀ y, φ (y + 1) = φ y) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc (1:ℝ) 0 φ) n = percoeff φ n := by
  rw [fourierCoeff_eq_intervalIntegral _ n 0]
  simp only [zero_add, one_div, inv_one, one_smul]
  rw [percoeff]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [liftIoc_apply_of_periodic hper, smul_eq_mul, ← chi_eq_fourier]
  ring

/-- **One-dimensional Fourier inversion** for a continuous `1`-periodic function with
absolutely summable Fourier coefficients. -/
theorem tsum_percoeff_chi {φ : ℝ → ℂ} (hc : Continuous φ) (hper : ∀ y, φ (y + 1) = φ y)
    (hs : Summable fun n : ℤ => ‖percoeff φ n‖) (y : ℝ) :
    ∑' n : ℤ, percoeff φ n * chi n y = φ y := by
  have hcont : Continuous (AddCircle.liftIoc (1:ℝ) 0 φ) :=
    AddCircle.liftIoc_continuous (hper 0).symm hc.continuousOn
  let f : C(Circ, ℂ) := ⟨AddCircle.liftIoc (1:ℝ) 0 φ, hcont⟩
  have hcoeff : ∀ n : ℤ, fourierCoeff (⇑f) n = percoeff φ n :=
    fourierCoeff_liftIoc_eq_percoeff hper
  have hsum : Summable (fourierCoeff (⇑f)) := by
    refine Summable.of_norm ?_
    exact hs.congr (fun n => by rw [hcoeff n])
  have hpt := has_pointwise_sum_fourier_series_of_summable (f := f) hsum ((y : ℝ) : Circ)
  have hfy : f ((y : ℝ) : Circ) = φ y := liftIoc_apply_of_periodic hper y
  have e : (fun i : ℤ => fourierCoeff (⇑f) i • (fourier i) ((y : ℝ) : Circ))
      = fun n : ℤ => percoeff φ n * chi n y := by
    funext i
    rw [hcoeff i, smul_eq_mul, chi_eq_fourier]
  rw [e, hfy] at hpt
  exact hpt.tsum_eq


/-! ## 10. Two-dimensional Fourier inversion -/

/-- The partial Fourier coefficient in the first variable, as a function of the second. -/
noncomputable def partialCoeff (G : ℝ × ℝ → ℂ) (m : ℤ) (y1 : ℝ) : ℂ :=
  percoeff (fun y0 => G (y0, y1)) m

theorem continuous_partialCoeff {G : ℝ × ℝ → ℂ} (hG : Continuous G) (m : ℤ) :
    Continuous (partialCoeff G m) := by
  have hf : Continuous (Function.uncurry fun (y1 t : ℝ) => G (t, y1) * chi (-m) t) :=
    (hG.comp (continuous_snd.prodMk continuous_fst)).mul
      ((continuous_chi (-m)).comp continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (a₀ := (0:ℝ)) (μ := (volume : Measure ℝ)) hf
    (continuous_const : Continuous fun _ : ℝ => (1:ℝ))

theorem periodic_partialCoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (m : ℤ) (y1 : ℝ) :
    partialCoeff G m (y1 + 1) = partialCoeff G m y1 :=
  percoeff_congr (fun y0 => h.per1 (y0, y1)) m

theorem pcoeff_eq_percoeff_partialCoeff {G : ℝ × ℝ → ℂ} (hG : Continuous G) (m n : ℤ) :
    pcoeff G (![m, n]) = percoeff (partialCoeff G m) n := by
  rw [pcoeff_eq_swap hG, pcoeffSwap]
  rfl

theorem summable_pcoeff_section {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (m : ℤ) :
    Summable fun n : ℤ => ‖pcoeff G (![m, n])‖ :=
  ((Equiv.summable_iff (finTwoArrowEquiv ℤ).symm
    (f := fun k : Gam => ‖pcoeff G k‖)).2 (summable_norm_pcoeff h)).prod_factor m

theorem summable_norm_percoeff_partialCoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (m : ℤ) :
    Summable fun n : ℤ => ‖percoeff (partialCoeff G m) n‖ :=
  (summable_pcoeff_section h m).congr
    (fun n => by rw [pcoeff_eq_percoeff_partialCoeff h.continuous m n])

/-- The partial Fourier coefficients decay in the first index, uniformly in the second
variable: this is the one-dimensional decay estimate applied on each horizontal line. -/
theorem summable_norm_partialCoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (y1 : ℝ) :
    Summable fun m : ℤ => ‖partialCoeff G m y1‖ := by
  obtain ⟨C2, hC2, hb2⟩ := exists_global_bound (h.pd0'.pd0')
  obtain ⟨C0, hC0, hb0⟩ := exists_global_bound h
  have hmain : ∀ m : ℤ, ‖partialCoeff G m y1‖ ≤ (max C0 C2) * decayWeight m := by
    intro m
    by_cases hm : m = 0
    · rw [hm, decayWeight_zero, mul_one]
      exact le_trans (norm_percoeff_le (fun t _ => hb0 (t, y1)) 0) (le_max_left _ _)
    · rw [decayWeight_of_ne hm]
      have hd := norm_percoeff_le_of_deriv_two
        (φ := fun t : ℝ => G (t, y1)) (φ' := fun t : ℝ => pd0 G (t, y1))
        (φ'' := fun t : ℝ => pd0 (pd0 G) (t, y1))
        (fun t => hasDerivAt_pd0 h.smooth t y1)
        (fun t => hasDerivAt_pd0 (contDiff_pd0 h.smooth) t y1)
        (continuous_partial_pd0 (contDiff_pd0 (contDiff_pd0 h.smooth)) y1)
        (fun t => h.per0 (t, y1)) (C := C2) (fun t _ => hb2 (t, y1)) hm
      calc ‖partialCoeff G m y1‖ ≤ C2 / (2 * Real.pi * |(m : ℝ)|) ^ 2 := hd
        _ ≤ max C0 C2 * (1 / (2 * Real.pi * |(m : ℝ)|) ^ 2) := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _)
              (by positivity)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmain ?_
  exact summable_decayWeight.mul_left _

/-- **Fourier inversion.**  The periodic lift of the Wiener element built from the Fourier
coefficients of a smooth doubly periodic function is that function again. -/
theorem lift_wienerOfSmooth {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (y : Fin 2 → ℝ) :
    lift (wienerOfSmooth G h) y = G (y 0, y 1) := by
  have hsum : Summable fun k : Gam => ‖pcoeff G k‖ := summable_norm_pcoeff h
  have hFnorm : Summable fun p : ℤ × ℤ => ‖pcoeff G (![p.1, p.2])‖ :=
    (Equiv.summable_iff (finTwoArrowEquiv ℤ).symm
      (f := fun k : Gam => ‖pcoeff G k‖)).2 hsum
  have hF : Summable fun p : ℤ × ℤ =>
      pcoeff G (![p.1, p.2]) * (chi p.1 (y 0) * chi p.2 (y 1)) := by
    refine Summable.of_norm (hFnorm.congr (fun p => ?_))
    rw [norm_mul, norm_mul, norm_chi, norm_chi, mul_one, mul_one]
  have hFsec : ∀ m : ℤ, Summable fun n : ℤ =>
      pcoeff G (![m, n]) * (chi m (y 0) * chi n (y 1)) := fun m => hF.prod_factor m
  rw [lift_apply]
  have h1 : (∑' k : Gam, (wienerOfSmooth G h) k * planeMode k y)
      = ∑' p : ℤ × ℤ, pcoeff G (![p.1, p.2]) * (chi p.1 (y 0) * chi p.2 (y 1)) := by
    refine ((Equiv.tsum_eq (finTwoArrowEquiv ℤ).symm
      (fun k : Gam => (wienerOfSmooth G h) k * planeMode k y)).symm).trans ?_
    refine tsum_congr (fun p => ?_)
    rw [wienerOfSmooth_coeff, ← chi_mul_chi]
    rfl
  rw [h1, hF.tsum_prod' hFsec]
  have hinner : ∀ m : ℤ,
      (∑' n : ℤ, pcoeff G (![m, n]) * (chi m (y 0) * chi n (y 1)))
        = partialCoeff G m (y 1) * chi m (y 0) := by
    intro m
    have hrw : ∀ n : ℤ, pcoeff G (![m, n]) * (chi m (y 0) * chi n (y 1))
        = (percoeff (partialCoeff G m) n * chi n (y 1)) * chi m (y 0) := by
      intro n
      rw [pcoeff_eq_percoeff_partialCoeff h.continuous m n]
      ring
    rw [tsum_congr hrw, tsum_mul_right]
    congr 1
    exact tsum_percoeff_chi (continuous_partialCoeff h.continuous m)
      (periodic_partialCoeff h m) (summable_norm_percoeff_partialCoeff h m) (y 1)
  rw [tsum_congr hinner]
  exact tsum_percoeff_chi (continuous_partial_pd0 h.smooth (y 1))
    (fun t => h.per0 (t, y 1)) (summable_norm_partialCoeff h (y 1)) (y 0)


end LiWang.Formalization
