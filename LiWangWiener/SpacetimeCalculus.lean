/-
# Spatial partial derivatives of a jointly smooth space-time function

To realize an arbitrary `C_c^∞(W × (0,T))` datum as a `Curve0 T` source one needs the Fourier
coefficients of the spatial slices to decay **uniformly in time**.  That in turn needs the
spatial partial derivatives of a jointly smooth `Φ : ℝ × ℝ² → ℂ` to be jointly smooth, which is
what this module supplies.

* `spd0`, `spd1` — the spatial partials, taken as directional Fréchet derivatives of `Φ` itself;
* `contDiff_spd0/1` — they are again `C^∞`;
* `slice_spd0/1` — their time slices are the `pd0`/`pd1` of the time slices, so all the existing
  two-dimensional integration-by-parts machinery applies to them;
* `exists_uniform_box_bound` — a continuous `Φ` supported in a compact time interval is bounded
  on `ℝ × [0,1]²`, **uniformly in time**;
* `pcoeff_decay4_of_bounds` — the fourth-order coefficient decay from four *given* box bounds
  (the parametric form of `exists_pcoeff_decay4`);
* `exists_uniform_pcoeff_decay4` — hence the decay estimate with a constant independent of time.

Part of `LiWangWienerPaperSourceRealizationPacket` v10.0.
-/
import LiWangWiener.SmoothFirstOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.WienerModel

/-! ## 1. The time slice -/

/-- The spatial slice of a space-time function at a fixed time. -/
noncomputable def slice (Φ : ℝ × (ℝ × ℝ) → ℂ) (t : ℝ) : ℝ × ℝ → ℂ := fun p => Φ (t, p)

theorem contDiff_slice {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) (t : ℝ) :
    ContDiff ℝ ∞ (slice Φ t) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem hasFDerivAt_sliceEmb (t : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (fun p' : ℝ × ℝ => ((t : ℝ), p'))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p :=
  (hasFDerivAt_const t p).prodMk (hasFDerivAt_id p)

/-! ## 2. The spatial partials of a space-time function -/

/-- The spatial partial derivative in the first space variable. -/
noncomputable def spd0 (Φ : ℝ × (ℝ × ℝ) → ℂ) : ℝ × (ℝ × ℝ) → ℂ :=
  fun q => fderiv ℝ Φ q (0, (1, 0))

/-- The spatial partial derivative in the second space variable. -/
noncomputable def spd1 (Φ : ℝ × (ℝ × ℝ) → ℂ) : ℝ × (ℝ × ℝ) → ℂ :=
  fun q => fderiv ℝ Φ q (0, (0, 1))

theorem contDiff_spd0 {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (spd0 Φ) :=
  (h.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_spd1 {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (spd1 Φ) :=
  (h.fderiv_right (by simp)).clm_apply contDiff_const

/-- **The slice of the spatial partial is the partial of the slice.** -/
theorem slice_spd0 {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) (t : ℝ) :
    slice (spd0 Φ) t = pd0 (slice Φ t) := by
  funext p
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (t, p)) (t, p) :=
    (h.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hΦ.comp p (hasFDerivAt_sliceEmb t p)
  have hfd : fderiv ℝ (slice Φ t) p
      = (fderiv ℝ Φ (t, p)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) := hcomp.fderiv
  show fderiv ℝ Φ (t, p) (0, (1, 0)) = fderiv ℝ (slice Φ t) p (1, 0)
  rw [hfd]
  rfl

/-- **The slice of the spatial partial is the partial of the slice.** -/
theorem slice_spd1 {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) (t : ℝ) :
    slice (spd1 Φ) t = pd1 (slice Φ t) := by
  funext p
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (t, p)) (t, p) :=
    (h.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hΦ.comp p (hasFDerivAt_sliceEmb t p)
  have hfd : fderiv ℝ (slice Φ t) p
      = (fderiv ℝ Φ (t, p)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) := hcomp.fderiv
  show fderiv ℝ Φ (t, p) (0, (0, 1)) = fderiv ℝ (slice Φ t) p (0, 1)
  rw [hfd]
  rfl

/-- A spatial partial inherits the time support: where the slice vanishes identically, so does
its spatial derivative. -/
theorem spd0_vanishes {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) {t : ℝ}
    (hz : ∀ p, Φ (t, p) = 0) : ∀ p, spd0 Φ (t, p) = 0 := by
  intro p
  have hsl : slice Φ t = fun _ : ℝ × ℝ => (0 : ℂ) := funext hz
  have hs := congrFun (slice_spd0 h t) p
  have h2 : pd0 (slice Φ t) p = 0 := by
    show fderiv ℝ (slice Φ t) p (1, 0) = 0
    rw [hsl]
    simp
  show slice (spd0 Φ) t p = 0
  rw [hs, h2]

theorem spd1_vanishes {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) {t : ℝ}
    (hz : ∀ p, Φ (t, p) = 0) : ∀ p, spd1 Φ (t, p) = 0 := by
  intro p
  have hsl : slice Φ t = fun _ : ℝ × ℝ => (0 : ℂ) := funext hz
  have hs := congrFun (slice_spd1 h t) p
  have h2 : pd1 (slice Φ t) p = 0 := by
    show fderiv ℝ (slice Φ t) p (0, 1) = 0
    rw [hsl]
    simp
  show slice (spd1 Φ) t p = 0
  rw [hs, h2]

/-! ## 3. Box bounds uniform in time -/

/-- **A continuous space-time function supported in a compact time interval is bounded on the
fundamental spatial square, uniformly in time.** -/
theorem exists_uniform_box_bound {Φ : ℝ × (ℝ × ℝ) → ℂ} (hc : Continuous Φ)
    {t₀ t₁ : ℝ} (ht01 : t₀ ≤ t₁)
    (hsupp : ∀ t ∉ Set.Icc t₀ t₁, ∀ p, Φ (t, p) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1,
      ‖Φ (t, (y0, y1))‖ ≤ C := by
  have hK : IsCompact (Set.Icc t₀ t₁ ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hne : (Set.Icc t₀ t₁ ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)).Nonempty :=
    ⟨(t₀, (0, 0)),
      Set.mem_prod.2 ⟨⟨le_refl _, ht01⟩,
        Set.mem_prod.2 ⟨by norm_num, by norm_num⟩⟩⟩
  obtain ⟨q, -, hmax⟩ := hK.exists_isMaxOn hne (Continuous.continuousOn hc.norm)
  refine ⟨max 0 ‖Φ q‖, le_max_left _ _, fun t y0 hy0 y1 hy1 => ?_⟩
  by_cases ht : t ∈ Set.Icc t₀ t₁
  · refine le_trans ?_ (le_max_right 0 ‖Φ q‖)
    rw [uIoc_zero_one] at hy0 hy1
    exact isMaxOn_iff.1 hmax (t, (y0, y1))
      (Set.mem_prod.2 ⟨ht,
        Set.mem_prod.2 ⟨Set.Ioc_subset_Icc_self hy0, Set.Ioc_subset_Icc_self hy1⟩⟩)
  · rw [hsupp t ht, norm_zero]
    exact le_max_left _ _

/-! ## 4. The fourth-order decay with a given constant -/

/-- **The parametric form of `exists_pcoeff_decay4`**: from four box bounds with the *same*
constant, the fourth-order coefficient decay with that constant. -/
theorem pcoeff_decay4_of_bounds {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) {C : ℝ}
    (hb0 : ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1, ‖G (y0, y1)‖ ≤ C)
    (hb1 : ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1,
      ‖pd0 (pd0 (pd0 (pd0 G))) (y0, y1)‖ ≤ C)
    (hb2 : ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1,
      ‖pd1 (pd1 (pd1 (pd1 G))) (y0, y1)‖ ≤ C)
    (hb3 : ∀ y0 ∈ Set.uIoc (0:ℝ) 1, ∀ y1 ∈ Set.uIoc (0:ℝ) 1,
      ‖pd0 (pd0 (pd0 (pd0 (pd1 (pd1 (pd1 (pd1 G))))))) (y0, y1)‖ ≤ C) (k : Gam) :
    ‖pcoeff G k‖ ≤ C * (decayWeight4 (k 0) * decayWeight4 (k 1)) := by
  have hnorm4 : ∀ n : ℤ, ‖((twoPiI * ((n : ℤ) : ℂ)) ^ 2) ^ 2‖
      = ((2 * Real.pi * |(n : ℝ)|) ^ 2) ^ 2 := by
    intro n; rw [norm_pow, norm_twoPiI_pow_two]
  by_cases h0 : k 0 = 0 <;> by_cases h1 : k 1 = 0
  · rw [h0, h1, decayWeight4_zero, mul_one, mul_one]
    exact norm_pcoeff_le hb0 k
  · rw [h0, decayWeight4_zero, one_mul, decayWeight4_of_ne h1]
    have hr : (0:ℝ) < ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2 :=
      pow_pos (twoPiI_pow_two_pos h1) 2
    have hmain := norm_le_div_of_factor hr (hnorm4 (k 1)) (pcoeff_pd1_four h k)
      (norm_pcoeff_le hb2 k)
    calc ‖pcoeff G k‖ ≤ C / ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2 := hmain
      _ = C * (1 / ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2) := div_eq_mul_one_div _ _
  · rw [h1, decayWeight4_zero, mul_one, decayWeight4_of_ne h0]
    have hr : (0:ℝ) < ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2 :=
      pow_pos (twoPiI_pow_two_pos h0) 2
    have hmain := norm_le_div_of_factor hr (hnorm4 (k 0)) (pcoeff_pd0_four h k)
      (norm_pcoeff_le hb1 k)
    calc ‖pcoeff G k‖ ≤ C / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2 := hmain
      _ = C * (1 / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2) := div_eq_mul_one_div _ _
  · rw [decayWeight4_of_ne h0, decayWeight4_of_ne h1]
    have hfac : pcoeff (pd0 (pd0 (pd0 (pd0 (pd1 (pd1 (pd1 (pd1 G)))))))) k
        = (((twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2) ^ 2 * ((twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2) ^ 2)
            * pcoeff G k := by
      rw [pcoeff_pd0_four h.pd1'.pd1'.pd1'.pd1' k, pcoeff_pd1_four h k]
      ring
    have hru : ‖((twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2) ^ 2 * ((twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2) ^ 2‖
        = ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2
            * ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2 := by
      rw [norm_mul, hnorm4, hnorm4]
    have hr : (0:ℝ) < ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2
        * ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2 :=
      mul_pos (pow_pos (twoPiI_pow_two_pos h0) 2) (pow_pos (twoPiI_pow_two_pos h1) 2)
    have hmain := norm_le_div_of_factor hr hru hfac (norm_pcoeff_le hb3 k)
    calc ‖pcoeff G k‖
        ≤ C / (((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2
            * ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2) := hmain
      _ = C * (1 / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2
            * (1 / ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2)) := by field_simp

/-! ## 5. The decay estimate, uniform in time -/

/-- Iterated spatial partials commute with slicing. -/
theorem slice_spd0_four {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) (t : ℝ) :
    slice (spd0 (spd0 (spd0 (spd0 Φ)))) t = pd0 (pd0 (pd0 (pd0 (slice Φ t)))) := by
  rw [slice_spd0 (contDiff_spd0 (contDiff_spd0 (contDiff_spd0 h))) t,
    slice_spd0 (contDiff_spd0 (contDiff_spd0 h)) t, slice_spd0 (contDiff_spd0 h) t,
    slice_spd0 h t]

theorem slice_spd1_four {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) (t : ℝ) :
    slice (spd1 (spd1 (spd1 (spd1 Φ)))) t = pd1 (pd1 (pd1 (pd1 (slice Φ t)))) := by
  rw [slice_spd1 (contDiff_spd1 (contDiff_spd1 (contDiff_spd1 h))) t,
    slice_spd1 (contDiff_spd1 (contDiff_spd1 h)) t, slice_spd1 (contDiff_spd1 h) t,
    slice_spd1 h t]

theorem spd0_four_vanishes {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) {t : ℝ}
    (hz : ∀ p, Φ (t, p) = 0) : ∀ p, spd0 (spd0 (spd0 (spd0 Φ))) (t, p) = 0 :=
  spd0_vanishes (contDiff_spd0 (contDiff_spd0 (contDiff_spd0 h)))
    (spd0_vanishes (contDiff_spd0 (contDiff_spd0 h))
      (spd0_vanishes (contDiff_spd0 h) (spd0_vanishes h hz)))

theorem spd1_four_vanishes {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) {t : ℝ}
    (hz : ∀ p, Φ (t, p) = 0) : ∀ p, spd1 (spd1 (spd1 (spd1 Φ))) (t, p) = 0 :=
  spd1_vanishes (contDiff_spd1 (contDiff_spd1 (contDiff_spd1 h)))
    (spd1_vanishes (contDiff_spd1 (contDiff_spd1 h))
      (spd1_vanishes (contDiff_spd1 h) (spd1_vanishes h hz)))

theorem contDiff_spd0_four {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (spd0 (spd0 (spd0 (spd0 Φ)))) :=
  contDiff_spd0 (contDiff_spd0 (contDiff_spd0 (contDiff_spd0 h)))

theorem contDiff_spd1_four {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (spd1 (spd1 (spd1 (spd1 Φ)))) :=
  contDiff_spd1 (contDiff_spd1 (contDiff_spd1 (contDiff_spd1 h)))

/-- The spatial slice of a jointly smooth doubly periodic space-time function. -/
theorem isSmoothPeriodic_slice {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y))) (t : ℝ) :
    IsSmoothPeriodic (slice Φ t) where
  smooth := contDiff_slice hsm t
  per0 p := hper0 t p.1 p.2
  per1 p := hper1 t p.1 p.2

/-- **The fourth-order coefficient decay, with a constant independent of time.** -/
theorem exists_uniform_pcoeff_decay4 {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y)))
    {t₀ t₁ : ℝ} (ht01 : t₀ ≤ t₁)
    (hsupp : ∀ t ∉ Set.Icc t₀ t₁, ∀ p, Φ (t, p) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (k : Gam),
      ‖pcoeff (slice Φ t) k‖ ≤ C * (decayWeight4 (k 0) * decayWeight4 (k 1)) := by
  obtain ⟨C0, hC00, hB0⟩ := exists_uniform_box_bound hsm.continuous ht01 hsupp
  obtain ⟨C1, hC10, hB1⟩ := exists_uniform_box_bound (contDiff_spd0_four hsm).continuous ht01
    (fun t ht => spd0_four_vanishes hsm (hsupp t ht))
  obtain ⟨C2, hC20, hB2⟩ := exists_uniform_box_bound (contDiff_spd1_four hsm).continuous ht01
    (fun t ht => spd1_four_vanishes hsm (hsupp t ht))
  obtain ⟨C3, hC30, hB3⟩ := exists_uniform_box_bound
    (contDiff_spd0_four (contDiff_spd1_four hsm)).continuous ht01
    (fun t ht => spd0_four_vanishes (contDiff_spd1_four hsm)
      (spd1_four_vanishes hsm (hsupp t ht)))
  refine ⟨max (max C0 C1) (max C2 C3),
    le_trans hC00 (le_trans (le_max_left _ _) (le_max_left _ _)), fun t k => ?_⟩
  set C := max (max C0 C1) (max C2 C3) with hCdef
  have hCC0 : C0 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC1 : C1 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCC2 : C2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCC3 : C3 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine pcoeff_decay4_of_bounds (isSmoothPeriodic_slice hsm hper0 hper1 t)
    (fun y0 hy0 y1 hy1 => le_trans (hB0 t y0 hy0 y1 hy1) hCC0) ?_ ?_ ?_ k
  · intro y0 hy0 y1 hy1
    have := hB1 t y0 hy0 y1 hy1
    rw [show spd0 (spd0 (spd0 (spd0 Φ))) (t, (y0, y1))
        = pd0 (pd0 (pd0 (pd0 (slice Φ t)))) (y0, y1) from
      congrFun (slice_spd0_four hsm t) (y0, y1)] at this
    exact le_trans this hCC1
  · intro y0 hy0 y1 hy1
    have := hB2 t y0 hy0 y1 hy1
    rw [show spd1 (spd1 (spd1 (spd1 Φ))) (t, (y0, y1))
        = pd1 (pd1 (pd1 (pd1 (slice Φ t)))) (y0, y1) from
      congrFun (slice_spd1_four hsm t) (y0, y1)] at this
    exact le_trans this hCC2
  · intro y0 hy0 y1 hy1
    have hb := hB3 t y0 hy0 y1 hy1
    have hfun : slice (spd0 (spd0 (spd0 (spd0 (spd1 (spd1 (spd1 (spd1 Φ)))))))) t
        = pd0 (pd0 (pd0 (pd0 (pd1 (pd1 (pd1 (pd1 (slice Φ t)))))))) := by
      rw [slice_spd0_four (contDiff_spd1_four hsm) t, slice_spd1_four hsm t]
    have heq : pd0 (pd0 (pd0 (pd0 (pd1 (pd1 (pd1 (pd1 (slice Φ t)))))))) (y0, y1)
        = spd0 (spd0 (spd0 (spd0 (spd1 (spd1 (spd1 (spd1 Φ))))))) (t, (y0, y1)) :=
      (congrFun hfun (y0, y1)).symm
    rw [heq]
    exact le_trans hb hCC3

/-! ## 6. Continuity in time of the Fourier coefficients and of the Wiener element -/

/-- **The Fourier coefficients of the slices are continuous in time.**  Two nested applications
of the parametric interval-integral continuity theorem. -/
theorem continuous_pcoeff_slice {Φ : ℝ × (ℝ × ℝ) → ℂ} (hc : Continuous Φ) (k : Gam) :
    Continuous fun t : ℝ => pcoeff (slice Φ t) k := by
  have hinner : Continuous fun q : ℝ × ℝ =>
      ∫ y1 in (0:ℝ)..1, Φ (q.1, (q.2, y1)) * chi (-(k 1)) y1 := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : ℝ × ℝ) (y1 : ℝ) => Φ (q.1, (q.2, y1)) * chi (-(k 1)) y1) ?_ 0 1
    exact (hc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).mul
      ((continuous_chi _).comp continuous_snd)
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (t : ℝ) (y0 : ℝ) =>
      (∫ y1 in (0:ℝ)..1, Φ (t, (y0, y1)) * chi (-(k 1)) y1) * chi (-(k 0)) y0) ?_ 0 1
  exact (hinner.comp (continuous_fst.prodMk continuous_snd)).mul
    ((continuous_chi _).comp continuous_snd)

/-- Bridge between the two spellings of a sum over the complement of a finite set. -/
theorem tsum_compl_spelling_gam {f : Gam → ℝ} (F : Finset Gam) :
    (∑' k : {x : Gam // x ∉ F}, f (k : Gam))
      = ∑' k : ((F : Set Gam)ᶜ : Set Gam), f (k : Gam) := rfl

theorem summable_decayWeight4 : Summable decayWeight4 :=
  Summable.of_nonneg_of_le (fun n => (decayWeight4_pos n).le) decayWeight4_le summable_decayWeight

/-- **The Wiener element of the slice is continuous in time**, in the `ℓ¹` norm.  The tail is
controlled uniformly in time by the fourth-order decay estimate, and the finitely many remaining
coefficients are continuous. -/
theorem continuous_wienerSlice {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y)))
    {a₀ a₁ : ℝ} (ha01 : a₀ ≤ a₁)
    (hsupp : ∀ t ∉ Set.Icc a₀ a₁, ∀ p, Φ (t, p) = 0) :
    Continuous fun t : ℝ =>
      wienerOfSmooth (slice Φ t) (isSmoothPeriodic_slice hsm hper0 hper1 t) := by
  classical
  set A : ℝ → Wiener :=
    fun t => wienerOfSmooth (slice Φ t) (isSmoothPeriodic_slice hsm hper0 hper1 t) with hA
  obtain ⟨C, hC0, hdec⟩ := exists_uniform_pcoeff_decay4 hsm hper0 hper1 ha01 hsupp
  set maj : Gam → ℝ := fun k => C * decayWeight4 (k 0) * decayWeight4 (k 1) with hmajdef
  have hmaj0 : ∀ k, 0 ≤ maj k := fun k => by
    rw [hmajdef]
    exact mul_nonneg (mul_nonneg hC0 (decayWeight4_pos _).le) (decayWeight4_pos _).le
  have hmajsum : Summable maj :=
    summable_gam_of_prod (f := fun n => C * decayWeight4 n) (g := decayWeight4)
      (summable_decayWeight4.mul_left C) summable_decayWeight4
      (fun n => mul_nonneg hC0 (decayWeight4_pos n).le)
      (fun n => (decayWeight4_pos n).le)
  have hbound : ∀ (t : ℝ) (k : Gam), ‖pcoeff (slice Φ t) k‖ ≤ maj k := by
    intro t k
    refine le_trans (hdec t k) (le_of_eq ?_)
    rw [hmajdef]; ring
  have hsub : ∀ (t s : ℝ) (k : Gam),
      ((A t - A s : Wiener) k) = pcoeff (slice Φ t) k - pcoeff (slice Φ s) k := by
    intro t s k; rw [lp.coeFn_sub]; rfl
  have hdsum : ∀ t s : ℝ,
      Summable fun k : Gam => ‖pcoeff (slice Φ t) k - pcoeff (slice Φ s) k‖ :=
    fun t s => (wiener_summable (A t - A s)).congr (fun k => by rw [hsub])
  rw [Metric.continuous_iff]
  intro s₀ ε hε
  have hε4 : (0:ℝ) < ε / 4 := by linarith
  obtain ⟨F, hF⟩ :=
    ((tendsto_tsum_compl_atTop_zero maj).eventually (eventually_lt_nhds hε4)).exists
  -- the finite part is continuous and vanishes at `s₀`
  have hfin : Continuous fun t : ℝ =>
      ∑ k ∈ F, ‖pcoeff (slice Φ t) k - pcoeff (slice Φ s₀) k‖ :=
    continuous_finset_sum F
      (fun k _ => ((continuous_pcoeff_slice hsm.continuous k).sub continuous_const).norm)
  have hzero : (∑ k ∈ F, ‖pcoeff (slice Φ s₀) k - pcoeff (slice Φ s₀) k‖) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [sub_self, norm_zero]
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.1 (hfin.continuousAt (x := s₀)) (ε / 2)
    (by linarith)
  refine ⟨δ, hδ0, fun t htd => ?_⟩
  have hfinlt : (∑ k ∈ F, ‖pcoeff (slice Φ t) k - pcoeff (slice Φ s₀) k‖) < ε / 2 := by
    have := hδ htd
    rw [Real.dist_eq, hzero, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  -- the tail is controlled uniformly
  have htail : (∑' k : {x : Gam // x ∉ F},
      ‖pcoeff (slice Φ t) (k : Gam) - pcoeff (slice Φ s₀) (k : Gam)‖)
        ≤ 2 * (∑' k : {x : Gam // x ∉ F}, maj (k : Gam)) := by
    have hle : (∑' k : {x : Gam // x ∉ F},
        ‖pcoeff (slice Φ t) (k : Gam) - pcoeff (slice Φ s₀) (k : Gam)‖)
          ≤ ∑' k : {x : Gam // x ∉ F}, 2 * maj (k : Gam) := by
      refine Summable.tsum_le_tsum (fun k => ?_) ((hdsum t s₀).subtype _)
        ((hmajsum.subtype _).mul_left 2)
      refine le_trans (norm_sub_le _ _) ?_
      have h1 := hbound t (k : Gam)
      have h2 := hbound s₀ (k : Gam)
      linarith
    have heq : (∑' k : {x : Gam // x ∉ F}, 2 * maj (k : Gam))
        = 2 * ∑' k : {x : Gam // x ∉ F}, maj (k : Gam) := tsum_mul_left
    linarith
  have hsplit := (hdsum t s₀).sum_add_tsum_compl (s := F)
  have hnorm : dist (A t) (A s₀)
      = ∑' k : Gam, ‖pcoeff (slice Φ t) k - pcoeff (slice Φ s₀) k‖ := by
    rw [dist_eq_norm, wiener_norm_eq]
    exact tsum_congr (fun k => by rw [hsub])
  show dist (A t) (A s₀) < ε
  rw [hnorm, ← hsplit]
  have hmajlt : (∑' k : {x : Gam // x ∉ F}, maj (k : Gam)) < ε / 4 := hF
  rw [tsum_compl_spelling_gam
    (f := fun k => ‖pcoeff (slice Φ t) k - pcoeff (slice Φ s₀) k‖) F] at htail
  linarith

end LiWang.WienerModel
