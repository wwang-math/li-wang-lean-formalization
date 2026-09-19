/-
# Smooth profiles are **first-order** states

`SmoothPeriodic` proves that a `C^∞` doubly periodic function has absolutely summable Fourier
coefficients, i.e. that it lies in the Wiener algebra `A(𝕋²)`.  The rest of the development
works with the *first-order* space `A¹(𝕋²)` (weight `wt k = 1 + |k₀| + |k₁|`), so this module
pushes the same integration-by-parts argument two steps further:

* `pcoeff_pd0_four`, `pcoeff_pd1_four` — **four** integrations by parts in each variable;
* `exists_pcoeff_decay4` — the resulting `|ĉ(k)| ≤ C·b₄(k₀)·b₄(k₁)` with `b₄(n) = (2π|n|)^{-4}`;
* `summable_wt_norm_pcoeff` — hence `∑ₖ wt k · |ĉ(k)| < ∞`;
* `wiener1OfSmooth` — the smooth profile as an actual element of `A¹(𝕋²)`, with
  `incl (wiener1OfSmooth G h) = wienerOfSmooth G h`;
* `exists_smooth_localized_profile1` — for every nonempty open `W`, a **nonzero first-order**
  real state whose physical field is `C^∞` and supported in a compact subset of `W`.

Part of `LiWangFormalizationSmoothObservationPacket` v5.0.
-/
import LiWangFormalization.SmoothSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.Formalization

/-! ## 1. Four integrations by parts in each variable -/

theorem pcoeff_pd1_four {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    pcoeff (pd1 (pd1 (pd1 (pd1 G)))) k
      = ((twoPiI * ((k 1 : ℤ) : ℂ)) ^ 2) ^ 2 * pcoeff G k := by
  rw [pcoeff_pd1_two h.pd1'.pd1' k, pcoeff_pd1_two h k]
  ring

theorem pcoeff_pd0_four {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    pcoeff (pd0 (pd0 (pd0 (pd0 G)))) k
      = ((twoPiI * ((k 0 : ℤ) : ℂ)) ^ 2) ^ 2 * pcoeff G k := by
  rw [pcoeff_pd0_two h.pd0'.pd0' k, pcoeff_pd0_two h k]
  ring

/-- The fourth-order weight `b₄(n) = (2π|n|)^{-4}` for `n ≠ 0`, and `b₄(0) = 1`. -/
noncomputable def decayWeight4 (n : ℤ) : ℝ :=
  if n = 0 then 1 else 1 / ((2 * Real.pi * |(n : ℝ)|) ^ 2) ^ 2

theorem decayWeight4_zero : decayWeight4 0 = 1 := by simp [decayWeight4]

theorem decayWeight4_of_ne {n : ℤ} (hn : n ≠ 0) :
    decayWeight4 n = 1 / ((2 * Real.pi * |(n : ℝ)|) ^ 2) ^ 2 := by
  rw [decayWeight4, if_neg hn]

theorem decayWeight4_pos (n : ℤ) : 0 < decayWeight4 n := by
  by_cases hn : n = 0
  · rw [decayWeight4, if_pos hn]; norm_num
  · rw [decayWeight4_of_ne hn]
    exact one_div_pos.2 (pow_pos (twoPiI_pow_two_pos hn) 2)

theorem one_le_abs_intCast {n : ℤ} (hn : n ≠ 0) : (1:ℝ) ≤ |(n : ℝ)| := by
  have h1 : (1:ℤ) ≤ |n| := Int.one_le_abs hn
  have h2 : ((1:ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h1
  rwa [Int.cast_abs, Int.cast_one] at h2

theorem one_le_twoPi_sq_abs {n : ℤ} (hn : n ≠ 0) :
    (1:ℝ) ≤ (2 * Real.pi * |(n : ℝ)|) ^ 2 := by
  have h1 : (1:ℝ) ≤ |(n : ℝ)| := one_le_abs_intCast hn
  have hpi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have hprod : (1:ℝ) ≤ 2 * Real.pi * |(n : ℝ)| := by nlinarith
  exact one_le_pow₀ hprod

theorem decayWeight4_le (n : ℤ) : decayWeight4 n ≤ decayWeight n := by
  by_cases hn : n = 0
  · subst hn; rw [decayWeight4_zero, decayWeight_zero]
  · rw [decayWeight4_of_ne hn, decayWeight_of_ne hn]
    have hb := twoPiI_pow_two_pos hn
    have h1 := one_le_twoPi_sq_abs hn
    refine one_div_le_one_div_of_le hb ?_
    nlinarith

theorem weighted_decayWeight4_le (n : ℤ) :
    (1 + |(n : ℝ)|) * decayWeight4 n ≤ 2 * decayWeight n := by
  by_cases hn : n = 0
  · subst hn
    rw [decayWeight4_zero, decayWeight_zero]
    norm_num
  · rw [decayWeight4_of_ne hn, decayWeight_of_ne hn]
    set A : ℝ := (2 * Real.pi * |(n : ℝ)|) ^ 2 with hA
    have hApos : (0:ℝ) < A := twoPiI_pow_two_pos hn
    have habs : (1:ℝ) ≤ |(n : ℝ)| := one_le_abs_intCast hn
    have hAt : |(n : ℝ)| ^ 2 ≤ A := by
      have hpi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
      have hle : |(n : ℝ)| ≤ 2 * Real.pi * |(n : ℝ)| := by
        nlinarith [abs_nonneg ((n : ℝ))]
      rw [hA]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    have hkey : 1 + |(n : ℝ)| ≤ 2 * A := by nlinarith
    calc (1 + |(n : ℝ)|) * (1 / A ^ 2) ≤ (2 * A) * (1 / A ^ 2) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 2 * (1 / A) := by field_simp

theorem wt_le_prod (k : Gam) :
    wt k ≤ (1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|) := by
  have h0 := abs_nonneg ((k 0 : ℤ) : ℝ)
  have h1 := abs_nonneg ((k 1 : ℤ) : ℝ)
  show 1 + |((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)| ≤ _
  nlinarith

/-! ## 2. The fourth-order decay estimate -/

theorem exists_pcoeff_decay4 {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Gam,
      ‖pcoeff G k‖ ≤ C * (decayWeight4 (k 0) * decayWeight4 (k 1)) := by
  obtain ⟨C0, hC0, hb0⟩ := exists_box_bound h.continuous
  obtain ⟨C1, hC1, hb1⟩ := exists_box_bound
    (contDiff_pd0 (contDiff_pd0 (contDiff_pd0 (contDiff_pd0 h.smooth)))).continuous
  obtain ⟨C2, hC2, hb2⟩ := exists_box_bound
    (contDiff_pd1 (contDiff_pd1 (contDiff_pd1 (contDiff_pd1 h.smooth)))).continuous
  obtain ⟨C3, hC3, hb3⟩ := exists_box_bound
    (contDiff_pd0 (contDiff_pd0 (contDiff_pd0 (contDiff_pd0
      (contDiff_pd1 (contDiff_pd1 (contDiff_pd1 (contDiff_pd1 h.smooth)))))))).continuous
  refine ⟨max (max C0 C1) (max C2 C3), le_trans hC0 (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun k => ?_⟩
  set C := max (max C0 C1) (max C2 C3) with hCdef
  have hCC0 : C0 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC1 : C1 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCC2 : C2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCC3 : C3 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hnorm4 : ∀ n : ℤ, ‖((twoPiI * ((n : ℤ) : ℂ)) ^ 2) ^ 2‖
      = ((2 * Real.pi * |(n : ℝ)|) ^ 2) ^ 2 := by
    intro n; rw [norm_pow, norm_twoPiI_pow_two]
  by_cases h0 : k 0 = 0 <;> by_cases h1 : k 1 = 0
  · rw [h0, h1, decayWeight4_zero, mul_one, mul_one]
    exact le_trans (norm_pcoeff_le hb0 k) hCC0
  · rw [h0, decayWeight4_zero, one_mul, decayWeight4_of_ne h1]
    have hr : (0:ℝ) < ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2 :=
      pow_pos (twoPiI_pow_two_pos h1) 2
    have hmain := norm_le_div_of_factor hr (hnorm4 (k 1)) (pcoeff_pd1_four h k)
      (norm_pcoeff_le hb2 k)
    calc ‖pcoeff G k‖ ≤ C2 / ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2 := hmain
      _ ≤ C * (1 / ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hCC2 (by positivity)
  · rw [h1, decayWeight4_zero, mul_one, decayWeight4_of_ne h0]
    have hr : (0:ℝ) < ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2 :=
      pow_pos (twoPiI_pow_two_pos h0) 2
    have hmain := norm_le_div_of_factor hr (hnorm4 (k 0)) (pcoeff_pd0_four h k)
      (norm_pcoeff_le hb1 k)
    calc ‖pcoeff G k‖ ≤ C1 / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2 := hmain
      _ ≤ C * (1 / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hCC1 (by positivity)
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
        ≤ C3 / (((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2
            * ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2) := hmain
      _ = C3 * (1 / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2
            * (1 / ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2)) := by field_simp
      _ ≤ C * (1 / ((2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2) ^ 2
            * (1 / ((2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_right hCC3 (by positivity)

/-! ## 3. Smooth profiles lie in the first-order space -/

/-- **Smoothness discharges the weighted summability too.** -/
theorem summable_wt_norm_pcoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    Summable fun k : Gam => wt k * ‖pcoeff G k‖ := by
  obtain ⟨C, hC, hbd⟩ := exists_pcoeff_decay4 h
  have hmaj : Summable fun k : Gam => (4 * C) * decayWeight (k 0) * decayWeight (k 1) := by
    refine summable_gam_of_prod (f := fun n => (4 * C) * decayWeight n) (g := decayWeight)
      (summable_decayWeight.mul_left (4 * C)) summable_decayWeight
      (fun n => mul_nonneg (by linarith) (decayWeight_pos n).le)
      (fun n => (decayWeight_pos n).le)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _)) (fun k => ?_) hmaj
  have hk : wt k * ‖pcoeff G k‖
      ≤ ((1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|)) * (C * (decayWeight4 (k 0)
          * decayWeight4 (k 1))) := by
    refine mul_le_mul (wt_le_prod k) (hbd k) (norm_nonneg _) ?_
    have h0 := abs_nonneg ((k 0 : ℤ) : ℝ)
    have h1 := abs_nonneg ((k 1 : ℤ) : ℝ)
    nlinarith
  refine le_trans hk ?_
  have e : ((1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|))
        * (C * (decayWeight4 (k 0) * decayWeight4 (k 1)))
      = C * (((1 + |((k 0 : ℤ) : ℝ)|) * decayWeight4 (k 0))
          * ((1 + |((k 1 : ℤ) : ℝ)|) * decayWeight4 (k 1))) := by ring
  rw [e]
  have hprod : ((1 + |((k 0 : ℤ) : ℝ)|) * decayWeight4 (k 0))
        * ((1 + |((k 1 : ℤ) : ℝ)|) * decayWeight4 (k 1))
      ≤ (2 * decayWeight (k 0)) * (2 * decayWeight (k 1)) := by
    have hn0 : (0:ℝ) ≤ (1 + |((k 1 : ℤ) : ℝ)|) * decayWeight4 (k 1) :=
      mul_nonneg (by positivity) (decayWeight4_pos _).le
    have hn1 : (0:ℝ) ≤ 2 * decayWeight (k 0) :=
      mul_nonneg (by norm_num) (decayWeight_pos _).le
    exact mul_le_mul (weighted_decayWeight4_le (k 0)) (weighted_decayWeight4_le (k 1)) hn0 hn1
  calc C * (((1 + |((k 0 : ℤ) : ℝ)|) * decayWeight4 (k 0))
        * ((1 + |((k 1 : ℤ) : ℝ)|) * decayWeight4 (k 1)))
      ≤ C * ((2 * decayWeight (k 0)) * (2 * decayWeight (k 1))) :=
        mul_le_mul_of_nonneg_left hprod hC
    _ = (4 * C) * decayWeight (k 0) * decayWeight (k 1) := by ring

/-- The smooth profile as an actual **first-order** state. -/
noncomputable def wiener1OfSmooth (G : ℝ × ℝ → ℂ) (h : IsSmoothPeriodic G) : Wiener1 :=
  Wiener1.mk (pcoeff G) (summable_wt_norm_pcoeff h)

@[simp] theorem coeff_wiener1OfSmooth (G : ℝ × ℝ → ℂ) (h : IsSmoothPeriodic G) (k : Gam) :
    (wiener1OfSmooth G h).coeff k = pcoeff G k := rfl

theorem incl_wiener1OfSmooth (G : ℝ × ℝ → ℂ) (h : IsSmoothPeriodic G) :
    incl (wiener1OfSmooth G h) = wienerOfSmooth G h := lp.ext (funext fun _ => rfl)

/-- **A nonzero first-order smooth profile supported in a compact subset of any nonempty open
region.**  This is `exists_smooth_localized_profile` upgraded to `A¹(𝕋²)`. -/
theorem exists_smooth_localized_profile1 {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (u : Wiener1) (K : Set Torus2),
      u ≠ 0 ∧ SmoothWiener (incl u) ∧ IsCompact K ∧ K ⊆ W ∧
      ∀ x ∉ K, synth (incl u) x = 0 := by
  obtain ⟨a, K, hane, hsm, hKc, hKW, hvan⟩ := exists_smooth_localized_profile hW hne
  have hper : IsSmoothPeriodic (planeLift a.val) := isSmoothPeriodic_planeLift hsm
  have hinv : wienerOfSmooth (planeLift a.val) hper = a.val :=
    planeLift_injective (planeLift_wienerOfSmooth hper)
  refine ⟨wiener1OfSmooth (planeLift a.val) hper, K, ?_, ?_, hKc, hKW, ?_⟩
  · intro hz
    have hincl : incl (wiener1OfSmooth (planeLift a.val) hper) = 0 := by rw [hz, map_zero]
    rw [incl_wiener1OfSmooth, hinv] at hincl
    exact hane (RealWiener.val_injective (by rw [hincl]; rfl))
  · rw [incl_wiener1OfSmooth, hinv]; exact hsm
  · intro x hx
    rw [incl_wiener1OfSmooth, hinv]
    exact hvan x hx

end LiWang.Formalization
