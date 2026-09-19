/-
# The forced equation

The same local theory with a source term:

    ∂t θ + ∇^⊥(κ ∗ θ) · ∇θ + (-Δ)^α θ = f ,   θ(0) = θ₀ ,

whose mild formulation is

    θ(t) = e^{-t(-Δ)^α}θ₀ + ∫₀^t e^{-(t-s)(-Δ)^α} f(s) ds
             - ∫₀^t e^{-(t-s)(-Δ)^α} N_m(θ(s), θ(s)) ds .

The forcing only changes the *affine part* of the Duhamel map, so the abstract contraction
argument of `AffineFixedPoint.lean` applies verbatim.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.LocalSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal
open Filter Topology MeasureTheory BoundedContinuousFunction

namespace LiWang.WienerModel

/-- The affine part of the forced problem, truncated at the horizon `T` so that it is
globally bounded (on `[0,T]` the truncation is invisible). -/
noncomputable def forcedAffine {α : ℝ} (hα : 1 / 2 ≤ α) (u₀ : Wiener1) (F : ℝ → Wiener)
    (T : ℝ) (t : ℝ) : Wiener1 :=
  heatFlow1 α t u₀ + duhamelIntegral hα (min t T) F

theorem forcedAffine_eq {α : ℝ} (hα : 1 / 2 ≤ α) (u₀ : Wiener1) (F : ℝ → Wiener) {T t : ℝ}
    (ht : t ≤ T) :
    forcedAffine hα u₀ F T t = heatFlow1 α t u₀ + duhamelIntegral hα t F := by
  rw [forcedAffine, min_eq_left ht]

theorem continuous_forcedAffine {α : ℝ} (hα : 1 / 2 < α) (u₀ : Wiener1) {F : ℝ → Wiener}
    (hF : Continuous F) {MF : ℝ} (hMF : ∀ s, ‖F s‖ ≤ MF) (T : ℝ) :
    Continuous fun t : ℝ => forcedAffine hα.le u₀ F T t :=
  (continuous_heatFlow1 α u₀).add
    ((continuous_duhamelIntegral hα hF hMF).comp (continuous_id.min continuous_const))

theorem norm_forcedAffine_le {α : ℝ} (hα : 1 / 2 < α) (u₀ : Wiener1) {F : ℝ → Wiener}
    {MF : ℝ} (hMF : ∀ s, ‖F s‖ ≤ MF) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    ‖forcedAffine hα.le u₀ F T t‖ ≤ ‖u₀‖ + MF * duhamelConst α T := by
  have hMF0 : 0 ≤ MF := le_trans (norm_nonneg _) (hMF 0)
  refine le_trans (norm_add_le _ _) (add_le_add (norm_heatFlow1_le α t u₀) ?_)
  rcases le_or_gt (min t T) 0 with hmin | hmin
  · rw [duhamelIntegral_of_nonpos hα.le F hmin, norm_zero]
    exact mul_nonneg hMF0 (duhamelConst_nonneg hα hT)
  · refine le_trans (norm_duhamelIntegral_le hα hmin.le hMF) ?_
    exact mul_le_mul_of_nonneg_left
      (duhamelConst_mono hα hmin.le (min_le_right t T)) hMF0

/-- **Local existence for the forced equation.**  For a bounded continuous source `f` there
is a positive time and a bounded continuous curve satisfying the forced mild equation. -/
theorem exists_local_mild_solution_forced {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1)
    {F : ℝ → Wiener} (hF : Continuous F) {MF : ℝ} (hMF : ∀ s, ‖F s‖ ≤ MF) :
    ∃ T : ℝ, 0 < T ∧ ∃ (u : ℝ → Wiener1) (R : ℝ), Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ R) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm u) := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hpi := Real.pi_pos
  have hu₀ : (0:ℝ) ≤ ‖u₀‖ := norm_nonneg _
  have hMF0 : (0:ℝ) ≤ MF := le_trans (norm_nonneg _) (hMF 0)
  -- a radius that works for every horizon with `duhamelConst α T ≤ 1`
  set a₁ : ℝ := ‖u₀‖ + MF with ha₁
  set R₁ : ℝ := 2 * a₁ + 1 with hR₁
  have ha₁0 : (0:ℝ) ≤ a₁ := by simp only [ha₁]; linarith
  have hR₁0 : (0:ℝ) < R₁ := by simp only [hR₁]; linarith
  set L : ℝ := 8 * Real.pi * C * R₁ + 4 * Real.pi * C * R₁ * R₁ + 1 with hL
  have hL0 : (0:ℝ) < L := by simp only [hL]; positivity
  have hε : (0:ℝ) < min 1 (1 / (2 * L)) := by
    have : (0:ℝ) < 1 / (2 * L) := by positivity
    exact lt_min one_pos this
  obtain ⟨T, hT, hsm⟩ := exists_duhamelConst_lt hα (ε := min 1 (1 / (2 * L))) hε
  have hGT : duhamelConst α T ≤ 1 := le_trans (hsm T ⟨hT.le, le_rfl⟩).le (min_le_left _ _)
  have hGT2 : duhamelConst α T ≤ 1 / (2 * L) :=
    le_trans (hsm T ⟨hT.le, le_rfl⟩).le (min_le_right _ _)
  -- the affine part of the forced problem
  set a : ℝ := ‖u₀‖ + MF * duhamelConst α T with hadef
  have ha0 : (0:ℝ) ≤ a := by
    have := mul_nonneg hMF0 (duhamelConst_nonneg hα hT.le)
    simp only [hadef]; linarith
  have haR : 2 * a + 1 ≤ R₁ := by
    have h1 : MF * duhamelConst α T ≤ MF := by
      calc MF * duhamelConst α T ≤ MF * 1 := mul_le_mul_of_nonneg_left hGT hMF0
        _ = MF := mul_one MF
    simp only [hadef, hR₁, ha₁]; linarith
  have haA : ∀ t, ‖forcedAffine hα.le u₀ F T t‖ ≤ a :=
    fun t => norm_forcedAffine_le hα u₀ hMF hT.le t
  -- smallness for the abstract lemma
  have hcomb : ∀ t ∈ Set.Icc (0:ℝ) T,
      (8 * Real.pi * C * (2 * a + 1) + 4 * Real.pi * C * (2 * a + 1) * (2 * a + 1))
        * duhamelConst α t ≤ 1 / 2 := by
    intro t ht
    have hgt : duhamelConst α t ≤ 1 / (2 * L) := le_trans (hsm t ht).le (min_le_right _ _)
    have hg0 : 0 ≤ duhamelConst α t := duhamelConst_nonneg hα ht.1
    have ha2 : (0:ℝ) ≤ 2 * a + 1 := by linarith
    have hmono : 8 * Real.pi * C * (2 * a + 1)
        + 4 * Real.pi * C * (2 * a + 1) * (2 * a + 1)
        ≤ 8 * Real.pi * C * R₁ + 4 * Real.pi * C * R₁ * R₁ := by
      have h1 : 8 * Real.pi * C * (2 * a + 1) ≤ 8 * Real.pi * C * R₁ := by
        have : (0:ℝ) ≤ 8 * Real.pi * C := by positivity
        exact mul_le_mul_of_nonneg_left haR this
      have h2 : 4 * Real.pi * C * (2 * a + 1) * (2 * a + 1)
          ≤ 4 * Real.pi * C * R₁ * R₁ := by
        have hc : (0:ℝ) ≤ 4 * Real.pi * C := by positivity
        nlinarith [hR₁0.le, ha2]
      linarith
    have hcoef0 : (0:ℝ) ≤ 8 * Real.pi * C * R₁ + 4 * Real.pi * C * R₁ * R₁ := by positivity
    calc (8 * Real.pi * C * (2 * a + 1) + 4 * Real.pi * C * (2 * a + 1) * (2 * a + 1))
          * duhamelConst α t
        ≤ (8 * Real.pi * C * R₁ + 4 * Real.pi * C * R₁ * R₁) * duhamelConst α t :=
          mul_le_mul_of_nonneg_right hmono hg0
      _ ≤ (8 * Real.pi * C * R₁ + 4 * Real.pi * C * R₁ * R₁) * (1 / (2 * L)) :=
          mul_le_mul_of_nonneg_left hgt hcoef0
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * L)]
          have hexp : (1:ℝ) / 2 * (2 * L) = L := by ring
          rw [hexp, hL]
          linarith
  obtain ⟨-, U, hUmem, hfix, -⟩ :=
    exists_affineCurve_fixedPoint hα hm hC (forcedAffine hα.le u₀ F T)
      (continuous_forcedAffine hα u₀ hF hMF T) haA hT.le hcomb
  refine ⟨T, hT, extendCurve hT.le U, 2 * a + 1, continuous_extendCurve hT.le U, ?_, ?_, ?_, ?_⟩
  · calc extendCurve hT.le U 0 = U (clampT hT.le 0) := rfl
      _ = affineCurveMap hα hm hC (forcedAffine hα.le u₀ F T)
            (continuous_forcedAffine hα u₀ hF hMF T) hT.le U (clampT hT.le 0) := by rw [hfix]
      _ = affineMildMap hα.le hm (forcedAffine hα.le u₀ F T)
            (extendCurve hT.le U) ((clampT hT.le 0 : ℝ)) := rfl
      _ = affineMildMap hα.le hm (forcedAffine hα.le u₀ F T) (extendCurve hT.le U) 0 := by
            rw [clampT_coe hT.le le_rfl hT.le]
      _ = u₀ := by
            show forcedAffine hα.le u₀ F T 0
              - duhamelIntegral hα.le 0 (quadCurve hm (extendCurve hT.le U)) = u₀
            rw [duhamelIntegral, intervalIntegral.integral_same, sub_zero,
              forcedAffine, min_eq_left hT.le, heatFlow1_zero, duhamelIntegral,
              intervalIntegral.integral_same, add_zero]
  · intro t
    exact le_trans (norm_extendCurve_le hT.le U t) hUmem
  · intro t ht
    have h := hcomb t ht
    have hg0 : 0 ≤ duhamelConst α t := duhamelConst_nonneg hα ht.1
    have hq : (0:ℝ) ≤ 4 * Real.pi * C * (2 * a + 1) * (2 * a + 1) * duhamelConst α t := by
      have ha2 : (0:ℝ) ≤ 2 * a + 1 := by linarith
      positivity
    nlinarith [hq]
  · intro t ht
    calc extendCurve hT.le U t = U (clampT hT.le t) := rfl
      _ = affineCurveMap hα hm hC (forcedAffine hα.le u₀ F T)
            (continuous_forcedAffine hα u₀ hF hMF T) hT.le U (clampT hT.le t) := by rw [hfix]
      _ = affineMildMap hα.le hm (forcedAffine hα.le u₀ F T)
            (extendCurve hT.le U) ((clampT hT.le t : ℝ)) := rfl
      _ = affineMildMap hα.le hm (forcedAffine hα.le u₀ F T) (extendCurve hT.le U) t := by
            rw [clampT_coe hT.le ht.1 ht.2]
      _ = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
            - duhamelIntegral hα.le t (quadCurve hm (extendCurve hT.le U)) := by
            show forcedAffine hα.le u₀ F T t
              - duhamelIntegral hα.le t (quadCurve hm (extendCurve hT.le U)) = _
            rw [forcedAffine_eq hα.le u₀ F ht.2]

/-- **Uniqueness for the forced equation.**  Same contraction estimate as in the unforced
case: the forcing sits in the affine part and cancels. -/
theorem forced_mild_solution_unique {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1)
    (F : ℝ → Wiener) {R T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ t ∈ Set.Icc (0:ℝ) T, 8 * Real.pi * C * R * duhamelConst α t ≤ 1 / 2)
    {u v : ℝ → Wiener1} (hu : Continuous u) (hv : Continuous v)
    (hRu : ∀ s, ‖u s‖ ≤ R) (hRv : ∀ s, ‖v s‖ ≤ R)
    (heu : ∀ t ∈ Set.Icc (0:ℝ) T, u t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
      - duhamelIntegral hα.le t (quadCurve hm u))
    (hev : ∀ t ∈ Set.Icc (0:ℝ) T, v t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
      - duhamelIntegral hα.le t (quadCurve hm v)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t :=
  affine_solution_unique hα hm hC (fun t => heatFlow1 α t u₀ + duhamelIntegral hα.le t F)
    hT hsmall hu hv hRu hRv heu hev

/-- **Local existence and uniqueness for the forced mild equation** on one interval.

This is *not* full Hadamard well-posedness: no continuous dependence statement is asserted
here.  Continuous dependence for the forced problem is proved in the curve formulation,
`mild_curve_lipschitz` and `sourceSolution` (`SourceSolution.lean`); the unforced Hadamard
statement is `exists_local_well_posed` (`LocalSolution.lean`).  All of these concern the
**mild** (Duhamel) formulation only, never a classical solution. -/
theorem exists_local_forced_well_posed {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u₀ : Wiener1)
    {F : ℝ → Wiener} (hF : Continuous F) {MF : ℝ} (hMF : ∀ s, ‖F s‖ ≤ MF) :
    ∃ (T : ℝ) (R : ℝ), 0 < T ∧
      (∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧ (∀ t, ‖u t‖ ≤ R) ∧
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm u)) ∧
      (∀ u v : ℝ → Wiener1, Continuous u → Continuous v →
        (∀ s, ‖u s‖ ≤ R) → (∀ s, ‖v s‖ ≤ R) →
        (∀ t ∈ Set.Icc (0:ℝ) T, u t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm u)) →
        (∀ t ∈ Set.Icc (0:ℝ) T, v t = heatFlow1 α t u₀ + duhamelIntegral hα.le t F
          - duhamelIntegral hα.le t (quadCurve hm v)) →
        ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t) := by
  obtain ⟨T, hT, u, R, huc, hu0, hub, hsmall, heq⟩ :=
    exists_local_mild_solution_forced hα hm hC u₀ hF hMF
  exact ⟨T, R, hT, ⟨u, huc, hu0, hub, heq⟩,
    fun w v hw hv hRw hRv hew hev =>
      forced_mild_solution_unique hα hm hC u₀ F hT.le hsmall hw hv hRw hRv hew hev⟩

end LiWang.WienerModel
