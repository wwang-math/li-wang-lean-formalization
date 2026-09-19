/-
**Smooth sources satisfy the higher-weight bound.**

The last forward-theory input of the v8.0 Sobolev bridge is the hypothesis
`HasHigherBound`: a source curve whose instantaneous Fourier data carries uniform `wt`- and
`wt²`-weighted `ℓ¹` bounds.  This module *proves* that hypothesis for every element of the
smooth source space `smoothSources hT W` that the recovery theorem actually uses, so that the
Sobolev existence statement is discharged rather than assumed.

The route is the packet's own fourth-order coefficient decay: a smooth doubly periodic
function has `‖pcoeff G k‖ ≤ C · b₄(k₀) b₄(k₁)` with `b₄(n) = (2π|n|)^{-4}`, while
`wt k ≤ (1+|k₀|)(1+|k₁|)`; the elementary estimate `(1+|n|)² b₄(n) ≤ 4 b₂(n)` then makes
`k ↦ wt k ² ‖a k‖` summable by the product criterion.

Part of `LiWangFormalizationSobolevCompatibilityPacket` v8.0.
-/
import LiWangFormalization.SobolevExample
import LiWangFormalization.SmoothFirstOrder
import LiWangFormalization.SmoothSpacetimeSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.Formalization

variable {T : ℝ}

/-! ## 1. A second-order weighted decay estimate -/

/-- **The quadratic weight is absorbed by the fourth-order decay.**  This is the only new
arithmetic input: `(1+|n|)² b₄(n) ≤ 4 b₂(n)`, where `b₂` is already known to be summable. -/
theorem weighted_sq_decayWeight4_le (n : ℤ) :
    (1 + |(n : ℝ)|) ^ 2 * decayWeight4 n ≤ 4 * decayWeight n := by
  by_cases hn : n = 0
  · subst hn
    rw [decayWeight4_zero, decayWeight_zero]
    norm_num
  · rw [decayWeight4_of_ne hn, decayWeight_of_ne hn]
    set A : ℝ := (2 * Real.pi * |(n : ℝ)|) ^ 2 with hA
    have hApos : (0:ℝ) < A := twoPiI_pow_two_pos hn
    have habs : (1:ℝ) ≤ |(n : ℝ)| := one_le_abs_intCast hn
    have hpi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
    have hAt : |(n : ℝ)| ^ 2 ≤ A := by
      have hle : |(n : ℝ)| ≤ 2 * Real.pi * |(n : ℝ)| := by
        nlinarith [abs_nonneg ((n : ℝ))]
      rw [hA]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    have hkey : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * A := by nlinarith [abs_nonneg ((n : ℝ))]
    calc (1 + |(n : ℝ)|) ^ 2 * (1 / A ^ 2) ≤ (4 * A) * (1 / A ^ 2) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 4 * (1 / A) := by field_simp
      _ = 4 * (1 / A) := rfl

theorem weighted_sq_decayWeight4_nonneg (n : ℤ) :
    0 ≤ (1 + |(n : ℝ)|) ^ 2 * decayWeight4 n :=
  mul_nonneg (by positivity) (decayWeight4_pos n).le

/-- The quadratically weighted fourth-order decay is summable on `ℤ`. -/
theorem summable_weighted_sq_decayWeight4 :
    Summable fun n : ℤ => (1 + |(n : ℝ)|) ^ 2 * decayWeight4 n :=
  Summable.of_nonneg_of_le weighted_sq_decayWeight4_nonneg weighted_sq_decayWeight4_le
    (summable_decayWeight.mul_left 4)

/-! ## 2. Smooth Wiener elements have a `wt²`-weighted `ℓ¹` bound -/

/-- **Smoothness gives the `wt²` bound.**  The Fourier coefficients of a smooth doubly
periodic function are summable even after multiplication by `wt²`. -/
theorem summable_wtsq_norm_of_smoothWiener {a : Wiener} (h : SmoothWiener a) :
    Summable fun k : Gam => wt k ^ 2 * ‖a k‖ := by
  have hper : IsSmoothPeriodic (planeLift a) := isSmoothPeriodic_planeLift h
  have hcoe : ∀ k : Gam, a k = pcoeff (planeLift a) k := by
    intro k
    have hw : wienerOfSmooth (planeLift a) hper = a := wienerOfSmooth_planeLift h
    calc a k = (wienerOfSmooth (planeLift a) hper) k := by rw [hw]
      _ = pcoeff (planeLift a) k := rfl
  obtain ⟨C, hC, hbd⟩ := exists_pcoeff_decay4 hper
  have hmaj : Summable fun k : Gam =>
      (C * ((1 + |((k 0 : ℤ) : ℝ)|) ^ 2 * decayWeight4 (k 0)))
        * ((1 + |((k 1 : ℤ) : ℝ)|) ^ 2 * decayWeight4 (k 1)) :=
    summable_gam_of_prod (f := fun n : ℤ => C * ((1 + |(n : ℝ)|) ^ 2 * decayWeight4 n))
      (g := fun n : ℤ => (1 + |(n : ℝ)|) ^ 2 * decayWeight4 n)
      (summable_weighted_sq_decayWeight4.mul_left C) summable_weighted_sq_decayWeight4
      (fun n => mul_nonneg hC (weighted_sq_decayWeight4_nonneg n))
      (fun n => weighted_sq_decayWeight4_nonneg n)
  refine Summable.of_nonneg_of_le (fun k => by have := (wt_pos k).le; positivity) ?_ hmaj
  intro k
  have hw : wt k ≤ (1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|) := wt_le_prod k
  have hw0 : (0:ℝ) ≤ wt k := (wt_pos k).le
  have hp0 : (0:ℝ) ≤ (1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|) := by positivity
  have hwsq : wt k ^ 2 ≤ ((1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|)) ^ 2 :=
    pow_le_pow_left₀ hw0 hw 2
  have hnorm : ‖a k‖ ≤ C * (decayWeight4 (k 0) * decayWeight4 (k 1)) := by
    rw [hcoe k]; exact hbd k
  have hd0 : (0:ℝ) ≤ decayWeight4 (k 0) := (decayWeight4_pos _).le
  have hd1 : (0:ℝ) ≤ decayWeight4 (k 1) := (decayWeight4_pos _).le
  calc wt k ^ 2 * ‖a k‖
      ≤ ((1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|)) ^ 2
          * (C * (decayWeight4 (k 0) * decayWeight4 (k 1))) := by
        refine mul_le_mul hwsq hnorm (norm_nonneg _) (by positivity)
    _ = (C * ((1 + |((k 0 : ℤ) : ℝ)|) ^ 2 * decayWeight4 (k 0)))
          * ((1 + |((k 1 : ℤ) : ℝ)|) ^ 2 * decayWeight4 (k 1)) := by ring

/-- **The `WB 2` bound of a smooth Wiener element**, with an explicit nonnegative constant. -/
theorem exists_WB_two_of_smoothWiener {a : Wiener} (h : SmoothWiener a) :
    ∃ S : ℝ, 0 ≤ S ∧ WB 2 S (fun k => a k) := by
  have hs := summable_wtsq_norm_of_smoothWiener h
  refine ⟨∑' k : Gam, wt k ^ 2 * ‖a k‖, tsum_nonneg (fun k => ?_), WB.of_summable hs le_rfl⟩
  have := (wt_pos k).le; positivity

/-! ## 3. `HasHigherBound` for smooth sources -/

theorem hasHigherBound_zero (hT : 0 ≤ T) : HasHigherBound hT (0 : Curve0 T) := by
  refine ⟨0, le_rfl, fun s => ?_, fun s => ?_⟩ <;>
  · intro F
    have h0 : ∀ k : Gam, (sourceFun hT (0 : Curve0 T) s) k = 0 := by
      intro k; rw [sourceFun_zero' hT s]; rfl
    refine le_of_eq ?_
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp only [h0 k, norm_zero, mul_zero]

/-- **A smooth spatial profile times a continuous time profile has the higher-weight bound.**
The time factor only needs to be continuous: it is evaluated at clamped times, hence on the
compact interval `[0,T]`. -/
theorem hasHigherBound_productSource (hT : 0 ≤ T) {a : RealWiener} (ha : SmoothWiener a.val)
    {χ : ℝ → ℝ} (hχ : Continuous χ) : HasHigherBound hT (productSource hT a hχ) := by
  obtain ⟨S, hS0, hS⟩ := exists_WB_two_of_smoothWiener ha
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
    hχ.continuousOn
  set B' : ℝ := max B 0 with hB'
  have hB'0 : (0:ℝ) ≤ B' := le_max_right _ _
  have hkey : ∀ (s : ℝ) (k : Gam),
      ‖(sourceFun hT (productSource hT a hχ) s) k‖ ≤ B' * ‖a.val k‖ := by
    intro s k
    have hmem : ((clampT hT s : TimeI T) : ℝ) ∈ Set.Icc (0:ℝ) T := (clampT hT s).2
    have hbound : |χ ((clampT hT s : TimeI T) : ℝ)| ≤ B' :=
      le_trans (by simpa [Real.norm_eq_abs] using hB _ hmem) (le_max_left _ _)
    have hval : (sourceFun hT (productSource hT a hχ) s) k
        = ((χ ((clampT hT s : TimeI T) : ℝ) : ℝ) : ℂ) • (a.val k) := by
      rw [sourceFun_productSource hT a hχ s, smul_real_wiener]; rfl
    rw [hval, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simpa using hbound
  refine ⟨B' * S, mul_nonneg hB'0 hS0, fun s => ?_, fun s => ?_⟩
  · exact WB.of_norm_le_mul hB'0 (hS.mono_exp (by norm_num)) (hkey s)
  · exact WB.of_norm_le_mul hB'0 hS (hkey s)

theorem hasHigherBound_smoothSourceGens (hT : 0 < T) (W : Set Torus2) {V : Curve0 T}
    (hV : V ∈ smoothSourceGens hT W) : HasHigherBound hT.le V := by
  obtain ⟨a, χ, hχ, ha, -, rfl⟩ := hV
  exact hasHigherBound_productSource hT.le ha.1 hχ

/-- **Every smooth source satisfies the higher-weight bound.**  This discharges the only
forward-theory hypothesis of the Sobolev existence theorem on the source space the recovery
theorem actually uses. -/
theorem hasHigherBound_of_mem_smoothSources (hT : 0 < T) (W : Set Torus2) {V : Curve0 T}
    (hV : V ∈ smoothSources hT W) : HasHigherBound hT.le V := by
  refine Submodule.span_induction (p := fun x _ => HasHigherBound hT.le x)
    (fun x hx => hasHigherBound_smoothSourceGens hT W hx) (hasHigherBound_zero hT.le)
    (fun x y _ _ hx hy => hx.add hy) (fun c x _ hx => hx.smul c) hV

/-! ## 4. Unconditional Sobolev existence on the smooth source space -/

variable {α : ℝ} {m : Fin 2 → Gam → ℂ}

/-- **Sobolev existence on `smoothSources hT W` is proved, not assumed.**  For a small enough
uniform positive smallness radius (explicit absorption constants, existential neighbourhood
components), every smooth source admits an `L²(𝕋²)`-valued Sobolev solution with
a finite `H³` bound. -/
theorem exists_sobolevExistence_smoothSources (hα : 1 / 2 < α) (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (W : Set Torus2) :
    ∃ ε > 0, SobolevExistence hα hT.le hm (smoothSources hT W) ε :=
  exists_sobolevExistence_of_higherBound hα hT.le hm hr hC (smoothSources hT W)
    (fun _ hf => hasHigherBound_of_mem_smoothSources hT W hf)

/-- **The recovery theorem with the Sobolev existence hypotheses discharged.**  What remains
is exactly the portable analytic input (`FractionalUCP`) and the measurement hypothesis
`SobolevObsAgreeOn`, stated on the paper's `L²(𝕋²)`-valued solutions. -/
theorem paper_exterior_velocity_eq_sobolev_smooth (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖rotatedGradientSymbol κ₁ j k‖ ≤ C₁)
    (hC₂ : ∀ j k, ‖rotatedGradientSymbol κ₂ j k‖ ≤ C₂)
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε)
    (ψ : Wiener1) (j : Fin 2) {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    synth (velocity (rotatedGradientSymbol κ₁) hm₁ j (incl ψ)) x
      = synth (velocity (rotatedGradientSymbol κ₂) hm₂ j (incl ψ)) x :=
  paper_exterior_velocity_eq_sobolev hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hC hτ0 hτT
    (exists_sobolevExistence_smoothSources hα hT hm₁ hr₁ hC₁ W)
    (exists_sobolevExistence_smoothSources hα hT hm₂ hr₂ hC₂ W) hobs ψ j hx

/-- **The Sobolev solution class is inhabited over the class the recovery theorem uses.**  For a
nonempty open `W` there is a **nonzero** smooth source in `smoothSources hT W` admitting a
Sobolev solution.  (The explicitly nonzero *state* is the constructed `meanSolution` of
`SobolevExample`, whose source is spatially constant and therefore not localized in `W`.) -/
theorem exists_nonzero_smoothSource_sobolevSolution (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (f : Curve0 T) (M : ℝ) (θ : ℝ → TorusL2),
      f ∈ smoothSources hT W ∧ f ≠ 0 ∧ IsSobolevSolution hα hT.le hm M f θ := by
  obtain ⟨ε, hε0, hex⟩ := exists_sobolevExistence_smoothSources hα hT hm hr hC W
  obtain ⟨V, hV, hV0, -⟩ := exists_nonzero_smoothSource hT hW hne
  have hVn : (0:ℝ) < ‖V‖ := norm_pos_iff.2 hV0
  set c : ℝ := ε / (2 * ‖V‖) with hc
  have hc0 : (0:ℝ) < c := by rw [hc]; positivity
  have hnorm : ‖c • V‖ = ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0, hc]
    field_simp
  have hsmall : ‖c • V‖ < ε := by rw [hnorm]; linarith
  have hne0 : c • V ≠ 0 := by
    refine norm_ne_zero_iff.1 ?_
    rw [hnorm]; positivity
  obtain ⟨M, θ, hsol⟩ := hex (c • V) (Submodule.smul_mem _ c hV) hsmall
  exact ⟨c • V, M, θ, Submodule.smul_mem _ c hV, hne0, hsol⟩

end LiWang.Formalization
