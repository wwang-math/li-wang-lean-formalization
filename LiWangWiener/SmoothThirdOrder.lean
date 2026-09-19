/-
# Smooth profiles have a `wt³`-weighted `ℓ¹` bound

The `s = 3` paper energy package needs one more weight on the **source** than v8.0 established:
`WB 3`, not just `WB 2`.  No new integration-by-parts estimate is required.  The observation is
that two more derivatives buy exactly one factor of `ρ(k) = 1 + k₀² + k₁²`, and `wt² ≤ 3ρ`:

```
    wt(k)³ |â(k)|  ≤  3 · wt(k) (1 + k₀² + k₁²) |â(k)|
                    =  3 [ wt|â| + wt k₀²|â| + wt k₁²|â| ] ,
```

and `k₀² |â(k)| = (4π²)^{-1} |(pd0² a)^(k)|`, so each of the three families is the existing
`summable_wt_norm_pcoeff` applied to `G`, `pd0² G` and `pd1² G`.

Part of `LiWangWienerPaperMapAlignmentPacket` v9.0.
-/
import LiWangWiener.SmoothHigherBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.WienerModel

variable {T : ℝ}

/-! ## 1. Two derivatives buy one power of the frequency squared -/

theorem norm_pcoeff_pd0_two {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    ‖pcoeff (pd0 (pd0 G)) k‖ = 4 * Real.pi ^ 2 * ((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff G k‖ := by
  rw [pcoeff_pd0_two h k, norm_mul, norm_twoPiI_pow_two]
  have e : (2 * Real.pi * |((k 0 : ℤ) : ℝ)|) ^ 2
      = 4 * Real.pi ^ 2 * ((k 0 : ℤ) : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [e]

theorem norm_pcoeff_pd1_two {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) (k : Gam) :
    ‖pcoeff (pd1 (pd1 G)) k‖ = 4 * Real.pi ^ 2 * ((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff G k‖ := by
  rw [pcoeff_pd1_two h k, norm_mul, norm_twoPiI_pow_two]
  have e : (2 * Real.pi * |((k 1 : ℤ) : ℝ)|) ^ 2
      = 4 * Real.pi ^ 2 * ((k 1 : ℤ) : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [e]

theorem summable_wt_mul_sq0_pcoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    Summable fun k : Gam => wt k * (((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff G k‖) := by
  have hs := (summable_wt_norm_pcoeff (h.pd0'.pd0')).mul_left (1 / (4 * Real.pi ^ 2))
  refine hs.congr (fun k => ?_)
  rw [norm_pcoeff_pd0_two h k]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem summable_wt_mul_sq1_pcoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    Summable fun k : Gam => wt k * (((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff G k‖) := by
  have hs := (summable_wt_norm_pcoeff (h.pd1'.pd1')).mul_left (1 / (4 * Real.pi ^ 2))
  refine hs.congr (fun k => ?_)
  rw [norm_pcoeff_pd1_two h k]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## 2. The `wt³` bound -/

/-- **The third-order weighted coefficient sum of a smooth doubly periodic function converges.**
Proved from the existing first-order estimate applied to `G`, `∂₀²G` and `∂₁²G`. -/
theorem summable_wt_cube_norm_pcoeff {G : ℝ × ℝ → ℂ} (h : IsSmoothPeriodic G) :
    Summable fun k : Gam => wt k ^ 3 * ‖pcoeff G k‖ := by
  have h0 := summable_wt_norm_pcoeff h
  have h1 := summable_wt_mul_sq0_pcoeff h
  have h2 := summable_wt_mul_sq1_pcoeff h
  have hmaj := ((h0.add h1).add h2).mul_left 3
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmaj
  · have := (wt_pos k).le; positivity
  · have hwt : (0:ℝ) < wt k := wt_pos k
    have hn : (0:ℝ) ≤ ‖pcoeff G k‖ := norm_nonneg _
    have hsq : wt k ^ 2 ≤ 3 * rho k := wt_sq_le_three_rho k
    have hrho : rho k = 1 + ((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2 := rho_eq k
    have hstep : wt k ^ 3 * ‖pcoeff G k‖
        ≤ (wt k * (3 * rho k)) * ‖pcoeff G k‖ := by
      have hcube : wt k ^ 3 ≤ wt k * (3 * rho k) := by
        have he : wt k ^ 3 = wt k * wt k ^ 2 := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_left hsq hwt.le
      exact mul_le_mul_of_nonneg_right hcube hn
    refine le_trans hstep (le_of_eq ?_)
    rw [hrho]; ring

/-- The same bound for a smooth element of the Wiener algebra. -/
theorem summable_wt3_norm_of_smoothWiener {a : Wiener} (h : SmoothWiener a) :
    Summable fun k : Gam => wt k ^ 3 * ‖a k‖ := by
  have hper : IsSmoothPeriodic (planeLift a) := isSmoothPeriodic_planeLift h
  have hcoe : ∀ k : Gam, a k = pcoeff (planeLift a) k := by
    intro k
    have hw : wienerOfSmooth (planeLift a) hper = a := wienerOfSmooth_planeLift h
    calc a k = (wienerOfSmooth (planeLift a) hper) k := by rw [hw]
      _ = pcoeff (planeLift a) k := rfl
  exact (summable_wt_cube_norm_pcoeff hper).congr (fun k => by rw [hcoe k])

/-- **The `WB 3` bound of a smooth Wiener element**, with an explicit nonnegative constant. -/
theorem exists_WB_three_of_smoothWiener {a : Wiener} (h : SmoothWiener a) :
    ∃ S : ℝ, 0 ≤ S ∧ WB 3 S (fun k => a k) := by
  have hs := summable_wt3_norm_of_smoothWiener h
  refine ⟨∑' k : Gam, wt k ^ 3 * ‖a k‖, tsum_nonneg (fun k => ?_), WB.of_summable hs le_rfl⟩
  have := (wt_pos k).le; positivity

/-! ## 3. The third-order source bound -/

/-- The source hypothesis of the `s = 3` package: uniform `wt¹`, `wt²` **and** `wt³` bounds on
the instantaneous Fourier data. -/
def HasHigherBound3 (hT : 0 ≤ T) (f : Curve0 T) : Prop :=
  ∃ S : ℝ, 0 ≤ S ∧ (∀ s : ℝ, WB 1 S (fun k => (sourceFun hT f s) k))
    ∧ (∀ s : ℝ, WB 2 S (fun k => (sourceFun hT f s) k))
    ∧ (∀ s : ℝ, WB 3 S (fun k => (sourceFun hT f s) k))

theorem HasHigherBound3.toHasHigherBound {hT : 0 ≤ T} {f : Curve0 T}
    (h : HasHigherBound3 hT f) : HasHigherBound hT f := by
  obtain ⟨S, hS0, h1, h2, -⟩ := h
  exact ⟨S, hS0, h1, h2⟩

theorem HasHigherBound3.add {hT : 0 ≤ T} {f g : Curve0 T} (hf : HasHigherBound3 hT f)
    (hg : HasHigherBound3 hT g) : HasHigherBound3 hT (f + g) := by
  obtain ⟨S₁, hS₁0, h₁a, h₁b, h₁c⟩ := hf
  obtain ⟨S₂, hS₂0, h₂a, h₂b, h₂c⟩ := hg
  refine ⟨S₁ + S₂, by linarith, fun s => ?_, fun s => ?_, fun s => ?_⟩
  · exact (WB.add (h₁a s) (h₂a s)).of_norm_le (fun k => le_of_eq (by rfl))
  · exact (WB.add (h₁b s) (h₂b s)).of_norm_le (fun k => le_of_eq (by rfl))
  · exact (WB.add (h₁c s) (h₂c s)).of_norm_le (fun k => le_of_eq (by rfl))

theorem HasHigherBound3.smul {hT : 0 ≤ T} {f : Curve0 T} (c : ℝ)
    (hf : HasHigherBound3 hT f) : HasHigherBound3 hT (c • f) := by
  obtain ⟨S, hS0, ha, hb, hc⟩ := hf
  have hstep : ∀ k : Gam, ∀ s : ℝ,
      ‖(sourceFun hT (c • f) s) k‖ ≤ |c| * ‖(sourceFun hT f s) k‖ := by
    intro k s
    show ‖(c : ℂ) • (sourceFun hT f s) k‖ ≤ |c| * ‖(sourceFun hT f s) k‖
    rw [norm_smul]
    simp
  refine ⟨|c| * S, by positivity, fun s => ?_, fun s => ?_, fun s => ?_⟩
  · exact WB.of_norm_le_mul (abs_nonneg c) (ha s) (fun k => hstep k s)
  · exact WB.of_norm_le_mul (abs_nonneg c) (hb s) (fun k => hstep k s)
  · exact WB.of_norm_le_mul (abs_nonneg c) (hc s) (fun k => hstep k s)

theorem hasHigherBound3_zero (hT : 0 ≤ T) : HasHigherBound3 hT (0 : Curve0 T) := by
  refine ⟨0, le_rfl, fun s => ?_, fun s => ?_, fun s => ?_⟩ <;>
  · intro F
    have h0 : ∀ k : Gam, (sourceFun hT (0 : Curve0 T) s) k = 0 := by
      intro k; rw [sourceFun_zero' hT s]; rfl
    refine le_of_eq (Finset.sum_eq_zero (fun k _ => ?_))
    simp only [h0 k, norm_zero, mul_zero]

theorem hasHigherBound3_productSource (hT : 0 ≤ T) {a : RealWiener} (ha : SmoothWiener a.val)
    {χ : ℝ → ℝ} (hχ : Continuous χ) : HasHigherBound3 hT (productSource hT a hχ) := by
  obtain ⟨S, hS0, hS⟩ := exists_WB_three_of_smoothWiener ha
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
  refine ⟨B' * S, mul_nonneg hB'0 hS0, fun s => ?_, fun s => ?_, fun s => ?_⟩
  · exact WB.of_norm_le_mul hB'0 (hS.mono_exp (by norm_num)) (hkey s)
  · exact WB.of_norm_le_mul hB'0 (hS.mono_exp (by norm_num)) (hkey s)
  · exact WB.of_norm_le_mul hB'0 hS (hkey s)

theorem hasHigherBound3_smoothSourceGens (hT : 0 < T) (W : Set Torus2) {V : Curve0 T}
    (hV : V ∈ smoothSourceGens hT W) : HasHigherBound3 hT.le V := by
  obtain ⟨a, χ, hχ, ha, -, rfl⟩ := hV
  exact hasHigherBound3_productSource hT.le ha.1 hχ

/-- **Every smooth source carries the third-order bound too.** -/
theorem hasHigherBound3_of_mem_smoothSources (hT : 0 < T) (W : Set Torus2) {V : Curve0 T}
    (hV : V ∈ smoothSources hT W) : HasHigherBound3 hT.le V := by
  refine Submodule.span_induction (p := fun x _ => HasHigherBound3 hT.le x)
    (fun x hx => hasHigherBound3_smoothSourceGens hT W hx) (hasHigherBound3_zero hT.le)
    (fun x y _ _ hx hy => hx.add hy) (fun c x _ hx => hx.smul c) hV

end LiWang.WienerModel
