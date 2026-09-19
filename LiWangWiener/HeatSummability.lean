/-
# Summability of the positive-time heat kernel against polynomial weights

The `heatSmooth` estimate of `FractionalHeat` bounds `wt k · e^{-t λ_k}` by a *constant*,
which suffices when the datum is already in `ℓ¹`.  For the duality argument of
`TerminalControl` the datum is only in `ℓ²`, so the bound `‖y k‖ ≤ ‖y‖` must be combined
with genuine **summability** of the heat factor itself.  This module proves

* `pow_mul_exp_neg_le` — `uⁿ e^{-cu} ≤ (n/c + 1)ⁿ` for `u ≥ 0`, `c > 0`;
* `summable_int_exp_decay` — `Summable (n : ℤ) ↦ (1+|n|) e^{-c|n|}`;
* `summable_gam_wt_frac_heat` — `Summable (k : Γ) ↦ wt k (1 + λ_k) e^{-r λ_k}` for `r > 0`,
  the master estimate, and its three corollaries used later.

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.FractionalHeat
import LiWangWiener.SmoothPeriodic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## 1. Polynomial times decaying exponential -/

/-- `uⁿ e^{-cu} ≤ (n/c + 1)ⁿ` for `u ≥ 0` and `c > 0`. -/
theorem pow_mul_exp_neg_le (n : ℕ) {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    u ^ n * Real.exp (-(c * u)) ≤ ((n : ℝ) / c + 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, one_mul, pow_zero, Real.exp_le_one_iff]
    have : 0 ≤ c * u := mul_nonneg hc.le hu
    linarith
  · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hne : ((n:ℝ)) ≠ 0 := ne_of_gt hn0
    have hx : 0 ≤ (c / (n:ℝ)) * u := by positivity
    have h1 := mul_exp_neg_le_one hx
    have key : u * Real.exp (-((c / (n:ℝ)) * u)) ≤ (n:ℝ) / c := by
      have hrw : u * Real.exp (-((c / (n:ℝ)) * u))
          = ((n:ℝ)/c) * (((c / (n:ℝ)) * u) * Real.exp (-((c / (n:ℝ)) * u))) := by
        field_simp
      rw [hrw]
      calc ((n:ℝ)/c) * (((c / (n:ℝ)) * u) * Real.exp (-((c / (n:ℝ)) * u)))
          ≤ ((n:ℝ)/c) * 1 := by
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (n:ℝ)/c := mul_one _
    have hpow : (Real.exp (-((c / (n:ℝ)) * u))) ^ n = Real.exp (-(c * u)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    calc u ^ n * Real.exp (-(c * u))
        = (u * Real.exp (-((c / (n:ℝ)) * u))) ^ n := by rw [mul_pow, hpow]
      _ ≤ ((n:ℝ)/c) ^ n := pow_le_pow_left₀ (by positivity) key n
      _ ≤ ((n:ℝ)/c + 1) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n

/-! ## 2. Summability on the integer lattice -/

/-- `Summable (n : ℤ) ↦ (1 + |n|) e^{-c|n|}` for every `c > 0`. -/
theorem summable_int_exp_decay {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => (1 + |((n : ℤ) : ℝ)|) * Real.exp (-(c * |((n : ℤ) : ℝ)|))) := by
  set M : ℝ := 1 + (2 * Real.pi) ^ 2 * (((2:ℝ)/c + 1) ^ 2 + ((3:ℝ)/c + 1) ^ 3) with hM
  have hM1 : (1:ℝ) ≤ M := by
    have : 0 ≤ (2 * Real.pi) ^ 2 * (((2:ℝ)/c + 1) ^ 2 + ((3:ℝ)/c + 1) ^ 3) := by positivity
    rw [hM]; linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_decayWeight.mul_left M)
  by_cases hn : n = 0
  · subst hn
    rw [decayWeight_zero, mul_one]
    have h0 : (1 + |((0 : ℤ) : ℝ)|) * Real.exp (-(c * |((0 : ℤ) : ℝ)|)) = 1 := by norm_num
    rw [h0]; exact hM1
  · rw [decayWeight_of_ne hn]
    set u : ℝ := |((n : ℤ) : ℝ)| with hu
    have hu0 : 0 < u := abs_pos.mpr (by exact_mod_cast hn)
    have hbase : (2 * Real.pi * u) ^ 2 = (2 * Real.pi) ^ 2 * u ^ 2 := by ring
    rw [hbase]
    have hden : (0:ℝ) < (2 * Real.pi) ^ 2 * u ^ 2 := by positivity
    rw [mul_one_div, le_div_iff₀ hden]
    have h2 := pow_mul_exp_neg_le 2 hc hu0.le
    have h3 := pow_mul_exp_neg_le 3 hc hu0.le
    have hsplit : (1 + u) * Real.exp (-(c * u)) * ((2 * Real.pi) ^ 2 * u ^ 2)
        = (2 * Real.pi) ^ 2 * (u ^ 2 * Real.exp (-(c * u)) + u ^ 3 * Real.exp (-(c * u))) := by
      ring
    rw [hsplit]
    have hpi : (0:ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
    have hsum : u ^ 2 * Real.exp (-(c * u)) + u ^ 3 * Real.exp (-(c * u))
        ≤ ((2:ℝ)/c + 1) ^ 2 + ((3:ℝ)/c + 1) ^ 3 := by
      have e2 : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
      have e3 : ((3:ℕ):ℝ) = (3:ℝ) := by norm_num
      rw [e2] at h2; rw [e3] at h3
      linarith
    calc (2 * Real.pi) ^ 2 * (u ^ 2 * Real.exp (-(c * u)) + u ^ 3 * Real.exp (-(c * u)))
        ≤ (2 * Real.pi) ^ 2 * (((2:ℝ)/c + 1) ^ 2 + ((3:ℝ)/c + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left hsum hpi
      _ ≤ M := by rw [hM]; linarith

/-! ## 3. The master estimate on the frequency lattice -/

/-- `λ_k e^{-(r/2) λ_k} ≤ 2/r`. -/
theorem fracSymbol_mul_exp_le {α r : ℝ} (hr : 0 < r) (k : Gam) :
    fracSymbol α k * Real.exp (-((r / 2) * fracSymbol α k)) ≤ 2 / r := by
  have hx : 0 ≤ (r / 2) * fracSymbol α k := mul_nonneg (by linarith) (fracSymbol_nonneg α k)
  have h1 := mul_exp_neg_le_one hx
  have hrw : fracSymbol α k * Real.exp (-((r / 2) * fracSymbol α k))
      = (2 / r) * (((r / 2) * fracSymbol α k) * Real.exp (-((r / 2) * fracSymbol α k))) := by
    field_simp
  rw [hrw]
  calc (2 / r) * (((r / 2) * fracSymbol α k) * Real.exp (-((r / 2) * fracSymbol α k)))
      ≤ (2 / r) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 / r := mul_one _

/-- **The master summability estimate.**  For every positive time the heat factor beats the
first-order weight *and* one power of the fractional symbol. -/
theorem summable_gam_wt_frac_heat {α r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) :
    Summable (fun k : Gam =>
      (wt k * (1 + fracSymbol α k)) * Real.exp (-(r * fracSymbol α k))) := by
  set c : ℝ := Real.pi * r / 2 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set F : ℤ → ℝ := fun n => (1 + 2 / r) * ((1 + |((n : ℤ) : ℝ)|) * Real.exp (-(c * |((n : ℤ) : ℝ)|)))
    with hF
  set G : ℤ → ℝ := fun n => (1 + |((n : ℤ) : ℝ)|) * Real.exp (-(c * |((n : ℤ) : ℝ)|)) with hG
  have hFs : Summable F := (summable_int_exp_decay hc0).mul_left _
  have hGs : Summable G := summable_int_exp_decay hc0
  have hF0 : ∀ n, 0 ≤ F n := by
    intro n; rw [hF]
    have : (0:ℝ) ≤ 1 + 2 / r := by positivity
    positivity
  have hG0 : ∀ n, 0 ≤ G n := by intro n; rw [hG]; positivity
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (summable_gam_of_prod hFs hGs hF0 hG0)
  · have := wt_pos k
    have := fracSymbol_nonneg α k
    positivity
  · -- the pointwise bound
    set lam : ℝ := fracSymbol α k with hlam
    have hlam0 : 0 ≤ lam := fracSymbol_nonneg α k
    set p : ℝ := |((k 0 : ℤ) : ℝ)| with hp
    set q : ℝ := |((k 1 : ℤ) : ℝ)| with hq
    have hp0 : 0 ≤ p := abs_nonneg _
    have hq0 : 0 ≤ q := abs_nonneg _
    have hwt : wt k = 1 + p + q := by simp only [hp, hq, wt]
    have hlow : Real.pi * (p + q) ≤ lam := by
      simp only [hp, hq, hlam]
      exact pi_l1_le_fracSymbol hα k
    -- split the exponential
    have hesplit : Real.exp (-(r * lam))
        = Real.exp (-((r / 2) * lam)) * Real.exp (-((r / 2) * lam)) := by
      rw [← Real.exp_add]; congr 1; ring
    -- the first half absorbs `1 + λ`
    have hfirst : (1 + lam) * Real.exp (-((r / 2) * lam)) ≤ 1 + 2 / r := by
      have h1 : Real.exp (-((r / 2) * lam)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (r / 2) * lam := mul_nonneg (by linarith) hlam0
        linarith
      have h2 := fracSymbol_mul_exp_le (α := α) hr k
      rw [← hlam] at h2
      nlinarith [Real.exp_pos (-((r / 2) * lam))]
    -- the second half decays in the ℓ¹ frequency
    have hsecond : Real.exp (-((r / 2) * lam))
        ≤ Real.exp (-(c * p)) * Real.exp (-(c * q)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hcc : -(c * p) + -(c * q) = -((Real.pi * r / 2) * (p + q)) := by rw [hc]; ring
      rw [hcc]
      have hr2 : 0 < r / 2 := by linarith
      nlinarith
    have hwtle : wt k ≤ (1 + p) * (1 + q) := by rw [hwt]; nlinarith
    -- assemble
    have hmain : (wt k * (1 + lam)) * Real.exp (-(r * lam))
        ≤ ((1 + p) * (1 + q)) * ((1 + 2 / r) * (Real.exp (-(c * p)) * Real.exp (-(c * q)))) := by
      rw [hesplit]
      have hA : (wt k * (1 + lam)) * (Real.exp (-((r / 2) * lam)) * Real.exp (-((r / 2) * lam)))
          = (wt k * Real.exp (-((r / 2) * lam)))
            * ((1 + lam) * Real.exp (-((r / 2) * lam))) := by ring
      rw [hA]
      have hB : wt k * Real.exp (-((r / 2) * lam))
          ≤ ((1 + p) * (1 + q)) * (Real.exp (-(c * p)) * Real.exp (-(c * q))) := by
        have := mul_le_mul hwtle hsecond (Real.exp_pos _).le
          (by nlinarith : (0:ℝ) ≤ (1 + p) * (1 + q))
        exact this
      have hnn1 : (0:ℝ) ≤ (1 + lam) * Real.exp (-((r / 2) * lam)) := by positivity
      have hnn2 : (0:ℝ) ≤ ((1 + p) * (1 + q)) * (Real.exp (-(c * p)) * Real.exp (-(c * q))) := by
        positivity
      calc (wt k * Real.exp (-((r / 2) * lam))) * ((1 + lam) * Real.exp (-((r / 2) * lam)))
          ≤ (((1 + p) * (1 + q)) * (Real.exp (-(c * p)) * Real.exp (-(c * q))))
              * ((1 + lam) * Real.exp (-((r / 2) * lam))) :=
            mul_le_mul_of_nonneg_right hB hnn1
        _ ≤ (((1 + p) * (1 + q)) * (Real.exp (-(c * p)) * Real.exp (-(c * q))))
              * (1 + 2 / r) := mul_le_mul_of_nonneg_left hfirst hnn2
        _ = ((1 + p) * (1 + q)) * ((1 + 2 / r) * (Real.exp (-(c * p)) * Real.exp (-(c * q)))) := by
            ring
    have hgoal : F (k 0) * G (k 1)
        = ((1 + p) * (1 + q)) * ((1 + 2 / r) * (Real.exp (-(c * p)) * Real.exp (-(c * q)))) := by
      show ((1 + 2 / r) * ((1 + |((k 0 : ℤ) : ℝ)|) * Real.exp (-(c * |((k 0 : ℤ) : ℝ)|))))
          * ((1 + |((k 1 : ℤ) : ℝ)|) * Real.exp (-(c * |((k 1 : ℤ) : ℝ)|))) = _
      rw [← hp, ← hq]; ring
    rw [hgoal]
    exact hmain

/-! ## 4. The three corollaries used in the duality argument -/

theorem summable_gam_heat {α r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) :
    Summable (fun k : Gam => Real.exp (-(r * fracSymbol α k))) := by
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (summable_gam_wt_frac_heat hα hr)
  have h1 : (1:ℝ) ≤ wt k * (1 + fracSymbol α k) := by
    have := one_le_wt k
    have := fracSymbol_nonneg α k
    nlinarith
  nlinarith [Real.exp_pos (-(r * fracSymbol α k))]

theorem summable_gam_wt_heat {α r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) :
    Summable (fun k : Gam => wt k * Real.exp (-(r * fracSymbol α k))) := by
  refine Summable.of_nonneg_of_le (fun k => by
      have := (wt_pos k).le; positivity) (fun k => ?_) (summable_gam_wt_frac_heat hα hr)
  have h1 : wt k ≤ wt k * (1 + fracSymbol α k) := by
    have := (wt_pos k).le
    have := fracSymbol_nonneg α k
    nlinarith
  nlinarith [Real.exp_pos (-(r * fracSymbol α k))]

theorem summable_gam_frac_heat {α r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) :
    Summable (fun k : Gam => fracSymbol α k * Real.exp (-(r * fracSymbol α k))) := by
  refine Summable.of_nonneg_of_le (fun k => by
      have := fracSymbol_nonneg α k; positivity) (fun k => ?_) (summable_gam_wt_frac_heat hα hr)
  have h1 : fracSymbol α k ≤ wt k * (1 + fracSymbol α k) := by
    have h2 := one_le_wt k
    have h3 := fracSymbol_nonneg α k
    nlinarith
  nlinarith [Real.exp_pos (-(r * fracSymbol α k))]

end LiWang.WienerModel
