/-
# The fractional heat semigroup on the Wiener algebra

The diagonal multiplier `exp(-t (4π²|k|²)^α)` for `1/2 < α < 1`.  We prove contractivity on
the Wiener algebra, the semigroup law, the smoothing estimate `Wiener → Wiener1` for `t > 0`
with the explicit constant `1 + 1/(πt)`, the isolated scalar estimate that controls
`(1 + |k|) exp(-t c |k|^{2α})`, and integrability of the resulting time singularity — the
last of which is exactly where `1/2 < α` is used.

Part of `LiWangWienerPhysicalResidualPacket` v2.0.
-/
import LiWangWiener.Spacetime
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## The isolated scalar estimate -/

/-- `x e^{-x} ≤ 1` for `x ≥ 0`. -/
theorem mul_exp_neg_le_one {x : ℝ} (_hx : 0 ≤ x) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have h2 : x ≤ Real.exp x := by linarith
  have h3 : (0:ℝ) < Real.exp (-x) := Real.exp_pos _
  calc x * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) := by nlinarith
    _ = 1 := by rw [← Real.exp_add]; simp

/-- **The scalar estimate controlling `(1 + |k|) exp(-t c |k|^{2α})`.**
For `s > 0` and `r ≥ 0`, `(1 + r) e^{-s r} ≤ 1 + 1/s`. -/
theorem one_add_mul_exp_le {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    (1 + r) * Real.exp (-(s * r)) ≤ 1 + 1 / s := by
  have hexp_le_one : Real.exp (-(s * r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hkey : r * Real.exp (-(s * r)) ≤ 1 / s := by
    have h := mul_exp_neg_le_one (x := s * r) (by positivity)
    have : s * (r * Real.exp (-(s * r))) ≤ 1 := by
      calc s * (r * Real.exp (-(s * r))) = (s * r) * Real.exp (-(s * r)) := by ring
        _ ≤ 1 := h
    rw [le_div_iff₀ hs]
    linarith [this]
  calc (1 + r) * Real.exp (-(s * r))
      = Real.exp (-(s * r)) + r * Real.exp (-(s * r)) := by ring
    _ ≤ 1 + 1 / s := add_le_add hexp_le_one hkey

/-- **Integrability of the time singularity.**  The smoothing constant of the fractional heat
semigroup behaves like `t^{-1/(2α)}`, which is integrable near `0` precisely because
`1/2 < α`. -/
theorem intervalIntegrable_time_singularity {α : ℝ} (hα : 1 / 2 < α) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ (-(1 / (2 * α)))) MeasureTheory.volume 0 T := by
  refine intervalIntegral.intervalIntegrable_rpow' ?_
  have hα0 : (0:ℝ) < α := by linarith
  have h2 : (1:ℝ) < 2 * α := by linarith
  have : 1 / (2 * α) < 1 := by
    rw [div_lt_one (by linarith)]
    exact h2
  linarith

/-! ## The fractional Laplacian symbol -/

/-- The squared Euclidean length of a lattice frequency. -/
noncomputable def sqNorm (k : Gam) : ℝ := ((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2

theorem sqNorm_nonneg (k : Gam) : 0 ≤ sqNorm k := by
  simp only [sqNorm]; positivity

theorem one_le_sqNorm {k : Gam} (hk : k ≠ 0) : 1 ≤ sqNorm k := by
  have h : k 0 ≠ 0 ∨ k 1 ≠ 0 := by
    by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    refine hk ?_
    funext i
    fin_cases i
    · show k 0 = 0; exact hcon.1
    · show k 1 = 0; exact hcon.2
  have h0 : (0:ℝ) ≤ ((k 0 : ℤ) : ℝ) ^ 2 := sq_nonneg _
  have h1 : (0:ℝ) ≤ ((k 1 : ℤ) : ℝ) ^ 2 := sq_nonneg _
  rcases h with h | h
  · have : (1:ℤ) ≤ |k 0| := Int.one_le_abs (by omega)
    have hr : (1:ℝ) ≤ |((k 0 : ℤ) : ℝ)| := by exact_mod_cast this
    have : (1:ℝ) ≤ ((k 0 : ℤ) : ℝ) ^ 2 := by nlinarith [abs_nonneg ((k 0 : ℤ) : ℝ), sq_abs ((k 0 : ℤ) : ℝ)]
    simp only [sqNorm]; linarith
  · have : (1:ℤ) ≤ |k 1| := Int.one_le_abs (by omega)
    have hr : (1:ℝ) ≤ |((k 1 : ℤ) : ℝ)| := by exact_mod_cast this
    have : (1:ℝ) ≤ ((k 1 : ℤ) : ℝ) ^ 2 := by nlinarith [abs_nonneg ((k 1 : ℤ) : ℝ), sq_abs ((k 1 : ℤ) : ℝ)]
    simp only [sqNorm]; linarith

/-- The Euclidean length of a lattice frequency. -/
noncomputable def absK (k : Gam) : ℝ := Real.sqrt (sqNorm k)

theorem absK_nonneg (k : Gam) : 0 ≤ absK k := Real.sqrt_nonneg _

theorem sq_absK (k : Gam) : absK k ^ 2 = sqNorm k := Real.sq_sqrt (sqNorm_nonneg k)

theorem one_le_absK {k : Gam} (hk : k ≠ 0) : 1 ≤ absK k := by
  rw [absK, show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (one_le_sqNorm hk)

/-- The `ℓ¹` frequency length is at most twice the Euclidean length. -/
theorem l1_le_two_absK (k : Gam) : |((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)| ≤ 2 * absK k := by
  have hs := sqNorm_nonneg k
  have hkey : ((|((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)|) / 2) ^ 2 ≤ sqNorm k := by
    have h0 := sq_abs ((k 0 : ℤ) : ℝ)
    have h1 := sq_abs ((k 1 : ℤ) : ℝ)
    have hab : 0 ≤ (|((k 0 : ℤ) : ℝ)| - |((k 1 : ℤ) : ℝ)|) ^ 2 := sq_nonneg _
    simp only [sqNorm]
    nlinarith
  have h := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_sq (by positivity)] at h
  rw [absK]
  linarith

/-- The fractional Laplacian symbol `(4π²|k|²)^α`. -/
noncomputable def fracSymbol (α : ℝ) (k : Gam) : ℝ := (4 * Real.pi ^ 2 * sqNorm k) ^ α

theorem fracSymbol_nonneg (α : ℝ) (k : Gam) : 0 ≤ fracSymbol α k :=
  Real.rpow_nonneg (by have := sqNorm_nonneg k; positivity) α

theorem fracSymbol_eq_rpow (α : ℝ) (k : Gam) :
    fracSymbol α k = (2 * Real.pi * absK k) ^ (2 * α) := by
  have hX : (0:ℝ) ≤ 2 * Real.pi * absK k := by
    have := absK_nonneg k; positivity
  have hsq : 4 * Real.pi ^ 2 * sqNorm k = (2 * Real.pi * absK k) ^ (2 : ℕ) := by
    rw [mul_pow, mul_pow, sq_absK]; ring
  rw [fracSymbol, hsq, ← Real.rpow_natCast (2 * Real.pi * absK k) 2, ← Real.rpow_mul hX]
  norm_num

/-- **The frequency-space lower bound** `(4π²|k|²)^α ≥ π (|k₀| + |k₁|)`, valid for
`1/2 ≤ α`.  This is the estimate that converts the fractional dissipation into a gain of one
lattice derivative. -/
theorem pi_l1_le_fracSymbol {α : ℝ} (hα : 1 / 2 ≤ α) (k : Gam) :
    Real.pi * (|((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)|) ≤ fracSymbol α k := by
  by_cases hk : k = 0
  · subst hk
    have h0 : ((((0 : Gam)) 0 : ℤ) : ℝ) = 0 := by norm_num
    have h1 : ((((0 : Gam)) 1 : ℤ) : ℝ) = 0 := by norm_num
    rw [h0, h1]
    simp only [abs_zero, add_zero, mul_zero]
    exact fracSymbol_nonneg α 0
  · have hA : 1 ≤ absK k := one_le_absK hk
    have hX : 1 ≤ 2 * Real.pi * absK k := by
      have hpi : (3:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith
    have h2a : (1:ℝ) ≤ 2 * α := by linarith
    have hstep : (2 * Real.pi * absK k) ^ (1 : ℝ) ≤ (2 * Real.pi * absK k) ^ (2 * α) :=
      Real.rpow_le_rpow_of_exponent_le hX h2a
    rw [Real.rpow_one] at hstep
    rw [fracSymbol_eq_rpow]
    refine le_trans ?_ hstep
    have hl1 := l1_le_two_absK k
    nlinarith [Real.pi_pos]

/-! ## The fractional heat multiplier -/

/-- The fractional heat symbol `exp(-t (4π²|k|²)^α)`. -/
noncomputable def heatSymbol (α t : ℝ) (k : Gam) : ℂ :=
  ((Real.exp (-(t * fracSymbol α k)) : ℝ) : ℂ)

theorem norm_heatSymbol (α t : ℝ) (k : Gam) :
    ‖heatSymbol α t k‖ = Real.exp (-(t * fracSymbol α k)) := by
  rw [heatSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **Contractivity**: the heat symbol is bounded by one for `t ≥ 0`. -/
theorem norm_heatSymbol_le_one {α t : ℝ} (ht : 0 ≤ t) (k : Gam) : ‖heatSymbol α t k‖ ≤ 1 := by
  rw [norm_heatSymbol, Real.exp_le_one_iff]
  have := fracSymbol_nonneg α k
  nlinarith

theorem heatSymbol_bdd {α t : ℝ} (ht : 0 ≤ t) : ∃ C : ℝ, ∀ k, ‖heatSymbol α t k‖ ≤ C :=
  ⟨1, norm_heatSymbol_le_one ht⟩

/-- **The fractional heat operator** on the Wiener algebra. -/
noncomputable def heatOp (α : ℝ) {t : ℝ} (ht : 0 ≤ t) : Wiener →L[ℂ] Wiener :=
  mult (heatSymbol α t) (heatSymbol_bdd ht)

@[simp] theorem heatOp_apply (α : ℝ) {t : ℝ} (ht : 0 ≤ t) (a : Wiener) (k : Gam) :
    (heatOp α ht a) k = heatSymbol α t k * a k := rfl

/-- **Contractivity of the fractional heat semigroup on the Wiener algebra.** -/
theorem norm_heatOp_le (α : ℝ) {t : ℝ} (ht : 0 ≤ t) : ‖heatOp α ht‖ ≤ 1 :=
  norm_mult_le _ _ (norm_heatSymbol_le_one ht)

theorem norm_heatOp_apply_le (α : ℝ) {t : ℝ} (ht : 0 ≤ t) (a : Wiener) :
    ‖heatOp α ht a‖ ≤ ‖a‖ := by
  have h := norm_mult_apply_le (heatSymbol α t) (heatSymbol_bdd ht)
    (norm_heatSymbol_le_one ht) a
  simpa using h

/-- **The semigroup law.** -/
theorem heatSymbol_add (α s t : ℝ) (k : Gam) :
    heatSymbol α s k * heatSymbol α t k = heatSymbol α (s + t) k := by
  rw [heatSymbol, heatSymbol, heatSymbol, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem heatOp_heatOp (α : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (a : Wiener) :
    heatOp α hs (heatOp α ht a) = heatOp α (add_nonneg hs ht) a := by
  ext k
  show heatSymbol α s k * (heatSymbol α t k * a k) = heatSymbol α (s + t) k * a k
  rw [← mul_assoc, heatSymbol_add]

/-! ## The smoothing estimate `Wiener → Wiener1` -/

/-- **The pointwise smoothing bound**: for `t > 0` and `1/2 ≤ α`,
`(1 + |k₀| + |k₁|) exp(-t (4π²|k|²)^α) ≤ 1 + 1/(πt)`. -/
theorem wt_mul_heat_le {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (k : Gam) :
    wt k * Real.exp (-(t * fracSymbol α k)) ≤ 1 + 1 / (Real.pi * t) := by
  set r : ℝ := |((k 0 : ℤ) : ℝ)| + |((k 1 : ℤ) : ℝ)| with hr
  have hr0 : 0 ≤ r := by positivity
  have hlow := pi_l1_le_fracSymbol hα k
  have hmono : Real.exp (-(t * fracSymbol α k)) ≤ Real.exp (-((Real.pi * t) * r)) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have hwt : wt k = 1 + r := by simp only [wt, hr]; ring
  have hs : 0 < Real.pi * t := by positivity
  calc wt k * Real.exp (-(t * fracSymbol α k))
      ≤ wt k * Real.exp (-((Real.pi * t) * r)) := by
        exact mul_le_mul_of_nonneg_left hmono (wt_pos k).le
    _ = (1 + r) * Real.exp (-((Real.pi * t) * r)) := by rw [hwt]
    _ ≤ 1 + 1 / (Real.pi * t) := one_add_mul_exp_le hs hr0

theorem summable_heatSmooth {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) :
    Summable fun k => wt k * ‖heatSymbol α t k * a k‖ := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => ?_) ((wiener_summable a).mul_left (1 + 1 / (Real.pi * t)))
  rw [norm_mul, norm_heatSymbol]
  calc wt k * (Real.exp (-(t * fracSymbol α k)) * ‖a k‖)
      = (wt k * Real.exp (-(t * fracSymbol α k))) * ‖a k‖ := by ring
    _ ≤ (1 + 1 / (Real.pi * t)) * ‖a k‖ :=
        mul_le_mul_of_nonneg_right (wt_mul_heat_le hα ht k) (norm_nonneg _)

/-- **The smoothing map** `Wiener → Wiener1` for positive time. -/
noncomputable def heatSmooth {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) : Wiener1 :=
  Wiener1.mk (fun k => heatSymbol α t k * a k) (summable_heatSmooth hα ht a)

@[simp] theorem heatSmooth_coeff {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener)
    (k : Gam) : (heatSmooth hα ht a).coeff k = heatSymbol α t k * a k := rfl

/-- The smoothing map really is the heat operator, seen in the first-order space. -/
theorem incl_heatSmooth {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) :
    incl (heatSmooth hα ht a) = heatOp α ht.le a := by
  ext k; rfl

/-- **The smoothing estimate**: `‖e^{-t(-Δ)^α} a‖_{A¹} ≤ (1 + 1/(πt)) ‖a‖_A`. -/
theorem norm_heatSmooth_le {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) :
    ‖heatSmooth hα ht a‖ ≤ (1 + 1 / (Real.pi * t)) * ‖a‖ := by
  rw [Wiener1.norm_eq, wiener_norm_eq, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_heatSmooth hα ht a)
    ((wiener_summable a).mul_left _)
  show wt k * ‖heatSymbol α t k * a k‖ ≤ (1 + 1 / (Real.pi * t)) * ‖a k‖
  rw [norm_mul, norm_heatSymbol]
  calc wt k * (Real.exp (-(t * fracSymbol α k)) * ‖a k‖)
      = (wt k * Real.exp (-(t * fracSymbol α k))) * ‖a k‖ := by ring
    _ ≤ (1 + 1 / (Real.pi * t)) * ‖a k‖ :=
        mul_le_mul_of_nonneg_right (wt_mul_heat_le hα ht k) (norm_nonneg _)

theorem heatSmooth_add {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a b : Wiener) :
    heatSmooth hα ht (a + b) = heatSmooth hα ht a + heatSmooth hα ht b := by
  apply Wiener1.coeff_injective
  funext k
  show heatSymbol α t k * ((a + b : Wiener) k) = _
  show heatSymbol α t k * (a k + b k) = heatSymbol α t k * a k + heatSymbol α t k * b k
  ring

theorem heatSmooth_smul {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (c : ℂ) (a : Wiener) :
    heatSmooth hα ht (c • a) = c • heatSmooth hα ht a := by
  apply Wiener1.coeff_injective
  funext k
  show heatSymbol α t k * ((c • a : Wiener) k) = _
  show heatSymbol α t k * (c * a k) = c * (heatSymbol α t k * a k)
  ring

/-- **The smoothing operator as a bounded linear map** `Wiener →L[ℂ] Wiener1`. -/
noncomputable def heatSmoothCLM {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) :
    Wiener →L[ℂ] Wiener1 :=
  LinearMap.mkContinuous
    { toFun := heatSmooth hα ht
      map_add' := heatSmooth_add hα ht
      map_smul' := fun c a => heatSmooth_smul hα ht c a }
    (1 + 1 / (Real.pi * t)) (fun a => norm_heatSmooth_le hα ht a)

@[simp] theorem heatSmoothCLM_apply {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) :
    heatSmoothCLM hα ht a = heatSmooth hα ht a := rfl

theorem norm_heatSmoothCLM_le {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) :
    ‖heatSmoothCLM hα ht‖ ≤ 1 + 1 / (Real.pi * t) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _


/-! ## The sharp smoothing estimate and the integrable time singularity -/

theorem mul_exp_neg_rpow_le {β s u : ℝ} (hβ : 1 ≤ β) (hs : 0 < s) (hu : 0 ≤ u) :
    u * Real.exp (-(s * u ^ β)) ≤ s ^ (-(1 / β)) := by
  have hβ0 : (0:ℝ) < β := by linarith
  set c : ℝ := s ^ (1 / β) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hs _
  set v : ℝ := c * u with hv
  have hv0 : 0 ≤ v := by positivity
  have hvb : v ^ β = s * u ^ β := by
    rw [hv, Real.mul_rpow hc0.le hu, hc, ← Real.rpow_mul hs.le, one_div,
      inv_mul_cancel₀ (ne_of_gt hβ0), Real.rpow_one]
  have hkey : v * Real.exp (-(v ^ β)) ≤ 1 := by
    rcases le_or_gt v 1 with h | h
    · have he : Real.exp (-(v ^ β)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ v ^ β := Real.rpow_nonneg hv0 β
        linarith
      nlinarith [Real.exp_pos (-(v ^ β))]
    · have hvv : v ≤ v ^ β := by
        calc v = v ^ (1:ℝ) := (Real.rpow_one v).symm
          _ ≤ v ^ β := Real.rpow_le_rpow_of_exponent_le h.le hβ
      have he : Real.exp (-(v ^ β)) ≤ Real.exp (-v) := by
        rw [Real.exp_le_exp]; linarith
      nlinarith [mul_exp_neg_le_one hv0, Real.exp_pos (-v), Real.exp_pos (-(v ^ β))]
  have hcv : v * Real.exp (-(v ^ β)) = c * (u * Real.exp (-(s * u ^ β))) := by
    rw [hvb, hv]; ring
  have hle : c * (u * Real.exp (-(s * u ^ β))) ≤ 1 := by rw [← hcv]; exact hkey
  have hX : u * Real.exp (-(s * u ^ β)) ≤ 1 / c := by
    rw [le_div_iff₀ hc0]
    calc (u * Real.exp (-(s * u ^ β))) * c = c * (u * Real.exp (-(s * u ^ β))) := by ring
      _ ≤ 1 := hle
  rw [Real.rpow_neg hs.le, ← hc, ← one_div]
  exact hX

theorem fracSymbol_factor (α : ℝ) (k : Gam) :
    fracSymbol α k = (2 * Real.pi) ^ (2 * α) * (absK k) ^ (2 * α) := by
  rw [fracSymbol_eq_rpow, Real.mul_rpow (by positivity) (absK_nonneg k)]

theorem rpow_two_pi_inv {α : ℝ} (hα : 1 / 2 ≤ α) :
    ((2 * Real.pi) ^ (2 * α)) ^ (-(1 / (2 * α))) = (2 * Real.pi)⁻¹ := by
  have h2a : (0:ℝ) < 2 * α := by linarith
  rw [← Real.rpow_mul (by positivity),
    show (2 * α) * (-(1 / (2 * α))) = -1 by field_simp,
    Real.rpow_neg_one]

theorem wt_mul_heat_le_sharp {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (k : Gam) :
    wt k * Real.exp (-(t * fracSymbol α k)) ≤ 1 + t ^ (-(1 / (2 * α))) / Real.pi := by
  have h2a : (1:ℝ) ≤ 2 * α := by linarith
  set u : ℝ := absK k with hu
  have hu0 : 0 ≤ u := absK_nonneg k
  have hpow0 : (0:ℝ) < (2 * Real.pi) ^ (2 * α) := Real.rpow_pos_of_pos (by positivity) _
  set s : ℝ := t * (2 * Real.pi) ^ (2 * α) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hts : t * fracSymbol α k = s * u ^ (2 * α) := by
    rw [fracSymbol_factor α k, hsdef, hu]; ring
  have hkey := mul_exp_neg_rpow_le (β := 2 * α) (s := s) (u := u) h2a hs0 hu0
  have hup : (0:ℝ) ≤ u ^ (2 * α) := Real.rpow_nonneg hu0 _
  have hexp1 : Real.exp (-(s * u ^ (2 * α))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hwt : wt k ≤ 1 + 2 * u := by
    have := l1_le_two_absK k
    simp only [wt, hu]
    linarith
  have hsrp : s ^ (-(1 / (2 * α))) = t ^ (-(1 / (2 * α))) / (2 * Real.pi) := by
    rw [hsdef, Real.mul_rpow ht.le hpow0.le, rpow_two_pi_inv hα]
    ring
  rw [hts]
  calc wt k * Real.exp (-(s * u ^ (2 * α)))
      ≤ (1 + 2 * u) * Real.exp (-(s * u ^ (2 * α))) :=
        mul_le_mul_of_nonneg_right hwt (Real.exp_pos _).le
    _ = Real.exp (-(s * u ^ (2 * α))) + 2 * (u * Real.exp (-(s * u ^ (2 * α)))) := by ring
    _ ≤ 1 + 2 * s ^ (-(1 / (2 * α))) := by
        have : 2 * (u * Real.exp (-(s * u ^ (2 * α)))) ≤ 2 * s ^ (-(1 / (2 * α))) := by
          linarith
        linarith
    _ = 1 + t ^ (-(1 / (2 * α))) / Real.pi := by
        rw [hsrp]
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

theorem summable_heatSmooth_sharp {α t : ℝ} (_hα : 1 / 2 ≤ α) (_ht : 0 < t) (a : Wiener) :
    Summable fun k => (1 + t ^ (-(1 / (2 * α))) / Real.pi) * ‖a k‖ :=
  (wiener_summable a).mul_left _

/-- **The sharp smoothing estimate**
`‖e^{-t(-Δ)^α} a‖_{A¹} ≤ (1 + t^{-1/(2α)}/π) ‖a‖_A`.
The `t`-dependence `t^{-1/(2α)}` is the sharp one; it is integrable near `t = 0` exactly
when `α > 1/2` (see `intervalIntegrable_heatConst`). -/
theorem norm_heatSmooth_le_sharp {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) (a : Wiener) :
    ‖heatSmooth hα ht a‖ ≤ (1 + t ^ (-(1 / (2 * α))) / Real.pi) * ‖a‖ := by
  rw [Wiener1.norm_eq, wiener_norm_eq, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_heatSmooth hα ht a)
    (summable_heatSmooth_sharp hα ht a)
  show wt k * ‖heatSymbol α t k * a k‖ ≤ (1 + t ^ (-(1 / (2 * α))) / Real.pi) * ‖a k‖
  rw [norm_mul, norm_heatSymbol]
  calc wt k * (Real.exp (-(t * fracSymbol α k)) * ‖a k‖)
      = (wt k * Real.exp (-(t * fracSymbol α k))) * ‖a k‖ := by ring
    _ ≤ (1 + t ^ (-(1 / (2 * α))) / Real.pi) * ‖a k‖ :=
        mul_le_mul_of_nonneg_right (wt_mul_heat_le_sharp hα ht k) (norm_nonneg _)

theorem norm_heatSmoothCLM_le_sharp {α t : ℝ} (hα : 1 / 2 ≤ α) (ht : 0 < t) :
    ‖heatSmoothCLM hα ht‖ ≤ 1 + t ^ (-(1 / (2 * α))) / Real.pi := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun a => norm_heatSmooth_le_sharp hα ht a)
  have : (0:ℝ) ≤ t ^ (-(1 / (2 * α))) := Real.rpow_nonneg ht.le _
  have hpi := Real.pi_pos
  positivity

/-- **Integrability of the sharp smoothing constant.**  This is exactly where `1/2 < α`
enters: the time singularity `t^{-1/(2α)}` of the smoothing constant is integrable on
`[0,T]` precisely because `1/(2α) < 1`. -/
theorem intervalIntegrable_heatConst {α : ℝ} (hα : 1 / 2 < α) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => 1 + t ^ (-(1 / (2 * α))) / Real.pi)
      MeasureTheory.volume 0 T :=
  (intervalIntegrable_const).add
    ((intervalIntegrable_time_singularity hα T).div_const Real.pi)

/-! ## The Duhamel integrand

The bound below is what a Duhamel/mild-solution argument would integrate in time.  The
mild-solution map itself is **not** constructed in this packet; see `STATUS.md`. -/

/-- **The Duhamel integrand bound.**  Applying the fractional heat smoothing to the
transport term costs the sharp factor `1 + (t-s)^{-1/(2α)}/π`, which is integrable in `s`. -/
theorem norm_duhamel_integrand_le {α τ : ℝ} (hα : 1 / 2 ≤ α) (hτ : 0 < τ)
    {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (u v : Wiener1) :
    ‖heatSmooth hα hτ (transport m hm u v)‖
      ≤ (1 + τ ^ (-(1 / (2 * α))) / Real.pi) * (4 * Real.pi * C * ‖u‖ * ‖v‖) := by
  refine le_trans (norm_heatSmooth_le_sharp hα hτ _) ?_
  have hpos : (0:ℝ) ≤ 1 + τ ^ (-(1 / (2 * α))) / Real.pi := by
    have : (0:ℝ) ≤ τ ^ (-(1 / (2 * α))) := Real.rpow_nonneg hτ.le _
    have hpi := Real.pi_pos
    positivity
  exact mul_le_mul_of_nonneg_left (norm_transport_apply_le hm hC u v) hpos

/-- Conjugate symmetry is preserved by the heat semigroup: the fractional heat flow of a
real field is real. -/
theorem conjSymmetric_heatSymbol (α t : ℝ) : ConjSymmetric (heatSymbol α t) := by
  intro k
  have hsq : sqNorm (-k) = sqNorm k := by
    have h0 : (((-k) 0 : ℤ) : ℝ) = -((k 0 : ℤ) : ℝ) := by
      rw [show ((-k) 0 : ℤ) = -(k 0) from rfl]; push_cast; ring
    have h1 : (((-k) 1 : ℤ) : ℝ) = -((k 1 : ℤ) : ℝ) := by
      rw [show ((-k) 1 : ℤ) = -(k 1) from rfl]; push_cast; ring
    simp only [sqNorm, h0, h1]; ring
  rw [heatSymbol, heatSymbol, fracSymbol, fracSymbol, hsq, Complex.conj_ofReal]

theorem conjSymmetric_heatOp {α t : ℝ} (ht : 0 ≤ t) {a : Wiener}
    (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric ((heatOp α ht a : Wiener) : Gam → ℂ) :=
  ConjSymmetric.mult _ (conjSymmetric_heatSymbol α t) ha

end LiWang.WienerModel
