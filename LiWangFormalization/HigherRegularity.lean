/-
# Higher regularity of the constructed small-source solution

Step 3 of the v8.0 Sobolev-compatibility bridge.

Three estimates, all stated as bounds on finite partial sums (`WB`), all proved:

* `WB_duhamel` — the Duhamel operator **gains one weight**:
  `∑_k wt(k)^{r+1} |(J g)_k(t)| ≤ (sup_s ∑_k wt(k)^r |g_k(s)|) · duhamelConst α T`.
  This is the packet's own sharp heat estimate `wt_mul_heat_le_sharp` integrated in time; it is
  exactly where `1/2 < α` is used.
* `WB_quadCurve` — the **tame** transport bound: the high weight appears linearly, multiplied by
  the *low* Wiener norm of the state.  That is what lets a small `A¹` norm absorb it.
* `sobBound_of_WB3` — a `wt³` bound implies the `H³` bound, since `ρ(k) ≤ wt(k)²` and
  `∑ x_k² ≤ (∑ x_k)²` for nonnegative `x`.

Part of `LiWangFormalizationSobolevCompatibilityPacket` v8.0.
-/
import LiWangFormalization.HigherWeight
import LiWangFormalization.PhysicalComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. Elementary `WB` arithmetic -/

theorem WB.add {r : ℕ} {R₁ R₂ : ℝ} {a b : Gam → ℂ} (ha : WB r R₁ a) (hb : WB r R₂ b) :
    WB r (R₁ + R₂) (fun k => a k + b k) := by
  intro F
  have hle : ∀ k ∈ F, wt k ^ r * ‖a k + b k‖
      ≤ wt k ^ r * ‖a k‖ + wt k ^ r * ‖b k‖ := by
    intro k _
    have := norm_add_le (a k) (b k)
    have hw : (0:ℝ) ≤ wt k ^ r := by have := (wt_pos k).le; positivity
    nlinarith
  calc (∑ k ∈ F, wt k ^ r * ‖a k + b k‖)
      ≤ ∑ k ∈ F, (wt k ^ r * ‖a k‖ + wt k ^ r * ‖b k‖) := Finset.sum_le_sum hle
    _ = (∑ k ∈ F, wt k ^ r * ‖a k‖) + ∑ k ∈ F, wt k ^ r * ‖b k‖ := Finset.sum_add_distrib
    _ ≤ R₁ + R₂ := add_le_add (ha F) (hb F)

/-- Scaling the coefficients pointwise. -/
theorem WB.of_norm_le_mul {r : ℕ} {R c : ℝ} (hc : 0 ≤ c) {a b : Gam → ℂ}
    (hb : WB r R b) (hab : ∀ k, ‖a k‖ ≤ c * ‖b k‖) : WB r (c * R) a := by
  intro F
  have hstep : (∑ k ∈ F, wt k ^ r * ‖a k‖) ≤ ∑ k ∈ F, c * (wt k ^ r * ‖b k‖) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hw : (0:ℝ) ≤ wt k ^ r := by have := (wt_pos k).le; positivity
    have := hab k
    nlinarith
  rw [← Finset.mul_sum] at hstep
  exact le_trans hstep (mul_le_mul_of_nonneg_left (hb F) hc)

/-- Raising the weight by one costs one power of `wt`, which the derivative supplies. -/
theorem WB.shift {r : ℕ} {R : ℝ} {a : Gam → ℂ} (h : WB (r + 1) R a) :
    WB r R (fun k => (wt k : ℂ) * a k) := by
  intro F
  refine le_trans (le_of_eq ?_) (h F)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos k).le, pow_succ]
  ring

/-! ## 2. The `H³` bound from a `wt³` bound -/

theorem rho_le_wt_sq (k : Gam) : rho k ≤ wt k ^ 2 := by
  have h0 : (0:ℝ) ≤ |((k 0 : ℤ) : ℝ)| := abs_nonneg _
  have h1 : (0:ℝ) ≤ |((k 1 : ℤ) : ℝ)| := abs_nonneg _
  have ha : |((k 0 : ℤ) : ℝ)| ^ 2 = ((k 0 : ℤ) : ℝ) ^ 2 := sq_abs _
  have hb : |((k 1 : ℤ) : ℝ)| ^ 2 = ((k 1 : ℤ) : ℝ) ^ 2 := sq_abs _
  rw [rho_eq, wt, ← ha, ← hb]
  nlinarith

/-- **A `wt³` bound gives the `H³` bound.** -/
theorem sobBound_of_WB3 {R : ℝ} {c : Gam → ℂ} (h : WB 3 R c) :
    ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖c k‖ ^ 2) ≤ R ^ 2 := by
  intro F
  have hterm : ∀ k ∈ F, rho k ^ 3 * ‖c k‖ ^ 2 ≤ (wt k ^ 3 * ‖c k‖) ^ 2 := by
    intro k _
    have hρ : rho k ^ 3 ≤ (wt k ^ 2) ^ 3 :=
      pow_le_pow_left₀ (rho_pos k).le (rho_le_wt_sq k) 3
    have hc2 : (0:ℝ) ≤ ‖c k‖ ^ 2 := sq_nonneg _
    have hexp : (wt k ^ 3 * ‖c k‖) ^ 2 = (wt k ^ 2) ^ 3 * ‖c k‖ ^ 2 := by ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hρ hc2
  have hsq : (∑ k ∈ F, (wt k ^ 3 * ‖c k‖) ^ 2) ≤ (∑ k ∈ F, wt k ^ 3 * ‖c k‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => wt_pow_norm_nonneg 3 c k)
  have hR : (∑ k ∈ F, wt k ^ 3 * ‖c k‖) ^ 2 ≤ R ^ 2 := by
    have h0 : (0:ℝ) ≤ ∑ k ∈ F, wt k ^ 3 * ‖c k‖ :=
      Finset.sum_nonneg (fun k _ => wt_pow_norm_nonneg 3 c k)
    nlinarith [h F, h.nonneg]
  calc (∑ k ∈ F, rho k ^ 3 * ‖c k‖ ^ 2)
      ≤ ∑ k ∈ F, (wt k ^ 3 * ‖c k‖) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ (∑ k ∈ F, wt k ^ 3 * ‖c k‖) ^ 2 := hsq
    _ ≤ R ^ 2 := hR

/-! ## 3. The tame transport bound -/

/-- **The tame transport bound.**  With `R₀ ≤ R₁` the low Wiener norms, the transport of the
state is controlled at weight `r` by `R_r · R₁` and `R₀ · R_{r+1}`: the top weight enters
*linearly* and is multiplied by the **low** norm `R₀`. -/
theorem WB_transport {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (hm : IsBddSymbol m) (u : Wiener1)
    {r : ℕ} {R₀ R₁ Rr Rr1 : ℝ}
    (h0 : WB 0 R₀ u.coeff) (h1 : WB 1 R₁ u.coeff) (hr : WB r Rr u.coeff)
    (hr1 : WB (r + 1) Rr1 u.coeff) :
    WB r (2 * (2 ^ r * ((C * Rr) * (2 * Real.pi * R₁) + (C * R₀) * (2 * Real.pi * Rr1))))
      (fun k => (transport m hm u u : Wiener) k) := by
  have hC0 : (0:ℝ) ≤ C := nonneg_of_symbol_bound hC
  have hpi : (0:ℝ) ≤ 2 * Real.pi := by positivity
  -- the velocity factor
  have hvel : ∀ j : Fin 2, ∀ k : Gam,
      ‖(velocity m hm j (incl u) : Wiener) k‖ ≤ C * ‖u.coeff k‖ := by
    intro j k
    show ‖m j k * u.coeff k‖ ≤ C * ‖u.coeff k‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC j k) (norm_nonneg _)
  -- the derivative factor
  have hder : ∀ j : Fin 2, ∀ k : Gam,
      ‖(fourierDeriv j u : Wiener) k‖ ≤ (2 * Real.pi) * (wt k * ‖u.coeff k‖) := by
    intro j k
    show ‖twoPiI * ((k j : ℤ) : ℂ) * u.coeff k‖ ≤ _
    rw [norm_mul, norm_mul, norm_twoPiI, Complex.norm_intCast]
    have hk : |((k j : ℤ) : ℝ)| ≤ wt k := abs_coe_le_wt j k
    have h0' : (0:ℝ) ≤ ‖u.coeff k‖ := norm_nonneg _
    calc 2 * Real.pi * |((k j : ℤ) : ℝ)| * ‖u.coeff k‖
        = (2 * Real.pi) * (|((k j : ℤ) : ℝ)| * ‖u.coeff k‖) := by ring
      _ ≤ (2 * Real.pi) * (wt k * ‖u.coeff k‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk h0') hpi
  -- weighted bounds on the two factors
  have hA : ∀ j : Fin 2, WB r (C * Rr) (fun k => (velocity m hm j (incl u) : Wiener) k) :=
    fun j => WB.of_norm_le_mul hC0 hr (hvel j)
  have hA0 : ∀ j : Fin 2, WB 0 (C * R₀) (fun k => (velocity m hm j (incl u) : Wiener) k) :=
    fun j => WB.of_norm_le_mul hC0 h0 (hvel j)
  have hB : ∀ j : Fin 2, WB r ((2 * Real.pi) * Rr1)
      (fun k => (fourierDeriv j u : Wiener) k) := by
    intro j
    refine WB.of_norm_le_mul hpi (WB.shift (r := r) hr1) ?_
    intro k
    refine le_trans (hder j k) (le_of_eq ?_)
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos k).le]
  have hB0 : ∀ j : Fin 2, WB 0 ((2 * Real.pi) * R₁)
      (fun k => (fourierDeriv j u : Wiener) k) := by
    intro j
    refine WB.of_norm_le_mul hpi (WB.shift (r := 0) h1) ?_
    intro k
    refine le_trans (hder j k) (le_of_eq ?_)
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos k).le]
  -- the tame convolution bound, summed over the two components
  have hconv : ∀ j : Fin 2,
      WB r (2 ^ r * ((C * Rr) * ((2 * Real.pi) * R₁) + (C * R₀) * ((2 * Real.pi) * Rr1)))
        (fun k => (conv (velocity m hm j (incl u)) (fourierDeriv j u) : Wiener) k) := by
    intro j
    exact WB.conv_tame (hA j) (hA0 j) (hB j) (hB0 j)
  have hsum : (fun k => (transport m hm u u : Wiener) k)
      = fun k => (conv (velocity m hm 0 (incl u)) (fourierDeriv 0 u) : Wiener) k
        + (conv (velocity m hm 1 (incl u)) (fourierDeriv 1 u) : Wiener) k := by
    funext k
    rw [transport_apply]
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, Fin.sum_univ_two]
  rw [hsum]
  have := (hconv 0).add (hconv 1)
  refine this.mono (le_of_eq ?_)
  ring


/-! ## 4. The Duhamel operator gains one weight -/

/-- The sharp smoothing constant of the fractional heat flow, as a function of elapsed time. -/
noncomputable def heatConstFun (α ρ : ℝ) : ℝ := 1 + ρ ^ (-(1 / (2 * α))) / Real.pi

theorem heatConstFun_nonneg (α : ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ heatConstFun α ρ := by
  have : (0:ℝ) ≤ ρ ^ (-(1 / (2 * α))) := Real.rpow_nonneg hρ _
  have hpi := Real.pi_pos
  rw [heatConstFun]
  positivity

theorem intervalIntegrable_heatConstFun (hα : 1 / 2 < α) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => heatConstFun α (t - s)) volume 0 t := by
  have hbase : IntervalIntegrable (fun ρ : ℝ => 1 + ρ ^ (-(1 / (2 * α))) / Real.pi)
      volume 0 t := intervalIntegrable_heatConst hα t
  have hsub := hbase.comp_sub_left t
  simp only [sub_zero, sub_self] at hsub
  exact hsub.symm

theorem integral_heatConstFun (hα : 1 / 2 < α) (t : ℝ) :
    (∫ s in (0:ℝ)..t, heatConstFun α (t - s)) = duhamelConst α t :=
  integral_heatConst hα t

/-- **The Duhamel operator gains one Wiener weight.**  This is the packet's sharp heat estimate
`wt_mul_heat_le_sharp` integrated in time; the time singularity `ρ^{-1/(2α)}` is integrable
exactly because `1/2 < α`. -/
theorem WB_duhamel (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {r : ℕ} {S : ℝ}
    (hS : ∀ s : ℝ, WB r S (fun k => (sourceFun hT g s) k))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    WB (r + 1) (S * duhamelConst α T) (curveState hT (duhamelOp hα hT g) t).coeff := by
  intro F
  have hS0 : (0:ℝ) ≤ S := (hS 0).nonneg
  set G : Gam → ℝ → ℂ := fun k s => (sourceFun hT g s) k with hG
  have hGcont : ∀ k, Continuous (G k) :=
    fun k => continuous_wiener_coeff k (continuous_sourceFun hT g)
  set E : Gam → ℝ → ℝ := fun k s => Real.exp (-((t - s) * fracSymbol α k)) with hE
  have hEcont : ∀ k, Continuous (E k) := by
    intro k
    exact Real.continuous_exp.comp (((continuous_const.sub continuous_id).mul
      continuous_const).neg)
  have hEnn : ∀ k s, 0 ≤ E k s := fun k s => (Real.exp_pos _).le
  -- the coefficient formula
  have hcoeff : ∀ k : Gam, (curveState hT (duhamelOp hα hT g) t).coeff k
      = ∫ s in (0:ℝ)..t, ((E k s : ℝ) : ℂ) * G k s := by
    intro k
    rw [coeff_duhamelOp_eq_scalarDuhamel hα hT g k ht, scalarDuhamel]
  -- the majorant is interval integrable
  have hmaj : ∀ k : Gam, IntervalIntegrable
      (fun s : ℝ => heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖)) volume 0 t := by
    intro k
    refine IntervalIntegrable.mul_continuousOn (intervalIntegrable_heatConstFun hα t) ?_
    exact (continuous_const.mul (hGcont k).norm).continuousOn
  have hlhs : ∀ k : Gam, IntervalIntegrable
      (fun s : ℝ => wt k ^ (r + 1) * (E k s * ‖G k s‖)) volume 0 t :=
    fun k => (continuous_const.mul ((hEcont k).mul (hGcont k).norm)).intervalIntegrable 0 t
  -- the per-mode bound
  have hbound : ∀ k : Gam, wt k ^ (r + 1) * ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖
      ≤ ∫ s in (0:ℝ)..t, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖) := by
    intro k
    have hwr : (0:ℝ) ≤ wt k ^ (r + 1) := by have := (wt_pos k).le; positivity
    have h1 : ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖
        ≤ ∫ s in (0:ℝ)..t, E k s * ‖G k s‖ := by
      rw [hcoeff k]
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm ht.1) ?_
      refine le_of_eq (intervalIntegral.integral_congr (fun s _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hEnn k s)]
    have h2 : wt k ^ (r + 1) * ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖
        ≤ ∫ s in (0:ℝ)..t, wt k ^ (r + 1) * (E k s * ‖G k s‖) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left h1 hwr
    refine le_trans h2 ?_
    refine intervalIntegral.integral_mono_on_of_le_Ioo ht.1 (hlhs k) (hmaj k) (fun s hs => ?_)
    have hts : 0 < t - s := by linarith [hs.2]
    have hsharp := wt_mul_heat_le_sharp hα.le hts k
    have hGn : (0:ℝ) ≤ ‖G k s‖ := norm_nonneg _
    have hwr' : (0:ℝ) ≤ wt k ^ r := by have := (wt_pos k).le; positivity
    have hEeq : E k s = Real.exp (-((t - s) * fracSymbol α k)) := rfl
    have hfac : wt k ^ (r + 1) * (E k s * ‖G k s‖)
        = (wt k * E k s) * (wt k ^ r * ‖G k s‖) := by rw [pow_succ]; ring
    rw [hfac, heatConstFun]
    exact mul_le_mul_of_nonneg_right (by rw [hEeq]; exact hsharp)
      (mul_nonneg hwr' hGn)
  -- sum over the finite set and interchange with the integral
  have hswap : (∑ k ∈ F, ∫ s in (0:ℝ)..t, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖))
      = ∫ s in (0:ℝ)..t, ∑ k ∈ F, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖) :=
    (intervalIntegral.integral_finset_sum (fun k _ => hmaj k)).symm
  have hcollect : ∀ s : ℝ, (∑ k ∈ F, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖))
      = heatConstFun α (t - s) * ∑ k ∈ F, wt k ^ r * ‖G k s‖ := by
    intro s; rw [Finset.mul_sum]
  have hfinal : (∫ s in (0:ℝ)..t, ∑ k ∈ F, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖))
      ≤ ∫ s in (0:ℝ)..t, heatConstFun α (t - s) * S := by
    refine intervalIntegral.integral_mono_on ht.1 ?_ ?_ (fun s hs => ?_)
    · have hconv : (∑ i ∈ F, fun s : ℝ => heatConstFun α (t - s) * (wt i ^ r * ‖G i s‖))
          = fun s : ℝ => ∑ k ∈ F, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖) := by
        funext s
        exact Finset.sum_apply s F _
      have hI := IntervalIntegrable.sum F (fun k (_ : k ∈ F) => hmaj k)
      rwa [hconv] at hI
    · exact (intervalIntegrable_heatConstFun hα t).mul_const S
    · rw [hcollect s]
      refine mul_le_mul_of_nonneg_left (hS s F) ?_
      exact heatConstFun_nonneg α (t - s) (by linarith [hs.2])
  have hconst : (∫ s in (0:ℝ)..t, heatConstFun α (t - s) * S) = duhamelConst α t * S := by
    rw [intervalIntegral.integral_mul_const, integral_heatConstFun hα t]
  calc (∑ k ∈ F, wt k ^ (r + 1) * ‖(curveState hT (duhamelOp hα hT g) t).coeff k‖)
      ≤ ∑ k ∈ F, ∫ s in (0:ℝ)..t, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖) :=
        Finset.sum_le_sum (fun k _ => hbound k)
    _ = ∫ s in (0:ℝ)..t, ∑ k ∈ F, heatConstFun α (t - s) * (wt k ^ r * ‖G k s‖) := hswap
    _ ≤ ∫ s in (0:ℝ)..t, heatConstFun α (t - s) * S := hfinal
    _ = duhamelConst α t * S := hconst
    _ ≤ duhamelConst α T * S :=
        mul_le_mul_of_nonneg_right (duhamelConst_mono hα ht.1 ht.2) hS0
    _ = S * duhamelConst α T := by ring


/-! ## 5. The Picard iterates -/

section Picard

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-- The Picard map of the mild equation, `Θ v = J_T f − B_K(v,v)`. -/
noncomputable def picardMap (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (f : Curve0 T) (v : Curve1 T) : Curve1 T :=
  duhamelOp hα hT f - sourceQuad hα hT m hm hr v v

/-- The Picard iterates, starting from `0`. -/
noncomputable def picard (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (f : Curve0 T) : ℕ → Curve1 T
  | 0 => 0
  | n + 1 => picardMap hα hT hm hr f (picard hα hT hm hr f n)

@[simp] theorem picard_zero (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (f : Curve0 T) : picard hα hT hm hr f 0 = 0 := rfl

@[simp] theorem picard_succ (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (f : Curve0 T) (n : ℕ) :
    picard hα hT hm hr f (n + 1) = picardMap hα hT hm hr f (picard hα hT hm hr f n) := rfl

/-- The Picard map written as a single Duhamel response — this is the form the higher-weight
estimate uses. -/
theorem picardMap_eq_duhamel (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (f : Curve0 T) (v : Curve1 T) :
    picardMap hα hT hm hr f v
      = duhamelOp hα hT (f - spacetimeTransport m hm hr v v) := by
  rw [picardMap, map_sub]
  rfl

variable {hα : 1 / 2 < α} {hT : 0 ≤ T} {hm : IsBddSymbol m} {hr : IsRealSymbol m}

/-- The iterates stay in the ball on which the map contracts. -/
theorem picard_norm_le {f : Curve0 T} {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b)
    (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ) (hbρ : b * ρ ≤ 1 / 4)
    (hf : ‖duhamelOp hα hT f‖ ≤ ρ / 2) (n : ℕ) : ‖picard hα hT hm hr f n‖ ≤ ρ := by
  induction n with
  | zero => simpa using hρ0
  | succ n ih =>
    rw [picard_succ, picardMap]
    refine le_trans (norm_sub_le _ _) ?_
    have hq : ‖sourceQuad hα hT m hm hr (picard hα hT hm hr f n) (picard hα hT hm hr f n)‖
        ≤ b * (ρ * ρ) := by
      refine le_trans ((sourceQuad hα hT m hm hr).le_opNorm₂ _ _) ?_
      have h1 : ‖sourceQuad hα hT m hm hr‖ * ‖picard hα hT hm hr f n‖ ≤ b * ρ :=
        mul_le_mul hb ih (norm_nonneg _) hb0
      have h2 : ‖picard hα hT hm hr f n‖ ≤ ρ := ih
      calc ‖sourceQuad hα hT m hm hr‖ * ‖picard hα hT hm hr f n‖ * ‖picard hα hT hm hr f n‖
          ≤ (b * ρ) * ρ := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = b * (ρ * ρ) := by ring
    have : b * (ρ * ρ) ≤ ρ / 4 := by nlinarith
    linarith [hf, hq]

/-- The Picard map contracts on the ball. -/
theorem picardMap_sub_le {f : Curve0 T} {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b)
    (hb0 : 0 ≤ b) (_hρ0 : 0 ≤ ρ) (hbρ : b * ρ ≤ 1 / 4) {v w : Curve1 T}
    (hv : ‖v‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖picardMap hα hT hm hr f v - picardMap hα hT hm hr f w‖ ≤ (1 / 2) * ‖v - w‖ := by
  have hdiff : picardMap hα hT hm hr f v - picardMap hα hT hm hr f w
      = -(quad (sourceQuad hα hT m hm hr) v - quad (sourceQuad hα hT m hm hr) w) := by
    rw [picardMap, picardMap]
    show duhamelOp hα hT f - sourceQuad hα hT m hm hr v v
        - (duhamelOp hα hT f - sourceQuad hα hT m hm hr w w) = _
    abel
  rw [hdiff, norm_neg]
  refine le_trans (norm_quad_sub_le (sourceQuad hα hT m hm hr) v w) ?_
  have hsum : ‖v‖ + ‖w‖ ≤ 2 * ρ := by linarith
  have h1 : ‖sourceQuad hα hT m hm hr‖ * (‖v‖ + ‖w‖) ≤ b * (2 * ρ) :=
    mul_le_mul hb hsum (by positivity) hb0
  have h2 : b * (2 * ρ) ≤ 1 / 2 := by linarith
  have h3 : (0:ℝ) ≤ ‖v - w‖ := norm_nonneg _
  calc ‖sourceQuad hα hT m hm hr‖ * (‖v‖ + ‖w‖) * ‖v - w‖
      ≤ (b * (2 * ρ)) * ‖v - w‖ := mul_le_mul_of_nonneg_right h1 h3
    _ ≤ (1 / 2) * ‖v - w‖ := mul_le_mul_of_nonneg_right h2 h3

/-- **The Picard iterates converge to any mild solution in the ball**, at a geometric rate.
No fixed-point theorem and no completeness argument is needed: the contraction estimate is
applied directly against the given solution. -/
theorem picard_tendsto {f : Curve0 T} {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b)
    (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ) (hbρ : b * ρ ≤ 1 / 4)
    (hf : ‖duhamelOp hα hT f‖ ≤ ρ / 2) {u : Curve1 T} (hu : ‖u‖ ≤ ρ)
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    Tendsto (fun n => ‖picard hα hT hm hr f n - u‖) atTop (nhds 0) := by
  have hfix : picardMap hα hT hm hr f u = u := by
    rw [picardMap, ← hmild]
    abel
  have hstep : ∀ n, ‖picard hα hT hm hr f n - u‖ ≤ (1 / 2) ^ n * ‖u‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hball := picard_norm_le hb hb0 hρ0 hbρ hf n
      have := picardMap_sub_le hb hb0 hρ0 hbρ hball hu (f := f)
      rw [picard_succ, hfix] at *
      calc ‖picardMap hα hT hm hr f (picard hα hT hm hr f n) - u‖
          ≤ (1 / 2) * ‖picard hα hT hm hr f n - u‖ := this
        _ ≤ (1 / 2) * ((1 / 2) ^ n * ‖u‖) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2) ^ (n + 1) * ‖u‖ := by rw [pow_succ]; ring
  have hgeo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖u‖) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1:ℝ) / 2 < 1)
    simpa using this.mul_const ‖u‖
  refine squeeze_zero (fun n => norm_nonneg _) hstep hgeo

/-- Coefficientwise convergence of the iterates, which is all the weighted bounds need. -/
theorem picard_tendsto_coeff {f : Curve0 T} {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b)
    (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ) (hbρ : b * ρ ≤ 1 / 4)
    (hf : ‖duhamelOp hα hT f‖ ≤ ρ / 2) {u : Curve1 T} (hu : ‖u‖ ≤ ρ)
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (s : ℝ) (k : Gam) :
    Tendsto (fun n => (curveState hT (picard hα hT hm hr f n) s).coeff k) atTop
      (nhds ((curveState hT u s).coeff k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (picard_tendsto hb hb0 hρ0 hbρ hf hu hmild)
  have hcoeff : (curveState hT (picard hα hT hm hr f n) s).coeff k
      - (curveState hT u s).coeff k
      = (curveState hT (picard hα hT hm hr f n - u) s).coeff k := rfl
  rw [hcoeff]
  refine le_trans ?_ (norm_curveState_le hT (picard hα hT hm hr f n - u) s)
  have h1 : ‖(curveState hT (picard hα hT hm hr f n - u) s).coeff k‖
      ≤ wt k * ‖(curveState hT (picard hα hT hm hr f n - u) s).coeff k‖ := by
    have := one_le_wt k
    nlinarith [norm_nonneg ((curveState hT (picard hα hT hm hr f n - u) s).coeff k)]
  refine le_trans h1 ?_
  rw [Wiener1.norm_eq]
  exact (Wiener1.summable_wt _).sum_le_tsum {k}
    (fun j _ => mul_nonneg (wt_pos j).le (norm_nonneg _)) |>.trans' (by simp)

/-! ## 6. Uniform higher-weight bounds on the iterates -/

/-- The constant in the tame transport bound. -/
noncomputable def transportConst (r : ℕ) (C : ℝ) : ℝ := 2 ^ (r + 2) * Real.pi * C

theorem WB_transport' {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (hm' : IsBddSymbol m) (u : Wiener1)
    {r : ℕ} {R₀ R₁ Rr Rr1 : ℝ}
    (h0 : WB 0 R₀ u.coeff) (h1 : WB 1 R₁ u.coeff) (hrb : WB r Rr u.coeff)
    (hr1 : WB (r + 1) Rr1 u.coeff) :
    WB r (transportConst r C * (Rr * R₁ + R₀ * Rr1))
      (fun k => (transport m hm' u u : Wiener) k) := by
  refine (WB_transport hC hm' u h0 h1 hrb hr1).mono (le_of_eq ?_)
  rw [transportConst]
  ring

/-- A bound holding at every time of `[0,T]` holds at every real time, because the curve is
clamped outside the interval. -/
theorem WB_curveState_all {v : Curve1 T} {r : ℕ} {R : ℝ}
    (h : ∀ t ∈ Set.Icc (0:ℝ) T, WB r R (curveState hT v t).coeff) (s : ℝ) :
    WB r R (curveState hT v s).coeff := by
  have hmem : ((clampT hT s : TimeI T) : ℝ) ∈ Set.Icc (0:ℝ) T := (clampT hT s).2
  have heq : curveState hT v s = curveState hT v ((clampT hT s : TimeI T) : ℝ) := by
    rw [curveState_coe hT v (clampT hT s)]
    rfl
  rw [heq]
  exact h _ hmem

/-- **One Picard step raises the weight by one.** -/
theorem WB_picardMap {f : Curve0 T} {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {r : ℕ} {Sf R₀ R₁ Rr Rr1 : ℝ}
    (hSf : ∀ s : ℝ, WB r Sf (fun k => (sourceFun hT f s) k)) {v : Curve1 T}
    (h0 : ∀ s : ℝ, WB 0 R₀ (curveState hT v s).coeff)
    (h1 : ∀ s : ℝ, WB 1 R₁ (curveState hT v s).coeff)
    (hrb : ∀ s : ℝ, WB r Rr (curveState hT v s).coeff)
    (hr1 : ∀ s : ℝ, WB (r + 1) Rr1 (curveState hT v s).coeff)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    WB (r + 1) ((Sf + transportConst r C * (Rr * R₁ + R₀ * Rr1)) * duhamelConst α T)
      (curveState hT (picardMap hα hT hm hr f v) t).coeff := by
  rw [picardMap_eq_duhamel]
  refine WB_duhamel hα hT _ (fun s => ?_) ht
  have hsplit : (fun k => (sourceFun hT (f - spacetimeTransport m hm hr v v) s) k)
      = fun k => (sourceFun hT f s) k
        + (-((transport m hm (curveState hT v s) (curveState hT v s) : Wiener) k)) := by
    funext k
    rw [sourceFun_sub_spacetimeTransport hT hm hr v f s, lp.coeFn_sub, Pi.sub_apply]
    show _ = _
    ring_nf
    rfl
  rw [hsplit]
  refine WB.add (hSf s) ?_
  refine WB.of_norm_le (WB_transport' hC hm (curveState hT v s) (h0 s) (h1 s) (hrb s) (hr1 s))
    (fun k => by rw [norm_neg])

/-- **Uniform higher-weight bound on every Picard iterate.**  The high weight is absorbed by the
small `A¹` norm `ρ`; the bound is independent of `n`. -/
theorem WB_picard_uniform {f : Curve0 T} {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b) (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ)
    (hbρ : b * ρ ≤ 1 / 4) (hfsmall : ‖duhamelOp hα hT f‖ ≤ ρ / 2)
    {r : ℕ} {Sf Rr : ℝ} (hSf0 : 0 ≤ Sf) (hRr0 : 0 ≤ Rr)
    (hSf : ∀ s : ℝ, WB r Sf (fun k => (sourceFun hT f s) k))
    (hRr : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB r Rr (curveState hT (picard hα hT hm hr f n) t).coeff)
    (habs : duhamelConst α T * (transportConst r C * ρ) ≤ 1 / 2)
    (n : ℕ) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      WB (r + 1)
        (2 * ((Sf + transportConst r C * (Rr * ρ)) * duhamelConst α T))
        (curveState hT (picard hα hT hm hr f n) t).coeff := by
  have hK0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  have hcc0 : (0:ℝ) ≤ transportConst r C := by
    have hC0 : (0:ℝ) ≤ C := nonneg_of_symbol_bound hC
    rw [transportConst]
    have := Real.pi_pos
    positivity
  set A : ℝ := (Sf + transportConst r C * (Rr * ρ)) * duhamelConst α T with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : (0:ℝ) ≤ transportConst r C * (Rr * ρ) := by positivity
    nlinarith
  induction n with
  | zero =>
    intro t ht F
    have hz : ∀ k : Gam, (curveState hT (picard hα hT hm hr f 0) t).coeff k = 0 := by
      intro k
      show (curveState hT (0 : Curve1 T) t).coeff k = 0
      rfl
    have : (∑ k ∈ F, wt k ^ (r + 1) * ‖(curveState hT (picard hα hT hm hr f 0) t).coeff k‖) = 0 := by
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [hz k, norm_zero, mul_zero]
    rw [this]
    linarith
  | succ n ih =>
    intro t ht
    -- the low-order bounds from the ball
    have hball : ∀ j : ℕ, ∀ s : ℝ, ‖curveState hT (picard hα hT hm hr f j) s‖ ≤ ρ := by
      intro j s
      exact le_trans (norm_curveState_le hT _ s) (picard_norm_le hb hb0 hρ0 hbρ hfsmall j)
    have h1 : ∀ s : ℝ, WB 1 ρ (curveState hT (picard hα hT hm hr f n) s).coeff :=
      fun s => (WB.wiener1 (curveState hT (picard hα hT hm hr f n) s)).mono (hball n s)
    have h0 : ∀ s : ℝ, WB 0 ρ (curveState hT (picard hα hT hm hr f n) s).coeff :=
      fun s => (h1 s).mono_exp (by omega)
    have hrb : ∀ s : ℝ, WB r Rr (curveState hT (picard hα hT hm hr f n) s).coeff :=
      WB_curveState_all (hRr n)
    have hr1 : ∀ s : ℝ, WB (r + 1) (2 * A) (curveState hT (picard hα hT hm hr f n) s).coeff :=
      WB_curveState_all (fun s hs => ih s hs)
    have hstep := WB_picardMap (hα := hα) (hT := hT) (hm := hm) (hr := hr) hC hSf h0 h1 hrb hr1 ht
    rw [← picard_succ] at hstep
    refine hstep.mono ?_
    have hexp : (Sf + transportConst r C * (Rr * ρ + ρ * (2 * A))) * duhamelConst α T
        = A + (duhamelConst α T * (transportConst r C * ρ)) * (2 * A) := by
      rw [hA]; ring
    rw [hexp]
    have : (duhamelConst α T * (transportConst r C * ρ)) * (2 * A) ≤ (1 / 2) * (2 * A) :=
      mul_le_mul_of_nonneg_right habs (by linarith)
    linarith

/-- **The higher-weight bound passes to the mild solution.** -/
theorem WB_mild_of_picard {f : Curve0 T} {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b)
    (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ) (hbρ : b * ρ ≤ 1 / 4) (hfsmall : ‖duhamelOp hα hT f‖ ≤ ρ / 2)
    {u : Curve1 T} (hu : ‖u‖ ≤ ρ)
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    {r : ℕ} {R : ℝ} {t : ℝ}
    (hiter : ∀ n : ℕ, WB r R (curveState hT (picard hα hT hm hr f n) t).coeff) :
    WB r R (curveState hT u t).coeff :=
  WB.of_tendsto
    (fun k => picard_tendsto_coeff hb hb0 hρ0 hbρ hfsmall hu hmild t k) hiter

end Picard

end LiWang.Formalization
