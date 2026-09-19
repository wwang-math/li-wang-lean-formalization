/-
# The `H³(𝕋²) ⊂ A¹(𝕋²)` embedding

Step 1a of the v8.0 Sobolev-compatibility bridge.

The paper's solutions live in Sobolev spaces; the packet's checked theory lives in the Wiener
algebra `A¹ = A¹_ℝ(𝕋²)` of absolutely summable Fourier coefficients with one derivative.  This
file proves the embedding that connects them, by Cauchy–Schwarz on the frequency lattice:

    ∑_k wt(k) |a_k| ≤ ( ∑_k wt(k)² / ρ(k)³ )^{1/2} ( ∑_k ρ(k)³ |a_k|² )^{1/2},
    ρ(k) = 1 + k₀² + k₁²,   wt(k) = 1 + |k₀| + |k₁|.

The lattice sum on the right is **proved** summable, not assumed: `wt(k)² ≤ 3ρ(k)` gives
`wt(k)²/ρ(k)³ ≤ 3/ρ(k)² ≤ 3/((1+k₀²)(1+k₁²))`, a product of two summable one-dimensional
sequences (`summable_gam_of_prod`).

Rather than invoke an infinite-dimensional Cauchy–Schwarz, the file uses the elementary
weighted arithmetic–geometric bound `wt|a| ≤ (2δ)⁻¹ wt²/ρ³ + (δ/2) ρ³|a|²`, valid for every
`δ > 0`, whose optimisation over `δ` recovers Cauchy–Schwarz exactly and which is what the
uniform tail estimate of `SobolevCurve.lean` actually needs.

The constructed object is a genuine `Wiener1` element (`sobToWiener1`) whose coefficients are
the given ones **by definition**, and whose physical synthesis is proved equal to the given
`L²(𝕋²)` state (`synthL2_sobToWiener1`, using the completeness of the trigonometric system).
Reality is carried through conjugate symmetry.

Part of `LiWangWienerSobolevCompatibilityPacket` v8.0.
-/
import LiWangWiener.FourierCompleteness
import LiWangWiener.SmoothPeriodic
import LiWangWiener.FractionalRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

/-! ## 1. The Sobolev weight `ρ(k) = 1 + |k|²` -/

/-- The integer Sobolev weight `ρ(k) = 1 + k₀² + k₁²`. -/
noncomputable def rho (k : Gam) : ℝ := 1 + sqNorm k

theorem one_le_rho (k : Gam) : 1 ≤ rho k := by
  have := sqNorm_nonneg k
  rw [rho]; linarith

theorem rho_pos (k : Gam) : 0 < rho k := lt_of_lt_of_le zero_lt_one (one_le_rho k)

theorem rho_eq (k : Gam) : rho k = 1 + ((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2 := by
  rw [rho, sqNorm]; ring

/-- `ρ(k)³` is the integer power of the real Sobolev weight `sobWeight 3`. -/
theorem sobWeight_three_eq (k : Gam) : sobWeight 3 k = rho k ^ 3 := by
  rw [sobWeight, rho, show (3:ℝ) = ((3:ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast]

/-- **`wt(k)² ≤ 3 ρ(k)`** — Cauchy–Schwarz for the three-term vector `(1, |k₀|, |k₁|)`. -/
theorem wt_sq_le_three_rho (k : Gam) : wt k ^ 2 ≤ 3 * rho k := by
  have ha : |((k 0 : ℤ) : ℝ)| ^ 2 = ((k 0 : ℤ) : ℝ) ^ 2 := sq_abs _
  have hb : |((k 1 : ℤ) : ℝ)| ^ 2 = ((k 1 : ℤ) : ℝ) ^ 2 := sq_abs _
  have h0 : (0:ℝ) ≤ |((k 0 : ℤ) : ℝ)| := abs_nonneg _
  have h1 : (0:ℝ) ≤ |((k 1 : ℤ) : ℝ)| := abs_nonneg _
  rw [wt, rho_eq, ← ha, ← hb]
  nlinarith [sq_nonneg (1 - |((k 0 : ℤ) : ℝ)|), sq_nonneg (1 - |((k 1 : ℤ) : ℝ)|),
    sq_nonneg (|((k 0 : ℤ) : ℝ)| - |((k 1 : ℤ) : ℝ)|)]

/-- **`(1 + k₀²)(1 + k₁²) ≤ ρ(k)²`**. -/
theorem prod_le_rho_sq (k : Gam) :
    (1 + ((k 0 : ℤ) : ℝ) ^ 2) * (1 + ((k 1 : ℤ) : ℝ) ^ 2) ≤ rho k ^ 2 := by
  have h0 : (0:ℝ) ≤ ((k 0 : ℤ) : ℝ) ^ 2 := sq_nonneg _
  have h1 : (0:ℝ) ≤ ((k 1 : ℤ) : ℝ) ^ 2 := sq_nonneg _
  rw [rho_eq]
  nlinarith [sq_nonneg (((k 0 : ℤ) : ℝ) ^ 2), sq_nonneg (((k 1 : ℤ) : ℝ) ^ 2)]

/-- **The pointwise majorant of the embedding kernel.** -/
theorem wtsq_div_rho3_le (k : Gam) :
    wt k ^ 2 / rho k ^ 3
      ≤ 3 * ((1 / (1 + ((k 0 : ℤ) : ℝ) ^ 2)) * (1 / (1 + ((k 1 : ℤ) : ℝ) ^ 2))) := by
  have hρ : 0 < rho k := rho_pos k
  have hρ3 : (0:ℝ) < rho k ^ 3 := by positivity
  have hp0 : (0:ℝ) < 1 + ((k 0 : ℤ) : ℝ) ^ 2 := by positivity
  have hp1 : (0:ℝ) < 1 + ((k 1 : ℤ) : ℝ) ^ 2 := by positivity
  have hprod : (0:ℝ) < (1 + ((k 0 : ℤ) : ℝ) ^ 2) * (1 + ((k 1 : ℤ) : ℝ) ^ 2) :=
    mul_pos hp0 hp1
  have hstep1 : wt k ^ 2 / rho k ^ 3 ≤ 3 / rho k ^ 2 := by
    rw [div_le_div_iff₀ hρ3 (by positivity)]
    have := wt_sq_le_three_rho k
    nlinarith [pow_pos hρ 2, sq_nonneg (rho k)]
  have hstep2 : (3:ℝ) / rho k ^ 2 ≤ 3 / ((1 + ((k 0 : ℤ) : ℝ) ^ 2) * (1 + ((k 1 : ℤ) : ℝ) ^ 2)) :=
    div_le_div_of_nonneg_left (by norm_num) hprod (prod_le_rho_sq k)
  have hrewrite : (3:ℝ) / ((1 + ((k 0 : ℤ) : ℝ) ^ 2) * (1 + ((k 1 : ℤ) : ℝ) ^ 2))
      = 3 * ((1 / (1 + ((k 0 : ℤ) : ℝ) ^ 2)) * (1 / (1 + ((k 1 : ℤ) : ℝ) ^ 2))) := by
    field_simp
  rw [hrewrite] at hstep2
  linarith

theorem wtsq_div_rho3_nonneg (k : Gam) : 0 ≤ wt k ^ 2 / rho k ^ 3 :=
  div_nonneg (sq_nonneg _) (by have := (rho_pos k).le; positivity)

/-! ## 2. The lattice summability -/

theorem summable_int_one_div_one_add_sq :
    Summable (fun n : ℤ => 1 / (1 + ((n : ℤ) : ℝ) ^ 2)) := by
  have hmaj : Summable fun n : ℤ => (if n = 0 then (1:ℝ) else 0) + 1 / ((n : ℝ) ^ 2) := by
    refine Summable.add ?_ (Real.summable_one_div_int_pow.2 (by norm_num))
    exact summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) (fun b hb => by
      rw [if_neg (by simpa using hb)])
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  by_cases hn : n = 0
  · subst hn; norm_num
  · have hn2 : (0:ℝ) < ((n : ℤ) : ℝ) ^ 2 := by
      have : ((n : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
      positivity
    have h1 : 1 / (1 + ((n : ℤ) : ℝ) ^ 2) ≤ 1 / ((n : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le hn2
      linarith
    rw [if_neg hn]
    linarith

/-- **The embedding kernel is summable over the frequency lattice.**  Proved, not assumed. -/
theorem summable_wtsq_div_rho3 : Summable (fun k : Gam => wt k ^ 2 / rho k ^ 3) := by
  have hmaj : Summable (fun k : Gam =>
      (3 * (1 / (1 + ((k 0 : ℤ) : ℝ) ^ 2))) * (1 / (1 + ((k 1 : ℤ) : ℝ) ^ 2))) :=
    summable_gam_of_prod (f := fun n : ℤ => 3 * (1 / (1 + ((n : ℤ) : ℝ) ^ 2)))
      (g := fun n : ℤ => 1 / (1 + ((n : ℤ) : ℝ) ^ 2))
      (summable_int_one_div_one_add_sq.mul_left 3) summable_int_one_div_one_add_sq
      (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_nonneg_of_le (fun k => wtsq_div_rho3_nonneg k) (fun k => ?_) hmaj
  have h := wtsq_div_rho3_le k
  calc wt k ^ 2 / rho k ^ 3
      ≤ 3 * ((1 / (1 + ((k 0 : ℤ) : ℝ) ^ 2)) * (1 / (1 + ((k 1 : ℤ) : ℝ) ^ 2))) := h
    _ = (3 * (1 / (1 + ((k 0 : ℤ) : ℝ) ^ 2))) * (1 / (1 + ((k 1 : ℤ) : ℝ) ^ 2)) := by ring

/-! ## 3. The weighted arithmetic–geometric bound -/

/-- **The `δ`-weighted embedding bound.**  Optimising over `δ` gives exactly Cauchy–Schwarz;
what the uniform tail estimate needs is this family of bounds with `δ` at our disposal. -/
theorem wt_mul_norm_le (c : Gam → ℂ) {δ : ℝ} (hδ : 0 < δ) (k : Gam) :
    wt k * ‖c k‖
      ≤ (1 / (2 * δ)) * (wt k ^ 2 / rho k ^ 3) + (δ / 2) * (rho k ^ 3 * ‖c k‖ ^ 2) := by
  have hρp : (0:ℝ) < rho k := rho_pos k
  have hρ : (0:ℝ) < rho k ^ 3 := by positivity
  have hρ0 : rho k ≠ 0 := ne_of_gt hρp
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  rw [← sub_nonneg]
  have hid : (1 / (2 * δ)) * (wt k ^ 2 / rho k ^ 3) + (δ / 2) * (rho k ^ 3 * ‖c k‖ ^ 2)
      - wt k * ‖c k‖
      = (1 / (2 * δ * rho k ^ 3)) * (wt k - δ * rho k ^ 3 * ‖c k‖) ^ 2 := by
    field_simp
    ring
  rw [hid]
  positivity

/-! ## 4. The embedding -/

/-- **`H³ ⊂ A¹`.**  A coefficient family with finite `H³` energy is absolutely summable against
the first-order weight. -/
theorem summable_wt_mul_norm {c : Gam → ℂ}
    (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2) :
    Summable fun k => wt k * ‖c k‖ := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => wt_mul_norm_le c one_pos k) ?_
  exact (summable_wtsq_div_rho3.mul_left (1 / (2 * 1))).add (h.mul_left (1 / 2))

/-- The same statement in terms of the packet's `MemSobolev` predicate. -/
theorem summable_wt_mul_norm_of_memSobolev {c : Gam → ℂ} (h : MemSobolev 3 c) :
    Summable fun k => wt k * ‖c k‖ := by
  refine summable_wt_mul_norm ?_
  have : (fun k : Gam => rho k ^ 3 * ‖c k‖ ^ 2) = fun k => sobWeight 3 k * ‖c k‖ ^ 2 := by
    funext k; rw [sobWeight_three_eq]
  rw [this]
  exact h

/-- **The `A¹` element of an `H³` coefficient family.**  Its coefficients are the given ones by
definition; nothing is modified. -/
noncomputable def sobToWiener1 {c : Gam → ℂ} (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2) :
    Wiener1 := Wiener1.mk c (summable_wt_mul_norm h)

@[simp] theorem sobToWiener1_coeff {c : Gam → ℂ}
    (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2) : (sobToWiener1 h).coeff = c := rfl

/-- **Realness is carried through conjugate symmetry.** -/
noncomputable def sobToRealWiener1 {c : Gam → ℂ}
    (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2) (hc : ConjSymmetric c) : RealWiener1 :=
  RealWiener1.mk (sobToWiener1 h) hc

@[simp] theorem sobToRealWiener1_val {c : Gam → ℂ}
    (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2) (hc : ConjSymmetric c) :
    (sobToRealWiener1 h hc).val = sobToWiener1 h := rfl

/-- **Agreement with the physical state.**  If the `L²(𝕋²)` class `θ` has exactly these Fourier
coefficients then its synthesis from the constructed `A¹` element *is* `θ` — an equality in
`L²(𝕋²)`, obtained from completeness of the trigonometric system, not by redefining `θ`. -/
theorem synthL2_sobToWiener1 {c : Gam → ℂ} (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2)
    {θ : TorusL2} (hθ : ∀ k : Gam, l2coeff k θ = c k) :
    synthL2 (incl (sobToWiener1 h)) = θ :=
  synthL2_incl_eq_of_coeff (w := sobToWiener1 h) (fun k => hθ k)

/-- The norm bound behind the embedding, with the explicit `δ`-family of constants. -/
theorem norm_sobToWiener1_le {c : Gam → ℂ} (h : Summable fun k => rho k ^ 3 * ‖c k‖ ^ 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖sobToWiener1 h‖
      ≤ (1 / (2 * δ)) * (∑' k : Gam, wt k ^ 2 / rho k ^ 3)
        + (δ / 2) * ∑' k : Gam, rho k ^ 3 * ‖c k‖ ^ 2 := by
  rw [Wiener1.norm_eq]
  have hle : ∀ k : Gam, wt k * ‖(sobToWiener1 h).coeff k‖
      ≤ (1 / (2 * δ)) * (wt k ^ 2 / rho k ^ 3) + (δ / 2) * (rho k ^ 3 * ‖c k‖ ^ 2) :=
    fun k => wt_mul_norm_le c hδ k
  have hsum : Summable fun k : Gam =>
      (1 / (2 * δ)) * (wt k ^ 2 / rho k ^ 3) + (δ / 2) * (rho k ^ 3 * ‖c k‖ ^ 2) :=
    (summable_wtsq_div_rho3.mul_left _).add (h.mul_left _)
  have heq : (∑' k : Gam,
        ((1 / (2 * δ)) * (wt k ^ 2 / rho k ^ 3) + (δ / 2) * (rho k ^ 3 * ‖c k‖ ^ 2)))
      = (1 / (2 * δ)) * (∑' k : Gam, wt k ^ 2 / rho k ^ 3)
        + (δ / 2) * ∑' k : Gam, rho k ^ 3 * ‖c k‖ ^ 2 := by
    rw [Summable.tsum_add (summable_wtsq_div_rho3.mul_left _) (h.mul_left _),
      tsum_mul_left, tsum_mul_left]
  rw [← heq]
  exact Summable.tsum_le_tsum hle (summable_wt_mul_norm h) hsum

end LiWang.WienerModel
