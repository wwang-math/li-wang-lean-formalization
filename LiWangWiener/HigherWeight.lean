/-
# Higher Wiener weights, as bounds rather than as new spaces

Step 3a of the v8.0 Sobolev-compatibility bridge.

To close the forward regularity needed by the observation bridge we need control of
`∑_k wt(k)^r |a_k|` for `r = 2, 3`, but we do **not** need new Banach spaces: every statement
below is a bound on *finite partial sums*,

    `WB r R a  ↔  ∀ F : Finset Gam, ∑_{k ∈ F} wt(k)^r ‖a k‖ ≤ R`,

which already implies summability (`WB.summable`) and the corresponding `tsum` bound
(`WB.tsum_le`), and which passes to limits along coefficientwise convergence
(`WB.of_tendsto`).  This is exactly the "finite Fourier sums and lower semicontinuity" route:
no convergence in a stronger norm is ever assumed.

The main estimate is `WB.conv_tame`, the **tame convolution bound**

    `∑_k wt(k)^r |(a ⋆ b)_k| ≤ 2^{r-1} ( ‖a‖_{W^r} ‖b‖_{W^0} + ‖a‖_{W^0} ‖b‖_{W^r} )`,

proved from `wt(p+q) ≤ wt p + wt q` and the packet's own shear/Tonelli lemmas for the Wiener
convolution.  The point is that only **one** factor carries the high weight, so the high norm
appears linearly: that is what lets the small `A¹` norm absorb it.

Part of `LiWangWienerSobolevCompatibilityPacket` v8.0.
-/
import LiWangWiener.SobolevCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology

namespace LiWang.WienerModel

/-! ## 1. The weighted bound predicate -/

/-- `WB r R a`: every finite partial sum of `wt(k)^r ‖a k‖` is at most `R`. -/
def WB (r : ℕ) (R : ℝ) (a : Gam → ℂ) : Prop :=
  ∀ F : Finset Gam, (∑ k ∈ F, wt k ^ r * ‖a k‖) ≤ R

theorem WB.nonneg {r : ℕ} {R : ℝ} {a : Gam → ℂ} (h : WB r R a) : 0 ≤ R := by
  have := h ∅
  simpa using this

theorem wt_pow_norm_nonneg (r : ℕ) (a : Gam → ℂ) (k : Gam) : 0 ≤ wt k ^ r * ‖a k‖ := by
  have := (wt_pos k).le
  positivity

theorem WB.summable {r : ℕ} {R : ℝ} {a : Gam → ℂ} (h : WB r R a) :
    Summable fun k => wt k ^ r * ‖a k‖ :=
  summable_of_finset_sum_le (fun k => wt_pow_norm_nonneg r a k) h

theorem WB.tsum_le {r : ℕ} {R : ℝ} {a : Gam → ℂ} (h : WB r R a) :
    (∑' k : Gam, wt k ^ r * ‖a k‖) ≤ R :=
  tsum_le_of_finset_sum_le (fun k => wt_pow_norm_nonneg r a k) h

theorem WB.of_summable {r : ℕ} {a : Gam → ℂ} (hs : Summable fun k => wt k ^ r * ‖a k‖)
    {R : ℝ} (h : (∑' k : Gam, wt k ^ r * ‖a k‖) ≤ R) : WB r R a := fun F =>
  le_trans (hs.sum_le_tsum F (fun k _ => wt_pow_norm_nonneg r a k)) h

theorem WB.mono {r : ℕ} {R R' : ℝ} {a : Gam → ℂ} (h : WB r R a) (hR : R ≤ R') : WB r R' a :=
  fun F => le_trans (h F) hR

theorem WB.of_norm_le {r : ℕ} {R : ℝ} {a b : Gam → ℂ} (h : WB r R b)
    (hab : ∀ k, ‖a k‖ ≤ ‖b k‖) : WB r R a := by
  intro F
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (h F)
  exact mul_le_mul_of_nonneg_left (hab k) (by have := (wt_pos k).le; positivity)

/-- Lowering the weight exponent is harmless, since `wt ≥ 1`. -/
theorem WB.mono_exp {r r' : ℕ} {R : ℝ} {a : Gam → ℂ} (h : WB r' R a) (hr : r ≤ r') :
    WB r R a := by
  intro F
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (h F)
  have h1 : (1:ℝ) ≤ wt k := one_le_wt k
  have : wt k ^ r ≤ wt k ^ r' := pow_le_pow_right₀ h1 hr
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

/-- The Wiener norm is the `r = 0` bound. -/
theorem WB.wiener (a : Wiener) : WB 0 ‖a‖ (a : Gam → ℂ) := by
  intro F
  have : (∑ k ∈ F, wt k ^ 0 * ‖a k‖) = ∑ k ∈ F, ‖a k‖ := by
    refine Finset.sum_congr rfl (fun k _ => by rw [pow_zero, one_mul])
  rw [this, wiener_norm_eq]
  exact (wiener_summable a).sum_le_tsum F (fun k _ => norm_nonneg _)

/-- The first-order norm is the `r = 1` bound. -/
theorem WB.wiener1 (u : Wiener1) : WB 1 ‖u‖ u.coeff := by
  intro F
  have : (∑ k ∈ F, wt k ^ 1 * ‖u.coeff k‖) = ∑ k ∈ F, wt k * ‖u.coeff k‖ := by
    refine Finset.sum_congr rfl (fun k _ => by rw [pow_one])
  rw [this, Wiener1.norm_eq]
  exact (Wiener1.summable_wt u).sum_le_tsum F
    (fun k _ => mul_nonneg (wt_pos k).le (norm_nonneg _))

/-- **Passage to a coefficientwise limit.**  A weighted bound valid for every member of a
sequence passes to any coefficientwise limit; only finite sums are involved, so no convergence
in a stronger norm is needed. -/
theorem WB.of_tendsto {r : ℕ} {R : ℝ} {a : ℕ → Gam → ℂ} {b : Gam → ℂ}
    (hlim : ∀ k, Tendsto (fun n => a n k) atTop (nhds (b k)))
    (h : ∀ n, WB r R (a n)) : WB r R b := by
  intro F
  have hcont : Tendsto (fun n => ∑ k ∈ F, wt k ^ r * ‖a n k‖) atTop
      (nhds (∑ k ∈ F, wt k ^ r * ‖b k‖)) := by
    refine tendsto_finset_sum F (fun k _ => ?_)
    exact ((hlim k).norm).const_mul _
  exact le_of_tendsto' hcont (fun n => h n F)

/-! ## 2. The tame convolution bound -/

theorem abs_add_le' (u v : ℝ) : |u + v| ≤ |u| + |v| := by
  rcases abs_cases (u + v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases u with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
      rcases abs_cases v with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> rw [h1, h2, h3] <;> linarith

theorem wt_add_le_wt (p q : Gam) : wt (p + q) ≤ wt p + wt q := by
  simp only [wt]
  have e0 : ((p + q) 0 : ℤ) = p 0 + q 0 := rfl
  have e1 : ((p + q) 1 : ℤ) = p 1 + q 1 := rfl
  rw [e0, e1]
  push_cast
  have a0 := abs_add_le' ((p 0 : ℤ) : ℝ) ((q 0 : ℤ) : ℝ)
  have a1 := abs_add_le' ((p 1 : ℤ) : ℝ) ((q 1 : ℤ) : ℝ)
  linarith

/-- `(x+y)^r ≤ 2^r (x^r + y^r)` for nonnegative `x, y`.  The constant is not sharp and does not
need to be. -/
theorem add_pow_le_two_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℕ) :
    (x + y) ^ r ≤ 2 ^ r * (x ^ r + y ^ r) := by
  have h4 : (0:ℝ) ≤ (2:ℝ) ^ r := by positivity
  rcases le_total x y with h | h
  · have h1 : x + y ≤ 2 * y := by linarith
    have h2 : (x + y) ^ r ≤ (2 * y) ^ r := pow_le_pow_left₀ (by linarith) h1 r
    rw [mul_pow] at h2
    have h3 : (0:ℝ) ≤ x ^ r := pow_nonneg hx r
    nlinarith
  · have h1 : x + y ≤ 2 * x := by linarith
    have h2 : (x + y) ^ r ≤ (2 * x) ^ r := pow_le_pow_left₀ (by linarith) h1 r
    rw [mul_pow] at h2
    have h3 : (0:ℝ) ≤ y ^ r := pow_nonneg hy r
    nlinarith

/-- The weight splitting used by the tame estimate. -/
theorem wt_pow_le_split (r : ℕ) (k p : Gam) :
    wt k ^ r ≤ 2 ^ r * (wt p ^ r + wt (k - p) ^ r) := by
  have hsum : wt k ≤ wt p + wt (k - p) := by
    have := wt_add_le_wt p (k - p)
    rwa [add_sub_cancel] at this
  have hk : (0:ℝ) ≤ wt k := (wt_pos k).le
  have hstep : wt k ^ r ≤ (wt p + wt (k - p)) ^ r :=
    pow_le_pow_left₀ hk hsum r
  exact le_trans hstep (add_pow_le_two_pow (wt_pos p).le (wt_pos (k - p)).le r)

/-- **The tame convolution bound.**  The high weight appears on only one factor at a time. -/
theorem WB.conv_tame {r : ℕ} {a b : Gam → ℂ} {Ra R0a Rb R0b : ℝ}
    (ha : WB r Ra a) (ha0 : WB 0 R0a a) (hb : WB r Rb b) (hb0 : WB 0 R0b b) :
    WB r (2 ^ r * (Ra * R0b + R0a * Rb)) (_root_.LiWang.WienerModel.convFun a b) := by
  classical
  set A : Gam → ℂ := fun p => ((wt p ^ r * ‖a p‖ : ℝ) : ℂ) with hA
  set A0 : Gam → ℂ := fun p => ((‖a p‖ : ℝ) : ℂ) with hA0
  set B : Gam → ℂ := fun q => ((wt q ^ r * ‖b q‖ : ℝ) : ℂ) with hB
  set B0 : Gam → ℂ := fun q => ((‖b q‖ : ℝ) : ℂ) with hB0
  have hnA : ∀ p, ‖A p‖ = wt p ^ r * ‖a p‖ := fun p => by
    rw [hA]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (wt_pow_norm_nonneg r a p)
  have hnA0 : ∀ p, ‖A0 p‖ = ‖a p‖ := fun p => by
    rw [hA0]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (norm_nonneg _)
  have hnB : ∀ q, ‖B q‖ = wt q ^ r * ‖b q‖ := fun q => by
    rw [hB]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (wt_pow_norm_nonneg r b q)
  have hnB0 : ∀ q, ‖B0 q‖ = ‖b q‖ := fun q => by
    rw [hB0]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (norm_nonneg _)
  have hsA : Summable fun p => ‖A p‖ := by
    simpa only [hnA] using ha.summable
  have hsA0 : Summable fun p => ‖A0 p‖ := by
    have := ha0.summable
    simp only [pow_zero, one_mul] at this
    simpa only [hnA0] using this
  have hsB : Summable fun q => ‖B q‖ := by
    simpa only [hnB] using hb.summable
  have hsB0 : Summable fun q => ‖B0 q‖ := by
    have := hb0.summable
    simp only [pow_zero, one_mul] at this
    simpa only [hnB0] using this
  -- the two majorant families
  set P : Gam → ℝ := fun k => ∑' p, ‖A p * B0 (k - p)‖ with hP
  set Q : Gam → ℝ := fun k => ∑' p, ‖A0 p * B (k - p)‖ with hQ
  have hPs : Summable P := summable_tsum_norm hsA hsB0
  have hQs : Summable Q := summable_tsum_norm hsA0 hsB
  have hsa : Summable fun p => ‖a p‖ := by
    have := ha0.summable
    simpa only [pow_zero, one_mul] using this
  have hsb : Summable fun q => ‖b q‖ := by
    have := hb0.summable
    simpa only [pow_zero, one_mul] using this
  have hPt : (∑' k, P k) ≤ Ra * R0b := by
    have hprod : (∑' k, P k) = (∑' k, ‖A k‖) * (∑' k, ‖B0 k‖) := by
      rw [hP, ← (summable_shear hsA hsB0).tsum_prod, tsum_shear hsA hsB0]
    rw [hprod]
    have h1 : (∑' k, ‖A k‖) ≤ Ra := by simpa only [hnA] using ha.tsum_le
    have h2 : (∑' k, ‖B0 k‖) ≤ R0b := by
      have := hb0.tsum_le
      simp only [pow_zero, one_mul] at this
      simpa only [hnB0] using this
    have hn1 : (0:ℝ) ≤ ∑' k, ‖A k‖ := tsum_nonneg (fun _ => norm_nonneg _)
    have hn2 : (0:ℝ) ≤ ∑' k, ‖B0 k‖ := tsum_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul h1 h2 hn2 (le_trans hn1 h1)
  have hQt : (∑' k, Q k) ≤ R0a * Rb := by
    have hprod : (∑' k, Q k) = (∑' k, ‖A0 k‖) * (∑' k, ‖B k‖) := by
      rw [hQ, ← (summable_shear hsA0 hsB).tsum_prod, tsum_shear hsA0 hsB]
    rw [hprod]
    have h1 : (∑' k, ‖A0 k‖) ≤ R0a := by
      have := ha0.tsum_le
      simp only [pow_zero, one_mul] at this
      simpa only [hnA0] using this
    have h2 : (∑' k, ‖B k‖) ≤ Rb := by simpa only [hnB] using hb.tsum_le
    have hn1 : (0:ℝ) ≤ ∑' k, ‖A0 k‖ := tsum_nonneg (fun _ => norm_nonneg _)
    have hn2 : (0:ℝ) ≤ ∑' k, ‖B k‖ := tsum_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul h1 h2 hn2 (le_trans hn1 h1)
  have h2r : (0:ℝ) ≤ 2 ^ r := by positivity
  -- the pointwise estimate
  have hkey : ∀ k : Gam, wt k ^ r * ‖_root_.LiWang.WienerModel.convFun a b k‖ ≤ 2 ^ r * (P k + Q k) := by
    intro k
    have hsum : Summable fun p => ‖a p * b (k - p)‖ := summable_convFun_norm hsa hsb k
    have hsum1 : Summable fun p => ‖A p * B0 (k - p)‖ := summable_convFun_norm hsA hsB0 k
    have hsum2 : Summable fun p => ‖A0 p * B (k - p)‖ := summable_convFun_norm hsA0 hsB k
    have hterm : ∀ p : Gam, wt k ^ r * ‖a p * b (k - p)‖
        ≤ 2 ^ r * (‖A p * B0 (k - p)‖ + ‖A0 p * B (k - p)‖) := by
      intro p
      have hsplit := wt_pow_le_split r k p
      have hab : (0:ℝ) ≤ ‖a p‖ * ‖b (k - p)‖ := by positivity
      have hL : ‖a p * b (k - p)‖ = ‖a p‖ * ‖b (k - p)‖ := norm_mul _ _
      have hR1 : ‖A p * B0 (k - p)‖ = (wt p ^ r * ‖a p‖) * ‖b (k - p)‖ := by
        rw [norm_mul, hnA, hnB0]
      have hR2 : ‖A0 p * B (k - p)‖ = ‖a p‖ * (wt (k - p) ^ r * ‖b (k - p)‖) := by
        rw [norm_mul, hnA0, hnB]
      rw [hL, hR1, hR2]
      nlinarith [hsplit, hab, norm_nonneg (a p), norm_nonneg (b (k - p))]
    calc wt k ^ r * ‖_root_.LiWang.WienerModel.convFun a b k‖
        ≤ wt k ^ r * ∑' p, ‖a p * b (k - p)‖ :=
          mul_le_mul_of_nonneg_left (norm_convFun_le hsa hsb k)
            (by have := (wt_pos k).le; positivity)
      _ = ∑' p, wt k ^ r * ‖a p * b (k - p)‖ := (tsum_mul_left).symm
      _ ≤ ∑' p, 2 ^ r * (‖A p * B0 (k - p)‖ + ‖A0 p * B (k - p)‖) :=
          Summable.tsum_le_tsum hterm (hsum.mul_left _) ((hsum1.add hsum2).mul_left _)
      _ = 2 ^ r * (P k + Q k) := by
          rw [tsum_mul_left, hP, hQ, Summable.tsum_add hsum1 hsum2]
  intro F
  have hstep1 : (∑ k ∈ F, wt k ^ r * ‖_root_.LiWang.WienerModel.convFun a b k‖)
      ≤ ∑ k ∈ F, 2 ^ r * (P k + Q k) :=
    Finset.sum_le_sum (fun k _ => hkey k)
  have hstep2 : (∑ k ∈ F, 2 ^ r * (P k + Q k))
      = 2 ^ r * ∑ k ∈ F, (P k + Q k) := by rw [Finset.mul_sum]
  have hPQnn : ∀ k : Gam, 0 ≤ P k + Q k := fun k =>
    add_nonneg (tsum_nonneg (fun _ => norm_nonneg _)) (tsum_nonneg (fun _ => norm_nonneg _))
  have hstep3 : (∑ k ∈ F, (P k + Q k)) ≤ ∑' k : Gam, (P k + Q k) :=
    (hPs.add hQs).sum_le_tsum F (fun k _ => hPQnn k)
  have hstep4 : (∑' k : Gam, (P k + Q k)) ≤ Ra * R0b + R0a * Rb := by
    rw [Summable.tsum_add hPs hQs]
    linarith [hPt, hQt]
  calc (∑ k ∈ F, wt k ^ r * ‖_root_.LiWang.WienerModel.convFun a b k‖)
      ≤ 2 ^ r * ∑ k ∈ F, (P k + Q k) := by rw [← hstep2]; exact hstep1
    _ ≤ 2 ^ r * (∑' k : Gam, (P k + Q k)) :=
        mul_le_mul_of_nonneg_left hstep3 h2r
    _ ≤ 2 ^ r * (Ra * R0b + R0a * Rb) := mul_le_mul_of_nonneg_left hstep4 h2r

end LiWang.WienerModel
