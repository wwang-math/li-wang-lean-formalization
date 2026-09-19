/-
# The paper's source class, and its higher-weight bounds

`paperSources hT W` is the submodule of source curves whose physical space-time field is a
`C_c^∞(W × (0,T))` datum — by `PaperSourceRealization` this is exactly the class of sources the
paper's map (1.6) is defined on.  This module proves:

* uniform-in-time `wt`- and `wt³`-weighted bounds for the Fourier data of a paper field, from
  the time-uniform fourth-order decay of `SpacetimeCalculus`;
* hence `HasHigherBound3` for **every** admissible paper source, so that paper solutions exist on
  the whole class;
* `smoothSources hT W ≤ paperSources hT W`, with every realization in the larger class;
* monotonicity of the measurement hypothesis: equality of the paper maps on the larger class
  implies it on the smaller, because the canonical solutions of the two classes agree by
  uniqueness.

Part of `LiWangWienerPaperSourceRealizationPacket` v10.0.
-/
import LiWangWiener.PaperSourceRealization
import LiWangWiener.SmoothThirdOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.WienerModel

variable {T : ℝ}

/-! ## 1. Periodicity and support of the second spatial derivatives -/

theorem per0_spd0_two {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y))) (t x y : ℝ) :
    spd0 (spd0 Φ) (t, (x + 1, y)) = spd0 (spd0 Φ) (t, (x, y)) := by
  have hsl : slice (spd0 (spd0 Φ)) t = pd0 (pd0 (slice Φ t)) := by
    rw [slice_spd0 (contDiff_spd0 hsm) t, slice_spd0 hsm t]
  show slice (spd0 (spd0 Φ)) t (x + 1, y) = slice (spd0 (spd0 Φ)) t (x, y)
  rw [hsl]
  exact ((isSmoothPeriodic_slice hsm hper0 hper1 t).pd0'.pd0').per0 (x, y)

theorem per1_spd0_two {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y))) (t x y : ℝ) :
    spd0 (spd0 Φ) (t, (x, y + 1)) = spd0 (spd0 Φ) (t, (x, y)) := by
  have hsl : slice (spd0 (spd0 Φ)) t = pd0 (pd0 (slice Φ t)) := by
    rw [slice_spd0 (contDiff_spd0 hsm) t, slice_spd0 hsm t]
  show slice (spd0 (spd0 Φ)) t (x, y + 1) = slice (spd0 (spd0 Φ)) t (x, y)
  rw [hsl]
  exact ((isSmoothPeriodic_slice hsm hper0 hper1 t).pd0'.pd0').per1 (x, y)

theorem per0_spd1_two {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y))) (t x y : ℝ) :
    spd1 (spd1 Φ) (t, (x + 1, y)) = spd1 (spd1 Φ) (t, (x, y)) := by
  have hsl : slice (spd1 (spd1 Φ)) t = pd1 (pd1 (slice Φ t)) := by
    rw [slice_spd1 (contDiff_spd1 hsm) t, slice_spd1 hsm t]
  show slice (spd1 (spd1 Φ)) t (x + 1, y) = slice (spd1 (spd1 Φ)) t (x, y)
  rw [hsl]
  exact ((isSmoothPeriodic_slice hsm hper0 hper1 t).pd1'.pd1').per0 (x, y)

theorem per1_spd1_two {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y))) (t x y : ℝ) :
    spd1 (spd1 Φ) (t, (x, y + 1)) = spd1 (spd1 Φ) (t, (x, y)) := by
  have hsl : slice (spd1 (spd1 Φ)) t = pd1 (pd1 (slice Φ t)) := by
    rw [slice_spd1 (contDiff_spd1 hsm) t, slice_spd1 hsm t]
  show slice (spd1 (spd1 Φ)) t (x, y + 1) = slice (spd1 (spd1 Φ)) t (x, y)
  rw [hsl]
  exact ((isSmoothPeriodic_slice hsm hper0 hper1 t).pd1'.pd1').per1 (x, y)

/-! ## 2. Uniform weighted bounds on the Fourier data of a paper field -/

/-- **The first-order weighted coefficient sum of the slices is bounded uniformly in time.** -/
theorem exists_uniform_wt_bound {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y)))
    {a₀ a₁ : ℝ} (ha01 : a₀ ≤ a₁)
    (hav : ∀ t ∉ Set.Icc a₀ a₁, ∀ p, Φ (t, p) = 0) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (t : ℝ) (F : Finset Gam),
      (∑ k ∈ F, wt k * ‖pcoeff (slice Φ t) k‖) ≤ S := by
  obtain ⟨C, hC0, hdec⟩ := exists_uniform_pcoeff_decay4 hsm hper0 hper1 ha01 hav
  set maj : Gam → ℝ := fun k => (4 * C) * decayWeight (k 0) * decayWeight (k 1) with hmajdef
  have hmaj0 : ∀ k, 0 ≤ maj k := by
    intro k
    rw [hmajdef]
    exact mul_nonneg (mul_nonneg (by linarith) (decayWeight_pos _).le) (decayWeight_pos _).le
  have hmajsum : Summable maj :=
    summable_gam_of_prod (f := fun n => (4 * C) * decayWeight n) (g := decayWeight)
      (summable_decayWeight.mul_left (4 * C)) summable_decayWeight
      (fun n => mul_nonneg (by linarith) (decayWeight_pos n).le)
      (fun n => (decayWeight_pos n).le)
  refine ⟨∑' k : Gam, maj k, tsum_nonneg hmaj0, fun t F => ?_⟩
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_))
    (hmajsum.sum_le_tsum F (fun k _ => hmaj0 k))
  have hk : wt k * ‖pcoeff (slice Φ t) k‖
      ≤ ((1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|))
        * (C * (decayWeight4 (k 0) * decayWeight4 (k 1))) := by
    refine mul_le_mul (wt_le_prod k) (hdec t k) (norm_nonneg _) ?_
    have h0 := abs_nonneg ((k 0 : ℤ) : ℝ)
    have h1 := abs_nonneg ((k 1 : ℤ) : ℝ)
    nlinarith
  refine le_trans hk ?_
  have e : ((1 + |((k 0 : ℤ) : ℝ)|) * (1 + |((k 1 : ℤ) : ℝ)|))
        * (C * (decayWeight4 (k 0) * decayWeight4 (k 1)))
      = C * (((1 + |((k 0 : ℤ) : ℝ)|) * decayWeight4 (k 0))
          * ((1 + |((k 1 : ℤ) : ℝ)|) * decayWeight4 (k 1))) := by ring
  rw [e]
  have hA := weighted_decayWeight4_le (k 0)
  have hB := weighted_decayWeight4_le (k 1)
  have hB0 : (0:ℝ) ≤ (1 + |((k 1 : ℤ) : ℝ)|) * decayWeight4 (k 1) :=
    mul_nonneg (by positivity) (decayWeight4_pos _).le
  have hd0 : (0:ℝ) ≤ decayWeight (k 0) := (decayWeight_pos _).le
  have hstep : C * (((1 + |((k 0 : ℤ) : ℝ)|) * decayWeight4 (k 0))
        * ((1 + |((k 1 : ℤ) : ℝ)|) * decayWeight4 (k 1)))
      ≤ C * ((2 * decayWeight (k 0)) * (2 * decayWeight (k 1))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hA hB hB0 (by linarith)) hC0
  have hfin : C * ((2 * decayWeight (k 0)) * (2 * decayWeight (k 1))) = maj k := by
    simp only [hmajdef]; ring
  linarith

/-- **The third-order weighted coefficient sum of the slices is bounded uniformly in time.**
Two derivatives buy one factor of `ρ`, exactly as in `SmoothThirdOrder`, and the derivatives of
a paper field are again paper fields. -/
theorem exists_uniform_WB3 {Φ : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ Φ)
    (hper0 : ∀ (t x y : ℝ), Φ (t, (x + 1, y)) = Φ (t, (x, y)))
    (hper1 : ∀ (t x y : ℝ), Φ (t, (x, y + 1)) = Φ (t, (x, y)))
    {a₀ a₁ : ℝ} (ha01 : a₀ ≤ a₁)
    (hav : ∀ t ∉ Set.Icc a₀ a₁, ∀ p, Φ (t, p) = 0) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t : ℝ, WB 3 S (fun k => pcoeff (slice Φ t) k) := by
  obtain ⟨S0, hS00, hS0⟩ := exists_uniform_wt_bound hsm hper0 hper1 ha01 hav
  obtain ⟨S1, hS10, hS1⟩ := exists_uniform_wt_bound (contDiff_spd0 (contDiff_spd0 hsm))
    (per0_spd0_two hsm hper0 hper1) (per1_spd0_two hsm hper0 hper1) ha01
    (fun t ht => spd0_vanishes (contDiff_spd0 hsm) (spd0_vanishes hsm (hav t ht)))
  obtain ⟨S2, hS20, hS2⟩ := exists_uniform_wt_bound (contDiff_spd1 (contDiff_spd1 hsm))
    (per0_spd1_two hsm hper0 hper1) (per1_spd1_two hsm hper0 hper1) ha01
    (fun t ht => spd1_vanishes (contDiff_spd1 hsm) (spd1_vanishes hsm (hav t ht)))
  have hpi : (1:ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  refine ⟨3 * (S0 + S1 + S2), by linarith, fun t F => ?_⟩
  have hsl0 : slice (spd0 (spd0 Φ)) t = pd0 (pd0 (slice Φ t)) := by
    rw [slice_spd0 (contDiff_spd0 hsm) t, slice_spd0 hsm t]
  have hsl1 : slice (spd1 (spd1 Φ)) t = pd1 (pd1 (slice Φ t)) := by
    rw [slice_spd1 (contDiff_spd1 hsm) t, slice_spd1 hsm t]
  have hterm : ∀ k : Gam, wt k ^ 3 * ‖pcoeff (slice Φ t) k‖
      ≤ 3 * (wt k * ‖pcoeff (slice Φ t) k‖
        + wt k * ‖pcoeff (slice (spd0 (spd0 Φ)) t) k‖
        + wt k * ‖pcoeff (slice (spd1 (spd1 Φ)) t) k‖) := by
    intro k
    have hwt : (0:ℝ) < wt k := wt_pos k
    have hn : (0:ℝ) ≤ ‖pcoeff (slice Φ t) k‖ := norm_nonneg _
    have hsq : wt k ^ 2 ≤ 3 * rho k := wt_sq_le_three_rho k
    have hrho : rho k = 1 + ((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2 := rho_eq k
    have e0 : ‖pcoeff (slice (spd0 (spd0 Φ)) t) k‖
        = 4 * Real.pi ^ 2 * ((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖ := by
      rw [hsl0]
      exact norm_pcoeff_pd0_two (isSmoothPeriodic_slice hsm hper0 hper1 t) k
    have e1 : ‖pcoeff (slice (spd1 (spd1 Φ)) t) k‖
        = 4 * Real.pi ^ 2 * ((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖ := by
      rw [hsl1]
      exact norm_pcoeff_pd1_two (isSmoothPeriodic_slice hsm hper0 hper1 t) k
    have hx0 : (0:ℝ) ≤ ((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖ :=
      mul_nonneg (sq_nonneg _) hn
    have hx1 : (0:ℝ) ≤ ((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖ :=
      mul_nonneg (sq_nonneg _) hn
    have hb0 : ((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖
        ≤ ‖pcoeff (slice (spd0 (spd0 Φ)) t) k‖ := by
      rw [e0]
      calc ((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖
          = 1 * (((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖) := (one_mul _).symm
        _ ≤ (4 * Real.pi ^ 2) * (((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖) :=
            mul_le_mul_of_nonneg_right hpi hx0
        _ = 4 * Real.pi ^ 2 * ((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖ := by ring
    have hb1 : ((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖
        ≤ ‖pcoeff (slice (spd1 (spd1 Φ)) t) k‖ := by
      rw [e1]
      calc ((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖
          = 1 * (((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖) := (one_mul _).symm
        _ ≤ (4 * Real.pi ^ 2) * (((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖) :=
            mul_le_mul_of_nonneg_right hpi hx1
        _ = 4 * Real.pi ^ 2 * ((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖ := by ring
    have hstep : wt k ^ 2 * ‖pcoeff (slice Φ t) k‖ ≤ (3 * rho k) * ‖pcoeff (slice Φ t) k‖ :=
      mul_le_mul_of_nonneg_right hsq hn
    have hstep2 : wt k * (wt k ^ 2 * ‖pcoeff (slice Φ t) k‖)
        ≤ wt k * ((3 * rho k) * ‖pcoeff (slice Φ t) k‖) :=
      mul_le_mul_of_nonneg_left hstep hwt.le
    have hL : wt k ^ 3 * ‖pcoeff (slice Φ t) k‖
        = wt k * (wt k ^ 2 * ‖pcoeff (slice Φ t) k‖) := by ring
    have hR : wt k * ((3 * rho k) * ‖pcoeff (slice Φ t) k‖)
        = 3 * (wt k * ‖pcoeff (slice Φ t) k‖
          + wt k * (((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖)
          + wt k * (((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖)) := by
      rw [hrho]; ring
    have hcube : wt k ^ 3 * ‖pcoeff (slice Φ t) k‖
        ≤ 3 * (wt k * ‖pcoeff (slice Φ t) k‖
          + wt k * (((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖)
          + wt k * (((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖)) := by
      rw [hL, ← hR]; exact hstep2
    have hm0 : wt k * (((k 0 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖)
        ≤ wt k * ‖pcoeff (slice (spd0 (spd0 Φ)) t) k‖ :=
      mul_le_mul_of_nonneg_left hb0 hwt.le
    have hm1 : wt k * (((k 1 : ℤ) : ℝ) ^ 2 * ‖pcoeff (slice Φ t) k‖)
        ≤ wt k * ‖pcoeff (slice (spd1 (spd1 Φ)) t) k‖ :=
      mul_le_mul_of_nonneg_left hb1 hwt.le
    linarith
  calc (∑ k ∈ F, wt k ^ 3 * ‖pcoeff (slice Φ t) k‖)
      ≤ ∑ k ∈ F, 3 * (wt k * ‖pcoeff (slice Φ t) k‖
        + wt k * ‖pcoeff (slice (spd0 (spd0 Φ)) t) k‖
        + wt k * ‖pcoeff (slice (spd1 (spd1 Φ)) t) k‖) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = 3 * ((∑ k ∈ F, wt k * ‖pcoeff (slice Φ t) k‖)
        + (∑ k ∈ F, wt k * ‖pcoeff (slice (spd0 (spd0 Φ)) t) k‖)
        + ∑ k ∈ F, wt k * ‖pcoeff (slice (spd1 (spd1 Φ)) t) k‖) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ ≤ 3 * (S0 + S1 + S2) := by
        have := hS0 t F
        have := hS1 t F
        have := hS2 t F
        linarith

/-! ## 3. `HasHigherBound3` for every admissible paper source -/

/-- The instantaneous source of a curve with a space-time representative is the Wiener element
of the corresponding slice. -/
theorem sourceFun_eq_of_rep {hT : 0 < T} {W : Set Torus2} {V : Curve0 T}
    {Φ : ℝ × (ℝ × ℝ) → ℂ} (h : SmoothSpacetimeRep hT W V Φ) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    sourceFun hT.le V t
      = wienerOfSmooth (slice Φ t) (isSmoothPeriodic_slice h.smooth h.per0 h.per1 t) := by
  refine planeLift_injective ?_
  rw [planeLift_wienerOfSmooth]
  funext p
  obtain ⟨y0, y1⟩ := p
  have hag := h.agrees t ht ![y0, y1]
  rw [sourcePhys] at hag
  show lift (sourceFun hT.le V t) ![y0, y1] = Φ (t, (y0, y1))
  rw [lift_def]
  exact hag

/-- **Every admissible paper source carries the third-order bound.** -/
theorem hasHigherBound3_of_isPaperSource {hT : 0 < T} {W : Set Torus2} {V : Curve0 T}
    (h : IsPaperSource hT W V) : HasHigherBound3 hT.le V := by
  obtain ⟨Φ, hrep⟩ := h
  obtain ⟨a₀, a₁, -, ha01, -, hav⟩ := hrep.timeSupp
  obtain ⟨S, hS0, hS⟩ := exists_uniform_WB3 hrep.smooth hrep.per0 hrep.per1 ha01 hav
  have hcoeff : ∀ (s : ℝ) (k : Gam),
      (sourceFun hT.le V s) k = pcoeff (slice Φ ((clampT hT.le s : TimeI T) : ℝ)) k := by
    intro s k
    have hcl : clampT hT.le ((clampT hT.le s : TimeI T) : ℝ) = clampT hT.le s :=
      Subtype.ext (clampT_coe hT.le (clampT hT.le s).2.1 (clampT hT.le s).2.2)
    have hid : sourceFun hT.le V ((clampT hT.le s : TimeI T) : ℝ) = sourceFun hT.le V s := by
      show (V (clampT hT.le ((clampT hT.le s : TimeI T) : ℝ))).val = (V (clampT hT.le s)).val
      rw [hcl]
    rw [← hid, sourceFun_eq_of_rep hrep (clampT hT.le s).2]
    rfl
  have hWB : ∀ s : ℝ, WB 3 S (fun k => (sourceFun hT.le V s) k) := by
    intro s
    exact (hS ((clampT hT.le s : TimeI T) : ℝ)).of_norm_le
      (fun k => le_of_eq (by rw [hcoeff s k]))
  exact ⟨S, hS0, fun s => (hWB s).mono_exp (by norm_num),
    fun s => (hWB s).mono_exp (by norm_num), hWB⟩

/-! ## 4. The paper source class -/

/-- **The paper's source class**: the source curves whose physical space-time field is a real
`C^∞` function compactly supported in `W × (0,T)`.  By `PaperSourceRealization` every such
field is realized, so this is exactly `C_c^∞(W × (0,T))` viewed inside `Curve0 T`. -/
def paperSources (hT : 0 < T) (W : Set Torus2) : Submodule ℝ (Curve0 T) where
  carrier := {V | IsPaperSource hT W V}
  add_mem' := by
    rintro V V' ⟨Φ, h⟩ ⟨Φ', h'⟩
    exact ⟨_, h.add h'⟩
  zero_mem' := ⟨_, SmoothSpacetimeRep.zero hT W⟩
  smul_mem' := by
    rintro r V ⟨Φ, h⟩
    exact ⟨_, h.smul r⟩

@[simp] theorem mem_paperSources (hT : 0 < T) (W : Set Torus2) (V : Curve0 T) :
    V ∈ paperSources hT W ↔ IsPaperSource hT W V := Iff.rfl

/-- **The packet's smooth sources are paper sources.** -/
theorem smoothSources_le_paperSources (hT : 0 < T) (W : Set Torus2) :
    smoothSources hT W ≤ paperSources hT W :=
  fun _ hV => isPaperSource_of_mem_smoothSources hT hV

/-- **Every paper datum is realized inside the class.** -/
theorem paperCurve_mem_paperSources {hT : 0 < T} {W : Set Torus2} {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (h : IsPaperField hT W Φ) : paperCurve h ∈ paperSources hT W :=
  isPaperSource_paperCurve h

variable {α : ℝ} {m : Fin 2 → Gam → ℂ}

/-- **Paper solutions exist on the whole paper source class**, with a uniform positive radius. -/
theorem exists_paperExistence_paperSources (hα : 1 / 2 < α) (hα1 : α < 1) (hT : 0 < T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (W : Set Torus2) :
    ∃ ε > 0, PaperExistence hα hT hm (paperSources hT W) ε :=
  exists_paperExistence_of_higherBound3 hα hα1 hT hm hr hC (paperSources hT W)
    (fun _ hf => hasHigherBound3_of_isPaperSource hf)

/-! ## 5. Restricting the measurement hypothesis to a smaller source class -/

theorem PaperExistence.mono {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m}
    {A : Submodule ℝ (Curve0 T)} {ε ε' : ℝ} (hle : ε' ≤ ε)
    (h : PaperExistence hα hT hm A ε) : PaperExistence hα hT hm A ε' :=
  fun f hf hs => h f hf (lt_of_lt_of_le hs hle)

/-- **Equality of the paper maps on a larger source class implies it on a smaller one.**  The
canonical solutions of the two classes need not be the same witness, but they agree by the
uniqueness theorem, so the observations coincide. -/
theorem paperObsMapsAgree_mono {hα : 1 / 2 < α} {hT : 0 < T} {W : Set Torus2}
    {m₁ m₂ : Fin 2 → Gam → ℂ} {hm₁ : IsBddSymbol m₁} {hm₂ : IsBddSymbol m₂}
    (hr₁ : IsRealSymbol m₁) {C₁ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁)
    (hr₂ : IsRealSymbol m₂) {C₂ : ℝ} (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    {A B : Submodule ℝ (Curve0 T)} (hAB : A ≤ B) {ε : ℝ}
    (hexA₁ : PaperExistence hα hT hm₁ A ε) (hexB₁ : PaperExistence hα hT hm₁ B ε)
    (hexA₂ : PaperExistence hα hT hm₂ A ε) (hexB₂ : PaperExistence hα hT hm₂ B ε)
    (h : PaperObsMapsAgree hα hT W hm₁ hm₂ B ε hexB₁ hexB₂) :
    PaperObsMapsAgree hα hT W hm₁ hm₂ A ε hexA₁ hexA₂ := by
  intro f hf hs
  obtain ⟨hstate, hvel⟩ := h f (hAB hf) hs
  constructor
  · have hIoo := self_mem_ae_restrict
      (measurableSet_Ioo (a := (0:ℝ)) (b := T)) (μ := (volume : Measure ℝ))
    filter_upwards [hstate, hIoo] with t ht htmem
    have hmem : t ∈ Set.Icc (0:ℝ) T := ⟨htmem.1.le, htmem.2.le⟩
    have e1 : paperObsState hexA₁ hf hs t = paperObsState hexB₁ (hAB hf) hs t :=
      paperSol_eq hr₁ hC₁ hexA₁ hf hs (isPaperSolution_paperSol hexB₁ (hAB hf) hs) hmem
    have e2 : paperObsState hexA₂ hf hs t = paperObsState hexB₂ (hAB hf) hs t :=
      paperSol_eq hr₂ hC₂ hexA₂ hf hs (isPaperSolution_paperSol hexB₂ (hAB hf) hs) hmem
    rw [e1, e2]
    exact ht
  · intro j
    filter_upwards [hvel j] with t ht
    have e1 : paperObsVel hexA₁ hf hs j t = paperObsVel hexB₁ (hAB hf) hs j t :=
      paperObsVel_eq hr₁ hC₁ hexA₁ hf hs (isPaperSolution_paperSol hexB₁ (hAB hf) hs) j t
    have e2 : paperObsVel hexA₂ hf hs j t = paperObsVel hexB₂ (hAB hf) hs j t :=
      paperObsVel_eq hr₂ hC₂ hexA₂ hf hs (isPaperSolution_paperSol hexB₂ (hAB hf) hs) j t
    rw [e1, e2]
    exact ht

/-- **A common radius on which paper solutions exist for both kernels.** -/
theorem exists_paperExistence_pair (hα : 1 / 2 < α) (hα1 : α < 1) (hT : 0 < T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    {C₁ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {C₂ : ℝ} (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    (W : Set Torus2) :
    ∃ ε > 0, PaperExistence hα hT hm₁ (paperSources hT W) ε
      ∧ PaperExistence hα hT hm₂ (paperSources hT W) ε := by
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_paperExistence_paperSources hα hα1 hT hm₁ hr₁ hC₁ W
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_paperExistence_paperSources hα hα1 hT hm₂ hr₂ hC₂ W
  exact ⟨min ε₁ ε₂, lt_min hε₁ hε₂, h₁.mono (min_le_left _ _), h₂.mono (min_le_right _ _)⟩

end LiWang.WienerModel
