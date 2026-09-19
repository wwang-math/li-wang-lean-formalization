/-
# Unconditional uniqueness of the mild solution in the first-order class

Step 3(a) of the v7.0 physical bridge.

`SourceSolution.mild_curve_unique_ball` proves uniqueness **inside an explicit small ball**.
That is not enough for the physical comparison theorem, because a reference solution coming
from the PDE literature is not given to us with a small `A¹` norm.  This file removes the
smallness assumption entirely:

> two mild solutions of the *same* source that both lie in `Curve1 T = C([0,T]; A¹)` are equal,
> with **no** bound on their norms.

The mechanism is the smoothing gain of the fractional heat semigroup.  The difference
`w = u − v` satisfies `w(t) = −∫₀ᵗ e^{-(t-s)L}(N(u,u) − N(v,v))(s) ds`, and the integrand is
controlled by `(1 + (t−s)^{-1/(2α)}/π)‖w(s)‖`, whose time integral over a window of length `τ`
is `duhamelConst α τ → 0` as `τ → 0`.  A window on which `L · duhamelConst α τ ≤ 1/2`
therefore forces `w ≡ 0` there, and since the window length is uniform the conclusion
propagates over `[0,T]` in finitely many steps.  This is the standard local-in-time absorption
argument, made unconditional by `norm_duhamelIntegral_le_of_vanishing`, which is the
refinement of `norm_duhamelIntegral_le` that actually sees that the source vanishes on the
part of the interval already treated.

Part of `LiWangWienerPhysicalPDEBridgePacket` v7.0.
-/
import LiWangWiener.PhysicalPDE

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. A Duhamel estimate that sees a vanishing source -/

@[simp] theorem heatSmoothFun_zero {α t : ℝ} (hα : 1 / 2 ≤ α) :
    heatSmoothFun hα t (0 : Wiener) = 0 := by
  by_cases ht : 0 < t
  · rw [heatSmoothFun_eq hα ht]
    exact map_zero (heatSmoothCLM hα ht)
  · exact heatSmoothFun_of_nonpos hα (not_lt.1 ht) _

/-- The time integral of the smoothing constant, in the un-reflected variable. -/
theorem integral_heatConst' {α : ℝ} (hα : 1 / 2 < α) (u : ℝ) :
    (∫ r in (0:ℝ)..u, (1 + r ^ (-(1 / (2 * α))) / Real.pi)) = duhamelConst α u := by
  rw [← integral_heatConst hα u,
    intervalIntegral.integral_comp_sub_left
      (fun r : ℝ => 1 + r ^ (-(1 / (2 * α))) / Real.pi) u]
  simp

/-- **The Duhamel bound that sees a vanishing source.**  If the source vanishes on `[0,a]` then
the Duhamel integral at time `t` only feels the window `[a,t]`, and the smoothing constant is
integrated over a window of length `t − a` instead of `t`.  This is what makes the uniqueness
argument below unconditional. -/
theorem norm_duhamelIntegral_le_of_vanishing {α : ℝ} (hα : 1 / 2 < α) {t a : ℝ}
    (ha0 : 0 ≤ a) (hat : a ≤ t) {g : ℝ → Wiener} (hg : Continuous g) {M₀ : ℝ}
    (hM₀ : ∀ s, ‖g s‖ ≤ M₀) (hzero : ∀ s ∈ Set.Icc (0:ℝ) a, g s = 0)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s ∈ Set.Icc a t, ‖g s‖ ≤ M) :
    ‖duhamelIntegral hα.le t g‖ ≤ M * duhamelConst α (t - a) := by
  have ht0 : (0:ℝ) ≤ t := le_trans ha0 hat
  have hint := intervalIntegrable_duhamelIntegrand hα ht0 hg hM₀
  have hsub1 : Set.uIcc (0:ℝ) a ⊆ Set.uIcc (0:ℝ) t := by
    rw [Set.uIcc_of_le ha0, Set.uIcc_of_le ht0]
    exact Set.Icc_subset_Icc le_rfl hat
  have hsub2 : Set.uIcc a t ⊆ Set.uIcc (0:ℝ) t := by
    rw [Set.uIcc_of_le hat, Set.uIcc_of_le ht0]
    exact Set.Icc_subset_Icc ha0 le_rfl
  have hI1 : IntervalIntegrable (duhamelIntegrand hα.le t g) volume 0 a := hint.mono_set hsub1
  have hI2 : IntervalIntegrable (duhamelIntegrand hα.le t g) volume a t := hint.mono_set hsub2
  have hsplit : duhamelIntegral hα.le t g
      = (∫ s in (0:ℝ)..a, duhamelIntegrand hα.le t g s)
        + ∫ s in a..t, duhamelIntegrand hα.le t g s := by
    rw [duhamelIntegral, intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have hz : (∫ s in (0:ℝ)..a, duhamelIntegrand hα.le t g s) = 0 := by
    have hcg : (∫ s in (0:ℝ)..a, duhamelIntegrand hα.le t g s)
        = ∫ _s in (0:ℝ)..a, (0 : Wiener1) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le ha0] at hs
      rw [duhamelIntegrand, hzero s hs, heatSmoothFun_zero]
    rw [hcg, intervalIntegral.integral_zero]
  rw [hsplit, hz, zero_add]
  have hbase : IntervalIntegrable (fun r : ℝ => 1 + r ^ (-(1 / (2 * α))) / Real.pi)
      volume 0 t := intervalIntegrable_heatConst hα t
  have hrefl := hbase.comp_sub_left t
  simp only [sub_zero, sub_self] at hrefl
  have hrefl2 : IntervalIntegrable
      (fun s : ℝ => 1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi) volume a t := by
    refine IntervalIntegrable.mono_set hrefl ?_
    rw [Set.uIcc_of_le hat]
    refine le_trans ?_ (le_of_eq (Set.uIcc_comm (0:ℝ) t))
    rw [Set.uIcc_of_le ht0]
    exact Set.Icc_subset_Icc ha0 le_rfl
  have hmaj := hrefl2.const_mul M
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc a t →
      ‖duhamelIntegrand hα.le t g s‖
        ≤ M * (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi) := by
    refine MeasureTheory.ae_of_all _ fun s hs => ?_
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · refine le_trans (norm_duhamelIntegrand_le hα.le hlt g) ?_
      have h1 : (0:ℝ) ≤ (t - s) ^ (-(1 / (2 * α))) := Real.rpow_nonneg (by linarith) _
      have h2 : 0 ≤ (t - s) ^ (-(1 / (2 * α))) / Real.pi := div_nonneg h1 Real.pi_pos.le
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM s ⟨hs.1.le, hs.2⟩) (by linarith)
    · have hts : t - s = 0 := by rw [heq]; ring
      rw [duhamelIntegrand_of_le hα.le heq.ge g, norm_zero]
      refine mul_nonneg hM0 ?_
      have h1 : (0:ℝ) ≤ (t - s) ^ (-(1 / (2 * α))) := by
        rw [hts]; exact Real.rpow_nonneg le_rfl _
      have h2 : 0 ≤ (t - s) ^ (-(1 / (2 * α))) / Real.pi := div_nonneg h1 Real.pi_pos.le
      linarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le hat hbound hmaj
  refine le_trans hle ?_
  rw [intervalIntegral.integral_const_mul]
  have hval : (∫ s in a..t, (1 + (t - s) ^ (-(1 / (2 * α))) / Real.pi))
      = duhamelConst α (t - a) := by
    rw [intervalIntegral.integral_comp_sub_left
      (fun r : ℝ => 1 + r ^ (-(1 / (2 * α))) / Real.pi) t]
    simp only [sub_self]
    exact integral_heatConst' hα (t - a)
  rw [hval]

/-! ## 2. The absorption window -/

theorem duhamelConst_zero {α : ℝ} (hα : 1 / 2 < α) : duhamelConst α 0 = 0 := by
  have hne : (1:ℝ) - 1 / (2 * α) ≠ 0 := by
    have h2α : (1:ℝ) < 2 * α := by linarith
    have : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
    intro h; linarith
  rw [duhamelConst, Real.zero_rpow hne, zero_div, add_zero]

theorem continuousAt_duhamelConst {α : ℝ} (hα : 1 / 2 < α) :
    ContinuousAt (fun r : ℝ => duhamelConst α r) 0 := by
  have hpos : (0:ℝ) < 1 - 1 / (2 * α) := by
    have h2α : (1:ℝ) < 2 * α := by linarith
    have : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; exact h2α
    linarith
  have hrp : ContinuousAt (fun r : ℝ => r ^ (1 - 1 / (2 * α))) 0 :=
    Real.continuousAt_rpow_const 0 _ (Or.inr hpos.le)
  exact continuousAt_id.add (hrp.div_const _)

/-- **The absorption window.**  For every nonnegative Lipschitz constant `L` there is a window
length `τ > 0` on which `L · duhamelConst α τ ≤ 1/2`. -/
theorem exists_absorption_window {α : ℝ} (hα : 1 / 2 < α) (L : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ L * duhamelConst α τ ≤ 1 / 2 := by
  have hcont : ContinuousAt (fun r : ℝ => L * duhamelConst α r) 0 :=
    continuousAt_const.mul (continuousAt_duhamelConst hα)
  have hval : L * duhamelConst α 0 = 0 := by rw [duhamelConst_zero hα, mul_zero]
  have htend : Tendsto (fun r : ℝ => L * duhamelConst α r) (nhds 0) (nhds 0) := by
    have := hcont
    rw [ContinuousAt, hval] at this
    exact this
  have hev : ∀ᶠ r in nhds (0:ℝ), L * duhamelConst α r < 1 / 2 :=
    htend.eventually (gt_mem_nhds (by norm_num))
  have hev' : ∀ᶠ r in nhdsWithin (0:ℝ) (Set.Ioi 0), L * duhamelConst α r < 1 / 2 :=
    eventually_nhdsWithin_of_eventually_nhds hev
  obtain ⟨τ, hτ1, hτ2⟩ := (hev'.and self_mem_nhdsWithin).exists
  exact ⟨τ, hτ2, hτ1.le⟩

/-! ## 3. Elementary curve identities -/

theorem curveState_sub (hT : 0 ≤ T) (u v : Curve1 T) (s : ℝ) :
    curveState hT (u - v) s = curveState hT u s - curveState hT v s := rfl

theorem curveState_neg (hT : 0 ≤ T) (u : Curve1 T) (s : ℝ) :
    curveState hT (-u) s = -curveState hT u s := rfl

theorem curveState_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) (V : Curve0 T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    curveState hT (duhamelOp hα hT V) t = duhamelIntegral hα.le t (sourceFun hT V) := by
  rw [curveState_coe hT (duhamelOp hα hT V) ⟨t, ht⟩]
  exact duhamelOp_apply_val hα hT V ⟨t, ht⟩

theorem sourceFun_spacetimeTransport_sub (hT : 0 ≤ T) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (u v : Curve1 T) (s : ℝ) :
    sourceFun hT (spacetimeTransport m hm hr u u - spacetimeTransport m hm hr v v) s
      = quadCurve hm (curveState hT u) s - quadCurve hm (curveState hT v) s := rfl

/-! ## 4. Unconditional uniqueness -/

/-- **Unconditional uniqueness of mild solutions.**  Two continuous `A¹`-valued curves solving
the same mild equation are equal.  No smallness of the source, of the solutions, or of the
time horizon is assumed: the only inputs are `1/2 < α` (through the integrability of the
smoothing constant) and the uniform symbol bound. -/
theorem mild_curve_unique (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u v : Curve1 T} (f : Curve0 T)
    (heu : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hev : v + sourceQuad hα hT m hm hr v v = duhamelOp hα hT f) : u = v := by
  have hC0 : (0:ℝ) ≤ C := nonneg_of_symbol_bound hC
  set R : ℝ := max ‖u‖ ‖v‖ with hRdef
  have hR0 : (0:ℝ) ≤ R := le_trans (norm_nonneg u) (le_max_left _ _)
  set L : ℝ := 8 * Real.pi * C * R with hLdef
  have hL0 : (0:ℝ) ≤ L := by positivity
  set φ : ℝ → ℝ := fun s => ‖curveState hT u s - curveState hT v s‖ with hφdef
  have hφcont : Continuous φ :=
    ((continuous_curveState hT u).sub (continuous_curveState hT v)).norm
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => norm_nonneg _
  set Q : ℝ → Wiener :=
    fun s => quadCurve hm (curveState hT u) s - quadCurve hm (curveState hT v) s with hQdef
  have hQcont : Continuous Q :=
    (continuous_quadCurve hm (continuous_curveState hT u)).sub
      (continuous_quadCurve hm (continuous_curveState hT v))
  have hub : ∀ s, ‖curveState hT u s‖ ≤ R :=
    fun s => le_trans (norm_curveState_le hT u s) (le_max_left _ _)
  have hvb : ∀ s, ‖curveState hT v s‖ ≤ R :=
    fun s => le_trans (norm_curveState_le hT v s) (le_max_right _ _)
  have hQbound : ∀ s, ‖Q s‖ ≤ L * φ s := fun s =>
    norm_quadCurve_sub_le hm hC hub hvb s
  have hQM₀ : ∀ s, ‖Q s‖ ≤ L * (2 * R) := by
    intro s
    refine le_trans (hQbound s) (mul_le_mul_of_nonneg_left ?_ hL0)
    calc φ s ≤ ‖curveState hT u s‖ + ‖curveState hT v s‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hub s) (hvb s)
      _ = 2 * R := by ring
  -- the Duhamel representation of the difference
  have hdiff : u - v = -duhamelOp hα hT
      (spacetimeTransport m hm hr u u - spacetimeTransport m hm hr v v) := by
    have h : u + duhamelOp hα hT (spacetimeTransport m hm hr u u)
        = v + duhamelOp hα hT (spacetimeTransport m hm hr v v) := by
      rw [show duhamelOp hα hT (spacetimeTransport m hm hr u u)
            = sourceQuad hα hT m hm hr u u from rfl,
        show duhamelOp hα hT (spacetimeTransport m hm hr v v)
            = sourceQuad hα hT m hm hr v v from rfl, heu, hev]
    rw [map_sub]
    linear_combination (norm := abel) h
  have hrep : ∀ t ∈ Set.Icc (0:ℝ) T,
      curveState hT u t - curveState hT v t = -duhamelIntegral hα.le t Q := by
    intro t ht
    have h1 : curveState hT u t - curveState hT v t = curveState hT (u - v) t := rfl
    rw [h1, hdiff, curveState_neg, curveState_duhamelOp hα hT _ ht]
    congr 1
  -- the absorption window
  obtain ⟨τ, hτ0, hτ⟩ := exists_absorption_window hα L
  -- the finite induction
  have key : ∀ n : ℕ, ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) T → s ≤ (n : ℝ) * τ → φ s = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs hsn
      have hs0 : s = 0 := le_antisymm (by simpa using hsn) hs.1
      rw [hφdef]
      simp only [hs0]
      rw [curveState_initial_of_mild hα hT hm hr heu,
        curveState_initial_of_mild hα hT hm hr hev, sub_zero, norm_zero]
    | succ n ih =>
      intro s hs hsn
      set a : ℝ := min ((n : ℝ) * τ) T with hadef
      set b : ℝ := min (((n : ℝ) + 1) * τ) T with hbdef
      have ha0 : (0:ℝ) ≤ a := le_min (by positivity) hT
      have haT : a ≤ T := min_le_right _ _
      have hbT : b ≤ T := min_le_right _ _
      have hab : a ≤ b := by
        refine min_le_min ?_ le_rfl
        nlinarith [hτ0, Nat.cast_nonneg (α := ℝ) n]
      have hba : b - a ≤ τ := by
        rcases le_total ((n : ℝ) * τ) T with hcase | hcase
        · have hae : a = (n : ℝ) * τ := min_eq_left hcase
          have hble : b ≤ ((n : ℝ) + 1) * τ := min_le_left _ _
          rw [hae]; nlinarith
        · have hae : a = T := min_eq_right hcase
          have : b ≤ T := hbT
          rw [hae]; linarith
      have hzero_a : ∀ r ∈ Set.Icc (0:ℝ) a, φ r = 0 := fun r hr =>
        ih r ⟨hr.1, le_trans hr.2 haT⟩ (le_trans hr.2 (min_le_left _ _))
      have hQzero : ∀ r ∈ Set.Icc (0:ℝ) a, Q r = 0 := by
        intro r hr
        have := hQbound r
        rw [hzero_a r hr, mul_zero] at this
        exact norm_le_zero_iff.1 this
      obtain ⟨s₀, hs₀mem, hs₀max⟩ :=
        (isCompact_Icc (a := a) (b := b)).exists_isMaxOn (Set.nonempty_Icc.2 hab)
          hφcont.continuousOn
      have hMφ0 : (0:ℝ) ≤ φ s₀ := hφ0 s₀
      have hmain : ∀ t ∈ Set.Icc a b, φ t ≤ (1 / 2) * φ s₀ := by
        intro t htmem
        have htIcc : t ∈ Set.Icc (0:ℝ) T :=
          ⟨le_trans ha0 htmem.1, le_trans htmem.2 hbT⟩
        have hQt : ∀ r ∈ Set.Icc a t, ‖Q r‖ ≤ L * φ s₀ := by
          intro r hr
          refine le_trans (hQbound r) (mul_le_mul_of_nonneg_left ?_ hL0)
          exact hs₀max ⟨hr.1, le_trans hr.2 htmem.2⟩
        have hbd := norm_duhamelIntegral_le_of_vanishing hα ha0 htmem.1 hQcont hQM₀ hQzero
          (by positivity) hQt
        have hφt : φ t = ‖duhamelIntegral hα.le t Q‖ := by
          rw [hφdef]; simp only []; rw [hrep t htIcc, norm_neg]
        rw [hφt]
        refine le_trans hbd ?_
        have hmono : duhamelConst α (t - a) ≤ duhamelConst α τ :=
          duhamelConst_mono hα (by linarith [htmem.1]) (by linarith [htmem.2])
        calc (L * φ s₀) * duhamelConst α (t - a)
            ≤ (L * φ s₀) * duhamelConst α τ :=
              mul_le_mul_of_nonneg_left hmono (by positivity)
          _ = φ s₀ * (L * duhamelConst α τ) := by ring
          _ ≤ φ s₀ * (1 / 2) := mul_le_mul_of_nonneg_left hτ hMφ0
          _ = (1 / 2) * φ s₀ := by ring
      have hcontr : φ s₀ ≤ (1 / 2) * φ s₀ := hmain s₀ hs₀mem
      have hzero₀ : φ s₀ = 0 := le_antisymm (by linarith) hMφ0
      rcases le_total s a with hle | hle
      · exact hzero_a s ⟨hs.1, hle⟩
      · have hsb : s ≤ b := le_min (by push_cast at hsn ⊢; linarith) hs.2
        have := hs₀max ⟨hle, hsb⟩
        rw [hzero₀] at this
        exact le_antisymm this (hφ0 s)
  -- cover `[0,T]`
  obtain ⟨N, hN⟩ := exists_nat_ge (T / τ)
  have hTN : T ≤ (N : ℝ) * τ := by
    rw [div_le_iff₀ hτ0] at hN
    exact hN
  refine DFunLike.ext _ _ (fun t => RealWiener1.val_injective ?_)
  have htmem : (t : ℝ) ∈ Set.Icc (0:ℝ) T := t.2
  have hφt : φ (t : ℝ) = 0 := key N (t : ℝ) htmem (le_trans htmem.2 hTN)
  have h0 : curveState hT u (t : ℝ) - curveState hT v (t : ℝ) = 0 := by
    have := hφt
    rw [hφdef] at this
    exact norm_eq_zero.1 this
  rw [curveState_coe hT u t, curveState_coe hT v t] at h0
  exact sub_eq_zero.1 h0

end LiWang.WienerModel
