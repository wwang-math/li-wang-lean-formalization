/-
# The fractional heat semigroup on `ℓ²` data, and its positive-time smoothing

For the terminal-control duality argument the *adjoint* datum is only square summable, so
the packet's `heatSmooth : Wiener → Wiener1` (which uses `‖a‖_{ℓ¹}`) does not apply.  Using
the genuine summability of the heat factor proved in `HeatSummability`, this module builds

* `heat2 hα hr y : Wiener1` — `e^{-r(-Δ)^α} y` for `y : Wiener2` and `r > 0`
  (**positive-time smoothing `ℓ² → A¹`**);
* `fracHeat2 hα hr y : Wiener` — `(-Δ)^α e^{-r(-Δ)^α} y`, **the fractional multiplier in the
  Wiener algebra**, satisfying the graph relation of `FractionalUCP` on the nose;
* `heatField α y x r` — the physical field `x ↦ (e^{-r(-Δ)^α}y)(x)` as an honest series, with
  `hasDerivAt_heatField`: it is differentiable in `r` with derivative `-(-Δ)^α e^{-r(-Δ)^α}y`;
* `heatPair α y a r = ⟪y, e^{-r(-Δ)^α} a⟫` as a series that is **continuous in `r` on all of
  `ℝ`** (including `r = 0`, where the `Wiener1` norm of `heat2` blows up), together with its
  two identifications: with the `ℓ²` inner product of the smoothed datum, and with the
  physical spatial integral against the test profile;
* `eq_zero_of_heatPair_vanishes` — **the UCP step**: if all these pairings vanish for the
  smooth profiles of `W` and all `r` in `[0,τ]`, then `y = 0`.

Nothing here assumes unique continuation: `FractionalUCP α W` is carried as an explicit
hypothesis exactly where it is used.

Part of `LiWangWienerTerminalControlPacket` v6.0.
-/
import LiWangWiener.HeatSummability
import LiWangWiener.TestSeparation
import LiWangWiener.TwoStateContinuity
import LiWangWiener.UCPBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory Filter Topology

namespace LiWang.WienerModel

variable {α : ℝ}

/-! ## 1. Smoothing an `ℓ²` datum -/

theorem conj_heatSymbol (α t : ℝ) (k : Gam) : conj (heatSymbol α t k) = heatSymbol α t k := by
  rw [heatSymbol, Complex.conj_ofReal]

theorem heatSymbol_ne_zero (α t : ℝ) (k : Gam) : heatSymbol α t k ≠ 0 := by
  rw [heatSymbol]
  simpa using (Real.exp_ne_zero _)

theorem norm_w2_apply_le (y : Wiener2) (k : Gam) : ‖y k‖ ≤ ‖y‖ :=
  lp.norm_apply_le_norm (by norm_num) y k

theorem summable_wt_heat_w2 {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) :
    Summable (fun k : Gam => wt k * ‖heatSymbol α r k * y k‖) := by
  refine Summable.of_nonneg_of_le (fun k => by have := (wt_pos k).le; positivity) (fun k => ?_)
    ((summable_gam_wt_heat hα hr).mul_left ‖y‖)
  rw [norm_mul, norm_heatSymbol]
  calc wt k * (Real.exp (-(r * fracSymbol α k)) * ‖y k‖)
      = (wt k * Real.exp (-(r * fracSymbol α k))) * ‖y k‖ := by ring
    _ ≤ (wt k * Real.exp (-(r * fracSymbol α k))) * ‖y‖ :=
        mul_le_mul_of_nonneg_left (norm_w2_apply_le y k)
          (by have := (wt_pos k).le; positivity)
    _ = ‖y‖ * (wt k * Real.exp (-(r * fracSymbol α k))) := by ring

theorem norm_fracSymbol_cast (α : ℝ) (k : Gam) :
    ‖((fracSymbol α k : ℝ) : ℂ)‖ = fracSymbol α k := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fracSymbol_nonneg α k)]

theorem summable_frac_heat_w2 {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) :
    Summable (fun k : Gam => ‖((fracSymbol α k : ℝ) : ℂ) * (heatSymbol α r k * y k)‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_gam_frac_heat hα hr).mul_left ‖y‖)
  rw [norm_mul, norm_mul, norm_fracSymbol_cast, norm_heatSymbol]
  calc fracSymbol α k * (Real.exp (-(r * fracSymbol α k)) * ‖y k‖)
      = (fracSymbol α k * Real.exp (-(r * fracSymbol α k))) * ‖y k‖ := by ring
    _ ≤ (fracSymbol α k * Real.exp (-(r * fracSymbol α k))) * ‖y‖ :=
        mul_le_mul_of_nonneg_left (norm_w2_apply_le y k)
          (by have := fracSymbol_nonneg α k; positivity)
    _ = ‖y‖ * (fracSymbol α k * Real.exp (-(r * fracSymbol α k))) := by ring

/-- **Positive-time smoothing `ℓ² → A¹`.** -/
noncomputable def heat2 {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) : Wiener1 :=
  Wiener1.mk (fun k => heatSymbol α r k * y k) (summable_wt_heat_w2 hα hr y)

/-- **The fractional multiplier of the smoothed datum, in the Wiener algebra.** -/
noncomputable def fracHeat2 {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) : Wiener :=
  wmk (fun k => ((fracSymbol α k : ℝ) : ℂ) * (heatSymbol α r k * y k))
    (summable_frac_heat_w2 hα hr y)

@[simp] theorem heat2_coeff {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (k : Gam) :
    (heat2 hα hr y).coeff k = heatSymbol α r k * y k := rfl

@[simp] theorem incl_heat2_apply {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (k : Gam) :
    (incl (heat2 hα hr y)) k = heatSymbol α r k * y k := rfl

@[simp] theorem fracHeat2_apply {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (k : Gam) :
    (fracHeat2 hα hr y) k = ((fracSymbol α k : ℝ) : ℂ) * (heatSymbol α r k * y k) := rfl

/-- **The `FractionalUCP` graph relation**, on the nose. -/
theorem fracHeat2_coeff_rel {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (k : Gam) :
    (fracHeat2 hα hr y) k = ((fracSymbol α k : ℝ) : ℂ) * (heat2 hα hr y).coeff k := rfl

/-- **Injectivity of the heat semigroup**: no positive-time information is lost, the zero
Fourier mode included (`fracSymbol α 0 = 0`, so `heatSymbol α r 0 = 1`). -/
theorem eq_zero_of_heat2_eq_zero {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) {y : Wiener2}
    (h : heat2 hα hr y = 0) : y = 0 := by
  refine lp.ext (funext fun k => ?_)
  have hk : heatSymbol α r k * y k = 0 := by
    have h2 := congrArg (fun u : Wiener1 => u.coeff k) h
    simpa using h2
  have := (mul_eq_zero.1 hk).resolve_left (heatSymbol_ne_zero α r k)
  simpa using this

/-! ## 2. The physical field and its time derivative -/

/-- The physical field of `e^{-r(-Δ)^α} y` at the point `x`, as an honest series. -/
noncomputable def heatField (α : ℝ) (y : Wiener2) (x : Torus2) (r : ℝ) : ℂ :=
  ∑' k : Gam, (heatSymbol α r k * y k) * emode k x

theorem heatField_eq_synth {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (x : Torus2) :
    heatField α y x r = synth (incl (heat2 hα hr y)) x := by
  rw [synth_apply]
  exact tsum_congr fun k => rfl

theorem hasDerivAt_heatSymbol (α : ℝ) (k : Gam) (s : ℝ) :
    HasDerivAt (fun t : ℝ => heatSymbol α t k)
      (((-(fracSymbol α k) * Real.exp (-(s * fracSymbol α k)) : ℝ) : ℂ)) s := by
  have h1 : HasDerivAt (fun t : ℝ => -(t * fracSymbol α k)) (-(fracSymbol α k)) s := by
    simpa using ((hasDerivAt_id s).mul_const (fracSymbol α k)).neg
  have h2 := h1.exp
  have h3 : HasDerivAt (fun t : ℝ => Real.exp (-(t * fracSymbol α k)))
      (-(fracSymbol α k) * Real.exp (-(s * fracSymbol α k))) s := by
    simpa [mul_comm] using h2
  exact h3.ofReal_comp

/-- **Term-by-term differentiation in time.**  On the positive-time half line the physical
field is differentiable in `r`, with derivative the physical field of `-(-Δ)^α e^{-r(-Δ)^α}y`. -/
theorem hasDerivAt_heatField {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (x : Torus2) :
    HasDerivAt (heatField α y x) (-(synth (fracHeat2 hα hr y) x)) r := by
  have hhalf : (0:ℝ) < r / 2 := by linarith
  set u : Gam → ℝ := fun k => ‖y‖ * (fracSymbol α k * Real.exp (-((r / 2) * fracSymbol α k)))
    with hu
  have hus : Summable u := (summable_gam_frac_heat hα hhalf).mul_left ‖y‖
  set g : Gam → ℝ → ℂ := fun k s => (heatSymbol α s k * y k) * emode k x with hg
  set g' : Gam → ℝ → ℂ := fun k s =>
    (-((fracSymbol α k : ℝ) : ℂ)) * ((heatSymbol α s k * y k) * emode k x) with hg'
  have hderiv : ∀ (k : Gam), ∀ s ∈ Set.Ioi (r / 2), HasDerivAt (g k) (g' k s) s := by
    intro k s _
    have h := (hasDerivAt_heatSymbol α k s).mul_const (y k * emode k x)
    have hrw : (fun t : ℝ => heatSymbol α t k * (y k * emode k x)) = g k := by
      funext t; rw [hg]; ring
    rw [hrw] at h
    have hval : ((-(fracSymbol α k) * Real.exp (-(s * fracSymbol α k)) : ℝ) : ℂ)
        * (y k * emode k x) = g' k s := by
      show ((-(fracSymbol α k) * Real.exp (-(s * fracSymbol α k)) : ℝ) : ℂ) * (y k * emode k x)
        = (-((fracSymbol α k : ℝ) : ℂ)) * ((heatSymbol α s k * y k) * emode k x)
      rw [heatSymbol, Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    rw [hval] at h
    exact h
  have hbound : ∀ (k : Gam), ∀ s ∈ Set.Ioi (r / 2), ‖g' k s‖ ≤ u k := by
    intro k s hs
    have hs' : r / 2 < s := hs
    rw [hg', norm_mul, norm_neg, norm_fracSymbol_cast, norm_mul, norm_mul, norm_heatSymbol,
      norm_emode_apply, mul_one]
    have hmono : Real.exp (-(s * fracSymbol α k)) ≤ Real.exp (-((r / 2) * fracSymbol α k)) := by
      rw [Real.exp_le_exp]
      have := fracSymbol_nonneg α k
      nlinarith
    have hyk := norm_w2_apply_le y k
    have hfs := fracSymbol_nonneg α k
    calc fracSymbol α k * (Real.exp (-(s * fracSymbol α k)) * ‖y k‖)
        ≤ fracSymbol α k * (Real.exp (-((r / 2) * fracSymbol α k)) * ‖y‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hfs
          exact mul_le_mul hmono hyk (norm_nonneg _) (Real.exp_pos _).le
      _ = u k := by rw [hu]; ring
  have hr0 : r ∈ Set.Ioi (r / 2) := by simp; linarith
  have hsum0 : Summable fun k : Gam => g k r := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_gam_heat hα hr).mul_left ‖y‖)
    rw [hg, norm_mul, norm_mul, norm_heatSymbol, norm_emode_apply, mul_one]
    calc Real.exp (-(r * fracSymbol α k)) * ‖y k‖
        ≤ Real.exp (-(r * fracSymbol α k)) * ‖y‖ :=
          mul_le_mul_of_nonneg_left (norm_w2_apply_le y k) (Real.exp_pos _).le
      _ = ‖y‖ * Real.exp (-(r * fracSymbol α k)) := by ring
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hus isOpen_Ioi isPreconnected_Ioi hderiv hbound hr0 hsum0 hr0
  have hlim : (∑' k : Gam, g' k r) = -(synth (fracHeat2 hα hr y) x) := by
    rw [synth_apply, ← tsum_neg]
    refine tsum_congr fun k => ?_
    rw [hg']
    show (-((fracSymbol α k : ℝ) : ℂ)) * ((heatSymbol α r k * y k) * emode k x)
      = -(((fracHeat2 hα hr y) k) * emode k x)
    rw [fracHeat2_apply]
    ring
  rw [hlim] at hmain
  exact hmain

/-! ## 3. The duality pairing, continuous up to `r = 0` -/

/-- The pairing `⟪y, e^{-r(-Δ)^α}a⟫` written as a series.  The clamp `max r 0` makes it an
honest continuous function of `r` on all of `ℝ`, which is what the time separation lemma
needs; for `r > 0` it agrees with the genuine pairing (`heatPair_eq_inner`). -/
noncomputable def heatPair (α : ℝ) (y : Wiener2) (a : Wiener) (r : ℝ) : ℂ :=
  ∑' k : Gam, conj (y k) * (heatSymbol α (max r 0) k * a k)

theorem continuous_heatPair (α : ℝ) (y : Wiener2) (a : Wiener) :
    Continuous (heatPair α y a) := by
  refine continuous_tsum (u := fun k => ‖y‖ * ‖a k‖) (fun k => ?_)
    ((wiener_summable a).mul_left ‖y‖) (fun k r => ?_)
  · have hc : Continuous fun r : ℝ => heatSymbol α (max r 0) k := by
      have : Continuous fun r : ℝ => (-(max r 0 * fracSymbol α k)) :=
        ((continuous_id.max continuous_const).mul continuous_const).neg
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp this)
    exact (hc.mul continuous_const).const_mul _
  · rw [norm_mul, norm_mul, RCLike.norm_conj]
    have h1 : ‖heatSymbol α (max r 0) k‖ ≤ 1 := norm_heatSymbol_le_one (le_max_right r 0) k
    calc ‖y k‖ * (‖heatSymbol α (max r 0) k‖ * ‖a k‖)
        ≤ ‖y‖ * (1 * ‖a k‖) := by
          refine mul_le_mul (norm_w2_apply_le y k) ?_ (by positivity) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖y‖ * ‖a k‖ := by ring

theorem heatPair_eq_inner {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (a : Wiener) :
    heatPair α y a r = inner ℂ y (toWiener2 (incl (heatSmoothFun hα r a))) := by
  rw [lp.inner_eq_tsum, heatPair]
  refine tsum_congr fun k => ?_
  rw [max_eq_left hr.le, RCLike.inner_apply]
  show conj (y k) * (heatSymbol α r k * a k)
    = (toWiener2 (incl (heatSmoothFun hα r a))) k * conj (y k)
  rw [toWiener2_apply, incl_apply, heatSmoothFun_coeff hα hr]
  ring

theorem heatPair_eq_integral {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) (y : Wiener2) (a : Wiener) :
    heatPair α y a r
      = ∫ x : Torus2, conj (synth (incl (heat2 hα hr y)) x) * synth a x := by
  rw [← inner_synthL2_integral, inner_synthL2, heatPair]
  refine tsum_congr fun k => ?_
  rw [max_eq_left hr.le]
  show conj (y k) * (heatSymbol α r k * a k) = conj ((incl (heat2 hα hr y)) k) * a k
  rw [incl_heat2_apply, map_mul, conj_heatSymbol]
  ring

/-! ## 4. The unique-continuation step -/

/-- If the pairing against every smooth profile of `W` vanishes at a positive time, the
smoothed datum vanishes on `W`. -/
theorem heat2_vanishes_on {r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) {W : Set Torus2}
    (hW : IsOpen W) {y : Wiener2} (h : ∀ a ∈ smoothProfiles W, heatPair α y a.val r = 0) :
    ∀ x ∈ W, synth (incl (heat2 hα hr y)) x = 0 := by
  have hv : Continuous fun x : Torus2 => conj (synth (incl (heat2 hα hr y)) x) :=
    Complex.continuous_conj.comp (synth (incl (heat2 hα hr y))).continuous
  have hint : ∀ a ∈ smoothProfiles W,
      (∫ x : Torus2, conj (synth (incl (heat2 hα hr y)) x) * synth a.val x) = 0 := by
    intro a ha
    rw [← heatPair_eq_integral hα hr]
    exact h a ha
  intro x hx
  have := eq_zero_on_of_forall_smoothProfile hW hv hint x hx
  simpa using this

/-- **The UCP step.**  If the duality pairing against every smooth profile supported in `W`
vanishes for every `r` in `[0,τ]`, then the `ℓ²` datum is zero.  The hypothesis
`FractionalUCP α W` is the portable parameter discharged by the platform adapter. -/
theorem eq_zero_of_heatPair_vanishes (hα : 1 / 2 ≤ α) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {y : Wiener2} {τ : ℝ} (hτ : 0 < τ)
    (h : ∀ a ∈ smoothProfiles W, ∀ r ∈ Set.Icc (0:ℝ) τ, heatPair α y a.val r = 0) :
    y = 0 := by
  set r : ℝ := τ / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hrτ : r < τ := by rw [hrdef]; linarith
  -- the state vanishes on `W` for every positive time below `τ`
  have hstate : ∀ s ∈ Set.Ioo (0:ℝ) τ, ∀ x ∈ W, heatField α y x s = 0 := by
    intro s hs x hx
    have hs0 : 0 < s := hs.1
    rw [heatField_eq_synth hα hs0]
    refine heat2_vanishes_on hα hs0 hW ?_ x hx
    intro a ha
    exact h a ha s ⟨hs.1.le, hs.2.le⟩
  -- hence so does the fractional multiplier, by differentiating in time
  have hfrac : ∀ x ∈ W, synth (fracHeat2 hα hr y) x = 0 := by
    intro x hx
    have hev : heatField α y x =ᶠ[𝓝 r] fun _ => (0:ℂ) := by
      have hnb : Set.Ioo (0:ℝ) τ ∈ 𝓝 r := isOpen_Ioo.mem_nhds ⟨hr, hrτ⟩
      filter_upwards [hnb] with s hs
      exact hstate s hs x hx
    have hzero : HasDerivAt (heatField α y x) 0 r :=
      (hasDerivAt_const r (0:ℂ)).congr_of_eventuallyEq hev
    have hd := hasDerivAt_heatField hα hr y x
    have := hd.unique hzero
    have h2 : -(synth (fracHeat2 hα hr y) x) = 0 := this
    simpa using h2
  have hstate_r : ∀ x ∈ W, synth (incl (heat2 hα hr y)) x = 0 := by
    intro x hx
    rw [← heatField_eq_synth hα hr]
    exact hstate r ⟨hr, hrτ⟩ x hx
  have := hUCP (heat2 hα hr y) (fracHeat2 hα hr y) (fracHeat2_coeff_rel hα hr y)
    hstate_r hfrac
  exact eq_zero_of_heat2_eq_zero hα hr this

end LiWang.WienerModel
