/-
# Local cancellation of the equations on the observation region

Two small mild solutions with the **same** localized source and **equal state and velocity
observations** on a nonempty open `W` are compared.  Term by term, on `W`:

* the source terms cancel (they are literally the same source);
* their spatial derivatives agree, because the two physical fields agree on an *open* set;
* the physical transport terms agree, by the transport commuting diagram together with the
  measured velocities and the equal spatial derivatives;
* the time derivative of the common observed state cancels — the observed difference is
  identically zero in time.

The conclusion is stated for the **time primitive** `v(t) = ∫₀ᵗ (u₁ − u₂)`, which is where the
fractional Laplacian is unconditionally available: `v(t) ∈ A¹`, `(-Δ)^α v(t) ∈ A` as an actual
element of the Wiener algebra (`fracTimeIntegral`), and **both vanish identically on `W`**, for
every `t ∈ [0,T]`.  The corresponding statement for any time window `[t₁,t₂]` follows by
difference, which is the precise sense in which the fractional Laplacian of the state
difference vanishes on `W` at almost every time.

Nothing here assumes that the fractional observations agree, or that the two global solutions
are equal.

Part of `LiWangWienerObservationBridgePacket` v4.0.
-/
import LiWangWiener.LocalizedSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

/-! ## Spatial derivatives on an open set -/

theorem continuous_torusShift (x : Torus2) (j : Fin 2) : Continuous (torusShift x j) := by
  refine continuous_pi fun i => ?_
  by_cases h : i = j
  · subst h
    have : (fun s : ℝ => torusShift x i s i) = fun s : ℝ => x i + ((s : ℝ) : Circ) := by
      funext s
      simp [torusShift]
    rw [this]
    exact continuous_const.add (AddCircle.continuous_mk' 1)
  · have : (fun s : ℝ => torusShift x j s i) = fun _ : ℝ => x i := by
      funext s
      simp [torusShift, h]
    rw [this]
    exact continuous_const

/-- **A state vanishing on an open set has vanishing spatial derivatives there.**  The
derivative is Mathlib's `HasDerivAt` along the group translation, so this is a genuine
statement about the physical field. -/
theorem synth_fourierDeriv_eq_zero_of_vanishes {W : Set Torus2} (hW : IsOpen W) {v : Wiener1}
    (hv : ∀ x ∈ W, synth (incl v) x = 0) (j : Fin 2) {x : Torus2} (hx : x ∈ W) :
    synth (fourierDeriv j v) x = 0 := by
  have hbase := hasDerivAt_synth_torus v x j
  have hpre : (torusShift x j) ⁻¹' W ∈ nhds (0:ℝ) := by
    refine (continuous_torusShift x j).continuousAt.preimage_mem_nhds ?_
    rw [torusShift_zero]
    exact hW.mem_nhds hx
  have heq : (fun s : ℝ => synth (incl v) (torusShift x j s)) =ᶠ[nhds 0] fun _ : ℝ => (0:ℂ) := by
    filter_upwards [hpre] with s hs
    exact hv _ hs
  have hzero : HasDerivAt (fun s : ℝ => synth (incl v) (torusShift x j s)) 0 0 :=
    (hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq heq
  exact hbase.unique hzero

/-- Two states agreeing on an open set have agreeing spatial derivatives there. -/
theorem synth_fourierDeriv_congr {W : Set Torus2} (hW : IsOpen W) {u₁ u₂ : Wiener1}
    (h : ∀ x ∈ W, synth (incl u₁) x = synth (incl u₂) x) (j : Fin 2) {x : Torus2} (hx : x ∈ W) :
    synth (fourierDeriv j u₁) x = synth (fourierDeriv j u₂) x := by
  have hdiff : ∀ y ∈ W, synth (incl (u₁ - u₂)) y = 0 := by
    intro y hy
    rw [map_sub, map_sub]
    show synth (incl u₁) y - synth (incl u₂) y = 0
    rw [h y hy, sub_self]
  have := synth_fourierDeriv_eq_zero_of_vanishes hW hdiff j hx
  rw [map_sub, map_sub] at this
  show synth (fourierDeriv j u₁) x = synth (fourierDeriv j u₂) x
  have h2 : synth (fourierDeriv j u₁) x - synth (fourierDeriv j u₂) x = 0 := this
  exact sub_eq_zero.mp h2

/-! ## Cancellation of the physical transport term -/

/-- **The physical transport terms agree on `W`.**  This uses only the transport commuting
diagram, the measured velocities, and the equality of spatial derivatives on the open set. -/
theorem synth_transport_congr_on {W : Set Torus2} (hW : IsOpen W)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hm₂ : IsBddSymbol m₂)
    {u₁ u₂ : Wiener1}
    (hstate : ∀ x ∈ W, synth (incl u₁) x = synth (incl u₂) x)
    (hvel : ∀ (j : Fin 2), ∀ x ∈ W,
      synth (velocity m₁ hm₁ j (incl u₁)) x = synth (velocity m₂ hm₂ j (incl u₂)) x)
    {x : Torus2} (hx : x ∈ W) :
    synth (transport m₁ hm₁ u₁ u₁) x = synth (transport m₂ hm₂ u₂ u₂) x := by
  rw [synth_transport_apply, synth_transport_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hvel j x hx, synth_fourierDeriv_congr hW hstate j hx]

/-! ## The difference of two solutions is a Duhamel response -/

variable {α T : ℝ}

/-- With the **same** source, the difference of two mild solutions is the Duhamel response of
the difference of their transport terms: the source cancels exactly. -/
theorem diff_eq_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT f)
    (h₂ : u₂ + sourceQuad hα hT m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT f) :
    u₁ - u₂ = duhamelOp hα hT
      (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) := by
  have e₁ := mild_curve_eq_duhamelOp hα hT hm₁ hr₁ h₁
  have e₂ := mild_curve_eq_duhamelOp hα hT hm₂ hr₂ h₂
  have hstep : u₁ - u₂
      = duhamelOp hα hT (f - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁)
        - duhamelOp hα hT (f - spacetimeTransport m₂ hm₂ hr₂ u₂ u₂) := by
    rw [← e₁, ← e₂]
  rw [hstep, ← map_sub]
  congr 1
  abel

/-! ## The time primitive and its fractional Laplacian -/

/-- The Bochner time primitive `v(t) = ∫₀ᵗ u(s) ds` of a state curve, an actual element of the
first-order Wiener space. -/
noncomputable def timePrimitive (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) : Wiener1 :=
  ∫ s in (0:ℝ)..t, curveState hT u s

theorem coeff_timePrimitive (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) (k : Gam) :
    (timePrimitive hT u t).coeff k = ∫ s in (0:ℝ)..t, (curveState hT u s).coeff k :=
  coeff_intervalIntegral ((continuous_curveState hT u).intervalIntegrable 0 t) k

theorem synth_incl_timePrimitive (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) (x : Torus2) :
    synth (incl (timePrimitive hT u t)) x
      = ∫ s in (0:ℝ)..t, synth (incl (curveState hT u s)) x := by
  exact (((ContinuousMap.evalCLM ℂ x).comp (synth.comp incl)).intervalIntegral_comp_comm
    (μ := (volume : Measure ℝ)) ((continuous_curveState hT u).intervalIntegrable 0 t)).symm

/-- **`fracTimeIntegral` really is the fractional Laplacian of the time primitive.** -/
theorem coeff_fracTimeIntegral_eq (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (fracTimeIntegral hα hT g t) k
      = (fracSymbol α k : ℂ) * (timePrimitive hT (duhamelOp hα hT g) t).coeff k := by
  rw [coeff_fracTimeIntegral hα hT g k ht, coeff_timePrimitive]

/-- The coefficient identity for the difference, with no observation hypothesis: the
`fracTimeIntegral` of the difference source is the fractional Laplacian of the time primitive
of the state difference. -/
theorem coeff_fracTimeIntegral_diff (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT f)
    (h₂ : u₂ + sourceQuad hα hT m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT f)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (k : Gam) :
    (fracTimeIntegral hα hT
        (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) t) k
      = (fracSymbol α k : ℂ) * (timePrimitive hT (u₁ - u₂) t).coeff k := by
  rw [coeff_fracTimeIntegral_eq hα hT _ k ht,
    ← diff_eq_duhamelOp hα hT hm₁ hr₁ hm₂ hr₂ h₁ h₂]

/-! ## The local cancellation theorem -/

/-- **Local cancellation on the observation region.**

For two mild solutions of the *same* source whose **state and velocity observations agree on
the open region `W`**, the time primitive `v(t) = ∫₀ᵗ (u₁ − u₂)` satisfies, at every time of
`[0,T]`:

* `v(t) ∈ A¹` and `(-Δ)^α v(t) ∈ A` — the latter as the actual Wiener element
  `fracTimeIntegral`, whose coefficients are `λ_k v_k(t)`;
* `v(t)` vanishes identically on `W`;
* `(-Δ)^α v(t)` vanishes identically on `W`.

No agreement of fractional observations is assumed, and the two solutions are **not** assumed
to be equal. -/
theorem local_cancellation (hα : 1 / 2 < α) (hT : 0 ≤ T) {W : Set Torus2} (hW : IsOpen W)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT f)
    (h₂ : u₂ + sourceQuad hα hT m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT f)
    (hobsState : ∀ (t : TimeI T), ∀ x ∈ W,
      synth (incl (u₁ t).val) x = synth (incl (u₂ t).val) x)
    (hobsVel : ∀ (j : Fin 2) (t : TimeI T), ∀ x ∈ W,
      synth (velocity m₁ hm₁ j (incl (u₁ t).val)) x
        = synth (velocity m₂ hm₂ j (incl (u₂ t).val)) x)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) {x : Torus2} (hx : x ∈ W) :
    synth (incl (timePrimitive hT (u₁ - u₂) t)) x = 0
      ∧ synth (fracTimeIntegral hα hT
          (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) t) x = 0
      ∧ (∀ k : Gam,
          (fracTimeIntegral hα hT
            (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) t) k
            = (fracSymbol α k : ℂ) * (timePrimitive hT (u₁ - u₂) t).coeff k) := by
  set g : Curve0 T :=
    spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁ with hgdef
  have hdiff : u₁ - u₂ = duhamelOp hα hT g := diff_eq_duhamelOp hα hT hm₁ hr₁ hm₂ hr₂ h₁ h₂
  -- the state difference vanishes on `W` at every time
  have hstate : ∀ s : ℝ, synth (incl (curveState hT (u₁ - u₂) s)) x = 0 := by
    intro s
    have hval : curveState hT (u₁ - u₂) s
        = (u₁ (clampT hT s)).val - (u₂ (clampT hT s)).val := rfl
    rw [hval, map_sub, map_sub]
    show synth (incl (u₁ (clampT hT s)).val) x - synth (incl (u₂ (clampT hT s)).val) x = 0
    rw [hobsState (clampT hT s) x hx, sub_self]
  -- the source difference vanishes on `W` at every time
  have hsrc : ∀ s : ℝ, synth (sourceFun hT g s) x = 0 := by
    intro s
    have hval : sourceFun hT g s
        = transport m₂ hm₂ (u₂ (clampT hT s)).val (u₂ (clampT hT s)).val
          - transport m₁ hm₁ (u₁ (clampT hT s)).val (u₁ (clampT hT s)).val := rfl
    rw [hval, map_sub]
    show synth (transport m₂ hm₂ (u₂ (clampT hT s)).val (u₂ (clampT hT s)).val) x
      - synth (transport m₁ hm₁ (u₁ (clampT hT s)).val (u₁ (clampT hT s)).val) x = 0
    rw [synth_transport_congr_on hW hm₁ hm₂ (hobsState (clampT hT s))
      (fun j y hy => hobsVel j (clampT hT s) y hy) hx, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · rw [synth_incl_timePrimitive]
    rw [intervalIntegral.integral_congr (fun s _ => hstate s)]
    simp
  · have hfrac : fracTimeIntegral hα hT g t
        = (∫ s in (0:ℝ)..t, sourceFun hT g s) - incl (curveState hT (duhamelOp hα hT g) t) := rfl
    rw [hfrac, map_sub]
    show synth (∫ s in (0:ℝ)..t, sourceFun hT g s) x
      - synth (incl (curveState hT (duhamelOp hα hT g) t)) x = 0
    have hint : synth (∫ s in (0:ℝ)..t, sourceFun hT g s) x
        = ∫ s in (0:ℝ)..t, synth (sourceFun hT g s) x :=
      (((ContinuousMap.evalCLM ℂ x).comp synth).intervalIntegral_comp_comm
        (μ := (volume : Measure ℝ))
        ((continuous_sourceFun hT g).intervalIntegrable 0 t)).symm
    rw [hint, intervalIntegral.integral_congr (fun s _ => hsrc s), ← hdiff, hstate t]
    simp
  · intro k
    rw [coeff_fracTimeIntegral_eq hα hT g k ht, ← hdiff]

/-- **The time-window form**: the fractional Laplacian of the state difference, averaged over
any window `[t₁,t₂] ⊆ [0,T]`, vanishes on `W`. -/
theorem local_cancellation_window (hα : 1 / 2 < α) (hT : 0 ≤ T) {W : Set Torus2}
    (hW : IsOpen W) {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT f)
    (h₂ : u₂ + sourceQuad hα hT m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT f)
    (hobsState : ∀ (t : TimeI T), ∀ x ∈ W,
      synth (incl (u₁ t).val) x = synth (incl (u₂ t).val) x)
    (hobsVel : ∀ (j : Fin 2) (t : TimeI T), ∀ x ∈ W,
      synth (velocity m₁ hm₁ j (incl (u₁ t).val)) x
        = synth (velocity m₂ hm₂ j (incl (u₂ t).val)) x)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc (0:ℝ) T) (ht₂ : t₂ ∈ Set.Icc (0:ℝ) T)
    {x : Torus2} (hx : x ∈ W) :
    synth (fracTimeIntegral hα hT
        (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) t₂
      - fracTimeIntegral hα hT
        (spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁) t₁) x = 0 := by
  have e₂ := (local_cancellation hα hT hW hm₁ hr₁ hm₂ hr₂ h₁ h₂ hobsState hobsVel ht₂ hx).2.1
  have e₁ := (local_cancellation hα hT hW hm₁ hr₁ hm₂ hr₂ h₁ h₂ hobsState hobsVel ht₁ hx).2.1
  rw [map_sub]
  show synth (fracTimeIntegral hα hT _ t₂) x - synth (fracTimeIntegral hα hT _ t₁) x = 0
  rw [e₂, e₁, sub_self]

end LiWang.WienerModel
