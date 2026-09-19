/-
# From local cancellation to the generated-source identity

The platform supplies spatial fractional unique continuation.  Here that theorem is the
**single external input**, stated as an explicit `Prop` for actual physical fields in the
fractional graph domain — never as an axiom, and never as injectivity of the nonlinear
observation map.  Every analytic premise it needs is *discharged* by `local_cancellation`.

Given it, two small solutions with the same localized source and equal measured state and
velocity on `W` are shown to be globally equal (first at interior times, then as continuous
curves).  Applying this to the whole germ of localized sources and letting the source scale to
zero along a ray produces the **generated-source identity**

    N_δ(J h₁, J h₂) + N_δ(J h₂, J h₁) = 0 ,     N_δ = N_{m₁ - m₂} ,

for all localized directions `h₁, h₂`, using the already proved second-variation formula and
the injectivity of the Duhamel operator.

Every statement using the external hypothesis is labelled **conditional**; nothing here
completes the Li–Wang inverse theorem.

Part of `LiWangFormalizationObservationBridgePacket` v4.0.
-/
import LiWangFormalization.LocalCancellation
import LiWangFormalization.SecondResponseNonzero

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## The external hypothesis -/

/-- **Spatial fractional unique continuation, as an explicit hypothesis.**

If `v` is an actual first-order Wiener state, its fractional Laplacian is again an actual
element of the Wiener algebra (given by the explicit coefficient family `λ_k v_k`), and both
physical fields vanish on the nonempty open set `W`, then `v = 0`.

This is a `Prop`, parameterised by `α` and `W`.  It is **never** assumed globally, only carried
as a hypothesis of the conditional theorems below, and it is a statement about physical fields
in a precisely specified domain — not about the nonlinear observation map. -/
def FractionalUCP (α : ℝ) (W : Set Torus2) : Prop :=
  ∀ (v : Wiener1) (F : Wiener),
    (∀ k : Gam, F k = (fracSymbol α k : ℂ) * v.coeff k) →
    (∀ x ∈ W, synth (incl v) x = 0) →
    (∀ x ∈ W, synth F x = 0) →
    v = 0

/-! ## Global equality of two solutions with equal observations -/

/-- **Conditional.**  Under the external UCP hypothesis, two mild solutions of the same source
with equal measured state and velocity on `W` have vanishing time primitive, hence agree at
every interior time, hence — being continuous curves — agree everywhere. -/
theorem curve_eq_of_ucp (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {u₁ u₂ : Curve1 T} {f : Curve0 T}
    (h₁ : u₁ + sourceQuad hα hT.le m₁ hm₁ hr₁ u₁ u₁ = duhamelOp hα hT.le f)
    (h₂ : u₂ + sourceQuad hα hT.le m₂ hm₂ hr₂ u₂ u₂ = duhamelOp hα hT.le f)
    (hobsState : ∀ (t : TimeI T), ∀ x ∈ W,
      synth (incl (u₁ t).val) x = synth (incl (u₂ t).val) x)
    (hobsVel : ∀ (j : Fin 2) (t : TimeI T), ∀ x ∈ W,
      synth (velocity m₁ hm₁ j (incl (u₁ t).val)) x
        = synth (velocity m₂ hm₂ j (incl (u₂ t).val)) x) :
    u₁ = u₂ := by
  set hT' : (0:ℝ) ≤ T := hT.le with hTdef
  set w : Curve1 T := u₁ - u₂ with hw
  set g : Curve0 T :=
    spacetimeTransport m₂ hm₂ hr₂ u₂ u₂ - spacetimeTransport m₁ hm₁ hr₁ u₁ u₁ with hg
  -- Step 1: the time primitive vanishes, by UCP
  have hprim : ∀ t ∈ Set.Icc (0:ℝ) T, timePrimitive hT' w t = 0 := by
    intro t ht
    refine hUCP (timePrimitive hT' w t) (fracTimeIntegral hα hT' g t) ?_ ?_ ?_
    · intro k
      exact coeff_fracTimeIntegral_diff hα hT' hm₁ hr₁ hm₂ hr₂ h₁ h₂ ht k
    · intro x hx
      exact (local_cancellation hα hT' hW hm₁ hr₁ hm₂ hr₂ h₁ h₂ hobsState hobsVel ht hx).1
    · intro x hx
      exact (local_cancellation hα hT' hW hm₁ hr₁ hm₂ hr₂ h₁ h₂ hobsState hobsVel ht hx).2.1
  -- Step 2: differentiate the primitive
  have hstate : ∀ t ∈ Set.Ioo (0:ℝ) T, curveState hT' w t = 0 := by
    intro t ht
    have hFTC : HasDerivAt (fun r : ℝ => timePrimitive hT' w r) (curveState hT' w t) t :=
      intervalIntegral.integral_hasDerivAt_right
        ((continuous_curveState hT' w).intervalIntegrable 0 t)
        ((continuous_curveState hT' w).stronglyMeasurableAtFilter _ _)
        (continuous_curveState hT' w).continuousAt
    have hzero : HasDerivAt (fun r : ℝ => timePrimitive hT' w r) 0 t := by
      have hev : (fun r : ℝ => timePrimitive hT' w r) =ᶠ[nhds t] fun _ : ℝ => (0 : Wiener1) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
        exact hprim r ⟨hr.1.le, hr.2.le⟩
      exact (hasDerivAt_const t (0 : Wiener1)).congr_of_eventuallyEq hev
    exact hFTC.unique hzero
  -- Step 3: upgrade to the closed interval by continuity
  have hclosed : ∀ t ∈ Set.Icc (0:ℝ) T, curveState hT' w t = 0 := by
    have hcl : Set.Icc (0:ℝ) T ⊆ {t : ℝ | curveState hT' w t = 0} := by
      have hsub : Set.Ioo (0:ℝ) T ⊆ {t : ℝ | curveState hT' w t = 0} := hstate
      have hclosedSet : IsClosed {t : ℝ | curveState hT' w t = 0} :=
        isClosed_eq (continuous_curveState hT' w) continuous_const
      have := closure_minimal hsub hclosedSet
      rwa [closure_Ioo (ne_of_lt hT)] at this
    exact fun t ht => hcl ht
  -- Step 4: the curve is zero
  have hzero : w = 0 := by
    ext t
    apply RealWiener1.val_injective
    have := hclosed (t : ℝ) ⟨t.2.1, t.2.2⟩
    rw [curveState_coe hT' w t] at this
    rw [this]
    rfl
  have := sub_eq_zero.mp hzero
  exact this

/-! ## From equality of the solutions to the generated-source identity -/

/-- If two solutions of the *same* source coincide, the difference of the two transport
operators annihilates their common value.  Proved from the two mild identities and the
**injectivity of the Duhamel operator**, not assumed. -/
theorem transport_diff_self_eq_zero (hα : 1 / 2 < α) (hT : 0 < T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {u : Curve1 T} {f : Curve0 T}
    (h₁ : u + sourceQuad hα hT.le m₁ hm₁ hr₁ u u = duhamelOp hα hT.le f)
    (h₂ : u + sourceQuad hα hT.le m₂ hm₂ hr₂ u u = duhamelOp hα hT.le f) :
    spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) u u = 0 := by
  have hsub : (spacetimeTransport m₁ hm₁ hr₁ : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve0 T)
      - spacetimeTransport m₂ hm₂ hr₂
      = spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) :=
    spacetimeTransport_sub hm₁ hm₂ hr₁ hr₂
  have hq : duhamelOp hα hT.le (spacetimeTransport m₁ hm₁ hr₁ u u)
      = duhamelOp hα hT.le (spacetimeTransport m₂ hm₂ hr₂ u u) := by
    have e₁ : sourceQuad hα hT.le m₁ hm₁ hr₁ u u
        = duhamelOp hα hT.le (spacetimeTransport m₁ hm₁ hr₁ u u) := rfl
    have e₂ : sourceQuad hα hT.le m₂ hm₂ hr₂ u u
        = duhamelOp hα hT.le (spacetimeTransport m₂ hm₂ hr₂ u u) := rfl
    rw [e₁] at h₁
    rw [e₂] at h₂
    have := h₁.trans h₂.symm
    exact add_left_cancel this
  have hzero : duhamelOp hα hT.le
      (spacetimeTransport m₁ hm₁ hr₁ u u - spacetimeTransport m₂ hm₂ hr₂ u u) = 0 := by
    rw [map_sub, hq, sub_self]
  have hdiff : spacetimeTransport m₁ hm₁ hr₁ u u - spacetimeTransport m₂ hm₂ hr₂ u u = 0 :=
    eq_zero_of_duhamelOp_eq_zero hα hT hzero
  have hval : spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) u u
      = spacetimeTransport m₁ hm₁ hr₁ u u - spacetimeTransport m₂ hm₂ hr₂ u u := by
    rw [← hsub]; rfl
  rw [hval, hdiff]

/-- Homogeneity of the quadratic form. -/
theorem quad_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) (c : ℝ) (v : E) :
    quad B (c • v) = (c * c) • quad B v := by
  show B (c • v) (c • v) = (c * c) • B v v
  rw [map_smul B c v, ContinuousLinearMap.smul_apply, map_smul, smul_smul]

/-- Polarization: a symmetric-part identity from vanishing of the quadratic form at `a`, `b`
and `a + b`. -/
theorem polarization_of_quad_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {B : E →L[ℝ] E →L[ℝ] F} {a b : E}
    (ha : quad B a = 0) (hb : quad B b = 0) (hab : quad B (a + b) = 0) :
    B a b + B b a = 0 := by
  have hexp : quad B (a + b) = quad B a + (B a b + B b a) + quad B b := by
    show B (a + b) (a + b) = B a a + (B a b + B b a) + B b b
    rw [map_add B a b, ContinuousLinearMap.add_apply, map_add, map_add]
    abel
  rw [ha, hb, hab] at hexp
  have : (0 : F) = B a b + B b a := by
    rw [hexp]; abel
  exact this.symm

set_option maxHeartbeats 1000000 in
/-- **The ray limit.**  If the transport difference annihilates the solution for every
sufficiently small multiple of `h`, it annihilates the first response `J h`. -/
theorem transport_diff_duhamelOp_self_eq_zero (hα : 1 / 2 < α) (hT : 0 < T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {h : Curve0 T} {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ s : ℝ, |s| * ‖h‖ < ε →
      quad (spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂))
        (sourceSolution hα hT.le hm₁ hr₁ (s • h)) = 0) :
    quad (spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂))
      (duhamelOp hα hT.le h) = 0 := by
  set B := spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) with hB
  set S := sourceSolution hα hT.le hm₁ hr₁ with hS
  set φ : ℝ → Curve1 T := fun s => S (s • h) with hφ
  -- the derivative of the ray
  have hray : HasDerivAt (fun s : ℝ => s • h) h (0:ℝ) := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const h
  have hzero0 : ((0:ℝ) • h) = (0 : Curve0 T) := zero_smul ℝ h
  have hFD : HasFDerivAt S (duhamelOp hα hT.le : Curve0 T →L[ℝ] Curve1 T) ((0:ℝ) • h) := by
    rw [hzero0]
    exact hasFDerivAt_sourceSolution_zero hα hT.le hm₁ hr₁
  have hderiv0 : HasDerivAt (S ∘ fun s : ℝ => s • h) (duhamelOp hα hT.le h) 0 :=
    hFD.comp_hasDerivAt 0 hray
  have hderiv : HasDerivAt φ (duhamelOp hα hT.le h) 0 := hderiv0
  have hslope := hasDerivAt_iff_tendsto_slope.1 hderiv
  -- the quadratic form is continuous
  have hcont : Continuous (quad B) := (contDiff_quad B 1).continuous
  have hlim : Tendsto (fun s : ℝ => quad B (slope φ 0 s)) (nhdsWithin 0 {(0:ℝ)}ᶜ)
      (nhds (quad B (duhamelOp hα hT.le h))) := (hcont.tendsto _).comp hslope
  -- but it is eventually zero
  have hnb : ∀ᶠ s : ℝ in nhds (0:ℝ), |s| * ‖h‖ < ε := by
    have hc : Continuous fun s : ℝ => |s| * ‖h‖ := continuous_abs.mul continuous_const
    have h0 : |(0:ℝ)| * ‖h‖ < ε := by simpa using hε
    exact hc.continuousAt.eventually_lt_const h0
  have hev : ∀ᶠ s : ℝ in nhdsWithin 0 {(0:ℝ)}ᶜ, quad B (slope φ 0 s) = 0 := by
    filter_upwards [nhdsWithin_le_nhds hnb, self_mem_nhdsWithin] with s hs hs0
    have hsne : s ≠ 0 := hs0
    have hφ0 : φ 0 = 0 := by
      rw [hφ]
      show S ((0:ℝ) • h) = 0
      rw [hzero0, hS]
      exact sourceSolution_zero hα hT.le hm₁ hr₁
    have hsl : slope φ 0 s = s⁻¹ • φ s := by
      simp [slope, hφ0]
    rw [hsl, quad_smul, hzero s hs, smul_zero]
  have hzerolim : Tendsto (fun s : ℝ => quad B (slope φ 0 s)) (nhdsWithin 0 {(0:ℝ)}ᶜ)
      (nhds 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : Curve0 T))
      (f := nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ))
    filter_upwards [hev] with s hs
    exact hs.symm
  exact (tendsto_nhds_unique hlim hzerolim)

/-! ## The generated-source identity -/

/-- The hypothesis that the two **measured maps** — state and velocity observed on `W` —
agree on every localized source of norm below `ε`. -/
def MeasuredMapsAgree (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (ε : ℝ) : Prop :=
  ∀ f ∈ localizedSources hT W, ‖f‖ < ε →
    (∀ (t : TimeI T), ∀ x ∈ W,
        synth (incl ((sourceSolution hα hT hm₁ hr₁ f) t).val) x
          = synth (incl ((sourceSolution hα hT hm₂ hr₂ f) t).val) x)
      ∧ (∀ (j : Fin 2) (t : TimeI T), ∀ x ∈ W,
        synth (velocity m₁ hm₁ j (incl ((sourceSolution hα hT hm₁ hr₁ f) t).val)) x
          = synth (velocity m₂ hm₂ j (incl ((sourceSolution hα hT hm₂ hr₂ f) t).val)) x)

/-- The hypothesis that both proved mild identities hold on the localized ball of radius `ε`.
`exists_radius_two_kernel_mild` produces such an `ε`. -/
def BothMildOn (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (ε : ℝ) : Prop :=
  ∀ f ∈ localizedSources hT W, ‖f‖ < ε →
    (sourceSolution hα hT hm₁ hr₁ f
        + sourceQuad hα hT m₁ hm₁ hr₁ (sourceSolution hα hT hm₁ hr₁ f)
            (sourceSolution hα hT hm₁ hr₁ f) = duhamelOp hα hT f)
      ∧ (sourceSolution hα hT hm₂ hr₂ f
        + sourceQuad hα hT m₂ hm₂ hr₂ (sourceSolution hα hT hm₂ hr₂ f)
            (sourceSolution hα hT hm₂ hr₂ f) = duhamelOp hα hT f)

theorem exists_bothMildOn (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) :
    ∃ ε > 0, BothMildOn hα hT W hm₁ hr₁ hm₂ hr₂ ε := by
  obtain ⟨ε, hε, hball⟩ := exists_radius_two_kernel_mild hα hT hm₁ hr₁ hm₂ hr₂ W
  exact ⟨ε, hε, hball⟩

/-- **Conditional (on the external UCP hypothesis).**  Equal measured maps on localized
sources force the transport difference to annihilate the solution, for every localized source
in the ball. -/
theorem quad_transport_diff_sourceSolution_eq_zero (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {ε : ℝ}
    (hmild : BothMildOn hα hT.le W hm₁ hr₁ hm₂ hr₂ ε)
    (hobs : MeasuredMapsAgree hα hT.le W hm₁ hr₁ hm₂ hr₂ ε)
    {f : Curve0 T} (hf : f ∈ localizedSources hT.le W) (hfn : ‖f‖ < ε) :
    quad (spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂))
      (sourceSolution hα hT.le hm₁ hr₁ f) = 0 := by
  obtain ⟨hm1, hm2⟩ := hmild f hf hfn
  obtain ⟨hs, hv⟩ := hobs f hf hfn
  have heq : sourceSolution hα hT.le hm₁ hr₁ f = sourceSolution hα hT.le hm₂ hr₂ f :=
    curve_eq_of_ucp hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hm1 hm2 hs hv
  have hm2' : sourceSolution hα hT.le hm₁ hr₁ f
      + sourceQuad hα hT.le m₂ hm₂ hr₂ (sourceSolution hα hT.le hm₁ hr₁ f)
          (sourceSolution hα hT.le hm₁ hr₁ f) = duhamelOp hα hT.le f := by
    rw [heq]; exact hm2
  exact transport_diff_self_eq_zero hα hT hm₁ hr₁ hm₂ hr₂ hm1 hm2'

/-- **Conditional (on the external UCP hypothesis).  The generated-source identity.**

If the two measured maps agree on all localized sources of norm below `ε`, then for all
localized directions `h₁, h₂`,

    `N_δ(J h₁, J h₂) + N_δ(J h₂, J h₁) = 0`,   `N_δ = N_{m₁ - m₂}`.

The proof discharges every analytic premise: local cancellation, UCP (the one external
input), injectivity of the Duhamel operator, the ray limit and polarization. -/
theorem generated_source_identity (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOn hα hT.le W hm₁ hr₁ hm₂ hr₂ ε)
    (hobs : MeasuredMapsAgree hα hT.le W hm₁ hr₁ hm₂ hr₂ ε)
    {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ localizedSources hT.le W)
    (hh₂ : h₂ ∈ localizedSources hT.le W) :
    spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT.le h₁) (duhamelOp hα hT.le h₂)
      + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT.le h₂) (duhamelOp hα hT.le h₁) = 0 := by
  set B := spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) with hB
  have key : ∀ h : Curve0 T, h ∈ localizedSources hT.le W →
      quad B (duhamelOp hα hT.le h) = 0 := by
    intro h hh
    refine transport_diff_duhamelOp_self_eq_zero hα hT hm₁ hr₁ hm₂ hr₂ hε ?_
    intro s hs
    have hmem : (s • h) ∈ localizedSources hT.le W := Submodule.smul_mem _ s hh
    have hnorm : ‖s • h‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs]
      exact hs
    exact quad_transport_diff_sourceSolution_eq_zero hα hT hW hUCP hm₁ hr₁ hm₂ hr₂
      hmild hobs hmem hnorm
  have ha := key h₁ hh₁
  have hb := key h₂ hh₂
  have hab := key (h₁ + h₂) (Submodule.add_mem _ hh₁ hh₂)
  rw [map_add] at hab
  exact polarization_of_quad_zero ha hb hab

/-- **Conditional.**  Consequently the two second source responses agree on localized
directions. -/
theorem fderiv_fderiv_sourceSolution_eq_on_localized (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOn hα hT.le W hm₁ hr₁ hm₂ hr₂ ε)
    (hobs : MeasuredMapsAgree hα hT.le W hm₁ hr₁ hm₂ hr₂ ε)
    {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ localizedSources hT.le W)
    (hh₂ : h₂ ∈ localizedSources hT.le W) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₁ hr₁)) (0 : Curve0 T) h₁ h₂
      = fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₂ hr₂)) (0 : Curve0 T) h₁ h₂ := by
  have hgen := generated_source_identity hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hε hmild hobs hh₁ hh₂
  have hdiff := fderiv_fderiv_sourceSolution_sub hα hT.le hm₁ hr₁ hm₂ hr₂ h₁ h₂
  rw [hgen, map_zero, neg_zero] at hdiff
  exact sub_eq_zero.mp hdiff

end LiWang.Formalization
