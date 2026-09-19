/-
# The physical PDE satisfied by the constructed mild state

Step 2 of the v7.0 physical bridge.  Everything here lives in the **physical** carrier
`TorusL2 = L²(𝕋²)`; nothing is a statement about a single Fourier coefficient.

The four physical fields of the problem are

* `physState hT u t = θ(t) ∈ L²(𝕋²)`, the synthesis of the coefficient state;
* `physSource hT f t = f(t) ∈ L²(𝕋²)`, the synthesis of the source;
* `physTransport hm hT u t = ℛ(θ(t))·∇θ(t) ∈ L²(𝕋²)`, the synthesis of the coefficient
  transport form — identified pointwise with the actual product of the velocity field and the
  gradient in `physTransport_apply_ae` (this is where the `2π` normalization, the sign and the
  divergence-free structure are checked), and
* `mildFracField hα hT hm hr u f t`, the field of `PhysicalFractionalField` for the Duhamel
  source `f − N_m(u,u)`.  Under the mild equation, and off the explicit null set where the
  coefficients fail to be square summable, its Fourier coefficients are `λ_k θ_k(t)`
  (`mildFracField_coeff`), so there it is `(-Δ)^α θ(t)`; the definition itself depends on the
  pair `(u, f)`, not on `θ` alone, and no unconditional identity is claimed.

The main theorem `physical_pde_integrated` is the **time-integrated physical equation**

    θ(t) + ∫₀ᵗ ℛ(θ)·∇θ (s) ds + ∫₀ᵗ (-Δ)^α θ(s) ds = ∫₀ᵗ f(s) ds     in `L²(𝕋²)`,

valid for every `t ∈ [0,T]`, together with the genuine (continuous, not almost-everywhere)
initial trace `θ(0) = 0`.  Since the integrand of `physState_eq_integral` is Bochner integrable
on `[0,T]`, this says exactly that `θ` is an `L²`-valued absolutely continuous (`W^{1,1}` in
time) representative whose time derivative, in the integral sense, is
`f − ℛ(θ)·∇θ − (-Δ)^α θ`.

*Scope of the derivative statement, stated exactly.*  What is proved pointwise in time is
`ae_hasDerivAt_pairing_physState`: for every bounded **real** functional `Λ` on `L²(𝕋²)` the
scalar function `t ↦ Λ(θ(t))` has derivative `Λ(f − ℛ(θ)·∇θ − (-Δ)^α θ)(t)` at almost every
interior time.  Mathlib's Lebesgue differentiation theorem is available for real-valued
integrands only, so no a.e. derivative in the norm topology of `L²(𝕋²)` is claimed, and no
statement against test functions in time is proved here either.  The integral identity is the
stronger, unconditional form.

Finally `mean_balance_physical` proves the mean identity `∫_{𝕋²} θ(t) = ∫₀ᵗ ∫_{𝕋²} f(s) ds`
for **arbitrary, in particular nonzero-mean** sources: no mean-zero normalization is imposed
anywhere.  The zero mode of the state is governed by `fracSymbol α 0 = 0` and by the genuine
divergence-free cancellation `transport_rotatedGradient_zero_mode`, which is a different issue
from the unobservable zero mode of the velocity symbol.

Part of `LiWangWienerPhysicalPDEBridgePacket` v7.0.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import LiWangWiener.PhysicalFractionalField

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal NNReal
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The physical fields -/

/-- The **physical state** `θ(t) ∈ L²(𝕋²)` of a coefficient curve. -/
noncomputable def physState (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) : TorusL2 :=
  synthL2 (incl (curveState hT u t))

/-- The **physical source** `f(t) ∈ L²(𝕋²)`. -/
noncomputable def physSource (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) : TorusL2 :=
  synthL2 (sourceFun hT g t)

/-- The **physical transport field** `R(θ(t))·∇θ(t) ∈ L²(𝕋²)`. -/
noncomputable def physTransport (hm : IsBddSymbol m) (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) :
    TorusL2 :=
  synthL2 (quadCurve hm (curveState hT u) t)

theorem continuous_physState (hT : 0 ≤ T) (u : Curve1 T) : Continuous (physState hT u) :=
  synthL2.continuous.comp (incl.continuous.comp (continuous_curveState hT u))

theorem continuous_physSource (hT : 0 ≤ T) (g : Curve0 T) : Continuous (physSource hT g) :=
  synthL2.continuous.comp (continuous_sourceFun hT g)

theorem continuous_physTransport (hm : IsBddSymbol m) (hT : 0 ≤ T) (u : Curve1 T) :
    Continuous (physTransport hm hT u) :=
  synthL2.continuous.comp (continuous_quadCurve hm (continuous_curveState hT u))

/-- **The physical transport field really is the product `R(θ)·∇θ`.**  At almost every point of
the torus the `L²` class `physTransport` is the Euclidean dot product of the velocity field
`R_m(θ(t))` with the gradient `∇θ(t)`, both synthesized from their Fourier data.  The `2π`
normalization sits in `fourierDeriv` (`∂_j e_k = 2πi k_j e_k`, proved analytically in
`hasDerivAt_synth_torus`), and the sign is the one in the equation. -/
theorem physTransport_apply_ae (hm : IsBddSymbol m) (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) :
    (physTransport hm hT u t : Torus2 → ℂ)
      =ᵐ[(volume : Measure Torus2)] fun x =>
        ∑ j : Fin 2,
          synth (velocity m hm j (incl (curveState hT u t))) x
            * synth (fourierDeriv j (curveState hT u t)) x := by
  simp only [physTransport]
  filter_upwards [synthL2_apply_ae (quadCurve hm (curveState hT u) t)] with x hx
  rw [hx]
  exact synth_transport_apply m hm _ _ x

/-! ## 2. Bochner integrability in time -/

theorem intervalIntegrable_physState (hT : 0 ≤ T) (u : Curve1 T) (a b : ℝ) :
    IntervalIntegrable (physState hT u) volume a b :=
  (continuous_physState hT u).intervalIntegrable a b

theorem intervalIntegrable_physSource (hT : 0 ≤ T) (g : Curve0 T) (a b : ℝ) :
    IntervalIntegrable (physSource hT g) volume a b :=
  (continuous_physSource hT g).intervalIntegrable a b

theorem intervalIntegrable_physTransport (hm : IsBddSymbol m) (hT : 0 ≤ T) (u : Curve1 T)
    (a b : ℝ) : IntervalIntegrable (physTransport hm hT u) volume a b :=
  (continuous_physTransport hm hT u).intervalIntegrable a b

/-- The physical fractional-Laplacian field is Bochner integrable on `[0,t]`.  This is a
genuine `L¹`-in-time statement obtained from the `L²`-in-time energy estimate of
`PhysicalFractionalField`; it is **not** a continuity statement — the field is only
strongly measurable. -/
theorem intervalIntegrable_physFracField (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    IntervalIntegrable (physFracField hα hT g) volume 0 t := by
  constructor
  · exact ContinuousLinearMap.integrable_comp coeffL2.toContinuousLinearMap
      (intervalIntegrable_fracFieldW2 hα hT g ht).1
  · exact ContinuousLinearMap.integrable_comp coeffL2.toContinuousLinearMap
      (intervalIntegrable_fracFieldW2 hα hT g ht).2

/-- Synthesis commutes with the time integral of a continuous Wiener-valued curve. -/
theorem synthL2_intervalIntegral {f : ℝ → Wiener} (hf : Continuous f) (a b : ℝ) :
    synthL2 (∫ s in a..b, f s) = ∫ s in a..b, synthL2 (f s) :=
  (synthL2.intervalIntegral_comp_comm (hf.intervalIntegrable a b)).symm

/-! ## 3. The integrated physical equation for a linear Duhamel response -/

/-- **The integrated physical equation for the linear evolution.**  For every `t ∈ [0,T]`

    `θ(t) + ∫₀ᵗ (-Δ)^α θ(s) ds = ∫₀ᵗ g(s) ds`   in `L²(𝕋²)`,

where `θ = J_T g` is the Duhamel response, the fractional term is the Bochner integral of the
genuine strongly measurable field, and the right-hand side is the Bochner integral of the
physical source. -/
theorem phys_duhamel_integrated (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    physState hT (duhamelOp hα hT g) t + ∫ s in (0:ℝ)..t, physFracField hα hT g s
      = ∫ s in (0:ℝ)..t, physSource hT g s := by
  calc physState hT (duhamelOp hα hT g) t + ∫ s in (0:ℝ)..t, physFracField hα hT g s
      = synthL2 (incl (curveState hT (duhamelOp hα hT g) t))
          + synthL2 (fracTimeIntegral hα hT g t) := by
        rw [physState, synthL2_fracTimeIntegral hα hT g ht]
    _ = synthL2 (incl (curveState hT (duhamelOp hα hT g) t) + fracTimeIntegral hα hT g t) :=
        (map_add _ _ _).symm
    _ = synthL2 (∫ s in (0:ℝ)..t, sourceFun hT g s) := by
        rw [strong_equation_integrated hα hT g t]
    _ = ∫ s in (0:ℝ)..t, physSource hT g s :=
        synthL2_intervalIntegral (continuous_sourceFun hT g) 0 t

/-! ## 4. The nonlinear physical equation -/

/-- The source of the Duhamel representation of a mild solution splits pointwise. -/
theorem sourceFun_sub_spacetimeTransport (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) (f : Curve0 T) (s : ℝ) :
    sourceFun hT (f - spacetimeTransport m hm hr u u) s
      = sourceFun hT f s - quadCurve hm (curveState hT u) s := rfl

/-- **The physical fractional-Laplacian field of a mild state.**  It is the field of
`PhysicalFractionalField` for the Duhamel source `f − N_m(u,u)`; under the mild equation its
Fourier coefficients are `λ_k u_k(t)` off the explicit null set (`mildFracField_coeff`). -/
noncomputable def mildFracField (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) (f : Curve0 T) (t : ℝ) : TorusL2 :=
  physFracField hα hT (f - spacetimeTransport m hm hr u u) t

/-- **The physical multiplier check.**  Off an explicit null set the Fourier coefficients of the
physical field `(-Δ)^α θ(t)` are exactly `λ_k θ_k(t)` with `λ_k = (4π²|k|²)^α`. -/
theorem mildFracField_coeff (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t : ℝ}
    (h : FracSummableAt hα hT (f - spacetimeTransport m hm hr u u) t) (k : Gam) :
    (fracFieldW2 hα hT (f - spacetimeTransport m hm hr u u) t) k
      = (fracSymbol α k : ℂ) * (curveState hT u t).coeff k := by
  rw [fracFieldW2_apply h k, ← mild_curve_eq_duhamelOp hα hT hm hr hmild]

theorem ae_fracSummable_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) (f : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      FracSummableAt hα hT (f - spacetimeTransport m hm hr u u) t :=
  ae_fracSummable hα hT _

theorem intervalIntegrable_mildFracField (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) (f : Curve0 T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    IntervalIntegrable (mildFracField hα hT hm hr u f) volume 0 t :=
  intervalIntegrable_physFracField hα hT _ ht

/-- **The physical PDE, in integrated form.**  For every `t ∈ [0,T]`,

    `θ(t) + ∫₀ᵗ R(θ)·∇θ (s) ds + ∫₀ᵗ (-Δ)^α θ(s) ds = ∫₀ᵗ f(s) ds`

as an identity in `L²(𝕋²)`.  Every term is a genuine physical object: `θ(t)` is the `L²`
state, the transport integrand is the pointwise product of the velocity field with the
gradient, and the fractional integrand is the Bochner integral of the strongly measurable
field with the correct Fourier multiplier. -/
theorem physical_pde_integrated (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    physState hT u t + (∫ s in (0:ℝ)..t, physTransport hm hT u s)
        + ∫ s in (0:ℝ)..t, mildFracField hα hT hm hr u f s
      = ∫ s in (0:ℝ)..t, physSource hT f s := by
  set g : Curve0 T := f - spacetimeTransport m hm hr u u with hgdef
  have hu : u = duhamelOp hα hT g := mild_curve_eq_duhamelOp hα hT hm hr hmild
  have hbase := phys_duhamel_integrated hα hT g ht
  rw [← hu] at hbase
  have hsrc : ∀ s : ℝ, physSource hT g s = physSource hT f s - physTransport hm hT u s := by
    intro s
    rw [physSource, physSource, physTransport, hgdef,
      sourceFun_sub_spacetimeTransport hT hm hr u f s, map_sub]
  have hsplit : (∫ s in (0:ℝ)..t, physSource hT g s)
      = (∫ s in (0:ℝ)..t, physSource hT f s) - ∫ s in (0:ℝ)..t, physTransport hm hT u s := by
    rw [intervalIntegral.integral_congr (g := fun s => physSource hT f s - physTransport hm hT u s)
      (fun s _ => hsrc s)]
    exact intervalIntegral.integral_sub (intervalIntegrable_physSource hT f 0 t)
      (intervalIntegrable_physTransport hm hT u 0 t)
  rw [hsplit, eq_sub_iff_add_eq] at hbase
  have hmf : mildFracField hα hT hm hr u f = physFracField hα hT g := rfl
  rw [hmf, ← hbase]
  abel

/-! ## 5. The initial trace -/

/-- **The initial trace is a genuine trace**, not an almost-everywhere statement: the physical
state is continuous in time with values in `L²(𝕋²)` and vanishes at `t = 0`. -/
theorem physState_initial_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    physState hT u 0 = 0 := by
  rw [physState, curveState_initial_of_mild hα hT hm hr hmild, map_zero, map_zero]

/-! ## 6. The absolutely continuous representative -/

/-- **The `L²`-valued absolutely continuous (`W^{1,1}`-in-time) representative.**  The physical
state is the indefinite Bochner integral of the integrable field
`f − R(θ)·∇θ − (-Δ)^α θ`, which is exactly the statement that `θ` is absolutely continuous in
time with values in `L²(𝕋²)`, with that field as its time derivative in the integral sense; the
pointwise form, for every bounded real observable, is `ae_hasDerivAt_pairing_physState`. -/
theorem physState_eq_integral (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    physState hT u t
      = ∫ s in (0:ℝ)..t,
          (physSource hT f s - physTransport hm hT u s - mildFracField hα hT hm hr u f s) := by
  have hmain := physical_pde_integrated hα hT hm hr hmild ht
  have h1 : (∫ s in (0:ℝ)..t,
        (physSource hT f s - physTransport hm hT u s - mildFracField hα hT hm hr u f s))
      = ((∫ s in (0:ℝ)..t, physSource hT f s) - ∫ s in (0:ℝ)..t, physTransport hm hT u s)
          - ∫ s in (0:ℝ)..t, mildFracField hα hT hm hr u f s := by
    rw [intervalIntegral.integral_sub
      ((intervalIntegrable_physSource hT f 0 t).sub (intervalIntegrable_physTransport hm hT u 0 t))
      (intervalIntegrable_mildFracField hα hT hm hr u f ht),
      intervalIntegral.integral_sub (intervalIntegrable_physSource hT f 0 t)
        (intervalIntegrable_physTransport hm hT u 0 t)]
  rw [h1, ← hmain]
  abel


/-! ## 7. The time derivative field and the absolutely continuous representative -/

/-- The **physical right-hand side** `f − R(θ)·∇θ − (-Δ)^α θ`, an `L²(𝕋²)`-valued Bochner
integrable field on `[0,T]`. -/
noncomputable def physRHS (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) (f : Curve0 T) (s : ℝ) : TorusL2 :=
  physSource hT f s - physTransport hm hT u s - mildFracField hα hT hm hr u f s

theorem intervalIntegrable_physRHS (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u : Curve1 T) (f : Curve0 T) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    IntervalIntegrable (physRHS hα hT hm hr u f) volume 0 t :=
  ((intervalIntegrable_physSource hT f 0 t).sub
      (intervalIntegrable_physTransport hm hT u 0 t)).sub
    (intervalIntegrable_mildFracField hα hT hm hr u f ht)

/-- **The `L²`-valued absolutely continuous representative.**  The physical state is the
indefinite Bochner integral of the integrable field `f − R(θ)·∇θ − (-Δ)^α θ`.  This is exactly
the assertion that `θ ∈ W^{1,1}(0,T;L²(𝕋²))` with that field as its time derivative; in
particular `θ` is absolutely continuous in time (see `norm_physState_sub_le`).  No statement
against test functions in time is proved here; see the scope note in the file header. -/
theorem physState_eq_integral_physRHS (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    physState hT u t = ∫ s in (0:ℝ)..t, physRHS hα hT hm hr u f s :=
  physState_eq_integral hα hT hm hr hmild ht

/-- **The increment identity.**  For any two times in `[0,T]`. -/
theorem physState_sub_eq_integral (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) (ht' : t' ∈ Set.Icc (0:ℝ) T) :
    physState hT u t - physState hT u t' = ∫ s in t'..t, physRHS hα hT hm hr u f s := by
  rw [physState_eq_integral hα hT hm hr hmild ht, physState_eq_integral hα hT hm hr hmild ht']
  exact intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_physRHS hα hT hm hr u f ht)
    (intervalIntegrable_physRHS hα hT hm hr u f ht')

/-- **Absolute continuity in `L²(𝕋²)`**: the increment is controlled by the `L¹`-in-time norm of
the derivative field on the corresponding subinterval. -/
theorem norm_physState_sub_le (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) (ht' : t' ∈ Set.Icc (0:ℝ) T) (htt : t' ≤ t) :
    ‖physState hT u t - physState hT u t'‖
      ≤ ∫ s in t'..t, ‖physRHS hα hT hm hr u f s‖ := by
  rw [physState_sub_eq_integral hα hT hm hr hmild ht ht']
  exact intervalIntegral.norm_integral_le_integral_norm htt

/-! ## 8. The pointwise time derivative of every real observable -/

/-- **Almost-everywhere differentiability in time of every bounded real observable.**  For each
continuous real-linear functional `Λ` on `L²(𝕋²)`, the scalar function `t ↦ Λ(θ(t))` is
differentiable at almost every interior time with derivative
`Λ(f(t) − R(θ(t))·∇θ(t) − (-Δ)^α θ(t))`.  This is the Lebesgue-differentiation form of the
statement `∂_t θ = f − R(θ)·∇θ − (-Δ)^α θ`. -/
theorem ae_hasDerivAt_pairing_physState (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (Λ : TorusL2 →L[ℝ] ℝ) :
    ∀ᵐ t : ℝ, t ∈ Set.Ioo (0:ℝ) T →
      HasDerivAt (fun r : ℝ => Λ (physState hT u r))
        (Λ (physRHS hα hT hm hr u f t)) t := by
  have hTmem : T ∈ Set.Icc (0:ℝ) T := ⟨hT, le_rfl⟩
  have hint : IntervalIntegrable (fun s => Λ (physRHS hα hT hm hr u f s)) volume 0 T := by
    constructor
    · exact ContinuousLinearMap.integrable_comp Λ
        (intervalIntegrable_physRHS hα hT hm hr u f hTmem).1
    · exact ContinuousLinearMap.integrable_comp Λ
        (intervalIntegrable_physRHS hα hT hm hr u f hTmem).2
  have heq : ∀ r ∈ Set.Icc (0:ℝ) T,
      Λ (physState hT u r) = ∫ s in (0:ℝ)..r, Λ (physRHS hα hT hm hr u f s) := by
    intro r hrmem
    rw [physState_eq_integral hα hT hm hr hmild hrmem]
    exact (Λ.intervalIntegral_comp_comm (intervalIntegrable_physRHS hα hT hm hr u f hrmem)).symm
  have huIcc : Set.uIcc (0:ℝ) T = Set.Icc (0:ℝ) T := Set.uIcc_of_le hT
  filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hint] with t hLDT htmem
  have htIcc : t ∈ Set.uIcc (0:ℝ) T := by
    rw [huIcc]; exact ⟨htmem.1.le, htmem.2.le⟩
  have h0 : (0:ℝ) ∈ Set.uIcc (0:ℝ) T := by rw [huIcc]; exact ⟨le_rfl, hT⟩
  have hbase := hLDT htIcc 0 h0
  refine hbase.congr_of_eventuallyEq ?_
  have hopen : Set.Ioo (0:ℝ) T ∈ nhds t := isOpen_Ioo.mem_nhds htmem
  filter_upwards [hopen] with r hrmem
  exact heq r ⟨hrmem.1.le, hrmem.2.le⟩

/-! ## 9. The mean balance with nonzero-mean forcing -/

/-- The **physical spatial mean** of an `L²(𝕋²)` class (the torus carries normalized Haar
measure, so this is the average value). -/
noncomputable def torusMean (θ : TorusL2) : ℂ := ∫ x : Torus2, (θ : Torus2 → ℂ) x

/-- The mean of a synthesized state is its zero Fourier coefficient. -/
theorem torusMean_synthL2 (a : Wiener) : torusMean (synthL2 a) = a 0 := by
  have h1 : torusMean (synthL2 a) = ∫ x : Torus2, synth a x := by
    rw [torusMean]
    exact integral_congr_ae (synthL2_apply_ae a)
  have h2 : (∫ x : Torus2, synth a x) = ∫ x : Torus2, synth a x * emode (0 : Gam) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [emode_zero]
    simp
  rw [h1, h2, integral_synth_mul_emode a 0, neg_zero]

/-- **The divergence-free cancellation at the zero mode.**  For the rotated-gradient velocity
`R_κ = ∇^⊥(κ ⋆ ·)` the transport form has vanishing zero Fourier mode: the two components
cancel term by term, which is the coefficient form of `∫_{𝕋²} R(θ)·∇θ dx = 0`.  This is a
statement about the state's mean, and is unrelated to the unobservable zero mode of the
velocity symbol. -/
theorem transport_rotatedGradient_zero_mode {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (u v : Wiener1) :
    (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) u v) (0 : Gam) = 0 := by
  rw [transport_apply_coeff, Fin.sum_univ_two]
  have hB : ∀ p : Gam,
      (rotatedGradientSymbol κ 1 p * u.coeff p)
          * (twoPiI * ((((0 : Gam) - p) 1 : ℤ) : ℂ) * v.coeff ((0 : Gam) - p))
        = -((rotatedGradientSymbol κ 0 p * u.coeff p)
          * (twoPiI * ((((0 : Gam) - p) 0 : ℤ) : ℂ) * v.coeff ((0 : Gam) - p))) := by
    intro p
    have h0 : (((0 : Gam) - p) 0 : ℤ) = -(p 0) := by
      show (0 : ℤ) - p 0 = -(p 0)
      ring
    have h1 : (((0 : Gam) - p) 1 : ℤ) = -(p 1) := by
      show (0 : ℤ) - p 1 = -(p 1)
      ring
    rw [h0, h1, rotatedGradientSymbol_zero_comp, rotatedGradientSymbol_one_comp]
    push_cast
    ring
  rw [tsum_congr hB, tsum_neg]
  ring

/-- **The zero-mode balance of the linear evolution.**  Since `λ_0 = 0`, the zero Fourier
coefficient of a Duhamel response is the plain time primitive of the zero coefficient of its
source. -/
theorem coeff_zero_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT (duhamelOp hα hT g) t).coeff 0 = ∫ s in (0:ℝ)..t, (sourceFun hT g s) 0 := by
  have hα0 : (0:ℝ) < α := by linarith
  have h := coeff_duhamelOp_integrated hα hT g 0 ht
  rw [fracSymbol_zero_eq hα0] at h
  simpa using h

/-- **The mean balance of the nonlinear physical equation, with arbitrary (in particular
nonzero-mean) forcing.**  No mean-zero normalization is imposed on the control: the zero mode
of the state is the exact time primitive of the zero mode of the source, because the
fractional symbol annihilates the zero mode and the transport term has no zero mode. -/
theorem coeff_zero_balance_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) {κ : Gam → ℂ}
    (hb : IsAdmissibleKernel κ) (hr : IsRealSymbol (rotatedGradientSymbol κ))
    {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) hr u u
      = duhamelOp hα hT f) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT u t).coeff 0 = ∫ s in (0:ℝ)..t, (sourceFun hT f s) 0 := by
  set hm := rotatedGradientSymbol_bdd hb with hmdef
  set g : Curve0 T := f - spacetimeTransport (rotatedGradientSymbol κ) hm hr u u with hgdef
  have hu : u = duhamelOp hα hT g := mild_curve_eq_duhamelOp hα hT hm hr hmild
  have hsrc : ∀ s : ℝ, (sourceFun hT g s) 0 = (sourceFun hT f s) 0 := by
    intro s
    have hsplit : sourceFun hT g s
        = sourceFun hT f s - quadCurve hm (curveState hT u) s :=
      sourceFun_sub_spacetimeTransport hT hm hr u f s
    rw [hsplit, lp.coeFn_sub, Pi.sub_apply,
      show quadCurve hm (curveState hT u) s
        = transport (rotatedGradientSymbol κ) hm (curveState hT u s) (curveState hT u s) from rfl,
      transport_rotatedGradient_zero_mode hb, sub_zero]
  rw [hu, coeff_zero_duhamelOp hα hT g ht]
  exact intervalIntegral.integral_congr (fun s _ => hsrc s)

/-- **The mean balance in physical form.**  `∫_{𝕋²} θ(t,x) dx = ∫₀ᵗ ∫_{𝕋²} f(s,x) dx ds`. -/
theorem mean_balance_physical (hα : 1 / 2 < α) (hT : 0 ≤ T) {κ : Gam → ℂ}
    (hb : IsAdmissibleKernel κ) (hr : IsRealSymbol (rotatedGradientSymbol κ))
    {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) hr u u
      = duhamelOp hα hT f) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    torusMean (physState hT u t) = ∫ s in (0:ℝ)..t, torusMean (physSource hT f s) := by
  have hL : torusMean (physState hT u t) = (curveState hT u t).coeff 0 := by
    rw [physState, torusMean_synthL2]
    rfl
  have hR : ∀ s : ℝ, torusMean (physSource hT f s) = (sourceFun hT f s) 0 := by
    intro s
    rw [physSource, torusMean_synthL2]
  rw [hL, coeff_zero_balance_of_mild hα hT hb hr hmild ht]
  exact (intervalIntegral.integral_congr (fun s _ => hR s)).symm

end LiWang.WienerModel
