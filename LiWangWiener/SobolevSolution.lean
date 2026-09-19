/-
# The paper's Sobolev solutions, and their `A¹` representative

Step 2 of the v8.0 Sobolev-compatibility bridge.

`IsSobolevSolution` is the solution class this packet compares with.  Its state is an
**`L²(𝕋²)`-valued function of time** — not a `Curve1 T`, and not an `A¹` object of any kind.
Its fields are:

* `coeff_continuous` — each Fourier coordinate is continuous in time (weak-`L²` time
  continuity: this is an explicit *regularity hypothesis*, listed as such in `STATUS.md`);
* `real` — the state is real valued (conjugate symmetry of the coordinates);
* `bound` — a uniform `H³` bound, stated on **finite partial sums** so that it can be upgraded
  from an almost-everywhere hypothesis by `forall_finset_sum_le_of_ae`;
* `initial` — zero initial trace, as an identity in `L²(𝕋²)`;
* `weak` — the time-integrated weak equation, tested against arbitrary trigonometric
  polynomials, with `(-Δ)^α` moved onto the test function.

The predicate contains **no** `A¹` representation, **no** equality to `sourceSolution`, and no
part of the inverse conclusion: the `A¹` membership of the state is *derived* from the `H³`
bound by `SobolevEmbedding`, and the `A¹`-valued time continuity is *derived* from
`coeff_continuous` plus the uniform bound by `SobolevCurve`.

The main theorem is `IsSobolevSolution.isPhysicalSolution_curve`: the constructed representative satisfies the
v7 predicate `IsPhysicalSolution`, so the whole checked chain — `mild_of_isPhysicalSolution`,
`mild_curve_unique`, `eq_of_isPhysicalSolution` — applies to it unchanged.

Part of `LiWangWienerSobolevCompatibilityPacket` v8.0.
-/
import LiWangWiener.SobolevCurve
import LiWangWiener.PhysicalComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The `A¹` state of an `H³`-bounded `L²` family -/

/-- The `A¹` element of the state at one time, built from the uniform `H³` bound. -/
noncomputable def sobState {M : ℝ} {θ : ℝ → TorusL2}
    (hb : ∀ t : ℝ, ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M)
    (t : ℝ) : Wiener1 :=
  sobToWiener1 (summable_of_finset_sum_le
    (fun k => sob_nonneg (fun j => l2coeff j (θ t)) k) (hb t))

@[simp] theorem sobState_coeff {M : ℝ} {θ : ℝ → TorusL2}
    (hb : ∀ t : ℝ, ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M)
    (t : ℝ) (k : Gam) : (sobState hb t).coeff k = l2coeff k (θ t) := rfl

/-- **The `A¹` state is the given `L²` state.**  Equality in `L²(𝕋²)`, from completeness of the
trigonometric system: no representative is altered. -/
theorem synthL2_sobState {M : ℝ} {θ : ℝ → TorusL2}
    (hb : ∀ t : ℝ, ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M)
    (t : ℝ) : synthL2 (incl (sobState hb t)) = θ t :=
  synthL2_incl_eq_of_coeff (w := sobState hb t) (fun _ => rfl)

/-- **The pairing used in the weak equation is the physical one**: `spacePair` against the `A¹`
state is literally the integral over the torus of the `L²` state against the test function. -/
theorem spacePair_sobState {M : ℝ} {θ : ℝ → TorusL2}
    (hb : ∀ t : ℝ, ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M)
    (t : ℝ) (P : C(Torus2, ℂ)) :
    spacePair (incl (sobState hb t)) P = ∫ x : Torus2, (θ t : Torus2 → ℂ) x * P x := by
  rw [spacePair]
  refine integral_congr_ae ?_
  have hae := synthL2_apply_ae (incl (sobState hb t))
  rw [synthL2_sobState hb t] at hae
  filter_upwards [hae] with x hx
  rw [hx]

/-! ## 2. The Sobolev solution class -/

/-- **A physical Sobolev solution** of `∂_t θ + ℛ_m(θ)·∇θ + (-Δ)^α θ = f`, `θ(0)=0`.

The state is an `L²(𝕋²)`-valued function of time.  Everything `A¹` is derived, never assumed.
The hypotheses are stated for every real time; a solution given on `[0,T]` is extended by
composing with the clamp `clampT`, which preserves each field. -/
structure IsSobolevSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m) (M : ℝ)
    (f : Curve0 T) (θ : ℝ → TorusL2) : Prop where
  /-- Each Fourier coordinate is continuous in time. -/
  coeff_continuous : ∀ k : Gam, Continuous fun t : ℝ => l2coeff k (θ t)
  /-- The state is real. -/
  real : ∀ t : ℝ, ConjSymmetric fun k : Gam => l2coeff k (θ t)
  /-- A uniform `H³` bound, on finite partial sums. -/
  bound : ∀ t : ℝ, ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M
  /-- Zero initial trace, in `L²(𝕋²)`. -/
  initial : θ 0 = 0
  /-- The time-integrated weak equation against trigonometric test polynomials. -/
  weak : ∀ (F : Finset Gam) (c : Gam → ℂ), ∀ t ∈ Set.Icc (0:ℝ) T,
    spacePair (incl (sobState bound t)) (trigPoly F c)
      + (∫ s in (0:ℝ)..t, spacePair (incl (sobState bound s)) (fracLapPoly α F c))
      + (∫ s in (0:ℝ)..t,
          spacePair (transport m hm (sobState bound s) (sobState bound s)) (trigPoly F c))
      = ∫ s in (0:ℝ)..t, spacePair (sourceFun hT f s) (trigPoly F c)

/-! ## 3. The representative -/

namespace IsSobolevSolution

variable {hα : 1 / 2 < α} {hT : 0 ≤ T} {hm : IsBddSymbol m} {M : ℝ} {f : Curve0 T}
  {θ : ℝ → TorusL2}

theorem summable (h : IsSobolevSolution hα hT hm M f θ) (t : ℝ) :
    Summable fun k : Gam => rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2 :=
  summable_of_finset_sum_le (fun k => sob_nonneg (fun j => l2coeff j (θ t)) k) (h.bound t)

theorem tsum_le (h : IsSobolevSolution hα hT hm M f θ) (t : ℝ) :
    (∑' k : Gam, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M :=
  tsum_le_of_finset_sum_le (fun k => sob_nonneg (fun j => l2coeff j (θ t)) k) (h.bound t)

/-- **The constructed `A¹` representative**: an actual `Curve1 T`. -/
noncomputable def curve (h : IsSobolevSolution hα hT hm M f θ) : Curve1 T :=
  sobCurve (T := T) h.coeff_continuous h.real h.summable h.tsum_le

theorem curve_def (h : IsSobolevSolution hα hT hm M f θ) :
    h.curve = sobCurve (T := T) h.coeff_continuous h.real h.summable h.tsum_le := rfl

theorem curve_coeff (h : IsSobolevSolution hα hT hm M f θ) (t : TimeI T) (k : Gam) :
    (h.curve t).val.coeff k = l2coeff k (θ (t : ℝ)) := rfl

/-- On `[0,T]` the clamped state of the representative is the `A¹` state of the solution. -/
theorem curveState_eq (h : IsSobolevSolution hα hT hm M f θ) {s : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) T) : curveState hT h.curve s = sobState h.bound s := by
  refine Wiener1.coeff_injective (funext fun k => ?_)
  rw [h.curve_def, curveState_sobCurve_mem hT h.coeff_continuous h.real h.summable h.tsum_le hs k]
  rfl

/-- **Physical agreement of the representative with the Sobolev solution**, in `L²(𝕋²)`. -/
theorem synthL2_curveState (h : IsSobolevSolution hα hT hm M f θ) {s : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) T) :
    synthL2 (incl (curveState hT h.curve s)) = θ s := by
  rw [h.curveState_eq hs, synthL2_sobState h.bound s]

/-- The initial trace of the representative is zero — the trace of the **continuous**
representative at `t = 0`, not an almost-everywhere statement. -/
theorem curveState_initial (h : IsSobolevSolution hα hT hm M f θ) :
    curveState hT h.curve 0 = 0 := by
  refine Wiener1.coeff_injective (funext fun k => ?_)
  rw [h.curve_def,
    curveState_sobCurve_mem hT h.coeff_continuous h.real h.summable h.tsum_le ⟨le_rfl, hT⟩ k]
  show l2coeff k (θ 0) = (0 : Wiener1).coeff k
  rw [h.initial]
  show (inner ℂ (synthL2 (wdirac k)) (0 : TorusL2) : ℂ) = _
  rw [inner_zero_right]
  rfl

/-- **The representative satisfies the v7 physical solution predicate.**  Every term of the weak
equation survives the change of representative: the state pairing, the fractional term and the
transport term are literally the same expressions, because `curveState hT h.curve s` and
`sobState h.bound s` are the same `A¹` element at every time of `[0,T]`. -/
theorem isPhysicalSolution_curve (h : IsSobolevSolution hα hT hm M f θ) :
    IsPhysicalSolution hα hT hm f h.curve := by
  refine ⟨h.curveState_initial, ?_⟩
  intro P F c hP t ht
  subst hP
  have hw := h.weak F c t ht
  have hstate : curveState hT h.curve t = sobState h.bound t := h.curveState_eq ht
  have hsub : ∀ s ∈ Set.uIcc (0:ℝ) t, curveState hT h.curve s = sobState h.bound s := by
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    exact h.curveState_eq ⟨hs.1, le_trans hs.2 ht.2⟩
  have h2 : (∫ s in (0:ℝ)..t,
        spacePair (incl (curveState hT h.curve s)) (fracLapPoly α F c))
      = ∫ s in (0:ℝ)..t, spacePair (incl (sobState h.bound s)) (fracLapPoly α F c) :=
    intervalIntegral.integral_congr (fun s hs => by rw [hsub s hs])
  have h3 : (∫ s in (0:ℝ)..t,
        spacePair (quadCurve hm (curveState hT h.curve) s) (trigPoly F c))
      = ∫ s in (0:ℝ)..t,
          spacePair (transport m hm (sobState h.bound s) (sobState h.bound s))
            (trigPoly F c) :=
    intervalIntegral.integral_congr (fun s hs => by
      show spacePair (transport m hm (curveState hT h.curve s) (curveState hT h.curve s))
          (trigPoly F c) = _
      rw [hsub s hs])
  rw [hstate, h2, h3]
  exact hw

/-! ## 4. Reusing the checked v7 chain -/

/-- **The representative satisfies the mild equation.**  This is `mild_of_isPhysicalSolution`
applied to the constructed representative; nothing is reproved. -/
theorem mild_curve (h : IsSobolevSolution hα hT hm M f θ) (hr : IsRealSymbol m) :
    h.curve + sourceQuad hα hT m hm hr h.curve h.curve = duhamelOp hα hT f :=
  mild_of_isPhysicalSolution hα hT hm hr h.isPhysicalSolution_curve

/-- **The comparison theorem in the Sobolev class.**  The representative of *any* Sobolev
solution equals the constructed mild state, with no smallness hypothesis. -/
theorem curve_eq_of_mild (h : IsSobolevSolution hα hT hm M f θ) (hr : IsRealSymbol m)
    {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) : h.curve = u :=
  eq_of_isPhysicalSolution hα hT hm hr hC hmild h.isPhysicalSolution_curve

/-- **The mean balance survives the bridge**, for arbitrary (in particular nonzero-mean)
sources: the zero Fourier mode of the Sobolev solution is the exact time primitive of the zero
mode of the source. -/
theorem mean_balance {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hr : IsRealSymbol (rotatedGradientSymbol κ)) {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsSobolevSolution hα hT (rotatedGradientSymbol_bdd hb) M f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    l2coeff 0 (θ t) = ∫ s in (0:ℝ)..t, (sourceFun hT f s) 0 := by
  have hmild := h.mild_curve hr
  have hbal := coeff_zero_balance_of_mild hα hT hb hr hmild ht
  rw [← hbal, h.curveState_eq ht]
  rfl

end IsSobolevSolution

/-- **Uniqueness in the Sobolev class.**  Two Sobolev solutions of the same source agree in
`L²(𝕋²)` at every time of `[0,T]`.  No smallness is assumed anywhere. -/
theorem sobolev_solution_unique {hα : 1 / 2 < α} {hT : 0 ≤ T} {hm : IsBddSymbol m}
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {M₁ M₂ : ℝ} {f : Curve0 T}
    {θ₁ θ₂ : ℝ → TorusL2}
    (h₁ : IsSobolevSolution hα hT hm M₁ f θ₁) (h₂ : IsSobolevSolution hα hT hm M₂ f θ₂)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) : θ₁ s = θ₂ s := by
  have hcurve : h₁.curve = h₂.curve :=
    physical_solution_unique hα hT hm hr hC h₁.isPhysicalSolution_curve
      h₂.isPhysicalSolution_curve
  rw [← h₁.synthL2_curveState hs, ← h₂.synthL2_curveState hs, hcurve]

end LiWang.WienerModel
