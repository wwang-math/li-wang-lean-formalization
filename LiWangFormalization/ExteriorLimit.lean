/-
# The nonlocal state-approximation step, precisely isolated

The v4.0 statement `tested_symmetrized_limit` varied the **test function** `ψ` while the two
states stayed fixed; as the review observed, its conclusion follows from
`tested_symmetrized_eq_zero` alone and it is **not** the Runge step.  The Runge step varies the
two *generated solution states*.  This module supplies the correct statement and the exact
analytic input it needs.

* `restL2`, `extL2sq` — the physical `L²` carrier of a measurable region and the exterior
  energy `∫_E |·|²`, with Cauchy–Schwarz on that region proved through the `L²` inner product
  of the restricted measure;
* `norm_sideInteraction_exterior_le` — the tested interaction with an **exterior test** is
  bounded by the exterior energies of *the scalar state* and of *the velocity of the full
  state*.  This is the precise pair of quantities that a limit argument must control;
* `ExteriorStateConvergence` — those hypotheses, named;
* `tendsto_sideInteraction_exterior` and `tested_symmetrized_state_limit` — the **sufficient
  convergence theorem**, proved: under exterior convergence of the scalar states and of the
  velocities of the full states (plus the uniform exterior bounds), the vanishing of the
  symmetrized interaction passes to the limit **with the states varying and `ψ` fixed**;
* `ae_eq_zero_of_tendsto_physicalL2` — the obstruction, proved: a *global* physical `L²` limit
  of states that vanish on a region still vanishes there.  So global convergence of generated
  states cannot be assumed in order to reach an arbitrary prescribed target;
* `disjoint_measured_exterior` — the measured region and the exterior are disjoint, which is
  why the observed-velocity identity (an identity on `W`) supplies no control on `E`;
* `GeneratedExteriorApproximation` — the exact remaining analytic input, stated and **not**
  proved and **not** assumed: every theorem below that uses it carries it as an explicit
  hypothesis and is labelled conditional.

Part of `LiWangFormalizationSmoothObservationPacket` v5.0.
-/
import LiWangFormalization.TwoStateContinuity
import LiWangFormalization.SmoothUCPBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## 1. The physical `L²` carrier of a region, and Cauchy–Schwarz there -/

theorem memLp_restrict_continuous (f : C(Torus2, ℂ)) (E : Set Torus2) :
    MemLp (fun x => f x) 2 ((volume : Measure Torus2).restrict E) :=
  MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)

/-- A continuous function of the torus, as an element of `L²` of the region `E`. -/
noncomputable def restL2 (E : Set Torus2) (f : C(Torus2, ℂ)) :
    Lp ℂ 2 ((volume : Measure Torus2).restrict E) :=
  MemLp.toLp (fun x => f x) (memLp_restrict_continuous f E)

theorem coeFn_restL2 (E : Set Torus2) (f : C(Torus2, ℂ)) :
    ((restL2 E f : Lp ℂ 2 ((volume : Measure Torus2).restrict E)) : Torus2 → ℂ)
      =ᵐ[(volume : Measure Torus2).restrict E] fun x => f x :=
  MemLp.coeFn_toLp _

/-- The conjugate of a continuous function of the torus. -/
noncomputable def cconj (f : C(Torus2, ℂ)) : C(Torus2, ℂ) :=
  ⟨fun x => conj (f x), Complex.continuous_conj.comp f.continuous⟩

@[simp] theorem cconj_apply (f : C(Torus2, ℂ)) (x : Torus2) : cconj f x = conj (f x) := rfl

theorem inner_restL2 (E : Set Torus2) (f g : C(Torus2, ℂ)) :
    (inner ℂ (restL2 E f) (restL2 E g) : ℂ) = ∫ x in E, conj (f x) * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restL2 E f, coeFn_restL2 E g] with x hx hy
  rw [hx, hy, RCLike.inner_apply (𝕜 := ℂ)]
  ring

theorem norm_restL2_sq (E : Set Torus2) (f : C(Torus2, ℂ)) :
    ‖restL2 E f‖ ^ 2 = ∫ x in E, ‖f x‖ ^ 2 := by
  have h := inner_restL2 E f f
  have hterm : ∀ x : Torus2, conj (f x) * f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [Complex.conj_mul']; norm_cast
  rw [integral_congr_ae (Filter.Eventually.of_forall hterm)] at h
  rw [integral_complex_ofReal] at h
  have hself : (inner ℂ (restL2 E f) (restL2 E f) : ℂ) = ((‖restL2 E f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hself] at h
  exact_mod_cast h

theorem norm_restL2_cconj (E : Set Torus2) (f : C(Torus2, ℂ)) :
    ‖restL2 E (cconj f)‖ = ‖restL2 E f‖ := by
  have h1 := norm_restL2_sq E (cconj f)
  have h2 := norm_restL2_sq E f
  have he : (∫ x in E, ‖(cconj f) x‖ ^ 2) = ∫ x in E, ‖f x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [cconj_apply, RCLike.norm_conj]
  have : ‖restL2 E (cconj f)‖ ^ 2 = ‖restL2 E f‖ ^ 2 := by rw [h1, he, h2]
  nlinarith [norm_nonneg (restL2 E (cconj f)), norm_nonneg (restL2 E f), this]

/-- **Cauchy–Schwarz on the region `E`** for continuous factors. -/
theorem norm_setIntegral_mul_le (E : Set Torus2) (f g : C(Torus2, ℂ)) :
    ‖∫ x in E, f x * g x‖
      ≤ Real.sqrt (∫ x in E, ‖f x‖ ^ 2) * Real.sqrt (∫ x in E, ‖g x‖ ^ 2) := by
  have hid : (∫ x in E, f x * g x) = inner ℂ (restL2 E (cconj f)) (restL2 E g) := by
    rw [inner_restL2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [cconj_apply, Complex.conj_conj]
  have hf : Real.sqrt (∫ x in E, ‖f x‖ ^ 2) = ‖restL2 E (cconj f)‖ := by
    rw [norm_restL2_cconj, ← norm_restL2_sq, Real.sqrt_sq (norm_nonneg _)]
  have hg : Real.sqrt (∫ x in E, ‖g x‖ ^ 2) = ‖restL2 E g‖ := by
    rw [← norm_restL2_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hid, hf, hg]
  exact norm_inner_le_norm _ _

/-! ## 2. The exterior energy of a state -/

/-- The **exterior energy** `∫_E |synth a|²` of a Wiener state. -/
noncomputable def extL2sq (E : Set Torus2) (a : Wiener) : ℝ := ∫ x in E, ‖synth a x‖ ^ 2

theorem extL2sq_nonneg (E : Set Torus2) (a : Wiener) : 0 ≤ extL2sq E a :=
  setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => sq_nonneg _)

theorem extL2sq_le_global (E : Set Torus2) (a : Wiener) : extL2sq E a ≤ ‖synthL2 a‖ ^ 2 := by
  rw [norm_synthL2_sq, ← integral_norm_sq_synth]
  refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun x => sq_nonneg _)
  exact ((synth a).continuous.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem sqrt_extL2sq_le_norm (E : Set Torus2) (a : Wiener) :
    Real.sqrt (extL2sq E a) ≤ ‖synthL2 a‖ := by
  rw [show ‖synthL2 a‖ = Real.sqrt (‖synthL2 a‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt (extL2sq_le_global E a)

/-- **The exterior triple bound**: the exterior integral of a triple product is controlled by
the sup norm of the test factor and the exterior energies of the two state factors. -/
theorem norm_setIntegral_triple_le {E : Set Torus2} (hE : MeasurableSet E) (A B C : Wiener) :
    ‖∫ x in E, synth A x * synth B x * synth C x‖
      ≤ ‖synth C‖ * (Real.sqrt (extL2sq E A) * Real.sqrt (extL2sq E B)) := by
  have hgroup : (∫ x in E, synth A x * synth B x * synth C x)
      = ∫ x in E, synth A x * ((synth B * synth C) x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show synth A x * synth B x * synth C x = synth A x * (synth B x * synth C x)
    ring
  have hcs := norm_setIntegral_mul_le E (synth A) (synth B * synth C)
  have hbnd : Real.sqrt (∫ x in E, ‖(synth B * synth C) x‖ ^ 2)
      ≤ ‖synth C‖ * Real.sqrt (extL2sq E B) := by
    have hmono : (∫ x in E, ‖(synth B * synth C) x‖ ^ 2)
        ≤ ‖synth C‖ ^ 2 * extL2sq E B := by
      rw [extL2sq, ← integral_const_mul]
      refine setIntegral_mono_on ?_ ?_ hE (fun x _ => ?_)
      · exact (((synth B).continuous.mul (synth C).continuous).norm.pow
          2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _) |>.integrableOn
      · exact (((synth B).continuous.norm.pow 2).const_mul
          (‖synth C‖ ^ 2)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _) |>.integrableOn
      · show ‖synth B x * synth C x‖ ^ 2 ≤ ‖synth C‖ ^ 2 * ‖synth B x‖ ^ 2
        rw [norm_mul, mul_pow, mul_comm (‖synth C‖ ^ 2)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) ((synth C).norm_coe_le_norm x) 2) (sq_nonneg _)
    calc Real.sqrt (∫ x in E, ‖(synth B * synth C) x‖ ^ 2)
        ≤ Real.sqrt (‖synth C‖ ^ 2 * extL2sq E B) := Real.sqrt_le_sqrt hmono
      _ = ‖synth C‖ * Real.sqrt (extL2sq E B) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hgroup]
  calc ‖∫ x in E, synth A x * ((synth B * synth C) x)‖
      ≤ Real.sqrt (∫ x in E, ‖synth A x‖ ^ 2)
          * Real.sqrt (∫ x in E, ‖(synth B * synth C) x‖ ^ 2) := hcs
    _ ≤ Real.sqrt (extL2sq E A) * (‖synth C‖ * Real.sqrt (extL2sq E B)) :=
        mul_le_mul_of_nonneg_left hbnd (Real.sqrt_nonneg _)
    _ = ‖synth C‖ * (Real.sqrt (extL2sq E A) * Real.sqrt (extL2sq E B)) := by ring

/-! ## 3. The tested interaction against an exterior test, in exterior energies -/

/-- **The estimate a limit argument must use.**  With an exterior test, the tested interaction
is controlled by the exterior energy of the *scalar state* `v` and the exterior energy of the
*velocity of the full state* `u`.  Both quantities are needed: `R_m` is nonlocal, so the second
is **not** controlled by the first. -/
theorem norm_sideInteraction_exterior_le {W : Set Torus2} {ψ : Wiener1} (hψ : IsExteriorTest W ψ)
    {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (u v : Wiener1) :
    ‖sideInteraction m hm ψ u v‖
      ≤ (2 * Real.pi * ‖ψ‖) * (Real.sqrt (extL2sq (closure W)ᶜ (incl v))
            * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm 0 (incl u))))
        + (2 * Real.pi * ‖ψ‖) * (Real.sqrt (extL2sq (closure W)ᶜ (incl v))
            * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm 1 (incl u)))) := by
  have hE : MeasurableSet ((closure W)ᶜ) := (isClosed_closure (s := W)).measurableSet.compl
  have hterm : ∀ j : Fin 2,
      ‖∫ x in (closure W)ᶜ, synth (incl v) x * synth (velocity m hm j (incl u)) x
          * synth (fourierDeriv j ψ) x‖
        ≤ (2 * Real.pi * ‖ψ‖) * (Real.sqrt (extL2sq (closure W)ᶜ (incl v))
            * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl u)))) := by
    intro j
    refine le_trans (norm_setIntegral_triple_le hE _ _ _) ?_
    exact mul_le_mul_of_nonneg_right (norm_synth_fourierDeriv_le j ψ)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [sideInteraction_eq_exterior hψ m hm u v, Fin.sum_univ_two]
  exact le_trans (norm_add_le _ _) (add_le_add (hterm 0) (hterm 1))

/-! ## 4. The sufficient exterior convergence hypotheses -/

/-- **The explicit sufficient convergence hypotheses.**  A bilinear exterior limit needs the
exterior convergence of the *scalar states*, the exterior convergence of *the velocities of the
full states*, and a uniform exterior bound.  These are exactly the three quantities the
estimate above involves. -/
structure ExteriorStateConvergence (W : Set Torus2) (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (u : ℕ → Wiener1) (U : Wiener1) : Prop where
  state : Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (incl (u n - U)))) atTop (nhds 0)
  velocityConv : ∀ j : Fin 2,
    Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U)))))
      atTop (nhds 0)
  stateBound : ∃ M : ℝ, ∀ n : ℕ, Real.sqrt (extL2sq (closure W)ᶜ (incl (u n))) ≤ M

theorem tendsto_of_norm_sub_le {f : ℕ → ℂ} {L : ℂ} {g : ℕ → ℝ} (hb : ∀ n, ‖f n - L‖ ≤ g n)
    (hg : Tendsto g atTop (nhds 0)) : Tendsto f atTop (nhds L) :=
  tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm hb hg)

/-- **The sufficient convergence theorem, proved.**  With `ψ` fixed and the two *states*
varying, the tested interaction converges under the exterior hypotheses above. -/
theorem tendsto_sideInteraction_exterior {W : Set Torus2} {ψ : Wiener1}
    (hψ : IsExteriorTest W ψ) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {u v : ℕ → Wiener1} {U V : Wiener1}
    (hu : ExteriorStateConvergence W m hm u U) (hv : ExteriorStateConvergence W m hm v V) :
    Tendsto (fun n => sideInteraction m hm ψ (u n) (v n)) atTop
      (nhds (sideInteraction m hm ψ U V)) := by
  obtain ⟨M, hM⟩ := hv.stateBound
  have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg _) (hM 0)
  set K : ℝ := 2 * Real.pi * ‖ψ‖ with hK
  have hK0 : 0 ≤ K := by positivity
  set P : Fin 2 → ℕ → ℝ := fun j n =>
    K * (Real.sqrt (extL2sq (closure W)ᶜ (incl (v n)))
      * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U))))) with hP
  set Q : Fin 2 → ℕ → ℝ := fun j n =>
    K * (Real.sqrt (extL2sq (closure W)ᶜ (incl (v n - V)))
      * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl U)))) with hQ
  have hbound : ∀ n : ℕ,
      ‖sideInteraction m hm ψ (u n) (v n) - sideInteraction m hm ψ U V‖
        ≤ (P 0 n + P 1 n) + (Q 0 n + Q 1 n) := by
    intro n
    rw [sideInteraction_decomp m hm hC]
    exact le_trans (norm_add_le _ _)
      (add_le_add (norm_sideInteraction_exterior_le hψ hm (u n - U) (v n))
        (norm_sideInteraction_exterior_le hψ hm U (v n - V)))
  refine tendsto_of_norm_sub_le hbound ?_
  have hPlim : ∀ j : Fin 2, Tendsto (P j) atTop (nhds 0) := by
    intro j
    have hlim : Tendsto (fun n : ℕ => K * M *
        Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U))))) atTop (nhds 0) := by
      have h := (hu.velocityConv j).const_mul (K * M)
      rwa [mul_zero] at h
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
    · exact mul_nonneg hK0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · rw [hP]
      have h1 : Real.sqrt (extL2sq (closure W)ᶜ (incl (v n))) ≤ M := hM n
      have h2 : (0:ℝ) ≤ Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U)))) :=
        Real.sqrt_nonneg _
      calc K * (Real.sqrt (extL2sq (closure W)ᶜ (incl (v n)))
              * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U)))))
          ≤ K * (M * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U))))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) hK0
        _ = K * M * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U)))) := by
            ring
  have hQlim : ∀ j : Fin 2, Tendsto (Q j) atTop (nhds 0) := by
    intro j
    have hc := hv.state.const_mul (K * Real.sqrt (extL2sq (closure W)ᶜ
      (velocity m hm j (incl U))))
    rw [mul_zero] at hc
    have he : Q j = fun n : ℕ =>
        (K * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl U))))
          * Real.sqrt (extL2sq (closure W)ᶜ (incl (v n - V))) := by
      funext n
      show K * (Real.sqrt (extL2sq (closure W)ᶜ (incl (v n - V)))
        * Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl U)))) = _
      ring
    rw [he]
    exact hc
  have hsum := ((hPlim 0).add (hPlim 1)).add ((hQlim 0).add (hQlim 1))
  simp only [add_zero] at hsum
  exact hsum

/-- **The corrected Runge-shaped statement**: the *states* vary, the test `ψ` is fixed.  Under
the exterior convergence hypotheses, the vanishing of the symmetrized tested interaction passes
to the prescribed targets. -/
theorem tested_symmetrized_state_limit {W : Set Torus2} {ψ : Wiener1}
    (hψ : IsExteriorTest W ψ) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (hdiv : IsDivFreeSymbol m) {u v : ℕ → Wiener1} {U V : Wiener1}
    (hzero : ∀ n : ℕ, transport m hm (u n) (v n) + transport m hm (v n) (u n) = 0)
    (hu : ExteriorStateConvergence W m hm u U) (hv : ExteriorStateConvergence W m hm v V) :
    testedInteraction m hm ψ U V = 0 := by
  have h1 := tendsto_sideInteraction_exterior hψ hm hC hu hv
  have h2 := tendsto_sideInteraction_exterior hψ hm hC hv hu
  have hlim : Tendsto (fun n => testedInteraction m hm ψ (u n) (v n)) atTop
      (nhds (testedInteraction m hm ψ U V)) := h1.add h2
  have hz : (fun n : ℕ => testedInteraction m hm ψ (u n) (v n)) = fun _ : ℕ => (0 : ℂ) :=
    funext fun n => testedInteraction_eq_zero_of_generated hm hdiv (hzero n) ψ
  rw [hz] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-! ## 5. The obstruction, proved -/

/-- **Global physical `L²` limits preserve vanishing on a region.**  If every `a n` vanishes on
`S` and `a n → A` in the *global* physical `L²` norm, then the exterior energy of `A` on `S` is
zero.  Consequently one may not assume global convergence of generated states towards an
arbitrary prescribed target: the target would inherit the vanishing. -/
theorem extL2sq_eq_zero_of_tendsto_physicalL2 {S : Set Torus2} (hS : MeasurableSet S)
    {a : ℕ → Wiener} {A : Wiener} (hvan : ∀ n : ℕ, ∀ x ∈ S, synth (a n) x = 0)
    (hconv : Tendsto (fun n => ‖synthL2 (a n - A)‖) atTop (nhds 0)) :
    extL2sq S A = 0 := by
  have hle : ∀ n : ℕ, extL2sq S A ≤ ‖synthL2 (a n - A)‖ ^ 2 := by
    intro n
    have heq : extL2sq S A = extL2sq S (a n - A) := by
      refine setIntegral_congr_fun hS (fun x hx => ?_)
      show ‖synth A x‖ ^ 2 = ‖synth (a n - A) x‖ ^ 2
      rw [map_sub]
      show ‖synth A x‖ ^ 2 = ‖synth (a n) x - synth A x‖ ^ 2
      rw [hvan n x hx, zero_sub, norm_neg]
    rw [heq]
    exact extL2sq_le_global S (a n - A)
  have hlim : Tendsto (fun n : ℕ => ‖synthL2 (a n - A)‖ ^ 2) atTop (nhds 0) := by
    have := hconv.pow 2
    simpa using this
  exact le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hle))
    (extL2sq_nonneg S A)

/-- The same conclusion as almost-everywhere vanishing of the physical field on `S`. -/
theorem ae_eq_zero_of_tendsto_physicalL2 {S : Set Torus2} (hS : MeasurableSet S)
    {a : ℕ → Wiener} {A : Wiener} (hvan : ∀ n : ℕ, ∀ x ∈ S, synth (a n) x = 0)
    (hconv : Tendsto (fun n => ‖synthL2 (a n - A)‖) atTop (nhds 0)) :
    ∀ᵐ x ∂((volume : Measure Torus2).restrict S), synth A x = 0 := by
  have h0 := extL2sq_eq_zero_of_tendsto_physicalL2 hS hvan hconv
  have hint : IntegrableOn (fun x : Torus2 => ‖synth A x‖ ^ 2) S (volume : Measure Torus2) :=
    (((synth A).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg (‖synth A x‖)) hint).1 h0
  filter_upwards [hae] with x hx
  have : ‖synth A x‖ ^ 2 = 0 := hx
  have hnorm : ‖synth A x‖ = 0 := by nlinarith [norm_nonneg (synth A x)]
  exact norm_eq_zero.1 hnorm

/-- **The measured region and the exterior are disjoint.**  The observed-velocity identity is an
identity on `W`; the missing input concerns `E = (closure W)ᶜ`.  These sets are disjoint, so the
former supplies no information about the latter. -/
theorem disjoint_measured_exterior (W : Set Torus2) : Disjoint W ((closure W)ᶜ) :=
  Set.disjoint_compl_right_iff_subset.2 subset_closure

/-! ## 6. The exact remaining analytic input, and the conditional conclusion -/

/-- **The exact remaining analytic input.**  For the *actual generated sequence*: a sequence of
admissible sources whose generated states at the given time approximate the prescribed target
in the exterior, together with the exterior convergence of the velocities of the **full**
states.  This is **not proved** here and is **not assumed** anywhere: it appears only as an
explicit hypothesis of the conditional theorem below. -/
def GeneratedExteriorApproximation (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (A : Submodule ℝ (Curve0 T)) (t : ℝ)
    (U : Wiener1) : Prop :=
  ∃ g : ℕ → Curve0 T, (∀ n : ℕ, g n ∈ A) ∧
    ExteriorStateConvergence W m hm (fun n => curveState hT (duhamelOp hα hT (g n)) t) U

/-- **Conditional (on the external UCP hypothesis and on the remaining approximation input).**
For prescribed targets reached by generated states in the exterior sense above, the tested
symmetrized interaction vanishes.  Every hypothesis is explicit: nothing about the generated
sequence is assumed beyond what `GeneratedExteriorApproximation` names, and the measured-map
agreement is required only on the smooth compactly supported class. -/
theorem tested_interaction_target_eq_zero (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {C : ℝ} (hC : ∀ j k, ‖(m₁ - m₂) j k‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (t : ℝ) {U V : Wiener1}
    (hU : GeneratedExteriorApproximation hα hT.le W (m₁ - m₂) (hm₁.sub hm₂)
      (smoothSources hT W) t U)
    (hV : GeneratedExteriorApproximation hα hT.le W (m₁ - m₂) (hm₁.sub hm₂)
      (smoothSources hT W) t V) :
    testedInteraction (m₁ - m₂) (hm₁.sub hm₂) ψ U V = 0 := by
  obtain ⟨g₁, hg₁, hc₁⟩ := hU
  obtain ⟨g₂, hg₂, hc₂⟩ := hV
  refine tested_symmetrized_state_limit hψ (hm₁.sub hm₂) hC hdiv (fun n => ?_) hc₁ hc₂
  have hgen := generated_source_identity_smooth hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hε hmild hobs
    (hg₁ n) (hg₂ n)
  have hval := congrArg (fun V : Curve0 T => (V (clampT hT.le t)).val) hgen
  simpa using hval


/-! ## 7. Identification with the v4 generated-state output on the smooth source class -/

/-- **Conditional.**  For `u = J h₁` and `v = J h₂` with `h₁, h₂` *smooth compactly supported*
sources, the tested interaction of the two actual generated states vanishes at every time. -/
theorem testedInteraction_generated_smooth_eq_zero (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (ψ : Wiener1) (t : ℝ) {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ smoothSources hT W)
    (hh₂ : h₂ ∈ smoothSources hT W) :
    testedInteraction (m₁ - m₂) (hm₁.sub hm₂) ψ
        (curveState hT.le (duhamelOp hα hT.le h₁) t)
        (curveState hT.le (duhamelOp hα hT.le h₂) t) = 0 := by
  have hgen := generated_source_identity_smooth hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hε hmild hobs
    hh₁ hh₂
  have hval := congrArg (fun V : Curve0 T => (V (clampT hT.le t)).val) hgen
  refine testedInteraction_eq_zero_of_generated (hm₁.sub hm₂) hdiv ?_ ψ
  simpa using hval

/-- **Conditional.**  The corresponding statement for the actual iterated space-time integral,
with an arbitrary continuous time profile. -/
theorem spacetimeTestedInteraction_generated_smooth_eq_zero (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (ψ : Wiener1) (φ : ℝ → ℂ) {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ smoothSources hT W)
    (hh₂ : h₂ ∈ smoothSources hT W) :
    spacetimeTestedInteraction hT.le (m₁ - m₂) (hm₁.sub hm₂) ψ φ
      (duhamelOp hα hT.le h₁) (duhamelOp hα hT.le h₂) = 0 :=
  spacetimeTestedInteraction_eq_zero hα hT.le hm₁ hr₁ hm₂ hr₂ hdiv
    (generated_source_identity_smooth hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hε hmild hobs hh₁ hh₂) ψ φ


end LiWang.Formalization
