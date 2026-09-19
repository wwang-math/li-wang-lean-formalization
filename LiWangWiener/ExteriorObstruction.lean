/-
# The exterior interface: what convergence gives, and a **proved** nonlocality obstruction

This module completes the analysis of the state-approximation step begun in `ExteriorLimit`.

* `sqrt_extL2sq_eq_norm_restL2` identifies `√(extL2sq E a)` with the honest `L²(E)` norm of the
  physical field, so the exterior quantities obey the triangle inequality;
* `ExteriorStateConvergence.of_state_velocity` removes the uniform-bound field: it follows from
  the convergence of the scalar states;
* `exteriorStateConvergence_of_global` shows that **global** physical `L²` convergence of the
  states supplies every hypothesis — the precise sense in which a stronger topology would
  close the step (and `ae_eq_zero_of_tendsto_physicalL2` of `ExteriorLimit` shows why it cannot
  simply be assumed for an arbitrary prescribed target);
* `exists_exterior_nonlocality` and `exists_state_conv_without_velocity_conv` show that the
  two fields of `ExteriorStateConvergence` are **logically independent**: there is a state whose
  physical field vanishes identically on the exterior `E` while its velocity vanishes *nowhere*.
  **Scope of that example.**  It is built from an *arbitrary bounded* Fourier symbol
  (`modeSymbol`), which is neither real nor divergence-free and is **not** a rotated-gradient
  paper symbol; and the state is an arbitrary localized profile, **not** a generated state
  satisfying measured-map agreement.  It is therefore a statement about the hypothesis class of
  `ExteriorStateConvergence` only — it is **not** a counterexample to the Li–Wang paper, and it
  does not preclude PDE-mediated transfer of information from the measured region to the
  exterior.  Disjointness of regions alone (`disjoint_measured_exterior`) never could;
* `sideInteraction_congr_exterior` is the positive half: for a fixed first state, the tested
  interaction depends on the **second** state only through its restriction to `E`, and
  `setIntegral_source_region_eq_zero` is the explicit accounting of the source-region part.

Part of `LiWangWienerSmoothObservationPacket` v5.0.
-/
import LiWangWiener.ExteriorLimit
import LiWangWiener.SmoothFirstOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. The exterior energy is a norm -/

theorem sqrt_extL2sq_eq_norm_restL2 (E : Set Torus2) (a : Wiener) :
    Real.sqrt (extL2sq E a) = ‖restL2 E (synth a)‖ := by
  rw [extL2sq, ← norm_restL2_sq, Real.sqrt_sq (norm_nonneg _)]

theorem restL2_synth_add (E : Set Torus2) (a b : Wiener) :
    restL2 E (synth (a + b)) = restL2 E (synth a) + restL2 E (synth b) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restL2 E (synth (a + b)), Lp.coeFn_add (restL2 E (synth a))
    (restL2 E (synth b)), coeFn_restL2 E (synth a), coeFn_restL2 E (synth b)]
    with x hx hsum ha hb
  rw [hx, hsum, Pi.add_apply, ha, hb, map_add]
  rfl

theorem sqrt_extL2sq_add_le (E : Set Torus2) (a b : Wiener) :
    Real.sqrt (extL2sq E (a + b)) ≤ Real.sqrt (extL2sq E a) + Real.sqrt (extL2sq E b) := by
  rw [sqrt_extL2sq_eq_norm_restL2, sqrt_extL2sq_eq_norm_restL2, sqrt_extL2sq_eq_norm_restL2,
    restL2_synth_add]
  exact norm_add_le _ _

theorem extL2sq_eq_zero_of_vanishes {E : Set Torus2} (hE : MeasurableSet E) {a : Wiener}
    (h : ∀ x ∈ E, synth a x = 0) : extL2sq E a = 0 := by
  rw [extL2sq]
  refine setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
  rw [h x hx, norm_zero]
  norm_num

/-! ## 2. Two constructors for the exterior convergence hypotheses -/

/-- The uniform exterior bound is not an extra assumption: it follows from the convergence of
the scalar states. -/
theorem ExteriorStateConvergence.of_state_velocity (W : Set Torus2) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {u : ℕ → Wiener1} {U : Wiener1}
    (hstate : Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (incl (u n - U)))) atTop (nhds 0))
    (hvel : ∀ j : Fin 2,
      Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (velocity m hm j (incl (u n - U)))))
        atTop (nhds 0)) :
    ExteriorStateConvergence W m hm u U := by
  refine ⟨hstate, hvel, ?_⟩
  obtain ⟨M₀, hM₀⟩ := hstate.bddAbove_range
  refine ⟨M₀ + Real.sqrt (extL2sq (closure W)ᶜ (incl U)), fun n => ?_⟩
  have hsplit : incl (u n) = incl (u n - U) + incl U := by
    rw [← map_add]
    congr 1
    abel
  have hle := sqrt_extL2sq_add_le ((closure W)ᶜ) (incl (u n - U)) (incl U)
  rw [← hsplit] at hle
  have hb : Real.sqrt (extL2sq (closure W)ᶜ (incl (u n - U))) ≤ M₀ := hM₀ ⟨n, rfl⟩
  linarith

/-- **Global** physical `L²` convergence of the states supplies every exterior hypothesis. -/
theorem exteriorStateConvergence_of_global (W : Set Torus2) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) {u : ℕ → Wiener1} {U : Wiener1}
    (hconv : Tendsto (fun n => ‖synthL2 (incl (u n - U))‖) atTop (nhds 0)) :
    ExteriorStateConvergence W m hm u U := by
  obtain ⟨C, hC⟩ := id hm
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (m 0 0)) (hC 0 0)
  refine ExteriorStateConvergence.of_state_velocity W hm ?_ (fun j => ?_)
  · refine squeeze_zero (fun n => Real.sqrt_nonneg _) (fun n => ?_) hconv
    exact sqrt_extL2sq_le_norm _ _
  · have hlim : Tendsto (fun n : ℕ => C * ‖synthL2 (incl (u n - U))‖) atTop (nhds 0) := by
      have h := hconv.const_mul C
      rwa [mul_zero] at h
    refine squeeze_zero (fun n => Real.sqrt_nonneg _) (fun n => ?_) hlim
    exact le_trans (sqrt_extL2sq_le_norm _ _) (norm_synthL2_velocity_le hm hC j _)

/-! ## 3. The nonlocality obstruction, proved -/

/-- A single-mode bounded symbol. -/
noncomputable def modeSymbol (k₀ : Gam) : Fin 2 → Gam → ℂ :=
  fun _ k => if k = k₀ then 1 else 0

theorem isBddSymbol_modeSymbol (k₀ : Gam) : IsBddSymbol (modeSymbol k₀) := by
  refine ⟨1, fun j k => ?_⟩
  show ‖(if k = k₀ then (1:ℂ) else 0)‖ ≤ 1
  by_cases hk : k = k₀ <;> simp [hk]

theorem velocity_modeSymbol (k₀ : Gam) (j : Fin 2) (a : Wiener) :
    velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) j a = (a k₀) • wdirac k₀ := by
  refine lp.ext (funext fun k => ?_)
  show (if k = k₀ then (1:ℂ) else 0) * a k = ((a k₀) • wdirac k₀) k
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show (if k = k₀ then (1:ℂ) else 0) * a k = a k₀ * (if k = k₀ then (1:ℂ) else 0)
  by_cases hk : k = k₀ <;> simp [hk]

/-- **Independence of the two exterior hypotheses.**  For every nonempty open `W` there is a
*nonzero* first-order state whose physical field vanishes identically on the exterior
`E = (closure W)ᶜ`, and a **bounded** symbol for which the velocity of that state vanishes
nowhere.  So exterior information about a state does not, for an arbitrary bounded symbol,
give exterior information about `R_m` applied to it.

**Scope.**  `modeSymbol k₀` is an arbitrary bounded symbol: it is not real, not divergence
free, and not a rotated-gradient paper symbol; and the state here is an arbitrary localized
profile, not a generated state subject to measured-map agreement.  This is a statement about
the hypothesis class of `ExteriorStateConvergence`, **not** a counterexample to the paper. -/
theorem exists_exterior_nonlocality {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (k₀ : Gam) (u : Wiener1), u ≠ 0 ∧
      (∀ x ∈ (closure W)ᶜ, synth (incl u) x = 0) ∧
      ∀ (j : Fin 2) (x : Torus2),
        synth (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) j (incl u)) x ≠ 0 := by
  obtain ⟨u, K, hune, -, -, hKW, hvan⟩ := exists_smooth_localized_profile1 hW hne
  have hcoeff : ∃ k₀ : Gam, (incl u) k₀ ≠ 0 := by
    by_contra hall
    exact hune (Wiener1.coeff_injective
      (funext fun k => not_not.1 (fun hk => hall ⟨k, hk⟩)))
  obtain ⟨k₀, hk₀⟩ := hcoeff
  refine ⟨k₀, u, hune, ?_, ?_⟩
  · intro x hx
    exact hvan x (fun hK => hx (subset_closure (hKW hK)))
  · intro j x
    rw [velocity_modeSymbol, map_smul, synth_wdirac]
    show (incl u) k₀ * emode k₀ x ≠ 0
    refine mul_ne_zero hk₀ ?_
    intro hz
    have := norm_emode_apply k₀ x
    rw [hz, norm_zero] at this
    exact one_ne_zero this.symm

/-- Quantitatively: the exterior energy of the state is `0`, that of its velocity is
`‖û(k₀)‖²·|E|`. -/
theorem extL2sq_velocity_modeSymbol {W : Set Torus2} (hW : IsOpen W) (hne : W.Nonempty)
    (hE : ((closure W)ᶜ).Nonempty) :
    ∃ (k₀ : Gam) (u : Wiener1), u ≠ 0 ∧
      extL2sq (closure W)ᶜ (incl u) = 0 ∧
      0 < extL2sq (closure W)ᶜ
        (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) 0 (incl u)) := by
  obtain ⟨k₀, u, hune, hvan, hnz⟩ := exists_exterior_nonlocality hW hne
  have hEmeas : MeasurableSet ((closure W)ᶜ) := (isClosed_closure (s := W)).measurableSet.compl
  have hEopen : IsOpen ((closure W)ᶜ) := isClosed_closure.isOpen_compl
  have hpos : 0 < (volume : Measure Torus2) ((closure W)ᶜ) := hEopen.measure_pos _ hE
  have hne_top : (volume : Measure Torus2) ((closure W)ᶜ) ≠ ⊤ :=
    (measure_lt_top (volume : Measure Torus2) _).ne
  refine ⟨k₀, u, hune, extL2sq_eq_zero_of_vanishes hEmeas hvan, ?_⟩
  have hval : extL2sq (closure W)ᶜ
      (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) 0 (incl u))
      = ((volume : Measure Torus2) ((closure W)ᶜ)).toReal * ‖(incl u) k₀‖ ^ 2 := by
    rw [extL2sq]
    have hcongr : ∀ x : Torus2,
        ‖synth (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) 0 (incl u)) x‖ ^ 2
          = ‖(incl u) k₀‖ ^ 2 := by
      intro x
      rw [velocity_modeSymbol, map_smul, synth_wdirac]
      show ‖(incl u) k₀ * emode k₀ x‖ ^ 2 = _
      rw [norm_mul, norm_emode_apply, mul_one]
    rw [setIntegral_congr_ae hEmeas (Filter.Eventually.of_forall (fun x _ => hcongr x)),
      setIntegral_const, smul_eq_mul]
    rfl
  rw [hval]
  have hk₀ : (incl u) k₀ ≠ 0 := by
    intro hz
    have h0 := hnz 0 (0 : Torus2)
    rw [velocity_modeSymbol, map_smul, synth_wdirac] at h0
    exact h0 (by show (incl u) k₀ * emode k₀ 0 = 0; rw [hz, zero_mul])
  have h1 : 0 < ((volume : Measure Torus2) ((closure W)ᶜ)).toReal :=
    ENNReal.toReal_pos hpos.ne' hne_top
  have h2 : 0 < ‖(incl u) k₀‖ ^ 2 := by positivity
  exact mul_pos h1 h2

/-- **Exterior convergence of the scalar states does not imply exterior convergence of the
velocities of the full states.**  Both fields of `ExteriorStateConvergence` are needed. -/
theorem exists_state_conv_without_velocity_conv {W : Set Torus2} (hW : IsOpen W)
    (hne : W.Nonempty) (hE : ((closure W)ᶜ).Nonempty) :
    ∃ (k₀ : Gam) (u : ℕ → Wiener1) (U : Wiener1),
      Tendsto (fun n => Real.sqrt (extL2sq (closure W)ᶜ (incl (u n - U)))) atTop (nhds 0)
        ∧ ¬ ExteriorStateConvergence W (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) u U := by
  obtain ⟨k₀, a, hane, hzero, hpos⟩ := extL2sq_velocity_modeSymbol hW hne hE
  refine ⟨k₀, fun _ => a, 0, ?_, ?_⟩
  · have he : (fun n : ℕ => Real.sqrt (extL2sq (closure W)ᶜ (incl ((fun _ : ℕ => a) n - 0))))
        = fun _ : ℕ => (0:ℝ) := by
      funext n
      rw [sub_zero, hzero, Real.sqrt_zero]
    rw [he]
    exact tendsto_const_nhds
  · intro hconv
    have h := hconv.velocityConv 0
    have he : ∀ n : ℕ,
        Real.sqrt (extL2sq (closure W)ᶜ (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) 0
          (incl ((fun _ : ℕ => a) n - 0))))
        = Real.sqrt (extL2sq (closure W)ᶜ
            (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) 0 (incl a))) := by
      intro n; rw [sub_zero]
    rw [funext he] at h
    have hlim := tendsto_nhds_unique h tendsto_const_nhds
    have : Real.sqrt (extL2sq (closure W)ᶜ
        (velocity (modeSymbol k₀) (isBddSymbol_modeSymbol k₀) 0 (incl a))) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hpos)
    exact this hlim.symm

/-! ## 4. The positive half: the second state argument is an exterior datum -/

/-- For an exterior test, the source-region part of the tested integrand vanishes identically —
this is the explicit accounting of the contribution from `closure W`. -/
theorem setIntegral_source_region_eq_zero {W : Set Torus2} {ψ : Wiener1}
    (hψ : IsExteriorTest W ψ) (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (u v : Wiener1) :
    (∫ x in closure W, synth (incl v) x * synth (velocity m hm j (incl u)) x
        * synth (fourierDeriv j ψ) x) = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
  rw [hψ.deriv_vanishes j hx, mul_zero]

/-- **The tested interaction depends on the second state only through its restriction to the
exterior.**  (By `exists_exterior_nonlocality` the same is *false* for the first state.) -/
theorem sideInteraction_congr_exterior {W : Set Torus2} {ψ : Wiener1} (hψ : IsExteriorTest W ψ)
    (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (u v v' : Wiener1)
    (h : ∀ x ∈ (closure W)ᶜ, synth (incl v) x = synth (incl v') x) :
    sideInteraction m hm ψ u v = sideInteraction m hm ψ u v' := by
  have hEmeas : MeasurableSet ((closure W)ᶜ) := (isClosed_closure (s := W)).measurableSet.compl
  rw [sideInteraction_eq_exterior hψ m hm u v, sideInteraction_eq_exterior hψ m hm u v']
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine setIntegral_congr_ae hEmeas (Filter.Eventually.of_forall (fun x hx => ?_))
  rw [h x hx]

/-! ## 5. Global convergence supplies the remaining analytic input -/

/-- If the generated states converge to the target in the **global** physical `L²` norm, the
remaining analytic input of `ExteriorLimit` is met.  Combined with
`ae_eq_zero_of_tendsto_physicalL2`, this is the exact tension: global convergence would close
the step, but it forces the target to inherit the vanishing of the approximants. -/
theorem generatedExteriorApproximation_of_global (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (A : Submodule ℝ (Curve0 T)) (t : ℝ)
    {U : Wiener1} {g : ℕ → Curve0 T} (hg : ∀ n : ℕ, g n ∈ A)
    (hconv : Tendsto (fun n => ‖synthL2 (incl (curveState hT (duhamelOp hα hT (g n)) t - U))‖)
      atTop (nhds 0)) :
    GeneratedExteriorApproximation hα hT W m hm A t U :=
  ⟨g, hg, exteriorStateConvergence_of_global W hm hconv⟩

end LiWang.WienerModel
