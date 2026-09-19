/-
# Recovering pointwise data, the exterior energy budget, and what the step reduces to

Three further pieces of the analysis of the state-approximation step.

* **Recovery in the other direction.**  `PrimitiveGraph` converts pointwise vanishing on the
  open region `W` into restricted-measure vanishing.  Here the converse is proved
  (`eq_zero_on_of_aeRestrict`): a continuous physical field that vanishes almost everywhere on
  an *open* set vanishes there identically, because a nonempty open subset of `𝕋²` has positive
  Haar measure.  Consequently the complex predicate `FractionalUCP` and the platform-shaped real
  boundary `RealFractionalUCP` are **equivalent** on open regions
  (`realFractionalUCP_iff_fractionalUCP`), so either may be instantiated with no loss.

* **The exterior energy budget.**  `extL2sq_add_compl` splits the global energy across a
  measurable set and its complement.  For a *continuous* physical field the boundary strip
  carries **no** energy: `synth_eq_zero_on_closure` shows that vanishing on `W` forces vanishing
  on `closure W` (the zero set is closed, so `closure_minimal` applies), hence
  `extL2sq_boundary_strip_eq_zero` and `extL2sq_exterior_of_vanishes_on`, which now reads
  `extL2sq E a = ‖a‖²_{L²(𝕋²)}` exactly.  No null-boundary assumption is used or needed.  This
  is a correction of the v5.0 commentary, and it is **not** a convergence statement: the global
  energy of a generated state is still not controlled.

* **A sufficient continuity lemma.**  `generatedExteriorApproximation_of_source_tendsto` proves
  that `Curve0 T`-norm convergence of the *sources* gives every exterior hypothesis for the
  generated states.  It applies **only** to targets of the form `J(gLim)(t)`, and it is *not*
  equivalent to Runge approximation: Runge controls need not converge at all, and their norms
  may diverge.  It is a sufficient condition for a restricted family of targets, nothing more.

Part of `LiWangWienerSmoothObservationPacket` v5.0.
-/
import LiWangWiener.ExteriorObstruction
import LiWangWiener.PrimitiveGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. Recovering pointwise vanishing on an open region -/

/-- **The converse of `aeRestrict_synthL2_eq_zero`.**  A continuous physical field vanishing
almost everywhere on an *open* region vanishes there identically. -/
theorem eq_zero_on_of_aeRestrict {W : Set Torus2} (hW : IsOpen W) {a : Wiener}
    (h : (synthL2 a : Torus2 → ℂ) =ᵐ[(volume : Measure Torus2).restrict W] 0) :
    ∀ x ∈ W, synth a x = 0 := by
  have h1 : (fun x : Torus2 => synth a x)
      =ᵐ[(volume : Measure Torus2).restrict W] (0 : Torus2 → ℂ) := by
    refine Filter.EventuallyEq.trans ?_ h
    exact ((synthL2_apply_ae a).filter_mono
      (MeasureTheory.ae_mono Measure.restrict_le_self)).symm
  have hmeas : ((volume : Measure Torus2).restrict W) {x : Torus2 | synth a x ≠ 0} = 0 := by
    have hae : ∀ᵐ x ∂((volume : Measure Torus2).restrict W), synth a x = 0 := by
      filter_upwards [h1] with x hx
      exact hx
    rw [ae_iff] at hae
    exact hae
  intro x hx
  by_contra hne
  set S : Set Torus2 := {y : Torus2 | synth a y ≠ 0} ∩ W with hSdef
  have hSopen : IsOpen S :=
    ((isClosed_eq (synth a).continuous continuous_const).isOpen_compl).inter hW
  have hSne : S.Nonempty := ⟨x, hne, hx⟩
  have hzero : (volume : Measure Torus2) S = 0 := by
    rw [hSdef, ← Measure.restrict_apply' hW.measurableSet]
    exact hmeas
  exact absurd hzero (hSopen.measure_pos (volume : Measure Torus2) hSne).ne'

/-- **The real and complex unique-continuation boundaries are equivalent** on an open region:
the real-only hypothesis the platform proves is exactly as strong as the complex predicate the
v4.0 bridge consumes. -/
theorem realFractionalUCP_iff_fractionalUCP (hα : 0 < α) {W : Set Torus2} (hW : IsOpen W) :
    RealFractionalUCP α W ↔ FractionalUCP α W := by
  refine ⟨fun h => fractionalUCP_of_real hα hW.measurableSet h, fun h v F hgraph => ?_⟩
  refine h v F hgraph.coeffRel ?_ ?_
  · exact eq_zero_on_of_aeRestrict hW hgraph.stateVanishes
  · exact eq_zero_on_of_aeRestrict hW hgraph.fracVanishes

/-! ## 2. The exterior energy budget -/

theorem integrable_norm_sq_synth (a : Wiener) :
    Integrable (fun x : Torus2 => ‖synth a x‖ ^ 2) (volume : Measure Torus2) :=
  ((synth a).continuous.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem extL2sq_univ (a : Wiener) : extL2sq Set.univ a = ‖synthL2 a‖ ^ 2 := by
  rw [extL2sq, setIntegral_univ, integral_norm_sq_synth, norm_synthL2_sq]

/-- The exterior energy and the interior energy add up to the global one. -/
theorem extL2sq_add_compl {S : Set Torus2} (hS : MeasurableSet S) (a : Wiener) :
    extL2sq S a + extL2sq Sᶜ a = ‖synthL2 a‖ ^ 2 := by
  rw [← extL2sq_univ, extL2sq, extL2sq, extL2sq, setIntegral_univ]
  exact integral_add_compl hS (integrable_norm_sq_synth a)

/-- The measured region and the boundary strip also add up. -/
theorem extL2sq_closure_split {W : Set Torus2} (hW : IsOpen W) (a : Wiener) :
    extL2sq W a + extL2sq (closure W \ W) a = extL2sq (closure W) a := by
  have hdis : Disjoint W (closure W \ W) := Set.disjoint_sdiff_right
  have hunion : W ∪ (closure W \ W) = closure W := by
    rw [Set.union_diff_cancel subset_closure]
  have hsplit := setIntegral_union hdis (isClosed_closure.measurableSet.diff hW.measurableSet)
    (integrable_norm_sq_synth a).integrableOn (integrable_norm_sq_synth a).integrableOn
  rw [hunion] at hsplit
  rw [extL2sq, extL2sq, extL2sq]
  exact hsplit.symm

/-- **A continuous physical field vanishing on `W` vanishes on `closure W`.**  The zero set of
`synth a` is closed, so `closure_minimal` applies.  No measure-theoretic hypothesis is used. -/
theorem synth_eq_zero_on_closure {W : Set Torus2} {a : Wiener} (h : ∀ x ∈ W, synth a x = 0) :
    ∀ x ∈ closure W, synth a x = 0 := by
  have hsub : W ⊆ {x : Torus2 | synth a x = 0} := fun x hx => h x hx
  have hclosed : IsClosed {x : Torus2 | synth a x = 0} :=
    isClosed_eq (synth a).continuous continuous_const
  exact fun x hx => closure_minimal hsub hclosed hx

/-- **Hence the boundary strip carries no energy.**  This corrects the v5.0 commentary: for the
*continuous* physical fields at issue there is no unaccounted boundary term. -/
theorem extL2sq_boundary_strip_eq_zero {W : Set Torus2} (hW : IsOpen W) {a : Wiener}
    (h : ∀ x ∈ W, synth a x = 0) : extL2sq (closure W \ W) a = 0 := by
  refine extL2sq_eq_zero_of_vanishes
    (isClosed_closure.measurableSet.diff hW.measurableSet) (fun x hx => ?_)
  exact synth_eq_zero_on_closure h x hx.1

/-- **What the measured identity buys, exactly.**  If the physical field vanishes on the
measured region `W`, its exterior energy is *equal to* the global energy.  The global energy is
still not controlled for generated states, so this is a bookkeeping identity, **not** a
convergence statement. -/
theorem extL2sq_exterior_of_vanishes_on {W : Set Torus2} (hW : IsOpen W) {a : Wiener}
    (h : ∀ x ∈ W, synth a x = 0) :
    extL2sq (closure W)ᶜ a = ‖synthL2 a‖ ^ 2 := by
  have hW0 : extL2sq W a = 0 := extL2sq_eq_zero_of_vanishes hW.measurableSet h
  have hstrip : extL2sq (closure W \ W) a = 0 := extL2sq_boundary_strip_eq_zero hW h
  have h1 := extL2sq_add_compl (isClosed_closure (s := W)).measurableSet a
  have h2 := extL2sq_closure_split hW a
  rw [hW0, hstrip, zero_add] at h2
  rw [← h2] at h1
  linarith

/-! ## 3. What the state-approximation step reduces to -/

theorem curveState_sub (hT : 0 ≤ T) (u v : Curve1 T) (t : ℝ) :
    curveState hT (u - v) t = curveState hT u t - curveState hT v t := rfl

theorem norm_synthL2_incl_curveState_le (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) :
    ‖synthL2 (incl (curveState hT (duhamelOp hα hT g) t))‖
      ≤ ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ * ‖g‖ := by
  calc ‖synthL2 (incl (curveState hT (duhamelOp hα hT g) t))‖
      ≤ ‖incl (curveState hT (duhamelOp hα hT g) t)‖ := norm_synthL2_le _
    _ ≤ ‖curveState hT (duhamelOp hα hT g) t‖ := norm_incl_apply_le _
    _ = ‖(duhamelOp hα hT g) (clampT hT t)‖ := (RealWiener1.norm_def _).symm
    _ ≤ ‖duhamelOp hα hT g‖ := ((duhamelOp hα hT) g).norm_coe_le_norm _
    _ ≤ ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ * ‖g‖ :=
        (duhamelOp hα hT).le_opNorm g

/-- **A sufficient continuity lemma.**  Convergence of the *sources* in the `Curve0 T` norm
gives every exterior hypothesis for the generated states.  It applies only to targets of the
form `J(gLim)(t)`, and is **not** equivalent to Runge approximation: Runge controls need not
converge, and their norms may diverge.  Nothing here says which targets are reachable. -/
theorem generatedExteriorApproximation_of_source_tendsto (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (W : Set Torus2) {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (A : Submodule ℝ (Curve0 T))
    (t : ℝ) {g : ℕ → Curve0 T} {gLim : Curve0 T} (hg : ∀ n : ℕ, g n ∈ A)
    (hconv : Tendsto (fun n => ‖g n - gLim‖) atTop (nhds 0)) :
    GeneratedExteriorApproximation hα hT W m hm A t
      (curveState hT (duhamelOp hα hT gLim) t) := by
  refine generatedExteriorApproximation_of_global hα hT W hm A t hg ?_
  have hstep : ∀ n : ℕ,
      ‖synthL2 (incl (curveState hT (duhamelOp hα hT (g n)) t
          - curveState hT (duhamelOp hα hT gLim) t))‖
        ≤ ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ * ‖g n - gLim‖ := by
    intro n
    have he : curveState hT (duhamelOp hα hT (g n)) t - curveState hT (duhamelOp hα hT gLim) t
        = curveState hT (duhamelOp hα hT (g n - gLim)) t := by
      rw [map_sub, curveState_sub]
    rw [he]
    exact norm_synthL2_incl_curveState_le hα hT (g n - gLim) t
  have hlim : Tendsto
      (fun n : ℕ => ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ * ‖g n - gLim‖)
      atTop (nhds 0) := by
    have h := hconv.const_mul ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖
    rwa [mul_zero] at h
  exact squeeze_zero (fun n => norm_nonneg _) hstep hlim

end LiWang.WienerModel
