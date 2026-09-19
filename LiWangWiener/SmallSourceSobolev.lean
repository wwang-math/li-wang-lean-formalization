/-
# The constructed small-source solution is a Sobolev solution

Step 3 (conclusion) of the v8.0 Sobolev-compatibility bridge.

This file runs the tame bootstrap of `HigherRegularity.lean`:

    `A¹` (ball)  ⟶  `wt²`  ⟶  `wt³`  ⟶  `H³`,

each arrow being one application of `WB_picard_uniform` (one Duhamel weight gain absorbed by
the small `A¹` norm), and the last one `sobBound_of_WB3`.  The bounds are proved for the
**Picard iterates** and transferred to the actual mild solution by coefficientwise convergence
(`WB_mild_of_picard`): no convergence in a stronger norm is used anywhere.

The conclusion `isSobolevSolution_mild` says that the constructed small-source mild state,
viewed in `L²(𝕋²)`, satisfies the Sobolev solution predicate of `SobolevSolution.lean`.  This is
what discharges `SobolevExistence` in the observation bridge — for sources whose own `wt¹` and
`wt²` coefficient sums are bounded, which is the honest hypothesis: a `Curve0` ball alone cannot
give it, since a highly oscillatory smooth source is small in `Curve0` and large in every higher
norm.

Part of `LiWangWienerSobolevCompatibilityPacket` v8.0.
-/
import LiWangWiener.HigherRegularity
import LiWangWiener.SobolevSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The physical state of a mild solution -/

/-- The `L²(𝕋²)` state of a coefficient curve. -/
noncomputable def mildPhysState (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) : TorusL2 :=
  synthL2 (incl (curveState hT u t))

@[simp] theorem l2coeff_mildPhysState (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) (k : Gam) :
    l2coeff k (mildPhysState hT u t) = (curveState hT u t).coeff k := by
  rw [mildPhysState, l2coeff_synthL2]
  rfl

/-! ## 2. The bootstrap -/

variable {hα : 1 / 2 < α} {hT : 0 ≤ T} {hm : IsBddSymbol m} {hr : IsRealSymbol m}

/-- **The tame bootstrap.**  From a `wt¹` and a `wt²` bound on the source, and smallness of the
`A¹` norm, the mild solution has a uniform `wt³` bound at every time of `[0,T]`. -/
theorem WB3_of_mild {f : Curve0 T} {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {b ρ : ℝ} (hb : ‖sourceQuad hα hT m hm hr‖ ≤ b) (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ)
    (hbρ : b * ρ ≤ 1 / 4) (hfsmall : ‖duhamelOp hα hT f‖ ≤ ρ / 2)
    {S1 S2 : ℝ} (hS10 : 0 ≤ S1) (hS20 : 0 ≤ S2)
    (hS1 : ∀ s : ℝ, WB 1 S1 (fun k => (sourceFun hT f s) k))
    (hS2 : ∀ s : ℝ, WB 2 S2 (fun k => (sourceFun hT f s) k))
    (habs1 : duhamelConst α T * (transportConst 1 C * ρ) ≤ 1 / 2)
    (habs2 : duhamelConst α T * (transportConst 2 C * ρ) ≤ 1 / 2)
    {u : Curve1 T} (hu : ‖u‖ ≤ ρ)
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    ∃ R3 : ℝ, 0 ≤ R3 ∧ ∀ t ∈ Set.Icc (0:ℝ) T, WB 3 R3 (curveState hT u t).coeff := by
  have hK0 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  have hC0 : (0:ℝ) ≤ C := nonneg_of_symbol_bound hC
  have hcc1 : (0:ℝ) ≤ transportConst 1 C := by
    rw [transportConst]; have := Real.pi_pos; positivity
  have hcc2 : (0:ℝ) ≤ transportConst 2 C := by
    rw [transportConst]; have := Real.pi_pos; positivity
  -- the ball bound gives the `wt¹` bound on every iterate
  have hball : ∀ n : ℕ, ∀ s : ℝ, ‖curveState hT (picard hα hT hm hr f n) s‖ ≤ ρ := by
    intro n s
    exact le_trans (norm_curveState_le hT _ s) (picard_norm_le hb hb0 hρ0 hbρ hfsmall n)
  have hR1 : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB 1 ρ (curveState hT (picard hα hT hm hr f n) t).coeff :=
    fun n t _ => (WB.wiener1 (curveState hT (picard hα hT hm hr f n) t)).mono (hball n t)
  -- first bootstrap: `wt²`
  set R2 : ℝ := 2 * ((S1 + transportConst 1 C * (ρ * ρ)) * duhamelConst α T) with hR2def
  have hR2 : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB 2 R2 (curveState hT (picard hα hT hm hr f n) t).coeff := by
    intro n
    exact WB_picard_uniform hC hb hb0 hρ0 hbρ hfsmall hS10 hρ0 hS1 hR1 habs1 n
  have hR20 : 0 ≤ R2 := by
    rw [hR2def]
    have : (0:ℝ) ≤ transportConst 1 C * (ρ * ρ) := by positivity
    nlinarith
  -- second bootstrap: `wt³`
  set R3 : ℝ := 2 * ((S2 + transportConst 2 C * (R2 * ρ)) * duhamelConst α T) with hR3def
  have hR3 : ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      WB 3 R3 (curveState hT (picard hα hT hm hr f n) t).coeff := by
    intro n
    exact WB_picard_uniform hC hb hb0 hρ0 hbρ hfsmall hS20 hR20 hS2 hR2 habs2 n
  have hR30 : 0 ≤ R3 := by
    rw [hR3def]
    have : (0:ℝ) ≤ transportConst 2 C * (R2 * ρ) := by positivity
    nlinarith
  refine ⟨R3, hR30, fun t ht => ?_⟩
  exact WB_mild_of_picard hb hb0 hρ0 hbρ hfsmall hu hmild (fun n => hR3 n t ht)

/-! ## 3. The mild solution is a Sobolev solution -/

/-- **The constructed small-source mild state is a Sobolev solution.**  Every field of
`IsSobolevSolution` is proved: the coefficients are continuous in time, the state is real, the
`H³` bound comes from the `wt³` bound of the bootstrap, the initial trace is the genuine trace
of the continuous representative, and the weak equation is the v7 predicate transported through
the (definitional) identification of the two `A¹` states. -/
theorem isSobolevSolution_mild {f : Curve0 T} {u : Curve1 T} {R3 : ℝ}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (h3 : ∀ t ∈ Set.Icc (0:ℝ) T, WB 3 R3 (curveState hT u t).coeff) :
    IsSobolevSolution hα hT hm (R3 ^ 2) f (mildPhysState hT u) := by
  have hall : ∀ t : ℝ, WB 3 R3 (curveState hT u t).coeff := WB_curveState_all h3
  have hbound : ∀ t : ℝ, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (mildPhysState hT u t)‖ ^ 2) ≤ R3 ^ 2 := by
    intro t F
    have := sobBound_of_WB3 (hall t) F
    simpa only [l2coeff_mildPhysState] using this
  refine ⟨fun k => ?_, fun t => ?_, hbound, ?_, ?_⟩
  · simpa only [l2coeff_mildPhysState] using continuous_coeff_curveState hT u k
  · have hc : ConjSymmetric (curveState hT u t).coeff := (u (clampT hT t)).conjSymmetric
    simpa only [l2coeff_mildPhysState] using hc
  · rw [mildPhysState, curveState_initial_of_mild hα hT hm hr hmild, map_zero, map_zero]
  · -- the weak equation
    have hstate : ∀ s : ℝ, sobState hbound s = curveState hT u s := by
      intro s
      exact Wiener1.coeff_injective (funext fun k => by
        rw [sobState_coeff, l2coeff_mildPhysState])
    have hphys := (isPhysicalSolution_of_mild hα hT hm hr hmild).weak
    intro F c t ht
    have hw := hphys (trigPoly F c) F c rfl t ht
    simp only [hstate]
    have hq2 : (∫ s in (0:ℝ)..t,
          spacePair (transport m hm (curveState hT u s) (curveState hT u s)) (trigPoly F c))
        = ∫ s in (0:ℝ)..t, spacePair (quadCurve hm (curveState hT u) s) (trigPoly F c) := rfl
    rw [hq2]
    exact hw

end LiWang.WienerModel
