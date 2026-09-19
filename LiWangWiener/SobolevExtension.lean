/-
**Entering the Sobolev solution class from data on `[0,T]`.**

`IsSobolevSolution` quantifies its regularity fields over every real time, because the weak
equation is integrated against an `A¹` state that has to exist at every `s` appearing in a
Bochner integral.  A solution produced by the forward theory is given on `[0,T]` only, and its
`H³` bound may hold only almost everywhere.

This module closes that entry point **by proof**, not by convention:

* `sobClamp` is the extension of an `L²(𝕋²)`-valued state by clamping the time to `[0,T]`; it
  agrees with the original at every time of `[0,T]` (`sobClamp_of_mem`);
* `bound_sobClamp_of_ae` upgrades an **almost-everywhere** `H³` bound on `[0,T]` to a bound at
  **every real time** for the clamped extension, by `forall_finset_sum_le_of_ae` — so the a.e.→
  everywhere lemma of `SobolevCurve` is actually wired into the class, endpoints included;
* `isSobolevSolution_sobClamp` assembles the clamped extension into an `IsSobolevSolution` from
  hypotheses all stated on `[0,T]`: continuity of the Fourier coordinates **on the interval**,
  reality on the interval, the a.e. `H³` bound, the zero initial value, and the weak equation.

Part of `LiWangWienerSobolevCompatibilityPacket` v8.0.
-/
import LiWangWiener.SobolevSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The clamped extension -/

/-- The extension of a time-dependent `L²(𝕋²)` state to all of `ℝ` by clamping the time to
`[0,T]`.  It changes nothing on `[0,T]`. -/
noncomputable def sobClamp (hT : 0 ≤ T) (θ : ℝ → TorusL2) (t : ℝ) : TorusL2 :=
  θ ((clampT hT t : TimeI T) : ℝ)

theorem sobClamp_mem (hT : 0 ≤ T) (t : ℝ) :
    ((clampT hT t : TimeI T) : ℝ) ∈ Set.Icc (0:ℝ) T := (clampT hT t).2

/-- **The extension agrees with the original at every time of `[0,T]`.** -/
theorem sobClamp_of_mem (hT : 0 ≤ T) (θ : ℝ → TorusL2) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    sobClamp hT θ t = θ t := by
  rw [sobClamp, clampT_coe hT ht.1 ht.2]

theorem sobClamp_idem (hT : 0 ≤ T) (θ : ℝ → TorusL2) (t : ℝ) :
    sobClamp hT θ ((clampT hT t : TimeI T) : ℝ) = sobClamp hT θ t :=
  sobClamp_of_mem hT θ (sobClamp_mem hT t)

/-- Coefficientwise continuity **on `[0,T]`** already makes the clamped extension continuous on
all of `ℝ`. -/
theorem continuous_l2coeff_sobClamp (hT : 0 ≤ T) {θ : ℝ → TorusL2}
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T))
    (k : Gam) : Continuous fun t : ℝ => l2coeff k (sobClamp hT θ t) :=
  (hcont k).comp_continuous ((continuous_clampT hT).subtype_val) (fun t => (clampT hT t).2)

/-! ## 2. From an almost-everywhere `H³` bound to the field of the class -/

/-- **The a.e. `H³` bound becomes a bound at every real time.**  This is the lemma that wires
`forall_finset_sum_le_of_ae` — whose endpoint and null-set handling is explicit — into the
`bound` field of `IsSobolevSolution`. -/
theorem bound_sobClamp_of_ae {T : ℝ} (hT : 0 < T) {θ : ℝ → TorusL2} {M : ℝ}
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T))
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) :
    ∀ t : ℝ, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (sobClamp hT.le θ t)‖ ^ 2) ≤ M := by
  have hc : ∀ k : Gam, Continuous fun t : ℝ => l2coeff k (sobClamp hT.le θ t) :=
    continuous_l2coeff_sobClamp hT.le hcont
  have hae' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (sobClamp hT.le θ t)‖ ^ 2) ≤ M := by
    filter_upwards [hae] with t ht hmem F
    rw [sobClamp_of_mem hT.le θ hmem]
    exact ht hmem F
  have hall := forall_finset_sum_le_of_ae
    (a := fun t k => l2coeff k (sobClamp hT.le θ t)) hT hc hae'
  intro t F
  have hval := hall _ (sobClamp_mem hT.le t) F
  simp only [sobClamp_idem hT.le θ t] at hval
  exact hval

/-! ## 3. The constructor -/

/-- **A Sobolev solution from data on `[0,T]`.**  Every hypothesis is stated on the closed
interval — coefficient continuity on `[0,T]`, reality on `[0,T]`, the `H³` bound only almost
everywhere, the zero initial value, and the weak equation on `[0,T]` — and the conclusion is an
`IsSobolevSolution` for the clamped extension, which coincides with the given state at every
time of `[0,T]` (`sobClamp_of_mem`). -/
theorem isSobolevSolution_sobClamp (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T) (hm : IsBddSymbol m)
    {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T))
    (hreal : ∀ t ∈ Set.Icc (0:ℝ) T, ConjSymmetric fun k : Gam => l2coeff k (θ t))
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M)
    (hinit : θ 0 = 0)
    (hweak : ∀ (F : Finset Gam) (c : Gam → ℂ), ∀ t ∈ Set.Icc (0:ℝ) T,
      spacePair (incl (sobState (bound_sobClamp_of_ae hT hcont hae) t)) (trigPoly F c)
        + (∫ s in (0:ℝ)..t,
            spacePair (incl (sobState (bound_sobClamp_of_ae hT hcont hae) s))
              (fracLapPoly α F c))
        + (∫ s in (0:ℝ)..t,
            spacePair (transport m hm (sobState (bound_sobClamp_of_ae hT hcont hae) s)
              (sobState (bound_sobClamp_of_ae hT hcont hae) s)) (trigPoly F c))
        = ∫ s in (0:ℝ)..t, spacePair (sourceFun hT.le f s) (trigPoly F c)) :
    IsSobolevSolution hα hT.le hm M f (sobClamp hT.le θ) where
  coeff_continuous := continuous_l2coeff_sobClamp hT.le hcont
  real := fun t => hreal _ (sobClamp_mem hT.le t)
  bound := bound_sobClamp_of_ae hT hcont hae
  initial := by
    rw [sobClamp, clampT_coe hT.le le_rfl hT.le]
    exact hinit
  weak := hweak

/-- **The representative of the clamped extension represents the original state.** -/
theorem synthL2_curveState_sobClamp {hα : 1 / 2 < α} {T : ℝ} {hT : 0 ≤ T} {hm : IsBddSymbol m}
    {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsSobolevSolution hα hT hm M f (sobClamp hT θ)) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    synthL2 (incl (curveState hT h.curve s)) = θ s := by
  rw [h.synthL2_curveState hs, sobClamp_of_mem hT θ hs]

end LiWang.WienerModel
