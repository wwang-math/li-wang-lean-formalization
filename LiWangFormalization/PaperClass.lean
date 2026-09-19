/-
# Entering the paper class from an essential-supremum bound

Proposition 3.1 puts the solution in `L^∞(0,T;H^s)`, an **essential** supremum; the field
`IsPaperSolution.energy3` asks for the bound at every time of `[0,T]`, because the `A¹` state
`paperState` used to write the nonlinear term has to exist at every time.

This module removes that discrepancy by proving the upgrade, for the class's own notion of
continuity (continuity of each Fourier coordinate **on the closed interval**, not on all of `ℝ`):

* `forall_le_of_ae_le_on` — a relatively continuous function on `[0,T]` that is `≤ M` almost
  everywhere there is `≤ M` everywhere there, endpoints included;
* `forall_finset_sum_le_of_ae_on` — the same for the finite partial sums of the `H³` energy;
* `isPaperSolution_of_ae` — a paper solution built from hypotheses in which the `H³` bound is
  only assumed almost everywhere.

Part of `LiWangFormalizationPaperSourceRealizationPacket` v10.0.
-/
import LiWangFormalization.PaperSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The almost-everywhere upgrade for a relatively continuous function -/

/-- **A closed full-measure condition on `[0,T]` holds at every point**, for a function that is
only continuous *relative to* `[0,T]`.  The endpoints are where this matters: around any
`t ∈ [0,T]` the set `Ioo (max 0 (t−η)) (min T (t+η))` is a nonempty subset of `[0,T]`, hence of
positive Lebesgue measure, so the exceptional null set cannot contain it. -/
theorem forall_le_of_ae_le_on {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0:ℝ) T)) {M : ℝ}
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T → g t ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) T, g t ≤ M := by
  intro t ht
  by_contra hcon
  push Not at hcon
  have hnb : {y : ℝ | M < y} ∈ nhds (g t) := (isOpen_lt' M).mem_nhds hcon
  have hpre : g ⁻¹' {y : ℝ | M < y} ∈ nhdsWithin t (Set.Icc (0:ℝ) T) := hg t ht hnb
  obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpre
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hu
  set A : ℝ := max 0 (t - η) with hA
  set B : ℝ := min T (t + η) with hB
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hAB : A < B := max_lt (lt_min hT (by linarith)) (lt_min (by linarith) (by linarith))
  have hA0 : 0 ≤ A := le_max_left _ _
  have hAt : t - η ≤ A := le_max_right _ _
  have hBT : B ≤ T := min_le_left _ _
  have hBt : B ≤ t + η := min_le_right _ _
  have hsubset : Set.Ioo A B ⊆ {s : ℝ | ¬ (s ∈ Set.Icc (0:ℝ) T → g s ≤ M)} := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hA0 hs.1.le
    have hsT : s ≤ T := le_trans hs.2.le hBT
    have hdist : dist s t < η := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [linarith [hs.1, hAt]; linarith [hs.2, hBt]]
    have hmu : s ∈ u := hball (by rwa [Metric.mem_ball])
    have hgs : M < g s := hsub ⟨hmu, ⟨hs0, hsT⟩⟩
    intro hmem
    exact absurd (hmem ⟨hs0, hsT⟩) (not_le.2 hgs)
  have hnull : (volume : Measure ℝ) {s : ℝ | ¬ (s ∈ Set.Icc (0:ℝ) T → g s ≤ M)} = 0 :=
    MeasureTheory.ae_iff.1 hae
  have hzero : (volume : Measure ℝ) (Set.Ioo A B) = 0 := measure_mono_null hsubset hnull
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hzero
  linarith

/-- **The `H³` bound, given only almost everywhere, holds at every time of `[0,T]`** for a state
whose Fourier coordinates are continuous on `[0,T]`. -/
theorem forall_finset_sum_le_of_ae_on {T : ℝ} (hT : 0 < T) {θ : ℝ → TorusL2}
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T)) {M : ℝ}
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M := by
  intro t ht F
  refine forall_le_of_ae_le_on hT
    (g := fun s => ∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ s)‖ ^ 2) ?_ ?_ t ht
  · exact continuousOn_finset_sum F
      (fun k _ => continuousOn_const.mul (((hcont k).norm).pow 2))
  · filter_upwards [hae] with s hs hsmem
    exact hs hsmem F

/-! ## 2. The constructor -/

/-- **A Li–Wang `s = 3` solution from an essential-supremum `H³` bound.**  Every hypothesis is
stated on `[0,T]`, and the `H³` bound only almost everywhere; the everywhere form needed to
define the `A¹` state is *derived* by `forall_finset_sum_le_of_ae_on`. -/
theorem isPaperSolution_of_ae (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T) (hm : IsBddSymbol m)
    {M N K : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2} (hα1 : α < 1)
    (hcont : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T))
    (hreal : ∀ t ∈ Set.Icc (0:ℝ) T, ConjSymmetric fun k : Gam => l2coeff k (θ t))
    (hinit : θ 0 = 0)
    (hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M)
    (hsob3a : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (3 + α) (fun k => l2coeff k (θ t)))
    (henergy3a : (∫⁻ t in Set.Ioc (0:ℝ) T,
      ENNReal.ofReal (sobEnergy (3 + α) (fun k => l2coeff k (θ t)))) ≤ ENNReal.ofReal N)
    (hlq : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      eLpNorm ((θ t : Torus2 → ℂ)) (ENNReal.ofReal (paperExp α)) (volume : Measure Torus2)
        ≤ ENNReal.ofReal K)
    (hweak : ∀ (F : Finset Gam) (c : Gam → ℂ), ∀ t ∈ Set.Icc (0:ℝ) T,
      spacePair (incl (paperState hT.le (forall_finset_sum_le_of_ae_on hT hcont hae) t))
          (trigPoly F c)
        + (∫ s in (0:ℝ)..t,
            spacePair (incl (paperState hT.le (forall_finset_sum_le_of_ae_on hT hcont hae) s))
              (fracLapPoly α F c))
        + (∫ s in (0:ℝ)..t,
            spacePair (transport m hm
              (paperState hT.le (forall_finset_sum_le_of_ae_on hT hcont hae) s)
              (paperState hT.le (forall_finset_sum_le_of_ae_on hT hcont hae) s)) (trigPoly F c))
        = ∫ s in (0:ℝ)..t, spacePair (sourceFun hT.le f s) (trigPoly F c)) :
    IsPaperSolution hα hT hm M N K f θ where
  alpha_lt_one := hα1
  coeff_continuous := hcont
  real := hreal
  initial := hinit
  energy3 := forall_finset_sum_le_of_ae_on hT hcont hae
  sob3a := hsob3a
  energy3a := henergy3a
  lq := hlq
  weak := hweak

end LiWang.Formalization
