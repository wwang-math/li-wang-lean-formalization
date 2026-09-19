/-
# Deriving the time-continuous representative of a paper energy solution

Proposition 3.1 states Bochner-space bounds and does not assume time continuity.  This file
introduces an integrated weak-energy class with no continuity field.  The only temporal
well-definedness fields say that the two integrands occurring in the weak equation are interval
integrable.  Continuity of every Fourier coordinate is then a theorem: each coordinate is the
difference of three indefinite integrals.  The uniform Sobolev tail upgrades this to the
canonical strongly continuous representative already used by `IsPaperSolution`.
-/
import LiWangWiener.PaperClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. A total a.e. Sobolev representative -/

/-- The finite Fourier pairing of an `L2` state with a trigonometric polynomial. -/
noncomputable def l2TrigPair (θ : TorusL2) (F : Finset Gam) (c : Gam → ℂ) : ℂ :=
  ∑ j ∈ F, c j * l2coeff (-j) θ

/-- A total `A^1` representative of an `L2` state: use the proved `H3 -> A1` embedding when
the state is in `H3`, and use zero on the exceptional set.  Integral statements are insensitive
to that null-set convention. -/
noncomputable def paperEnergyState (θ : ℝ → TorusL2) (t : ℝ) : Wiener1 := by
  classical
  exact if h : Summable (fun k : Gam => rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) then
    sobToWiener1 h
  else 0

@[simp] theorem paperEnergyState_coeff_of_summable {θ : ℝ → TorusL2} {t : ℝ}
    (h : Summable (fun k : Gam => rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2)) (k : Gam) :
    (paperEnergyState θ t).coeff k = l2coeff k (θ t) := by
  simp [paperEnergyState, h]

theorem h3Summable_of_finset_bound {θ : ℝ → TorusL2} {t M : ℝ}
    (h : ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) :
    Summable (fun k : Gam => rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) :=
  summable_of_finset_sum_le (rho_pow_norm_sq_nonneg 3 (fun k => l2coeff k (θ t))) h

theorem l2TrigPair_mode (θ : TorusL2) (k : Gam) :
    l2TrigPair θ {-k} (fun _ => 1) = l2coeff k θ := by
  simp [l2TrigPair]

/-! ## 2. The continuity-free energy solution -/

/-- A paper solution represented only through the Bochner bounds and integrated weak equation.
There is deliberately no continuity field.  `dissipation_integrable` and
`transport_integrable` are the temporal integrability needed for the displayed weak equation,
not regularity of the state. -/
structure IsPaperEnergySolution (hα : 1 / 2 < α) (hT : 0 < T) (hm : IsBddSymbol m)
    (M N K : ℝ) (f : Curve0 T) (θ : ℝ → TorusL2) : Prop where
  alpha_lt_one : α < 1
  real : ∀ t ∈ Set.Icc (0 : ℝ) T, ConjSymmetric fun k : Gam => l2coeff k (θ t)
  initial : θ 0 = 0
  energy3 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0 : ℝ) T →
    ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M
  sob3a : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) T)),
    MemSobolev (3 + α) (fun k => l2coeff k (θ t))
  energy3a : (∫⁻ t in Set.Ioc (0 : ℝ) T,
      ENNReal.ofReal (sobEnergy (3 + α) (fun k => l2coeff k (θ t)))) ≤ ENNReal.ofReal N
  lq : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) T)),
    eLpNorm ((θ t : Torus2 → ℂ)) (ENNReal.ofReal (paperExp α))
      (volume : Measure Torus2) ≤ ENNReal.ofReal K
  dissipation_integrable : ∀ (F : Finset Gam) (c : Gam → ℂ),
    IntervalIntegrable
      (fun s : ℝ => spacePair (incl (paperEnergyState θ s)) (fracLapPoly α F c))
      (volume : Measure ℝ) 0 T
  transport_integrable : ∀ (F : Finset Gam) (c : Gam → ℂ),
    IntervalIntegrable
      (fun s : ℝ => spacePair
        (transport m hm (paperEnergyState θ s) (paperEnergyState θ s)) (trigPoly F c))
      (volume : Measure ℝ) 0 T
  weak : ∀ (F : Finset Gam) (c : Gam → ℂ), ∀ t ∈ Set.Icc (0 : ℝ) T,
    l2TrigPair (θ t) F c
      + (∫ s in (0 : ℝ)..t,
          spacePair (incl (paperEnergyState θ s)) (fracLapPoly α F c))
      + (∫ s in (0 : ℝ)..t,
          spacePair (transport m hm (paperEnergyState θ s) (paperEnergyState θ s))
            (trigPoly F c))
      = ∫ s in (0 : ℝ)..t, spacePair (sourceFun hT.le f s) (trigPoly F c)

namespace IsPaperEnergySolution

variable {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m} {M N K : ℝ}
  {f : Curve0 T} {θ : ℝ → TorusL2}

/-- Each Fourier coordinate is continuous because the integrated weak equation writes it as a
difference of primitives of interval-integrable functions.  No continuity hypothesis is used. -/
theorem coeff_continuousOn (h : IsPaperEnergySolution hα hT hm M N K f θ) (k : Gam) :
    ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0 : ℝ) T) := by
  let P : C(Torus2, ℂ) := modeTest k
  let Q : C(Torus2, ℂ) := fracModeTest α k
  let d : ℝ → ℂ := fun s => spacePair (incl (paperEnergyState θ s)) Q
  let n : ℝ → ℂ := fun s =>
    spacePair (transport m hm (paperEnergyState θ s) (paperEnergyState θ s)) P
  let r : ℝ → ℂ := fun s => spacePair (sourceFun hT.le f s) P
  have hdInt : IntervalIntegrable d (volume : Measure ℝ) 0 T := by
    simpa [d, Q, fracModeTest] using h.dissipation_integrable ({-k} : Finset Gam) (fun _ => 1)
  have hnInt : IntervalIntegrable n (volume : Measure ℝ) 0 T := by
    simpa [n, P, modeTest] using h.transport_integrable ({-k} : Finset Gam) (fun _ => 1)
  have hrInt : IntervalIntegrable r (volume : Measure ℝ) 0 T := by
    exact (continuous_spacePair_source hT.le f P).intervalIntegrable 0 T
  have hdCont : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, d s)
      (Set.Icc (0 : ℝ) T) := by
    simpa [Set.uIcc_of_le hT.le] using
      (intervalIntegral.continuousOn_primitive_interval' hdInt Set.left_mem_uIcc)
  have hnCont : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, n s)
      (Set.Icc (0 : ℝ) T) := by
    simpa [Set.uIcc_of_le hT.le] using
      (intervalIntegral.continuousOn_primitive_interval' hnInt Set.left_mem_uIcc)
  have hrCont : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, r s)
      (Set.Icc (0 : ℝ) T) := by
    simpa [Set.uIcc_of_le hT.le] using
      (intervalIntegral.continuousOn_primitive_interval' hrInt Set.left_mem_uIcc)
  have heq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      l2coeff k (θ t) = (∫ s in (0 : ℝ)..t, r s)
        - (∫ s in (0 : ℝ)..t, d s) - (∫ s in (0 : ℝ)..t, n s) := by
    intro t ht
    have hw := h.weak ({-k} : Finset Gam) (fun _ => 1) t ht
    change l2TrigPair (θ t) {-k} (fun _ => 1)
        + (∫ s in (0 : ℝ)..t, d s) + (∫ s in (0 : ℝ)..t, n s)
          = ∫ s in (0 : ℝ)..t, r s at hw
    rw [l2TrigPair_mode] at hw
    linear_combination hw
  exact ((hrCont.sub hdCont).sub hnCont).congr (fun t ht => heq t ht)

theorem energy3_everywhere (h : IsPaperEnergySolution hα hT hm M N K f θ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M :=
  forall_finset_sum_le_of_ae_on hT h.coeff_continuousOn h.energy3

theorem paperEnergyState_eq_paperState (h : IsPaperEnergySolution hα hT hm M N K f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    paperEnergyState θ t = paperState hT.le h.energy3_everywhere t := by
  have hsum := h3Summable_of_finset_bound (h.energy3_everywhere t ht)
  refine Wiener1.coeff_injective (funext fun k => ?_)
  rw [paperEnergyState_coeff_of_summable hsum, paperState_of_mem hT.le _ ht]

/-- Every continuity-free paper energy solution has the canonical continuous representative
required by the old API. -/
theorem toPaperSolution (h : IsPaperEnergySolution hα hT hm M N K f θ) :
    IsPaperSolution hα hT hm M N K f θ where
  alpha_lt_one := h.alpha_lt_one
  coeff_continuous := h.coeff_continuousOn
  real := h.real
  initial := h.initial
  energy3 := h.energy3_everywhere
  sob3a := h.sob3a
  energy3a := h.energy3a
  lq := h.lq
  weak := by
    intro F c t ht
    have hw := h.weak F c t ht
    have hfirst :
        spacePair (incl (paperState hT.le h.energy3_everywhere t)) (trigPoly F c)
          = l2TrigPair (θ t) F c := by
      rw [spacePair_trigPoly]
      apply Finset.sum_congr rfl
      intro j hj
      rw [incl_apply, paperState_of_mem hT.le _ ht]
    have hstate : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        paperState hT.le h.energy3_everywhere s = paperEnergyState θ s := by
      intro s hs
      rw [Set.uIcc_of_le ht.1] at hs
      exact (h.paperEnergyState_eq_paperState ⟨hs.1, le_trans hs.2 ht.2⟩).symm
    have hdiss :
        (∫ s in (0 : ℝ)..t,
            spacePair (incl (paperState hT.le h.energy3_everywhere s)) (fracLapPoly α F c))
          = ∫ s in (0 : ℝ)..t,
            spacePair (incl (paperEnergyState θ s)) (fracLapPoly α F c) :=
      intervalIntegral.integral_congr (fun s hs => by rw [hstate s hs])
    have htransport :
        (∫ s in (0 : ℝ)..t,
            spacePair (transport m hm (paperState hT.le h.energy3_everywhere s)
              (paperState hT.le h.energy3_everywhere s)) (trigPoly F c))
          = ∫ s in (0 : ℝ)..t,
            spacePair (transport m hm (paperEnergyState θ s) (paperEnergyState θ s))
              (trigPoly F c) :=
      intervalIntegral.integral_congr (fun s hs => by rw [hstate s hs])
    rw [hfirst, hdiss, htransport]
    exact hw

/-- Strong `L2(T^2)` continuity of the selected representative, derived from the weak energy
formulation rather than assumed. -/
theorem continuousOn (h : IsPaperEnergySolution hα hT hm M N K f θ) :
    ContinuousOn θ (Set.Icc (0 : ℝ) T) :=
  h.toPaperSolution.continuousOn'

end IsPaperEnergySolution

/-! ## 3. Equivalence with the former representative-based class -/

namespace IsPaperSolution

variable {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m} {M N K : ℝ}
  {f : Curve0 T} {θ : ℝ → TorusL2}

theorem paperEnergyState_eq_paperState (h : IsPaperSolution hα hT hm M N K f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    paperEnergyState θ t = paperState hT.le h.energy3 t := by
  have hsum := h3Summable_of_finset_bound (h.energy3 t ht)
  refine Wiener1.coeff_injective (funext fun k => ?_)
  rw [paperEnergyState_coeff_of_summable hsum, paperState_of_mem hT.le _ ht]

theorem paperEnergyState_eq_curveState (h : IsPaperSolution hα hT hm M N K f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    paperEnergyState θ t = curveState hT.le h.isSobolevSolution.curve t := by
  rw [h.paperEnergyState_eq_paperState ht]
  refine Wiener1.coeff_injective (funext fun k => ?_)
  rw [paperState_of_mem hT.le _ ht, h.isSobolevSolution.curveState_eq ht, sobState_coeff,
    sobClamp_of_mem hT.le θ ht]

/-- The former class satisfies the continuity-free energy formulation.  Its integrability
fields follow from the continuous `Curve1` representative already proved from its bounds. -/
theorem toPaperEnergySolution (h : IsPaperSolution hα hT hm M N K f θ) :
    IsPaperEnergySolution hα hT hm M N K f θ where
  alpha_lt_one := h.alpha_lt_one
  real := h.real
  initial := h.initial
  energy3 := h.energy3_ae
  sob3a := h.sob3a
  energy3a := h.energy3a
  lq := h.lq
  dissipation_integrable := by
    intro F c
    have hi : IntervalIntegrable
        (fun s : ℝ => spacePair (incl (curveState hT.le h.isSobolevSolution.curve s))
          (fracLapPoly α F c)) (volume : Measure ℝ) 0 T :=
      (continuous_spacePair_curveState hT.le h.isSobolevSolution.curve
        (fracLapPoly α F c)).intervalIntegrable 0 T
    refine hi.congr ?_
    intro s hs
    rw [Set.uIoc_of_le hT.le] at hs
    change spacePair (incl (curveState hT.le h.isSobolevSolution.curve s))
      (fracLapPoly α F c) = spacePair (incl (paperEnergyState θ s)) (fracLapPoly α F c)
    rw [← h.paperEnergyState_eq_curveState ⟨hs.1.le, hs.2⟩]
  transport_integrable := by
    intro F c
    have hi : IntervalIntegrable
        (fun s : ℝ => spacePair (quadCurve hm (curveState hT.le h.isSobolevSolution.curve) s)
          (trigPoly F c)) (volume : Measure ℝ) 0 T :=
      (continuous_spacePair_quadCurve hT.le hm h.isSobolevSolution.curve
        (trigPoly F c)).intervalIntegrable 0 T
    refine hi.congr ?_
    intro s hs
    rw [Set.uIoc_of_le hT.le] at hs
    change spacePair (transport m hm (curveState hT.le h.isSobolevSolution.curve s)
      (curveState hT.le h.isSobolevSolution.curve s)) (trigPoly F c) = _
    rw [← h.paperEnergyState_eq_curveState ⟨hs.1.le, hs.2⟩]
  weak := by
    intro F c t ht
    have hw := h.weak F c t ht
    have hfirst :
        spacePair (incl (paperState hT.le h.energy3 t)) (trigPoly F c)
          = l2TrigPair (θ t) F c := by
      rw [spacePair_trigPoly]
      apply Finset.sum_congr rfl
      intro j hj
      rw [incl_apply, paperState_of_mem hT.le _ ht]
    have hstate : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        paperState hT.le h.energy3 s = paperEnergyState θ s := by
      intro s hs
      rw [Set.uIcc_of_le ht.1] at hs
      exact (h.paperEnergyState_eq_paperState ⟨hs.1, le_trans hs.2 ht.2⟩).symm
    have hdiss :
        (∫ s in (0 : ℝ)..t,
            spacePair (incl (paperState hT.le h.energy3 s)) (fracLapPoly α F c))
          = ∫ s in (0 : ℝ)..t,
            spacePair (incl (paperEnergyState θ s)) (fracLapPoly α F c) :=
      intervalIntegral.integral_congr (fun s hs => by rw [hstate s hs])
    have htransport :
        (∫ s in (0 : ℝ)..t,
            spacePair (transport m hm (paperState hT.le h.energy3 s)
              (paperState hT.le h.energy3 s)) (trigPoly F c))
          = ∫ s in (0 : ℝ)..t,
            spacePair (transport m hm (paperEnergyState θ s) (paperEnergyState θ s))
              (trigPoly F c) :=
      intervalIntegral.integral_congr (fun s hs => by rw [hstate s hs])
    rw [hfirst, hdiss, htransport] at hw
    exact hw

end IsPaperSolution

/-- **The continuity-free and continuous-representative formulations are equivalent.**
Continuity is therefore a consequence of the integrated weak evolution, not an additional
forward-class assumption. -/
theorem isPaperEnergySolution_iff_isPaperSolution
    {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m} {M N K : ℝ}
    {f : Curve0 T} {θ : ℝ → TorusL2} :
    IsPaperEnergySolution hα hT hm M N K f θ ↔
      IsPaperSolution hα hT hm M N K f θ :=
  ⟨IsPaperEnergySolution.toPaperSolution, IsPaperSolution.toPaperEnergySolution⟩

/-- The constructed small-source state inhabits the continuity-free paper class. -/
theorem isPaperEnergySolution_mild {hα : 1 / 2 < α} {hm : IsBddSymbol m}
    {hr : IsRealSymbol m} (hα1 : α < 1) (hT : 0 < T) {f : Curve0 T}
    {u : Curve1 T} {R4 : ℝ}
    (hmild : u + sourceQuad hα hT.le m hm hr u u = duhamelOp hα hT.le f)
    (h4 : ∀ t ∈ Set.Icc (0 : ℝ) T, WB 4 R4 (curveState hT.le u t).coeff) :
    IsPaperEnergySolution hα hT hm (R4 ^ 2) (T * R4 ^ 2) ‖u‖ f
      (mildPhysState hT.le u) :=
  (isPaperSolution_mild hα1 hT hmild h4).toPaperEnergySolution

end LiWang.WienerModel
