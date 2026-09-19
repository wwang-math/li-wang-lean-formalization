/-
# The paper-shaped endpoint

The statement Li–Wang prove (Theorem 1.1) compares the two **source-to-solution maps** (1.6)
and concludes that the two velocity operators agree on the exterior region
`Wᵉ = 𝕋² ∖ closure W`.  This module states and proves that shape, with:

* the paper's kernels: `K ∈ L¹(𝕋²)`, real, with a Fourier decay bound.  Stated exactly: the
  main theorem assumes only `wt k ‖K̂(k)‖ ≤ A` (the packet's `KernelBound`, which is what the
  paper's *upper* bound `|K̂(k)| ≤ D|k|^{-1}` gives) together with `ConjSymmetric K̂`.  A
  corollary specializes to the packet's `OrderedFourierEllipticity` — an **ordered,
  sign-definite** condition on `Re K̂`, strictly stronger than the paper's two-sided magnitude
  bound (the packet proves the strictness).  The lower ellipticity bound is *not used*: it is
  needed for the paper's own well-posedness theory, not for this implication;
* the paper's measurement datum: equality of the two canonical paper observation maps on a ball
  of smooth sources compactly supported in `W × (0,T)`;
* the portable analytic input `FractionalUCP α W`, carried as a parameter;
* the paper's test object: a smooth real profile, entered into the `A¹` carrier through its own
  Fourier coefficients (`exteriorProfile`), with the support and physical-synthesis
  correspondence proved.  Stated exactly: the exterior-support hypothesis yields the first
  conclusion (that the test really is supported in the exterior) and nothing else — the velocity
  equality holds for *every* `A¹` test, because it is derived from equality of the full
  symbols;
* the conclusion stated on the **genuine torus convolution**: the two components of
  `∇^⊥(K * ψ)` — actual derivatives of `torusConv K (synth (incl ψ))` — agree at every exterior
  point, and the kernels themselves agree off the zero mode.

Nothing about kernel recovery, Runge approximation or UCP is redone: the v6.0/v7.0/v8.0
theorems are invoked.

Part of `LiWangFormalizationPaperMapAlignmentPacket` v9.0.
-/
import LiWangFormalization.PaperAlignment

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ}

/-! ## 1. The exterior test profile as an `A¹` element -/

/-- **The `A¹` element of a smooth real profile**, built from its own Fourier coefficients. -/
noncomputable def exteriorProfile {a : RealWiener} (ha : SmoothWiener a.val) : Wiener1 :=
  wiener1OfSmooth (planeLift a.val) (isSmoothPeriodic_planeLift ha)

/-- Its inclusion into the Wiener algebra is the original profile: the round trip is exact. -/
theorem incl_exteriorProfile {a : RealWiener} (ha : SmoothWiener a.val) :
    incl (exteriorProfile ha) = a.val := by
  rw [exteriorProfile, incl_wiener1OfSmooth]
  exact planeLift_injective (planeLift_wienerOfSmooth _)

/-- **Physical-synthesis correspondence**: the synthesized field of the `A¹` element is the
original physical profile. -/
theorem synth_exteriorProfile {a : RealWiener} (ha : SmoothWiener a.val) (x : Torus2) :
    synth (incl (exteriorProfile ha)) x = synth a.val x := by rw [incl_exteriorProfile]

/-- **Support correspondence**: the `A¹` element is supported where the profile is. -/
theorem exteriorProfile_vanishes {a : RealWiener} (ha : SmoothWiener a.val) {S : Set Torus2}
    (hS : ∀ y ∈ S, synth a.val y = 0) : ∀ y ∈ S, synth (incl (exteriorProfile ha)) y = 0 :=
  fun y hy => by rw [synth_exteriorProfile ha y]; exact hS y hy

theorem coeff_exteriorProfile {a : RealWiener} (ha : SmoothWiener a.val) (k : Gam) :
    (exteriorProfile ha).coeff k = a.val k := by
  have h := incl_exteriorProfile ha
  calc (exteriorProfile ha).coeff k = (incl (exteriorProfile ha)) k := rfl
    _ = a.val k := by rw [h]

/-! ## 2. The endpoint -/

/-- **The paper-shaped conclusion from equality of the canonical paper observation maps.**

Hypotheses: `1/2 < α`, `T > 0`, `W` open with nonempty exterior (supplied by the exterior
point), the two kernels integrable and real with the weighted Fourier decay bound, the portable
fractional UCP input, and equality of the two canonical paper source-to-solution maps on a small
ball of smooth sources.

Conclusion: the exterior support and synthesis correspondence of the test profile; equality of
both components of the genuine convolution velocity `∇^⊥(K * ψ)` at the exterior point; and
equality of the two kernels off the zero mode. -/
theorem paper_exterior_velocity_eq_of_paperMapsAgree
    (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁) (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    {ε : ℝ} (hε : 0 < ε)
    (hex₁ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩) (smoothSources hT W) ε)
    (hex₂ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (smoothSources hT W) ε)
    (hagree : PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (smoothSources hT W) ε hex₁ hex₂)
    {a : RealWiener} (ha : SmoothWiener a.val)
    (hsupp : ∀ y ∈ closure W, synth a.val y = 0)
    {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    (∀ y ∈ closure W, synth (incl (exteriorProfile ha)) y = 0)
      ∧ (∀ y : Torus2, synth (incl (exteriorProfile ha)) y = synth a.val y)
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
      ∧ ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k := by
  classical
  have hm₁ : IsBddSymbol (rotatedGradientSymbol (kernelCoeff K₁)) :=
    rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩
  have hm₂ : IsBddSymbol (rotatedGradientSymbol (kernelCoeff K₂)) :=
    rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩
  have hr₁ : IsRealSymbol (rotatedGradientSymbol (kernelCoeff K₁)) :=
    rotatedGradientSymbol_isRealSymbol hcs₁
  have hr₂ : IsRealSymbol (rotatedGradientSymbol (kernelCoeff K₂)) :=
    rotatedGradientSymbol_isRealSymbol hcs₂
  obtain ⟨C₁, hC₁⟩ := id hm₁
  obtain ⟨C₂, hC₂⟩ := id hm₂
  obtain ⟨C, hC⟩ := hm₁.sub hm₂
  have hsob : ∃ ε' > 0,
      SobolevObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε' :=
    exists_sobolevObsAgreeOn_of_paperMapsAgree hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hε hex₁ hex₂ hagree
  have hmm : ∃ ε' > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε' :=
    exists_measuredMapsAgreeOn_of_sobolev hα hT hW hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ (smoothSources hT W)
      (exists_sobolevExistence_smoothSources hα hT hm₁ hr₁ hC₁ W)
      (exists_sobolevExistence_smoothSources hα hT hm₂ hr₂ hC₂ W) hsob
  have hveq : ∀ j : Fin 2,
      synth (velocity (rotatedGradientSymbol (kernelCoeff K₁)) hm₁ j
          (incl (exteriorProfile ha))) x
        = synth (velocity (rotatedGradientSymbol (kernelCoeff K₂)) hm₂ j
          (incl (exteriorProfile ha))) x := fun j =>
    paper_exterior_velocity_eq_sobolev hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hC hτ0 hτT
      (exists_sobolevExistence_smoothSources hα hT hm₁ hr₁ hC₁ W)
      (exists_sobolevExistence_smoothSources hα hT hm₂ hr₂ hC₂ W) hsob
      (exteriorProfile ha) j hx
  have e10 := velocity_integrableKernel_zero hK₁ hA₁ (exteriorProfile ha) x
  have e20 := velocity_integrableKernel_zero hK₂ hA₂ (exteriorProfile ha) x
  have e11 := velocity_integrableKernel_one hK₁ hA₁ (exteriorProfile ha) x
  have e21 := velocity_integrableKernel_one hK₂ hA₂ (exteriorProfile ha) x
  refine ⟨exteriorProfile_vanishes ha hsupp, synth_exteriorProfile ha, ?_, ?_, ?_⟩
  · have hneg : -(deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0)
        = -(deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0) := by
      rw [← e10, ← e20]
      exact hveq 0
    exact neg_inj.1 hneg
  · rw [← e11, ← e21]
    exact hveq 1
  · intro k hk
    exact kernel_diff_eq_zero hα hT hW ⟨x, hx⟩ hUCP _ hr₁ _ hr₂ hC hτ0 hτT hmm hk

/-- **The same conclusion for the packet's paper-kernel class.**  `OrderedFourierEllipticity` is
the packet's ordered, sign-definite rendering of the paper's two-sided Fourier bound; only its
upper half is used here, through `orderedEllipticity_admissible`. -/
theorem paper_exterior_velocity_eq_of_paperMapsAgree_elliptic
    (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {c₁ D₁ c₂ D₂ : ℝ}
    (hell₁ : OrderedFourierEllipticity (kernelCoeff K₁) c₁ D₁)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁))
    (hell₂ : OrderedFourierEllipticity (kernelCoeff K₂) c₂ D₂)
    (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    {ε : ℝ} (hε : 0 < ε)
    (hex₁ : PaperExistence hα hT
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁)) (smoothSources hT W) ε)
    (hex₂ : PaperExistence hα hT
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂)) (smoothSources hT W) ε)
    (hagree : PaperObsMapsAgree hα hT W
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁))
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂))
      (smoothSources hT W) ε hex₁ hex₂)
    {a : RealWiener} (ha : SmoothWiener a.val)
    (hsupp : ∀ y ∈ closure W, synth a.val y = 0)
    {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    (∀ y ∈ closure W, synth (incl (exteriorProfile ha)) y = 0)
      ∧ (∀ y : Torus2, synth (incl (exteriorProfile ha)) y = synth a.val y)
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 1 s)) 0
      ∧ deriv (fun s : ℝ =>
          torusConv K₁ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
        = deriv (fun s : ℝ =>
          torusConv K₂ (synth (incl (exteriorProfile ha))) (torusShift x 0 s)) 0
      ∧ ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k := by
  obtain ⟨A₁, hA₁⟩ := orderedEllipticity_admissible hell₁
  obtain ⟨A₂, hA₂⟩ := orderedEllipticity_admissible hell₂
  exact paper_exterior_velocity_eq_of_paperMapsAgree hα hT hW hUCP hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂
    hτ0 hτT hε hex₁ hex₂ hagree ha hsupp hx

end LiWang.Formalization
