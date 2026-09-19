/-
# The endpoint from the paper's own source-to-solution map

v9.0 proved the exterior identity from equality of the canonical paper maps on the packet's
smooth source family.  With the realization of `PaperSourceRealization` and the source class of
`PaperSourceClass`, the hypothesis can now be stated on **all** of `C_c^∞(W × (0,T))`:
`paperSources hT W` is exactly the class of source curves whose physical space-time field is
such a datum, every such datum is realized, and the packet's smooth sources form a subclass.

`paper_exterior_velocity_eq_of_paperMapsAgree_full` takes the measurement hypothesis on that
full class; `exists_radius_paper_endpoint` additionally discharges the existence hypotheses, so
the only remaining inputs are the portable `FractionalUCP α W` and the measurement datum itself.

Part of `LiWangFormalizationPaperSourceRealizationPacket` v10.0.
-/
import LiWangFormalization.PaperSourceClass
import LiWangFormalization.PaperEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ContDiff
open MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ}

/-- **The paper-shaped conclusion from equality of the source-to-solution maps (1.6) on the full
class `C_c^∞(W × (0,T))`.** -/
theorem paper_exterior_velocity_eq_of_paperMapsAgree_full
    (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁) (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    {ε : ℝ} (hε : 0 < ε)
    (hexP₁ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩) (paperSources hT W) ε)
    (hexP₂ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε)
    (hagree : PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε hexP₁ hexP₂)
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
  have hr₁ : IsRealSymbol (rotatedGradientSymbol (kernelCoeff K₁)) :=
    rotatedGradientSymbol_isRealSymbol hcs₁
  have hr₂ : IsRealSymbol (rotatedGradientSymbol (kernelCoeff K₂)) :=
    rotatedGradientSymbol_isRealSymbol hcs₂
  obtain ⟨C₁, hC₁⟩ := rotatedGradientSymbol_bdd (κ := kernelCoeff K₁) ⟨A₁, hA₁⟩
  obtain ⟨C₂, hC₂⟩ := rotatedGradientSymbol_bdd (κ := kernelCoeff K₂) ⟨A₂, hA₂⟩
  have hle : smoothSources hT W ≤ paperSources hT W := smoothSources_le_paperSources hT W
  have hexS₁ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (smoothSources hT W) ε := fun f hf hs => hexP₁ f (hle hf) hs
  have hexS₂ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩)
      (smoothSources hT W) ε := fun f hf hs => hexP₂ f (hle hf) hs
  have hagreeS : PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (smoothSources hT W) ε hexS₁ hexS₂ :=
    paperObsMapsAgree_mono hr₁ hC₁ hr₂ hC₂ hle hexS₁ hexP₁ hexS₂ hexP₂ hagree
  exact paper_exterior_velocity_eq_of_paperMapsAgree hα hT hW hUCP hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂
    hτ0 hτT hε hexS₁ hexS₂ hagreeS ha hsupp hx

/-- **The same, with the existence hypotheses discharged.**  There is a positive radius on which
paper solutions exist for both kernels on the full source class, and on which equality of the
two source-to-solution maps yields the paper's exterior identity.  The remaining inputs are the
portable `FractionalUCP α W` and the measurement datum. -/
theorem exists_radius_paper_endpoint
    (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁) (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    ∃ ε > 0, ∃ (hexP₁ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
        (paperSources hT W) ε)
      (hexP₂ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩)
        (paperSources hT W) ε),
      PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
          (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε hexP₁ hexP₂ →
        ∀ {a : RealWiener} (ha : SmoothWiener a.val),
          (∀ y ∈ closure W, synth a.val y = 0) →
          ∀ {x : Torus2}, x ∈ (closure W)ᶜ →
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
  have hr₁ : IsRealSymbol (rotatedGradientSymbol (kernelCoeff K₁)) :=
    rotatedGradientSymbol_isRealSymbol hcs₁
  have hr₂ : IsRealSymbol (rotatedGradientSymbol (kernelCoeff K₂)) :=
    rotatedGradientSymbol_isRealSymbol hcs₂
  obtain ⟨C₁, hC₁⟩ := rotatedGradientSymbol_bdd (κ := kernelCoeff K₁) ⟨A₁, hA₁⟩
  obtain ⟨C₂, hC₂⟩ := rotatedGradientSymbol_bdd (κ := kernelCoeff K₂) ⟨A₂, hA₂⟩
  obtain ⟨ε, hε, hex₁, hex₂⟩ := exists_paperExistence_pair hα hα1 hT
    (rotatedGradientSymbol_bdd (κ := kernelCoeff K₁) ⟨A₁, hA₁⟩) hr₁ hC₁
    (rotatedGradientSymbol_bdd (κ := kernelCoeff K₂) ⟨A₂, hA₂⟩) hr₂ hC₂ W
  exact ⟨ε, hε, hex₁, hex₂, fun hagree a ha hsupp x hx =>
    paper_exterior_velocity_eq_of_paperMapsAgree_full hα hT hW hUCP hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂
      hτ0 hτT hε hex₁ hex₂ hagree ha hsupp hx⟩

end LiWang.Formalization
