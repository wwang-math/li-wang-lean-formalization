/-
# Exact paper-facing endpoint

This module combines the two v11 bridges:

* forward solutions are supplied through `IsPaperEnergySolution`, which has no time-continuity
  assumption and from which continuity is proved;
* exterior tests are supplied as physical real smooth periodic fields compactly supported in
  `W^e`, not as Fourier coefficient carriers.

The older canonical map is reused only after the proved equivalence of solution classes.
-/
import LiWangFormalization.PaperEnergyRepresentative
import LiWangFormalization.PaperExteriorField

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-- Existence in the continuity-free paper energy class on a small source ball. -/
def PaperEnergyExistence (hα : 1 / 2 < α) (hT : 0 < T) (hm : IsBddSymbol m)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) : Prop :=
  ∀ f ∈ A, ‖f‖ < ε →
    ∃ p : (ℝ → TorusL2) × ℝ × ℝ × ℝ,
      IsPaperEnergySolution hα hT hm p.2.1 p.2.2.1 p.2.2.2 f p.1

/-- Energy-class existence gives the former representative-based existence by the proved
representative theorem. -/
def PaperEnergyExistence.toPaperExistence
    {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m}
    {A : Submodule ℝ (Curve0 T)} {ε : ℝ}
    (hex : PaperEnergyExistence hα hT hm A ε) : PaperExistence hα hT hm A ε := by
  intro f hf hs
  obtain ⟨p, hp⟩ := hex f hf hs
  exact ⟨p, hp.toPaperSolution⟩

/-- The former existence package gives energy-class existence without adding hypotheses. -/
def PaperExistence.toEnergyExistence
    {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m}
    {A : Submodule ℝ (Curve0 T)} {ε : ℝ}
    (hex : PaperExistence hα hT hm A ε) : PaperEnergyExistence hα hT hm A ε := by
  intro f hf hs
  obtain ⟨p, hp⟩ := hex f hf hs
  exact ⟨p, hp.toPaperEnergySolution⟩

/-- Equality of the canonical source-to-solution maps, now parameterized by existence in the
continuity-free energy class.  The selected observations are the former canonical observations
after applying the proved class equivalence. -/
def PaperEnergyObsMapsAgree (hα : 1 / 2 < α) (hT : 0 < T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ)
    (hex₁ : PaperEnergyExistence hα hT hm₁ A ε)
    (hex₂ : PaperEnergyExistence hα hT hm₂ A ε) : Prop :=
  PaperObsMapsAgree hα hT W hm₁ hm₂ A ε hex₁.toPaperExistence hex₂.toPaperExistence

/-- **Exact paper-facing inverse endpoint.**  The forward class contains no continuity
assumption, and the test field is an actual physical `C_c^∞(W^e)` field. -/
theorem paper_exact_endpoint_from_energy_maps
    (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁)
    (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    {ε : ℝ} (hε : 0 < ε)
    (hexE₁ : PaperEnergyExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (paperSources hT W) ε)
    (hexE₂ : PaperEnergyExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩)
      (paperSources hT W) ε)
    (hagree : PaperEnergyObsMapsAgree hα hT W
      (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩)
      (paperSources hT W) ε hexE₁ hexE₂)
    {G : ℝ × ℝ → ℂ} (hG : IsPaperExteriorField W G)
    {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    deriv (fun s : ℝ => torusConv K₁ (paperExteriorTorusField hG) (torusShift x 1 s)) 0
        = deriv (fun s : ℝ => torusConv K₂ (paperExteriorTorusField hG) (torusShift x 1 s)) 0
      ∧ deriv (fun s : ℝ => torusConv K₁ (paperExteriorTorusField hG) (torusShift x 0 s)) 0
        = deriv (fun s : ℝ => torusConv K₂ (paperExteriorTorusField hG) (torusShift x 0 s)) 0
      ∧ ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k := by
  exact paper_physical_exterior_velocity_eq_of_paperMapsAgree hα hT hW hUCP
    hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂ hτ0 hτT hε
    hexE₁.toPaperExistence hexE₂.toPaperExistence hagree hG hx

/-- The exact endpoint with forward existence discharged on one common positive radius. -/
theorem exists_radius_paper_exact_endpoint
    (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁)
    (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    ∃ ε > 0, ∃
      (hexE₁ : PaperEnergyExistence hα hT
        (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩) (paperSources hT W) ε)
      (hexE₂ : PaperEnergyExistence hα hT
        (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε),
      PaperEnergyObsMapsAgree hα hT W
          (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
          (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩)
          (paperSources hT W) ε hexE₁ hexE₂ →
        ∀ {G : ℝ × ℝ → ℂ}, (hG : IsPaperExteriorField W G) →
          ∀ {x : Torus2}, x ∈ (closure W)ᶜ →
            deriv (fun s : ℝ => torusConv K₁ (paperExteriorTorusField hG)
                (torusShift x 1 s)) 0
              = deriv (fun s : ℝ => torusConv K₂ (paperExteriorTorusField hG)
                (torusShift x 1 s)) 0
            ∧ deriv (fun s : ℝ => torusConv K₁ (paperExteriorTorusField hG)
                (torusShift x 0 s)) 0
              = deriv (fun s : ℝ => torusConv K₂ (paperExteriorTorusField hG)
                (torusShift x 0 s)) 0
            ∧ ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k := by
  obtain ⟨ε, hε, hexP₁, hexP₂⟩ := exists_paperExistence_pair hα hα1 hT
    (rotatedGradientSymbol_bdd (κ := kernelCoeff K₁) ⟨A₁, hA₁⟩)
    (rotatedGradientSymbol_isRealSymbol hcs₁)
    (Classical.choose_spec (rotatedGradientSymbol_bdd (κ := kernelCoeff K₁) ⟨A₁, hA₁⟩))
    (rotatedGradientSymbol_bdd (κ := kernelCoeff K₂) ⟨A₂, hA₂⟩)
    (rotatedGradientSymbol_isRealSymbol hcs₂)
    (Classical.choose_spec (rotatedGradientSymbol_bdd (κ := kernelCoeff K₂) ⟨A₂, hA₂⟩)) W
  let hexE₁ := hexP₁.toEnergyExistence
  let hexE₂ := hexP₂.toEnergyExistence
  refine ⟨ε, hε, hexE₁, hexE₂, ?_⟩
  intro hagree G hG x hx
  exact paper_exact_endpoint_from_energy_maps hα hT hW hUCP hK₁ hK₂ hA₁ hA₂
    hcs₁ hcs₂ hτ0 hτT hε hexE₁ hexE₂ hagree hG hx

end LiWang.Formalization
