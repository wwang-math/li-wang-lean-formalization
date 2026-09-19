/-
# The paper's physical exterior test fields

Theorem 1.1 of Li--Wang is quantified over real smooth test fields compactly supported in
`W^e = T^2 \ closure W`.  Earlier endpoints used the Fourier-coefficient carrier
`RealWiener`.  This file proves the exact bridge from the paper-facing physical lift to that
carrier and removes all coefficient-space objects from the final theorem's test-field input.
-/
import LiWangWiener.PaperFullEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ}

/-- A real smooth periodic lift whose torus support is compactly contained in the exterior of
`W`.  This is the lift-level rendering of `g ∈ C_c^∞(W^e)` used in Theorem 1.1. -/
structure IsPaperExteriorField (W : Set Torus2) (G : ℝ × ℝ → ℂ) : Prop where
  smoothPeriodic : IsSmoothPeriodic G
  real : ∀ p, conj (G p) = G p
  support : ∃ K : Set Torus2, IsCompact K ∧ K ⊆ (closure W)ᶜ ∧
    ∀ y : Fin 2 → ℝ, torusProj y ∉ K → G (y 0, y 1) = 0

/-- The real Wiener carrier canonically reconstructed from a paper exterior field. -/
noncomputable def paperExteriorWiener {W : Set Torus2} {G : ℝ × ℝ → ℂ}
    (hG : IsPaperExteriorField W G) : RealWiener :=
  realWienerOfSmooth G hG.smoothPeriodic hG.real

/-- The descended physical torus field.  Its lift is proved below to be exactly `G`. -/
noncomputable def paperExteriorTorusField {W : Set Torus2} {G : ℝ × ℝ → ℂ}
    (hG : IsPaperExteriorField W G) : C(Torus2, ℂ) :=
  synth (paperExteriorWiener hG).val

@[simp] theorem paperExteriorWiener_val {W : Set Torus2} {G : ℝ × ℝ → ℂ}
    (hG : IsPaperExteriorField W G) :
    (paperExteriorWiener hG).val = wienerOfSmooth G hG.smoothPeriodic := rfl

/-- Exact physical reconstruction: the lift of the descended torus field is the supplied
smooth periodic field, pointwise rather than merely almost everywhere. -/
theorem paperExteriorTorusField_torusProj {W : Set Torus2} {G : ℝ × ℝ → ℂ}
    (hG : IsPaperExteriorField W G) (y : Fin 2 → ℝ) :
    paperExteriorTorusField hG (torusProj y) = G (y 0, y 1) := by
  change lift (wienerOfSmooth G hG.smoothPeriodic) y = G (y 0, y 1)
  exact lift_wienerOfSmooth hG.smoothPeriodic y

/-- The reconstructed Fourier carrier is smooth in the packet's sense. -/
theorem smoothWiener_paperExteriorWiener {W : Set Torus2} {G : ℝ × ℝ → ℂ}
    (hG : IsPaperExteriorField W G) : SmoothWiener (paperExteriorWiener hG).val := by
  change SmoothWiener (wienerOfSmooth G hG.smoothPeriodic)
  exact smoothWiener_wienerOfSmooth hG.smoothPeriodic

/-- Compact exterior support implies vanishing on the closed observation region. -/
theorem paperExteriorTorusField_zero_on_closure {W : Set Torus2} {G : ℝ × ℝ → ℂ}
    (hG : IsPaperExteriorField W G) :
    ∀ x ∈ closure W, paperExteriorTorusField hG x = 0 := by
  rintro x hx
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  obtain ⟨K, -, hK, hvanish⟩ := hG.support
  rw [paperExteriorTorusField_torusProj hG]
  apply hvanish
  intro hyK
  exact (hK hyK) hx

/-- The `A^1` profile used internally by the inverse argument synthesizes to the supplied
physical test field exactly. -/
theorem synth_exteriorProfile_paperExteriorWiener {W : Set Torus2} {G : ℝ × ℝ → ℂ}
    (hG : IsPaperExteriorField W G) :
    synth (incl (exteriorProfile (smoothWiener_paperExteriorWiener hG))) =
      paperExteriorTorusField hG := by
  ext x
  rw [synth_exteriorProfile]
  rfl

/-- Paper exterior fields are non-vacuous whenever the exterior is nonempty.  More precisely,
one can choose a real smooth periodic field compactly supported in `W^e` whose descended torus
field takes the value one at a prescribed exterior point. -/
theorem exists_paperExteriorField_at {W : Set Torus2} {w : Torus2}
    (hw : w ∈ (closure W)ᶜ) :
    ∃ (G : ℝ × ℝ → ℂ) (hG : IsPaperExteriorField W G),
      paperExteriorTorusField hG w = 1 := by
  have hWe : IsOpen ((closure W)ᶜ) := isClosed_closure.isOpen_compl
  obtain ⟨a, K, hsm, hKc, hKWe, hvanish, -, hone⟩ :=
    exists_smooth_bump_at hWe hw
  let G : ℝ × ℝ → ℂ := planeLift a.val
  have hGsm : IsSmoothPeriodic G := isSmoothPeriodic_planeLift hsm
  have hGreal : ∀ p, conj (G p) = G p := by
    intro p
    change conj (synth a.val (torusProj ![p.1, p.2])) =
      synth a.val (torusProj ![p.1, p.2])
    exact conj_synth_apply a.conjSymmetric _
  have hGsupport : ∃ K : Set Torus2, IsCompact K ∧ K ⊆ (closure W)ᶜ ∧
      ∀ y : Fin 2 → ℝ, torusProj y ∉ K → G (y 0, y 1) = 0 := by
    refine ⟨K, hKc, hKWe, ?_⟩
    intro y hy
    change synth a.val (torusProj ![y 0, y 1]) = 0
    rw [vecPair_eq]
    exact hvanish _ hy
  let hG : IsPaperExteriorField W G := ⟨hGsm, hGreal, hGsupport⟩
  refine ⟨G, hG, ?_⟩
  obtain ⟨y, rfl⟩ := torusProj_surjective w
  rw [paperExteriorTorusField_torusProj]
  change synth a.val (torusProj ![y 0, y 1]) = 1
  rw [vecPair_eq]
  exact hone

/-- In particular, every nonempty exterior admits a nonzero paper test field. -/
theorem exists_nonzero_paperExteriorField {W : Set Torus2}
    (hne : ((closure W)ᶜ).Nonempty) :
    ∃ (G : ℝ × ℝ → ℂ) (hG : IsPaperExteriorField W G),
      paperExteriorTorusField hG ≠ 0 := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨G, hG, hone⟩ := exists_paperExteriorField_at hw
  refine ⟨G, hG, ?_⟩
  intro hzero
  have hzero' : paperExteriorTorusField hG w = 0 := by rw [hzero]; rfl
  rw [hone] at hzero'
  exact one_ne_zero hzero'

/-- **Theorem 1.1 with a physical `C_c^∞(W^e)` test field.**  No Wiener carrier appears in the
input or conclusion. -/
theorem paper_physical_exterior_velocity_eq_of_paperMapsAgree
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
    (hexP₁ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (paperSources hT W) ε)
    (hexP₂ : PaperExistence hα hT (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩)
      (paperSources hT W) ε)
    (hagree : PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
      (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε hexP₁ hexP₂)
    {G : ℝ × ℝ → ℂ} (hG : IsPaperExteriorField W G)
    {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    deriv (fun s : ℝ => torusConv K₁ (paperExteriorTorusField hG) (torusShift x 1 s)) 0
        = deriv (fun s : ℝ => torusConv K₂ (paperExteriorTorusField hG) (torusShift x 1 s)) 0
      ∧ deriv (fun s : ℝ => torusConv K₁ (paperExteriorTorusField hG) (torusShift x 0 s)) 0
        = deriv (fun s : ℝ => torusConv K₂ (paperExteriorTorusField hG) (torusShift x 0 s)) 0
      ∧ ∀ k : Gam, k ≠ 0 → kernelCoeff K₁ k = kernelCoeff K₂ k := by
  let ha : SmoothWiener (paperExteriorWiener hG).val :=
    smoothWiener_paperExteriorWiener hG
  have hsupp : ∀ y ∈ closure W, synth (paperExteriorWiener hG).val y = 0 :=
    paperExteriorTorusField_zero_on_closure hG
  have hresult := paper_exterior_velocity_eq_of_paperMapsAgree_full hα hT hW hUCP
    hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂ hτ0 hτT hε hexP₁ hexP₂ hagree ha hsupp hx
  have hfield : synth (incl (exteriorProfile ha)) = paperExteriorTorusField hG := by
    simpa only using synth_exteriorProfile_paperExteriorWiener hG
  rw [hfield] at hresult
  exact ⟨hresult.2.2.1, hresult.2.2.2.1, hresult.2.2.2.2⟩

/-- The physical endpoint with common-radius forward existence discharged. -/
theorem exists_radius_paper_physical_endpoint
    (hα : 1 / 2 < α) (hα1 : α < 1) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Torus2 → ℂ}
    (hK₁ : Integrable K₁ (volume : Measure Torus2))
    (hK₂ : Integrable K₂ (volume : Measure Torus2))
    {A₁ A₂ : ℝ} (hA₁ : KernelBound (kernelCoeff K₁) A₁)
    (hA₂ : KernelBound (kernelCoeff K₂) A₂)
    (hcs₁ : ConjSymmetric (kernelCoeff K₁)) (hcs₂ : ConjSymmetric (kernelCoeff K₂))
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    ∃ ε > 0, ∃ (hexP₁ : PaperExistence hα hT
          (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩) (paperSources hT W) ε)
        (hexP₂ : PaperExistence hα hT
          (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε),
      PaperObsMapsAgree hα hT W (rotatedGradientSymbol_bdd ⟨A₁, hA₁⟩)
          (rotatedGradientSymbol_bdd ⟨A₂, hA₂⟩) (paperSources hT W) ε hexP₁ hexP₂ →
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
  obtain ⟨ε, hε, hex₁, hex₂⟩ := exists_paperExistence_pair hα hα1 hT
    (rotatedGradientSymbol_bdd (κ := kernelCoeff K₁) ⟨A₁, hA₁⟩)
    (rotatedGradientSymbol_isRealSymbol hcs₁)
    (Classical.choose_spec (rotatedGradientSymbol_bdd (κ := kernelCoeff K₁) ⟨A₁, hA₁⟩))
    (rotatedGradientSymbol_bdd (κ := kernelCoeff K₂) ⟨A₂, hA₂⟩)
    (rotatedGradientSymbol_isRealSymbol hcs₂)
    (Classical.choose_spec (rotatedGradientSymbol_bdd (κ := kernelCoeff K₂) ⟨A₂, hA₂⟩)) W
  refine ⟨ε, hε, hex₁, hex₂, ?_⟩
  intro hagree G hG x hx
  exact paper_physical_exterior_velocity_eq_of_paperMapsAgree hα hT hW hUCP
    hK₁ hK₂ hA₁ hA₂ hcs₁ hcs₂ hτ0 hτT hε hex₁ hex₂ hagree hG hx

end LiWang.WienerModel
