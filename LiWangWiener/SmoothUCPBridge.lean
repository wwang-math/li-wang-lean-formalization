/-
# Correct measurement quantifiers: the UCP bridge over an admissible source submodule

The v4.0 predicate `MeasuredMapsAgree` quantified over **every** localized `Curve0 T` source of
small norm, while the paper's measurement hypothesis concerns **smooth compactly supported**
sources.  That quantifier mismatch is repaired here: the ray-limit / polarization argument is
re-run over an arbitrary *admissible source submodule* `A ⊆ localizedSources`, for which only
closure under addition and real scaling is used.  No closedness, completeness or density
hypothesis is imposed anywhere.

The results are then instantiated at `A = smoothSources hT W`, the actual space of smooth
compactly supported sources constructed in `SmoothSpacetimeSource`.  The resulting theorems
assume measured-map agreement **only** on that smooth class.

`MeasuredMapsAgreeOn.mono` records the exact logical relation: agreement on a larger class
implies agreement on a smaller one, so the smooth-class statements have strictly weaker
hypotheses than the v4.0 ones.

Part of `LiWangWienerSmoothObservationPacket` v5.0.
-/
import LiWangWiener.UCPBridge
import LiWangWiener.SmoothSpacetimeSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

variable {α T : ℝ}

/-! ## 1. The admissible-submodule hypotheses -/

/-- **Measured-map agreement over an admissible source submodule `A`.**  The state and the
velocity observed on `W` agree for the two kernels, for every source *in `A`* of norm below
`ε`.  Only membership in `A` is assumed — no density, closedness or completeness. -/
def MeasuredMapsAgreeOn (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T)) (ε : ℝ) :
    Prop :=
  ∀ f ∈ A, ‖f‖ < ε →
    (∀ (t : TimeI T), ∀ x ∈ W,
        synth (incl ((sourceSolution hα hT hm₁ hr₁ f) t).val) x
          = synth (incl ((sourceSolution hα hT hm₂ hr₂ f) t).val) x)
      ∧ (∀ (j : Fin 2) (t : TimeI T), ∀ x ∈ W,
        synth (velocity m₁ hm₁ j (incl ((sourceSolution hα hT hm₁ hr₁ f) t).val)) x
          = synth (velocity m₂ hm₂ j (incl ((sourceSolution hα hT hm₂ hr₂ f) t).val)) x)

/-- Both proved mild identities, over an admissible source submodule. -/
def BothMildOnSub (hα : 1 / 2 < α) (hT : 0 ≤ T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T)) (ε : ℝ) :
    Prop :=
  ∀ f ∈ A, ‖f‖ < ε →
    (sourceSolution hα hT hm₁ hr₁ f
        + sourceQuad hα hT m₁ hm₁ hr₁ (sourceSolution hα hT hm₁ hr₁ f)
            (sourceSolution hα hT hm₁ hr₁ f) = duhamelOp hα hT f)
      ∧ (sourceSolution hα hT hm₂ hr₂ f
        + sourceQuad hα hT m₂ hm₂ hr₂ (sourceSolution hα hT hm₂ hr₂ f)
            (sourceSolution hα hT hm₂ hr₂ f) = duhamelOp hα hT f)

/-- **The common mild neighbourhood**, derived from the existing construction: the two mild
identities hold simultaneously on a ball of the zero source, hence on any submodule. -/
theorem exists_bothMildOnSub (hα : 1 / 2 < α) (hT : 0 ≤ T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T)) :
    ∃ ε > 0, BothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A ε := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_two_kernel_mild hα hT hm₁ hr₁ hm₂ hr₂)
  refine ⟨ε, hε, fun f _ hf => hball ?_⟩
  rwa [dist_zero_right]

/-- Agreement on a larger class implies agreement on a smaller one. -/
theorem MeasuredMapsAgreeOn.mono (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {A B : Submodule ℝ (Curve0 T)}
    (hAB : A ≤ B) {ε : ℝ} (h : MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ B ε) :
    MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε :=
  fun f hf hfn => h f (hAB hf) hfn

theorem BothMildOnSub.mono (hα : 1 / 2 < α) (hT : 0 ≤ T)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {A B : Submodule ℝ (Curve0 T)}
    (hAB : A ≤ B) {ε : ℝ} (h : BothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ B ε) :
    BothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A ε :=
  fun f hf hfn => h f (hAB hf) hfn

/-- The v4.0 predicates are exactly the case `A = localizedSources`. -/
theorem measuredMapsAgreeOn_localizedSources (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (ε : ℝ) :
    MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ (localizedSources hT W) ε
      ↔ MeasuredMapsAgree hα hT W hm₁ hr₁ hm₂ hr₂ ε := Iff.rfl

theorem bothMildOnSub_localizedSources (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (ε : ℝ) :
    BothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ (localizedSources hT W) ε
      ↔ BothMildOn hα hT W hm₁ hr₁ hm₂ hr₂ ε := Iff.rfl

/-! ## 2. The ray limit and polarization over an admissible submodule -/

/-- **Conditional (on the external UCP hypothesis).**  For a source in the admissible submodule
`A` of small norm, the transport difference annihilates the actual solution.  The measured maps
are used only at that source. -/
theorem quad_transport_diff_sourceSolution_eq_zero_on (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {A : Submodule ℝ (Curve0 T)}
    (hA : A ≤ localizedSources hT.le W) {ε : ℝ}
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ A ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ A ε)
    {f : Curve0 T} (hf : f ∈ A) (hfn : ‖f‖ < ε) :
    quad (spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂))
      (sourceSolution hα hT.le hm₁ hr₁ f) = 0 := by
  obtain ⟨hm1, hm2⟩ := hmild f hf hfn
  obtain ⟨hs, hv⟩ := hobs f hf hfn
  have heq : sourceSolution hα hT.le hm₁ hr₁ f = sourceSolution hα hT.le hm₂ hr₂ f :=
    curve_eq_of_ucp hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hm1 hm2 hs hv
  have hm2' : sourceSolution hα hT.le hm₁ hr₁ f
      + sourceQuad hα hT.le m₂ hm₂ hr₂ (sourceSolution hα hT.le hm₁ hr₁ f)
          (sourceSolution hα hT.le hm₁ hr₁ f) = duhamelOp hα hT.le f := by
    rw [heq]; exact hm2
  exact transport_diff_self_eq_zero hα hT hm₁ hr₁ hm₂ hr₂ hm1 hm2'

/-- **Conditional.  The generated-source identity over an admissible submodule.**

If the two measured maps agree on the sources *in `A`* of norm below `ε`, then for all
directions `h₁, h₂ ∈ A`,

    `N_δ(J h₁, J h₂) + N_δ(J h₂, J h₁) = 0`,   `N_δ = N_{m₁ - m₂}`.

Only closure of `A` under addition and real scaling is used. -/
theorem generated_source_identity_on (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {A : Submodule ℝ (Curve0 T)} (hA : A ≤ localizedSources hT.le W) {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ A ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ A ε)
    {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ A) (hh₂ : h₂ ∈ A) :
    spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT.le h₁) (duhamelOp hα hT.le h₂)
      + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT.le h₂) (duhamelOp hα hT.le h₁) = 0 := by
  set B := spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) with hB
  have key : ∀ h : Curve0 T, h ∈ A → quad B (duhamelOp hα hT.le h) = 0 := by
    intro h hh
    refine transport_diff_duhamelOp_self_eq_zero hα hT hm₁ hr₁ hm₂ hr₂ hε ?_
    intro s hs
    have hmem : (s • h) ∈ A := Submodule.smul_mem _ s hh
    have hnorm : ‖s • h‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs]
      exact hs
    exact quad_transport_diff_sourceSolution_eq_zero_on hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hA
      hmild hobs hmem hnorm
  have ha := key h₁ hh₁
  have hb := key h₂ hh₂
  have hab := key (h₁ + h₂) (Submodule.add_mem _ hh₁ hh₂)
  rw [map_add] at hab
  exact polarization_of_quad_zero ha hb hab

/-- **Conditional.**  Equality of the two *actual* second source responses on directions of the
admissible submodule.  The derivatives are the genuine Fréchet derivatives of the actual
`sourceSolution` maps; nothing is assumed about them. -/
theorem fderiv_fderiv_sourceSolution_eq_on (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {A : Submodule ℝ (Curve0 T)} (hA : A ≤ localizedSources hT.le W) {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ A ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ A ε)
    {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ A) (hh₂ : h₂ ∈ A) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₁ hr₁)) (0 : Curve0 T) h₁ h₂
      = fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₂ hr₂)) (0 : Curve0 T) h₁ h₂ := by
  have hgen := generated_source_identity_on hα hT hW hUCP hm₁ hr₁ hm₂ hr₂ hA hε hmild hobs hh₁ hh₂
  have hdiff := fderiv_fderiv_sourceSolution_sub hα hT.le hm₁ hr₁ hm₂ hr₂ h₁ h₂
  rw [hgen, map_zero, neg_zero] at hdiff
  exact sub_eq_zero.mp hdiff

/-! ## 3. Instantiation at the actual smooth compactly supported source class -/

/-- **Conditional.  The generated-source identity, assuming measured-map agreement only on the
smooth compactly supported sources.**  This is the statement whose measurement hypothesis
matches the paper's. -/
theorem generated_source_identity_smooth (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ smoothSources hT W) (hh₂ : h₂ ∈ smoothSources hT W) :
    spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT.le h₁) (duhamelOp hα hT.le h₂)
      + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
        (duhamelOp hα hT.le h₂) (duhamelOp hα hT.le h₁) = 0 :=
  generated_source_identity_on hα hT hW hUCP hm₁ hr₁ hm₂ hr₂
    (smoothSources_le_localizedSources hT W) hε hmild hobs hh₁ hh₂

/-- **Conditional.**  Equality of the two actual second source responses on smooth compactly
supported directions. -/
theorem fderiv_fderiv_sourceSolution_eq_on_smooth (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {ε : ℝ} (hε : 0 < ε)
    (hmild : BothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    (hobs : MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε)
    {h₁ h₂ : Curve0 T} (hh₁ : h₁ ∈ smoothSources hT W) (hh₂ : h₂ ∈ smoothSources hT W) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₁ hr₁)) (0 : Curve0 T) h₁ h₂
      = fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le hm₂ hr₂)) (0 : Curve0 T) h₁ h₂ :=
  fderiv_fderiv_sourceSolution_eq_on hα hT hW hUCP hm₁ hr₁ hm₂ hr₂
    (smoothSources_le_localizedSources hT W) hε hmild hobs hh₁ hh₂

/-- The smooth-class hypothesis is genuinely weaker: v4.0-style agreement on all localized
sources implies it. -/
theorem measuredMapsAgreeOn_smooth_of_localized (hα : 1 / 2 < α) (hT : 0 < T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) {ε : ℝ}
    (h : MeasuredMapsAgree hα hT.le W hm₁ hr₁ hm₂ hr₂ ε) :
    MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ (smoothSources hT W) ε :=
  MeasuredMapsAgreeOn.mono hα hT.le W hm₁ hr₁ hm₂ hr₂
    (smoothSources_le_localizedSources hT W) h

/-- Non-vacuity of the smooth instantiation. -/
theorem exists_nonzero_mem_smoothSources (hT : 0 < T) {W : Set Torus2} (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ h ∈ smoothSources hT W, h ≠ 0 := by
  obtain ⟨V, hV, hVne, -⟩ := exists_nonzero_smoothSource hT hW hne
  exact ⟨V, hV, hVne⟩

end LiWang.WienerModel
