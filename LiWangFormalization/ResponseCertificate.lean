/-
# The source-response certificate

One record collecting the proved analytic inputs of a quadratic implicit-function /
source-to-solution interface, for a prescribed horizon `T` and one velocity symbol.

Its **inputs** are a uniform symbol bound and reality of the symbol; every other field is
discharged by a theorem of `DuhamelOperator.lean`, `SourceSolution.lean` and
`SourceVariations.lean`.  No field assumes existence, differentiability, or the variation
formulas.

Part of `LiWangFormalizationSourceResponsePacket` v3.0.
-/
import LiWangFormalization.SourceVariations

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal
open Filter Topology BoundedContinuousFunction

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-- The operator bound of the quadratic part used throughout the certificate. -/
noncomputable def responseQuadBound (α T C : ℝ) : ℝ := duhamelConst α T * (4 * Real.pi * C)

/-- The uniqueness radius attached to that bound. -/
noncomputable def responseRadius (α T C : ℝ) : ℝ := 1 / (4 * (responseQuadBound α T C + 1))

theorem responseQuadBound_nonneg {α T C : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 ≤ responseQuadBound α T C := by
  have h1 : (0:ℝ) ≤ duhamelConst α T := duhamelConst_nonneg hα hT
  have hpi := Real.pi_pos
  simp only [responseQuadBound]
  positivity

theorem responseRadius_pos {α T C : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 < responseRadius α T C := by
  have h := responseQuadBound_nonneg hα hT hC
  simp only [responseRadius]
  positivity

theorem two_mul_responseQuadBound_radius {α T C : ℝ} (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hC : 0 ≤ C) :
    2 * responseQuadBound α T C * responseRadius α T C ≤ 1 / 2 := by
  have hb := responseQuadBound_nonneg hα hT hC
  set b : ℝ := responseQuadBound α T C with hbdef
  have hb1 : (0:ℝ) < b + 1 := by linarith
  simp only [responseRadius, ← hbdef]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- **The source-response certificate.**  All fields are proved; the two hypotheses are the
symbol bound and reality of the symbol. -/
structure SourceResponseCertificate (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) : Prop where
  /-- The Duhamel operator is bounded by the Duhamel constant of the horizon. -/
  duhamel_bound : ‖(duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)‖ ≤ duhamelConst α T
  /-- The quadratic part is bounded. -/
  quad_bound : ‖(sourceQuad hα hT m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve1 T)‖
    ≤ responseQuadBound α T C
  /-- The Duhamel term starts at zero. -/
  duhamel_initial : ∀ f : Curve0 T, (duhamelOp hα hT f) ⟨0, ⟨le_rfl, hT⟩⟩ = 0
  /-- Zero source, zero solution. -/
  solution_zero : sourceSolution hα hT hm hr (0 : Curve0 T) = 0
  /-- The forced mild equation, on a neighbourhood of the zero source. -/
  mild_identity : ∀ᶠ f in 𝓝 (0 : Curve0 T),
    sourceSolution hα hT hm hr f
      + sourceQuad hα hT m hm hr (sourceSolution hα hT hm hr f)
          (sourceSolution hα hT hm hr f) = duhamelOp hα hT f
  /-- The pointwise (Fourier-coefficient) form of the mild equation. -/
  mild_pointwise : ∀ᶠ f in 𝓝 (0 : Curve0 T), ∀ t : TimeI T,
    ((sourceSolution hα hT hm hr f) t).val
      = duhamelIntegral hα.le (t : ℝ) (sourceFun hT f)
        - duhamelIntegral hα.le (t : ℝ)
            (fun s => transport m hm ((sourceSolution hα hT hm hr f) (clampT hT s)).val
              ((sourceSolution hα hT hm hr f) (clampT hT s)).val)
  /-- `C²` regularity at the zero source. -/
  contDiff_two : ContDiffAt ℝ 2 (sourceSolution hα hT hm hr) (0 : Curve0 T)
  /-- The first source variation is the Duhamel operator. -/
  first_variation : fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T)
    = (duhamelOp hα hT : Curve0 T →L[ℝ] Curve1 T)
  /-- Its pointwise form. -/
  first_variation_pointwise : ∀ (h : Curve0 T) (t : TimeI T),
    ((fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).val
      = duhamelIntegral hα.le (t : ℝ) (sourceFun hT h)
  /-- The exact second source variation, with the minus sign and the symmetrization. -/
  second_variation : ∀ h₁ h₂ : Curve0 T,
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = -(duhamelOp hα hT
            (spacetimeTransport m hm hr (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
              + spacetimeTransport m hm hr (duhamelOp hα hT h₂) (duhamelOp hα hT h₁)))
  /-- Symmetry of the second variation. -/
  second_variation_symm : ∀ h₁ h₂ : Curve0 T,
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂
      = fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₂ h₁
  /-- Both variations start at zero. -/
  variation_initial : ∀ h₁ h₂ : Curve0 T,
    (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h₁) ⟨0, ⟨le_rfl, hT⟩⟩ = 0 ∧
      (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂)
        ⟨0, ⟨le_rfl, hT⟩⟩ = 0
  /-- Quantitative bounds on the two variations. -/
  variation_bounds : ∀ h₁ h₂ : Curve0 T,
    ‖fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h₁‖ ≤ duhamelConst α T * ‖h₁‖ ∧
      ‖fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂‖
        ≤ 2 * responseQuadBound α T C * (duhamelConst α T * ‖h₁‖) * (duhamelConst α T * ‖h₂‖)
  /-- Existence in the explicit ball, for any prescribed horizon. -/
  existence : ∀ f : Curve0 T,
    ‖duhamelOp hα hT f‖ ≤ 1 / (8 * (responseQuadBound α T C + 1)) →
      ∃ u : Curve1 T, ‖u‖ ≤ responseRadius α T C ∧
        u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f
  /-- Uniqueness in that ball. -/
  uniqueness : ∀ (f : Curve0 T) (u v : Curve1 T),
    ‖u‖ ≤ responseRadius α T C → ‖v‖ ≤ responseRadius α T C →
      u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f →
      v + sourceQuad hα hT m hm hr v v = duhamelOp hα hT f → u = v
  /-- Lipschitz dependence on the source in that ball. -/
  stability : ∀ (f g : Curve0 T) (u v : Curve1 T),
    ‖u‖ ≤ responseRadius α T C → ‖v‖ ≤ responseRadius α T C →
      u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f →
      v + sourceQuad hα hT m hm hr v v = duhamelOp hα hT g →
      ‖u - v‖ ≤ 2 * (duhamelConst α T * ‖f - g‖)

/-- **The certificate is proved.** -/
theorem sourceResponseCertificate (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) :
    SourceResponseCertificate hα hT hm hr hC := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  have hb : ‖(sourceQuad hα hT m hm hr : Curve1 T →L[ℝ] Curve1 T →L[ℝ] Curve1 T)‖
      ≤ responseQuadBound α T C := norm_sourceQuad_le hα hT hm hr hC
  have hbr : 2 * responseQuadBound α T C * responseRadius α T C ≤ 1 / 2 :=
    two_mul_responseQuadBound_radius hα hT hC0
  exact
    { duhamel_bound := norm_duhamelOp_le hα hT
      quad_bound := hb
      duhamel_initial := fun f => duhamelOp_zero_time hα hT f
      solution_zero := sourceSolution_zero hα hT hm hr
      mild_identity := eventually_sourceSolution_eq hα hT hm hr
      mild_pointwise := by
        filter_upwards [eventually_sourceSolution_eq hα hT hm hr] with f hf t
        exact mild_pointwise_of_curve hα hT hm hr hf t
      contDiff_two := contDiffAt_sourceSolution hα hT hm hr
      first_variation := fderiv_sourceSolution_zero hα hT hm hr
      first_variation_pointwise := fun h t => fderiv_sourceSolution_zero_val hα hT hm hr h t
      second_variation := fun h₁ h₂ =>
        fderiv_fderiv_sourceSolution_apply' hα hT hm hr h₁ h₂
      second_variation_symm := fun h₁ h₂ =>
        fderiv_fderiv_sourceSolution_symm hα hT hm hr h₁ h₂
      variation_initial := fun h₁ h₂ =>
        ⟨fderiv_sourceSolution_zero_initial hα hT hm hr h₁,
          fderiv_fderiv_sourceSolution_initial hα hT hm hr h₁ h₂⟩
      variation_bounds := fun h₁ h₂ =>
        ⟨norm_fderiv_sourceSolution_apply_le hα hT hm hr h₁,
          norm_fderiv_fderiv_sourceSolution_le hα hT hm hr hb h₁ h₂⟩
      existence := fun f hf =>
        exists_mild_curve_of_small hα hT hm hr hb (responseQuadBound_nonneg hα hT hC0) f hf
      uniqueness := fun f u v hu hv heu hev =>
        mild_curve_unique_ball hα hT hm hr hb hbr hu hv f heu hev
      stability := fun f g u v hu hv heu hev =>
        mild_curve_lipschitz hα hT hm hr hb hbr hu hv f g heu hev }

end LiWang.Formalization
