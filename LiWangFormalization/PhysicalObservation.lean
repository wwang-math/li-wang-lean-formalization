/-
# The physical observation map and the recovery specialization

Step 4 of the v7.0 physical bridge.

The *physical* measurement of the Li–Wang inverse problem is the pair

    `L_ℛ : f ↦ (θ|_{W×(0,T)}, ℛ(θ)|_{W×(0,T)})`

where `θ` is **the** physical solution of `∂_t θ + ℛ(θ)·∇θ + (-Δ)^α θ = f`, `θ(0)=0`.  Here
`obsState` and `obsVelocity` are exactly those two restrictions, evaluated on the actual
continuous functions on the torus obtained by Fourier synthesis; `PhysicalObsAgreeOn` is the
hypothesis "`L_{ℛ₁} = L_{ℛ₂}` on small sources of the admissible class".

The content of this file is:

* `physicalObs_state_eq` / `physicalObs_velocity_eq` — the observation of *any* physical
  solution equals the observation of the constructed mild state.  This is a **proved
  consequence** of `eq_of_isPhysicalSolution`, i.e. of the PDE and the uniqueness theory of
  `PhysicalComparison`; it is not an extra hypothesis.  In particular the physical observation
  map is well defined: it does not depend on which physical solution is chosen.
* `exists_measuredMapsAgreeOn_of_physical` — the physical measurement hypothesis implies the
  packet's `MeasuredMapsAgreeOn` hypothesis on the same admissible source submodule.  The
  smallness radius is measured in the **`Curve0 T` norm** (the sup-in-time Wiener-algebra norm
  of the source) for *both* predicates, so no conversion of norms is involved; the common
  radius is the minimum of the physical radius and the radius on which both mild identities
  hold (`exists_bothMildOnSub`).
* the recovery theorems restated with the physical measurement hypothesis in place of the mild
  one, ending with `paper_exterior_velocity_eq`, the corollary in the shape of the paper's
  Theorem 1.1.

Hypotheses that remain, and are stated explicitly in every theorem below: the geometry
(`IsOpen W`), the genuine kernel assumptions (reality, and either `A¹` membership or the
paper's ordered ellipticity), the physical measurement equality, and the portable
`FractionalUCP α W` parameter.  Approximation, target identities, state convergence and
equality to the mild map do **not** appear as hypotheses.

Part of `LiWangFormalizationPhysicalPDEBridgePacket` v7.0.
-/
import LiWangFormalization.PhysicalComparison
import LiWangFormalization.LocalizedSource
import LiWangFormalization.PaperKernelBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The physical observations

The observations themselves are the v4 API `obsState hT W θ t x` and
`obsVelocity m hm j hT W θ t x` of `LocalizedSource.lean`: the *actual restrictions* to the
observation region `W` of the continuous functions on the torus obtained by Fourier synthesis
from `θ(t)` and from the velocity field `ℛ_m(θ(t))`.  They are reused unchanged. -/

/-- **The physical measurement hypothesis.**  For every source of the admissible class `A` with
`‖f‖ < ε`, the two kernels produce the same observed state and the same observed velocity on
the observation region `W`, at every time of `[0,T]`.  The solutions are *physical* solutions,
characterised by the PDE, the regularity and the initial trace — not by any formula. -/
def PhysicalObsAgreeOn (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) : Prop :=
  ∀ f ∈ A, ‖f‖ < ε → ∀ θ₁ θ₂ : Curve1 T,
    IsPhysicalSolution hα hT hm₁ f θ₁ → IsPhysicalSolution hα hT hm₂ f θ₂ →
      (∀ (t : TimeI T) (x : W), obsState hT W θ₁ (t : ℝ) x = obsState hT W θ₂ (t : ℝ) x)
        ∧ (∀ (j : Fin 2) (t : TimeI T) (x : W),
            obsVelocity m₁ hm₁ j hT W θ₁ (t : ℝ) x = obsVelocity m₂ hm₂ j hT W θ₂ (t : ℝ) x)

/-! ## 2. The physical observation map is well defined -/

/-- **The observed state of any physical solution is the observed state of the mild state.**
This is the identification the bridge needs, and it is proved from the PDE and the uniqueness
theorem, not assumed. -/
theorem physicalObs_state_eq (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {f : Curve0 T} {u θ : Curve1 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hθ : IsPhysicalSolution hα hT hm f θ) (W : Set Torus2) (t : ℝ) (x : W) :
    obsState hT W θ t x = obsState hT W u t x := by
  rw [eq_of_isPhysicalSolution hα hT hm hr hC hmild hθ]

/-- The same for the observed velocity. -/
theorem physicalObs_velocity_eq (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {f : Curve0 T} {u θ : Curve1 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hθ : IsPhysicalSolution hα hT hm f θ) (W : Set Torus2) (j : Fin 2) (t : ℝ) (x : W) :
    obsVelocity m hm j hT W θ t x = obsVelocity m hm j hT W u t x := by
  rw [eq_of_isPhysicalSolution hα hT hm hr hC hmild hθ]

/-! ## 3. From the physical measurement hypothesis to the packet's measured-map hypothesis -/

/-- **The bridge.**  Physical measurement equality on small sources of `A` implies the packet's
`MeasuredMapsAgreeOn` hypothesis on `A`.

The common smallness radius is `min ε ε₀` in the `Curve0 T` norm: `ε` is the radius of the
physical hypothesis and `ε₀` the radius on which both mild identities hold.  Both are radii for
the *same* norm, so no norm conversion occurs. -/
theorem exists_measuredMapsAgreeOn_of_physical (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T))
    (hphys : ∃ ε > 0, PhysicalObsAgreeOn hα hT W hm₁ hm₂ A ε) :
    ∃ ε > 0, MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε := by
  obtain ⟨ε, hε0, hε⟩ := hphys
  obtain ⟨ε₀, hε₀0, hmild⟩ := exists_bothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A
  refine ⟨min ε ε₀, lt_min hε0 hε₀0, ?_⟩
  intro f hfA hfn
  obtain ⟨hm1, hm2⟩ := hmild f hfA (lt_of_lt_of_le hfn (min_le_right _ _))
  have hp1 : IsPhysicalSolution hα hT hm₁ f (sourceSolution hα hT hm₁ hr₁ f) :=
    isPhysicalSolution_of_mild hα hT hm₁ hr₁ hm1
  have hp2 : IsPhysicalSolution hα hT hm₂ f (sourceSolution hα hT hm₂ hr₂ f) :=
    isPhysicalSolution_of_mild hα hT hm₂ hr₂ hm2
  obtain ⟨hs, hv⟩ := hε f hfA (lt_of_lt_of_le hfn (min_le_left _ _)) _ _ hp1 hp2
  constructor
  · intro t x hx
    have h := hs t ⟨x, hx⟩
    rw [obsState_eq, obsState_eq, curveState_coe hT _ t, curveState_coe hT _ t] at h
    exact h
  · intro j t x hx
    have h := hv j t ⟨x, hx⟩
    rw [obsVelocity_eq, obsVelocity_eq, curveState_coe hT _ t, curveState_coe hT _ t] at h
    exact h

/-- **Faithfulness of the physical measurement hypothesis.**  Conversely, the packet's
measured-map agreement implies the physical one on the same class.  The mechanism is
`eq_of_isPhysicalSolution`: on the common ball every physical solution *is* the mild state, so
the two hypotheses say the same thing.  In particular the physical hypothesis is neither
secretly stronger (which would make the bridge unusable) nor secretly weaker (which would make
it vacuous). -/
theorem exists_physicalObsAgreeOn_of_measured (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T))
    (hmeas : ∃ ε > 0, MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε) :
    ∃ ε > 0, PhysicalObsAgreeOn hα hT W hm₁ hm₂ A ε := by
  obtain ⟨ε, hε0, hε⟩ := hmeas
  obtain ⟨ε₀, hε₀0, hmild⟩ := exists_bothMildOnSub hα hT hm₁ hr₁ hm₂ hr₂ A
  obtain ⟨C₁, hC₁⟩ := id hm₁
  obtain ⟨C₂, hC₂⟩ := id hm₂
  refine ⟨min ε ε₀, lt_min hε0 hε₀0, ?_⟩
  intro f hfA hfn θ₁ θ₂ hp₁ hp₂
  obtain ⟨hm1, hm2⟩ := hmild f hfA (lt_of_lt_of_le hfn (min_le_right _ _))
  have he₁ : θ₁ = sourceSolution hα hT hm₁ hr₁ f :=
    eq_of_isPhysicalSolution hα hT hm₁ hr₁ hC₁ hm1 hp₁
  have he₂ : θ₂ = sourceSolution hα hT hm₂ hr₂ f :=
    eq_of_isPhysicalSolution hα hT hm₂ hr₂ hC₂ hm2 hp₂
  obtain ⟨hs, hv⟩ := hε f hfA (lt_of_lt_of_le hfn (min_le_left _ _))
  subst he₁
  subst he₂
  constructor
  · intro t x
    have h := hs t (x : Torus2) x.2
    rw [obsState_eq, obsState_eq, curveState_coe hT _ t, curveState_coe hT _ t]
    exact h
  · intro j t x
    have h := hv j t (x : Torus2) x.2
    rw [obsVelocity_eq, obsVelocity_eq, curveState_coe hT _ t, curveState_coe hT _ t]
    exact h

/-- **The two measurement hypotheses are equivalent.** -/
theorem exists_physicalObsAgreeOn_iff_measured (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂) (A : Submodule ℝ (Curve0 T)) :
    (∃ ε > 0, PhysicalObsAgreeOn hα hT W hm₁ hm₂ A ε)
      ↔ ∃ ε > 0, MeasuredMapsAgreeOn hα hT W hm₁ hr₁ hm₂ hr₂ A ε :=
  ⟨exists_measuredMapsAgreeOn_of_physical hα hT W hm₁ hr₁ hm₂ hr₂ A,
    exists_physicalObsAgreeOn_of_measured hα hT W hm₁ hr₁ hm₂ hr₂ A⟩

/-! ## 4. Recovery from the physical measurement -/

/-- **Operator recovery from the physical measurement.**  The two rotated-gradient velocity
symbols coincide.  Remaining hypotheses: the geometry `IsOpen W`, a nonempty exterior, the
genuine kernel assumptions (boundedness and reality of the symbols), the physical measurement
equality on the smooth admissible source class, and the portable `FractionalUCP α W`. -/
theorem rotatedGradientSymbol_eq_of_physical (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0,
      PhysicalObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ :=
  rotatedGradientSymbol_eq_of_measured hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT
    (exists_measuredMapsAgreeOn_of_physical hα hT.le W hm₁ hr₁ hm₂ hr₂ _ hobs)

/-- **Kernel recovery for genuine `A¹` kernels, from the physical measurement.** -/
theorem kernel_determined_of_wiener1_physical (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Wiener1} (hcs₁ : ConjSymmetric K₁.coeff) (hcs₂ : ConjSymmetric K₂.coeff)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, PhysicalObsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel)
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel) (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : K₁.coeff k = K₂.coeff k :=
  kernel_determined_of_wiener1 hα hT hW hE hUCP hcs₁ hcs₂ hτ0 hτT
    (exists_measuredMapsAgreeOn_of_physical hα hT.le W _ (rotatedGradientSymbol_isRealSymbol hcs₁)
      _ (rotatedGradientSymbol_isRealSymbol hcs₂) _ hobs) hk

/-- **Kernel recovery for the paper's ordered-elliptic class, from the physical
measurement.** -/
theorem kernel_determined_of_orderedEllipticity_physical (hα : 1 / 2 < α) (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ} {c₁ D₁ c₂ D₂ : ℝ}
    (hell₁ : OrderedFourierEllipticity κ₁ c₁ D₁) (hcs₁ : ConjSymmetric κ₁)
    (hell₂ : OrderedFourierEllipticity κ₂ c₂ D₂) (hcs₂ : ConjSymmetric κ₂)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, PhysicalObsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₁))
      (rotatedGradientSymbol_bdd (orderedEllipticity_admissible hell₂))
      (smoothSources hT W) ε)
    {k : Gam} (hk : k ≠ 0) : κ₁ k = κ₂ k :=
  kernel_determined_of_orderedEllipticity hα hT hW hE hUCP hell₁ hcs₁ hell₂ hcs₂ hτ0 hτT
    (exists_measuredMapsAgreeOn_of_physical hα hT.le W _ (rotatedGradientSymbol_isRealSymbol hcs₁)
      _ (rotatedGradientSymbol_isRealSymbol hcs₂) _ hobs) hk

/-! ## 5. The paper-level exterior corollary -/

/-- **The conclusion of the paper's Theorem 1.1, in this model.**  If the two physical
measurement maps agree on the smooth admissible sources supported in `W × (0,T)`, then for
every input `ψ` and every exterior point `x ∉ closure W`, the two velocity fields agree at `x`:

    `ℛ₁ψ (x) = ℛ₂ψ (x)`,  `x ∈ W^e`.

No separate nonempty-exterior hypothesis is imposed: the exterior point `hx` supplies it, and
for an empty exterior the statement is vacuous. -/
theorem paper_exterior_velocity_eq (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0,
      PhysicalObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε)
    (ψ : Wiener1) (j : Fin 2) {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    synth (velocity (rotatedGradientSymbol κ₁) hm₁ j (incl ψ)) x
      = synth (velocity (rotatedGradientSymbol κ₂) hm₂ j (incl ψ)) x := by
  have heq := rotatedGradientSymbol_eq_of_physical hα hT hW ⟨x, hx⟩ hUCP hm₁ hr₁ hm₂ hr₂ hC
    hτ0 hτT hobs
  rw [velocity_congr hm₁ hm₂ heq j]

/-- The same conclusion for a genuine `A¹` kernel pair, stated with the kernels rather than the
symbols, and for an exterior test input (the model of `g ∈ C^∞_c(W^e)`). -/
theorem paper_exterior_velocity_eq_wiener1 (hα : 1 / 2 < α) (hT : 0 < T) {W : Set Torus2}
    (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {K₁ K₂ : Wiener1} (hcs₁ : ConjSymmetric K₁.coeff) (hcs₂ : ConjSymmetric K₂.coeff)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hobs : ∃ ε > 0, PhysicalObsAgreeOn hα hT.le W
      (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel)
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel) (smoothSources hT W) ε)
    {ψ : Wiener1} (hψ : IsExteriorTest W ψ) (j : Fin 2) {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    (∀ y ∈ closure W, synth (incl ψ) y = 0)
      ∧ synth (velocity (rotatedGradientSymbol K₁.coeff)
          (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel) j (incl ψ)) x
        = synth (velocity (rotatedGradientSymbol K₂.coeff)
          (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel) j (incl ψ)) x := by
  obtain ⟨C, hC⟩ :=
    (rotatedGradientSymbol_bdd K₁.isAdmissibleKernel).sub
      (rotatedGradientSymbol_bdd K₂.isAdmissibleKernel)
  exact ⟨fun y hy => hψ.field_vanishes hy,
    paper_exterior_velocity_eq hα hT hW hUCP _ (rotatedGradientSymbol_isRealSymbol hcs₁)
      _ (rotatedGradientSymbol_isRealSymbol hcs₂) hC hτ0 hτT hobs ψ j hx⟩

/-! ## 6. Fourier normalization of the test inputs -/

/-- **The Wiener carrier carries the physical Fourier normalization.**  For an input `ψ` in the
first-order carrier, the physical function on the torus is `g = synth (incl ψ)` with
`g(x) = ∑_k ψ̂_k e^{2πi k·x}`, and its directional derivative along the `j`-th coordinate is the
synthesis of `fourierDeriv j ψ`, whose coefficients are `2πi k_j ψ̂_k`.  So the `2π` appearing
in the symbols is exactly the `2π` of the physical derivative: a smooth exterior test enters
the carrier with a compatible normalization. -/
theorem test_fourier_normalization (ψ : Wiener1) (x : Torus2) (j : Fin 2) :
    HasDerivAt (fun s : ℝ => synth (incl ψ) (torusShift x j s))
      (synth (fourierDeriv j ψ) x) 0 :=
  hasDerivAt_synth_torus ψ x j

/-- **Sign and normalization check for the velocity operator.**  For a genuine `A¹` kernel the
observed velocity really is the physical rotated gradient
`ℛ_K ψ = ∇^⊥(K ⋆ ψ) = (-∂₂(K ⋆ ψ), ∂₁(K ⋆ ψ))`, the derivatives being genuine directional
derivatives on the torus. -/
theorem velocity_eq_physical_rotatedGradient (K ψ : Wiener1) (x : Torus2) :
    synth (velocity (rotatedGradientSymbol K.coeff)
        (rotatedGradientSymbol_bdd K.isAdmissibleKernel) 0 (incl ψ)) x
          = -deriv (fun s : ℝ => synth (incl (kernelConv K ψ)) (torusShift x 1 s)) 0
      ∧ synth (velocity (rotatedGradientSymbol K.coeff)
        (rotatedGradientSymbol_bdd K.isAdmissibleKernel) 1 (incl ψ)) x
          = deriv (fun s : ℝ => synth (incl (kernelConv K ψ)) (torusShift x 0 s)) 0 := by
  constructor
  · rw [velocity_eq_kernelConvDeriv_zero K ψ, deriv_synth_torus,
      map_neg, incl_kernelConvDeriv]
    simp
  · rw [velocity_eq_kernelConvDeriv_one K ψ, deriv_synth_torus, incl_kernelConvDeriv]

end LiWang.Formalization
