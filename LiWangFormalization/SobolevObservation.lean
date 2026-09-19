/-
# The Sobolev observation map and the recovery corollary

Step 4 of the v8.0 Sobolev-compatibility bridge.

The paper's measurement is `L_ℛ : f ↦ (θ|_{W×(0,T)}, ℛ(θ)|_{W×(0,T)})`, an equality of
**almost-everywhere** objects on the *open* cylinder.  The packet's `MeasuredMapsAgreeOn` is a
**pointwise** statement at every time of the *closed* interval.  This file keeps the two apart
and proves the upgrade, rather than defining the difference away:

* `forall_eq_of_ae_eq_open` — two continuous functions agreeing almost everywhere on an open set
  agree on it, because the measure has full support (`IsOpenPosMeasure`);
* the spatial upgrade is that lemma on `𝕋²`, the time upgrade is that lemma on `(0,T)` followed
  by `Set.EqOn.closure` to reach the endpoints `t = 0` and `t = T`.

`SobolevObsAgreeOn` is the measurement hypothesis stated for the **Sobolev** solutions: the
state part is an equality of the `L²(𝕋²)` classes themselves, with no representative chosen.

`SobolevExistence` isolates the one forward-theory input: that the small admissible sources
*have* Sobolev solutions.  The `H³` bound `M` is **existentially quantified per source**, never
uniform over a `Curve0` ball: a highly oscillatory smooth source can be small in `Curve0` and
large in any higher norm, so a uniform `M` would be an unavailable — and here unnecessary —
strengthening.  It is named, carried explicitly, and discharged separately in
`HigherRegularity.lean` for the sources actually used; it is never assumed silently.

Part of `LiWangFormalizationSobolevCompatibilityPacket` v8.0.
-/
import LiWangFormalization.SobolevSolution
import LiWangFormalization.PhysicalObservation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. Upgrading almost-everywhere agreement on an open set -/

/-- **Continuous functions agreeing almost everywhere on an open set agree on it.**  The measure
must have full support; both `(volume : Measure ℝ)` and `(volume : Measure Torus2)` do. -/
theorem forall_eq_of_ae_eq_open {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} [μ.IsOpenPosMeasure] {U : Set X} (hU : IsOpen U)
    {g₁ g₂ : X → ℂ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hae : ∀ᵐ x ∂(μ.restrict U), g₁ x = g₂ x) : ∀ x ∈ U, g₁ x = g₂ x := by
  have hmeas : MeasurableSet U := hU.measurableSet
  have hnull : μ (U ∩ {x | g₁ x ≠ g₂ x}) = 0 := by
    have h := (MeasureTheory.ae_restrict_iff' hmeas).1 hae
    rw [MeasureTheory.ae_iff] at h
    refine measure_mono_null ?_ h
    intro x hx
    exact fun hmem => hx.2 (hmem hx.1)
  have hopen : IsOpen (U ∩ {x | g₁ x ≠ g₂ x}) :=
    hU.inter (isOpen_ne_fun hg₁ hg₂)
  have hempty : U ∩ {x | g₁ x ≠ g₂ x} = ∅ := hopen.measure_eq_zero_iff μ |>.1 hnull
  intro x hx
  by_contra hne
  exact absurd (Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hx, hne⟩) (by simp)

/-- The time upgrade: almost everywhere on `(0,T)` plus continuity gives every `t ∈ [0,T]`,
endpoints included. -/
theorem forall_eq_of_ae_eq_time {T : ℝ} (hT : 0 < T) {G₁ G₂ : ℝ → ℂ}
    (hg₁ : Continuous G₁) (hg₂ : Continuous G₂)
    (hae : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)), G₁ t = G₂ t) :
    ∀ t ∈ Set.Icc (0:ℝ) T, G₁ t = G₂ t := by
  have hIoo : ∀ t ∈ Set.Ioo (0:ℝ) T, G₁ t = G₂ t :=
    forall_eq_of_ae_eq_open isOpen_Ioo hg₁ hg₂ hae
  have heqOn : Set.EqOn G₁ G₂ (closure (Set.Ioo (0:ℝ) T)) :=
    (Set.EqOn.closure (fun t ht => hIoo t ht) hg₁ hg₂)
  rw [closure_Ioo (ne_of_lt hT)] at heqOn
  exact fun t ht => heqOn ht

/-! ## 2. The observations of a Sobolev solution -/

namespace IsSobolevSolution

variable {hα : 1 / 2 < α} {hT : 0 ≤ T} {hm : IsBddSymbol m} {M : ℝ} {f : Curve0 T}
  {θ : ℝ → TorusL2}

/-- **The observed state**: the value of the continuous representative. -/
noncomputable def obsState (h : IsSobolevSolution hα hT hm M f θ) (t : ℝ) (x : Torus2) : ℂ :=
  synth (incl (curveState hT h.curve t)) x

/-- **The observed velocity**: the `j`-th component of `ℛ_m(θ(t))`. -/
noncomputable def obsVel (h : IsSobolevSolution hα hT hm M f θ) (j : Fin 2) (t : ℝ)
    (x : Torus2) : ℂ :=
  synth (velocity m hm j (incl (curveState hT h.curve t))) x

/-- The observed state really is (a representative of) the `L²` state. -/
theorem obsState_ae (h : IsSobolevSolution hα hT hm M f θ) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    (fun x => h.obsState t x) =ᵐ[(volume : Measure Torus2)] (θ t : Torus2 → ℂ) := by
  have hae := synthL2_apply_ae (incl (curveState hT h.curve t))
  rw [h.synthL2_curveState ht] at hae
  filter_upwards [hae] with x hx
  rw [obsState, ← hx]

theorem continuous_obsState (h : IsSobolevSolution hα hT hm M f θ) (x : Torus2) :
    Continuous fun t : ℝ => h.obsState t x :=
  ((continuous_eval_const x).comp
    (synth.continuous.comp (incl.continuous.comp (continuous_curveState hT h.curve))))

theorem continuous_obsVel (h : IsSobolevSolution hα hT hm M f θ) (j : Fin 2) (x : Torus2) :
    Continuous fun t : ℝ => h.obsVel j t x :=
  ((continuous_eval_const x).comp
    (synth.continuous.comp ((velocity m hm j).continuous.comp
      (incl.continuous.comp (continuous_curveState hT h.curve)))))

theorem continuous_obsState_space (h : IsSobolevSolution hα hT hm M f θ) (t : ℝ) :
    Continuous fun x : Torus2 => h.obsState t x :=
  (synth (incl (curveState hT h.curve t))).continuous

theorem continuous_obsVel_space (h : IsSobolevSolution hα hT hm M f θ) (j : Fin 2) (t : ℝ) :
    Continuous fun x : Torus2 => h.obsVel j t x :=
  (synth (velocity m hm j (incl (curveState hT h.curve t)))).continuous

end IsSobolevSolution

/-! ## 3. The Sobolev measurement hypothesis -/

/-- **The forward input, isolated.**  Every admissible source of norm below `ε` has a Sobolev
solution with `H³` bound `M`.  This is the only forward-theory statement the bridge needs, and
it is carried explicitly rather than assumed inside a certificate. -/
def SobolevExistence (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) : Prop :=
  ∀ f ∈ A, ‖f‖ < ε → ∃ (M : ℝ) (θ : ℝ → TorusL2), IsSobolevSolution hα hT hm M f θ

/-- **The physical Sobolev measurement hypothesis.**  For each admissible small source, any two
Sobolev solutions for the two kernels have observations agreeing almost everywhere on the open
cylinder `W × (0,T)`.  The state part is an equality of the `L²(𝕋²)` classes themselves. -/
def SobolevObsAgreeOn (hα : 1 / 2 < α) (hT : 0 ≤ T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) : Prop :=
  ∀ f ∈ A, ‖f‖ < ε → ∀ (M₁ M₂ : ℝ) (θ₁ θ₂ : ℝ → TorusL2)
    (h₁ : IsSobolevSolution hα hT hm₁ M₁ f θ₁) (h₂ : IsSobolevSolution hα hT hm₂ M₂ f θ₂),
      (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)),
          ∀ᵐ x ∂((volume : Measure Torus2).restrict W),
            (θ₁ t : Torus2 → ℂ) x = (θ₂ t : Torus2 → ℂ) x)
        ∧ (∀ j : Fin 2, ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)),
            ∀ᵐ x ∂((volume : Measure Torus2).restrict W),
              h₁.obsVel j t x = h₂.obsVel j t x)

/-! ## 4. The bridge to the packet's measured-map hypothesis -/

/-- **The observation bridge.**  The Sobolev measurement hypothesis, together with the forward
existence input, yields the packet's `MeasuredMapsAgreeOn` on the same admissible class.

Every step is a proved upgrade: the `L²` state classes are replaced by the *continuous*
representatives (`obsState_ae`), the spatial almost-everywhere agreement is upgraded on the open
region `W` by `forall_eq_of_ae_eq_open`, the temporal one is upgraded to the closed interval by
`forall_eq_of_ae_eq_time`, and the Sobolev representative is identified with the packet's mild
solution by the unconditional comparison theorem `curve_eq_of_mild`. -/
theorem exists_measuredMapsAgreeOn_of_sobolev (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁) (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    (A : Submodule ℝ (Curve0 T))
    (hex₁ : ∃ ε > 0, SobolevExistence hα hT.le hm₁ A ε)
    (hex₂ : ∃ ε > 0, SobolevExistence hα hT.le hm₂ A ε)
    (hobs : ∃ ε > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ A ε) :
    ∃ ε > 0, MeasuredMapsAgreeOn hα hT.le W hm₁ hr₁ hm₂ hr₂ A ε := by
  obtain ⟨ε₁, hε₁0, he₁⟩ := hex₁
  obtain ⟨ε₂, hε₂0, he₂⟩ := hex₂
  obtain ⟨ε₃, hε₃0, hO⟩ := hobs
  obtain ⟨ε₀, hε₀0, hmild⟩ := exists_bothMildOnSub hα hT.le hm₁ hr₁ hm₂ hr₂ A
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₀), by positivity, ?_⟩
  intro f hfA hfn
  have hf1 : ‖f‖ < ε₁ := lt_of_lt_of_le hfn (le_trans (min_le_left _ _) (min_le_left _ _))
  have hf2 : ‖f‖ < ε₂ := lt_of_lt_of_le hfn (le_trans (min_le_left _ _) (min_le_right _ _))
  have hf3 : ‖f‖ < ε₃ := lt_of_lt_of_le hfn (le_trans (min_le_right _ _) (min_le_left _ _))
  have hf0 : ‖f‖ < ε₀ := lt_of_lt_of_le hfn (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨M₁, θ₁, hs₁⟩ := he₁ f hfA hf1
  obtain ⟨M₂, θ₂, hs₂⟩ := he₂ f hfA hf2
  obtain ⟨hm1, hm2⟩ := hmild f hfA hf0
  obtain ⟨hstate, hvel⟩ := hO f hfA hf3 M₁ M₂ θ₁ θ₂ hs₁ hs₂
  -- the two representatives are the packet's mild solutions
  have hc₁ : hs₁.curve = sourceSolution hα hT.le hm₁ hr₁ f :=
    hs₁.curve_eq_of_mild hr₁ hC₁ hm1
  have hc₂ : hs₂.curve = sourceSolution hα hT.le hm₂ hr₂ f :=
    hs₂.curve_eq_of_mild hr₂ hC₂ hm2
  -- the state observations agree pointwise
  have hstate' : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ x ∈ W, hs₁.obsState t x = hs₂.obsState t x := by
    have hspace : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)),
        ∀ x ∈ W, hs₁.obsState t x = hs₂.obsState t x := by
      have hIoo : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)),
          t ∈ Set.Icc (0:ℝ) T :=
        (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
          (Filter.Eventually.of_forall (fun t ht => ⟨ht.1.le, ht.2.le⟩))
      filter_upwards [hstate, hIoo] with t hts htm
      refine forall_eq_of_ae_eq_open (μ := (volume : Measure Torus2)) hW
        (hs₁.continuous_obsState_space t) (hs₂.continuous_obsState_space t) ?_
      have h1 : (fun x => hs₁.obsState t x) =ᵐ[(volume : Measure Torus2)] (θ₁ t : Torus2 → ℂ) :=
        hs₁.obsState_ae htm
      have h2 : (fun x => hs₂.obsState t x) =ᵐ[(volume : Measure Torus2)] (θ₂ t : Torus2 → ℂ) :=
        hs₂.obsState_ae htm
      have h1r := MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure Torus2)) (s := W) h1
      have h2r := MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure Torus2)) (s := W) h2
      filter_upwards [h1r, h2r, hts] with x hx1 hx2 hx
      rw [hx1, hx2, hx]
    intro t ht x hx
    refine forall_eq_of_ae_eq_time hT (hs₁.continuous_obsState x) (hs₂.continuous_obsState x)
      ?_ t ht
    filter_upwards [hspace] with s hs
    exact hs x hx
  -- the velocity observations agree pointwise
  have hvel' : ∀ (j : Fin 2), ∀ t ∈ Set.Icc (0:ℝ) T, ∀ x ∈ W,
      hs₁.obsVel j t x = hs₂.obsVel j t x := by
    intro j
    have hspace : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)),
        ∀ x ∈ W, hs₁.obsVel j t x = hs₂.obsVel j t x := by
      filter_upwards [hvel j] with t hts
      exact forall_eq_of_ae_eq_open (μ := (volume : Measure Torus2)) hW
        (hs₁.continuous_obsVel_space j t) (hs₂.continuous_obsVel_space j t) hts
    intro t ht x hx
    refine forall_eq_of_ae_eq_time hT (hs₁.continuous_obsVel j x) (hs₂.continuous_obsVel j x)
      ?_ t ht
    filter_upwards [hspace] with s hs
    exact hs x hx
  constructor
  · intro t x hx
    have h := hstate' (t : ℝ) t.2 x hx
    rw [IsSobolevSolution.obsState, IsSobolevSolution.obsState, hc₁, hc₂,
      curveState_coe hT.le _ t, curveState_coe hT.le _ t] at h
    exact h
  · intro j t x hx
    have h := hvel' j (t : ℝ) t.2 x hx
    rw [IsSobolevSolution.obsVel, IsSobolevSolution.obsVel, hc₁, hc₂,
      curveState_coe hT.le _ t, curveState_coe hT.le _ t] at h
    exact h


/-! ## 5. Recovery from the Sobolev measurement -/

/-- **Operator recovery from the physical Sobolev measurement.**  Hypotheses, all explicit: the
geometry (`IsOpen W`, a nonempty exterior), the genuine kernel assumptions, the forward
existence/regularity input `SobolevExistence`, the Sobolev measurement equality, and the
portable `FractionalUCP α W`.  Nothing about approximation, target identities, state convergence
or equality to `sourceSolution` is assumed. -/
theorem rotatedGradientSymbol_eq_of_sobolev (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hE : ((closure W)ᶜ).Nonempty) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖rotatedGradientSymbol κ₁ j k‖ ≤ C₁)
    (hC₂ : ∀ j k, ‖rotatedGradientSymbol κ₂ j k‖ ≤ C₂)
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hex₁ : ∃ ε > 0, SobolevExistence hα hT.le hm₁ (smoothSources hT W) ε)
    (hex₂ : ∃ ε > 0, SobolevExistence hα hT.le hm₂ (smoothSources hT W) ε)
    (hobs : ∃ ε > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε) :
    rotatedGradientSymbol κ₁ = rotatedGradientSymbol κ₂ :=
  rotatedGradientSymbol_eq_of_measured hα hT hW hE hUCP hm₁ hr₁ hm₂ hr₂ hC hτ0 hτT
    (exists_measuredMapsAgreeOn_of_sobolev hα hT hW hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ _ hex₁ hex₂ hobs)

/-- **The paper-shaped exterior corollary from the Sobolev measurement.**  For every input `ψ`
and every exterior point `x ∉ closure W`, the two velocity fields agree at `x`.  No separate
nonempty-exterior hypothesis is imposed: the exterior point supplies it. -/
theorem paper_exterior_velocity_eq_sobolev (hα : 1 / 2 < α) {T : ℝ} (hT : 0 < T)
    {W : Set Torus2} (hW : IsOpen W) (hUCP : FractionalUCP α W)
    {κ₁ κ₂ : Gam → ℂ}
    (hm₁ : IsBddSymbol (rotatedGradientSymbol κ₁))
    (hr₁ : IsRealSymbol (rotatedGradientSymbol κ₁))
    (hm₂ : IsBddSymbol (rotatedGradientSymbol κ₂))
    (hr₂ : IsRealSymbol (rotatedGradientSymbol κ₂))
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖rotatedGradientSymbol κ₁ j k‖ ≤ C₁)
    (hC₂ : ∀ j k, ‖rotatedGradientSymbol κ₂ j k‖ ≤ C₂)
    {C : ℝ} (hC : ∀ j k, ‖(rotatedGradientSymbol κ₁ - rotatedGradientSymbol κ₂) j k‖ ≤ C)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ ≤ T)
    (hex₁ : ∃ ε > 0, SobolevExistence hα hT.le hm₁ (smoothSources hT W) ε)
    (hex₂ : ∃ ε > 0, SobolevExistence hα hT.le hm₂ (smoothSources hT W) ε)
    (hobs : ∃ ε > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ (smoothSources hT W) ε)
    (ψ : Wiener1) (j : Fin 2) {x : Torus2} (hx : x ∈ (closure W)ᶜ) :
    synth (velocity (rotatedGradientSymbol κ₁) hm₁ j (incl ψ)) x
      = synth (velocity (rotatedGradientSymbol κ₂) hm₂ j (incl ψ)) x := by
  have heq := rotatedGradientSymbol_eq_of_sobolev hα hT hW ⟨x, hx⟩ hUCP hm₁ hr₁ hm₂ hr₂
    hC₁ hC₂ hC hτ0 hτT hex₁ hex₂ hobs
  rw [velocity_congr hm₁ hm₂ heq j]

/-! ## 6. The observed velocity of an integrable paper kernel -/

/-- **The observed velocity is the genuine convolution with the paper's integrable kernel.**
For a kernel `K ∈ L¹(𝕋²)` with a bounded Fourier symbol — the paper's class, not merely a
smooth `A¹` kernel — the observed velocity of a Sobolev solution is `∇^⊥(K ⋆ θ)` with the
convolution taken as an actual integral over the torus and the derivative as an actual
directional derivative. -/
theorem IsSobolevSolution.obsVel_integrableKernel {K : Torus2 → ℂ} {A : ℝ}
    (hK : Integrable K (volume : Measure Torus2)) (hA : KernelBound (kernelCoeff K) A)
    {hα : 1 / 2 < α} {hT : 0 ≤ T} {M : ℝ} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsSobolevSolution hα hT (rotatedGradientSymbol_bdd ⟨A, hA⟩) M f θ) (t : ℝ)
    (x : Torus2) :
    h.obsVel 0 t x
        = -(deriv (fun s : ℝ =>
            torusConv K (synth (incl (curveState hT h.curve t))) (torusShift x 1 s)) 0)
      ∧ h.obsVel 1 t x
        = deriv (fun s : ℝ =>
            torusConv K (synth (incl (curveState hT h.curve t))) (torusShift x 0 s)) 0 :=
  ⟨velocity_integrableKernel_zero hK hA (curveState hT h.curve t) x,
    velocity_integrableKernel_one hK hA (curveState hT h.curve t) x⟩

end LiWang.Formalization
