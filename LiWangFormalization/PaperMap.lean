/-
# The canonical paper-facing source-to-solution map

Li–Wang state their inverse problem as equality of the **maps**

```
    L_ℛ : f ↦ (θ|_{W×(0,T)}, ℛ(θ)|_{W×(0,T)}) .                              (1.6)
```

The v8.0 hypothesis `SobolevObsAgreeOn` is a *relation* between solution predicates: it
universally quantifies over all pairs of solutions.  This module formalizes the difference and
proves that the map form implies the relation form.

* `PaperExistence` — existence of a paper solution on a ball of admissible sources.  It is a
  hypothesis of the definitions below, **not** hidden inside them; it is discharged by
  `PaperAlignment.lean` for the smooth source class.
* `paperSol` — the canonical solution selected from that existence by `Classical.choose`, and
  `paperObsState`, `paperObsVel` — its two observations, as a.e. objects (elements of
  `L²(𝕋²)`).
* `paperSol_eq`, `paperObsVel_eq` — **single-valuedness**: the canonical observations do not
  depend on the chosen witness, because two paper solutions of the same source agree
  (`IsPaperSolution.unique`, i.e. the v8.0 uniqueness theorem).  Uniqueness is used, not
  assumed.
* `PaperObsMapsAgree` — equality of the two canonical maps.
* `sobolevObsAgreeOn_of_paperMapsAgree` — the map equality implies the v8.0 relation
  hypothesis, at the same radius and in the same `Curve0 T` norm.

Part of `LiWangFormalizationPaperMapAlignmentPacket` v9.0.
-/
import LiWangFormalization.PaperSolution
import LiWangFormalization.SobolevObservation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. Existence on a ball, and the canonical selection -/

/-- **Existence of a paper solution** for every source of the admissible family with small
`Curve0 T` norm.  The witness is bundled so that a canonical one can be selected. -/
def PaperExistence (hα : 1 / 2 < α) (hT : 0 < T) (hm : IsBddSymbol m)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ) : Prop :=
  ∀ f ∈ A, ‖f‖ < ε →
    ∃ p : (ℝ → TorusL2) × ℝ × ℝ × ℝ, IsPaperSolution hα hT hm p.2.1 p.2.2.1 p.2.2.2 f p.1

/-- Two Sobolev solutions with the same `L²` values on `[0,T]` have the same `A¹`
representative at every time. -/
theorem curveState_congr {hα' : 1 / 2 < α} {hT' : 0 ≤ T} {hm' : IsBddSymbol m}
    {M₁ M₂ : ℝ} {f : Curve0 T} {θ₁ θ₂ : ℝ → TorusL2}
    (h₁ : IsSobolevSolution hα' hT' hm' M₁ f θ₁) (h₂ : IsSobolevSolution hα' hT' hm' M₂ f θ₂)
    (heq : ∀ s ∈ Set.Icc (0:ℝ) T, θ₁ s = θ₂ s) (t : ℝ) :
    curveState hT' h₁.curve t = curveState hT' h₂.curve t := by
  refine Wiener1.coeff_injective (funext fun k => ?_)
  show (h₁.curve (clampT hT' t)).val.coeff k = (h₂.curve (clampT hT' t)).val.coeff k
  rw [h₁.curve_coeff, h₂.curve_coeff, heq _ (clampT hT' t).2]

variable {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m} {A : Submodule ℝ (Curve0 T)} {ε : ℝ}

/-- The chosen witness: a state together with its three energy constants. -/
noncomputable def paperWitness (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) : (ℝ → TorusL2) × ℝ × ℝ × ℝ :=
  Classical.choose (hex f hf hs)

theorem paperWitness_spec (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) :
    IsPaperSolution hα hT hm (paperWitness hex hf hs).2.1 (paperWitness hex hf hs).2.2.1
      (paperWitness hex hf hs).2.2.2 f (paperWitness hex hf hs).1 :=
  Classical.choose_spec (hex f hf hs)

/-- **The canonical paper solution** of an admissible small source.  It is canonical on `[0,T]`,
which is where the class constrains the state and where `paperSol_eq` proves independence of the
chosen witness; outside `[0,T]` its values are witness-dependent and are never used. -/
noncomputable def paperSol (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) : ℝ → TorusL2 := (paperWitness hex hf hs).1

theorem isPaperSolution_paperSol (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) :
    IsPaperSolution hα hT hm (paperWitness hex hf hs).2.1 (paperWitness hex hf hs).2.2.1
      (paperWitness hex hf hs).2.2.2 f (paperSol hex hf hs) :=
  paperWitness_spec hex hf hs

/-! ## 2. The two observations, and their independence of the witness -/

/-- **The observed state**, as an a.e. object: the `L²(𝕋²)` class itself.  Canonical on `[0,T]`
(see `paperSol`). -/
noncomputable def paperObsState (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) (t : ℝ) : TorusL2 := paperSol hex hf hs t

/-- **The observed velocity**, as an a.e. object: the `L²(𝕋²)` class of `ℛ_m(θ(t))_j`. -/
noncomputable def paperObsVel (hex : PaperExistence hα hT hm A ε) {f : Curve0 T}
    (hf : f ∈ A) (hs : ‖f‖ < ε) (j : Fin 2) (t : ℝ) : TorusL2 :=
  synthL2 (velocity m hm j
    (incl (curveState hT.le (isPaperSolution_paperSol hex hf hs).isSobolevSolution.curve t)))

/-- **Single-valuedness of the canonical state observation.** -/
theorem paperSol_eq (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (hex : PaperExistence hα hT hm A ε) {f : Curve0 T} (hf : f ∈ A) (hs : ‖f‖ < ε)
    {M N K : ℝ} {θ : ℝ → TorusL2} (h : IsPaperSolution hα hT hm M N K f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) : paperSol hex hf hs t = θ t :=
  IsPaperSolution.unique hr hC (isPaperSolution_paperSol hex hf hs) h ht

/-- **Single-valuedness of the canonical velocity observation.** -/
theorem paperObsVel_eq (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (hex : PaperExistence hα hT hm A ε) {f : Curve0 T} (hf : f ∈ A) (hs : ‖f‖ < ε)
    {M N K : ℝ} {θ : ℝ → TorusL2} (h : IsPaperSolution hα hT hm M N K f θ)
    (j : Fin 2) (t : ℝ) :
    paperObsVel hex hf hs j t
      = synthL2 (velocity m hm j (incl (curveState hT.le h.isSobolevSolution.curve t))) := by
  have heq : ∀ s ∈ Set.Icc (0:ℝ) T,
      sobClamp hT.le (paperSol hex hf hs) s = sobClamp hT.le θ s := by
    intro s hs'
    rw [sobClamp_of_mem hT.le _ hs', sobClamp_of_mem hT.le _ hs']
    exact paperSol_eq hr hC hex hf hs h hs'
  rw [paperObsVel, curveState_congr (isPaperSolution_paperSol hex hf hs).isSobolevSolution
    h.isSobolevSolution heq t]

/-- The canonical velocity observation is represented by the packet's pointwise observation. -/
theorem paperObsVel_ae (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    (hex : PaperExistence hα hT hm A ε) {f : Curve0 T} (hf : f ∈ A) (hs : ‖f‖ < ε)
    {M N K : ℝ} {θ : ℝ → TorusL2} (h : IsPaperSolution hα hT hm M N K f θ)
    (j : Fin 2) (t : ℝ) :
    ((paperObsVel hex hf hs j t : Torus2 → ℂ))
      =ᵐ[(volume : Measure Torus2)] fun x => h.isSobolevSolution.obsVel j t x := by
  rw [paperObsVel_eq hr hC hex hf hs h j t]
  exact synthL2_apply_ae _

/-! ## 3. Equality of the two canonical maps -/

/-- **Equality of the paper's source-to-solution maps** on the ball of admissible sources: the
state and the velocity agree almost everywhere on the open cylinder `W × (0,T)`. -/
def PaperObsMapsAgree (hα : 1 / 2 < α) (hT : 0 < T) (W : Set Torus2)
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hm₂ : IsBddSymbol m₂)
    (A : Submodule ℝ (Curve0 T)) (ε : ℝ)
    (hex₁ : PaperExistence hα hT hm₁ A ε) (hex₂ : PaperExistence hα hT hm₂ A ε) : Prop :=
  ∀ (f : Curve0 T) (hf : f ∈ A) (hs : ‖f‖ < ε),
      (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)),
          ∀ᵐ x ∂((volume : Measure Torus2).restrict W),
            (paperObsState hex₁ hf hs t : Torus2 → ℂ) x
              = (paperObsState hex₂ hf hs t : Torus2 → ℂ) x)
    ∧ (∀ j : Fin 2, ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)),
          ∀ᵐ x ∂((volume : Measure Torus2).restrict W),
            (paperObsVel hex₁ hf hs j t : Torus2 → ℂ) x
              = (paperObsVel hex₂ hf hs j t : Torus2 → ℂ) x)

/-- **From equality of the paper maps to the v8.0 measurement relation.**  Existence supplies
the canonical solutions and uniqueness identifies every other solution with them, so the
relation form follows from the map form — at **exactly the same radius** `ε`, in the same
`Curve0 T` norm. -/
theorem sobolevObsAgreeOn_of_paperMapsAgree {W : Set Torus2}
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁) (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    (hex₁ : PaperExistence hα hT hm₁ A ε) (hex₂ : PaperExistence hα hT hm₂ A ε)
    (hagree : PaperObsMapsAgree hα hT W hm₁ hm₂ A ε hex₁ hex₂) :
    SobolevObsAgreeOn hα hT.le W hm₁ hm₂ A ε := by
  intro f hf hsmall M₁ M₂ θ₁ θ₂ h₁ h₂
  -- the canonical solutions
  set p₁ := isPaperSolution_paperSol hex₁ hf hsmall with hp₁
  set p₂ := isPaperSolution_paperSol hex₂ hf hsmall with hp₂
  -- every Sobolev solution agrees with the canonical one on `[0,T]`
  have hq₁ : ∀ s ∈ Set.Icc (0:ℝ) T, θ₁ s = paperSol hex₁ hf hsmall s := by
    intro s hs
    have := sobolev_solution_unique hr₁ hC₁ h₁ p₁.isSobolevSolution hs
    rwa [sobClamp_of_mem hT.le _ hs] at this
  have hq₂ : ∀ s ∈ Set.Icc (0:ℝ) T, θ₂ s = paperSol hex₂ hf hsmall s := by
    intro s hs
    have := sobolev_solution_unique hr₂ hC₂ h₂ p₂.isSobolevSolution hs
    rwa [sobClamp_of_mem hT.le _ hs] at this
  obtain ⟨hstate, hvel⟩ := hagree f hf hsmall
  constructor
  · -- the state observation
    have hIoo := self_mem_ae_restrict
      (measurableSet_Ioo (a := (0:ℝ)) (b := T)) (μ := (volume : Measure ℝ))
    filter_upwards [hstate, hIoo] with t ht htmem
    have hmem : t ∈ Set.Icc (0:ℝ) T := ⟨htmem.1.le, htmem.2.le⟩
    rw [hq₁ t hmem, hq₂ t hmem]
    exact ht
  · -- the velocity observation
    intro j
    have hIoo := self_mem_ae_restrict
      (measurableSet_Ioo (a := (0:ℝ)) (b := T)) (μ := (volume : Measure ℝ))
    filter_upwards [hvel j, hIoo] with t ht htmem
    have hmem : t ∈ Set.Icc (0:ℝ) T := ⟨htmem.1.le, htmem.2.le⟩
    -- identify each canonical velocity with the corresponding packet observation
    have hc₁ : curveState hT.le h₁.curve t
        = curveState hT.le p₁.isSobolevSolution.curve t := by
      refine curveState_congr h₁ p₁.isSobolevSolution (fun s hs => ?_) t
      rw [sobClamp_of_mem hT.le _ hs]
      exact hq₁ s hs
    have hc₂ : curveState hT.le h₂.curve t
        = curveState hT.le p₂.isSobolevSolution.curve t := by
      refine curveState_congr h₂ p₂.isSobolevSolution (fun s hs => ?_) t
      rw [sobClamp_of_mem hT.le _ hs]
      exact hq₂ s hs
    have hae₁ := synthL2_apply_ae
      (velocity m₁ hm₁ j (incl (curveState hT.le p₁.isSobolevSolution.curve t)))
    have hae₂ := synthL2_apply_ae
      (velocity m₂ hm₂ j (incl (curveState hT.le p₂.isSobolevSolution.curve t)))
    have hres₁ : ∀ᵐ x ∂((volume : Measure Torus2).restrict W),
        (paperObsVel hex₁ hf hsmall j t : Torus2 → ℂ) x
          = synth (velocity m₁ hm₁ j (incl (curveState hT.le p₁.isSobolevSolution.curve t))) x :=
      ae_restrict_of_ae hae₁
    have hres₂ : ∀ᵐ x ∂((volume : Measure Torus2).restrict W),
        (paperObsVel hex₂ hf hsmall j t : Torus2 → ℂ) x
          = synth (velocity m₂ hm₂ j (incl (curveState hT.le p₂.isSobolevSolution.curve t))) x :=
      ae_restrict_of_ae hae₂
    filter_upwards [ht, hres₁, hres₂] with x hx hx₁ hx₂
    show h₁.obsVel j t x = h₂.obsVel j t x
    rw [IsSobolevSolution.obsVel, IsSobolevSolution.obsVel, hc₁, hc₂, ← hx₁, ← hx₂]
    exact hx

/-- The existential form the downstream recovery machinery consumes. -/
theorem exists_sobolevObsAgreeOn_of_paperMapsAgree {W : Set Torus2}
    {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    {C₁ C₂ : ℝ} (hC₁ : ∀ j k, ‖m₁ j k‖ ≤ C₁) (hC₂ : ∀ j k, ‖m₂ j k‖ ≤ C₂)
    (hε : 0 < ε)
    (hex₁ : PaperExistence hα hT hm₁ A ε) (hex₂ : PaperExistence hα hT hm₂ A ε)
    (hagree : PaperObsMapsAgree hα hT W hm₁ hm₂ A ε hex₁ hex₂) :
    ∃ ε' > 0, SobolevObsAgreeOn hα hT.le W hm₁ hm₂ A ε' :=
  ⟨ε, hε, sobolevObsAgreeOn_of_paperMapsAgree hm₁ hr₁ hm₂ hr₂ hC₁ hC₂ hex₁ hex₂ hagree⟩

end LiWang.Formalization
