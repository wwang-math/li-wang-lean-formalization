/-
# The paper-facing `s = 3` solution class

`IsPaperSolution` is the Li–Wang solution class of Proposition 3.1 at `s = 3`, written on the
packet's own objects:

* the state is a function `[0,T] → L²(𝕋²)` (extended to `ℝ`; only its values on `[0,T]` are
  used, and `sobClamp` makes that precise);
* each of its Fourier coordinates is continuous in time on `[0,T]` — this is the selection of
  the representative, and it is what makes the initial trace and the observations pointwise
  statements rather than a.e. ones.  It is weaker than continuity in the `L²(𝕋²)` norm, which is
  what the constructed solution has;
* it is real, vanishes at `t = 0`, and satisfies the time-integrated weak active-scalar
  equation tested against trigonometric polynomials;
* it lies in `L^∞(0,T;H³) ∩ L²(0,T;H^{3+α}) ∩ L^∞(0,T;L^q)` with `0 < 1/q < α − 1/2`;
* the paper's standing upper bound `α < 1` is recorded as a field, because it is what makes
  `H⁴ ⊂ H^{3+α}` in the existence direction.

The predicate contains **no** `Curve1`, no `A¹` datum, no equality to `sourceSolution`, no
certificate and no part of the inverse conclusion.  The `A¹` state used to express the
nonlinear term of the weak equation is `paperState`, which is *derived* from the state and the
`H³` bound through the proved embedding of `SobolevEmbedding.lean`.

Both directions are proved:

* `isPaperSolution_mild` — the constructed small-source solution is a paper solution;
* `IsPaperSolution.isSobolevSolution` — a paper solution is a v8.0 Sobolev solution (after the
  already-checked clamp and representative construction), with equality in `L²(𝕋²)` at every
  time of `[0,T]`.

Part of `LiWangFormalizationPaperMapAlignmentPacket` v9.0.
-/
import LiWangFormalization.PaperEnergy
import LiWangFormalization.SobolevExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. Continuity of the Fourier coordinates -/

theorem continuous_l2coeff (k : Gam) : Continuous (l2coeff k) :=
  (innerSL ℂ (synthL2 (wdirac k))).continuous

/-- Continuity in the `L²(𝕋²)` norm implies continuity of every Fourier coordinate; the paper
class asks only for the latter. -/
theorem coeff_continuousOn_of_continuousOn {T : ℝ} {θ : ℝ → TorusL2}
    (h : ContinuousOn θ (Set.Icc (0:ℝ) T)) (k : Gam) :
    ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T) :=
  (continuous_l2coeff k).comp_continuousOn h

/-! ## 2. The `A¹` state attached to an interval-local `H³` bound -/

/-- The `A¹` element of the state at one time, built from the `H³` bound on `[0,T]` and the
clamp.  It is a function of the state alone: the bound is a `Prop`. -/
noncomputable def paperState (hT : 0 ≤ T) {M : ℝ} {θ : ℝ → TorusL2}
    (hb : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) (t : ℝ) : Wiener1 :=
  sobToWiener1 (summable_of_finset_sum_le
    (fun k => sob_nonneg (fun j => l2coeff j (θ ((clampT hT t : TimeI T) : ℝ))) k)
    (hb _ (clampT hT t).2))

@[simp] theorem paperState_coeff (hT : 0 ≤ T) {M : ℝ} {θ : ℝ → TorusL2}
    (hb : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) (t : ℝ) (k : Gam) :
    (paperState hT hb t).coeff k = l2coeff k (θ ((clampT hT t : TimeI T) : ℝ)) := rfl

theorem paperState_of_mem (hT : 0 ≤ T) {M : ℝ} {θ : ℝ → TorusL2}
    (hb : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T)
    (k : Gam) : (paperState hT hb t).coeff k = l2coeff k (θ t) := by
  rw [paperState_coeff, clampT_coe hT ht.1 ht.2]

/-! ## 3. The paper solution class -/

/-- **A Li–Wang solution at `s = 3`.**  Every field is a property of the `L²(𝕋²)`-valued state;
nothing about the packet's construction appears. -/
structure IsPaperSolution (hα : 1 / 2 < α) (hT : 0 < T) (hm : IsBddSymbol m)
    (M N K : ℝ) (f : Curve0 T) (θ : ℝ → TorusL2) : Prop where
  /-- The paper's standing upper bound on the dissipation exponent. -/
  alpha_lt_one : α < 1
  /-- Each Fourier coordinate is continuous in time on the closed interval — weak-`L²` time
  continuity.  This is the selection of the representative; it is not imposed on an arbitrary
  a.e. modification, and it is **weaker** than continuity in the `L²(𝕋²)` norm (which is what
  the constructed solution actually has, see `coeff_continuousOn_of_continuousOn`). -/
  coeff_continuous : ∀ k : Gam, ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T)
  /-- The state is real. -/
  real : ∀ t ∈ Set.Icc (0:ℝ) T, ConjSymmetric fun k : Gam => l2coeff k (θ t)
  /-- Zero initial trace, in `L²(𝕋²)`. -/
  initial : θ 0 = 0
  /-- `θ ∈ L^∞(0,T; H³(𝕋²))`, on finite partial sums. -/
  energy3 : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam,
    (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M
  /-- The `H^{3+α}` energy is a genuine convergent sum at almost every time — exactly the
  almost-everywhere membership that `θ ∈ L²(0,T;H^{3+α})` carries.  Without this field the next
  one would be vacuously satisfiable, because Lean's `tsum` is `0` on a non-summable family:
  `tsum = 0` must never be read as evidence of summability. -/
  sob3a : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
    MemSobolev (3 + α) (fun k => l2coeff k (θ t))
  /-- `θ ∈ L²(0,T; H^{3+α}(𝕋²))`. -/
  energy3a : (∫⁻ t in Set.Ioc (0:ℝ) T,
      ENNReal.ofReal (sobEnergy (3 + α) (fun k => l2coeff k (θ t)))) ≤ ENNReal.ofReal N
  /-- `θ ∈ L^∞(0,T; L^q(𝕋²))` for the admissible exponent `q = paperExp α`, as an **essential**
  supremum. -/
  lq : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
    eLpNorm ((θ t : Torus2 → ℂ)) (ENNReal.ofReal (paperExp α)) (volume : Measure Torus2)
      ≤ ENNReal.ofReal K
  /-- The time-integrated weak active-scalar equation. -/
  weak : ∀ (F : Finset Gam) (c : Gam → ℂ), ∀ t ∈ Set.Icc (0:ℝ) T,
    spacePair (incl (paperState hT.le energy3 t)) (trigPoly F c)
      + (∫ s in (0:ℝ)..t, spacePair (incl (paperState hT.le energy3 s)) (fracLapPoly α F c))
      + (∫ s in (0:ℝ)..t,
          spacePair (transport m hm (paperState hT.le energy3 s) (paperState hT.le energy3 s))
            (trigPoly F c))
      = ∫ s in (0:ℝ)..t, spacePair (sourceFun hT.le f s) (trigPoly F c)

namespace IsPaperSolution

variable {hα : 1 / 2 < α} {hT : 0 < T} {hm : IsBddSymbol m} {M N K : ℝ} {f : Curve0 T}
  {θ : ℝ → TorusL2}

/-- The paper's exponent inequality, as carried by the class: `q = paperExp α` is a genuine
Lebesgue exponent (`q > 4`) and satisfies `0 < 1/q < α − 1/2`. -/
theorem exp_admissible (h : IsPaperSolution hα hT hm M N K f θ) :
    4 < paperExp α ∧ 0 < 1 / paperExp α ∧ 1 / paperExp α < α - 1 / 2 :=
  ⟨four_lt_paperExp hα h.alpha_lt_one, inv_paperExp_pos hα, inv_paperExp_lt hα⟩

theorem coeff_continuousOn (h : IsPaperSolution hα hT hm M N K f θ) (k : Gam) :
    ContinuousOn (fun t : ℝ => l2coeff k (θ t)) (Set.Icc (0:ℝ) T) := h.coeff_continuous k

theorem energy3_ae (h : IsPaperSolution hα hT hm M N K f θ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0:ℝ) T →
      ∀ F : Finset Gam, (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (θ t)‖ ^ 2) ≤ M := by
  filter_upwards with t ht using h.energy3 t ht

/-- **The `H^{3+α}` energy is almost-everywhere measurable in time**, derived from the `L²`
continuity of the state and the summability field — not assumed. -/
theorem aemeasurable_energy (h : IsPaperSolution hα hT hm M N K f θ) :
    AEMeasurable (fun t : ℝ => ENNReal.ofReal (sobEnergy (3 + α) (fun k => l2coeff k (θ t))))
      ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)) :=
  aemeasurable_sobEnergy_of_continuousOn h.coeff_continuousOn h.sob3a

/-- **A paper solution is a v8.0 Sobolev solution.**  The state is the same `L²(𝕋²)` function on
`[0,T]`; only the clamped extension is taken, which changes nothing there. -/
theorem isSobolevSolution (h : IsPaperSolution hα hT hm M N K f θ) :
    IsSobolevSolution hα hT.le hm M f (sobClamp hT.le θ) :=
  isSobolevSolution_sobClamp hα hT hm h.coeff_continuousOn h.real h.energy3_ae h.initial
    h.weak

/-- The `A¹` representative of a paper solution represents it in `L²(𝕋²)` at every time. -/
theorem synthL2_curveState (h : IsPaperSolution hα hT hm M N K f θ) {s : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) T) :
    synthL2 (incl (curveState hT.le h.isSobolevSolution.curve s)) = θ s :=
  synthL2_curveState_sobClamp h.isSobolevSolution hs

/-- **The state of a paper solution is continuous in the `L²(𝕋²)` norm** on `[0,T]`.  So the
weak-`L²` continuity field, together with the uniform `H³` bound, already forces norm
continuity: the two formulations of the representative-selection hypothesis agree inside the
class. -/
theorem continuousOn' {T : ℝ} {hT : 0 < T} {f : Curve0 T} {θ : ℝ → TorusL2}
    (h : IsPaperSolution hα hT hm M N K f θ) : ContinuousOn θ (Set.Icc (0:ℝ) T) := by
  have hcont : Continuous fun s : ℝ =>
      synthL2 (incl (curveState hT.le h.isSobolevSolution.curve s)) :=
    (synthL2.continuous.comp incl.continuous).comp
      (continuous_curveState hT.le h.isSobolevSolution.curve)
  exact hcont.continuousOn.congr (fun s hs => (h.synthL2_curveState hs).symm)

/-- **Uniqueness inside the paper class**, by the v8.0 uniqueness theorem. -/
theorem unique (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {M₁ N₁ K₁ M₂ N₂ K₂ : ℝ} {θ₁ θ₂ : ℝ → TorusL2}
    (h₁ : IsPaperSolution hα hT hm M₁ N₁ K₁ f θ₁)
    (h₂ : IsPaperSolution hα hT hm M₂ N₂ K₂ f θ₂) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    θ₁ s = θ₂ s := by
  have := sobolev_solution_unique hr hC h₁.isSobolevSolution h₂.isSobolevSolution hs
  rwa [sobClamp_of_mem hT.le θ₁ hs, sobClamp_of_mem hT.le θ₂ hs] at this

/-- **The nonzero-mean balance is proved for the class, not assumed.** -/
theorem mean_balance {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hr : IsRealSymbol (rotatedGradientSymbol κ))
    (h : IsPaperSolution hα hT (rotatedGradientSymbol_bdd hb) M N K f θ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    l2coeff 0 (θ t) = ∫ s in (0:ℝ)..t, (sourceFun hT.le f s) 0 := by
  have := h.isSobolevSolution.mean_balance hb hr ht
  rwa [sobClamp_of_mem hT.le θ ht] at this

end IsPaperSolution

/-! ## 4. The constructed small-source solution is a paper solution -/

section Mild

variable {hα : 1 / 2 < α} {hm : IsBddSymbol m} {hr : IsRealSymbol m}

theorem curveState_clamp (hT : 0 ≤ T) (v : Curve1 T) (s : ℝ) :
    curveState hT v ((clampT hT s : TimeI T) : ℝ) = curveState hT v s := by
  rw [curveState_coe hT v (clampT hT s)]
  rfl

theorem continuous_mildPhysState (hT : 0 ≤ T) (u : Curve1 T) :
    Continuous (mildPhysState hT u) :=
  (synthL2.continuous.comp incl.continuous).comp (continuous_curveState hT u)

/-- **The constructed small-source mild solution is a Li–Wang solution at `s = 3`.**  Each of
the three memberships of Proposition 3.1 is proved: `L^∞_t H³` and `L²_t H^{3+α}` from the
`wt⁴` bootstrap, and `L^∞_t L^q` from the `A¹ ⊂ C(𝕋²)` representative on a probability space. -/
theorem isPaperSolution_mild (hα1 : α < 1) (hT : 0 < T) {f : Curve0 T} {u : Curve1 T} {R4 : ℝ}
    (hmild : u + sourceQuad hα hT.le m hm hr u u = duhamelOp hα hT.le f)
    (h4 : ∀ t ∈ Set.Icc (0:ℝ) T, WB 4 R4 (curveState hT.le u t).coeff) :
    IsPaperSolution hα hT hm (R4 ^ 2) (T * R4 ^ 2) ‖u‖ f (mildPhysState hT.le u) := by
  have h4all : ∀ t : ℝ, WB 4 R4 (curveState hT.le u t).coeff := WB_curveState_all h4
  have h3 : ∀ t ∈ Set.Icc (0:ℝ) T, WB 3 R4 (curveState hT.le u t).coeff :=
    fun t ht => (h4 t ht).mono_exp (by norm_num)
  have hsol : IsSobolevSolution hα hT.le hm (R4 ^ 2) f (mildPhysState hT.le u) :=
    isSobolevSolution_mild hmild h3
  have henergy3 : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset Gam,
      (∑ k ∈ F, rho k ^ 3 * ‖l2coeff k (mildPhysState hT.le u t)‖ ^ 2) ≤ R4 ^ 2 :=
    fun t _ => hsol.bound t
  refine ⟨hα1,
    coeff_continuousOn_of_continuousOn (continuous_mildPhysState hT.le u).continuousOn,
    fun t _ => hsol.real t,
    hsol.initial, henergy3, ?_, ?_, ?_, ?_⟩
  · -- the `H^{3+α}` energy converges (at every time, hence almost everywhere)
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := T))] with t ht
    have hmem := memSobolev_of_WB4 hα1.le (h4 t ⟨ht.1.le, ht.2⟩)
    refine hmem.congr (fun k => ?_)
    simp only [l2coeff_mildPhysState]
  · -- `L²(0,T;H^{3+α})`
    have hle := lintegral_sobEnergy_le (hT := hT.le) hα1.le h4
    refine le_trans (le_of_eq ?_) hle
    refine lintegral_congr (fun t => ?_)
    congr 2
    funext k
    rw [l2coeff_mildPhysState]
  · -- `L^∞(0,T;L^q)`
    filter_upwards with t
    refine le_trans (eLpNorm_synthL2_le _ (incl (curveState hT.le u t))) ?_
    exact ENNReal.ofReal_le_ofReal
      (le_trans (norm_incl_apply_le _) (norm_curveState_le hT.le u t))
  · -- the weak equation, transported through the identification of the two `A¹` states
    have hstate : ∀ s : ℝ, paperState hT.le henergy3 s = curveState hT.le u s := by
      intro s
      refine Wiener1.coeff_injective (funext fun k => ?_)
      rw [paperState_coeff, l2coeff_mildPhysState, curveState_clamp]
    have hsob : ∀ s : ℝ, sobState hsol.bound s = curveState hT.le u s := by
      intro s
      exact Wiener1.coeff_injective (funext fun k => by
        rw [sobState_coeff, l2coeff_mildPhysState])
    intro F c t ht
    have hw := hsol.weak F c t ht
    simp only [hsob] at hw
    simp only [hstate]
    exact hw

end Mild

end LiWang.Formalization
