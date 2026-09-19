/-
# The physical solution predicate and the comparison theorem

Step 3(b) of the v7.0 physical bridge.

`IsPhysicalSolution` is a *physically meaningful* solution concept:

* **function-space regularity** — `θ : Curve1 T`, i.e. `θ ∈ C([0,T]; A¹(𝕋²))`, the
  Wiener algebra with one derivative; in particular `θ(t) ∈ L²(𝕋²)` for every `t` and
  `R(θ)·∇θ` is a genuine continuous function of `x`;
* **initial trace** — `θ(0) = 0`, a genuine trace, since `θ` is continuous in time;
* **the equation** — the time-integrated weak formulation tested against trigonometric
  polynomials, with the fractional Laplacian moved onto the test function.  Every term is an
  actual integral over `𝕋² × (0,t)` (`spacePair a P = ∫_{𝕋²} (synth a)(x) P(x) dx`).

The predicate mentions neither `sourceSolution`, nor any certificate, nor any part of the
conclusion of the inverse theorem.  It is exactly the standard distributional formulation of

  `∂_t θ + R(θ)·∇θ + (-Δ)^α θ = f,  θ(0) = 0`

integrated once in time.

The two main theorems are:

* `isPhysicalSolution_of_mild` — the constructed mild state **is** a physical solution, so the
  class is nonempty and contains the object the inverse problem is built on;
* `mild_of_isPhysicalSolution` — conversely, **every** physical solution satisfies the mild
  equation.  This is a genuine converse: the Fourier coefficients are extracted from the
  physical weak formulation by single-mode test polynomials, and the resulting scalar
  integrated identity is inverted by `integrated_equation_converse`, an actual scalar ODE
  uniqueness argument.

Combining them with the unconditional `mild_curve_unique` gives
`physical_solution_unique`: a physical solution of a given source is unique, with **no**
smallness hypothesis of any kind.

Part of `LiWangFormalizationPhysicalPDEBridgePacket` v7.0.
-/
import LiWangFormalization.PhysicalWeak
import LiWangFormalization.MildUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## 1. The scalar converse of the integrated equation -/

/-- **The converse of `integrated_equation`.**  A continuous function satisfying the
time-integrated linear equation on `[0,T]` *is* the scalar Duhamel integral.  The proof is a
genuine ODE uniqueness argument: the difference `d` of the two solutions satisfies
`d = -λ ∫₀ᵗ d`, so the integrating factor `e^{λt}∫₀ᵗ d` has vanishing derivative on `[0,T]`
and therefore vanishes identically. -/
theorem integrated_equation_converse {T lam : ℝ} {w g : ℝ → ℂ} (hw : Continuous w)
    (hg : Continuous g)
    (heq : ∀ t ∈ Set.Icc (0:ℝ) T,
      w t + (lam : ℂ) * (∫ s in (0:ℝ)..t, w s) = ∫ s in (0:ℝ)..t, g s)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    w t = scalarDuhamel lam g t := by
  set W : ℝ → ℂ := scalarDuhamel lam g with hWdef
  have hWderiv : ∀ s : ℝ, HasDerivAt W (g s - (lam : ℂ) * W s) s := fun s =>
    hasDerivAt_scalarDuhamel lam hg s
  have hWcont : Continuous W :=
    continuous_iff_continuousAt.2 fun s => (hWderiv s).continuousAt
  have hW0 : W 0 = 0 := by
    rw [hWdef, scalarDuhamel, intervalIntegral.integral_same]
  have hWeq : ∀ r ∈ Set.Icc (0:ℝ) T,
      W r + (lam : ℂ) * (∫ s in (0:ℝ)..r, W s) = ∫ s in (0:ℝ)..r, g s := fun r hr =>
    integrated_equation hWcont hg hW0 (fun s _ => hWderiv s) hr
  set d : ℝ → ℂ := fun s => w s - W s with hddef
  have hdcont : Continuous d := hw.sub hWcont
  set D : ℝ → ℂ := fun r => ∫ s in (0:ℝ)..r, d s with hDdef
  have hDderiv : ∀ r : ℝ, HasDerivAt D (d r) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hdcont.intervalIntegrable 0 r)
      (hdcont.stronglyMeasurableAtFilter _ _) hdcont.continuousAt
  have hDcont : Continuous D := continuous_iff_continuousAt.2 fun r => (hDderiv r).continuousAt
  have hkey : ∀ r ∈ Set.Icc (0:ℝ) T, d r = -((lam : ℂ) * D r) := by
    intro r hr
    have h1 := heq r hr
    have h2 := hWeq r hr
    have hsub : (∫ s in (0:ℝ)..r, w s) - (∫ s in (0:ℝ)..r, W s) = D r := by
      rw [hDdef]
      exact (intervalIntegral.integral_sub (hw.intervalIntegrable 0 r)
        (hWcont.intervalIntegrable 0 r)).symm
    rw [hddef]
    simp only []
    have : w r - W r + (lam : ℂ) * ((∫ s in (0:ℝ)..r, w s) - ∫ s in (0:ℝ)..r, W s) = 0 := by
      rw [mul_sub]
      linear_combination h1 - h2
    rw [hsub] at this
    linear_combination this
  -- the integrating factor
  set E : ℝ → ℂ := fun r => ((Real.exp (r * lam) : ℝ) : ℂ) * D r with hEdef
  set Ed : ℝ → ℂ := fun r =>
    ((lam * Real.exp (r * lam) : ℝ) : ℂ) * D r + ((Real.exp (r * lam) : ℝ) : ℂ) * d r with hEddef
  have hEderiv : ∀ r : ℝ, HasDerivAt E (Ed r) r := by
    intro r
    have hreal : HasDerivAt (fun q : ℝ => Real.exp (q * lam))
        (lam * Real.exp (r * lam)) r := by
      have h1 : HasDerivAt (fun q : ℝ => q * lam) lam r := by
        simpa using (hasDerivAt_id r).mul_const lam
      have h2 := (Real.hasDerivAt_exp (r * lam)).comp r h1
      have h3 : Real.exp (r * lam) * lam = lam * Real.exp (r * lam) := by ring
      simpa [Function.comp, h3] using h2
    have hcx : HasDerivAt (fun q : ℝ => ((Real.exp (q * lam) : ℝ) : ℂ))
        (((lam * Real.exp (r * lam) : ℝ) : ℂ)) r :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hreal
    exact hcx.mul (hDderiv r)
  have hEdcont : Continuous Ed := by
    rw [hEddef]
    exact ((Complex.continuous_ofReal.comp
        ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).const_mul lam)).mul
      hDcont).add
      ((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_id.mul continuous_const))).mul hdcont)
  have hEdzero : ∀ r ∈ Set.uIcc (0:ℝ) t, Ed r = 0 := by
    intro r hr
    rw [Set.uIcc_of_le ht.1] at hr
    have hrT : r ∈ Set.Icc (0:ℝ) T := ⟨hr.1, le_trans hr.2 ht.2⟩
    rw [hEddef]
    simp only []
    rw [hkey r hrT]
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := E) (f' := Ed) (a := (0:ℝ)) (b := t) (fun x _ => hEderiv x)
    (hEdcont.intervalIntegrable 0 t)
  have hzero : (∫ y in (0:ℝ)..t, Ed y) = 0 := by
    have hcg : (∫ y in (0:ℝ)..t, Ed y) = ∫ _y in (0:ℝ)..t, (0 : ℂ) :=
      intervalIntegral.integral_congr (fun y hy => hEdzero y hy)
    rw [hcg, intervalIntegral.integral_zero]
  rw [hzero] at hFTC
  have hE0 : E 0 = 0 := by
    rw [hEdef]
    simp only []
    rw [hDdef]
    simp
  have hEt : E t = 0 := by
    rw [hE0, sub_zero] at hFTC
    exact hFTC.symm
  have hDt : D t = 0 := by
    have hne : ((Real.exp (t * lam) : ℝ) : ℂ) ≠ 0 := by
      simp
    rw [hEdef] at hEt
    simp only [] at hEt
    exact (mul_eq_zero.1 hEt).resolve_left hne
  have hdt : d t = 0 := by rw [hkey t ht, hDt, mul_zero, neg_zero]
  rw [hddef] at hdt
  simp only [] at hdt
  exact sub_eq_zero.1 hdt

/-! ## 2. Single-mode test polynomials -/

/-- The trigonometric test polynomial that extracts the `k`-th Fourier coefficient. -/
noncomputable def modeTest (k : Gam) : C(Torus2, ℂ) := trigPoly {-k} (fun _ => 1)

theorem spacePair_modeTest (a : Wiener) (k : Gam) : spacePair a (modeTest k) = a k := by
  rw [modeTest, spacePair_trigPoly]
  simp

/-- The fractional test polynomial attached to a single mode. -/
noncomputable def fracModeTest (α : ℝ) (k : Gam) : C(Torus2, ℂ) :=
  fracLapPoly α {-k} (fun _ => 1)

theorem spacePair_fracModeTest (a : Wiener) (α : ℝ) (k : Gam) :
    spacePair a (fracModeTest α k) = (fracSymbol α k : ℂ) * a k := by
  rw [fracModeTest, spacePair_fracLapPoly]
  rw [Finset.sum_singleton, fracSymbol_neg]
  simp

/-! ## 3. The physical solution predicate -/

/-- **A physical solution of the Li–Wang active scalar equation with source `f`.**

The three fields of this structure are the three ingredients the assignment asks for:
function-space regularity (carried by the type `Curve1 T = C([0,T]; A¹)`), the initial trace,
and the equation itself in weak (distributional) form, integrated once in time and tested
against arbitrary trigonometric polynomials.  Each `spacePair` is a literal integral over the
torus of the synthesized physical function against the test function. -/
structure IsPhysicalSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (f : Curve0 T) (θ : Curve1 T) : Prop where
  /-- **Initial trace** `θ(0) = 0`. -/
  initial : curveState hT θ 0 = 0
  /-- **The equation**, tested against every trigonometric polynomial and integrated in time. -/
  weak : ∀ (P : C(Torus2, ℂ)) (F : Finset Gam) (c : Gam → ℂ), P = trigPoly F c →
    ∀ t ∈ Set.Icc (0:ℝ) T,
      spacePair (incl (curveState hT θ t)) P
        + (∫ s in (0:ℝ)..t, spacePair (incl (curveState hT θ s)) (fracLapPoly α F c))
        + (∫ s in (0:ℝ)..t, spacePair (quadCurve hm (curveState hT θ) s) P)
        = ∫ s in (0:ℝ)..t, spacePair (sourceFun hT f s) P

/-! ## 4. The constructed mild state is a physical solution -/

theorem continuous_spacePair_curveState (hT : 0 ≤ T) (θ : Curve1 T) (P : C(Torus2, ℂ)) :
    Continuous fun s : ℝ => spacePair (incl (curveState hT θ s)) P := by
  have hCLM : Continuous fun a : Wiener => spacePair a P := by
    have : (fun a : Wiener => spacePair a P) = fun a : Wiener => pairCLM P (synth a) := by
      funext a
      rw [pairCLM_apply, spacePair]
    rw [this]
    exact (pairCLM P).continuous.comp synth.continuous
  exact hCLM.comp (incl.continuous.comp (continuous_curveState hT θ))

theorem continuous_spacePair_source (hT : 0 ≤ T) (f : Curve0 T) (P : C(Torus2, ℂ)) :
    Continuous fun s : ℝ => spacePair (sourceFun hT f s) P := by
  have hCLM : Continuous fun a : Wiener => spacePair a P := by
    have : (fun a : Wiener => spacePair a P) = fun a : Wiener => pairCLM P (synth a) := by
      funext a
      rw [pairCLM_apply, spacePair]
    rw [this]
    exact (pairCLM P).continuous.comp synth.continuous
  exact hCLM.comp (continuous_sourceFun hT f)

theorem continuous_spacePair_quadCurve (hT : 0 ≤ T) (hm : IsBddSymbol m) (θ : Curve1 T)
    (P : C(Torus2, ℂ)) :
    Continuous fun s : ℝ => spacePair (quadCurve hm (curveState hT θ) s) P := by
  have hCLM : Continuous fun a : Wiener => spacePair a P := by
    have : (fun a : Wiener => spacePair a P) = fun a : Wiener => pairCLM P (synth a) := by
      funext a
      rw [pairCLM_apply, spacePair]
    rw [this]
    exact (pairCLM P).continuous.comp synth.continuous
  exact hCLM.comp (continuous_quadCurve hm (continuous_curveState hT θ))


/-! ## 5. The constructed mild state is a physical solution -/

/-- The coefficient form of the integrated equation for a mild solution, with the transport
term kept on the left. -/
theorem coeff_integrated_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {θ : Curve1 T} {f : Curve0 T}
    (hmild : θ + sourceQuad hα hT m hm hr θ θ = duhamelOp hα hT f) (k : Gam)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT θ t).coeff k
        + (fracSymbol α k : ℂ) * (∫ s in (0:ℝ)..t, (curveState hT θ s).coeff k)
        + (∫ s in (0:ℝ)..t, (quadCurve hm (curveState hT θ) s) k)
      = ∫ s in (0:ℝ)..t, (sourceFun hT f s) k := by
  set g : Curve0 T := f - spacetimeTransport m hm hr θ θ with hgdef
  have hu : θ = duhamelOp hα hT g := mild_curve_eq_duhamelOp hα hT hm hr hmild
  have hbase := coeff_duhamelOp_integrated hα hT g k ht
  rw [← hu] at hbase
  have hsrc : ∀ s : ℝ, (sourceFun hT g s) k
      = (sourceFun hT f s) k - (quadCurve hm (curveState hT θ) s) k := by
    intro s
    rw [hgdef, sourceFun_sub_spacetimeTransport hT hm hr θ f s, lp.coeFn_sub, Pi.sub_apply]
  have hsplit : (∫ s in (0:ℝ)..t, (sourceFun hT g s) k)
      = (∫ s in (0:ℝ)..t, (sourceFun hT f s) k)
        - ∫ s in (0:ℝ)..t, (quadCurve hm (curveState hT θ) s) k := by
    rw [intervalIntegral.integral_congr (g := fun s => (sourceFun hT f s) k
        - (quadCurve hm (curveState hT θ) s) k) (fun s _ => hsrc s)]
    exact intervalIntegral.integral_sub
      ((continuous_wiener_coeff k (continuous_sourceFun hT f)).intervalIntegrable 0 t)
      ((continuous_wiener_coeff k
        (continuous_quadCurve hm (continuous_curveState hT θ))).intervalIntegrable 0 t)
  rw [hsplit] at hbase
  linear_combination hbase

/-- **The constructed mild state is a physical solution.**  The class of physical solutions is
therefore nonempty and contains the object the inverse problem is built on. -/
theorem isPhysicalSolution_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {θ : Curve1 T} {f : Curve0 T}
    (hmild : θ + sourceQuad hα hT m hm hr θ θ = duhamelOp hα hT f) :
    IsPhysicalSolution hα hT hm f θ := by
  refine ⟨curveState_initial_of_mild hα hT hm hr hmild, ?_⟩
  intro P F c hP t ht
  subst hP
  have hI1 : spacePair (incl (curveState hT θ t)) (trigPoly F c)
      = ∑ j ∈ F, c j * (curveState hT θ t).coeff (-j) := spacePair_trigPoly _ F c
  have hI2 : (∫ s in (0:ℝ)..t, spacePair (incl (curveState hT θ s)) (fracLapPoly α F c))
      = ∑ j ∈ F, (fracSymbol α j : ℂ) * c j
          * ∫ s in (0:ℝ)..t, (curveState hT θ s).coeff (-j) := by
    have hpt : ∀ s : ℝ, spacePair (incl (curveState hT θ s)) (fracLapPoly α F c)
        = ∑ j ∈ F, (fracSymbol α j : ℂ) * c j * (curveState hT θ s).coeff (-j) :=
      fun s => spacePair_fracLapPoly _ F c
    rw [intervalIntegral.integral_congr (fun s _ => hpt s),
      intervalIntegral.integral_finset_sum (fun j _ =>
        ((continuous_coeff_curveState hT θ (-j)).const_mul
          ((fracSymbol α j : ℂ) * c j)).intervalIntegrable 0 t)]
    exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
  have hI3 : (∫ s in (0:ℝ)..t, spacePair (quadCurve hm (curveState hT θ) s) (trigPoly F c))
      = ∑ j ∈ F, c j * ∫ s in (0:ℝ)..t, (quadCurve hm (curveState hT θ) s) (-j) := by
    have hpt : ∀ s : ℝ, spacePair (quadCurve hm (curveState hT θ) s) (trigPoly F c)
        = ∑ j ∈ F, c j * (quadCurve hm (curveState hT θ) s) (-j) :=
      fun s => spacePair_trigPoly _ F c
    rw [intervalIntegral.integral_congr (fun s _ => hpt s),
      intervalIntegral.integral_finset_sum (fun j _ =>
        ((continuous_wiener_coeff (-j)
          (continuous_quadCurve hm (continuous_curveState hT θ))).const_mul
            (c j)).intervalIntegrable 0 t)]
    exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
  have hI4 : (∫ s in (0:ℝ)..t, spacePair (sourceFun hT f s) (trigPoly F c))
      = ∑ j ∈ F, c j * ∫ s in (0:ℝ)..t, (sourceFun hT f s) (-j) := by
    have hpt : ∀ s : ℝ, spacePair (sourceFun hT f s) (trigPoly F c)
        = ∑ j ∈ F, c j * (sourceFun hT f s) (-j) := fun s => spacePair_trigPoly _ F c
    rw [intervalIntegral.integral_congr (fun s _ => hpt s),
      intervalIntegral.integral_finset_sum (fun j _ =>
        ((continuous_wiener_coeff (-j) (continuous_sourceFun hT f)).const_mul
          (c j)).intervalIntegrable 0 t)]
    exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
  rw [hI1, hI2, hI3, hI4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h := coeff_integrated_of_mild hα hT hm hr hmild (-j) ht
  rw [fracSymbol_neg] at h
  linear_combination c j * h

/-! ## 6. Every physical solution is the mild solution -/

/-- **The converse.**  A physical solution satisfies the mild equation.  This is the step that
turns the distributional physical formulation into the fixed-point equation the packet's
inverse theory is written in; nothing is assumed about `θ` beyond the predicate. -/
theorem mild_of_isPhysicalSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {θ : Curve1 T} {f : Curve0 T}
    (h : IsPhysicalSolution hα hT hm f θ) :
    θ + sourceQuad hα hT m hm hr θ θ = duhamelOp hα hT f := by
  set g : Curve0 T := f - spacetimeTransport m hm hr θ θ with hgdef
  clear_value g
  have hgsrc : ∀ s : ℝ, ∀ k : Gam, (sourceFun hT g s) k
      = (sourceFun hT f s) k - (quadCurve hm (curveState hT θ) s) k := by
    intro s k
    rw [hgdef, sourceFun_sub_spacetimeTransport hT hm hr θ f s, lp.coeFn_sub, Pi.sub_apply]
  -- the scalar integrated equation, one mode at a time
  have hmode : ∀ k : Gam, ∀ t ∈ Set.Icc (0:ℝ) T,
      (curveState hT θ t).coeff k
          + (fracSymbol α k : ℂ) * (∫ s in (0:ℝ)..t, (curveState hT θ s).coeff k)
        = ∫ s in (0:ℝ)..t, (sourceFun hT g s) k := by
    intro k t ht
    have hw := h.weak (modeTest k) {-k} (fun _ => 1) rfl t ht
    rw [spacePair_modeTest] at hw
    have hfrac : (∫ s in (0:ℝ)..t,
        spacePair (incl (curveState hT θ s)) (fracLapPoly α {-k} (fun _ => 1)))
        = (fracSymbol α k : ℂ) * ∫ s in (0:ℝ)..t, (curveState hT θ s).coeff k := by
      have hpt : ∀ s : ℝ,
          spacePair (incl (curveState hT θ s)) (fracLapPoly α {-k} (fun _ => 1))
            = (fracSymbol α k : ℂ) * (curveState hT θ s).coeff k := by
        intro s
        have := spacePair_fracModeTest (incl (curveState hT θ s)) α k
        rw [fracModeTest] at this
        exact this
      rw [intervalIntegral.integral_congr (fun s _ => hpt s)]
      exact intervalIntegral.integral_const_mul _ _
    have hquad : (∫ s in (0:ℝ)..t,
        spacePair (quadCurve hm (curveState hT θ) s) (modeTest k))
        = ∫ s in (0:ℝ)..t, (quadCurve hm (curveState hT θ) s) k :=
      intervalIntegral.integral_congr (fun s _ => spacePair_modeTest _ k)
    have hsrc : (∫ s in (0:ℝ)..t, spacePair (sourceFun hT f s) (modeTest k))
        = ∫ s in (0:ℝ)..t, (sourceFun hT f s) k :=
      intervalIntegral.integral_congr (fun s _ => spacePair_modeTest _ k)
    rw [hfrac, hquad, hsrc] at hw
    have hsplit : (∫ s in (0:ℝ)..t, (sourceFun hT g s) k)
        = (∫ s in (0:ℝ)..t, (sourceFun hT f s) k)
          - ∫ s in (0:ℝ)..t, (quadCurve hm (curveState hT θ) s) k := by
      rw [intervalIntegral.integral_congr (g := fun s => (sourceFun hT f s) k
          - (quadCurve hm (curveState hT θ) s) k) (fun s _ => hgsrc s k)]
      exact intervalIntegral.integral_sub
        ((continuous_wiener_coeff k (continuous_sourceFun hT f)).intervalIntegrable 0 t)
        ((continuous_wiener_coeff k
          (continuous_quadCurve hm (continuous_curveState hT θ))).intervalIntegrable 0 t)
    rw [hsplit]
    simp only [incl_apply] at hw
    linear_combination hw
  -- invert the scalar equation
  have hduh : ∀ t ∈ Set.Icc (0:ℝ) T, curveState hT θ t = curveState hT (duhamelOp hα hT g) t := by
    intro t ht
    refine Wiener1.coeff_injective (funext fun k => ?_)
    have hconv := integrated_equation_converse (T := T) (lam := fracSymbol α k)
      (continuous_coeff_curveState hT θ k)
      (continuous_wiener_coeff k (continuous_sourceFun hT g))
      (fun r hr => hmode k r hr) ht
    rw [hconv, ← coeff_duhamelOp_eq_scalarDuhamel hα hT g k ht]
  have hθ : θ = duhamelOp hα hT g := by
    refine DFunLike.ext _ _ (fun t => RealWiener1.val_injective ?_)
    have := hduh (t : ℝ) t.2
    rwa [curveState_coe hT θ t, curveState_coe hT (duhamelOp hα hT g) t] at this
  have hsq : sourceQuad hα hT m hm hr θ θ
      = duhamelOp hα hT (spacetimeTransport m hm hr θ θ) := rfl
  rw [hsq]
  nth_rewrite 1 [hθ]
  rw [← map_add, hgdef]
  congr 1
  abel

/-! ## 7. The comparison theorem -/

/-- **Uniqueness of the physical solution.**  Two physical solutions of the same source
coincide.  No smallness of the source or of the solutions is assumed, and neither solution is
required to lie in any ball: the hypotheses are exactly the solution predicate. -/
theorem physical_solution_unique (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {f : Curve0 T} {θ₁ θ₂ : Curve1 T}
    (h₁ : IsPhysicalSolution hα hT hm f θ₁) (h₂ : IsPhysicalSolution hα hT hm f θ₂) :
    θ₁ = θ₂ :=
  mild_curve_unique hα hT hm hr hC f
    (mild_of_isPhysicalSolution hα hT hm hr h₁) (mild_of_isPhysicalSolution hα hT hm hr h₂)

/-- **The comparison theorem.**  Any physical solution of a source `f` equals the constructed
mild state.  This is the identification the physical bridge needs, and it is a *proved
consequence* of the PDE and the uniqueness theory — not an assumption. -/
theorem eq_of_isPhysicalSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {f : Curve0 T} {u θ : Curve1 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (hθ : IsPhysicalSolution hα hT hm f θ) :
    θ = u :=
  physical_solution_unique hα hT hm hr hC hθ (isPhysicalSolution_of_mild hα hT hm hr hmild)

/-! ## 8. Energy properties of the comparison class -/

/-- **The energy regularity of the comparison class.**  Every physical solution satisfies the
homogeneous `L²`-in-time bound

    `∑_k λ_k² ∫₀ᵀ |θ̂_k(t)|² dt ≤ T ‖f − N(θ,θ)‖²`,

i.e. it lies in `L²(0,T; Ḣ^{2α}(𝕋²))`.  Two things this does **not** say.  The left-hand side is
the homogeneous seminorm, not the full `H^{2α}` norm (the zero mode is annihilated by `λ₀ = 0`);
and the right-hand side contains the solution through the transport term, so this is an
a posteriori identity of the Duhamel energy estimate, not an a priori bound in `f` alone.  The
regularity exponent `2α` is the one the paper's class carries at `s = α`; the packet does not
formalize the paper's solution class and this is **not** claimed to imply membership in it (see
`STATUS.md` §4.1). -/
theorem energy_of_isPhysicalSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {f : Curve0 T} {θ : Curve1 T}
    (h : IsPhysicalSolution hα hT hm f θ) :
    (∑' k : Gam, (fracSymbol α k) ^ 2 * ∫ t in (0:ℝ)..T, ‖(curveState hT θ t).coeff k‖ ^ 2)
      ≤ T * ‖f - spacetimeTransport m hm hr θ θ‖ ^ 2 :=
  tsum_integral_fracSymbol_sq_mild_le hα hT hm hr (mild_of_isPhysicalSolution hα hT hm hr h)

/-- Every physical solution has `H^{2α}` spatial regularity at almost every time. -/
theorem ae_memSobolev_of_isPhysicalSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {f : Curve0 T} {θ : Curve1 T}
    (h : IsPhysicalSolution hα hT hm f θ) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α) (curveState hT θ t).coeff :=
  ae_memSobolev_mild hα hT hm hr (mild_of_isPhysicalSolution hα hT hm hr h)

/-- **The comparison class embeds in `L^∞(0,T; L²(𝕋²))`**, with the `A¹` norm as the bound.
This is a property of the ambient function space `Curve1 T` itself — the function-space
regularity carried by the type — so no solution hypothesis is needed or used. -/
theorem norm_physState_le (hT : 0 ≤ T) (θ : Curve1 T) (t : ℝ) :
    ‖physState hT θ t‖ ≤ ‖θ‖ := by
  calc ‖physState hT θ t‖ ≤ ‖incl (curveState hT θ t)‖ := norm_synthL2_le _
    _ ≤ ‖curveState hT θ t‖ := norm_incl_apply_le _
    _ ≤ ‖θ‖ := norm_curveState_le hT θ t

/-- **The initial trace is forced by the equation.**  Recording `initial` as a separate field of
`IsPhysicalSolution` is a convenience for readability, not an extra assumption: the weak
equation at `t = 0` already gives `θ(0) = 0`, because every time integral over `[0,0]` vanishes
and the single-mode test polynomials separate points of the carrier. -/
theorem curveState_zero_of_weak {α : ℝ} (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (f : Curve0 T) (θ : Curve1 T)
    (hw : ∀ (P : C(Torus2, ℂ)) (F : Finset Gam) (c : Gam → ℂ), P = trigPoly F c →
      ∀ t ∈ Set.Icc (0:ℝ) T,
        spacePair (incl (curveState hT θ t)) P
          + (∫ s in (0:ℝ)..t, spacePair (incl (curveState hT θ s)) (fracLapPoly α F c))
          + (∫ s in (0:ℝ)..t, spacePair (quadCurve hm (curveState hT θ) s) P)
          = ∫ s in (0:ℝ)..t, spacePair (sourceFun hT f s) P) :
    curveState hT θ 0 = 0 := by
  refine Wiener1.coeff_injective (funext fun k => ?_)
  have h := hw (modeTest k) {-k} (fun _ => 1) rfl 0 ⟨le_rfl, hT⟩
  rw [spacePair_modeTest] at h
  simp only [intervalIntegral.integral_same, add_zero] at h
  show (curveState hT θ 0).coeff k = (0 : Wiener1).coeff k
  simpa using h

end LiWang.Formalization
