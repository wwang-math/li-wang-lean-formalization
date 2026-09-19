/-
# The weak physical equation

The coefficient evolution equation is assembled into a genuine *weak physical* equation on
`(0,T) × 𝕋²`: for every finite spatial Fourier test function `P = ∑_{k ∈ F} c_k e_k` and every
`C¹` time test function `φ` supported in `(0,T)`,

    ∫₀^T ( -⟪u(t), P⟫ φ'(t) + ⟪u(t), (-Δ)^α P⟫ φ(t)
             + ⟪N_K(u(t),u(t)), P⟫ φ(t) - ⟪f(t), P⟫ φ(t) ) dt = 0 ,

where `⟪a, P⟫ = ∫_{𝕋²} (synth a)(x) P(x) dx` is an actual integral over the torus.  The
fractional Laplacian is applied to the *test function*, which is a trigonometric polynomial;
no additional regularity of the state is claimed or used.  In particular this does **not**
assert that `(-Δ)^α u(t)` is a Wiener element when `2α > 1`.

Part of `LiWangFormalizationSourceResponsePacket` v3.0.
-/
import LiWangFormalization.TorusIntegral
import LiWangFormalization.VariationODE

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-- The spatial pairing of a Wiener state with a continuous test function: an actual integral
over the two-torus of the synthesized (physical) function against the test function. -/
noncomputable def spacePair (a : Wiener) (P : C(Torus2, ℂ)) : ℂ :=
  ∫ x : Torus2, synth a x * P x

theorem spacePair_trigPoly (a : Wiener) (F : Finset Gam) (c : Gam → ℂ) :
    spacePair a (trigPoly F c) = ∑ j ∈ F, c j * a (-j) :=
  integral_synth_mul_trigPoly a F c

theorem spacePair_fracLapPoly (a : Wiener) (F : Finset Gam) (c : Gam → ℂ) :
    spacePair a (fracLapPoly α F c)
      = ∑ j ∈ F, (fracSymbol α j : ℂ) * c j * a (-j) :=
  integral_synth_mul_trigPoly a F (fun k => (fracSymbol α k : ℂ) * c k)

/-! ## The weak physical equation for the forced mild solution -/

/-- **The weak physical equation.**  Every term is an actual space-time integral; the
dissipation acts on the finite Fourier test polynomial, so no extra regularity of the state
is used. -/
theorem weak_physical_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f)
    (F : Finset Gam) (c : Gam → ℂ)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T,
        (-(spacePair (incl (curveState hT u t)) (trigPoly F c)) * ψ t
          + (spacePair (incl (curveState hT u t)) (fracLapPoly α F c)) * φ t
          + (spacePair (quadCurve hm (curveState hT u) t) (trigPoly F c)) * φ t
          - (spacePair (sourceFun hT f t) (trigPoly F c)) * φ t)) = 0 := by
  classical
  set W : Gam → ℝ → ℂ := fun k t =>
    -((curveState hT u t).coeff k) * ψ t
      + (fracSymbol α k : ℂ) * (curveState hT u t).coeff k * φ t
      + (quadCurve hm (curveState hT u) t) k * φ t
      - (sourceFun hT f t) k * φ t with hWdef
  have hcs : Continuous (curveState hT u) := continuous_curveState hT u
  have hWcont : ∀ k : Gam, Continuous (W k) := by
    intro k
    have h1 : Continuous fun t : ℝ => (curveState hT u t).coeff k :=
      continuous_coeff_curveState hT u k
    have h2 : Continuous fun t : ℝ => (quadCurve hm (curveState hT u) t) k :=
      continuous_wiener_coeff k (continuous_quadCurve hm hcs)
    have h3 : Continuous fun t : ℝ => (sourceFun hT f t) k :=
      continuous_wiener_coeff k (continuous_sourceFun hT f)
    exact ((((h1.neg).mul hψ).add ((continuous_const.mul h1).mul hφ)).add
      (h2.mul hφ)).sub (h3.mul hφ)
  have hWzero : ∀ k : Gam, (∫ t in (0:ℝ)..T, W k t) = 0 := fun k =>
    weak_coeff_of_mild hα hT hm hr hC hmild k hφ hψ hφderiv hsupp
  have hpt : ∀ t : ℝ,
      (-(spacePair (incl (curveState hT u t)) (trigPoly F c)) * ψ t
        + (spacePair (incl (curveState hT u t)) (fracLapPoly α F c)) * φ t
        + (spacePair (quadCurve hm (curveState hT u) t) (trigPoly F c)) * φ t
        - (spacePair (sourceFun hT f t) (trigPoly F c)) * φ t)
      = ∑ j ∈ F, c j * W (-j) t := by
    intro t
    rw [spacePair_trigPoly, spacePair_fracLapPoly, spacePair_trigPoly, spacePair_trigPoly,
      neg_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsym : (fracSymbol α j : ℂ) = (fracSymbol α (-j) : ℂ) := by
      rw [fracSymbol_neg]
    simp only [hWdef, incl_apply]
    rw [hsym]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_finset_sum (s := F) (f := fun (j : Gam) (t : ℝ) => c j * W (-j) t)
    (fun j (_ : j ∈ F) => ((continuous_const.mul (hWcont (-j))).intervalIntegrable 0 T))]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hcm := intervalIntegral.integral_const_mul (a := (0:ℝ)) (b := T)
    (μ := (volume : Measure ℝ)) (c j) (W (-j))
  exact hcm.trans (mul_eq_zero_of_right (c j) (hWzero (-j)))

/-! ## The weak physical equation for a Duhamel term -/

/-- **The weak physical equation of the linear Duhamel evolution.**  The same statement with
the quadratic term removed; this is what the source variations satisfy. -/
theorem weak_physical_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T)
    (F : Finset Gam) (c : Gam → ℂ)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T,
        (-(spacePair (incl (curveState hT (duhamelOp hα hT g) t)) (trigPoly F c)) * ψ t
          + (spacePair (incl (curveState hT (duhamelOp hα hT g) t)) (fracLapPoly α F c)) * φ t
          - (spacePair (sourceFun hT g t) (trigPoly F c)) * φ t)) = 0 := by
  classical
  set w : ℝ → Wiener1 := curveState hT (duhamelOp hα hT g) with hwdef
  set W : Gam → ℝ → ℂ := fun k t =>
    -((w t).coeff k) * ψ t + (fracSymbol α k : ℂ) * (w t).coeff k * φ t
      - (sourceFun hT g t) k * φ t with hWdef
  have hWcont : ∀ k : Gam, Continuous (W k) := by
    intro k
    have h1 : Continuous fun t : ℝ => (w t).coeff k := continuous_coeff_curveState hT _ k
    have h3 : Continuous fun t : ℝ => (sourceFun hT g t) k :=
      continuous_wiener_coeff k (continuous_sourceFun hT g)
    exact (((h1.neg).mul hψ).add ((continuous_const.mul h1).mul hφ)).sub (h3.mul hφ)
  have hWzero : ∀ k : Gam, (∫ t in (0:ℝ)..T, W k t) = 0 := fun k =>
    weak_coeff_duhamelOp hα hT g k hφ hψ hφderiv hsupp
  have hpt : ∀ t : ℝ,
      (-(spacePair (incl (w t)) (trigPoly F c)) * ψ t
        + (spacePair (incl (w t)) (fracLapPoly α F c)) * φ t
        - (spacePair (sourceFun hT g t) (trigPoly F c)) * φ t)
      = ∑ j ∈ F, c j * W (-j) t := by
    intro t
    rw [spacePair_trigPoly, spacePair_fracLapPoly, spacePair_trigPoly,
      neg_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsym : (fracSymbol α j : ℂ) = (fracSymbol α (-j) : ℂ) := by rw [fracSymbol_neg]
    simp only [hWdef, incl_apply]
    rw [hsym]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_finset_sum (s := F) (f := fun (j : Gam) (t : ℝ) => c j * W (-j) t)
    (fun j (_ : j ∈ F) => ((continuous_const.mul (hWcont (-j))).intervalIntegrable 0 T))]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hcm := intervalIntegral.integral_const_mul (a := (0:ℝ)) (b := T)
    (μ := (volume : Measure ℝ)) (c j) (W (-j))
  exact hcm.trans (mul_eq_zero_of_right (c j) (hWzero (-j)))

/-- **The weak physical equation satisfied by the first source response** `DS(0)[h] = J_T h`. -/
theorem weak_physical_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) (F : Finset Gam) (c : Gam → ℂ)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T,
        (-(spacePair (incl (curveState hT
              (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t)) (trigPoly F c)) * ψ t
          + (spacePair (incl (curveState hT
              (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t))
                (fracLapPoly α F c)) * φ t
          - (spacePair (sourceFun hT h t) (trigPoly F c)) * φ t)) = 0 := by
  rw [curveState_fderiv_sourceSolution hα hT hm hr h]
  exact weak_physical_duhamelOp hα hT h F c hφ hψ hφderiv hsupp

/-- **The weak physical equation satisfied by the second source response**
`D²S(0)[h₁,h₂] = -J_T(N_K(J h₁, J h₂) + N_K(J h₂, J h₁))`. -/
theorem weak_physical_fderiv_fderiv_sourceSolution (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T)
    (F : Finset Gam) (c : Gam → ℂ)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T,
        (-(spacePair (incl (curveState hT
              (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂) t))
                (trigPoly F c)) * ψ t
          + (spacePair (incl (curveState hT
              (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr)) (0 : Curve0 T) h₁ h₂) t))
                (fracLapPoly α F c)) * φ t
          - (spacePair (sourceFun hT (secondVariationSource hα hT hm hr h₁ h₂) t)
              (trigPoly F c)) * φ t)) = 0 := by
  rw [curveState_fderiv_fderiv_sourceSolution hα hT hm hr h₁ h₂]
  exact weak_physical_duhamelOp hα hT (secondVariationSource hα hT hm hr h₁ h₂) F c
    hφ hψ hφderiv hsupp

end LiWang.Formalization
