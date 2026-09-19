/-
# Reality of the Duhamel term and of the mild map

A real scalar field has conjugate-symmetric Fourier coefficients.  This module shows that the
whole mild machinery preserves that symmetry: the first-order heat flow, the Duhamel integral
(via the coefficient functionals and the fact that conjugation commutes with the Bochner
integral), the quadratic transport term along a curve, and hence the mild map itself.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.LocalSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory BoundedContinuousFunction

namespace LiWang.Formalization

/-! ## The coefficient functionals on the first-order space -/

/-- The `k`-th coefficient of a first-order Wiener element, as a bounded linear functional. -/
noncomputable def Wiener1.evalCLM (k : Gam) : Wiener1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun u => u.coeff k
      map_add' := fun u v => by rw [Wiener1.coeff_add]; rfl
      map_smul' := fun c u => by rw [Wiener1.coeff_smul]; rfl }
    1 (fun u => by rw [one_mul]; exact Wiener1.norm_coeff_le u k)

@[simp] theorem Wiener1.evalCLM_apply (k : Gam) (u : Wiener1) :
    Wiener1.evalCLM k u = u.coeff k := rfl

/-- Coefficients of an interval integral of curves are the integrals of the coefficients. -/
theorem coeff_intervalIntegral {F : ℝ → Wiener1} {a b : ℝ}
    (hF : IntervalIntegrable F volume a b) (k : Gam) :
    (∫ s in a..b, F s).coeff k = ∫ s in a..b, (F s).coeff k :=
  ((Wiener1.evalCLM k).intervalIntegral_comp_comm hF).symm

/-- Conjugation commutes with interval integration of complex-valued functions. -/
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    (∫ x in a..b, conj (f x)) = conj (∫ x in a..b, f x) := by
  rw [intervalIntegral, intervalIntegral, map_sub]
  congr 1
  · exact integral_conj
  · exact integral_conj

/-! ## Reality of the heat flow and of the Duhamel integrand -/

theorem conjSymmetric_heatFlow1 {α t : ℝ} {u : Wiener1} (hu : ConjSymmetric u.coeff) :
    ConjSymmetric (heatFlow1 α t u).coeff := by
  intro k
  show heatSymbol α (max t 0) (-k) * u.coeff (-k)
    = conj (heatSymbol α (max t 0) k * u.coeff k)
  rw [conjSymmetric_heatSymbol α (max t 0) k, hu k, map_mul]

theorem conjSymmetric_heatSmoothFun {α t : ℝ} (hα : 1 / 2 ≤ α) {a : Wiener}
    (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric (heatSmoothFun hα t a).coeff := by
  by_cases ht : 0 < t
  · intro k
    rw [heatSmoothFun_coeff hα ht a (-k), heatSmoothFun_coeff hα ht a k,
      conjSymmetric_heatSymbol α t k, ha k, map_mul]
  · rw [heatSmoothFun_of_nonpos hα (not_lt.1 ht), Wiener1.coeff_zero]
    exact ConjSymmetric.zero

theorem conjSymmetric_duhamelIntegrand {α t : ℝ} (hα : 1 / 2 ≤ α) {g : ℝ → Wiener}
    (hg : ∀ s, ConjSymmetric ((g s : Gam → ℂ))) (s : ℝ) :
    ConjSymmetric (duhamelIntegrand hα t g s).coeff :=
  conjSymmetric_heatSmoothFun hα (hg s)

/-! ## Reality of the Duhamel integral -/

/-- **The Duhamel integral of a real source is real.** -/
theorem conjSymmetric_duhamelIntegral {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ → Wiener} (hgc : Continuous g) {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M)
    (hg : ∀ s, ConjSymmetric ((g s : Gam → ℂ))) :
    ConjSymmetric (duhamelIntegral hα.le t g).coeff := by
  have hint : IntervalIntegrable (duhamelIntegrand hα.le t g) volume 0 t :=
    intervalIntegrable_duhamelIntegrand hα ht hgc hM
  intro k
  rw [duhamelIntegral, coeff_intervalIntegral hint (-k), coeff_intervalIntegral hint k,
    ← intervalIntegral_conj]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact conjSymmetric_duhamelIntegrand hα.le hg s k

/-! ## Reality of the quadratic term and of the mild map -/

theorem conjSymmetric_quadCurve {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : ℝ → Wiener1} (hu : ∀ s, ConjSymmetric (u s).coeff) (s : ℝ) :
    ConjSymmetric ((quadCurve hm u s : Wiener) : Gam → ℂ) :=
  ConjSymmetric.transport hm hr (hu s) (hu s)

/-- **The mild map preserves reality**: if the datum and the curve have conjugate-symmetric
coefficients and the velocity symbol is real, so does the image. -/
theorem conjSymmetric_mildMap1 {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {u₀ : Wiener1} (h₀ : ConjSymmetric u₀.coeff) {u : ℝ → Wiener1} (huc : Continuous u)
    {R : ℝ} (hR : ∀ s, ‖u s‖ ≤ R) (hu : ∀ s, ConjSymmetric (u s).coeff) {t : ℝ}
    (ht : 0 ≤ t) :
    ConjSymmetric (mildMap1 hα.le hm u₀ u t).coeff := by
  refine ConjSymmetric.wiener1_sub (conjSymmetric_heatFlow1 h₀) ?_
  exact conjSymmetric_duhamelIntegral hα ht (continuous_quadCurve hm huc)
    (fun s => norm_quadCurve_le hm hC hR s) (conjSymmetric_quadCurve hm hr hu)

/-! ## Reality of the abstract affine fixed point -/

theorem conjSymmetric_affineMildMap {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {A : ℝ → Wiener1} (hAr : ∀ t, ConjSymmetric (A t).coeff) {u : ℝ → Wiener1}
    (huc : Continuous u) {R : ℝ} (hR : ∀ s, ‖u s‖ ≤ R)
    (hu : ∀ s, ConjSymmetric (u s).coeff) {t : ℝ} (ht : 0 ≤ t) :
    ConjSymmetric (affineMildMap hα.le hm A u t).coeff := by
  refine ConjSymmetric.wiener1_sub (hAr t) ?_
  exact conjSymmetric_duhamelIntegral hα ht (continuous_quadCurve hm huc)
    (fun s => norm_quadCurve_le hm hC hR s) (conjSymmetric_quadCurve hm hr hu)

/-- **The Banach iterates of the affine mild map preserve reality**, hence so does its fixed
point: if the affine part has conjugate-symmetric coefficients, so has the solution. -/
theorem conjSymmetric_of_affineCurve_fixedPoint {α : ℝ} (hα : 1 / 2 < α)
    {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) {A : ℝ → Wiener1} (hA : Continuous A)
    (hAr : ∀ t, ConjSymmetric (A t).coeff) {a : ℝ} (haA : ∀ t, ‖A t‖ ≤ a) {T : ℝ}
    (hT : 0 ≤ T)
    (hballmaps : ∀ V : TimeI T →ᵇ Wiener1, ‖V‖ ≤ 2 * a + 1 →
      ‖affineCurveMap hα hm hC A hA hT V‖ ≤ 2 * a + 1)
    {U : TimeI T →ᵇ Wiener1}
    (htend : Tendsto (fun n : ℕ => (affineCurveMap hα hm hC A hA hT)^[n] 0) atTop (𝓝 U)) :
    ∀ t : TimeI T, ConjSymmetric ((U t).coeff) := by
  have ha0 : (0:ℝ) ≤ a := le_trans (norm_nonneg _) (haA 0)
  have hRnn : (0:ℝ) ≤ 2 * a + 1 := by linarith
  set S : Set (TimeI T →ᵇ Wiener1) := {V | ∀ t : TimeI T, ConjSymmetric (V t).coeff} with hS
  have hSmem : ∀ V : TimeI T →ᵇ Wiener1,
      V ∈ S ↔ ∀ t : TimeI T, ConjSymmetric (V t).coeff := by
    intro V; rw [hS]; exact Iff.rfl
  have hSclosed : IsClosed S := by
    have hEq : S = ⋂ (t : TimeI T), ⋂ (k : Gam),
        {V : TimeI T →ᵇ Wiener1 | (V t).coeff (-k) = conj ((V t).coeff k)} := by
      ext V
      simp only [hS, Set.mem_setOf_eq, Set.mem_iInter, ConjSymmetric]
    rw [hEq]
    refine isClosed_iInter fun t => isClosed_iInter fun k => isClosed_eq ?_ ?_
    · exact (Wiener1.evalCLM (-k)).continuous.comp
        (ContinuousEvalConst.continuous_eval_const t)
    · exact Complex.continuous_conj.comp ((Wiener1.evalCLM k).continuous.comp
        (ContinuousEvalConst.continuous_eval_const t))
  have hiter : ∀ n : ℕ,
      ‖(affineCurveMap hα hm hC A hA hT)^[n] (0 : TimeI T →ᵇ Wiener1)‖ ≤ 2 * a + 1 ∧
      (affineCurveMap hα hm hC A hA hT)^[n] (0 : TimeI T →ᵇ Wiener1) ∈ S := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_zero_apply, norm_zero]
        exact hRnn
      · refine (hSmem _).2 (fun t => ?_)
        rw [Function.iterate_zero_apply]
        show ConjSymmetric ((0 : Wiener1)).coeff
        rw [Wiener1.coeff_zero]
        exact ConjSymmetric.zero
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨hballmaps _ ih.1, (hSmem _).2 (fun t => ?_)⟩
      show ConjSymmetric (affineMildMap hα.le hm A
        (extendCurve hT ((affineCurveMap hα hm hC A hA hT)^[n] 0)) (t : ℝ)).coeff
      exact conjSymmetric_affineMildMap hα hm hr hC hAr
        (continuous_extendCurve hT _)
        (fun s => le_trans (norm_extendCurve_le hT _ s) ih.1)
        (fun s => (hSmem _).1 ih.2 (clampT hT s)) t.2.1
  exact (hSmem _).1
    (hSclosed.mem_of_tendsto htend (Filter.Eventually.of_forall fun n => (hiter n).2))

/-! ## The mild solution of a real datum is real -/

/-- **Local existence of a *real* mild solution.**  If the velocity symbol is real
(`IsRealSymbol`) and the datum has conjugate-symmetric Fourier coefficients — i.e. the initial
scalar field is real valued — then the local mild solution constructed by
`exists_local_mild_solution` has conjugate-symmetric coefficients at every time.

The proof does not re-run the fixed point: it observes that the set of curves with
conjugate-symmetric values is closed, that the mild map preserves it, and that the Banach
iterates start at `0`, so the limit stays in it. -/
theorem exists_local_mild_solution_real {α : ℝ} (hα : 1 / 2 < α) {m : Fin 2 → Gam → ℂ}
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C)
    {u₀ : Wiener1} (h₀ : ConjSymmetric u₀.coeff) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * C * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      (∀ t, ConjSymmetric (u t).coeff) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀ - duhamelIntegral hα.le t (quadCurve hm u) := by
  obtain ⟨T, hT, hsmall, hballmaps, U, hUmem, hfix, htend⟩ :=
    exists_mildCurve_fixedPoint hα hm hC u₀
  have hUS : ∀ t : TimeI T, ConjSymmetric ((U t).coeff) :=
    conjSymmetric_of_affineCurve_fixedPoint hα hm hr hC (continuous_heatFlow1 α u₀)
      (fun t => conjSymmetric_heatFlow1 h₀) (fun t => norm_heatFlow1_le α t u₀) hT.le
      hballmaps htend
  refine ⟨T, hT, hsmall, extendCurve hT.le U, continuous_extendCurve hT.le U, ?_, ?_, ?_, ?_⟩
  · calc extendCurve hT.le U 0 = U (clampT hT.le 0) := rfl
      _ = mildCurveMap hα hm hC u₀ hT.le U (clampT hT.le 0) := by rw [hfix]
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) ((clampT hT.le 0 : ℝ)) := rfl
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) 0 := by
            rw [clampT_coe hT.le le_rfl hT.le]
      _ = u₀ := mildMap1_zero hα.le hm u₀ _
  · intro t
    exact le_trans (norm_extendCurve_le hT.le U t) hUmem
  · intro t
    exact hUS (clampT hT.le t)
  · intro t ht
    calc extendCurve hT.le U t = U (clampT hT.le t) := rfl
      _ = mildCurveMap hα hm hC u₀ hT.le U (clampT hT.le t) := by rw [hfix]
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) ((clampT hT.le t : ℝ)) := rfl
      _ = mildMap1 hα.le hm u₀ (extendCurve hT.le U) t := by
            rw [clampT_coe hT.le ht.1 ht.2]
      _ = heatFlow1 α t u₀
            - duhamelIntegral hα.le t (quadCurve hm (extendCurve hT.le U)) := rfl

/-- **The paper-facing local solution.**  For the source-faithful rotated-gradient velocity
`R_κ = ∇^⊥(κ ∗ ·)` with a real kernel coefficient law and a real initial scalar field, the
local mild solution exists and stays real. -/
theorem exists_local_mild_solution_real_rotatedGradient {α : ℝ} (hα : 1 / 2 < α)
    {κ : Gam → ℂ} {A : ℝ} (hb : KernelBound κ A) (hc : ConjSymmetric κ)
    {u₀ : Wiener1} (h₀ : ConjSymmetric u₀.coeff) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Icc (0:ℝ) T,
        8 * Real.pi * (2 * Real.pi * A) * (2 * ‖u₀‖ + 1) * duhamelConst α t ≤ 1 / 2) ∧
      ∃ u : ℝ → Wiener1, Continuous u ∧ u 0 = u₀ ∧
      (∀ t, ‖u t‖ ≤ 2 * ‖u₀‖ + 1) ∧
      (∀ t, ConjSymmetric (u t).coeff) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatFlow1 α t u₀
          - duhamelIntegral hα.le t
              (quadCurve (rotatedGradientSymbol_bdd (⟨A, hb⟩ : IsAdmissibleKernel κ)) u) :=
  exists_local_mild_solution_real hα (rotatedGradientSymbol_bdd ⟨A, hb⟩)
    (rotatedGradientSymbol_isRealSymbol hc)
    (fun j k => rotatedGradientSymbol_norm_le hb j k) h₀

end LiWang.Formalization
