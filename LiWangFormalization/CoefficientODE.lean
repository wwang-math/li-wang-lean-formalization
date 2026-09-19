/-
# The coefficient evolution equation

The mild solution is differentiated back into an actual evolution equation.  For every
frequency `k` and every interior time,

    d/dt u_k(t) + λ_k u_k(t) + (N_K(u(t),u(t)))_k = f_k(t) ,
    λ_k = (4π²(k₀² + k₁²))^α ,

together with the initial trace `u_k(0) = 0`.  Everything is proved from the Bochner Duhamel
integral: the scalar Duhamel formula is differentiated by the fundamental theorem of calculus
after pulling the semigroup factor out of the integral.

Part of `LiWangFormalizationSourceResponsePacket` v3.0.
-/
import LiWangFormalization.SourceSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Filter Topology MeasureTheory intervalIntegral

namespace LiWang.Formalization

/-! ## The scalar Duhamel formula -/

/-- The scalar Duhamel integral with decay rate `lam`. -/
noncomputable def scalarDuhamel (lam : ℝ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..r, ((Real.exp (-((r - s) * lam)) : ℝ) : ℂ) * g s

/-- Pulling the semigroup factor out of the integral. -/
theorem scalarDuhamel_eq (lam : ℝ) (g : ℝ → ℂ) (r : ℝ) :
    scalarDuhamel lam g r
      = ((Real.exp (-(r * lam)) : ℝ) : ℂ) * ∫ s in (0:ℝ)..r, ((Real.exp (s * lam) : ℝ) : ℂ) * g s := by
  rw [scalarDuhamel]
  have hpull : (((Real.exp (-(r * lam)) : ℝ) : ℂ)
      * ∫ s in (0:ℝ)..r, ((Real.exp (s * lam) : ℝ) : ℂ) * g s)
      = ∫ s in (0:ℝ)..r, ((Real.exp (-(r * lam)) : ℝ) : ℂ)
          * (((Real.exp (s * lam) : ℝ) : ℂ) * g s) :=
    (intervalIntegral.integral_const_mul _ _).symm
  rw [hpull]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  have hexp : Real.exp (-((r - s) * lam)) = Real.exp (-(r * lam)) * Real.exp (s * lam) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  push_cast
  ring

/-- **The scalar Duhamel integral solves the scalar ODE.** -/
theorem hasDerivAt_scalarDuhamel (lam : ℝ) {g : ℝ → ℂ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (scalarDuhamel lam g) (g t - (lam : ℂ) * scalarDuhamel lam g t) t := by
  set G : ℝ → ℂ := fun r => ∫ s in (0:ℝ)..r, ((Real.exp (s * lam) : ℝ) : ℂ) * g s with hG
  have hcont : Continuous fun s : ℝ => ((Real.exp (s * lam) : ℝ) : ℂ) * g s :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_id.mul continuous_const))).mul hg
  have hGderiv : HasDerivAt G (((Real.exp (t * lam) : ℝ) : ℂ) * g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hEreal : HasDerivAt (fun r : ℝ => Real.exp (-(r * lam)))
      (-lam * Real.exp (-(t * lam))) t := by
    have h1 : HasDerivAt (fun r : ℝ => -(r * lam)) (-lam) t := by
      simpa using ((hasDerivAt_id t).mul_const lam).neg
    have h2 := (Real.hasDerivAt_exp (-(t * lam))).comp t h1
    have h3 : Real.exp (-(t * lam)) * -lam = -lam * Real.exp (-(t * lam)) := by ring
    simpa [Function.comp, h3] using h2
  have hE : HasDerivAt (fun r : ℝ => ((Real.exp (-(r * lam)) : ℝ) : ℂ))
      (((-lam * Real.exp (-(t * lam)) : ℝ) : ℂ)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hEreal
  have hprod := hE.mul hGderiv
  have hval : scalarDuhamel lam g = fun r : ℝ => ((Real.exp (-(r * lam)) : ℝ) : ℂ) * G r := by
    funext r
    exact scalarDuhamel_eq lam g r
  rw [hval]
  convert hprod using 1
  have hcancel : ((Real.exp (-(t * lam)) : ℝ) : ℂ) * ((Real.exp (t * lam) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  show g t - (lam : ℂ) * (((Real.exp (-(t * lam)) : ℝ) : ℂ) * G t)
      = ((-lam * Real.exp (-(t * lam)) : ℝ) : ℂ) * G t
        + ((Real.exp (-(t * lam)) : ℝ) : ℂ) * (((Real.exp (t * lam) : ℝ) : ℂ) * g t)
  rw [show ((Real.exp (-(t * lam)) : ℝ) : ℂ) * (((Real.exp (t * lam) : ℝ) : ℂ) * g t)
        = (((Real.exp (-(t * lam)) : ℝ) : ℂ) * ((Real.exp (t * lam) : ℝ) : ℂ)) * g t from by
      ring, hcancel, one_mul]
  push_cast
  ring

theorem scalarDuhamel_sub (lam : ℝ) (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h)
    (r : ℝ) :
    scalarDuhamel lam (fun s => g s - h s) r = scalarDuhamel lam g r - scalarDuhamel lam h r := by
  have hcg : Continuous fun s : ℝ => ((Real.exp (-((r - s) * lam)) : ℝ) : ℂ) * g s :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (((continuous_const.sub continuous_id).mul continuous_const).neg))).mul hg
  have hch : Continuous fun s : ℝ => ((Real.exp (-((r - s) * lam)) : ℝ) : ℂ) * h s :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (((continuous_const.sub continuous_id).mul continuous_const).neg))).mul hh
  rw [scalarDuhamel, scalarDuhamel, scalarDuhamel,
    ← intervalIntegral.integral_sub (hcg.intervalIntegrable 0 r) (hch.intervalIntegrable 0 r)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

/-! ## Coefficients of the Duhamel integral -/

/-- **The `k`-th coefficient of the Duhamel integral is the scalar Duhamel integral** with
decay rate `λ_k`. -/
theorem coeff_duhamelIntegral {α : ℝ} (hα : 1 / 2 < α) {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ → Wiener} (hg : Continuous g) {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) (k : Gam) :
    (duhamelIntegral hα.le t g).coeff k = scalarDuhamel (fracSymbol α k) (fun s => (g s) k) t := by
  have hint : IntervalIntegrable (duhamelIntegrand hα.le t g) volume 0 t :=
    intervalIntegrable_duhamelIntegrand hα ht hg hM
  rw [duhamelIntegral, coeff_intervalIntegral hint k, scalarDuhamel]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ s : ℝ, s ≠ t := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with s hs hmem
  have hst : s < t := by
    rcases Set.mem_uIoc.1 hmem with h | h
    · exact lt_of_le_of_ne h.2 hs
    · exact absurd (lt_of_lt_of_le h.1 (le_trans h.2 ht)) (lt_irrefl t)
  have hts : 0 < t - s := by linarith
  show (heatSmoothFun hα.le (t - s) (g s)).coeff k = _
  rw [heatSmoothFun_coeff hα.le hts]
  rfl

/-! ## Coefficient functionals on the Wiener algebra -/

/-- The `k`-th coefficient of a Wiener element, as a bounded linear functional. -/
noncomputable def Wiener.evalCLM (k : Gam) : Wiener →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => a k
      map_add' := fun a b => by simp only [lp.coeFn_add, Pi.add_apply]
      map_smul' := fun c a => by simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply] }
    1 (fun a => by rw [one_mul]; exact wiener_norm_apply_le a k)

@[simp] theorem Wiener.evalCLM_apply (k : Gam) (a : Wiener) : Wiener.evalCLM k a = a k := rfl

/-- Continuity of a single Fourier coefficient along a continuous Wiener-valued curve. -/
theorem continuous_wiener_coeff (k : Gam) {g : ℝ → Wiener} (hg : Continuous g) :
    Continuous fun s => (g s) k :=
  (Wiener.evalCLM k).continuous.comp hg

/-! ## The evolution equation satisfied by a mild solution -/

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-- The state curve, extended to all of `ℝ` by clamping the time. -/
noncomputable def curveState {T : ℝ} (hT : 0 ≤ T) (u : Curve1 T) (s : ℝ) : Wiener1 :=
  (u (clampT hT s)).val

theorem continuous_curveState {T : ℝ} (hT : 0 ≤ T) (u : Curve1 T) :
    Continuous (curveState hT u) :=
  RealWiener1.isometry_val.continuous.comp (u.continuous.comp (continuous_clampT hT))

theorem norm_curveState_le {T : ℝ} (hT : 0 ≤ T) (u : Curve1 T) (s : ℝ) :
    ‖curveState hT u s‖ ≤ ‖u‖ := u.norm_coe_le_norm _

theorem curveState_coe {T : ℝ} (hT : 0 ≤ T) (u : Curve1 T) (t : TimeI T) :
    curveState hT u (t : ℝ) = (u t).val := by
  have h : clampT hT (t : ℝ) = t := Subtype.ext (clampT_coe hT t.2.1 t.2.2)
  rw [curveState, h]

theorem continuous_coeff_curveState {T : ℝ} (hT : 0 ≤ T) (u : Curve1 T) (k : Gam) :
    Continuous fun s => (curveState hT u s).coeff k :=
  (Wiener1.evalCLM k).continuous.comp (continuous_curveState hT u)

/-- **The coefficient form of the mild equation.**  Every Fourier coefficient of the state
is the scalar Duhamel integral of the corresponding coefficient of the right-hand side, with
decay rate `λ_k = fracSymbol α k`. -/
theorem coeff_mild_eq_scalarDuhamel (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT u t).coeff k
      = scalarDuhamel (fracSymbol α k)
          (fun s => (sourceFun hT f s) k - (quadCurve hm (curveState hT u) s) k) t := by
  have hcs : Continuous (curveState hT u) := continuous_curveState hT u
  have hq : Continuous (quadCurve hm (curveState hT u)) := continuous_quadCurve hm hcs
  have hqM : ∀ s, ‖quadCurve hm (curveState hT u) s‖ ≤ 4 * Real.pi * C * ‖u‖ * ‖u‖ :=
    fun s => norm_quadCurve_le hm hC (fun x => norm_curveState_le hT u x) s
  have hsc : Continuous (sourceFun hT f) := continuous_sourceFun hT f
  have hsM : ∀ s, ‖sourceFun hT f s‖ ≤ ‖f‖ := fun s => norm_sourceFun_le hT f s
  have hstate : curveState hT u t = (u ⟨t, ht⟩).val := curveState_coe hT u ⟨t, ht⟩
  have hpt : (u ⟨t, ht⟩).val = duhamelIntegral hα.le t (sourceFun hT f)
      - duhamelIntegral hα.le t (quadCurve hm (curveState hT u)) :=
    mild_pointwise_of_curve hα hT hm hr hmild ⟨t, ht⟩
  have hsplit : (duhamelIntegral hα.le t (sourceFun hT f)
      - duhamelIntegral hα.le t (quadCurve hm (curveState hT u))).coeff k
      = (duhamelIntegral hα.le t (sourceFun hT f)).coeff k
        - (duhamelIntegral hα.le t (quadCurve hm (curveState hT u))).coeff k := rfl
  rw [hstate, hpt, hsplit, coeff_duhamelIntegral hα ht.1 hsc hsM k,
    coeff_duhamelIntegral hα ht.1 hq hqM k]
  exact (scalarDuhamel_sub (fracSymbol α k) _ _
    (continuous_wiener_coeff k hsc) (continuous_wiener_coeff k hq) t).symm

/-- **The coefficient evolution equation.**  At every interior time and every frequency the
Fourier coefficient of the mild solution is differentiable, with

    `d/dt u_k(t) = f_k(t) - (N_K(u(t),u(t)))_k - λ_k u_k(t)`. -/
theorem hasDerivAt_coeff_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun r : ℝ => (curveState hT u r).coeff k)
      ((sourceFun hT f t) k - (quadCurve hm (curveState hT u) t) k
        - (fracSymbol α k : ℂ) * (curveState hT u t).coeff k) t := by
  set G : ℝ → ℂ := fun s => (sourceFun hT f s) k - (quadCurve hm (curveState hT u) s) k with hGdef
  have hcs : Continuous (curveState hT u) := continuous_curveState hT u
  have hq : Continuous (quadCurve hm (curveState hT u)) := continuous_quadCurve hm hcs
  have hsc : Continuous (sourceFun hT f) := continuous_sourceFun hT f
  have hG : Continuous G :=
    (continuous_wiener_coeff k hsc).sub (continuous_wiener_coeff k hq)
  have hbase := hasDerivAt_scalarDuhamel (fracSymbol α k) hG t
  have hmemt : t ∈ Set.Icc (0:ℝ) T := ⟨ht0.le, htT.le⟩
  have hvalt : scalarDuhamel (fracSymbol α k) G t = (curveState hT u t).coeff k :=
    (coeff_mild_eq_scalarDuhamel hα hT hm hr hC hmild k hmemt).symm
  have heq : (fun r : ℝ => (curveState hT u r).coeff k)
      =ᶠ[nhds t] scalarDuhamel (fracSymbol α k) G := by
    have hopen : Set.Ioo (0:ℝ) T ∈ nhds t := isOpen_Ioo.mem_nhds ⟨ht0, htT⟩
    filter_upwards [hopen] with r hr'
    exact coeff_mild_eq_scalarDuhamel hα hT hm hr hC hmild k ⟨hr'.1.le, hr'.2.le⟩
  rw [← hvalt]
  exact hbase.congr_of_eventuallyEq heq

/-- **The evolution equation in the assignment's normal form.**  For every interior time and
every frequency `k`, with `λ_k = (4π²(k₀² + k₁²))^α`,

    `d/dt u_k(t) + λ_k u_k(t) + (N_K(u(t),u(t)))_k = f_k(t)`. -/
theorem coeff_evolution_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    deriv (fun r : ℝ => (curveState hT u r).coeff k) t
        + (((4 * Real.pi ^ 2 * (((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2)) ^ α : ℝ) : ℂ)
            * (curveState hT u t).coeff k
        + (quadCurve hm (curveState hT u) t) k
      = (sourceFun hT f t) k := by
  have hd := (hasDerivAt_coeff_of_mild hα hT hm hr hC hmild k ht0 htT).deriv
  have hlam : ((4 * Real.pi ^ 2 * (((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2)) ^ α : ℝ)
      = fracSymbol α k := by
    rw [fracSymbol, sqNorm]
  rw [hd, hlam]
  ring

/-- **The initial trace.**  Every coefficient of the mild solution vanishes at `t = 0`. -/
theorem coeff_initial_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam) :
    (curveState hT u 0).coeff k = 0 := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_rfl, hT⟩
  have hstate : curveState hT u 0 = (u ⟨0, h0⟩).val := curveState_coe hT u ⟨0, h0⟩
  have hpt : (u ⟨0, h0⟩).val = duhamelIntegral hα.le (0:ℝ) (sourceFun hT f)
      - duhamelIntegral hα.le (0:ℝ) (quadCurve hm (curveState hT u)) :=
    mild_pointwise_of_curve hα hT hm hr hmild ⟨0, h0⟩
  have hz : duhamelIntegral hα.le (0:ℝ) (sourceFun hT f) = 0 := by
    rw [duhamelIntegral, intervalIntegral.integral_same]
  have hz' : duhamelIntegral hα.le (0:ℝ) (quadCurve hm (curveState hT u)) = 0 := by
    rw [duhamelIntegral, intervalIntegral.integral_same]
  rw [hstate, hpt, hz, hz', sub_zero]
  rfl

/-- The initial state itself vanishes. -/
theorem curveState_initial_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    curveState hT u 0 = 0 :=
  Wiener1.coeff_injective (funext fun k => coeff_initial_of_mild hα hT hm hr hmild k)

/-! ## Integration by parts against a time test function -/

/-- **Integration by parts.**  If `u` is continuous on `ℝ`, differentiable with derivative `D`
at every interior time of `[0,T]`, and `φ` is a `C¹` time test function whose (closed) support
is contained in the open interval, then `∫₀^T (D φ + u φ') = 0`. -/
theorem integral_test_of_hasDerivAt {T : ℝ} {u D φ ψ : ℝ → ℂ}
    (hu : Continuous u) (hD : Continuous D) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt u (D t) t)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t)
    (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T, (D t * φ t + u t * ψ t)) = 0 := by
  have hvanish : ∀ t : ℝ, t ∉ tsupport φ → ∀ᶠ r in nhds t, φ r = 0 := by
    intro t hmem
    have hopen : (tsupport φ)ᶜ ∈ nhds t := (isClosed_closure).isOpen_compl.mem_nhds hmem
    filter_upwards [hopen] with r hr
    by_contra hne
    exact hr (subset_closure (Function.mem_support.2 hne))
  have hzeroOut : ∀ t : ℝ, t ∉ tsupport φ → φ t = 0 := by
    intro t hmem
    by_contra hne
    exact hmem (subset_closure (Function.mem_support.2 hne))
  have hprod : ∀ t : ℝ, HasDerivAt (fun r => u r * φ r) (D t * φ t + u t * ψ t) t := by
    intro t
    by_cases hmem : t ∈ tsupport φ
    · exact (hderiv t (hsupp hmem)).mul (hφderiv t)
    · have hev := hvanish t hmem
      have hψt : ψ t = 0 := by
        have hc : HasDerivAt φ 0 t :=
          (hasDerivAt_const t (0:ℂ)).congr_of_eventuallyEq (by filter_upwards [hev] with r hr
            using hr)
        exact (hφderiv t).unique hc
      have hφt : φ t = 0 := hzeroOut t hmem
      have hzero : (fun r => u r * φ r) =ᶠ[nhds t] fun _ => (0:ℂ) := by
        filter_upwards [hev] with r hr
        rw [hr, mul_zero]
      have hbase : HasDerivAt (fun r => u r * φ r) 0 t :=
        (hasDerivAt_const t (0:ℂ)).congr_of_eventuallyEq hzero
      rw [hφt, hψt, mul_zero, mul_zero, add_zero]
      exact hbase
  have hcont : Continuous fun t => D t * φ t + u t * ψ t := (hD.mul hφ).add (hu.mul hψ)
  have hbdry : (∫ t in (0:ℝ)..T, (D t * φ t + u t * ψ t)) = u T * φ T - u 0 * φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprod t)
      (hcont.intervalIntegrable 0 T)
  have h0 : φ 0 = 0 := hzeroOut 0 (fun hc => (hsupp hc).1.false)
  have hT' : φ T = 0 := hzeroOut T (fun hc => (hsupp hc).2.false)
  rw [hbdry, h0, hT', mul_zero, mul_zero, sub_zero]

/-! ## The weak coefficient equation -/

/-- **The weak coefficient equation for the mild solution.**  For every frequency `k` and every
`C¹` time test function supported in `(0,T)`,

    `∫₀^T ( -u_k φ' + λ_k u_k φ + (N_K(u,u))_k φ - f_k φ ) dt = 0`. -/
theorem weak_coeff_of_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T, (-((curveState hT u t).coeff k) * ψ t
        + (fracSymbol α k : ℂ) * (curveState hT u t).coeff k * φ t
        + (quadCurve hm (curveState hT u) t) k * φ t
        - (sourceFun hT f t) k * φ t)) = 0 := by
  set uk : ℝ → ℂ := fun r => (curveState hT u r).coeff k with hukdef
  set D : ℝ → ℂ := fun r => (sourceFun hT f r) k - (quadCurve hm (curveState hT u) r) k
      - (fracSymbol α k : ℂ) * (curveState hT u r).coeff k with hDdef
  have hcs : Continuous (curveState hT u) := continuous_curveState hT u
  have hu : Continuous uk := continuous_coeff_curveState hT u k
  have hD : Continuous D :=
    ((continuous_wiener_coeff k (continuous_sourceFun hT f)).sub
      (continuous_wiener_coeff k (continuous_quadCurve hm hcs))).sub (continuous_const.mul hu)
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt uk (D t) t := fun t ht =>
    hasDerivAt_coeff_of_mild hα hT hm hr hC hmild k ht.1 ht.2
  have hkey := integral_test_of_hasDerivAt hu hD hφ hψ hderiv hφderiv hsupp
  have hrewrite : (fun t : ℝ => -(uk t) * ψ t
      + (fracSymbol α k : ℂ) * uk t * φ t
      + (quadCurve hm (curveState hT u) t) k * φ t
      - (sourceFun hT f t) k * φ t)
      = fun t : ℝ => -(D t * φ t + uk t * ψ t) := by
    funext t
    simp only [hDdef]
    ring
  rw [hrewrite, intervalIntegral.integral_neg, hkey, neg_zero]

/-- The `C¹`-compactly-supported form of the weak coefficient equation. -/
theorem weak_coeff_of_mild_contDiff (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) (k : Gam)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T, (-((curveState hT u t).coeff k) * deriv φ t
        + (fracSymbol α k : ℂ) * (curveState hT u t).coeff k * φ t
        + (quadCurve hm (curveState hT u) t) k * φ t
        - (sourceFun hT f t) k * φ t)) = 0 :=
  weak_coeff_of_mild hα hT hm hr hC hmild k hφ.continuous
    (hφ.continuous_deriv le_rfl)
    (fun t => ((hφ.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt) hsupp

/-! ## The linear evolution satisfied by the Duhamel term -/

/-- Coefficients of the Duhamel curve are scalar Duhamel integrals. -/
theorem coeff_duhamelOp_eq_scalarDuhamel (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (curveState hT (duhamelOp hα hT g) t).coeff k
      = scalarDuhamel (fracSymbol α k) (fun s => (sourceFun hT g s) k) t := by
  have hsc : Continuous (sourceFun hT g) := continuous_sourceFun hT g
  have hsM : ∀ s, ‖sourceFun hT g s‖ ≤ ‖g‖ := fun s => norm_sourceFun_le hT g s
  have hstate : curveState hT (duhamelOp hα hT g) t = (duhamelOp hα hT g ⟨t, ht⟩).val :=
    curveState_coe hT _ ⟨t, ht⟩
  have hval : (duhamelOp hα hT g ⟨t, ht⟩).val = duhamelIntegral hα.le t (sourceFun hT g) :=
    duhamelOp_apply_val hα hT g ⟨t, ht⟩
  rw [hstate, hval, coeff_duhamelIntegral hα ht.1 hsc hsM k]

/-- **The linear coefficient evolution of the Duhamel term**:
`d/dt (J_T g)_k(t) + λ_k (J_T g)_k(t) = g_k(t)` at interior times. -/
theorem hasDerivAt_coeff_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun r : ℝ => (curveState hT (duhamelOp hα hT g) r).coeff k)
      ((sourceFun hT g t) k
        - (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k) t := by
  have hsc : Continuous (sourceFun hT g) := continuous_sourceFun hT g
  have hG : Continuous fun s => (sourceFun hT g s) k := continuous_wiener_coeff k hsc
  have hbase := hasDerivAt_scalarDuhamel (fracSymbol α k) hG t
  have hmemt : t ∈ Set.Icc (0:ℝ) T := ⟨ht0.le, htT.le⟩
  have hvalt : scalarDuhamel (fracSymbol α k) (fun s => (sourceFun hT g s) k) t
      = (curveState hT (duhamelOp hα hT g) t).coeff k :=
    (coeff_duhamelOp_eq_scalarDuhamel hα hT g k hmemt).symm
  have heq : (fun r : ℝ => (curveState hT (duhamelOp hα hT g) r).coeff k)
      =ᶠ[nhds t] scalarDuhamel (fracSymbol α k) (fun s => (sourceFun hT g s) k) := by
    have hopen : Set.Ioo (0:ℝ) T ∈ nhds t := isOpen_Ioo.mem_nhds ⟨ht0, htT⟩
    filter_upwards [hopen] with r hr'
    exact coeff_duhamelOp_eq_scalarDuhamel hα hT g k ⟨hr'.1.le, hr'.2.le⟩
  rw [← hvalt]
  exact hbase.congr_of_eventuallyEq heq

/-- The Duhamel term starts at zero. -/
theorem coeff_duhamelOp_initial (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam) :
    (curveState hT (duhamelOp hα hT g) 0).coeff k = 0 := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_rfl, hT⟩
  rw [coeff_duhamelOp_eq_scalarDuhamel hα hT g k h0, scalarDuhamel,
    intervalIntegral.integral_same]

/-- **The weak linear equation for the Duhamel term.** -/
theorem weak_coeff_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam)
    {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφderiv : ∀ t, HasDerivAt φ (ψ t) t) (hsupp : tsupport φ ⊆ Set.Ioo (0:ℝ) T) :
    (∫ t in (0:ℝ)..T, (-((curveState hT (duhamelOp hα hT g) t).coeff k) * ψ t
        + (fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k * φ t
        - (sourceFun hT g t) k * φ t)) = 0 := by
  set wk : ℝ → ℂ := fun r => (curveState hT (duhamelOp hα hT g) r).coeff k with hwkdef
  set D : ℝ → ℂ := fun r => (sourceFun hT g r) k - (fracSymbol α k : ℂ) * wk r with hDdef
  have hu : Continuous wk := continuous_coeff_curveState hT _ k
  have hD : Continuous D :=
    (continuous_wiener_coeff k (continuous_sourceFun hT g)).sub (continuous_const.mul hu)
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt wk (D t) t := fun t ht =>
    hasDerivAt_coeff_duhamelOp hα hT g k ht.1 ht.2
  have hkey := integral_test_of_hasDerivAt hu hD hφ hψ hderiv hφderiv hsupp
  have hrewrite : (fun t : ℝ => -(wk t) * ψ t + (fracSymbol α k : ℂ) * wk t * φ t
      - (sourceFun hT g t) k * φ t) = fun t : ℝ => -(D t * φ t + wk t * ψ t) := by
    funext t
    simp only [hDdef]
    ring
  rw [hrewrite, intervalIntegral.integral_neg, hkey, neg_zero]

end LiWang.Formalization
