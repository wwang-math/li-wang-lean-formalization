/-
# The coefficient `ℓ²` carrier, the physical representative, and `H^{2α}` regularity

The orthonormal family of Fourier monomials in `L²(𝕋²)` induces a **linear isometry**
`ℓ²(Γ) →ₗᵢ[ℂ] L²(𝕋²)`.  Combined with the `L²`-in-time energy estimate of `DuhamelL2.lean`
this gives, for almost every time, an actual physical `L²` representative of `(-Δ)^α u(t)`
and membership of `u(t)` in the coefficient space `H^{2α}`.

The `H^{2α}` regularity is **not** inferred from `u(t) ∈ A¹` — that implication is false for
`2α > 1`.  It is obtained from the energy estimate for the Duhamel response.

Part of `LiWangWienerObservationBridgePacket` v4.0.
-/
import LiWangWiener.PhysicalL2
import LiWangWiener.DuhamelL2
import LiWangWiener.VariationODE
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate ENNReal NNReal
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

/-! ## The coefficient `ℓ²` space and its isometry into `L²(𝕋²)` -/

/-- The **coefficient `ℓ²` space** `ℓ²(Γ)`. -/
abbrev Wiener2 : Type := lp (fun _ : Gam => ℂ) 2

theorem memLp2_of_summable_sq {c : Gam → ℂ} (hc : Summable fun k => ‖c k‖ ^ 2) :
    Memℓp c 2 := by
  refine memℓp_gen ?_
  have h : ∀ k : Gam, ‖c k‖ ^ (2 : ℝ≥0∞).toReal = ‖c k‖ ^ (2 : ℕ) := by
    intro k
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa only [h] using hc

/-- Build an `ℓ²` coefficient family from square summability. -/
noncomputable def w2mk (c : Gam → ℂ) (hc : Summable fun k => ‖c k‖ ^ 2) : Wiener2 :=
  ⟨c, memLp2_of_summable_sq hc⟩

@[simp] theorem w2mk_apply (c : Gam → ℂ) (hc : Summable fun k => ‖c k‖ ^ 2) (k : Gam) :
    (w2mk c hc) k = c k := rfl

/-- **The coefficient `ℓ²` space embeds isometrically in the physical `L²` space** of the
torus, by summing the Fourier series against the orthonormal monomials. -/
noncomputable def coeffL2 : Wiener2 →ₗᵢ[ℂ] TorusL2 :=
  orthonormal_synthL2_wdirac.orthogonalFamily.linearIsometry

theorem coeffL2_apply (c : Wiener2) :
    coeffL2 c = ∑' k : Gam, (c k) • synthL2 (wdirac k) := by
  rw [coeffL2, OrthogonalFamily.linearIsometry_apply]
  exact tsum_congr fun k => LinearIsometry.toSpanSingleton_apply _ _

theorem norm_coeffL2 (c : Wiener2) : ‖coeffL2 c‖ = ‖c‖ := coeffL2.norm_map c

theorem hasSum_coeffL2 (c : Wiener2) :
    HasSum (fun k : Gam => (c k) • synthL2 (wdirac k)) (coeffL2 c) := by
  have h := orthonormal_synthL2_wdirac.orthogonalFamily.hasSum_linearIsometry c
  have hfun : (fun k : Gam =>
      (LinearIsometry.toSpanSingleton ℂ TorusL2
        (orthonormal_synthL2_wdirac.1 k)) (c k))
      = fun k : Gam => (c k) • synthL2 (wdirac k) := by
    funext k
    exact LinearIsometry.toSpanSingleton_apply _ _
  rw [hfun] at h
  exact h

/-! ## Consistency with the `ℓ¹` synthesis -/

theorem summable_norm_sq_wiener (a : Wiener) : Summable fun k => ‖a k‖ ^ 2 :=
  summable_norm_sq a

/-- A Wiener (`ℓ¹`) state, viewed in the coefficient `ℓ²` space. -/
noncomputable def toWiener2 (a : Wiener) : Wiener2 :=
  w2mk (fun k => a k) (summable_norm_sq_wiener a)

@[simp] theorem toWiener2_apply (a : Wiener) (k : Gam) : (toWiener2 a) k = a k := rfl

/-- **The two synthesis maps agree** on `ℓ¹` states: the `ℓ²` isometry extends the physical
`L²` synthesis of `Wiener`. -/
theorem coeffL2_toWiener2 (a : Wiener) : coeffL2 (toWiener2 a) = synthL2 a := by
  have hsum : Summable fun k : Gam => (a k) • emode k := summable_synth a
  have hmap := ContinuousLinearMap.map_tsum
    (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure Torus2) ℂ) hsum
  have hs : synthL2 a = ∑' k : Gam, (a k) • synthL2 (wdirac k) := by
    calc synthL2 a
        = (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure Torus2) ℂ)
            (∑' k : Gam, (a k) • emode k) :=
          congrArg (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure Torus2) ℂ) (synth_def a)
      _ = ∑' k : Gam,
            (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure Torus2) ℂ) ((a k) • emode k) := hmap
      _ = ∑' k : Gam, (a k) • synthL2 (wdirac k) := by
          refine tsum_congr fun k => ?_
          rw [map_smul, synthL2_wdirac]
  rw [coeffL2_apply, hs]
  rfl

/-! ## The `Hˢ` coefficient spaces -/

/-- The squared `Hˢ` weight `(1 + |k|²)ˢ` in the Euclidean frequency length. -/
noncomputable def sobWeight (s : ℝ) (k : Gam) : ℝ := (1 + sqNorm k) ^ s

theorem sobWeight_pos (s : ℝ) (k : Gam) : 0 < sobWeight s k := by
  have h : (0:ℝ) < 1 + sqNorm k := by have := sqNorm_nonneg k; linarith
  exact Real.rpow_pos_of_pos h s

/-- Membership of a coefficient family in the (coefficient) Sobolev space `Hˢ(𝕋²)`. -/
def MemSobolev (s : ℝ) (c : Gam → ℂ) : Prop := Summable fun k => sobWeight s k * ‖c k‖ ^ 2

theorem rpow_one_add_le {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) :
    (1 + x) ^ s ≤ 2 ^ s * (1 + x ^ s) := by
  have h2 : (0:ℝ) ≤ (2:ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
  have hxs : (0:ℝ) ≤ x ^ s := Real.rpow_nonneg hx s
  rcases le_total x 1 with h | h
  · have h1 : (1 + x) ^ s ≤ (2:ℝ) ^ s := Real.rpow_le_rpow (by linarith) (by linarith) hs
    nlinarith
  · have h1 : (1 + x) ^ s ≤ (2 * x) ^ s := Real.rpow_le_rpow (by linarith) (by linarith) hs
    rw [Real.mul_rpow (by norm_num) hx] at h1
    nlinarith

theorem sq_fracSymbol_eq {α : ℝ} (hα : 0 < α) (k : Gam) :
    (fracSymbol α k) ^ 2 = (4 * Real.pi ^ 2) ^ (2 * α) * (sqNorm k) ^ (2 * α) := by
  have hb : (0:ℝ) ≤ 4 * Real.pi ^ 2 * sqNorm k := by
    have := sqNorm_nonneg k
    have hpi := Real.pi_pos
    positivity
  have h1 : (fracSymbol α k) ^ 2 = (4 * Real.pi ^ 2 * sqNorm k) ^ (2 * α) := by
    rw [fracSymbol, ← Real.rpow_natCast ((4 * Real.pi ^ 2 * sqNorm k) ^ α) 2,
      ← Real.rpow_mul hb]
    norm_num
    ring_nf
  rw [h1, Real.mul_rpow (by positivity) (sqNorm_nonneg k)]

/-- **`H^{2α}` membership from square summability of the state and of its fractional
multiplier.**  Nothing here uses `A¹` membership: the `H^{2α}` control comes from the energy
estimate, not from the Wiener norm. -/
theorem memSobolev_two_alpha {α : ℝ} (hα : 0 < α) {c : Gam → ℂ}
    (h1 : Summable fun k => ‖c k‖ ^ 2)
    (h2 : Summable fun k => ‖(fracSymbol α k : ℂ) * c k‖ ^ 2) :
    MemSobolev (2 * α) c := by
  have hpi : (0:ℝ) < 4 * Real.pi ^ 2 := by have := Real.pi_pos; positivity
  set C : ℝ := (2:ℝ) ^ (2 * α) with hC
  set B : ℝ := (4 * Real.pi ^ 2) ^ (2 * α) with hB
  have hCnn : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
  have hBpos : 0 < B := Real.rpow_pos_of_pos hpi _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((h1.mul_left C).add ((h2.mul_left (C / B))))
  · exact mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _)
  · have hs : sobWeight (2 * α) k ≤ C * (1 + (sqNorm k) ^ (2 * α)) :=
      rpow_one_add_le (sqNorm_nonneg k) (by linarith)
    have hsq : ‖(fracSymbol α k : ℂ) * c k‖ ^ 2 = (fracSymbol α k) ^ 2 * ‖c k‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have hfs : (sqNorm k) ^ (2 * α) = (fracSymbol α k) ^ 2 / B := by
      rw [sq_fracSymbol_eq hα k, hB]
      field_simp
    have hnn : (0:ℝ) ≤ ‖c k‖ ^ 2 := sq_nonneg _
    calc sobWeight (2 * α) k * ‖c k‖ ^ 2
        ≤ (C * (1 + (sqNorm k) ^ (2 * α))) * ‖c k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hs hnn
      _ = C * ‖c k‖ ^ 2 + (C / B) * ((fracSymbol α k) ^ 2 * ‖c k‖ ^ 2) := by
          rw [hfs]
          field_simp
      _ = C * ‖c k‖ ^ 2 + (C / B) * ‖(fracSymbol α k : ℂ) * c k‖ ^ 2 := by rw [hsq]

/-! ## The physical representative of the fractional Laplacian -/

/-- The physical `L²(𝕋²)` representative of `(-Δ)^α` applied to a coefficient family whose
fractional multiplier is square summable. -/
noncomputable def fracLapRep {α : ℝ} (c : Gam → ℂ)
    (h : Summable fun k => ‖(fracSymbol α k : ℂ) * c k‖ ^ 2) : TorusL2 :=
  coeffL2 (w2mk (fun k => (fracSymbol α k : ℂ) * c k) h)

theorem norm_w2mk_sq (c : Gam → ℂ) (hc : Summable fun k => ‖c k‖ ^ 2) :
    ‖w2mk c hc‖ ^ 2 = ∑' k : Gam, ‖c k‖ ^ 2 := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hnorm := lp.norm_eq_tsum_rpow hp (w2mk c hc)
  have hcast : ∀ k : Gam, ‖(w2mk c hc) k‖ ^ (2 : ℝ≥0∞).toReal = ‖c k‖ ^ 2 := by
    intro k
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rfl
  rw [hnorm]
  simp only [hcast]
  have hnn : (0:ℝ) ≤ ∑' k : Gam, ‖c k‖ ^ 2 :=
    tsum_nonneg (fun k => sq_nonneg _)
  rw [show (1 : ℝ) / (2 : ℝ≥0∞).toReal = 1 / 2 by norm_num,
    ← Real.rpow_natCast ((∑' k : Gam, ‖c k‖ ^ 2) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hnn]
  norm_num

/-- **Parseval for the physical representative.** -/
theorem norm_fracLapRep_sq {α : ℝ} (c : Gam → ℂ)
    (h : Summable fun k => ‖(fracSymbol α k : ℂ) * c k‖ ^ 2) :
    ‖fracLapRep (α := α) c h‖ ^ 2 = ∑' k : Gam, ‖(fracSymbol α k : ℂ) * c k‖ ^ 2 := by
  rw [fracLapRep, norm_coeffL2, norm_w2mk_sq]

/-! ## The strong equation in integrated Bochner form -/

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-- The candidate for the time-integral of `(-Δ)^α u` over `[0,t]`, defined — without any
regularity assumption — as `∫₀ᵗ g − u(t)`, hence automatically an element of the Wiener algebra.
That it really *is* that Bochner integral is proved in `PhysicalFractionalField`
(`synthL2_fracTimeIntegral`); the definition by itself proves nothing of the kind. -/
noncomputable def fracTimeIntegral (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) :
    Wiener :=
  (∫ s in (0:ℝ)..t, sourceFun hT g s) - incl (curveState hT (duhamelOp hα hT g) t)

/-- **An algebraic identity, by construction of `fracTimeIntegral`.**  Since
`fracTimeIntegral hα hT g t` is *defined* as `∫₀ᵗ g(s) ds − u(t)`, this rearrangement is
immediate.  The definition alone is **not** a construction of the Bochner integral of the
pointwise fractional-Laplacian field: no strongly measurable field `s ↦ (-Δ)^α u(s)` is built
here.  What *is* proved here is `coeff_fracTimeIntegral`: the Fourier coefficients of
`fracTimeIntegral` are `λ_k` times those of the time primitive of `u` (see also
`fracTimeIntegral_is_frac_of_primitive` in `PrimitiveGraph`).  The genuine field, its
`L²`-in-time bound and Bochner integrability, and the identification
`synthL2 (fracTimeIntegral …) = ∫₀ᵗ (-Δ)^α u(s) ds` are built in `PhysicalFractionalField`. -/
theorem strong_equation_integrated (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (t : ℝ) :
    incl (curveState hT (duhamelOp hα hT g) t) + fracTimeIntegral hα hT g t
      = ∫ s in (0:ℝ)..t, sourceFun hT g s := by
  rw [fracTimeIntegral]
  abel

/-- **The coefficients of that Bochner integral are the expected ones**: `λ_k ∫₀ᵗ u_k`.  This
is where the coefficient evolution equation is actually used. -/
theorem coeff_fracTimeIntegral (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) (k : Gam)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    (fracTimeIntegral hα hT g t) k
      = (fracSymbol α k : ℂ)
          * ∫ s in (0:ℝ)..t, (curveState hT (duhamelOp hα hT g) s).coeff k := by
  have hg : Continuous (sourceFun hT g) := continuous_sourceFun hT g
  have hsplit : ((∫ s in (0:ℝ)..t, sourceFun hT g s) : Wiener) k
      = ∫ s in (0:ℝ)..t, (sourceFun hT g s) k :=
    ((Wiener.evalCLM k).intervalIntegral_comp_comm (hg.intervalIntegrable 0 t)).symm
  have hkey := coeff_duhamelOp_integrated hα hT g k ht
  show ((∫ s in (0:ℝ)..t, sourceFun hT g s) - incl (curveState hT (duhamelOp hα hT g) t) :
      Wiener) k = _
  rw [lp.coeFn_sub, Pi.sub_apply, hsplit]
  show (∫ s in (0:ℝ)..t, (sourceFun hT g s) k)
      - (curveState hT (duhamelOp hα hT g) t).coeff k = _
  rw [← hkey]
  ring

/-! ## Almost-everywhere `H^{2α}` regularity of the Duhamel response -/

theorem summable_norm_sq_curveState (hT : 0 ≤ T) (u : Curve1 T) (t : ℝ) :
    Summable fun k : Gam => ‖(curveState hT u t).coeff k‖ ^ 2 :=
  summable_norm_sq (incl (curveState hT u t))

/-- **`H^{2α}` regularity of the Duhamel response for almost every time.** -/
theorem ae_memSobolev_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α) (curveState hT (duhamelOp hα hT g) t).coeff := by
  have hα0 : (0:ℝ) < α := by linarith
  filter_upwards [ae_summable_fracSymbol_sq hα hT g] with t ht
  exact memSobolev_two_alpha hα0 (summable_norm_sq_curveState hT _ t) ht

/-- **The physical `L²` representative of `(-Δ)^α u(t)` exists for almost every time**, with
its Parseval norm. -/
theorem ae_exists_fracLapRep (hα : 1 / 2 < α) (hT : 0 ≤ T) (g : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      ∃ h : Summable fun k : Gam =>
          ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2,
        ‖fracLapRep (α := α) (curveState hT (duhamelOp hα hT g) t).coeff h‖ ^ 2
          = ∑' k : Gam,
              ‖(fracSymbol α k : ℂ) * (curveState hT (duhamelOp hα hT g) t).coeff k‖ ^ 2 := by
  filter_upwards [ae_summable_fracSymbol_sq hα hT g] with t ht
  exact ⟨ht, norm_fracLapRep_sq _ ht⟩

/-! ## Application to the nonlinear state and its two responses -/

/-- **The nonlinear mild state is itself a Duhamel response**, with source `f − N_K(u,u)`, so
every result above applies to it. -/
theorem mild_curve_eq_duhamelOp (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    u = duhamelOp hα hT (f - spacetimeTransport m hm hr u u) := by
  rw [map_sub, ← sourceQuad_apply hα hT m hm hr u u, ← hmild]
  abel

/-- The `L²`-in-time estimate for the **nonlinear** state. -/
theorem tsum_integral_fracSymbol_sq_mild_le (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    (∑' k : Gam, (fracSymbol α k) ^ 2
        * ∫ t in (0:ℝ)..T, ‖(curveState hT u t).coeff k‖ ^ 2)
      ≤ T * ‖f - spacetimeTransport m hm hr u u‖ ^ 2 := by
  set g : Curve0 T := f - spacetimeTransport m hm hr u u with hg
  have hu : u = duhamelOp hα hT g := mild_curve_eq_duhamelOp hα hT hm hr hmild
  rw [hu]
  exact tsum_integral_fracSymbol_sq_le hα hT g

/-- `H^{2α}` regularity of the **nonlinear** state for almost every time. -/
theorem ae_memSobolev_mild (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u : Curve1 T} {f : Curve0 T}
    (hmild : u + sourceQuad hα hT m hm hr u u = duhamelOp hα hT f) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α) (curveState hT u t).coeff := by
  set g : Curve0 T := f - spacetimeTransport m hm hr u u with hg
  have hu : u = duhamelOp hα hT g := mild_curve_eq_duhamelOp hα hT hm hr hmild
  rw [hu]
  exact ae_memSobolev_duhamelOp hα hT g

/-- The `L²`-in-time estimate for the **first source response** `DS_K(0)[h] = J_T h`. -/
theorem tsum_integral_fracSymbol_sq_firstResponse_le (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h : Curve0 T) :
    (∑' k : Gam, (fracSymbol α k) ^ 2
        * ∫ t in (0:ℝ)..T,
            ‖(curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).coeff k‖ ^ 2)
      ≤ T * ‖h‖ ^ 2 := by
  rw [curveState_fderiv_sourceSolution hα hT hm hr h]
  exact tsum_integral_fracSymbol_sq_le hα hT h

theorem ae_memSobolev_firstResponse (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α)
        (curveState hT (fderiv ℝ (sourceSolution hα hT hm hr) (0 : Curve0 T) h) t).coeff := by
  rw [curveState_fderiv_sourceSolution hα hT hm hr h]
  exact ae_memSobolev_duhamelOp hα hT h

/-- The `L²`-in-time estimate for the **second source response**
`D²S_K(0)[h₁,h₂] = -J_T(N_K(J h₁, J h₂) + N_K(J h₂, J h₁))`. -/
theorem tsum_integral_fracSymbol_sq_secondResponse_le (hα : 1 / 2 < α) (hT : 0 ≤ T)
    (hm : IsBddSymbol m) (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    (∑' k : Gam, (fracSymbol α k) ^ 2
        * ∫ t in (0:ℝ)..T,
            ‖(curveState hT (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr))
                (0 : Curve0 T) h₁ h₂) t).coeff k‖ ^ 2)
      ≤ T * ‖secondVariationSource hα hT hm hr h₁ h₂‖ ^ 2 := by
  rw [curveState_fderiv_fderiv_sourceSolution hα hT hm hr h₁ h₂]
  exact tsum_integral_fracSymbol_sq_le hα hT _

theorem ae_memSobolev_secondResponse (hα : 1 / 2 < α) (hT : 0 ≤ T) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : Curve0 T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) T)),
      MemSobolev (2 * α)
        (curveState hT (fderiv ℝ (fderiv ℝ (sourceSolution hα hT hm hr))
          (0 : Curve0 T) h₁ h₂) t).coeff := by
  rw [curveState_fderiv_fderiv_sourceSolution hα hT hm hr h₁ h₂]
  exact ae_memSobolev_duhamelOp hα hT _

end LiWang.WienerModel
