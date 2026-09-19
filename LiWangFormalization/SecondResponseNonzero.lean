/-
# A nonzero mixed second source response for an explicit real forcing profile

Everything here is about the *actual* forced solution map `S_K` of `SourceSolution.lean`, not
about a model of it.  Two ingredients:

* the Duhamel operator `J_T` is **injective** for `T > 0` (proved from the coefficient
  evolution equation, so no nonzero source produces the zero response);
* for the explicit constant-in-time real forcing profile whose synthesis is
  `2·cos(2πx₀) + 2·cos(2πx₁)` (each of `cosMode1 e₀`, `cosMode1 e₁` puts coefficient one on
  *both* `±eⱼ`, so the physical amplitude is two, not one) and
  the finite-support kernel, the transported second-variation source is nonzero.

Together they give `D²S_K(0)[f,f] ≠ 0`: the second source response of the forced solution map
is genuinely nondegenerate, not merely the nonvanishing of the transport form.

Part of `LiWangFormalizationSourceResponsePacket` v3.0.
-/
import LiWangFormalization.VariationODE
import LiWangFormalization.HessianNonDegeneracy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

variable {α T : ℝ} {m : Fin 2 → Gam → ℂ}

/-! ## The exponential window -/

/-- The scalar Duhamel integral of the constant source `1`. -/
noncomputable def expWindow (lam t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, Real.exp (-((t - s) * lam))

theorem continuous_expIntegrand (lam t : ℝ) :
    Continuous fun s : ℝ => Real.exp (-((t - s) * lam)) :=
  Real.continuous_exp.comp (((continuous_const.sub continuous_id).mul continuous_const).neg)

/-- **The exponential window is strictly positive at positive times.** -/
theorem expWindow_pos (lam : ℝ) {t : ℝ} (ht : 0 < t) : 0 < expWindow lam t := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_expIntegrand lam t).intervalIntegrable 0 t) (fun x _ => Real.exp_pos _) ht

/-- The scalar Duhamel integral of a constant. -/
theorem scalarDuhamel_const (lam : ℝ) (c : ℂ) (t : ℝ) :
    scalarDuhamel lam (fun _ => c) t = c * ((expWindow lam t : ℝ) : ℂ) := by
  have hofReal : (∫ s in (0:ℝ)..t, ((Real.exp (-((t - s) * lam)) : ℝ) : ℂ))
      = ((∫ s in (0:ℝ)..t, Real.exp (-((t - s) * lam)) : ℝ) : ℂ) :=
    ContinuousLinearMap.intervalIntegral_comp_comm Complex.ofRealCLM
      ((continuous_expIntegrand lam t).intervalIntegrable 0 t)
  have hmul := intervalIntegral.integral_mul_const (a := (0:ℝ)) (b := t)
    (μ := (volume : Measure ℝ)) c (fun s : ℝ => ((Real.exp (-((t - s) * lam)) : ℝ) : ℂ))
  rw [scalarDuhamel]
  calc (∫ s in (0:ℝ)..t, ((Real.exp (-((t - s) * lam)) : ℝ) : ℂ) * (fun _ : ℝ => c) s)
      = (∫ s in (0:ℝ)..t, ((Real.exp (-((t - s) * lam)) : ℝ) : ℂ)) * c := hmul
    _ = ((expWindow lam t : ℝ) : ℂ) * c := by
        rw [expWindow]; exact congrArg (fun z : ℂ => z * c) hofReal
    _ = c * ((expWindow lam t : ℝ) : ℂ) := mul_comm _ _

/-! ## Injectivity of the Duhamel operator -/

/-- **The Duhamel operator is injective on a nondegenerate time interval.**  A source whose
Duhamel response vanishes identically is itself zero: this is read off from the coefficient
evolution equation, which forces every coefficient of the source to vanish at interior
times. -/
theorem eq_zero_of_duhamelOp_eq_zero (hα : 1 / 2 < α) (hT : 0 < T) {g : Curve0 T}
    (h : duhamelOp hα hT.le g = 0) : g = 0 := by
  have hstate : ∀ r : ℝ, curveState hT.le (duhamelOp hα hT.le g) r = 0 := by
    intro r
    rw [curveState, h]
    rfl
  have hcoeffs : ∀ (t : ℝ), 0 < t → t < T → ∀ k : Gam, (sourceFun hT.le g t) k = 0 := by
    intro t ht0 htT k
    have hd := hasDerivAt_coeff_duhamelOp hα hT.le g k ht0 htT
    have hfun : (fun r : ℝ => (curveState hT.le (duhamelOp hα hT.le g) r).coeff k)
        = fun _ : ℝ => (0 : ℂ) := by
      funext r
      rw [hstate r]
      rfl
    have hconst : HasDerivAt
        (fun r : ℝ => (curveState hT.le (duhamelOp hα hT.le g) r).coeff k) 0 t := by
      rw [hfun]
      exact hasDerivAt_const t (0 : ℂ)
    have huniq := hd.unique hconst
    have hz : (curveState hT.le (duhamelOp hα hT.le g) t).coeff k = 0 := by
      rw [hstate t]; rfl
    rwa [hz, mul_zero, sub_zero] at huniq
  have hIoo : ∀ t ∈ Set.Ioo (0:ℝ) T, sourceFun hT.le g t = 0 := by
    intro t ht
    ext k
    have hz : ((0 : Wiener) : Gam → ℂ) k = 0 := by simp only [lp.coeFn_zero, Pi.zero_apply]
    rw [hz]
    exact hcoeffs t ht.1 ht.2 k
  have hclosed : IsClosed {t : ℝ | sourceFun hT.le g t = 0} :=
    isClosed_eq (continuous_sourceFun hT.le g) continuous_const
  have hIcc : Set.Icc (0:ℝ) T ⊆ {t : ℝ | sourceFun hT.le g t = 0} := by
    have hsub : Set.Ioo (0:ℝ) T ⊆ {t : ℝ | sourceFun hT.le g t = 0} := hIoo
    have hcl := closure_minimal hsub hclosed
    rwa [closure_Ioo (ne_of_lt hT)] at hcl
  ext t
  apply RealWiener.val_injective
  have := hIcc ⟨t.2.1, t.2.2⟩
  rw [Set.mem_setOf_eq, sourceFun_coe hT.le g t] at this
  rw [this]
  rfl

theorem duhamelOp_ne_zero (hα : 1 / 2 < α) (hT : 0 < T) {g : Curve0 T} (hg : g ≠ 0) :
    duhamelOp hα hT.le g ≠ 0 :=
  fun h => hg (eq_zero_of_duhamelOp_eq_zero hα hT h)

/-! ## The explicit real forcing profile -/

/-- The two-mode real packet as an element of the real Wiener algebra. -/
noncomputable def realPacketW : RealWiener :=
  RealWiener.mk (incl realPacket) realPacket_conjSymmetric.incl

/-- The **explicit real forcing profile**: constant in time, equal to the real packet
`2·cos(2πx₀) + 2·cos(2πx₁)`. -/
noncomputable def packetSource (T : ℝ) : Curve0 T :=
  BoundedContinuousFunction.const (TimeI T) realPacketW

theorem sourceFun_packetSource (hT : 0 ≤ T) (s : ℝ) :
    sourceFun hT (packetSource T) s = incl realPacket := rfl

/-- Every frequency carrying the packet has squared length one. -/
theorem sqNorm_eq_one_of_realPacket_coeff_ne_zero {k : Gam} (hk : realPacket.coeff k ≠ 0) :
    sqNorm k = 1 := by
  have hsplit : realPacket.coeff k = cosModeFun (unitFreq 0) k + cosModeFun (unitFreq 1) k := rfl
  by_cases h0 : k = unitFreq 0
  · subst h0
    show ((unitFreq 0 0 : ℤ) : ℝ) ^ 2 + ((unitFreq 0 1 : ℤ) : ℝ) ^ 2 = 1
    rw [unitFreq_self, unitFreq_zero_one]; norm_num
  by_cases h1 : k = -unitFreq 0
  · subst h1
    have e0 : ((-unitFreq 0 : Gam) 0 : ℤ) = -1 := by
      show -((unitFreq 0) 0) = -1
      rw [unitFreq_self]
    have e1 : ((-unitFreq 0 : Gam) 1 : ℤ) = 0 := by
      show -((unitFreq 0) 1) = 0
      rw [unitFreq_zero_one]; ring
    show (((-unitFreq 0 : Gam) 0 : ℤ) : ℝ) ^ 2 + (((-unitFreq 0 : Gam) 1 : ℤ) : ℝ) ^ 2 = 1
    rw [e0, e1]; norm_num
  by_cases h2 : k = unitFreq 1
  · subst h2
    show ((unitFreq 1 0 : ℤ) : ℝ) ^ 2 + ((unitFreq 1 1 : ℤ) : ℝ) ^ 2 = 1
    rw [unitFreq_one_zero, unitFreq_self]; norm_num
  by_cases h3 : k = -unitFreq 1
  · subst h3
    have e0 : ((-unitFreq 1 : Gam) 0 : ℤ) = 0 := by
      show -((unitFreq 1) 0) = 0
      rw [unitFreq_one_zero]; ring
    have e1 : ((-unitFreq 1 : Gam) 1 : ℤ) = -1 := by
      show -((unitFreq 1) 1) = -1
      rw [unitFreq_self]
    show (((-unitFreq 1 : Gam) 0 : ℤ) : ℝ) ^ 2 + (((-unitFreq 1 : Gam) 1 : ℤ) : ℝ) ^ 2 = 1
    rw [e0, e1]; norm_num
  · exact absurd (by rw [hsplit, cosModeFun_eq_zero_of_ne h0 h1,
      cosModeFun_eq_zero_of_ne h2 h3, add_zero]) hk

theorem fracSymbol_of_realPacket_coeff_ne_zero (α : ℝ) {k : Gam}
    (hk : realPacket.coeff k ≠ 0) : fracSymbol α k = fracSymbol α (unitFreq 0) := by
  have h1 : sqNorm k = 1 := sqNorm_eq_one_of_realPacket_coeff_ne_zero hk
  have h2 : sqNorm (unitFreq 0) = 1 := by
    show ((unitFreq 0 0 : ℤ) : ℝ) ^ 2 + ((unitFreq 0 1 : ℤ) : ℝ) ^ 2 = 1
    rw [unitFreq_self, unitFreq_zero_one]; norm_num
  rw [fracSymbol, fracSymbol, h1, h2]

/-- **The Duhamel response of the constant packet forcing is a scalar multiple of the
packet** — all its frequencies share the same dissipation rate. -/
theorem curveState_duhamelOp_packetSource (hα : 1 / 2 < α) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    curveState hT (duhamelOp hα hT (packetSource T)) t
      = ((expWindow (fracSymbol α (unitFreq 0)) t : ℝ) : ℂ) • realPacket := by
  refine Wiener1.coeff_injective (funext fun k => ?_)
  rw [coeff_duhamelOp_eq_scalarDuhamel hα hT (packetSource T) k ht]
  have hsrc : (fun s : ℝ => (sourceFun hT (packetSource T) s) k)
      = fun _ : ℝ => realPacket.coeff k := by
    funext s
    rw [sourceFun_packetSource hT s]
    rfl
  rw [hsrc, scalarDuhamel_const]
  show realPacket.coeff k * ((expWindow (fracSymbol α k) t : ℝ) : ℂ)
      = ((expWindow (fracSymbol α (unitFreq 0)) t : ℝ) : ℂ) * realPacket.coeff k
  by_cases hk : realPacket.coeff k = 0
  · rw [hk, zero_mul, mul_zero]
  · rw [fracSymbol_of_realPacket_coeff_ne_zero α hk]
    ring

/-! ## Nonvanishing of the second source response -/

/-- The second-variation source of the packet forcing has a nonzero `(1,1)` coefficient at
every positive interior time. -/
theorem sourceFun_secondVariationSource_packet_coeff (hα : 1 / 2 < α) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) :
    (sourceFun hT (secondVariationSource hα hT
        (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric)
        (packetSource T) (packetSource T)) t) (unitFreq 0 + unitFreq 1)
      = -(2 * ((expWindow (fracSymbol α (unitFreq 0)) t : ℝ) : ℂ) ^ 2 * (twoPiI * twoPiI)) := by
  set c : ℂ := ((expWindow (fracSymbol α (unitFreq 0)) t : ℝ) : ℂ) with hc
  set hb := rotatedGradientSymbol_bdd finiteKernel_admissible with hbdef
  have hstate : (duhamelOp hα hT (packetSource T) (clampT hT t)).val = c • realPacket := by
    have hcs := curveState_duhamelOp_packetSource hα hT ht
    rw [curveState] at hcs
    exact hcs
  rw [sourceFun_secondVariationSource, hstate]
  have h1 : transport (rotatedGradientSymbol finiteKernel.coeff) hb (c • realPacket)
      = c • transport (rotatedGradientSymbol finiteKernel.coeff) hb realPacket :=
    map_smul _ c realPacket
  have hbil : transport (rotatedGradientSymbol finiteKernel.coeff) hb (c • realPacket)
      (c • realPacket) = (c * c) • transport (rotatedGradientSymbol finiteKernel.coeff) hb
        realPacket realPacket := by
    rw [h1, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [hbil]
  have hcoeff : (transport (rotatedGradientSymbol finiteKernel.coeff) hb realPacket realPacket)
      (unitFreq 0 + unitFreq 1) = twoPiI * twoPiI := by
    rw [transport_realPacket_coeff finiteKernel_admissible, finiteKernel_coeff_unitFreq,
      finiteKernel_coeff_unitFreq_one]
    ring
  have hval : ((-((c * c) • transport (rotatedGradientSymbol finiteKernel.coeff) hb realPacket
        realPacket + (c * c) • transport (rotatedGradientSymbol finiteKernel.coeff) hb
          realPacket realPacket) : Wiener) : Gam → ℂ) (unitFreq 0 + unitFreq 1)
      = -((c * c) * (twoPiI * twoPiI) + (c * c) * (twoPiI * twoPiI)) := by
    simp only [lp.coeFn_neg, Pi.neg_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, hcoeff]
  rw [hval]
  ring

/-- The second-variation source of the packet forcing is not the zero curve, provided the
horizon is positive. -/
theorem secondVariationSource_packet_ne_zero (hα : 1 / 2 < α) (hT : 0 < T) :
    secondVariationSource hα hT.le (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric)
        (packetSource T) (packetSource T) ≠ 0 := by
  intro hz
  have hmid : T / 2 ∈ Set.Icc (0:ℝ) T := ⟨by linarith, by linarith⟩
  have hpos : 0 < expWindow (fracSymbol α (unitFreq 0)) (T / 2) :=
    expWindow_pos _ (by linarith)
  have hkey := sourceFun_secondVariationSource_packet_coeff hα hT.le hmid
  rw [hz] at hkey
  have hzero : (sourceFun hT.le (0 : Curve0 T) (T / 2)) (unitFreq 0 + unitFreq 1) = 0 := by
    show ((((0 : Curve0 T) (clampT hT.le (T/2))).val : Wiener) : Gam → ℂ)
        (unitFreq 0 + unitFreq 1) = 0
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, RealWiener.val_zero,
      lp.coeFn_zero, Pi.zero_apply]
  rw [hzero] at hkey
  have hne : ((expWindow (fracSymbol α (unitFreq 0)) (T / 2) : ℝ) : ℂ) ≠ 0 := by
    simpa using hpos.ne'
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have := hkey.symm
  rw [neg_eq_zero] at this
  rcases mul_eq_zero.1 this with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact h2 h'
    · exact hne (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h')
  · exact twoPiI_sq_ne_zero h

/-- **A genuinely nonzero mixed second source response.**  For the finite-support kernel, the
explicit real forcing profile `2·cos(2πx₀) + 2·cos(2πx₁)` (constant in time) has

    `D²S_K(0)[f,f] ≠ 0` . -/
theorem fderiv_fderiv_sourceSolution_packet_ne_zero (hα : 1 / 2 < α) (hT : 0 < T) :
    fderiv ℝ (fderiv ℝ (sourceSolution hα hT.le
        (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric)))
      (0 : Curve0 T) (packetSource T) (packetSource T) ≠ 0 := by
  rw [fderiv_fderiv_sourceSolution_eq_duhamelOp]
  exact duhamelOp_ne_zero hα hT (secondVariationSource_packet_ne_zero hα hT)

end LiWang.Formalization
