/-
# Non-degeneracy of the symmetrized quadratic response

`RotatedNonDegeneracy.lean` shows that the *ordered* interaction `N_κ(δ_{(1,0)}, δ_{(0,1)})`
is nonzero.  That is **not** the same as the Hessian of the quadratic residual, which is the
*symmetrized* form `h₁, h₂ ↦ N(h₁,h₂) + N(h₂,h₁)`: for some kernels the symmetrized
coefficient cancels.  This module

* computes the transport of two Dirac modes exactly,
* exhibits a kernel and two modes for which the **symmetrized** coefficient — hence the
  second derivative `D²Q_κ(0)` — is nonzero,
* records that the single cosine mode used in the concrete v2 solution has **zero**
  self-advection, so it is not a witness of nonlinearity.

Part of `LiWangWienerSourceResponsePacket` v3.0.
-/
import LiWangWiener.RotatedNonDegeneracy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-- **The transport of two Dirac modes**, exactly. -/
theorem transport_dirac1 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (a b k : Gam) :
    (transport m hm (dirac1 a) (dirac1 b)) k
      = if k = a + b then ∑ j : Fin 2, m j a * (twoPiI * ((b j : ℤ) : ℂ)) else 0 := by
  rw [transport_apply_coeff]
  by_cases hk : k = a + b
  · rw [if_pos hk]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hterm : ∀ p : Gam,
        (m j p * (dirac1 a).coeff p) * (twoPiI * (((k - p) j : ℤ) : ℂ) * (dirac1 b).coeff (k - p))
          = if p = a then m j a * (twoPiI * ((b j : ℤ) : ℂ)) else 0 := by
      intro p
      by_cases hp : p = a
      · rw [if_pos hp, hp]
        have h1 : (dirac1 a).coeff a = 1 := by
          show diracFun a a = 1
          simp [diracFun]
        have h2 : k - a = b := by rw [hk]; abel
        rw [h1, h2, mul_one]
        have h3 : (dirac1 b).coeff b = 1 := by
          show diracFun b b = 1
          simp [diracFun]
        rw [h3, mul_one]
      · rw [if_neg hp]
        have h0 : (dirac1 a).coeff p = 0 := by
          show diracFun a p = 0
          simp [diracFun, hp]
        rw [h0, mul_zero, zero_mul]
    rw [tsum_congr hterm]
    exact tsum_ite_eq a _
  · rw [if_neg hk]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hterm : ∀ p : Gam,
        (m j p * (dirac1 a).coeff p) * (twoPiI * (((k - p) j : ℤ) : ℂ) * (dirac1 b).coeff (k - p))
          = 0 := by
      intro p
      by_cases hp : p = a
      · have hne : k - p ≠ b := by
          rw [hp]
          intro hc
          exact hk (by rw [← hc]; abel)
        have h0 : (dirac1 b).coeff (k - p) = 0 := by
          show diracFun b (k - p) = 0
          simp [diracFun, hne]
        rw [h0, mul_zero, mul_zero]
      · have h0 : (dirac1 a).coeff p = 0 := by
          show diracFun a p = 0
          simp [diracFun, hp]
        rw [h0, mul_zero, zero_mul]
    rw [tsum_congr hterm]
    exact tsum_zero

/-! ## The symmetrized coefficient for the finite-support kernel -/

theorem rotatedGradientSymbol_unitFreq_zero {κ : Gam → ℂ} :
    rotatedGradientSymbol κ 0 (unitFreq 0) = 0 := by
  show -twoPiI * (((unitFreq 0) 1 : ℤ) : ℂ) * κ (unitFreq 0) = 0
  rw [unitFreq_zero_one]
  norm_num

theorem rotatedGradientSymbol_unitFreq_one {κ : Gam → ℂ} :
    rotatedGradientSymbol κ 1 (unitFreq 0) = twoPiI * κ (unitFreq 0) := by
  show twoPiI * (((unitFreq 0) 0 : ℤ) : ℂ) * κ (unitFreq 0) = twoPiI * κ (unitFreq 0)
  rw [unitFreq_self]
  norm_num

/-- The **symmetrized** Dirac coefficient of the rotated-gradient transport. -/
theorem transport_rotatedGradient_symmetrized {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) :
    (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
        (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))
      + transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
        (dirac1 (unitFreq 1)) (dirac1 (unitFreq 0))) (unitFreq 0 + unitFreq 1)
      = twoPiI * twoPiI * (κ (unitFreq 0) - κ (unitFreq 1)) := by
  have hadd : ((transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
        (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))
      + transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
        (dirac1 (unitFreq 1)) (dirac1 (unitFreq 0))) : Wiener) (unitFreq 0 + unitFreq 1)
      = (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
          (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))) (unitFreq 0 + unitFreq 1)
        + (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
          (dirac1 (unitFreq 1)) (dirac1 (unitFreq 0))) (unitFreq 0 + unitFreq 1) := by
    simp only [lp.coeFn_add, Pi.add_apply]
  rw [hadd, transport_dirac1, transport_dirac1, if_pos rfl,
    if_pos (by abel : unitFreq 0 + unitFreq 1 = unitFreq 1 + unitFreq 0)]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h00 : rotatedGradientSymbol κ 0 (unitFreq 0) = 0 := rotatedGradientSymbol_unitFreq_zero
  have h10 : rotatedGradientSymbol κ 1 (unitFreq 0) = twoPiI * κ (unitFreq 0) :=
    rotatedGradientSymbol_unitFreq_one
  have h01 : rotatedGradientSymbol κ 0 (unitFreq 1) = -twoPiI * κ (unitFreq 1) := by
    show -twoPiI * (((unitFreq 1) 1 : ℤ) : ℂ) * κ (unitFreq 1) = -twoPiI * κ (unitFreq 1)
    rw [unitFreq_self]; norm_num
  have h11 : rotatedGradientSymbol κ 1 (unitFreq 1) = 0 := by
    show twoPiI * (((unitFreq 1) 0 : ℤ) : ℂ) * κ (unitFreq 1) = 0
    rw [unitFreq_one_zero]; norm_num
  have e0 : (((unitFreq 1) 0 : ℤ) : ℂ) = 0 := by rw [unitFreq_one_zero]; norm_num
  have e1 : (((unitFreq 1) 1 : ℤ) : ℂ) = 1 := by rw [unitFreq_self]; norm_num
  have f0 : (((unitFreq 0) 0 : ℤ) : ℂ) = 1 := by rw [unitFreq_self]; norm_num
  have f1 : (((unitFreq 0) 1 : ℤ) : ℂ) = 0 := by rw [unitFreq_zero_one]; norm_num
  rw [h00, h10, h01, h11, e0, e1, f0, f1]
  ring

/-! ## A kernel whose symmetrized coefficient does **not** cancel -/

theorem finiteKernel_coeff_unitFreq_one : finiteKernel.coeff (unitFreq 1) = 0 := by
  show cosModeFun (unitFreq 0) (unitFreq 1) = 0
  have h1 : (unitFreq 1 : Gam) ≠ unitFreq 0 := by
    intro hc
    have := congrArg (fun f : Gam => f 1) hc
    simp only [unitFreq_self, unitFreq_zero_one] at this
    norm_num at this
  have h2 : (unitFreq 1 : Gam) ≠ -unitFreq 0 := by
    intro hc
    have h4 : (unitFreq 1 : Gam) 1 = ((-unitFreq 0 : Gam)) 1 := congrArg (fun f : Gam => f 1) hc
    have h3 : ((-unitFreq 0 : Gam)) 1 = -((unitFreq 0) 1) := rfl
    rw [unitFreq_self, h3, unitFreq_zero_one] at h4
    norm_num at h4
  show diracFun (unitFreq 0) (unitFreq 1) + diracFun (-unitFreq 0) (unitFreq 1) = 0
  simp [diracFun, h1, h2]

/-- **The Hessian of the quadratic residual is nonzero** for the finite-support kernel: the
*symmetrized* Dirac coefficient equals `(2πi)² = -4π²`. -/
theorem transport_finiteKernel_symmetrized :
    (transport (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))
      + transport (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (dirac1 (unitFreq 1)) (dirac1 (unitFreq 0))) (unitFreq 0 + unitFreq 1)
      = twoPiI * twoPiI := by
  rw [transport_rotatedGradient_symmetrized finiteKernel_admissible,
    finiteKernel_coeff_unitFreq, finiteKernel_coeff_unitFreq_one]
  ring

theorem twoPiI_sq_ne_zero : twoPiI * twoPiI ≠ 0 := by
  refine mul_ne_zero ?_ ?_ <;>
    · intro hz
      have h : ‖twoPiI‖ = 0 := by rw [hz]; simp
      rw [norm_twoPiI] at h
      have := Real.pi_pos
      linarith

/-- **The second derivative of the quadratic residual is nonzero** for the finite-support
kernel — not merely the ordered interaction. -/
theorem fderiv_fderiv_quadResidual_finiteKernel_ne_zero :
    fderiv ℂ (fderiv ℂ (quadResidual (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible)))
      0 (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1)) ≠ 0 := by
  intro hzero
  have hsum := fderiv_fderiv_quadResidual_apply (rotatedGradientSymbol finiteKernel.coeff)
    (rotatedGradientSymbol_bdd finiteKernel_admissible) (dirac1 (unitFreq 0))
    (dirac1 (unitFreq 1))
  rw [hzero] at hsum
  have hcoeff := congrArg (fun w : Wiener => (w : Gam → ℂ) (unitFreq 0 + unitFreq 1)) hsum.symm
  simp only at hcoeff
  have hz : ((0 : Wiener) : Gam → ℂ) (unitFreq 0 + unitFreq 1) = 0 := by
    simp only [lp.coeFn_zero, Pi.zero_apply]
  rw [transport_finiteKernel_symmetrized, hz] at hcoeff
  exact twoPiI_sq_ne_zero hcoeff

/-! ## The cancelling kernel: a proved regression -/

theorem exampleKernel_unitFreq_zero : exampleKernel (unitFreq 0) = ((1/2 : ℝ) : ℂ) := by
  show (((wt (unitFreq 0))⁻¹ : ℝ) : ℂ) = ((1/2 : ℝ) : ℂ)
  rw [wt_unitFreq]
  norm_num

theorem exampleKernel_unitFreq_one : exampleKernel (unitFreq 1) = ((1/2 : ℝ) : ℂ) := by
  show (((wt (unitFreq 1))⁻¹ : ℝ) : ℂ) = ((1/2 : ℝ) : ℂ)
  rw [wt_unitFreq]
  norm_num

/-- **The symmetrized coefficient really can cancel.**  For `exampleKernel` the ordered
interaction is nonzero but the symmetrized one — the Hessian coefficient — vanishes at the
frequency `(1,1)`.  So "N ≠ 0" does *not* imply "D²Q ≠ 0". -/
theorem transport_exampleKernel_symmetrized_eq_zero :
    (transport (rotatedGradientSymbol exampleKernel)
        (rotatedGradientSymbol_bdd exampleKernel_admissible)
        (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))
      + transport (rotatedGradientSymbol exampleKernel)
        (rotatedGradientSymbol_bdd exampleKernel_admissible)
        (dirac1 (unitFreq 1)) (dirac1 (unitFreq 0))) (unitFreq 0 + unitFreq 1) = 0 := by
  rw [transport_rotatedGradient_symmetrized exampleKernel_admissible,
    exampleKernel_unitFreq_zero, exampleKernel_unitFreq_one]
  ring

/-- …while the *ordered* coefficient for the same kernel is nonzero. -/
theorem transport_exampleKernel_ordered_ne_zero :
    (transport (rotatedGradientSymbol exampleKernel)
        (rotatedGradientSymbol_bdd exampleKernel_admissible)
        (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))) (unitFreq 0 + unitFreq 1) ≠ 0 := by
  rw [transport_rotatedGradient_dirac exampleKernel_admissible, exampleKernel_unitFreq_zero]
  intro hz
  have h2 : twoPiI * twoPiI ≠ 0 := twoPiI_sq_ne_zero
  have : (((1:ℝ)/2 : ℝ) : ℂ) ≠ 0 := by
    simp
  exact (mul_ne_zero h2 this) hz

/-! ## A real packet with genuinely nonzero self-advection -/

/-- A real (conjugate-symmetric) two-mode packet.  Its physical synthesis is
`2·cos(2π x₀) + 2·cos(2π x₁)`: each `cosMode1 eⱼ` places coefficient one on **both** `±eⱼ`, so
the cosine amplitudes are two, not one. -/
noncomputable def realPacket : Wiener1 := cosMode1 (unitFreq 0) + cosMode1 (unitFreq 1)

theorem realPacket_conjSymmetric : ConjSymmetric realPacket.coeff :=
  ConjSymmetric.wiener1_add (cosMode1_conjSymmetric _) (cosMode1_conjSymmetric _)

/-- **The self-advection coefficient of the real packet** at the frequency `(1,1)`. -/
theorem transport_realPacket_coeff {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) :
    (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) realPacket realPacket)
        (unitFreq 0 + unitFreq 1)
      = twoPiI * twoPiI * (κ (unitFreq 0) - κ (unitFreq 1)) := by
  rw [realPacket, cosMode1, cosMode1]
  simp only [map_add, ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    transport_dirac1]
  norm_num +decide [Fin.sum_univ_two, rotatedGradientSymbol]
  rw [unitFreq_self, unitFreq_self, unitFreq_zero_one, unitFreq_one_zero]
  push_cast
  ring

/-- **The quadratic residual of the real packet is nonzero** for the finite-support kernel:
its `(1,1)` coefficient is `(2πi)² = -4π²`. -/
theorem quadResidual_realPacket_coeff :
    (quadResidual (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible) realPacket)
      (unitFreq 0 + unitFreq 1) = twoPiI * twoPiI := by
  rw [quadResidual_apply, transport_realPacket_coeff finiteKernel_admissible,
    finiteKernel_coeff_unitFreq, finiteKernel_coeff_unitFreq_one]
  ring

theorem quadResidual_realPacket_ne_zero :
    quadResidual (rotatedGradientSymbol finiteKernel.coeff)
      (rotatedGradientSymbol_bdd finiteKernel_admissible) realPacket ≠ 0 := by
  intro hz
  have hc := congrArg (fun w : Wiener => (w : Gam → ℂ) (unitFreq 0 + unitFreq 1)) hz
  simp only at hc
  rw [quadResidual_realPacket_coeff] at hc
  have hz0 : ((0 : Wiener) : Gam → ℂ) (unitFreq 0 + unitFreq 1) = 0 := by
    simp only [lp.coeFn_zero, Pi.zero_apply]
  rw [hz0] at hc
  exact twoPiI_sq_ne_zero hc

/-! ## The single cosine has zero self-advection -/

/-- If a frequency is neither `a` nor `-a`, the cosine packet vanishes there. -/
theorem cosModeFun_eq_zero_of_ne {a x : Gam} (h1 : x ≠ a) (h2 : x ≠ -a) :
    cosModeFun a x = 0 := by
  show diracFun a x + diracFun (-a) x = 0
  simp [diracFun, h1, h2]

/-- **A single cosine mode does not advect itself**: for *every* admissible kernel the
quadratic residual of a cosine in one coordinate direction vanishes identically.  In
particular the concrete solution of v2 (`exists_concrete_local_physical_solution`), whose
datum is such a cosine, is not a witness of nonlinear behaviour. -/
theorem transport_cosMode1_self {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) (a : Gam)
    (ha : a 1 = 0) :
    transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
      (cosMode1 a) (cosMode1 a) = 0 := by
  have hna : ((-a : Gam)) 1 = 0 := by
    show -(a 1) = 0
    rw [ha]; ring
  ext k
  rw [transport_apply_coeff]
  have hzero : ((0 : Wiener) : Gam → ℂ) k = 0 := by
    simp only [lp.coeFn_zero, Pi.zero_apply]
  rw [hzero]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have hterm : ∀ p : Gam,
      (rotatedGradientSymbol κ j p * (cosMode1 a).coeff p)
        * (twoPiI * (((k - p) j : ℤ) : ℂ) * (cosMode1 a).coeff (k - p)) = 0 := by
    intro p
    fin_cases j
    · -- the first velocity component vanishes on the support of the packet
      show (rotatedGradientSymbol κ 0 p * (cosMode1 a).coeff p)
        * (twoPiI * (((k - p) 0 : ℤ) : ℂ) * (cosMode1 a).coeff (k - p)) = 0
      by_cases h1 : p = a
      · have hs : rotatedGradientSymbol κ 0 p = 0 := by
          show -twoPiI * (((p 1 : ℤ)) : ℂ) * κ p = 0
          rw [h1, ha]
          norm_num
        rw [hs, zero_mul, zero_mul]
      · by_cases h2 : p = -a
        · have hs : rotatedGradientSymbol κ 0 p = 0 := by
            show -twoPiI * (((p 1 : ℤ)) : ℂ) * κ p = 0
            rw [h2, hna]
            norm_num
          rw [hs, zero_mul, zero_mul]
        · have hc : (cosMode1 a).coeff p = 0 := by
            show cosModeFun a p = 0
            exact cosModeFun_eq_zero_of_ne h1 h2
          rw [hc, mul_zero, zero_mul]
    · -- the second gradient component vanishes on the support of the packet
      show (rotatedGradientSymbol κ 1 p * (cosMode1 a).coeff p)
        * (twoPiI * (((k - p) 1 : ℤ) : ℂ) * (cosMode1 a).coeff (k - p)) = 0
      by_cases h1 : k - p = a
      · have hs : (((k - p) 1 : ℤ) : ℂ) = 0 := by rw [h1, ha]; norm_num
        rw [hs]
        ring
      · by_cases h2 : k - p = -a
        · have hs : (((k - p) 1 : ℤ) : ℂ) = 0 := by rw [h2, hna]; norm_num
          rw [hs]
          ring
        · have hc : (cosMode1 a).coeff (k - p) = 0 := by
            show cosModeFun a (k - p) = 0
            exact cosModeFun_eq_zero_of_ne h1 h2
          rw [hc, mul_zero, mul_zero]
  rw [tsum_congr hterm, tsum_zero]

/-- The concrete v2 datum `finiteKernel = cosMode1 e₀`, whose synthesis is
`e_{e₀} + e_{-e₀} = 2·cos(2π x₀)` (amplitude **two**, not one, because both `±e₀` carry
coefficient one), has zero self-advection. -/
theorem quadResidual_finiteKernel_self_zero :
    quadResidual (rotatedGradientSymbol finiteKernel.coeff)
      (rotatedGradientSymbol_bdd finiteKernel_admissible) finiteKernel = 0 := by
  rw [quadResidual_apply]
  show transport (rotatedGradientSymbol finiteKernel.coeff)
      (rotatedGradientSymbol_bdd finiteKernel_admissible)
      (cosMode1 (unitFreq 0)) (cosMode1 (unitFreq 0)) = 0
  exact transport_cosMode1_self finiteKernel_admissible (unitFreq 0) unitFreq_zero_one

/-! ## A nonzero **real** second derivative -/

/-- The two-mode real packet as an element of the real first-order carrier. -/
noncomputable def realPacketR : RealWiener1 :=
  RealWiener1.mk realPacket realPacket_conjSymmetric

/-- **The real second derivative of the real quadratic residual is nonzero** at the two-mode
real packet: this is the symmetrized (Hessian) statement on the *real* carriers, not merely
the non-vanishing of an ordered interaction. -/
theorem fderiv_fderiv_realQuadResidual_realPacket_ne_zero :
    fderiv ℝ (fderiv ℝ (realQuadResidual (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible)
        (rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric))) 0
      realPacketR realPacketR ≠ 0 := by
  intro hz
  rw [fderiv_fderiv_realQuadResidual_apply] at hz
  have hval := congrArg
    (fun w : RealWiener => ((w.val : Wiener) : Gam → ℂ) (unitFreq 0 + unitFreq 1)) hz
  simp only [RealWiener.val_add, RealWiener.val_zero, lp.coeFn_add, Pi.add_apply,
    lp.coeFn_zero, Pi.zero_apply] at hval
  have hcoeff : ((realTransport (rotatedGradientSymbol finiteKernel.coeff)
      (rotatedGradientSymbol_bdd finiteKernel_admissible)
      (rotatedGradientSymbol_isRealSymbol finiteKernel_conjSymmetric)
      realPacketR realPacketR).val : Gam → ℂ) (unitFreq 0 + unitFreq 1) = twoPiI * twoPiI := by
    show (transport (rotatedGradientSymbol finiteKernel.coeff)
        (rotatedGradientSymbol_bdd finiteKernel_admissible) realPacket realPacket : Gam → ℂ)
      (unitFreq 0 + unitFreq 1) = twoPiI * twoPiI
    rw [transport_realPacket_coeff finiteKernel_admissible, finiteKernel_coeff_unitFreq,
      finiteKernel_coeff_unitFreq_one]
    ring
  rw [hcoeff] at hval
  have h2 : twoPiI * twoPiI = 0 := by
    have := hval
    linear_combination this / 2
  exact twoPiI_sq_ne_zero h2

end LiWang.WienerModel
