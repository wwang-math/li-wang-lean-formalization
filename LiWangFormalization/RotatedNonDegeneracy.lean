/-
# Non-degeneracy of the source-faithful nonlinearity

`NonDegeneracy.lean` shows that the transport form of the *test* symbol `oneSymbol` is not
identically zero.  Here the same is done for the **rotated-gradient** symbol
`∇^⊥(κ ∗ ·)` that the Li–Wang velocity operator actually uses: an explicit pair of Dirac
modes has a computable, nonzero transport coefficient.

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0.
-/
import LiWangFormalization.SolutionCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.Formalization

theorem unitFreq_zero_one : (unitFreq 0) 1 = 0 := by simp [unitFreq]
theorem unitFreq_one_zero : (unitFreq 1) 0 = 0 := by simp [unitFreq]

/-- The explicit transport coefficient of two Dirac modes for the rotated-gradient symbol. -/
theorem transport_rotatedGradient_dirac {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ) :
    (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
        (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))) (unitFreq 0 + unitFreq 1)
      = twoPiI * twoPiI * κ (unitFreq 0) := by
  set k : Gam := unitFreq 0 + unitFreq 1 with hk
  rw [transport_apply_coeff]
  have hsub : k - unitFreq 0 = unitFreq 1 := by rw [hk]; abel
  have hterm : ∀ (j : Fin 2) (p : Gam),
      (rotatedGradientSymbol κ j p * (dirac1 (unitFreq 0)).coeff p)
        * (twoPiI * (((k - p) j : ℤ) : ℂ) * (dirac1 (unitFreq 1)).coeff (k - p))
      = if p = unitFreq 0 then
          (rotatedGradientSymbol κ j (unitFreq 0))
            * (twoPiI * (((unitFreq 1) j : ℤ) : ℂ) * 1)
        else 0 := by
    intro j p
    by_cases hp : p = unitFreq 0
    · rw [if_pos hp, hp, hsub]
      have h1 : (dirac1 (unitFreq 0)).coeff (unitFreq 0) = 1 := by
        show diracFun (unitFreq 0) (unitFreq 0) = 1
        simp [diracFun]
      have h3 : (dirac1 (unitFreq 1)).coeff (unitFreq 1) = 1 := by
        show diracFun (unitFreq 1) (unitFreq 1) = 1
        simp [diracFun]
      rw [h1, h3, mul_one]
    · rw [if_neg hp]
      have h0 : (dirac1 (unitFreq 0)).coeff p = 0 := by
        show diracFun (unitFreq 0) p = 0
        simp [diracFun, hp]
      rw [h0, mul_zero, zero_mul]
  have hsum : ∀ j : Fin 2,
      (∑' p : Gam, (rotatedGradientSymbol κ j p * (dirac1 (unitFreq 0)).coeff p)
        * (twoPiI * (((k - p) j : ℤ) : ℂ) * (dirac1 (unitFreq 1)).coeff (k - p)))
      = (rotatedGradientSymbol κ j (unitFreq 0))
          * (twoPiI * (((unitFreq 1) j : ℤ) : ℂ) * 1) := by
    intro j
    rw [tsum_congr (hterm j)]
    exact tsum_ite_eq (unitFreq 0) _
  rw [Fin.sum_univ_two, hsum 0, hsum 1]
  have h0 : (((unitFreq 1) 0 : ℤ) : ℂ) = 0 := by rw [unitFreq_one_zero]; norm_num
  have h1 : (((unitFreq 1) 1 : ℤ) : ℂ) = 1 := by rw [unitFreq_self]; norm_num
  have hm1 : rotatedGradientSymbol κ 1 (unitFreq 0) = twoPiI * κ (unitFreq 0) := by
    show twoPiI * (((unitFreq 0) 0 : ℤ) : ℂ) * κ (unitFreq 0) = twoPiI * κ (unitFreq 0)
    rw [unitFreq_self]
    norm_num
  rw [h0, h1, hm1]
  ring

/-- **The rotated-gradient transport form is not identically zero** for a kernel that does
not vanish at the frequency `(1,0)`.

**Scope.**  This is a statement about the *ordered* interaction `N_κ(u,v)`.  It does **not**
by itself say that the Hessian `D²Q_κ(0)[v,w] = N_κ(v,w) + N_κ(w,v)` is nonzero: the
symmetrized coefficient can cancel, and for `exampleKernel` it does — see
`transport_exampleKernel_symmetrized_eq_zero` in `HessianNonDegeneracy.lean`, where a kernel
with a genuinely nonzero Hessian is also exhibited. -/
theorem transport_rotatedGradient_ne_zero {κ : Gam → ℂ} (hb : IsAdmissibleKernel κ)
    (hκ : κ (unitFreq 0) ≠ 0) :
    transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb) ≠ 0 := by
  intro h
  have h0 : (transport (rotatedGradientSymbol κ) (rotatedGradientSymbol_bdd hb)
      (dirac1 (unitFreq 0)) (dirac1 (unitFreq 1))) (unitFreq 0 + unitFreq 1) = 0 := by
    rw [h]; rfl
  rw [transport_rotatedGradient_dirac hb] at h0
  have hne : twoPiI * twoPiI * κ (unitFreq 0) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hκ <;>
      · intro hz
        have : ‖twoPiI‖ = 0 := by rw [hz]; simp
        rw [norm_twoPiI] at this
        have := Real.pi_pos
        linarith
  exact hne h0

/-- The concrete finite-support kernel does not vanish at `(1,0)`. -/
theorem finiteKernel_coeff_unitFreq : finiteKernel.coeff (unitFreq 0) = 1 := by
  show cosModeFun (unitFreq 0) (unitFreq 0) = 1
  have h1 : diracFun (unitFreq 0) (unitFreq 0) = 1 := by simp [diracFun]
  have h2 : diracFun (-unitFreq 0) (unitFreq 0) = 0 := by
    have hne : (unitFreq 0 : Gam) ≠ -unitFreq 0 := by
      intro hcon
      have := congrArg (fun f : Gam => f 0) hcon
      simp only [unitFreq_self] at this
      have h3 : ((-unitFreq 0 : Gam)) 0 = -((unitFreq 0) 0) := rfl
      rw [h3, unitFreq_self] at this
      norm_num at this
    simp [diracFun, hne]
  show diracFun (unitFreq 0) (unitFreq 0) + diracFun (-unitFreq 0) (unitFreq 0) = 1
  rw [h1, h2, add_zero]

/-- **The nonlinearity of the concrete instance is not identically zero.** -/
theorem transport_finiteKernel_ne_zero :
    transport (rotatedGradientSymbol finiteKernel.coeff)
      (rotatedGradientSymbol_bdd finiteKernel_admissible) ≠ 0 :=
  transport_rotatedGradient_ne_zero finiteKernel_admissible
    (by rw [finiteKernel_coeff_unitFreq]; exact one_ne_zero)

end LiWang.Formalization
