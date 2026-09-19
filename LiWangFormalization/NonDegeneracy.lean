/-
Dirac coefficient families, non-degeneracy certificates, and the `i`-free complex test
symbol of v1.0 (retained only as a test symbol).

Part of `LiWangFormalizationPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import LiWangFormalization.Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.Formalization

/-! ## 9. Dirac coefficient families and non-degeneracy

The lemmas of this section exist to certify that nothing above is vacuous: the first-order
norm is strictly stronger than the Wiener norm, the Fourier derivatives are nonzero
operators, and the transport form is not identically zero. -/

/-- The Dirac coefficient family concentrated at the frequency `k₀`. -/
def diracFun (k₀ : Gam) : Gam → ℂ := fun k => if k = k₀ then 1 else 0

theorem norm_diracFun (k₀ k : Gam) : ‖diracFun k₀ k‖ = if k = k₀ then (1 : ℝ) else 0 := by
  by_cases h : k = k₀ <;> simp [diracFun, h]

theorem hasSum_norm_diracFun (k₀ : Gam) : HasSum (fun k => ‖diracFun k₀ k‖) 1 := by
  simpa only [norm_diracFun] using hasSum_ite_eq k₀ (1 : ℝ)

theorem hasSum_wt_norm_diracFun (k₀ : Gam) :
    HasSum (fun k => wt k * ‖diracFun k₀ k‖) (wt k₀) := by
  have h : ∀ k : Gam, wt k * ‖diracFun k₀ k‖ = if k = k₀ then wt k₀ else 0 := by
    intro k; by_cases hk : k = k₀ <;> simp [norm_diracFun, hk]
  simpa only [h] using hasSum_ite_eq k₀ (wt k₀)

/-- The Dirac element of the Wiener algebra. -/
noncomputable def wdirac (k₀ : Gam) : Wiener :=
  wmk (diracFun k₀) (hasSum_norm_diracFun k₀).summable

/-- The Dirac element of the first-order Wiener space. -/
noncomputable def dirac1 (k₀ : Gam) : Wiener1 :=
  Wiener1.mk (diracFun k₀) (hasSum_wt_norm_diracFun k₀).summable

@[simp] theorem wdirac_apply (k₀ k : Gam) : (wdirac k₀) k = diracFun k₀ k := rfl
@[simp] theorem dirac1_coeff (k₀ : Gam) : (dirac1 k₀).coeff = diracFun k₀ := rfl

theorem norm_wdirac (k₀ : Gam) : ‖wdirac k₀‖ = 1 := by
  rw [wiener_norm_eq]; exact (hasSum_norm_diracFun k₀).tsum_eq

theorem norm_dirac1 (k₀ : Gam) : ‖dirac1 k₀‖ = wt k₀ := by
  rw [Wiener1.norm_eq]; exact (hasSum_wt_norm_diracFun k₀).tsum_eq

theorem incl_dirac1 (k₀ : Gam) : incl (dirac1 k₀) = wdirac k₀ := by ext k; rfl

theorem one_lt_wt {k : Gam} (hk : k ≠ 0) : 1 < wt k := by
  have h0 := abs_nonneg ((k 0 : ℝ))
  have h1 := abs_nonneg ((k 1 : ℝ))
  rcases (one_le_wt k).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hk
    have hsum : |(k 0 : ℝ)| + |(k 1 : ℝ)| = 0 := by simp only [wt] at h; linarith
    have e0 : ((k 0 : ℝ)) = 0 := abs_eq_zero.mp (by linarith)
    have e1 : ((k 1 : ℝ)) = 0 := abs_eq_zero.mp (by linarith)
    funext i
    fin_cases i
    · show k 0 = 0; exact_mod_cast e0
    · show k 1 = 0; exact_mod_cast e1

/-- The `j`-th standard basis frequency of `Γ = ℤ²`. -/
def unitFreq (j : Fin 2) : Gam := fun i => if i = j then 1 else 0

theorem unitFreq_self (j : Fin 2) : unitFreq j j = 1 := by simp [unitFreq]

theorem unitFreq_ne_zero (j : Fin 2) : unitFreq j ≠ 0 := by
  intro h
  have := congrFun h j
  simp [unitFreq] at this

theorem wt_unitFreq (j : Fin 2) : wt (unitFreq j) = 2 := by
  fin_cases j <;> · simp [wt, unitFreq]; norm_num

/-- **The inclusion `A¹ ↪ A` is not isometric**: the first-order norm is strictly stronger
than the Wiener norm, so the boundedness of `∂ⱼ : A¹ → A` is not a triviality. -/
theorem norm_incl_lt {k₀ : Gam} (hk : k₀ ≠ 0) : ‖incl (dirac1 k₀)‖ < ‖dirac1 k₀‖ := by
  rw [incl_dirac1, norm_wdirac, norm_dirac1]
  exact one_lt_wt hk

theorem exists_norm_incl_lt : ∃ u : Wiener1, ‖incl u‖ < ‖u‖ :=
  ⟨dirac1 (unitFreq 0), norm_incl_lt (unitFreq_ne_zero 0)⟩

theorem norm_fourierDeriv_dirac1 (j : Fin 2) (k₀ : Gam) :
    ‖fourierDeriv j (dirac1 k₀)‖ = 2 * Real.pi * |(k₀ j : ℝ)| := by
  rw [wiener_norm_eq]
  have h : ∀ k : Gam, ‖(fourierDeriv j (dirac1 k₀)) k‖
      = if k = k₀ then 2 * Real.pi * |(k₀ j : ℝ)| else 0 := by
    intro k
    rw [fourierDeriv_apply, dirac1_coeff]
    by_cases hk : k = k₀
    · subst hk
      simp [diracFun, norm_twoPiI, Complex.norm_intCast]
    · simp [diracFun, hk]
  rw [tsum_congr h]
  exact tsum_ite_eq k₀ (fun _ => 2 * Real.pi * |(k₀ j : ℝ)|)

/-- **The Fourier derivative is a nonzero operator.**  Its norm is at least `π`, so the
upper bound `‖∂ⱼ‖ ≤ 2π` proved above is sharp up to a factor of two. -/
theorem pi_le_norm_fourierDeriv (j : Fin 2) : Real.pi ≤ ‖fourierDeriv j‖ := by
  have hu : ‖dirac1 (unitFreq j)‖ = 2 := by rw [norm_dirac1]; exact wt_unitFreq j
  have h1 : ‖fourierDeriv j (dirac1 (unitFreq j))‖ = 2 * Real.pi := by
    rw [norm_fourierDeriv_dirac1, unitFreq_self]
    norm_num
  have h2 := (fourierDeriv j).le_opNorm (dirac1 (unitFreq j))
  rw [h1, hu] at h2
  linarith

/-- The constant velocity symbol `m ≡ 1`. -/
def oneSymbol : Fin 2 → Gam → ℂ := fun _ _ => 1

theorem oneSymbol_bdd : IsBddSymbol oneSymbol := ⟨1, fun j k => by simp [oneSymbol]⟩

theorem velocity_oneSymbol (j : Fin 2) (a : Wiener) :
    velocity oneSymbol oneSymbol_bdd j a = a := by
  ext k
  show (1 : ℂ) * a k = a k
  ring

theorem conv_wdirac_left (k₀ : Gam) (b : Wiener) (k : Gam) :
    conv (wdirac k₀) b k = b (k - k₀) := by
  show ∑' p, (wdirac k₀) p * b (k - p) = b (k - k₀)
  have h : ∀ p : Gam, (wdirac k₀) p * b (k - p) = if p = k₀ then b (k - k₀) else 0 := by
    intro p; by_cases hp : p = k₀ <;> simp [wdirac, diracFun, hp]
  rw [tsum_congr h]
  exact tsum_ite_eq k₀ (fun _ => b (k - k₀))

theorem transport_oneSymbol_dirac :
    (transport oneSymbol oneSymbol_bdd (dirac1 0) (dirac1 (unitFreq 1))) (unitFreq 1)
      = twoPiI := by
  rw [transport_apply, lp.coeFn_sum]
  simp only [Finset.sum_apply, velocity_oneSymbol, incl_dirac1, conv_wdirac_left, sub_zero,
    fourierDeriv_apply, dirac1_coeff, diracFun]
  rw [Fin.sum_univ_two]
  simp [unitFreq]

/-- **The transport form is not identically zero**, hence neither is `D²Q_m(0)`. -/
theorem transport_ne_zero : transport oneSymbol oneSymbol_bdd ≠ 0 := by
  intro h
  have h0 : (transport oneSymbol oneSymbol_bdd (dirac1 0) (dirac1 (unitFreq 1))) (unitFreq 1)
      = 0 := by rw [h]; rfl
  rw [transport_oneSymbol_dirac] at h0
  have hz : ‖twoPiI‖ = 0 := by rw [h0]; simp
  rw [norm_twoPiI] at hz
  have := Real.pi_pos
  linarith

/-! ## 10. A complex test symbol (NOT a real velocity symbol)

`m(k) = (-k₁, k₀) / (|k₀| + |k₁|)`, `m(0) = 0`.

**Warning.**  This symbol is *not* a source-faithful velocity symbol for the Li–Wang
active scalar equations, and it is not described as one.  It is missing the factor `2πi`
that a genuine rotated-gradient (Biot–Savart) symbol carries, and as a consequence it
**fails** the reality (conjugate-symmetry) condition `m j (-k) = conj (m j k)`: see
`LiWang.Formalization.testSymbolNoI_reality_failure` in Section 12.  It is retained here only as a
concrete *complex* test symbol exercising the general machinery of Sections 4–8.

The source-faithful, `i`-corrected rotated-gradient symbol is
`LiWang.Formalization.rotatedGradientSymbol` in Section 12; the showcased concrete example of the
packet is `LiWang.Formalization.exampleKernel` in Section 14. -/

noncomputable def den (k : Gam) : ℝ := |(k 0 : ℝ)| + |(k 1 : ℝ)|

theorem den_nonneg (k : Gam) : 0 ≤ den k := by
  simp only [den]; positivity

theorem den_pos {k : Gam} (hk : k ≠ 0) : 0 < den k := by
  rcases (den_nonneg k).lt_or_eq with h | h
  · exact h
  · exfalso
    have ha0 := abs_nonneg ((k 0 : ℝ))
    have ha1 := abs_nonneg ((k 1 : ℝ))
    have hd : |(k 0 : ℝ)| + |(k 1 : ℝ)| = 0 := by simp only [den] at h; linarith
    have e0 : ((k 0 : ℝ)) = 0 := abs_eq_zero.mp (by linarith)
    have e1 : ((k 1 : ℝ)) = 0 := abs_eq_zero.mp (by linarith)
    apply hk
    funext i
    fin_cases i
    · show k 0 = 0; exact_mod_cast e0
    · show k 1 = 0; exact_mod_cast e1

/-- The `ℓ¹`-normalised **no-`i` test symbol** on `Γ = ℤ²`.  Not a real velocity symbol;
see the warning above and `LiWang.Formalization.testSymbolNoI_reality_failure`. -/
noncomputable def testSymbolNoI : Fin 2 → Gam → ℂ := fun j k =>
  if k = 0 then 0
  else (if j = 0 then (-(k 1 : ℂ)) else (k 0 : ℂ)) / (den k : ℂ)

/-- An explicit uniform bound for the no-`i` test symbol. -/
theorem testSymbolNoI_norm_le_one (j : Fin 2) (k : Gam) : ‖testSymbolNoI j k‖ ≤ 1 := by
  by_cases hk : k = 0
  · simp [testSymbolNoI, hk]
  · have hd : 0 < den k := den_pos hk
    have ha0 := abs_nonneg ((k 0 : ℝ))
    have ha1 := abs_nonneg ((k 1 : ℝ))
    have hnum : ‖(if j = 0 then (-(k 1 : ℂ)) else (k 0 : ℂ))‖ ≤ den k := by
      split
      · rw [norm_neg, Complex.norm_intCast]; simp only [den]; linarith
      · rw [Complex.norm_intCast]; simp only [den]; linarith
    have hval : testSymbolNoI j k
        = (if j = 0 then (-(k 1 : ℂ)) else (k 0 : ℂ)) / (den k : ℂ) := by
      simp only [testSymbolNoI, if_neg hk]
    rw [hval, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, div_le_one hd]
    exact hnum

theorem testSymbolNoI_bdd : IsBddSymbol testSymbolNoI := ⟨1, testSymbolNoI_norm_le_one⟩

/-- The no-`i` test symbol is nonzero, so the instantiation is not degenerate. -/
theorem testSymbolNoI_unitFreq_one : testSymbolNoI 1 (unitFreq 0) = 1 := by
  have hk : unitFreq 0 ≠ (0 : Gam) := unitFreq_ne_zero 0
  have hd : den (unitFreq 0) = 1 := by simp [den, unitFreq]
  simp [testSymbolNoI, if_neg hk, hd, unitFreq]

/-- `‖N_m‖ ≤ 4π` for the no-`i` test symbol. -/
theorem norm_transport_testSymbolNoI_le : ‖transport testSymbolNoI testSymbolNoI_bdd‖ ≤ 4 * Real.pi := by
  have h := norm_transport_le testSymbolNoI_bdd (C := 1) testSymbolNoI_norm_le_one
  simpa using h

end LiWang.Formalization
