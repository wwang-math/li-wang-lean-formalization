/-
# The tested symmetrized interaction (Section 6 output)

The pairing `⟪A, B⟫ = ∑_k A_k B_{-k}` is the **actual integral** `∫_{𝕋²} (synth A)(x)(synth B)(x) dx`
for the normalized Haar measure.  With respect to it, and for a **divergence-free** velocity
symbol, the transport form is *skew-adjoint in its second argument*:

    ⟪N_m(a, b), ψ⟫ = − ⟪b, N_m(a, ψ)⟫ .

This is spatial integration by parts against the exterior test function `ψ`: the derivative is
moved off the state and onto `ψ`, and the interior term produced by the product rule is exactly
the one annihilated by `div R_m(a) = 0`.  Nothing is discarded.

Applied to the generated-source identity this yields the **tested symmetrized interaction of
the full linearized states**, with its exact sign, as an actual space-time integral.

**The nonlocality caveat is stated, not silently bypassed**: `R_m` is a nonlocal operator, so
the tested identity below is about `R_m` applied to the *full* state; replacing it by `R_m`
applied to a zero extension of an exterior restriction is a separate approximation step, and
the exact additional control it needs is recorded in `NonlocalTailControl`.

Part of `LiWangWienerObservationBridgePacket` v4.0.
-/
import LiWangWiener.UCPBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.WienerModel

/-! ## The bilinear pairing and its physical meaning -/

theorem summable_wpair (A B : Wiener) : Summable fun k : Gam => ‖A k * B (-k)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((wiener_summable A).mul_right ‖B‖)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (wiener_norm_apply_le B (-k)) (norm_nonneg _)

/-- The **bilinear spatial pairing** of two Wiener states. -/
noncomputable def wpair (A B : Wiener) : ℂ := ∑' k : Gam, A k * B (-k)

/-- **The pairing is the actual integral over the torus** for the normalized Haar measure. -/
theorem wpair_eq_integral (A B : Wiener) :
    wpair A B = ∫ x : Torus2, synth A x * synth B x := by
  rw [integral_synth_mul A (synth B)]
  refine tsum_congr fun k => ?_
  have h2 : (∫ x : Torus2, emode k x * synth B x) = B (-k) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall
      fun x => mul_comm (emode k x) (synth B x))]
    exact integral_synth_mul_emode B k
  rw [h2]

theorem wpair_comm (A B : Wiener) : wpair A B = wpair B A := by
  rw [wpair, wpair]
  have h : ∀ k : Gam, A (-k) * B (-(-k)) = B k * A (-k) := by
    intro k
    rw [neg_neg]
    ring
  calc (∑' k : Gam, A k * B (-k))
      = ∑' k : Gam, A (-k) * B (-(-k)) := ((Equiv.neg Gam).tsum_eq
        (fun k : Gam => A k * B (-k))).symm
    _ = ∑' k : Gam, B k * A (-k) := tsum_congr h

/-! ## The three-factor sum -/

theorem summable_triple (A B C : Wiener) :
    Summable fun z : Gam × Gam => ‖A z.1 * B z.2 * C (-(z.1 + z.2))‖ := by
  have hprod : Summable fun z : Gam × Gam => ‖A z.1‖ * ‖B z.2‖ :=
    (wiener_summable A).mul_of_nonneg (wiener_summable B) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) (hprod.mul_right ‖C‖)
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (wiener_norm_apply_le C _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The symmetric three-factor sum over frequency triples summing to zero. -/
noncomputable def wtriple (A B C : Wiener) : ℂ :=
  ∑' z : Gam × Gam, A z.1 * B z.2 * C (-(z.1 + z.2))

theorem wtriple_swap12 (A B C : Wiener) : wtriple A B C = wtriple B A C := by
  rw [wtriple, wtriple]
  have hswap := (Equiv.prodComm Gam Gam).tsum_eq
    (fun z : Gam × Gam => B z.1 * A z.2 * C (-(z.1 + z.2)))
  rw [← hswap]
  refine tsum_congr fun z => ?_
  show A z.1 * B z.2 * C (-(z.1 + z.2)) = B z.2 * A z.1 * C (-(z.2 + z.1))
  rw [add_comm z.2 z.1]
  ring

theorem wtriple_swap23 (A B C : Wiener) : wtriple A B C = wtriple A C B := by
  rw [wtriple, wtriple]
  let e : Gam × Gam ≃ Gam × Gam :=
    { toFun := fun z => (z.1, -(z.1 + z.2))
      invFun := fun z => (z.1, -(z.1 + z.2))
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
  have h := e.tsum_eq (fun z : Gam × Gam => A z.1 * C z.2 * B (-(z.1 + z.2)))
  rw [← h]
  refine tsum_congr fun z => ?_
  show A z.1 * B z.2 * C (-(z.1 + z.2))
    = A z.1 * C (-(z.1 + z.2)) * B (-(z.1 + -(z.1 + z.2)))
  have hz : (z.1 + -(z.1 + z.2)) = -z.2 := by abel
  rw [hz, neg_neg]
  ring

/-! ## Pairing against a convolution -/

theorem wpair_conv_eq_wtriple (P Q R : Wiener) : wpair (conv P Q) R = wtriple P Q R := by
  have hPQ : Summable fun z : Gam × Gam => ‖P z.2 * Q (z.1 - z.2)‖ :=
    summable_shear (wiener_summable P) (wiener_summable Q)
  have hF : Summable fun z : Gam × Gam => ‖P z.2 * Q (z.1 - z.2) * R (-z.1)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) (hPQ.mul_right ‖R‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (wiener_norm_apply_le R _) (norm_nonneg _)
  have hFs : Summable fun z : Gam × Gam => P z.2 * Q (z.1 - z.2) * R (-z.1) := hF.of_norm
  have hleft : wpair (conv P Q) R
      = ∑' z : Gam × Gam, P z.2 * Q (z.1 - z.2) * R (-z.1) := by
    rw [wpair, hFs.tsum_prod]
    refine tsum_congr fun k => ?_
    show conv P Q k * R (-k) = ∑' c : Gam, P c * Q (k - c) * R (-k)
    rw [conv_apply]
    exact tsum_mul_right.symm
  have hshear := shear.tsum_eq (fun w : Gam × Gam => P w.1 * Q w.2 * R (-(w.1 + w.2)))
  rw [hleft, wtriple, ← hshear]
  refine tsum_congr fun z => ?_
  show P z.2 * Q (z.1 - z.2) * R (-z.1)
    = P z.2 * Q (z.1 - z.2) * R (-(z.2 + (z.1 - z.2)))
  have harg : (z.2 + (z.1 - z.2) : Gam) = z.1 := by abel
  rw [harg]

theorem wpair_add_left (A A' B : Wiener) : wpair (A + A') B = wpair A B + wpair A' B := by
  rw [wpair, wpair, wpair, ← Summable.tsum_add (summable_wpair A B).of_norm
    (summable_wpair A' B).of_norm]
  refine tsum_congr fun k => ?_
  show (A + A') k * B (-k) = A k * B (-k) + A' k * B (-k)
  rw [lp.coeFn_add, Pi.add_apply]
  ring

/-! ## The velocity of a first-order state is first order -/

/-- For a uniformly bounded symbol the velocity of an `A¹` state is again an `A¹` state.  This
is what makes the interior term of the integration by parts an honest Wiener element. -/
noncomputable def velocity1 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (a : Wiener1) : Wiener1 :=
  Wiener1.mk (fun k => m j k * a.coeff k) (by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
      (fun k => ?_) (a.summable_wt.mul_left (Classical.choose hm))
    rw [norm_mul]
    have h := Classical.choose_spec hm j k
    have hw : (0:ℝ) ≤ wt k := (wt_pos k).le
    have hn : (0:ℝ) ≤ ‖a.coeff k‖ := norm_nonneg _
    calc wt k * (‖m j k‖ * ‖a.coeff k‖) = ‖m j k‖ * (wt k * ‖a.coeff k‖) := by ring
      _ ≤ Classical.choose hm * (wt k * ‖a.coeff k‖) :=
          mul_le_mul_of_nonneg_right h (by positivity))

@[simp] theorem velocity1_coeff (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (a : Wiener1) (k : Gam) : (velocity1 m hm j a).coeff k = m j k * a.coeff k := rfl

theorem incl_velocity1 (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2) (a : Wiener1) :
    incl (velocity1 m hm j a) = velocity m hm j (incl a) := by
  ext k; rfl

/-! ## Leibniz and divergence freedom -/

/-- **The Leibniz identity for the three-factor pairing.**  This is the product rule, and it is
where the interior term of the integration by parts appears explicitly. -/
theorem wtriple_leibniz (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (j : Fin 2)
    (a b ψ : Wiener1) :
    wtriple (incl (velocity1 m hm j a)) (fourierDeriv j b) (incl ψ)
      + wtriple (fourierDeriv j (velocity1 m hm j a)) (incl b) (incl ψ)
      + wtriple (incl (velocity1 m hm j a)) (incl b) (fourierDeriv j ψ) = 0 := by
  set P : Wiener := incl (velocity1 m hm j a) with hP
  set dP : Wiener := fourierDeriv j (velocity1 m hm j a) with hdP
  set B : Wiener := incl b with hB
  set dB : Wiener := fourierDeriv j b with hdB
  set Ψ : Wiener := incl ψ with hΨ
  set dΨ : Wiener := fourierDeriv j ψ with hdΨ
  have h1 : Summable fun z : Gam × Gam => P z.1 * dB z.2 * Ψ (-(z.1 + z.2)) :=
    (summable_triple P dB Ψ).of_norm
  have h2 : Summable fun z : Gam × Gam => dP z.1 * B z.2 * Ψ (-(z.1 + z.2)) :=
    (summable_triple dP B Ψ).of_norm
  have h3 : Summable fun z : Gam × Gam => P z.1 * B z.2 * dΨ (-(z.1 + z.2)) :=
    (summable_triple P B dΨ).of_norm
  rw [wtriple, wtriple, wtriple, ← Summable.tsum_add h1 h2, ← Summable.tsum_add (h1.add h2) h3]
  have hzero : ∀ z : Gam × Gam,
      (P z.1 * dB z.2 * Ψ (-(z.1 + z.2)) + dP z.1 * B z.2 * Ψ (-(z.1 + z.2)))
        + P z.1 * B z.2 * dΨ (-(z.1 + z.2)) = 0 := by
    intro z
    have e1 : dB z.2 = twoPiI * ((z.2 j : ℤ) : ℂ) * B z.2 := rfl
    have e2 : dP z.1 = twoPiI * ((z.1 j : ℤ) : ℂ) * P z.1 := rfl
    have e3 : dΨ (-(z.1 + z.2))
        = twoPiI * (((-(z.1 + z.2)) j : ℤ) : ℂ) * Ψ (-(z.1 + z.2)) := rfl
    have e4 : (((-(z.1 + z.2)) j : ℤ) : ℂ) = -(((z.1 j : ℤ) : ℂ) + ((z.2 j : ℤ) : ℂ)) := by
      have h : ((-(z.1 + z.2)) j : ℤ) = -((z.1 j) + (z.2 j)) := rfl
      rw [h]
      push_cast
      ring
    rw [e1, e2, e3, e4]
    ring
  rw [tsum_congr hzero, tsum_zero]

/-- A symbol whose velocity field is divergence free at every frequency. -/
def IsDivFreeSymbol (m : Fin 2 → Gam → ℂ) : Prop :=
  ∀ k : Gam, ∑ j : Fin 2, ((k j : ℤ) : ℂ) * m j k = 0

theorem rotatedGradientSymbol_isDivFree (κ : Gam → ℂ) :
    IsDivFreeSymbol (rotatedGradientSymbol κ) := by
  intro k
  rw [Fin.sum_univ_two]
  exact rotatedGradientSymbol_divFree κ k

theorem IsDivFreeSymbol.sub {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsDivFreeSymbol m₁)
    (h₂ : IsDivFreeSymbol m₂) : IsDivFreeSymbol (m₁ - m₂) := by
  intro k
  have e : ∀ j : Fin 2, ((k j : ℤ) : ℂ) * (m₁ - m₂) j k
      = ((k j : ℤ) : ℂ) * m₁ j k - ((k j : ℤ) : ℂ) * m₂ j k := by
    intro j
    show ((k j : ℤ) : ℂ) * (m₁ j k - m₂ j k) = _
    ring
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, h₁ k, h₂ k, sub_zero]

/-- **The interior term of the integration by parts vanishes** for a divergence-free
velocity. -/
theorem sum_wtriple_divFree {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hdiv : IsDivFreeSymbol m) (a b ψ : Wiener1) :
    ∑ j : Fin 2, wtriple (fourierDeriv j (velocity1 m hm j a)) (incl b) (incl ψ) = 0 := by
  have hsum : ∀ j : Fin 2, Summable fun z : Gam × Gam =>
      (fourierDeriv j (velocity1 m hm j a)) z.1 * (incl b) z.2 * (incl ψ) (-(z.1 + z.2)) :=
    fun j => (summable_triple _ _ _).of_norm
  simp only [wtriple]
  rw [← Summable.tsum_finsetSum (fun j _ => hsum j)]
  have hzero : ∀ z : Gam × Gam,
      (∑ j : Fin 2, (fourierDeriv j (velocity1 m hm j a)) z.1 * (incl b) z.2
        * (incl ψ) (-(z.1 + z.2))) = 0 := by
    intro z
    have e : ∀ j : Fin 2, (fourierDeriv j (velocity1 m hm j a)) z.1 * (incl b) z.2
        * (incl ψ) (-(z.1 + z.2))
        = (((z.1 j : ℤ) : ℂ) * m j z.1)
          * (twoPiI * a.coeff z.1 * (incl b) z.2 * (incl ψ) (-(z.1 + z.2))) := by
      intro j
      show (twoPiI * ((z.1 j : ℤ) : ℂ) * (m j z.1 * a.coeff z.1)) * (incl b) z.2
          * (incl ψ) (-(z.1 + z.2)) = _
      ring
    rw [Finset.sum_congr rfl (fun j _ => e j), ← Finset.sum_mul, hdiv z.1, zero_mul]
  rw [tsum_congr hzero, tsum_zero]

/-! ## Skew-adjointness: the actual spatial integration by parts -/

/-- **Spatial integration by parts against an exterior test state.**  For a divergence-free
velocity symbol the transport form is skew-adjoint in its second argument for the physical
pairing:

    `∫_{𝕋²} N_m(a,b)·ψ = − ∫_{𝕋²} b·N_m(a,ψ)`.

The derivative is moved off the state and onto the test function; the interior term produced by
the product rule is exactly the one killed by `div R_m(a) = 0`, and it is **not** discarded but
proved to vanish (`sum_wtriple_divFree`). -/
theorem wpair_transport_skew {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hdiv : IsDivFreeSymbol m) (a b ψ : Wiener1) :
    wpair (transport m hm a b) (incl ψ) = - wpair (incl b) (transport m hm a ψ) := by
  have hvel : ∀ j : Fin 2, velocity m hm j (incl a) = incl (velocity1 m hm j a) :=
    fun j => (incl_velocity1 m hm j a).symm
  -- expand the transport form
  have hsplit : ∀ c : Wiener1, wpair (transport m hm a c) (incl ψ)
      = ∑ j : Fin 2, wtriple (incl (velocity1 m hm j a)) (fourierDeriv j c) (incl ψ) := by
    intro c
    rw [transport_apply, Fin.sum_univ_two, wpair_add_left, Fin.sum_univ_two,
      hvel 0, hvel 1, wpair_conv_eq_wtriple, wpair_conv_eq_wtriple]
  have hL := hsplit b
  -- Leibniz, term by term
  have hleib : ∀ j : Fin 2,
      wtriple (incl (velocity1 m hm j a)) (fourierDeriv j b) (incl ψ)
        = -(wtriple (fourierDeriv j (velocity1 m hm j a)) (incl b) (incl ψ))
          - wtriple (incl (velocity1 m hm j a)) (incl b) (fourierDeriv j ψ) := by
    intro j
    have h := wtriple_leibniz m hm j a b ψ
    linear_combination h
  rw [hL, Fin.sum_univ_two, hleib 0, hleib 1]
  have hdivz := sum_wtriple_divFree hm hdiv a b ψ
  rw [Fin.sum_univ_two] at hdivz
  -- the remaining terms reassemble the transport form with the test function
  have hswap : ∀ j : Fin 2,
      wtriple (incl (velocity1 m hm j a)) (incl b) (fourierDeriv j ψ)
        = wtriple (incl (velocity1 m hm j a)) (fourierDeriv j ψ) (incl b) :=
    fun j => wtriple_swap23 _ _ _
  rw [hswap 0, hswap 1]
  have hR : wpair (incl b) (transport m hm a ψ)
      = wtriple (incl (velocity1 m hm 0 a)) (fourierDeriv 0 ψ) (incl b)
        + wtriple (incl (velocity1 m hm 1 a)) (fourierDeriv 1 ψ) (incl b) := by
    rw [wpair_comm, transport_apply, Fin.sum_univ_two, wpair_add_left,
      hvel 0, hvel 1, wpair_conv_eq_wtriple, wpair_conv_eq_wtriple]
  rw [hR]
  linear_combination (-1 : ℂ) * hdivz

theorem norm_wpair_le (A B : Wiener) : ‖wpair A B‖ ≤ ‖A‖ * ‖B‖ := by
  have hb : ∀ k : Gam, ‖A k * B (-k)‖ ≤ ‖A k‖ * ‖B‖ := by
    intro k
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (wiener_norm_apply_le B (-k)) (norm_nonneg _)
  calc ‖wpair A B‖ ≤ ∑' k : Gam, ‖A k * B (-k)‖ :=
        norm_tsum_le_tsum_norm (summable_wpair A B)
    _ ≤ ∑' k : Gam, ‖A k‖ * ‖B‖ :=
        Summable.tsum_le_tsum hb (summable_wpair A B) ((wiener_summable A).mul_right ‖B‖)
    _ = ‖A‖ * ‖B‖ := by rw [tsum_mul_right, wiener_norm_eq A]

/-! ## The tested symmetrized interaction -/

/-- **The tested symmetrized interaction, with its exact sign.**  For a divergence-free
velocity symbol and any exterior test state `ψ`,

    `∫ (N(v₁,v₂) + N(v₂,v₁))·ψ  =  − ∫ v₂·N(v₁,ψ) − ∫ v₁·N(v₂,ψ)`,

both sides actual integrals over `𝕋²`, with the derivative moved onto `ψ`. -/
theorem wpair_symmetrized_transport {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hdiv : IsDivFreeSymbol m) (v₁ v₂ ψ : Wiener1) :
    wpair (transport m hm v₁ v₂ + transport m hm v₂ v₁) (incl ψ)
      = -(wpair (incl v₂) (transport m hm v₁ ψ))
        - wpair (incl v₁) (transport m hm v₂ ψ) := by
  rw [wpair_add_left, wpair_transport_skew hm hdiv v₁ v₂ ψ,
    wpair_transport_skew hm hdiv v₂ v₁ ψ]
  ring

/-- **The Section 6 identity.**  If the symmetrized generated interaction vanishes, the tested
form vanishes with the derivative on the exterior test function. -/
theorem tested_symmetrized_eq_zero {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hdiv : IsDivFreeSymbol m) {v₁ v₂ : Wiener1}
    (hgen : transport m hm v₁ v₂ + transport m hm v₂ v₁ = 0) (ψ : Wiener1) :
    wpair (incl v₂) (transport m hm v₁ ψ) + wpair (incl v₁) (transport m hm v₂ ψ) = 0 := by
  have h := wpair_symmetrized_transport hm hdiv v₁ v₂ ψ
  rw [hgen] at h
  have hz : wpair (0 : Wiener) (incl ψ) = 0 := by
    rw [wpair]
    have : ∀ k : Gam, (0 : Wiener) k * (incl ψ) (-k) = 0 := by
      intro k
      show (0 : Wiener) k * _ = 0
      simp only [lp.coeFn_zero, Pi.zero_apply, zero_mul]
    rw [tsum_congr this, tsum_zero]
  rw [hz] at h
  linear_combination h

/-! ## The space-time (Bochner) form -/

variable {α T : ℝ}

/-- **The tested output, pointwise in time.**  Pairing the vanishing symmetrized interaction of
the two first responses against a test state gives zero at *every* time.  This is a
pointwise-in-time identity, **not** a time integral; the genuine iterated space-time integral is
`LiWang.WienerModel.spacetimeTestedInteraction_eq_zero` in `TwoStateContinuity`. -/
theorem section6_spacetime_output (hα : 1 / 2 < α) (hT : 0 ≤ T) {m₁ m₂ : Fin 2 → Gam → ℂ}
    (hm₁ : IsBddSymbol m₁) (hr₁ : IsRealSymbol m₁) (hm₂ : IsBddSymbol m₂) (hr₂ : IsRealSymbol m₂)
    (hdiv : IsDivFreeSymbol (m₁ - m₂)) {h₁ h₂ : Curve0 T}
    (hgen : spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
          (duhamelOp hα hT h₁) (duhamelOp hα hT h₂)
        + spacetimeTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)
          (duhamelOp hα hT h₂) (duhamelOp hα hT h₁) = 0)
    (ψ : Wiener1) (φ : ℝ → ℂ) :
    ∀ t : ℝ, φ t * (wpair (incl (curveState hT (duhamelOp hα hT h₂) t))
          (transport (m₁ - m₂) (hm₁.sub hm₂) (curveState hT (duhamelOp hα hT h₁) t) ψ)
        + wpair (incl (curveState hT (duhamelOp hα hT h₁) t))
          (transport (m₁ - m₂) (hm₁.sub hm₂) (curveState hT (duhamelOp hα hT h₂) t) ψ)) = 0 := by
  intro t
  have hpt : transport (m₁ - m₂) (hm₁.sub hm₂)
        (curveState hT (duhamelOp hα hT h₁) t) (curveState hT (duhamelOp hα hT h₂) t)
      + transport (m₁ - m₂) (hm₁.sub hm₂)
        (curveState hT (duhamelOp hα hT h₂) t) (curveState hT (duhamelOp hα hT h₁) t) = 0 := by
    have hval := congrArg (fun V : Curve0 T => (V (clampT hT t)).val) hgen
    simpa using hval
  rw [tested_symmetrized_eq_zero (hm₁.sub hm₂) hdiv hpt ψ, mul_zero]

/-! ## The nonlocality obstruction, isolated

`R_m` is a **nonlocal** operator.  The identity above concerns `N_m` applied to the *full*
states.  Replacing a test state by the zero extension of its exterior restriction changes the
velocity everywhere, so exterior convergence of restrictions is **not** enough: what is needed
is convergence of the test states in the Wiener `A¹` norm, which is a strictly stronger
topology.  The next two statements make that precise: the tested pairing *is* continuous for
`A¹` convergence (proved), and the required approximation property is named (not proved, not
assumed). -/

/-- **Stability of the tested pairing under `A¹` convergence of the test state.**  The tested
interaction is Lipschitz in the test state for the Wiener `A¹` norm, with the explicit
constant `4πC‖v‖`. -/
theorem norm_wpair_transport_sub_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (a b ψ ψ' : Wiener1) :
    ‖wpair (incl b) (transport m hm a ψ) - wpair (incl b) (transport m hm a ψ')‖
      ≤ ‖b‖ * (4 * Real.pi * C * ‖a‖ * ‖ψ - ψ'‖) := by
  have hlin : wpair (incl b) (transport m hm a ψ) - wpair (incl b) (transport m hm a ψ')
      = wpair (incl b) (transport m hm a (ψ - ψ')) := by
    have hadd := wpair_add_left (transport m hm a (ψ - ψ')) (transport m hm a ψ') (incl b)
    have hsum : transport m hm a (ψ - ψ') + transport m hm a ψ' = transport m hm a ψ := by
      rw [← map_add]
      congr 1
      abel
    rw [hsum] at hadd
    rw [wpair_comm (incl b) (transport m hm a ψ),
      wpair_comm (incl b) (transport m hm a ψ'),
      wpair_comm (incl b) (transport m hm a (ψ - ψ'))]
    linear_combination hadd
  rw [hlin]
  calc ‖wpair (incl b) (transport m hm a (ψ - ψ'))‖
      ≤ ‖incl b‖ * ‖transport m hm a (ψ - ψ')‖ := norm_wpair_le _ _
    _ ≤ ‖b‖ * (4 * Real.pi * C * ‖a‖ * ‖ψ - ψ'‖) := by
        refine mul_le_mul (norm_incl_apply_le b) (norm_transport_apply_le hm hC a (ψ - ψ'))
          (norm_nonneg _) (norm_nonneg _)

/-- `A¹` approximation of a **test state** by exterior-supported test states.  This concerns the
test function only; see `ExteriorStateConvergence` in `ExteriorLimit` for the hypotheses the
actual state-approximation step needs. -/
def ExteriorApproximationInA1 (Ω : Set Torus2) (ψ : ℕ → Wiener1) (Ψ : Wiener1) : Prop :=
  (∀ n : ℕ, ∀ x ∈ Ω, synth (incl (ψ n)) x = 0) ∧
    Filter.Tendsto (fun n => ‖ψ n - Ψ‖) Filter.atTop (nhds 0)

/-- **A test-function limit, not the Runge step.**  Here the *test state* `ψ n` varies while the
two states `v₁, v₂` stay fixed, so the conclusion already follows from
`tested_symmetrized_eq_zero hm hdiv hgen Ψ` without `happrox`, without a sequence, and without
any limit; the statement is kept only as a continuity regression for the `A¹` topology.  It is
**not** the Runge step, which replaces the *generated solution states* by prescribed targets.
The correct state-limit statement, with `ψ` fixed and the two states varying, is
`LiWang.WienerModel.tested_symmetrized_state_limit` in `ExteriorLimit`. -/
theorem tested_symmetrized_limit {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) {C : ℝ}
    (hC : ∀ j k, ‖m j k‖ ≤ C) (hdiv : IsDivFreeSymbol m) {v₁ v₂ : Wiener1}
    (hgen : transport m hm v₁ v₂ + transport m hm v₂ v₁ = 0) {Ω : Set Torus2}
    {ψ : ℕ → Wiener1} {Ψ : Wiener1} (happrox : ExteriorApproximationInA1 Ω ψ Ψ) :
    wpair (incl v₂) (transport m hm v₁ Ψ) + wpair (incl v₁) (transport m hm v₂ Ψ) = 0 := by
  have hzero : ∀ n : ℕ,
      wpair (incl v₂) (transport m hm v₁ (ψ n)) + wpair (incl v₁) (transport m hm v₂ (ψ n)) = 0 :=
    fun n => tested_symmetrized_eq_zero hm hdiv hgen (ψ n)
  have hbound : ∀ n : ℕ,
      ‖(wpair (incl v₂) (transport m hm v₁ Ψ) + wpair (incl v₁) (transport m hm v₂ Ψ))‖
        ≤ (‖v₂‖ * (4 * Real.pi * C * ‖v₁‖) + ‖v₁‖ * (4 * Real.pi * C * ‖v₂‖)) * ‖ψ n - Ψ‖ := by
    intro n
    have e1 := norm_wpair_transport_sub_le hm hC v₁ v₂ Ψ (ψ n)
    have e2 := norm_wpair_transport_sub_le hm hC v₂ v₁ Ψ (ψ n)
    have hd : (wpair (incl v₂) (transport m hm v₁ Ψ) + wpair (incl v₁) (transport m hm v₂ Ψ))
        = (wpair (incl v₂) (transport m hm v₁ Ψ) - wpair (incl v₂) (transport m hm v₁ (ψ n)))
          + (wpair (incl v₁) (transport m hm v₂ Ψ)
              - wpair (incl v₁) (transport m hm v₂ (ψ n))) := by
      have := hzero n
      linear_combination this
    rw [hd]
    have hnormsub : ‖Ψ - ψ n‖ = ‖ψ n - Ψ‖ := norm_sub_rev _ _
    calc ‖(wpair (incl v₂) (transport m hm v₁ Ψ) - wpair (incl v₂) (transport m hm v₁ (ψ n)))
            + (wpair (incl v₁) (transport m hm v₂ Ψ)
              - wpair (incl v₁) (transport m hm v₂ (ψ n)))‖
        ≤ ‖wpair (incl v₂) (transport m hm v₁ Ψ)
            - wpair (incl v₂) (transport m hm v₁ (ψ n))‖
          + ‖wpair (incl v₁) (transport m hm v₂ Ψ)
            - wpair (incl v₁) (transport m hm v₂ (ψ n))‖ := norm_add_le _ _
      _ ≤ ‖v₂‖ * (4 * Real.pi * C * ‖v₁‖ * ‖Ψ - ψ n‖)
          + ‖v₁‖ * (4 * Real.pi * C * ‖v₂‖ * ‖Ψ - ψ n‖) := add_le_add e1 e2
      _ = (‖v₂‖ * (4 * Real.pi * C * ‖v₁‖) + ‖v₁‖ * (4 * Real.pi * C * ‖v₂‖)) * ‖ψ n - Ψ‖ := by
          rw [hnormsub]; ring
  -- let n → ∞
  have hlim : Filter.Tendsto (fun n : ℕ =>
      (‖v₂‖ * (4 * Real.pi * C * ‖v₁‖) + ‖v₁‖ * (4 * Real.pi * C * ‖v₂‖)) * ‖ψ n - Ψ‖)
      Filter.atTop (nhds 0) := by
    have := happrox.2.const_mul
      (‖v₂‖ * (4 * Real.pi * C * ‖v₁‖) + ‖v₁‖ * (4 * Real.pi * C * ‖v₂‖))
    simpa using this
  have hle := ge_of_tendsto' hlim (fun n => hbound n)
  have hnn : (0:ℝ) ≤ ‖wpair (incl v₂) (transport m hm v₁ Ψ)
      + wpair (incl v₁) (transport m hm v₂ Ψ)‖ := norm_nonneg _
  have : ‖wpair (incl v₂) (transport m hm v₁ Ψ)
      + wpair (incl v₁) (transport m hm v₂ Ψ)‖ = 0 := le_antisymm hle hnn
  exact norm_eq_zero.mp this

end LiWang.WienerModel
