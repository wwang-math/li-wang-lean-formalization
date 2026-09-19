/-
The real (conjugate-symmetric) Banach carriers `RealWiener`, `RealWiener1`, the real
transport form and the real quadratic residual.

Part of `LiWangWienerPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import LiWangWiener.RotatedGradient

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## 13. Real Banach carriers and the real quadratic residual

The conjugate-symmetric elements form closed **real** subspaces of the Wiener carriers.
They are Banach spaces over `ℝ`, and the transport form and the quadratic residual restrict
to them.  Nothing here is assumed: the preservation of conjugate symmetry is the theorem
`LiWang.WienerModel.ConjSymmetric.transport` of Section 11, and the real polarization identity is
proved, not postulated.

Each carrier is defined as an `ℝ`-submodule wrapped in a type synonym (`def`, not `abbrev`),
so that its normed structure is the one *induced* from the ambient Wiener carrier rather
than a competing subtype instance; this is the same device used for `Wiener1`. -/

theorem continuous_wienerEval (k : Gam) : Continuous fun a : Wiener => (a : Gam → ℂ) k :=
  (lp.lipschitzWith_one_eval (E := fun _ : Gam => ℂ) 1 k).continuous

theorem continuous_wiener1Coeff (k : Gam) : Continuous fun u : Wiener1 => u.coeff k :=
  (continuous_wienerEval k).comp incl.continuous

/-- The set of conjugate-symmetric Wiener elements is closed. -/
theorem isClosed_conjSymmetricWiener :
    IsClosed {a : Wiener | ConjSymmetric (a : Gam → ℂ)} := by
  have hset : {a : Wiener | ConjSymmetric (a : Gam → ℂ)}
      = ⋂ k : Gam, {a : Wiener | (a : Gam → ℂ) (-k) = conj ((a : Gam → ℂ) k)} := by
    ext a
    simp only [Set.mem_setOf_eq, ConjSymmetric, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun k => ?_
  exact isClosed_eq (continuous_wienerEval (-k))
    (Complex.continuous_conj.comp (continuous_wienerEval k))

/-- The set of conjugate-symmetric first-order elements is closed. -/
theorem isClosed_conjSymmetricWiener1 :
    IsClosed {u : Wiener1 | ConjSymmetric u.coeff} := by
  have hset : {u : Wiener1 | ConjSymmetric u.coeff}
      = ⋂ k : Gam, {u : Wiener1 | u.coeff (-k) = conj (u.coeff k)} := by
    ext u
    simp only [Set.mem_setOf_eq, ConjSymmetric, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun k => ?_
  exact isClosed_eq (continuous_wiener1Coeff (-k))
    (Complex.continuous_conj.comp (continuous_wiener1Coeff k))

/-- The real (conjugate-symmetric) `ℝ`-submodule of the Wiener algebra. -/
def realWienerSub : Submodule ℝ Wiener where
  carrier := {a | ConjSymmetric (a : Gam → ℂ)}
  zero_mem' := conjSymmetric_zero_wiener
  add_mem' := fun ha hb => ConjSymmetric.wiener_add ha hb
  smul_mem' := fun r _ ha => ConjSymmetric.wiener_real_smul r ha

/-- The real (conjugate-symmetric) `ℝ`-submodule of the first-order Wiener space. -/
def realWiener1Sub : Submodule ℝ Wiener1 where
  carrier := {u | ConjSymmetric u.coeff}
  zero_mem' := conjSymmetric_zero_wiener1
  add_mem' := fun hu hv => ConjSymmetric.wiener1_add hu hv
  smul_mem' := fun r _ hu => ConjSymmetric.wiener1_real_smul r hu

/-- The **real Wiener algebra** `A_ℝ(𝕋²)`: conjugate-symmetric absolutely summable Fourier
coefficients, a real Banach space. -/
def RealWiener : Type := ↥realWienerSub

/-- The **real first-order Wiener space** `A¹_ℝ(𝕋²)`, a real Banach space. -/
def RealWiener1 : Type := ↥realWiener1Sub

namespace RealWiener

noncomputable instance : AddCommGroup RealWiener := inferInstanceAs (AddCommGroup ↥realWienerSub)
noncomputable instance : Module ℝ RealWiener := inferInstanceAs (Module ℝ ↥realWienerSub)

/-- The underlying element of the Wiener algebra. -/
def val (a : RealWiener) : Wiener := (show ↥realWienerSub from a).1

theorem conjSymmetric (a : RealWiener) : ConjSymmetric ((a.val : Wiener) : Gam → ℂ) :=
  (show ↥realWienerSub from a).2

/-- Build a real Wiener element from a conjugate-symmetric one. -/
def mk (a : Wiener) (h : ConjSymmetric (a : Gam → ℂ)) : RealWiener :=
  (⟨a, h⟩ : ↥realWienerSub)

@[simp] theorem val_mk (a : Wiener) (h : ConjSymmetric (a : Gam → ℂ)) : (mk a h).val = a := rfl
@[simp] theorem val_zero : (0 : RealWiener).val = 0 := rfl
@[simp] theorem val_add (a b : RealWiener) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_sub (a b : RealWiener) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_smul (r : ℝ) (a : RealWiener) : (r • a).val = r • a.val := rfl

theorem val_injective : Function.Injective RealWiener.val := by
  intro a b h
  exact Subtype.ext (α := Wiener) h

/-- The underlying-element map as an additive homomorphism. -/
def valHom : RealWiener →+ Wiener where
  toFun := val
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem valHom_apply (a : RealWiener) : valHom a = a.val := rfl

noncomputable instance : NormedAddCommGroup RealWiener :=
  NormedAddCommGroup.induced RealWiener Wiener valHom val_injective

theorem norm_def (a : RealWiener) : ‖a‖ = ‖a.val‖ := rfl

noncomputable instance : NormedSpace ℝ RealWiener :=
  { (inferInstance : Module ℝ RealWiener) with
    norm_smul_le := fun r a => by
      show ‖(r • a).val‖ ≤ ‖r‖ * ‖a.val‖
      rw [val_smul]
      exact norm_smul_le r a.val }

theorem isometry_val : Isometry RealWiener.val :=
  AddMonoidHomClass.isometry_of_norm valHom (fun _ => rfl)

theorem range_val : Set.range RealWiener.val = {a : Wiener | ConjSymmetric (a : Gam → ℂ)} := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩; exact x.conjSymmetric
  · intro h; exact ⟨mk a h, rfl⟩

/-- The real Wiener algebra is a real Banach space. -/
instance : CompleteSpace RealWiener :=
  (completeSpace_iff_isComplete_range isometry_val.isUniformInducing).mpr
    (by rw [range_val]; exact isClosed_conjSymmetricWiener.isComplete)

end RealWiener

namespace RealWiener1

noncomputable instance : AddCommGroup RealWiener1 := inferInstanceAs (AddCommGroup ↥realWiener1Sub)
noncomputable instance : Module ℝ RealWiener1 := inferInstanceAs (Module ℝ ↥realWiener1Sub)

/-- The underlying element of the first-order Wiener space. -/
def val (u : RealWiener1) : Wiener1 := (show ↥realWiener1Sub from u).1

theorem conjSymmetric (u : RealWiener1) : ConjSymmetric (u.val).coeff :=
  (show ↥realWiener1Sub from u).2

/-- Build a real first-order element from a conjugate-symmetric one. -/
def mk (u : Wiener1) (h : ConjSymmetric u.coeff) : RealWiener1 := (⟨u, h⟩ : ↥realWiener1Sub)

@[simp] theorem val_mk (u : Wiener1) (h : ConjSymmetric u.coeff) : (mk u h).val = u := rfl
@[simp] theorem val_zero : (0 : RealWiener1).val = 0 := rfl
@[simp] theorem val_add (u v : RealWiener1) : (u + v).val = u.val + v.val := rfl
@[simp] theorem val_sub (u v : RealWiener1) : (u - v).val = u.val - v.val := rfl
@[simp] theorem val_smul (r : ℝ) (u : RealWiener1) : (r • u).val = r • u.val := rfl

theorem val_injective : Function.Injective RealWiener1.val := by
  intro u v h
  exact Subtype.ext (α := Wiener1) h

def valHom : RealWiener1 →+ Wiener1 where
  toFun := val
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem valHom_apply (u : RealWiener1) : valHom u = u.val := rfl

noncomputable instance : NormedAddCommGroup RealWiener1 :=
  NormedAddCommGroup.induced RealWiener1 Wiener1 valHom val_injective

theorem norm_def (u : RealWiener1) : ‖u‖ = ‖u.val‖ := rfl

noncomputable instance : NormedSpace ℝ RealWiener1 :=
  { (inferInstance : Module ℝ RealWiener1) with
    norm_smul_le := fun r u => by
      show ‖(r • u).val‖ ≤ ‖r‖ * ‖u.val‖
      rw [val_smul]
      exact norm_smul_le r u.val }

theorem isometry_val : Isometry RealWiener1.val :=
  AddMonoidHomClass.isometry_of_norm valHom (fun _ => rfl)

theorem range_val : Set.range RealWiener1.val = {u : Wiener1 | ConjSymmetric u.coeff} := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩; exact x.conjSymmetric
  · intro h; exact ⟨mk u h, rfl⟩

/-- The real first-order Wiener space is a real Banach space. -/
instance : CompleteSpace RealWiener1 :=
  (completeSpace_iff_isComplete_range isometry_val.isUniformInducing).mpr
    (by rw [range_val]; exact isClosed_conjSymmetricWiener1.isComplete)

end RealWiener1

/-! ### The real transport form -/

theorem smul_real_wiener1 (r : ℝ) (u : Wiener1) : r • u = ((r : ℂ)) • u :=
  (Complex.coe_smul r u).symm

theorem smul_real_wiener (r : ℝ) (a : Wiener) : r • a = ((r : ℂ)) • a :=
  (Complex.coe_smul r a).symm

noncomputable def realTransportLm (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : RealWiener1 →ₗ[ℝ] RealWiener1 →ₗ[ℝ] RealWiener :=
  LinearMap.mk₂ ℝ
    (fun u v => RealWiener.mk (transport m hm u.val v.val)
      (ConjSymmetric.transport hm hr u.conjSymmetric v.conjSymmetric))
    (fun u₁ u₂ v => RealWiener.val_injective (by
      show transport m hm (u₁.val + u₂.val) v.val
          = transport m hm u₁.val v.val + transport m hm u₂.val v.val
      rw [map_add, ContinuousLinearMap.add_apply]))
    (fun r u v => RealWiener.val_injective (by
      show transport m hm (r • u.val) v.val = r • transport m hm u.val v.val
      rw [smul_real_wiener1, map_smul, ContinuousLinearMap.smul_apply, smul_real_wiener]))
    (fun u v₁ v₂ => RealWiener.val_injective (by
      show transport m hm u.val (v₁.val + v₂.val)
          = transport m hm u.val v₁.val + transport m hm u.val v₂.val
      rw [map_add]))
    (fun r u v => RealWiener.val_injective (by
      show transport m hm u.val (r • v.val) = r • transport m hm u.val v.val
      rw [smul_real_wiener1, map_smul, smul_real_wiener]))

@[simp] theorem realTransportLm_val (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u v : RealWiener1) :
    (realTransportLm m hm hr u v).val = transport m hm u.val v.val := rfl

theorem norm_realTransportLm_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u v : RealWiener1) :
    ‖realTransportLm m hm hr u v‖ ≤ 4 * Real.pi * C * ‖u‖ * ‖v‖ := by
  show ‖transport m hm u.val v.val‖ ≤ 4 * Real.pi * C * ‖u.val‖ * ‖v.val‖
  exact norm_transport_apply_le hm hC _ _

/-- **The real transport form** `N_m : A¹_ℝ × A¹_ℝ → A_ℝ`, a continuous *real*-bilinear
map between real Banach spaces. -/
noncomputable def realTransport (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : RealWiener1 →L[ℝ] RealWiener1 →L[ℝ] RealWiener :=
  LinearMap.mkContinuousOfExistsBound₂ (realTransportLm m hm hr)
    ⟨4 * Real.pi * Classical.choose hm, fun u v =>
      norm_realTransportLm_le hm hr (Classical.choose_spec hm) u v⟩

@[simp] theorem realTransport_val (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (u v : RealWiener1) :
    (realTransport m hm hr u v).val = transport m hm u.val v.val := rfl

theorem norm_realTransport_apply_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) (u v : RealWiener1) :
    ‖realTransport m hm hr u v‖ ≤ 4 * Real.pi * C * ‖u‖ * ‖v‖ :=
  norm_realTransportLm_le hm hr hC u v

theorem norm_realTransport_le {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    {C : ℝ} (hC : ∀ j k, ‖m j k‖ ≤ C) : ‖realTransport m hm hr‖ ≤ 4 * Real.pi * C := by
  have hC0 : 0 ≤ C := nonneg_of_symbol_bound hC
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) (fun u v => ?_)
  exact norm_realTransport_apply_le hm hr hC u v

theorem realTransport_congr_symbol {m m' : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hm' : IsBddSymbol m') (hr : IsRealSymbol m) (hr' : IsRealSymbol m') (h : m = m') :
    realTransport m hm hr = realTransport m' hm' hr' := by subst h; rfl

/-- Linearity of the real transport form in the symbol. -/
theorem realTransport_sub {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₁ : IsRealSymbol m₁) (hr₂ : IsRealSymbol m₂) :
    realTransport m₁ hm₁ hr₁ - realTransport m₂ hm₂ hr₂
      = realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) := by
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  refine RealWiener.val_injective ?_
  show transport m₁ hm₁ u.val v.val - transport m₂ hm₂ u.val v.val
      = transport (m₁ - m₂) (hm₁.sub hm₂) u.val v.val
  rw [← transport_sub hm₁ hm₂, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]

/-! ### The real quadratic residual -/

/-- **The real quadratic residual** `Q_m(u) = N_m(u,u)` on the real carriers. -/
noncomputable def realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : RealWiener1 → RealWiener := quad (realTransport m hm hr)

theorem realQuadResidual_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (u : RealWiener1) : realQuadResidual m hm hr u = realTransport m hm hr u u := rfl

/-- `Q_m(0) = 0` over `ℝ`. -/
theorem realQuadResidual_zero (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m) :
    realQuadResidual m hm hr 0 = 0 := quad_zero _

theorem hasFDerivAt_realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (x : RealWiener1) :
    HasFDerivAt (realQuadResidual m hm hr)
      (realTransport m hm hr x + (realTransport m hm hr).flip x) x := hasFDerivAt_quad _ x

theorem fderiv_realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (x : RealWiener1) : fderiv ℝ (realQuadResidual m hm hr) x
      = realTransport m hm hr x + (realTransport m hm hr).flip x := fderiv_quad _ x

/-- **`DQ_m(0) = 0` over `ℝ`.** -/
theorem fderiv_realQuadResidual_zero (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : fderiv ℝ (realQuadResidual m hm hr) 0 = 0 := fderiv_quad_zero _

/-- `Q_m` is `C^n` over `ℝ` for every smoothness index. -/
theorem contDiff_realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (n : WithTop ℕ∞) : ContDiff ℝ n (realQuadResidual m hm hr) :=
  contDiff_quad _ n

/-- **`Q_m` is `C²` over `ℝ`.** -/
theorem contDiff_two_realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : ContDiff ℝ 2 (realQuadResidual m hm hr) := contDiff_quad _ 2

theorem contDiff_top_realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) : ContDiff ℝ (⊤ : ℕ∞) (realQuadResidual m hm hr) := contDiff_quad _ _

/-- Analyticity of the real quadratic residual, as a genuine `AnalyticOnNhd` statement. -/
theorem analyticOnNhd_realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (s : Set RealWiener1) :
    AnalyticOnNhd ℝ (realQuadResidual m hm hr) s := analyticOnNhd_quad _ s

/-- **The mixed second derivative over `ℝ`** is the symmetrized real transport form. -/
theorem fderiv_fderiv_realQuadResidual_apply (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : RealWiener1) :
    fderiv ℝ (fderiv ℝ (realQuadResidual m hm hr)) 0 h₁ h₂
      = realTransport m hm hr h₁ h₂ + realTransport m hm hr h₂ h₁ := by
  have hq : realQuadResidual m hm hr = quad (realTransport m hm hr) := rfl
  rw [hq, fderiv_fderiv_quad]
  simp

theorem iteratedFDeriv_two_realQuadResidual (m : Fin 2 → Gam → ℂ) (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) (h₁ h₂ : RealWiener1) :
    iteratedFDeriv ℝ 2 (realQuadResidual m hm hr) 0 ![h₁, h₂]
      = realTransport m hm hr h₁ h₂ + realTransport m hm hr h₂ h₁ :=
  iteratedFDeriv_two_quad _ 0 h₁ h₂

/-- **The real two-symbol Li–Wang polarization identity.** -/
theorem realLiWangPolarization {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₁ : IsRealSymbol m₁) (hr₂ : IsRealSymbol m₂)
    (g₁ g₂ : RealWiener1) :
    fderiv ℝ (fderiv ℝ (fun x => realQuadResidual m₁ hm₁ hr₁ x
        - realQuadResidual m₂ hm₂ hr₂ x)) 0 g₁ g₂
      = realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) g₁ g₂
        + realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) g₂ g₁ := by
  have hfun : (fun x => realQuadResidual m₁ hm₁ hr₁ x - realQuadResidual m₂ hm₂ hr₂ x)
      = quad (realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)) := by
    funext x
    rw [← realTransport_sub hm₁ hm₂ hr₁ hr₂]
    rfl
  rw [hfun, fderiv_fderiv_quad]
  simp

theorem realLiWangPolarization_iteratedFDeriv {m₁ m₂ : Fin 2 → Gam → ℂ} (hm₁ : IsBddSymbol m₁)
    (hm₂ : IsBddSymbol m₂) (hr₁ : IsRealSymbol m₁) (hr₂ : IsRealSymbol m₂)
    (g₁ g₂ : RealWiener1) :
    iteratedFDeriv ℝ 2 (fun x => realQuadResidual m₁ hm₁ hr₁ x
        - realQuadResidual m₂ hm₂ hr₂ x) 0 ![g₁, g₂]
      = realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) g₁ g₂
        + realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂) g₂ g₁ := by
  have hfun : (fun x => realQuadResidual m₁ hm₁ hr₁ x - realQuadResidual m₂ hm₂ hr₂ x)
      = quad (realTransport (m₁ - m₂) (hm₁.sub hm₂) (hr₁.sub hr₂)) := by
    funext x
    rw [← realTransport_sub hm₁ hm₂ hr₁ hr₂]
    rfl
  rw [hfun]
  exact iteratedFDeriv_two_quad _ 0 g₁ g₂

end LiWang.WienerModel
