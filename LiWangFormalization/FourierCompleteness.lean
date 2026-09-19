/-
# Completeness of the trigonometric system in `L²(𝕋²)`

The packet already knows that the Fourier monomials `emode k` are orthonormal in `L²(𝕋²)`
(`orthonormal_synthL2_wdirac`).  This file proves the missing half — **completeness** — and
extracts from it the Fourier-coefficient functional on the physical carrier:

* `l2coeff k f = ⟪e_k, f⟫` is the `k`-th Fourier coefficient of an arbitrary element of
  `TorusL2`, with `l2coeff_synthL2` identifying it with the coefficient of a synthesized state;
* `torusL2_ext_of_forall_l2coeff` — two `L²(𝕋²)` classes with the same Fourier coefficients are
  equal;
* `synthL2_incl_eq_of_coeff` — an `L²` state whose Fourier coefficients are those of a
  first-order Wiener element **is** the synthesis of that element.

The proof is Stone–Weierstrass plus density of continuous functions in `L²`: the linear span of
the monomials is dense in `C(𝕋², ℂ)` (Mathlib's `UnitAddTorus.span_mFourier_closure_eq_top`,
which is a statement about continuous functions and involves no measure), and `C(𝕋², ℂ)` is
dense in `L²` for a finite regular measure on a compact space
(`ContinuousMap.toLp_denseRange`).  Both steps are carried out in **this packet's own measure**
`(volume : Measure Torus2)`; no measure is replaced or rescaled.

Part of `LiWangFormalizationSobolevCompatibilityPacket` v8.0.
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import LiWangFormalization.PhysicalL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate
open Filter Topology MeasureTheory

namespace LiWang.Formalization

/-! ## 1. The packet's monomials are Mathlib's multivariate monomials -/

/-- `emode k` is exactly Mathlib's `UnitAddTorus.mFourier k` on `𝕋² = (ℝ/ℤ)²`. -/
theorem emode_eq_mFourier (k : Gam) : emode k = UnitAddTorus.mFourier k := by
  refine ContinuousMap.ext (fun x => ?_)
  rw [emode_apply]
  show _ = ∏ i : Fin 2, fourier (k i) (x i)
  rw [Fin.prod_univ_two]

/-- **The linear span of the Fourier monomials is dense in `C(𝕋², ℂ)`.** -/
theorem dense_span_emode :
    Dense ((Submodule.span ℂ (Set.range emode) : Submodule ℂ C(Torus2, ℂ)) : Set C(Torus2, ℂ)) := by
  have hrange : Set.range emode = Set.range (UnitAddTorus.mFourier (d := Fin 2)) := by
    ext F
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, (emode_eq_mFourier k).symm⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, emode_eq_mFourier k⟩
  have htop := UnitAddTorus.span_mFourier_closure_eq_top (d := Fin 2)
  rw [hrange]
  have := congrArg (fun S : Submodule ℂ C(Torus2, ℂ) => (S : Set C(Torus2, ℂ))) htop
  simpa [Submodule.topologicalClosure_coe, dense_iff_closure_eq] using this

/-! ## 2. Density in the physical `L²` carrier -/

/-- **The synthesized monomials span a dense subspace of `L²(𝕋²)`.** -/
theorem dense_span_synthL2_wdirac :
    Dense ((Submodule.span ℂ (Set.range (fun k : Gam => synthL2 (wdirac k))) :
      Submodule ℂ TorusL2) : Set TorusL2) := by
  set Φ : C(Torus2, ℂ) →L[ℂ] TorusL2 :=
    ContinuousMap.toLp (E := ℂ) 2 (volume : Measure Torus2) ℂ with hΦ
  have hdr : DenseRange (Φ : C(Torus2, ℂ) → TorusL2) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := (volume : Measure Torus2)) ℂ
      (by simp)
  set P : Submodule ℂ C(Torus2, ℂ) := Submodule.span ℂ (Set.range emode) with hP
  have hPd : Dense (P : Set C(Torus2, ℂ)) := dense_span_emode
  set Q : Submodule ℂ TorusL2 :=
    Submodule.span ℂ (Set.range (fun k : Gam => synthL2 (wdirac k))) with hQ
  have himg : Submodule.map (Φ : C(Torus2, ℂ) →ₗ[ℂ] TorusL2) P = Q := by
    rw [hP, hQ, Submodule.map_span]
    congr 1
    ext F
    constructor
    · rintro ⟨G, ⟨k, rfl⟩, rfl⟩
      refine ⟨k, ?_⟩
      show synthL2 (wdirac k) = Φ (emode k)
      rw [synthL2_wdirac]
    · rintro ⟨k, rfl⟩
      refine ⟨emode k, ⟨k, rfl⟩, ?_⟩
      show Φ (emode k) = synthL2 (wdirac k)
      rw [synthL2_wdirac]
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  have hsub : (Φ : C(Torus2, ℂ) → TorusL2) '' (closure (P : Set C(Torus2, ℂ)))
      ⊆ closure ((Φ : C(Torus2, ℂ) → TorusL2) '' (P : Set C(Torus2, ℂ))) :=
    image_closure_subset_closure_image Φ.continuous
  have himgset : (Φ : C(Torus2, ℂ) → TorusL2) '' (P : Set C(Torus2, ℂ)) = (Q : Set TorusL2) := by
    rw [← himg]; rfl
  rw [himgset] at hsub
  rw [hPd.closure_eq, Set.image_univ] at hsub
  calc (Set.univ : Set TorusL2) = closure (Set.range (Φ : C(Torus2, ℂ) → TorusL2)) :=
        hdr.closure_range.symm
    _ ⊆ closure (closure (Q : Set TorusL2)) := closure_mono hsub
    _ = closure (Q : Set TorusL2) := closure_closure

/-! ## 3. The Fourier coefficient functional on `L²(𝕋²)` -/

/-- **The `k`-th Fourier coefficient of an arbitrary `L²(𝕋²)` class.** -/
noncomputable def l2coeff (k : Gam) (f : TorusL2) : ℂ := inner ℂ (synthL2 (wdirac k)) f

/-- On a synthesized state it is the Wiener coefficient. -/
@[simp] theorem l2coeff_synthL2 (a : Wiener) (k : Gam) : l2coeff k (synthL2 a) = a k := by
  rw [l2coeff, inner_synthL2]
  have hterm : ∀ j : Gam, conj ((wdirac k) j) * a j = if j = k then a j else 0 := by
    intro j
    by_cases hj : j = k
    · subst hj; simp [diracFun]
    · simp [diracFun, hj]
  rw [tsum_congr hterm, tsum_ite_eq]

theorem l2coeff_sub (k : Gam) (f g : TorusL2) :
    l2coeff k (f - g) = l2coeff k f - l2coeff k g := by
  rw [l2coeff, l2coeff, l2coeff, inner_sub_right]

/-! ## 4. Completeness -/

/-- **An `L²(𝕋²)` class all of whose Fourier coefficients vanish is zero.** -/
theorem eq_zero_of_forall_l2coeff_eq_zero {u : TorusL2} (h : ∀ k : Gam, l2coeff k u = 0) :
    u = 0 := by
  set K : Submodule ℂ TorusL2 :=
    { carrier := {v : TorusL2 | (inner ℂ v u : ℂ) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        show (inner ℂ (x + y) u : ℂ) = 0
        rw [inner_add_left]
        show (inner ℂ x u : ℂ) + (inner ℂ y u : ℂ) = 0
        rw [hx, hy, add_zero]
      smul_mem' := by
        intro c x hx
        show (inner ℂ (c • x) u : ℂ) = 0
        rw [inner_smul_left]
        show conj c * (inner ℂ x u : ℂ) = 0
        rw [hx, mul_zero] } with hK
  have hclosed : IsClosed ((K : Submodule ℂ TorusL2) : Set TorusL2) := by
    have hcont : Continuous fun v : TorusL2 => (inner ℂ v u : ℂ) :=
      (continuous_inner (𝕜 := ℂ)).comp (continuous_id.prodMk continuous_const)
    exact isClosed_eq hcont continuous_const
  have hspan : (Submodule.span ℂ (Set.range (fun k : Gam => synthL2 (wdirac k)))) ≤ K := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨k, rfl⟩
    exact h k
  have hsub : closure ((Submodule.span ℂ (Set.range (fun k : Gam => synthL2 (wdirac k))) :
      Submodule ℂ TorusL2) : Set TorusL2) ⊆ (K : Set TorusL2) :=
    hclosed.closure_subset_iff.2 hspan
  rw [dense_span_synthL2_wdirac.closure_eq] at hsub
  exact inner_self_eq_zero.1 (hsub (Set.mem_univ u))

/-- **Two `L²(𝕋²)` classes with the same Fourier coefficients are equal.** -/
theorem torusL2_ext_of_forall_l2coeff {u v : TorusL2} (h : ∀ k : Gam, l2coeff k u = l2coeff k v) :
    u = v := by
  have h0 : ∀ k : Gam, l2coeff k (u - v) = 0 := by
    intro k; rw [l2coeff_sub, h k, sub_self]
  have := eq_zero_of_forall_l2coeff_eq_zero h0
  exact sub_eq_zero.1 this

/-- **The identification an `H^s` state needs**: an `L²` class whose Fourier coefficients are
those of a first-order Wiener element *is* the synthesis of that element.  Nothing about the
state is modified: the equality is in `L²(𝕋²)`. -/
theorem synthL2_incl_eq_of_coeff {w : Wiener1} {θ : TorusL2}
    (h : ∀ k : Gam, l2coeff k θ = w.coeff k) : synthL2 (incl w) = θ :=
  (torusL2_ext_of_forall_l2coeff (fun k => by rw [l2coeff_synthL2, h k]; rfl)).symm

end LiWang.Formalization
