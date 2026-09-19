/-
Conjugate symmetry `a(-k) = conj (a k)` — the Fourier-side reality condition — and its
preservation by every operation of the packet.

Part of `LiWangWienerPhysicalResidualPacket` v2.0 (coefficient layer, unchanged from v1.1).
-/
import LiWangWiener.NonDegeneracy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace LiWang.WienerModel

/-! ## 11. Conjugate symmetry: the Fourier side of reality

A Fourier coefficient family on `Γ = ℤ²` is the coefficient family of a *real-valued*
function on `𝕋²` exactly when it is conjugate symmetric, `a(-k) = conj (a k)`.  This
section defines that condition and proves that it is preserved by every operation of the
packet. -/

/-- A coefficient family is **conjugate symmetric** if `a(-k) = conj (a k)` for all `k`.
This is the Fourier-side reality condition. -/
def ConjSymmetric (a : Gam → ℂ) : Prop := ∀ k, a (-k) = conj (a k)

namespace ConjSymmetric

theorem zero : ConjSymmetric (0 : Gam → ℂ) := fun _ => by simp

theorem add {a b : Gam → ℂ} (ha : ConjSymmetric a) (hb : ConjSymmetric b) :
    ConjSymmetric (a + b) := fun k => by
  simp only [Pi.add_apply, ha k, hb k, map_add]

theorem neg {a : Gam → ℂ} (ha : ConjSymmetric a) : ConjSymmetric (-a) := fun k => by
  simp only [Pi.neg_apply, ha k, map_neg]

theorem sub {a b : Gam → ℂ} (ha : ConjSymmetric a) (hb : ConjSymmetric b) :
    ConjSymmetric (a - b) := fun k => by
  simp only [Pi.sub_apply, ha k, hb k, map_sub]

/-- Conjugate symmetry is preserved by **real** scalar multiplication (but not, in general,
by complex scalar multiplication). -/
theorem real_smul (r : ℝ) {a : Gam → ℂ} (ha : ConjSymmetric a) :
    ConjSymmetric (fun k => (r : ℂ) * a k) := fun k => by
  simp only [ha k, map_mul, Complex.conj_ofReal]

theorem smul_fun (r : ℝ) {a : Gam → ℂ} (ha : ConjSymmetric a) : ConjSymmetric (r • a) :=
  fun k => by
  simp only [Pi.smul_apply, Complex.real_smul, ha k, map_mul, Complex.conj_ofReal]

end ConjSymmetric

/-! ### Conjugate symmetry on the Wiener carriers -/

theorem conjSymmetric_zero_wiener : ConjSymmetric ((0 : Wiener) : Gam → ℂ) := by
  rw [lp.coeFn_zero]; exact ConjSymmetric.zero

theorem ConjSymmetric.wiener_add {a b : Wiener} (ha : ConjSymmetric (a : Gam → ℂ))
    (hb : ConjSymmetric (b : Gam → ℂ)) : ConjSymmetric ((a + b : Wiener) : Gam → ℂ) := by
  rw [lp.coeFn_add]; exact ha.add hb

theorem ConjSymmetric.wiener_sub {a b : Wiener} (ha : ConjSymmetric (a : Gam → ℂ))
    (hb : ConjSymmetric (b : Gam → ℂ)) : ConjSymmetric ((a - b : Wiener) : Gam → ℂ) := by
  rw [lp.coeFn_sub]; exact ha.sub hb

theorem ConjSymmetric.wiener_real_smul (r : ℝ) {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric ((r • a : Wiener) : Gam → ℂ) := by
  rw [lp.coeFn_smul]; exact ha.smul_fun r

theorem conjSymmetric_zero_wiener1 : ConjSymmetric ((0 : Wiener1).coeff) := by
  rw [Wiener1.coeff_zero]; exact ConjSymmetric.zero

theorem ConjSymmetric.wiener1_add {u v : Wiener1} (hu : ConjSymmetric u.coeff)
    (hv : ConjSymmetric v.coeff) : ConjSymmetric ((u + v).coeff) := by
  rw [Wiener1.coeff_add]; exact hu.add hv

theorem ConjSymmetric.wiener1_sub {u v : Wiener1} (hu : ConjSymmetric u.coeff)
    (hv : ConjSymmetric v.coeff) : ConjSymmetric ((u - v).coeff) := by
  have h : (u - v).coeff = u.coeff - v.coeff := rfl
  rw [h]; exact hu.sub hv

theorem ConjSymmetric.wiener1_real_smul (r : ℝ) {u : Wiener1} (hu : ConjSymmetric u.coeff) :
    ConjSymmetric ((r • u : Wiener1).coeff) := by
  have h : ((r • u : Wiener1)).coeff = r • u.coeff := rfl
  rw [h]; exact hu.smul_fun r

/-! ### Conjugate symmetry is preserved by the operators of the packet -/

/-- **The inclusion `A¹ ↪ A` preserves conjugate symmetry.** -/
theorem ConjSymmetric.incl {u : Wiener1} (hu : ConjSymmetric u.coeff) :
    ConjSymmetric ((incl u : Wiener) : Gam → ℂ) := hu

theorem conj_twoPiI : conj twoPiI = -twoPiI := by
  simp [twoPiI, Complex.conj_ofReal, map_ofNat]

/-- **Fourier differentiation preserves conjugate symmetry.** -/
theorem ConjSymmetric.fourierDeriv (j : Fin 2) {u : Wiener1} (hu : ConjSymmetric u.coeff) :
    ConjSymmetric ((fourierDeriv j u : Wiener) : Gam → ℂ) := by
  intro k
  show twoPiI * (((-k) j : ℤ) : ℂ) * u.coeff (-k)
      = conj (twoPiI * ((k j : ℤ) : ℂ) * u.coeff k)
  have hneg : ((-k) j : ℤ) = -(k j) := rfl
  rw [hneg, hu k, map_mul, map_mul, conj_twoPiI, map_intCast, Int.cast_neg]
  ring

/-- **Convolution preserves conjugate symmetry.** -/
theorem ConjSymmetric.conv {a b : Wiener} (ha : ConjSymmetric (a : Gam → ℂ))
    (hb : ConjSymmetric (b : Gam → ℂ)) : ConjSymmetric ((conv a b : Wiener) : Gam → ℂ) := by
  intro k
  show ∑' p, a p * b (-k - p) = conj (∑' p, a p * b (k - p))
  rw [Complex.conj_tsum]
  rw [← Equiv.tsum_eq (Equiv.neg Gam) (fun p => a p * b (-k - p))]
  refine tsum_congr fun p => ?_
  show a (-p) * b (-k - -p) = conj (a p * b (k - p))
  have h1 : (-k - -p : Gam) = -(k - p) := by abel
  rw [h1, ha p, hb (k - p), map_mul]

/-- **A Fourier multiplier whose symbol is conjugate symmetric preserves conjugate
symmetry.** -/
theorem ConjSymmetric.mult {μ : Gam → ℂ} (hμ : ∃ C : ℝ, ∀ k, ‖μ k‖ ≤ C)
    (hcs : ConjSymmetric μ) {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric ((mult μ hμ a : Wiener) : Gam → ℂ) := by
  intro k
  show μ (-k) * a (-k) = conj (μ k * a k)
  rw [hcs k, ha k, map_mul]

/-- A velocity symbol is **real** (in the Fourier sense) if each component is conjugate
symmetric, `m j (-k) = conj (m j k)`. -/
def IsRealSymbol (m : Fin 2 → Gam → ℂ) : Prop := ∀ j, ConjSymmetric (m j)

theorem IsRealSymbol.sub {m₁ m₂ : Fin 2 → Gam → ℂ} (h₁ : IsRealSymbol m₁)
    (h₂ : IsRealSymbol m₂) : IsRealSymbol (m₁ - m₂) := fun j => (h₁ j).sub (h₂ j)

/-- **The velocity operator of a real symbol preserves conjugate symmetry.** -/
theorem ConjSymmetric.velocity {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m) (hr : IsRealSymbol m)
    (j : Fin 2) {a : Wiener} (ha : ConjSymmetric (a : Gam → ℂ)) :
    ConjSymmetric ((velocity m hm j a : Wiener) : Gam → ℂ) :=
  ConjSymmetric.mult (hm.component j) (hr j) ha

/-- **The full transport map preserves conjugate symmetry.** -/
theorem ConjSymmetric.transport {m : Fin 2 → Gam → ℂ} (hm : IsBddSymbol m)
    (hr : IsRealSymbol m) {u v : Wiener1} (hu : ConjSymmetric u.coeff)
    (hv : ConjSymmetric v.coeff) :
    ConjSymmetric ((transport m hm u v : Wiener) : Gam → ℂ) := by
  rw [transport_apply, Fin.sum_univ_two]
  refine ConjSymmetric.wiener_add ?_ ?_ <;>
    exact ConjSymmetric.conv (ConjSymmetric.velocity hm hr _ hu.incl)
      (ConjSymmetric.fourierDeriv _ hv)

end LiWang.WienerModel
