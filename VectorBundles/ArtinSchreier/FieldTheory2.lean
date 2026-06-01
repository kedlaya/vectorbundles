module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

open Module

variable (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsPurelyInseparable F K]

lemma finite_inseparable_extension_intermediate_small (h: 1 < finrank F K) :
  ∃ E: IntermediateField F K, finrank F E = ringChar F := by
  let p := ringChar F
  let iota := algebraMap F K
  have h : Nat.Prime p ∧ p = ringExpChar F ∧ ∃ n : ℕ, finrank F K = p ^ n :=
    finite_inseparable_extension_data F K h
  obtain ⟨hpp, hp, n, hn⟩ := h
  have hx : ∃ x : K, x ∉ iota.range :=
    have h1 : ¬ Function.Surjective iota := finite_extension_degree_one F K h
    not_forall.mp h1
  obtain ⟨x, hx⟩ := hx
  let e := IsPurelyInseparable.elemExponent F x
  have he1 : e ≠ 0 := by
    by_contra
    have hexp : x ^ (ringExpChar F) ^ e ∈ iota.range := IsPurelyInseparable.elemExponent_def F x
    rw [this] at hexp
    grind
  let y := x ^ p ^ (e-1)
  let z := IsPurelyInseparable.elemReduct F x
  let pol1 := Polynomial.X ^ p ^ e - Polynomial.C z
  have h_pol1 : minpoly F x = pol1 := by grind [IsPurelyInseparable.minpoly_eq F x]
  let pol := Polynomial.X ^ p - Polynomial.C z
  have hy_int : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have ha : ∀ a : F, a^p ≠ z := by
    have hx1 : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    have hirr1 : Irreducible (minpoly F x) := minpoly.irreducible hx1
    rw [h_pol1] at hirr1
    have hirr2 : ∀ {m : ℕ}, m ∣ p^e → m ≠ 1 → ∀ (b : F), b ^ m ≠ z :=
      pow_ne_of_irreducible_X_pow_sub_C hirr1
    apply hirr2
    · simp only [dvd_pow_self_iff]
      left
      exact he1
    · exact CharP.ringChar_ne_one
  have hirr : Irreducible pol := (X_pow_sub_C_irreducible_iff_of_prime hpp).mpr ha
  have h_pol : minpoly F y = pol :=
    have hy : pol.aeval y = 0 := by
      calc
      pol.aeval y = y ^ p - iota z := by aesop
      _ = x ^ p ^ e - iota z := by
        refine sub_left_inj.mpr ?_
        subst y
        ring_nf
        have h: p * p^(e-1) = p^e := mul_pow_sub_one he1 p
        rw [h]
      _ = pol1.aeval x := by aesop
      _ = 0 := by
        rw [←h_pol1]
        apply minpoly.aeval F x
    let pol2 := minpoly F y
    have hpol : pol2 ∣ pol := (minpoly.isIntegrallyClosed_dvd_iff hy_int pol).mp hy
    have hmon1 : pol.Monic := by
      refine Polynomial.monic_X_pow_sub_C z ?_
      exact Nat.Prime.ne_zero hpp
    have hmon : pol2.Monic := minpoly.monic hy_int
    have hdeg : pol2.natDegree = pol.natDegree := by
      have : pol2.natDegree = 0 ∨ pol2.natDegree = pol.natDegree :=
        divisor_of_irreducible_poly hpol hirr
      have : pol2.natDegree > 0 := minpoly.natDegree_pos hy_int
      grind
    monic_divisor_of_same_degree hmon hmon1 hpol hdeg
  let E := IntermediateField.adjoin F {y}
  use E
  calc
      finrank F E = (minpoly F y).natDegree := IntermediateField.adjoin.finrank hy_int
      _ = pol.natDegree := by rw [h_pol]
      _ = p := Polynomial.natDegree_X_pow_sub_C

-- Note unusual hypothesis format, needed for induction tactic.
lemma finite_inseparable_extension_intermediate_internal (n : ℕ) :
  ∀ (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K], 1 < finrank F K → finrank F K = (ringChar F)^n →
      ∃ (E : IntermediateField F K), finrank E K = ringChar F := by
  induction n with
  | zero => -- This case cannot occur
    grind
  | succ n hyp =>
    intro F K _ _ _ _ _ hr h1
    let p := ringChar F
    have h : Nat.Prime p ∧ p = ringExpChar F ∧ ∃ n : ℕ, finrank F K = p ^ n :=
      finite_inseparable_extension_data F K hr
    obtain ⟨hpp, hp, _⟩ := h
    have : ExpChar F p := ringExpChar.eq_iff.mp (id hp.symm)
    have hp2 : p ≥ 2 := Nat.Prime.two_le hpp
    have hE₀: ∃ E₀: IntermediateField F K, finrank F E₀ = p :=
      finite_inseparable_extension_intermediate_small F K hr
    obtain ⟨E₀, hE₀⟩ := hE₀
    by_cases hn1 : n = 0
    · use ⊥
      aesop
    · have hchar : ringChar E₀ = p := (Algebra.ringChar_eq F ↥E₀).symm
      have hE : ∃ E: IntermediateField E₀ K, finrank E K = ringChar E₀ := by
        have hn2 : finrank E₀ K = p^n := by
          have h3 : p * finrank E₀ K = p * p^n  := by
            calc
              p * finrank E₀ K = finrank F E₀ * finrank E₀ K := by rw [hE₀]
              _ = finrank F K := finrank_mul_finrank F E₀ K
              _ = p ^ (n+1) := h1
              _ = p * p^n := Nat.pow_succ'
          have h5 : p ≠ 0 := Nat.ne_zero_of_lt hp2
          apply (Nat.mul_right_inj h5).mp h3
        apply hyp E₀ K
        · calc
            finrank E₀ K = p^n := hn2
            _ > 1 := Nat.one_lt_pow hn1 hp2
        · rw [hchar]
          exact hn2
      obtain ⟨E, hE₁⟩ := hE
      let E₁ := IntermediateField.restrictScalars F E
      use E₁
      calc
        finrank E₁ K = ringChar E₀ := hE₁
        _ = p := hchar

lemma finite_inseparable_extension_intermediate (h: 1 < finrank F K) :
  ∃ E : IntermediateField F K, finrank E K = ringChar F := by
  let p := ringChar F
  have h : Nat.Prime p ∧ p = ringExpChar F ∧ ∃ n : ℕ, finrank F K = p ^ n :=
    finite_inseparable_extension_data F K h
  obtain ⟨_, _, n, hn⟩ := h
  apply finite_inseparable_extension_intermediate_internal n F K h hn
