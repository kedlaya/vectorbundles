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

lemma finite_inseparable_extension_data (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (h: finrank F K > 1) :
      Nat.Prime (ringChar F) ∧ ringChar F = ringExpChar F ∧
        ∃ (n : ℕ), finrank F K = (ringChar F) ^ n := by

  let p := ringChar F
  let q := ringExpChar F
  have _ : ExpChar F q := ringExpChar.expChar F
  have hn : ∃ n, finrank F K = q ^ n :=
    IsPurelyInseparable.finrank_eq_pow F K q
  obtain ⟨n₁, hn⟩ := hn
  have hpp : Nat.Prime p := by
    have : q ≠ 1 := by
      by_contra
      have : finrank F K = 1 := by
        rw [this] at hn
        simp_all
      grind
    have : q = 1 ↔ p = 0 := expChar_one_iff_char_zero F p q
    have : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
    simp_all
  have hp : p = ringExpChar F := (char_eq_expChar_iff F p q).mpr hpp
  constructor
  · exact hpp
  constructor
  · exact hp
  · subst q
    rw [← hp] at hn
    use n₁

lemma finite_inseparable_extension_intermediate_small (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (h: finrank F K > 1) :
      ∃ E: IntermediateField F K, finrank F E = ringChar F := by

  let p := ringChar F
  have h : Nat.Prime p ∧ p = ringExpChar F ∧ ∃ (n : ℕ), finrank F K = p ^ n :=
    finite_inseparable_extension_data F K h
  obtain ⟨hpp, hp, n, hn⟩ := h
  have hx : ∃ x : K, x ∉ (algebraMap F K).range :=
    have h1 : ¬ Function.Surjective (algebraMap F K) :=
      finite_extension_degree_one F K h
    not_forall.mp h1
  obtain ⟨x, hx⟩ := hx
  let e := IsPurelyInseparable.elemExponent F x
  have he : e > 0 := by
    have hexp : x ^ (ringExpChar F) ^ e ∈ (algebraMap F K).range := IsPurelyInseparable.elemExponent_def F x
    by_contra
    push Not at this
    have this : e = 0 := Nat.le_zero.mp this
    rw [this] at hexp
    grind
  let y := x^(p^(e-1))
  let z := IsPurelyInseparable.elemReduct F x
  let pol1 := Polynomial.X ^ (p^e) - Polynomial.C z
  have h_pol1 : minpoly F x = pol1 := by grind [IsPurelyInseparable.minpoly_eq F x]
  let pol := Polynomial.X ^ p - Polynomial.C z
  have hy_int : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hirr : Irreducible pol := by
    have ha : ∀ (a : F), a^p ≠ z := by
      have hx1 : IsIntegral F x := Algebra.IsIntegral.isIntegral x
      have hirr1 : Irreducible (minpoly F x) := minpoly.irreducible hx1
      rw [h_pol1] at hirr1
      have hirr2 : ∀ {m : ℕ}, m ∣ p^e → m ≠ 1 → ∀ (b : F), b ^ m ≠ z :=
        pow_ne_of_irreducible_X_pow_sub_C hirr1
      apply hirr2
      · simp
        left
        exact Nat.ne_zero_iff_zero_lt.mpr he
      · exact CharP.ringChar_ne_one
    exact (X_pow_sub_C_irreducible_iff_of_prime hpp).mpr ha
  have h_pol : minpoly F y = pol := by
    have hy : pol.aeval y = 0 := by
      calc
        pol.aeval y = pol1.aeval x := by
          have h1 : ∃ (f : ℕ), e = f + 1 := Nat.exists_eq_add_of_le' he
          obtain ⟨f, hf⟩ := h1
          unfold Polynomial.aeval Polynomial.aevalEquiv
          subst pol pol1 y
          simp
          rw [hf]
          ring_nf
          simp
        _ = (Polynomial.aeval x) (minpoly F x) :=
          AlgHom.congr_arg (Polynomial.aeval x) (id h_pol1.symm)
        _ = 0 := minpoly.aeval F x
    have hpol : minpoly F y ∣ pol := (minpoly.isIntegrallyClosed_dvd_iff hy_int pol).mp hy
    have hmon1 : pol.Monic := by
      refine Polynomial.monic_X_pow_sub_C z ?_
      exact Nat.Prime.ne_zero hpp
    have hmon : (minpoly F y).Monic := minpoly.monic hy_int
    have hdeg : (minpoly F y).natDegree = pol.natDegree := by
      have : (minpoly F y).natDegree = 0 ∨ (minpoly F y).natDegree = pol.natDegree :=
        divisor_of_irreducible_poly (minpoly F y) pol hpol hirr
      have : (minpoly F y).natDegree > 0 := minpoly.natDegree_pos hy_int
      grind
    exact monic_divisor_of_same_degree (minpoly F y) pol hmon hmon1 hpol hdeg
  let E := IntermediateField.adjoin F {y}
  use E
  calc
    finrank F E = (minpoly F y).natDegree := IntermediateField.adjoin.finrank hy_int
    _ = pol.natDegree := by rw [h_pol]
    _ = p := Polynomial.natDegree_X_pow_sub_C

-- Note unusual hypothesis format, needed for induction tactic.
lemma finite_inseparable_extension_intermediate_internal (n : ℕ) :
  ∀ (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K], finrank F K > 1 → finrank F K = (ringChar F)^n →
       ∃ (E : IntermediateField F K), finrank E K = ringChar F := by

  induction n with
  | zero => -- This case cannot occur
    grind
  | succ n hyp =>
    intro F K _ _ _ _ _ hr h1
    let p := ringChar F
    have h : Nat.Prime p ∧ p = ringExpChar F ∧ ∃ (n : ℕ), finrank F K = p ^ n :=
      finite_inseparable_extension_data F K hr
    obtain ⟨hpp, hp, _⟩ := h
    have : ExpChar F p := ringExpChar.eq_iff.mp (id hp.symm)
    have hp2 : p ≥ 2 := Nat.Prime.two_le hpp
    by_cases hn1 : n = 0
    · use (⊥: IntermediateField F K)
      simp_all
    · have hE₀: ∃ E₀: IntermediateField F K, finrank F E₀ = p :=
        finite_inseparable_extension_intermediate_small F K hr
      obtain ⟨E₀, hE₀⟩ := hE₀
      have hchar : ringChar E₀ = p := (Algebra.ringChar_eq F ↥E₀).symm
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
      obtain ⟨E, hE⟩ := hE
      let E₁ := IntermediateField.restrictScalars F E
      use E₁
      calc
        finrank E₁ K = ringChar E₀ := hE
        _ = p := hchar

lemma finite_inseparable_extension_intermediate (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (hr: finrank F K > 1) :
      ∃ E : IntermediateField F K, finrank E K = ringChar F := by

    let p := ringChar F
    have h : Nat.Prime p ∧ p = ringExpChar F ∧
      ∃ (n : ℕ), finrank F K = p ^ n :=
      finite_inseparable_extension_data F K hr
    obtain ⟨hpp, hp, n, hn⟩ := h
    apply finite_inseparable_extension_intermediate_internal n F K hr hn
