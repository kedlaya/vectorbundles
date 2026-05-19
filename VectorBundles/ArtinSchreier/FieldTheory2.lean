module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower

public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

lemma finite_inseparable_extension_intermediate_small (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsPurelyInseparable F K] (h: Module.finrank F K > 1) :
  ∃ E: IntermediateField F K, Module.finrank F E = ringChar F := by

  have hx : ∃ x : K, x ∉ (algebraMap F K).range := by
    have h1 : Module.finrank F K > 1 → ¬ Function.Surjective (algebraMap F K) :=
      finite_extension_degree_one F K
    unfold Function.Surjective at h1
    simp_all
  obtain ⟨x, hx⟩ := hx
  let e := IsPurelyInseparable.elemExponent F x
  have he : e > 0 := by
    by_contra
    subst e
    unfold IsPurelyInseparable.elemExponent at this
    simp_all
    obtain ⟨x₁, h⟩ := this
    specialize hx x₁
    have _ : (algebraMap F K) x₁ = x := by
      refine minpoly.root ?_ ?_
      exact Algebra.IsIntegral.isIntegral x
      refine Polynomial.IsRoot.def.mpr ?_
      have _ : Polynomial.eval x₁ (Polynomial.X - Polynomial.C x₁) = 0 := by
        simp_all
      grind
    grind
  let p := ringChar F
  let q := ringExpChar F
  have h : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], p = q ↔ Nat.Prime p :=
    char_eq_expChar_iff F
  specialize h p (ringExpChar F)
  have hpp : Nat.Prime p := by
    have hn : ∃ n, Module.finrank F K = q ^ n := by
      apply IsPurelyInseparable.finrank_eq_pow
    have _ : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
    have _ : ExpChar F q := ringExpChar.expChar F
    have hpq : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], q = 1 ↔ p = 0 :=
      expChar_one_iff_char_zero F
    specialize hpq p q
    by_contra
    simp_all
  have hp : p = ringExpChar F := by
    simp_all
  let y := x^(p^(e-1))
  let z := IsPurelyInseparable.elemReduct F x
  let pol1 :=  Polynomial.X ^ (p^e) - Polynomial.C z
  have _ : minpoly F x = pol1 := by
    grind [IsPurelyInseparable.minpoly_eq F x]
  let pol := Polynomial.X ^ p - Polynomial.C z
  have hx1 : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have _ : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hirr : Irreducible pol := by
    have hirr1 : Irreducible (minpoly F x) := by
      apply minpoly.irreducible
      simp_all
    have hirr2 : Irreducible (Polynomial.X ^ (p^e) - Polynomial.C z) →
    ∀ {m : ℕ}, m ∣ p^e → m ≠ 1 → ∀ (b : F), b ^ m ≠ z :=
      pow_ne_of_irreducible_X_pow_sub_C
    have _ : ∀ (a : F), a^p ≠ z := by
      apply hirr2
      grind
      simp
      left
      grind
      exact CharP.ringChar_ne_one
    have _ : Irreducible (Polynomial.X ^ p - Polynomial.C z) ↔ ∀ (a : F), a ^ p ≠ z := by
      apply X_pow_sub_C_irreducible_iff_of_prime
      apply hpp
    grind
  have _ : minpoly F y = pol := by
    have _ : (Polynomial.aeval x) (minpoly F x) = 0 := by
      apply minpoly.aeval
    have _ : pol1.aeval x = 0 := by
      simp_all
    have _ : pol.aeval y = pol1.aeval x := by
      unfold Polynomial.aeval
      simp_all
      subst pol
      subst pol1
      subst y
      unfold Polynomial.aevalEquiv
      simp
      have h: ∀ (x : K) (p e : ℕ), (x ^ p ^ e) ^ p = x ^ p ^ (e+1) := by
        ring_nf
        simp_all
      have h1 : ∃ (f : ℕ), e = f + 1 := by
        simp_all
      obtain ⟨f, _ ⟩ := h1
      specialize h x p f
      simp_all
    have hy : pol.aeval y = 0 := by
      simp_all
    have _ : pol.aeval y = 0 ↔ minpoly F y ∣ pol := by
      apply minpoly.isIntegrallyClosed_dvd_iff
      simp_all
    have hpol : minpoly F y ∣ pol := by
      simp_all
    unfold Polynomial.aeval at hy
    have _ : ExpChar F p := by
      exact ringExpChar.eq_iff.mp (id (Eq.symm hp))
    have hp1 : ∀ [ExpChar F p], 0 < p := by
      apply expChar_pos
    have _ : pol.Monic := by
      refine Polynomial.monic_X_pow_sub_C z ?_
      specialize hp1
      linarith
    have _ : (minpoly F y).Monic := by
      (expose_names; exact minpoly.monic h_3)
    have hfg : ∀ (f g : Polynomial F) (hf: f.Monic) (hg: Irreducible g) (hg1 : g.Monic) (_: f.natDegree > 0) (_ : f ∣ g),
      f = g := by
      intro f g hf hg hg1 hfd hdiv
      have : f.natDegree = 0 ∨ f.natDegree = g.natDegree := divisor_of_irreducible_poly f g hdiv hg
      have hdeg : f.natDegree = g.natDegree := by grind
      exact monic_divisor_of_same_degree f g hf hg1 hdiv hdeg
    specialize hfg (minpoly F y) pol
    have _ : (minpoly F y).natDegree > 0 := by
      (expose_names; exact minpoly.natDegree_pos h_3)
    simp_all
  let E := IntermediateField.adjoin F {y}
  use E
  have _ : IsIntegral F y →  Module.finrank F E = (minpoly F y).natDegree :=
    fun a => IntermediateField.adjoin.finrank a
  have _ : pol.natDegree = p := by
    exact Polynomial.natDegree_X_pow_sub_C
  grind

lemma finite_inseparable_extension_intermediate_internal (n : ℕ) :
  ∀ (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K], Module.finrank F K = (ringChar F)^n ∧ n > 0 →
       ∃ (E : IntermediateField F K), Module.finrank E K = ringChar F := by
  induction n with
  | zero => simp_all -- This case doesn't occur
  | succ n hyp =>
    intro F K _ _ _ _ _ t
    obtain ⟨h1, h2⟩ := t
    let p := ringChar F
    let q := ringExpChar F
    have h : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], p = q ↔ Nat.Prime p :=
      char_eq_expChar_iff F
    specialize h p (ringExpChar F)
    have _ : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
    have _ : ExpChar F q := ringExpChar.expChar F
    have hn : ∃ n, Module.finrank F K = q ^ n := by
      apply IsPurelyInseparable.finrank_eq_pow
    obtain ⟨n₁, hn⟩ := hn
    have hpp : Nat.Prime p := by
      have hpq : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], q = 1 ↔ p = 0 :=
        expChar_one_iff_char_zero F
      specialize hpq p q
      by_contra
      grind
    have hp : p = ringExpChar F := by simp_all
    have _ : ExpChar F p := ringExpChar.eq_iff.mp (id (Eq.symm hp))
    have _ : p ≥ 2 := Nat.Prime.two_le hpp
    by_cases n = 0
    · use (⊥: IntermediateField F K)
      simp_all
    · have _ : p^(n+1) ≥ 2^(n+1) := by
        (expose_names; exact Nat.pow_le_pow_left h_4 (n + 1))
      have _ : 2^(n+1) > 1 := Nat.one_lt_two_pow' n
      have _ : p^(n+1) > 1 := by grind
      have hr : Module.finrank F K > 1 := by grind
      have hE₀: ∃ E₀: IntermediateField F K, Module.finrank F E₀ = ringChar F :=
        finite_inseparable_extension_intermediate_small F K hr
      obtain ⟨E₀, hE₀⟩ := hE₀
      let _ := IntermediateField E₀ K
      have _ : Module.finrank E₀ K = ringChar E₀ ^ n ∧ n > 0 →
        ∃ (E: IntermediateField E₀ K), Module.finrank E K = ringChar E₀ :=
        hyp E₀ K
      have _ : Module.finrank F E₀ = p := by
        simp_all
        grind
      have _ : ringChar E₀ = p := Eq.symm (Algebra.ringChar_eq F ↥E₀)
      have hE : ∃ E: IntermediateField E₀ K, Module.finrank E K = ringChar E₀ := by
        apply hyp E₀ K
        constructor
        · have hmul : Module.finrank F E₀ * Module.finrank E₀ K = Module.finrank F K :=
            Module.finrank_mul_finrank F E₀ K
          have _ : Module.finrank F K = p^(n+1) := by
            simp_all
          have h3 : p * Module.finrank E₀ K = p * p^n := by
            grind
          have _ : p > 0 := by
            (expose_names; exact Nat.zero_lt_of_lt h_4)
          have h4 : (p * Module.finrank E₀ K) / p = (p * p^n) / p := by
            grind
          have h4 (a b c : ℕ) : a * b = a * c ∧ a ≠ 0 → b = c := by
            intro h5
            obtain ⟨h5, h6⟩ := h5
            exact (Nat.mul_right_inj h6).mp h5
          have _ : Module.finrank E₀ K = p^n := by
            grind
          grind
        · grind
      obtain ⟨E, _⟩ := hE
      let E₁ := IntermediateField.restrictScalars F E
      use E₁
      grind

lemma finite_inseparable_extension_intermediate (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (hr: Module.finrank F K > 1) :
      ∃ E : IntermediateField F K, Module.finrank E K = ringChar F := by
    let p := ringChar F
    let q := ringExpChar F
    have h : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], p = q ↔ Nat.Prime p :=
      char_eq_expChar_iff F
    specialize h p (ringExpChar F)
    have _ : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero F p
    have _ : ExpChar F q := ringExpChar.expChar F
    have hn : ∃ n, Module.finrank F K = q ^ n := by
      apply IsPurelyInseparable.finrank_eq_pow
    obtain ⟨n, hn⟩ := hn
    have hpp : Nat.Prime p := by
      have hpq : ∀ (p q : ℕ) [CharP F p] [ExpChar F q], q = 1 ↔ p = 0 :=
        expChar_one_iff_char_zero F
      specialize hpq p q
      by_contra
      simp_all
    have hp : p = ringExpChar F := by simp_all
    apply finite_inseparable_extension_intermediate_internal n F K
    constructor
    · grind
    · have _ : p > 1 := Nat.Prime.one_lt hpp
      have _ : p^n > 1 := by
        grind
      have _ : n > 0 := by
        (expose_names; exact (Nat.pow_lt_pow_iff_right h_3).mp h_4)
      grind
