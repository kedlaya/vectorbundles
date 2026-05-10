module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type

public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2

@[expose] public section

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (h: Module.finrank F K = p)
  (hsep: IsGalois F K): ¬ ringChar F = p := by
  sorry

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
  (hgal: IsGalois F K): p = 2 := by
  sorry

lemma finite_separable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Algebra.IsSeparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  sorry

lemma finite_inseparable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsPurelyInseparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  sorry

lemma finite_algebraic_closure_separable (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] : IsGalois F K :=
  have _: PerfectField F := by
    by_cases CharZero F
    · apply PerfectField.ofCharZero
    · let p := ringChar F
      have _: Nat.Prime p ∨ p = 0 := by
        apply CharP.char_is_prime_or_zero F p
      have _: Nat.Prime p := by
        grind [CharP.ringChar_zero_iff_CharZero F]
      have hchar: ExpChar F p := by
        (expose_names; exact ExpChar.prime h_2)
      let frob := frobenius F p
      have hpow: ∀ a : F, ∃ b : F, b^p = a := by
        intro a
        by_cases hp: p = 2
        · have hi : ∃ (i : F), i^2 = -1 := by
            use 1
            sorry
          sorry
          --   sorry
            -- apply quadratic_algebraic_closure_no_i F K a
        · let d := Module.finrank F K
          have _ : 1 < p := by
            (expose_names; exact Nat.Prime.one_lt h_2)
          have h1: ∃ n : ℕ, d < p^n := by
            refine pow_unbounded_of_one_lt d ?_
            grind
          obtain ⟨n, h2⟩ := h1
          have _: IsAlgClosed K := by
            exact IsAlgClosure.isAlgClosed F
          have h3: ∃ b : K, b^(p^n) = (algebraMap F K) a := by
            refine IsAlgClosed.exists_pow_nat_eq ((algebraMap F K) a) ?_
            grind
          obtain ⟨b, h4⟩ := h3
          let f := minpoly F b
          have _ : ¬ Irreducible f := by
            sorry
          let g := Polynomial.factor f
          let d₁ := Polynomial.natDegree g
          have _ : d₁ < p^n := by
            sorry
          let e := gcd d₁ p^n
          let (g_1, g_2) := Nat.xgcd d₁ p^n
          sorry
      have _: Function.Surjective frob := by
          unfold Function.Surjective
          unfold frob
          intro a
          apply hpow
      have _: PerfectRing F p := by
        exact PerfectRing.ofSurjective F p hpow
      exact PerfectRing.toPerfectField F p
  { to_isSeparable := IsSepClosure.isSeparable, to_normal := IsGalois.to_normal }

lemma finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : ∃ (i : K), i^2 = -1 ∧ i ∈ (algebraMap F K).range) : IsAlgClosed F := by

  obtain ⟨i, h1, h2⟩ := h
  by_contra
  have hgal: IsGalois F K :=
    finite_algebraic_closure_separable F K
  let G := K ≃ₐ[F] K
  let d := Nat.card G
  have _ : d = Module.finrank F K := by
    apply IsGaloisGroup.card_eq_finrank
  have hd : 1 < d := by
    sorry
  let p := Nat.minFac d
  have hp : Nat.Prime p := by
    sorry
    --apply Nat.minFac_prime d hd
  have cyc: ∃ (g : G), orderOf g = p := by
    -- apply exists_prime_orderOf_dvd_card p
    sorry
  obtain ⟨g, hg1⟩ := cyc
  let H := Subgroup.zpowers g
  let F₁ := IntermediateField.fixedField H
  have hrank : Module.finrank F₁ K = p := by
    sorry
    --apply IsGalois.card_fixingSubgroup_eq_finrank
  have _: IsAlgClosure F₁ K := by
    sorry
  have hgal1: IsGalois F₁ K :=
    finite_algebraic_closure_separable F₁ K
  have hp2: p = 2 :=
    finite_algebraic_closure_cyclic_quadratic F₁ K p hp hrank hgal1
  have hfin: Module.finrank F₁ K = 2 := by
    sorry
  have hq : ∀ (a : F₁), IsSquare a ∨ IsSquare (-a) :=
    quadratic_algebraic_closure_no_i F₁ K hfin
  have _ : ∀ a : F₁, IsSquare a := by
    sorry
  have ha: ∃ a : F₁, ¬ IsSquare a := by
    sorry
  obtain ⟨a, ha⟩ := ha
  sorry
