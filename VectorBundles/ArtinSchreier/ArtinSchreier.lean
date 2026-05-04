module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

lemma Field.two_power_roots_irreducible (F : Type) [Field F] (hF: ringChar F = 2)
  (a : F) (ha : ¬ ∃ (b : F), b^2 = a) :
  ∀ (n : ℕ), Irreducible (Polynomial.X ^ (2^n) - Polynomial.C a) := by

  intro n
  let K := AlgebraicClosure F
  -- have have_b: ∃ b : K, b^(2^n) = a := by
    -- apply IsAlgClosed.exists_pow_nat_eq
    -- simp
  sorry

lemma Field.finite_algebraic_closure_separable (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosed K] : IsGalois F K := by
  sorry

lemma Field.finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (hp: Prime p) (h: Module.finrank F K = p)
  (hsep: IsGalois F K): ¬ ringChar F = p := by
  sorry

lemma Field.finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (hp: Prime p) (hrank: Module.finrank F K = p)
  (hgal: IsGalois F K): p = 2 := by
  sorry

lemma Field.quadratic_algebraic_closure_no_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (h : Module.finrank F K = 2) : ¬∃ (i : F), i^2 = -1 := by
  sorry

lemma Field.finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (h : ∃ (i : F), i^2 = -1) : F = K := by

  by_contra
  let d := Module.finrank F K
  have hd : 1 < d := by
    sorry
  let p := Nat.minFac d
  have hp : Prime p := by
    sorry
    --apply Nat.minFac_prime d hd

  let G := K ≃ₐ[F] K
  have hgal: IsGalois F K :=
    Field.finite_algebraic_closure_separable F K

  have cyc: ∃ (g : G), orderOf g = p := by
    -- apply exists_prime_orderOf_dvd_card
    sorry
  obtain ⟨g, hg1⟩ := cyc
  let H := Subgroup.zpowers g
  let F₁ := IntermediateField.fixedField H
  have hrank : Module.rank F₁ K = p := by
    sorry
    -- apply IsGalois.card_fixingSubgroup_eq_finrank
  have hgal1: IsGalois F₁ K :=
    Field.finite_algebraic_closure_separable F₁ K
  have hp2: p = 2 :=
    sorry
    -- Field.finite_algebraic_closure_cyclic_quadratic F₁ K p hp hrank hgal1

  sorry

lemma Field.RealClosed_from_quadratic (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (h : Module.rank F K = 2)
  (h1 : ¬ ∃ i : F, i^2 = -1) :
  IsRealClosed F := by

  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i

  have semi: IsSemireal F := by
    sorry
  have hR: CharZero F := by
    exact CharP.charP_to_charZero F
  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := ?_, exists_isRoot_of_odd_natDegree := ?_ }
  -- ∀ (x : F), IsSquare x ∨ IsSquare (-x)
  sorry
  -- ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x
  intro f
  let p := f.roots
  sorry

theorem Field.artin_schreier_thm (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosed K] : IsAlgClosed F ∨ IsRealClosed F := by

  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i
  sorry
